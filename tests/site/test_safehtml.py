"""The writeups' HTML sanitizer (site/safehtml.py) and the HTML the site writes from it (site/writeup.py), decided
2026-11-16 (the owner asked for HTML writeups that can hold inline SVG figures).

    python3.12 svgolf/tests/site/test_safehtml.py

A writeup comes in a pull request from anyone and is published on the site's origin. These tests feed the sanitizer
an adversarial battery (scripts, event handlers in every casing, javascript:/data:/vbscript: links hidden by white
space and character references, SVG's own vectors, style, CDATA, malformed and misnested markup, mutation-XSS
nesting, id and class clobbering of the page's own, oversized input) and require each to be REFUSED, with a message
that names the element or attribute and the right line; they check that what is allowed renders as documented, that
`sanitize` is idempotent, and that the allowlists stated for authors (README.md, "Writeups") are the module's.
No tool is needed."""

import os
import re
import sys
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
SVGOLF = os.path.dirname(os.path.dirname(HERE))
SITE = os.path.join(SVGOLF, "site")
WRITEUPS = os.path.join(SVGOLF, "leaderboard", "writeups")
sys.path.insert(0, SITE)
sys.dont_write_bytecode = True

import figs        # noqa: E402
import safehtml    # noqa: E402
import writeup     # noqa: E402

S = safehtml.SVG_NS


def fig(inner, caption="A caption.", vb="0 0 100 50", title="A drawing."):
    """An author's figure: a drawing with a title, then `inner`, then the caption."""
    return (f'<figure>\n<svg viewBox="{vb}"><title>{title}</title>{inner}</svg>\n'
            f"<figcaption>{caption}</figcaption>\n</figure>")


def render(body, **kw):
    return writeup.render(f"<h1>T</h1>\n\n{body}\n", source="w.html", **kw)[1]


# (what it is, the body, a fragment the refusal must hold, the line it must name; the body starts on line 3, after
# the title line and a blank line)
HOSTILE = [
    # -- scripts
    ("script", "<script>alert(1)</script>", "the element <script> is not allowed", 3),
    ("script, upper case", "<SCRIPT SRC=https://evil.example/x.js></SCRIPT>", "<script> is not allowed", 3),
    ("script, mixed case, later line", "<p>a</p>\n\n<ScRiPt>alert(1)</sCrIpT>", "<script> is not allowed", 5),
    ("script, slash attribute", "<script/xss src=x></script>", "<script> is not allowed", 3),
    ("script, split name", "<scr<script>ipt>alert(1)</script>", "is not allowed", 3),
    ("script in a paragraph", "<p>x <script>alert(1)</script></p>", "<script> is not allowed", 3),
    ("script in a drawing", fig("<script>alert(1)</script>"), "<script> is not allowed", 4),
    ("svg script with href", fig('<script href="https://evil.example/x.js"/>'), "<script> is not allowed", 4),
    # -- event handlers, every casing, every element
    ("onclick on p", '<p onclick="alert(1)">x</p>', "<p>: the attribute onclick is not allowed (event handlers", 3),
    ("ONCLICK upper", "<p ONCLICK=alert(1)>x</p>", "the attribute onclick is not allowed", 3),
    ("oNmOuSeOvEr mixed", '<p>a <em oNmOuSeOvEr="alert(1)">b</em></p>', "<em>: the attribute onmouseover", 3),
    ("onerror unquoted", "<p><code onerror=alert(1)>x</code></p>", "<code>: the attribute onerror", 3),
    ("onfocus with spaces", '<h2 onfocus = "alert(1)">x</h2>', "<h2>: the attribute onfocus", 3),
    ("handler after slash", "<p/onclick=alert(1)>x</p>", "the attribute onclick", 3),
    ("handler on a later line of the tag", '<p><span\n  class="muted"\n  onclick="alert(1)">x</span></p>',
     "<span>: the attribute onclick", 5),
    ("onload on svg", '<figure><svg viewBox="0 0 9 9" onload="alert(1)"><title>t</title></svg>'
     "<figcaption>c</figcaption></figure>", "<svg>: the attribute onload", 3),
    ("onbegin on rect", fig('<rect onbegin="alert(1)" x="1" y="1" width="2" height="2"/>'), "<rect>: the attribute "
     "onbegin", 4),
    ("onanimationstart on figure", '<figure onanimationstart="alert(1)" data-figure="add-ripple" data-alt="a">'
     "<figcaption>c</figcaption></figure>", "<figure>: the attribute onanimationstart", 3),
    ("onclick on a link", '<p><a href="https://example.org" onclick="alert(1)">x</a></p>', "<a>: the attribute "
     "onclick", 3),
    ("onclick on a list item", "<ul>\n<li onclick=alert(1)>x</li>\n</ul>", "<li>: the attribute onclick", 4),
    ("onclick on a cell", "<table><tbody><tr><td onclick=x>1</td></tr></tbody></table>", "<td>: the attribute onclick",
     3),
    # -- javascript:, data:, vbscript: links, hidden by white space and character references
    ("javascript:", '<p><a href="javascript:alert(1)">x</a></p>', "<a>: href='javascript:alert(1)': a link is", 3),
    ("JaVaScRiPt:", '<p><a href="JaVaScRiPt:alert(1)">x</a></p>', "href='JaVaScRiPt:alert(1)'", 3),
    ("leading space", '<p><a href=" javascript:alert(1)">x</a></p>', "href=' javascript:alert(1)'", 3),
    ("tab character reference", '<p><a href="java&#x09;script:alert(1)">x</a></p>', "&#x09; names U+0009", 3),
    ("decimal tab reference", '<p><a href="java&#9;script:alert(1)">x</a></p>', "U+0009", 3),
    ("newline reference", '<p><a href="java&#x0A;script:alert(1)">x</a></p>', "a link is", 3),
    ("NewLine entity", '<p><a href="jav&NewLine;ascript:alert(1)">x</a></p>', "a link is", 3),
    ("encoded j", '<p><a href="&#106;avascript:alert(1)">x</a></p>', "href='javascript:alert(1)'", 3),
    ("hex encoded j", '<p><a href="&#x6A;avascript:alert(1)">x</a></p>', "href='javascript:alert(1)'", 3),
    ("colon entity", '<p><a href="javascript&colon;alert(1)">x</a></p>', "href='javascript:alert(1)'", 3),
    ("colon reference", '<p><a href="javascript&#58;alert(1)">x</a></p>', "href='javascript:alert(1)'", 3),
    ("control character first", '<p><a href="&#1;javascript:alert(1)">x</a></p>', "&#1; names U+0001", 3),
    ("NUL reference", '<p><a href="&#0;javascript:alert(1)">x</a></p>', "&#0; names U+0000", 3),
    ("C1 reference", '<p><a href="&#x9b;javascript:alert(1)">x</a></p>', "names U+009B", 3),
    ("reference without ;", '<p><a href="&#1javascript:alert(1)">x</a></p>', "&#1 names U+0001", 3),
    ("surrogate reference", "<p>&#xD800;</p>", "names U+D800", 3),
    ("reference past Unicode", "<p>&#x110000;</p>", "names U+110000", 3),
    ("noncharacter reference", "<p>&#xFFFE;</p>", "names U+FFFE", 3),
    ("bare & in an attribute", '<p><a href="https://example.org/?a=1&b=2">x</a></p>', "write & as &amp;", 3),
    ("legacy entity in an attribute", '<p><a href="https://example.org/?a=1&copy=2">x</a></p>', "write & as &amp;", 3),
    ("prefix entity in an attribute", '<figure data-figure="add-ripple" data-alt="&notit;"><figcaption>c</figcaption>'
     "</figure>", "write & as &amp;", 3),
    ("percent-encoded scheme", '<p><a href="%6Aavascript:alert(1)">x</a></p>', "a link is", 3),
    ("javascript with a comment", '<p><a href="javascript://%0aalert(1)">x</a></p>', "a link is", 3),
    ("data:text/html", '<p><a href="data:text/html;base64,PHNjcmlwdD5hbGVydCgxKTwvc2NyaXB0Pg==">x</a></p>',
     "href='data:text/html", 3),
    ("DATA: upper", '<p><a href="DATA:text/html,x">x</a></p>', "a link is", 3),
    ("vbscript:", '<p><a href="vbscript:msgbox(1)">x</a></p>', "href='vbscript:msgbox(1)'", 3),
    ("protocol-relative", '<p><a href="//evil.example/x">x</a></p>', "a link is", 3),
    ("backslashes", '<p><a href="\\\\evil.example\\x">x</a></p>', "a link is", 3),
    ("root-relative", '<p><a href="/abs/x">x</a></p>', "a link is", 3),
    ("scheme without slashes", '<p><a href="https:evil.example">x</a></p>', "a link is", 3),
    ("a quote in the address", '<p><a href="https://ex.example/&quot;onmouseover=alert(1)">x</a></p>', "a link is", 3),
    ("user info", '<p><a href="https://user@localhost/">x</a></p>', "a link is", 3),
    ("empty href", '<p><a href="">x</a></p>', "a link is", 3),
    ("href without value", "<p><a href>x</a></p>", "needs a value", 3),
    ("link without href", "<p><a>x</a></p>", "<a> needs the attribute href", 3),
    ("target _blank", '<p><a href="https://example.org" target="_blank">x</a></p>', "the attribute target", 3),
    # -- SVG's own vectors
    ("foreignObject", fig('<foreignObject width="9" height="9"><p>x</p></foreignObject>'), "<foreignObject> is not "
     "allowed", 4),
    ("use, external", fig('<use href="https://evil.example/x.svg#a"/>'), "<use> is not allowed", 4),
    ("use, xlink data:", fig('<use xlink:href="data:image/svg+xml;base64,PHN2Zy8+"/>'), "<use> is not allowed", 4),
    ("use, internal", fig('<use href="#a"/>'), "<use> is not allowed", 4),
    ("animate href", fig('<animate attributeName="href" to="javascript:alert(1)"/>'), "<animate> is not allowed", 4),
    ("set onmouseover", fig('<set attributeName="onmouseover" to="alert(1)"/>'), "<set> is not allowed", 4),
    ("animateTransform", fig("<animateTransform/>"), "<animateTransform> is not allowed", 4),
    ("svg a", fig('<a href="javascript:alert(1)"><text>x</text></a>'), "<a> inside a drawing", 4),
    ("svg a with xlink", fig('<a xlink:href="javascript:alert(1)"><text>x</text></a>'), "<a> inside a drawing", 4),
    ("image", fig('<image href="https://evil.example/x.png"/>'), "<image> is not allowed", 4),
    ("feImage filter", fig('<filter id="f"><feImage href="https://evil.example/x"/></filter>'), "<filter> is not "
     "allowed", 4),
    ("filter attribute", fig('<rect filter="url(#f)" x="1" y="1" width="2" height="2"/>'), "the attribute filter", 4),
    ("textPath", fig('<text><textPath href="#p">x</textPath></text>'), "<textPath> is not allowed", 4),
    ("xlink:href on rect", fig('<rect xlink:href="javascript:alert(1)" x="1"/>'), "the attribute xlink:href is not "
     "allowed", 4),
    ("href on a gradient", fig('<defs><linearGradient id="g" href="#h"><stop offset="0"/></linearGradient></defs>'),
     "<linearGradient>: the attribute href", 4),
    ("xmlns:xlink", '<figure><svg viewBox="0 0 9 9" xmlns:xlink="http://www.w3.org/1999/xlink"><title>t</title>'
     "</svg><figcaption>c</figcaption></figure>", "the attribute xmlns:xlink", 3),
    ("wrong xmlns", '<figure><svg viewBox="0 0 9 9" xmlns="http://www.w3.org/1999/xhtml"><title>t</title>'
     "</svg><figcaption>c</figcaption></figure>", "the SVG namespace is", 3),
    ("external paint", fig('<rect fill="url(https://evil.example/x.svg#g)" x="1"/>'), "fill='url(https://evil", 4),
    ("paint to nothing", fig('<rect fill="url(#nowhere)" x="1"/>'), "fill=url(#nowhere) names no <linearGradient>", 4),
    ("marker to a gradient", fig('<defs><linearGradient id="g"><stop offset="0"/></linearGradient></defs>'
                                  '<line marker-end="url(#g)" x1="0"/>'), "names no <marker>", 4),
    ("clip-path data:", fig('<rect clip-path="url(data:image/svg+xml,x)" x="1"/>'), "url(#id) of this drawing", 4),
    ("transform url()", fig('<g transform="url(#x)"></g>'), "transform='url(#x)'", 4),
    ("path commands", fig('<path d="javascript:alert(1)"/>'), "a path's commands", 4),
    ("nested svg", fig('<svg viewBox="0 0 1 1" onload="alert(1)"></svg>'), "an <svg> inside an <svg>", 4),
    ("svg outside a figure", '<p><svg viewBox="0 0 1 1"><title>t</title></svg></p>', "an <svg> drawing goes in a "
     "<figure>", 3),
    ("svg at the top", '<svg viewBox="0 0 1 1"><title>t</title></svg>', "goes in a <figure>", 3),
    ("svg style element", fig("<style>@import url(https://evil.example/x.css);</style>"), "<style> is not allowed",
     4),
    ("a colour", fig('<rect fill="#ff0000" x="1"/>'), "fill='#ff0000': a colour comes from a class", 4),
    ("stop colour", fig('<defs><linearGradient id="g"><stop offset="0" stop-color="red"/></linearGradient></defs>'),
     "stop-color is currentColor", 4),
    ("svg width", '<figure><svg viewBox="0 0 9 9" width="900"><title>t</title></svg><figcaption>c</figcaption>'
     "</figure>", "<svg>: the attribute width is not allowed", 3),
    ("svg class", '<figure><svg viewBox="0 0 9 9" class="tabs-pane"><title>t</title></svg><figcaption>c'
     "</figcaption></figure>", "<svg>: the attribute class is not allowed", 3),
    ("svg without viewBox", "<figure><svg><title>t</title></svg><figcaption>c</figcaption></figure>", "<svg> needs "
     "the attribute viewBox", 3),
    ("drawing too wide", fig("", vb="0 0 5000 10"), "a drawing is at most 1200 wide", 4),
    ("drawing without title", '<figure><svg viewBox="0 0 9 9"><rect x="1"/></svg><figcaption>c</figcaption>'
     "</figure>", "first element is its <title>", 3),
    ("title in a group", fig("<g><title>x</title></g>"), "<title> is not allowed directly inside <g>", 4),
    ("HTML in a title", fig("", title="a <em>b</em>"), "<em> inside a drawing", 4),
    ("p in a desc", fig("<desc><p>x</p></desc>"), "<p> inside a drawing", 4),
    ("unknown svg class", fig('<rect class="tabs-pane" x="1"/>'), "a class here is one of t-lab", 4),
    ("svg id on a shape", fig('<rect id="schematics" x="1"/>'), "<rect>: the attribute id is not allowed", 4),
    ("upper-case id", fig('<defs><marker id="Arrow"><path d="M0 0"/></marker></defs>'), "an id is lower-case", 4),
    ("duplicate ids", fig('<defs><marker id="a"><path d="M0 0"/></marker><marker id="a"><path d="M0 0"/></marker>'
                          "</defs>"), "the id 'a' is used twice in this drawing", 4),
    ("a drawing over 50 kB", fig('<path d="M0 0' + " L1 1" * 11000 + '"/>'), "bytes, over 50000", 4),
    # -- style
    ("style attribute url()", '<p style="background:url(javascript:alert(1))">x</p>', "<p>: the attribute style is "
     "not allowed", 3),
    ("style on a drawing's mark", fig('<rect style="fill:url(javascript:alert(1))" x="1"/>'), "<rect>: the attribute "
     "style", 4),
    ("style element", "<style>@import 'https://evil.example/x.css';</style>", "<style> is not allowed", 3),
    ("behavior", '<div style="behavior:url(x.htc)">x</div>', "the attribute style", 3),
    # -- CDATA, comments, declarations
    ("CDATA at the top", "<![CDATA[<script>alert(1)</script>]]>", "a CDATA section", 3),
    ("CDATA in a drawing", fig("<text><![CDATA[</text><script>alert(1)</script>]]></text>"), "a CDATA section", 4),
    ("comment", "<!-- <script>alert(1)</script> -->", "a comment is not allowed", 3),
    ("bogus comment", "<p>a</p>\n<!x>", "a comment is not allowed", 4),
    ("doctype", "<!DOCTYPE html>", "no doctype", 3),
    ("processing instruction", '<?xml version="1.0"?>', "processing instruction", 3),
    # -- malformed, unclosed, misnested
    ("unclosed paragraph", "<p>a", "<p> (opened on line 3) is never closed", 3),
    ("unclosed link", '<p><a href="https://example.org">x</p>', "</p> closes <a>", 3),
    ("misnested", "<p><em>a<strong>b</em></strong></p>", "</em> closes <strong>", 3),
    ("stray end tag", "</p>", "</p> has no open <p>", 3),
    ("wrong end tag", "<p>a</div>", "</div> has no open <div>", 3),
    ("self-closed p", "<p/>", "<p/> does not close an HTML element", 3),
    ("end tag of a void", "<p>a</br></p>", "</br> is not a tag", 3),
    ("empty end tag", "<p>a</p></>", "`</>` is not a tag", 3),
    ("text loose at the top", "Just Markdown, no tags", "outside a block", 3),
    ("Markdown heading", "## The idea", "outside a block", 3),
    ("a lone <", "<p>a</p>\n<", "outside a block", 4),
    # refused either way: Python's html.parser reads an unterminated comment as loose text before
    # 3.12.11 and as a comment from then on
    ("unterminated comment", "<p>a</p>\n<!-- x", ("outside a block", "a comment is not allowed"), 4),
    # -- mutation XSS: nesting a browser would rearrange
    ("p in svg breakout", fig('<p><style><img src=x onerror=alert(1)></style></p>'), "<p> inside a drawing", 4),
    ("math mglyph", "<math><mtext><table><mglyph><style><img src=x onerror=alert(1)>", "<math> is not allowed", 3),
    ("noscript title", '<noscript><p title="</noscript><img src=x onerror=alert(1)>"></p></noscript>',
     "<noscript> is not allowed", 3),
    ("form math", "<form><math><mtext></form><form><mglyph><style></math><img src onerror=alert(1)>",
     "<form> is not allowed", 3),
    ("svg end p", fig('</p><style><a id="</style><img src=1 onerror=alert(1)>">'), "</p> has no open <p>", 4),
    ("div in p", "<p>a<div>b</div></p>", "<div> is not allowed directly inside <p>", 3),
    ("table in p", "<p><table><tbody><tr><td>x</td></tr></tbody></table></p>", "<table> is not allowed directly", 3),
    ("tr without tbody", "<table><tr><td>x</td></tr></table>", "<tr> is not allowed directly inside <table>: it goes "
     "in a <thead> or <tbody>", 3),
    ("text in a table", "<table>x<tbody></tbody></table>", "directly inside <table>", 3),
    ("li at the top", "<li>x</li>", "<li> is not allowed directly inside the top: it goes in a <ul> or <ol>", 3),
    ("td at the top", "<td>x</td>", "<td> is not allowed directly inside the top: it goes in a <tr>", 3),
    ("caption at the top", "<figcaption>x</figcaption>", "it goes in a <figure>", 3),
    ("heading in a heading", "<h2>a<h3>b</h3></h2>", "<h3> is not allowed directly inside <h2>", 3),
    ("link in a link", '<p><a href="https://a.example"><em><a href="https://b.example">x</a></em></a></p>',
     "a link inside a link", 3),
    ("pre with text outside code", "<pre>x<code>y</code></pre>", "text 'x' directly inside <pre>", 3),
    ("pre with a newline", "<pre>\n<code>y</code></pre>", "a <pre> holds one <code>", 3),
    ("figure in a list", "<ul><li><figure data-figure=\"add-ripple\" data-alt=\"a\"><figcaption>c</figcaption>"
     "</figure></li></ul>", "<figure> is not allowed directly inside <li>", 3),
    ("figure without a caption", '<figure><svg viewBox="0 0 9 9"><title>t</title></svg></figure>', "holds an <svg> "
     "drawing and then its <figcaption>", 3),
    ("two drawings", '<figure><svg viewBox="0 0 9 9"><title>t</title></svg><svg viewBox="0 0 9 9"><title>u</title>'
     "</svg><figcaption>c</figcaption></figure>", "holds an <svg> drawing", 3),
    ("template", "<template><script>alert(1)</script></template>", "<template> is not allowed", 3),
    ("textarea", "<textarea></textarea><script>alert(1)</script>", "<textarea> is not allowed", 3),
    ("xmp", "<xmp><script>alert(1)</script></xmp>", "<xmp> is not allowed", 3),
    ("plaintext", "<plaintext><script>alert(1)</script>", "<plaintext> is not allowed", 3),
    ("iframe srcdoc", '<iframe srcdoc="&lt;script&gt;alert(1)&lt;/script&gt;"></iframe>', "<iframe> is not allowed",
     3),
    ("deep nesting", "<div>" * 40 + "x" + "</div>" * 40, "nested more than 32 deep", 3),
    # -- id and class clobbering of the page's own
    ("id on a heading", '<h2 id="schematics">x</h2>', "<h2>: the attribute id is not allowed", 3),
    ("id on a paragraph", '<p id="writeup">x</p>', "<p>: the attribute id is not allowed", 3),
    ("id on a div", '<div id="main">x</div>', "<div>: the attribute id is not allowed", 3),
    ("name", '<p><a href="https://example.org" name="tabs">x</a></p>', "the attribute name is not allowed", 3),
    ("class of the page's tabs", '<div class="tabs-pane">x</div>', "class='tabs-pane': a class here is one of muted",
     3),
    ("class of the page's script hook", '<p><span class="js-tabs">x</span></p>', "a class here is one of muted", 3),
    ("class on a paragraph", '<p class="anchor">x</p>', "<p>: the attribute class is not allowed", 3),
    ("data attribute", '<p data-tabs="x">x</p>', "the attribute data-tabs is not allowed", 3),
    ("role", '<p role="tab">x</p>', "the attribute role is not allowed", 3),
    ("aria", '<p aria-hidden="true">x</p>', "the attribute aria-hidden is not allowed", 3),
    ("dir", '<p dir="rtl">x</p>', "the attribute dir is not allowed", 3),
    ("title attribute", '<p title="x">x</p>', "the attribute title is not allowed", 3),
    ("code language outside pre", '<p><code class="language-lean">x</code></p>', "only on the <code> of a <pre>", 3),
    ("unknown code language", '<pre><code class="language-js">x</code></pre>', "language-X, X one of", 3),
    # -- characters a text may not hold, also as references
    ("bidi override", "<p>left &#x202E; right</p>", "&#x202E; names U+202E", 3),
    ("raw bidi override", "<p>left \u202e right</p>", "the character U+202E", 3),
    ("bidi isolate", "<p>&#x2066;x</p>", "U+2066", 3),
    ("byte-order mark", "<p>&#xFEFF;x</p>", "U+FEFF", 3),
    ("DEL", "<p>&#127;</p>", "names U+007F", 3),
    ("tab entity", "<p>a&Tab;b</p>", "the character U+0009", 3),
    ("backspace in alt", '<figure data-figure="add-ripple" data-alt="a&#8;b"><figcaption>c</figcaption></figure>',
     "names U+0008", 3),
    ("bidi in a caption, line 5", "<p>a</p>\n\n<figure data-figure=\"add-ripple\" data-alt=\"a\"><figcaption>&#x202d;"
     "</figcaption></figure>", "U+202D", 5),
    # -- elements authors are likely to try
    ("img remote", '<p><img src="https://evil.example/pixel.png"></p>', "<img> is not allowed: a picture", 3),
    ("img data", '<p><img src="data:image/png;base64,AAAA"></p>', "<img> is not allowed", 3),
    ("object", '<object data="https://evil.example/x.swf"></object>', "<object> is not allowed", 3),
    ("embed", '<embed src="https://evil.example/x">', "<embed> is not allowed", 3),
    ("link", '<link rel="stylesheet" href="https://evil.example/x.css">', "<link> is not allowed", 3),
    ("meta refresh", '<meta http-equiv="refresh" content="0;url=https://evil.example">', "<meta> is not allowed", 3),
    ("base", '<base href="https://evil.example/">', "<base> is not allowed", 3),
    ("form", '<form action="https://evil.example"><input name="p"></form>', "<form> is not allowed", 3),
    ("button formaction", '<p><button formaction="javascript:alert(1)">x</button></p>', "<button> is not allowed", 3),
    ("bold", "<p><b>x</b></p>", "<b> is not allowed: use <strong>", 3),
    ("details", "<details><summary>x</summary></details>", "<details> is not allowed", 3),
    ("h1 in the body", "<h1>Another title</h1>", "line 1's <h1> is the title", 3),
    ("title element", "<title>x</title>", "<title> is a drawing's element", 3),
]


class HostileTest(unittest.TestCase):
    def test_every_hostile_body_is_refused_with_its_line_and_what(self):
        self.assertGreaterEqual(len(HOSTILE), 150)
        for what, body, msg, line in HOSTILE:
            with self.subTest(what=what):
                # the sanitizer alone, then the whole writeup through the site's renderer
                for refuse in (lambda: safehtml.parse(body + "\n", source="w.html", first_line=3),
                               lambda: render(body)):
                    with self.assertRaises(safehtml.HtmlError) as cm:
                        refuse()
                    msgs = msg if isinstance(msg, tuple) else (msg,)
                    self.assertTrue(any(m in cm.exception.message for m in msgs), cm.exception.message)
                    self.assertEqual(cm.exception.line, line, cm.exception.message)
                    self.assertTrue(str(cm.exception).startswith(f"w.html:{line}: "))

    def test_the_writer_refuses_what_it_alone_can_see(self):
        h2 = "<h2>The idea</h2>\n\n"
        for what, body, msg in (
                ("a fragment of the page", h2 + '<p><a href="#schematics">x</a></p>', "names no heading or figure"),
                ("the page's pane", '<p><a href="#writeup">x</a></p>', "names no heading or figure"),
                ("a figure id that is not there", h2 + '<p><a href="#figure-1">x</a></p>', "names no heading"),
                ("an unknown generated figure", '<figure data-figure="nope" data-alt="a"><figcaption>c</figcaption>'
                                                "</figure>", "no figure is named 'nope'"),
                ("the site's title id", fig('<defs><marker id="t"><path d="M0 0"/></marker></defs>'),
                 "the ids t and d are the site's"),
                ("a drawing's id a heading has", "<h2>Figure 1 arrow</h2>\n\n"
                                                 + fig('<defs><marker id="arrow"><path d="M0 0"/></marker></defs>'),
                 "which a heading of this writeup has")):
            with self.subTest(what=what):
                with self.assertRaisesRegex(safehtml.HtmlError, re.escape(msg)):
                    render(body)

    def test_oversized_input_is_refused(self):
        with self.assertRaisesRegex(safehtml.HtmlError, "bytes, over the cap of 200000"):
            safehtml.parse("<p>" + "x" * 200_001 + "</p>")
        with self.assertRaisesRegex(safehtml.HtmlError, "nested more than 32 deep"):
            safehtml.parse("<ul><li>" * 20 + "x" + "</li></ul>" * 20)

    def test_the_audit_refuses_what_the_writer_never_writes(self):
        for bad in ("<script>x</script>", '<p onclick="x">a</p>', '<a href="javascript:x">a</a>', '<p id="main">a</p>',
                    '<p class="tabs-pane">a</p>', '<svg style="fill:red"></svg>', "<!-- x -->", '<img src="x">',
                    '<h3 id="writeup-a">a</h3><h3 id="writeup-a">b</h3>', '<a href="#schematics">a</a>'):
            with self.subTest(bad=bad):
                with self.assertRaisesRegex(safehtml.HtmlError, "internal: the rendered writeup holds"):
                    writeup.audit(bad, source="w")


ALLOWED = """<h2>The idea</h2>

<p>Text with <code>a &lt; b</code> &amp; <em>em</em>, <strong>strong</strong>, x<sub>i</sub>, 2<sup>N</sup>, a
<span class="muted">quiet</span> word, a <a href="https://example.org/x?a=1&amp;b=2">link</a>, a
<a href="mailto:someone&#64;example.org">mail</a>, a <a href="../index.html">relative link</a>, <a href="#figure-1">Figure
1</a> and <a href="#the-idea">a section</a>.<br>A new line.</p>

<h3>Lists <em>and</em> code</h3>

<ol start="3">
<li>one</li>
<li><p>two</p>
<ul>
<li>nested</li>
</ul>
</li>
</ol>

<pre><code class="language-lean">theorem x : 1 = 1 := rfl</code></pre>

<pre><code>plain &amp; simple</code></pre>

<blockquote>
<p>A quotation.</p>
</blockquote>

<hr>

<div class="muted"><p>A note.</p></div>

<h4>A table</h4>

<table>
<thead><tr><th class="al-left">a</th><th class="al-right" colspan="2">b</th></tr></thead>
<tbody><tr><td>1</td><td class="al-center">2</td><td rowspan="1">3</td></tr></tbody>
</table>

<figure>
<svg viewBox="0 0 480 160" xmlns="http://www.w3.org/2000/svg">
<title>Two boxes and an arrow.</title>
<desc>The left box feeds the right one.</desc>
<defs>
<marker id="arrow" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="6" markerHeight="6" orient="auto-start-reverse"
markerUnits="strokeWidth"><path class="arrow" d="M0 0L10 5L0 10z"/></marker>
<clipPath id="clip" clipPathUnits="userSpaceOnUse"><rect x="0" y="0" width="480" height="160"/></clipPath>
<linearGradient id="fade" x1="0" y1="0" x2="100%" y2="0" gradientUnits="objectBoundingBox"><stop offset="0"
stop-color="currentColor" stop-opacity="0"/><stop offset="100%" stop-color="currentColor"/></linearGradient>
</defs>
<g clip-path="url(#clip)" transform="translate(10, 10) scale(1)">
<rect class="b" x="0" y="0" width="120" height="60" rx="4"/>
<rect class="b-hot" x="300" y="0" width="120" height="60"/>
<line class="e" x1="120" y1="30" x2="300" y2="30" marker-end="url(#arrow)"/>
<path class="e-dash" d="M 0 80 C 40 120, 80 120, 120 80" fill="none" stroke-linecap="round"/>
<circle class="n-hot" cx="200" cy="100" r="5"/>
<ellipse cx="260" cy="100" rx="10" ry="5" fill="url(#fade)" stroke="currentColor" stroke-width="1.5"
stroke-dasharray="4 2" opacity="0.8"/>
<polyline class="w" points="300,100 320,110 340,100"/>
<polygon class="b-soft" points="360,90 380,110 400,90" fill-rule="evenodd"/>
<text class="t-lab" x="60" y="34" text-anchor="middle" dominant-baseline="middle">a<tspan baseline-shift="sub"
font-style="italic">i</tspan></text>
<text class="t-note" x="360" y="34" text-anchor="middle" font-weight="bold">b &amp; c</text>
</g>
</svg>
<figcaption>Two boxes, <code>a</code> and <code>b</code>. Hand-drawn by the writer.</figcaption>
</figure>

<figure data-figure="add-ripple" data-alt="The ripple carry chain.">
<figcaption>A figure the site draws.</figcaption>
</figure>
"""


class AllowedTest(unittest.TestCase):
    def test_everything_on_the_lists_is_accepted_and_sanitize_is_idempotent(self):
        once = safehtml.sanitize(ALLOWED)
        self.assertEqual(safehtml.sanitize(once), once)
        self.assertIn('<svg viewBox="0 0 480 160" xmlns="http://www.w3.org/2000/svg">', once)
        self.assertIn('<marker id="arrow" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="6"', once)
        self.assertIn("<clipPath", once)
        self.assertIn("<linearGradient", once)
        self.assertIn('<circle class="n-hot" cx="200" cy="100" r="5"/>', once)
        self.assertIn("<br>", once)

    def test_a_diff_against_the_parent_record_is_accepted(self):
        """Decided 2026-11-17 (CONTRIBUTING.md, "A record derived from another"): a writeup of a record derived from
        another shows the diff of the two design files in a code block. `diff -u`'s lines (---, +++, @@, the - and +
        lines, the context), with <, > and & written as references, are accepted, kept byte for byte (a context line's
        leading space included) and written back as the same text; with or without a language class."""
        diff = ("--- a/add_n.sv\n+++ b/add_mux.sv\n@@ -9,3 +9,3 @@\n"
                "   for (i = 0; i &lt; N; i++) begin : g_bit\n"
                "-    assign c[i+1] = (a[i] &amp; b[i]) | (c[i] &amp; (a[i] ^ b[i]));\n"
                "+    assign c[i+1] = (a[i] ^ b[i]) ? c[i] : a[i];\n"
                "   end\n")
        for cls in (' class="language-text"', ""):
            with self.subTest(cls=cls):
                body = (f"<p>Derived from record <code>e30d319a06ed</code>, one line changed:</p>\n"
                        f"<pre><code{cls}>{diff}</code></pre>")
                once = safehtml.sanitize(body)
                self.assertEqual(safehtml.sanitize(once), once)
                h = render(body)
                code = re.search(r"<pre\b[^>]*><code>(.*?)</code></pre>", h, re.S).group(1)
                self.assertEqual(code, diff)
                for line in ("--- a/add_n.sv", "+++ b/add_mux.sv", "@@ -9,3 +9,3 @@", "   end"):
                    self.assertIn("\n" + line + "\n", "\n" + code)
        # an unwritten < before a letter reads as a tag: refused with its line, never guessed (write &lt;)
        with self.assertRaises(safehtml.HtmlError):
            safehtml.parse("<pre><code>-  if (a<b) y = 1;\n</code></pre>", source="w.html")

    def test_the_committed_writeups_and_the_template_are_accepted_and_idempotent(self):
        n = 0
        for name in sorted(os.listdir(WRITEUPS)):
            if not name.endswith(".html"):
                continue
            with open(os.path.join(WRITEUPS, name), encoding="utf-8") as fh:
                title, body, first = writeup.split(fh.read())
            with self.subTest(writeup=name[:12]):
                once = safehtml.sanitize(body, source=name, first_line=first)
                self.assertEqual(safehtml.sanitize(once), once)
                n += 1
        self.assertGreater(n, 40)

    def test_an_authors_drawing_is_written_as_documented(self):
        h = render(ALLOWED, rules_href="../../../rules.html#figures-in-a-writeup")
        self.assertEqual(writeup.render(f"<h1>T</h1>\n\n{ALLOWED}\n", source="w.html")[1].count("<figure"), 2)
        f1 = h.split('<figure class="wfig" id="writeup-figure-1">')[1].split("</figure>")[0]
        # the site's class, role, labels and size; the writer's drawing unchanged otherwise
        self.assertIn('<div class="wfig-box"><svg class="wfig-svg" viewBox="0 0 480 160" width="480.0" height="160.0" '
                      'style="max-width:480.0px;min-width:320.0px" role="img" aria-labelledby="writeup-figure-1-t '
                      f'writeup-figure-1-d" xmlns="{S}"><title id="writeup-figure-1-t">Two boxes and an arrow.</title>'
                      '<desc id="writeup-figure-1-d">The left box feeds the right one.</desc><defs>', f1)
        # ids and their references in the figure's namespace
        self.assertIn('<marker id="writeup-figure-1-arrow"', f1)
        self.assertIn('marker-end="url(#writeup-figure-1-arrow)"', f1)
        self.assertIn('clip-path="url(#writeup-figure-1-clip)"', f1)
        self.assertIn('fill="url(#writeup-figure-1-fade)"', f1)
        self.assertNotRegex(f1, r'url\(#(?!writeup-figure-1-)')
        self.assertIn('<figcaption><span class="wfig-n">Figure 1.</span> Two boxes, <code>a</code> and <code>b</code>. '
                      "Hand-drawn by the writer.</figcaption>", f1)
        self.assertNotIn("generated from the design", f1)
        # the generated figure is Figure 2, with its credit line; links to both and to the section resolve
        self.assertIn('<span class="wfig-n">Figure 2.</span> A figure the site draws. <span class="wfig-credit">', h)
        self.assertIn('<a href="#writeup-figure-1">Figure\n1</a>', h)
        self.assertIn('<a href="#writeup-the-idea">a section</a>', h)
        self.assertIn('<div class="table-wrap"><table>', h)
        self.assertIn('<pre class="code" data-lang="lean"><code>', h)
        self.assertIn('<pre class="code"><code>plain &amp; simple</code></pre>', h)
        self.assertIn('<h4 id="writeup-lists-and-code">Lists <em>and</em> code <a class="anchor"', h)

    def test_a_narrow_or_wide_drawing_gets_its_size(self):
        for vb, lo in (("0 0 200 50", "200.0"), ("0 0 400 50", "320.0"), ("0 0 900 50", "600.0")):
            with self.subTest(viewBox=vb):
                h = render(fig("", vb=vb))
                w = vb.split()[2]
                self.assertIn(f'style="max-width:{float(w):.1f}px;min-width:{lo}px"', h)

    def test_white_space_between_blocks_is_one_newline(self):
        self.assertEqual(render("<p>a</p>\n\n\n<p>b</p>\n\n<ul>\n\n<li>x</li>\n\n</ul>"),
                         "<p>a</p>\n<p>b</p>\n<ul>\n<li>x</li>\n</ul>")


class DocumentedTest(unittest.TestCase):
    def test_every_drawing_class_has_its_colours_in_the_stylesheet(self):
        with open(os.path.join(SITE, "style.css"), encoding="utf-8") as fh:
            css = fh.read()
        for c in safehtml.SVG_CLASSES:
            with self.subTest(cls=c):
                self.assertRegex(css, r"svg\.wfig-svg \." + re.escape(c) + r"\b")
        with open(os.path.join(SITE, "figs", "svg.py"), encoding="utf-8") as fh:
            doc = fh.read().split('"""')[1]
        for c in safehtml.SVG_CLASSES:                 # (the generators' own list of the classes)
            self.assertRegex(doc, r"(?<![\w-])" + re.escape(c) + r"(?![\w-])")

    def test_the_rules_for_authors_state_the_allowlists(self):
        with open(os.path.join(SVGOLF, "README.md"), encoding="utf-8") as fh:
            readme = fh.read()
        sec = readme.split("### Writeups", 1)[1].split("\n## ", 1)[0]
        names = {safehtml._name(t) for t in safehtml.HTML_ELEMENTS | safehtml.SVG_ELEMENTS}
        classes = list(safehtml.SVG_CLASSES) + list(safehtml.PROSE_CLASSES) + list(safehtml.ALIGN_CLASSES)
        for n in sorted(names) + classes:
            with self.subTest(name=n):
                self.assertRegex(sec, r"`[^`]*\b" + re.escape(n) + r"\b[^`]*`")
        for limit in ("200 kB", "50 kB", "1200", "300 characters"):
            self.assertIn(limit, sec)

    def test_generated_figures_pass_the_audit(self):
        for name, f in sorted(figs.REGISTRY.items()):
            with self.subTest(figure=name):
                writeup.audit(f'<figure class="wfig" id="writeup-figure-1"><div class="wfig-box">'
                              f'{figs.svg_of(f, alt="a", uid="writeup-figure-1")}</div></figure>', source=name)


if __name__ == "__main__":
    unittest.main()
