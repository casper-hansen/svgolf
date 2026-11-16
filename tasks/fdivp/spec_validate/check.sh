#!/bin/bash
# Lean checks for the IEEE 754 division the fdivp statement names, Proglib's
# LeanModels.SoftFloat.Binary.divide, through the svgolf Lake project (run from anywhere):
#   1. `lake build tasks.fdivp.Spec`: the statement and the library's definitions it imports
#      (the statement's golden vectors and kernel `decide`s; the library's own differential rows
#      and five characterization theorems are its modules Tests and Characterization);
#   2. the batch runner Run.lean used by validate.py (compile only).
# Environment: LEAN_WRAP (optional command prefix, e.g. a slot-limiting wrapper).
set -euo pipefail
SVGOLF="$(cd "$(dirname "$0")/../../.." && pwd)"
WRAP=(${LEAN_WRAP:-})
cd "$SVGOLF"
echo "== spec: lake build tasks.fdivp.Spec"
"${WRAP[@]}" lake build tasks.fdivp.Spec
echo "== runner: tasks/fdivp/spec_validate/Run.lean"
"${WRAP[@]}" lake env lean tasks/fdivp/spec_validate/Run.lean
echo "OK"
