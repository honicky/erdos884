#!/usr/bin/env bash
# Verify the amalgamated artifact Erdos884.lean with the Axle hosted Lean engine
# (https://axle.axiommath.ai), environment lean-4.31.0 (Lean 4.31.0 + Mathlib).
#
# Requirements:
#   pip install axiom-axle           # provides the `axle` CLI (Python >= 3.11)
#   export AXLE_API_KEY=...          # optional; anonymous access also works
#
# Reports okay / error count / failed_declarations and the axiom footprint of the
# main theorem. Exit status is nonzero if the proof does not check clean.
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
FILE="${1:-$ROOT/Erdos884.lean}"

axle --json check "$FILE" --environment lean-4.31.0 --timeout-seconds 540 > "$ROOT/.axle-result.json"

python3 - "$ROOT/.axle-result.json" <<'PY'
import json, sys
r = json.load(open(sys.argv[1]))
errs = r["lean_messages"]["errors"]
ok = r["okay"]
failed = r["failed_declarations"]
print("okay: %s  errors: %d  failed_declarations: %s" % (ok, len(errs), failed))
for e in errs[:20]:
    print("ERROR:", str(e)[:300])
for i in r["lean_messages"]["infos"]:
    if "axiom" in str(i):
        print(str(i)[:300])
sys.exit(0 if (ok and not errs and not failed) else 1)
PY
