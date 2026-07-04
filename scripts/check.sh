#!/usr/bin/env bash
# Fast incremental checker: concatenate the given module files (from modules/, or
# absolute/relative paths) in the order given, prepend a single `import Mathlib`,
# wrap each in an anonymous `section … end` so opens/notations don't leak, and check
# the result with Axle (env lean-4.31.0). Use during development to check a subset of
# modules without amalgamating/compiling the whole file.
#
#   scripts/check.sh Prelude884.lean DivisorsProd884.lean        # names resolve under modules/
#   scripts/check.sh $(cat modules/ORDER)                        # whole thing
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
TMP="$(mktemp -t erdos884check).lean"
trap 'rm -f "$TMP"' EXIT

JSON="$(mktemp -t erdos884json).json"
trap 'rm -f "$TMP" "$JSON"' EXIT

echo "import Mathlib" > "$TMP"
for f in "$@"; do
  [ -f "$f" ] || f="$ROOT/modules/$f"
  printf '\n/- ===== %s ===== -/\nsection\n' "$(basename "$f")" >> "$TMP"
  grep -v '^import ' "$f" >> "$TMP"
  printf '\nend\n' >> "$TMP"
done

axle --json check "$TMP" --environment lean-4.31.0 --timeout-seconds 540 > "$JSON"
python3 - "$JSON" <<'PY'
import json, sys
r = json.load(open(sys.argv[1]))
errs = r["lean_messages"]["errors"]
print("okay: %s  errors: %d  failed_declarations: %s"
      % (r["okay"], len(errs), r["failed_declarations"]))
for e in errs[:25]:
    print("ERROR:", str(e)[:350].replace(chr(10), " "))
PY
