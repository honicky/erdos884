#!/usr/bin/env bash
# Regenerate the single-file artifact Erdos884.lean from the modules in modules/,
# concatenated in dependency order (modules/ORDER). The modules carry no `import`
# lines; a single `import Mathlib` is prepended and each module is wrapped in an
# anonymous `section … end` so that `open`/`local notation` in one module cannot
# leak into the next.
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"
OUT="Erdos884.lean"

cat > "$OUT" <<'HEADER'
/-
# Erdős Problem 884 — a formal disproof (Lean 4 / Mathlib)

For a natural number n with divisors 1 = d₁ < ⋯ < d_τ = n, Erdős conjectured

    ∑_{i<j} 1/(d_j − d_i)  ≪  1 + ∑_i 1/(d_{i+1} − d_i)      (n → ∞).

This file proves the conjecture FALSE, formalizing Daniel Larsen's unconditional
disproof (https://github.com/Larsen-Daniel/Erdos-884/blob/main/884.pdf), which builds
on Terence Tao's conditional construction
(https://terrytao.wordpress.com/wp-content/uploads/2025/09/erdos-884.pdf).

Main theorem (statement identical to google-deepmind/formal-conjectures
FormalConjectures/ErdosProblems/884.lean, where `f ≪ g` denotes `f =O[Filter.atTop] g`):

    theorem Erdos884.erdos_884_disproof :
        ¬ (sumDivisorInvPairwiseDifference =O[Filter.atTop]
            (1 + sumDivisorInvConsecutiveDifference))

This file is AMALGAMATED from the modules in `modules/` by `scripts/amalgamate.sh`;
edit the modules, not this file. Verify with `scripts/verify.sh` (Axle, env lean-4.31.0):
0 errors, 0 sorries; `#print axioms` = [propext, Classical.choice, Quot.sound].

The first module (SieveVendored.lean) is vendored from PrimeNumberTheoremAnd
(https://github.com/AlexKontorovich/PrimeNumberTheoremAnd), © 2024 Arend Mellendijk,
Apache 2.0 — the fundamental theorem of the Selberg sieve. Its copyright headers are
retained inline. Everything else was produced for this formalization (July 2026).
-/
import Mathlib
HEADER

while IFS= read -r m; do
  [ -z "$m" ] && continue
  printf '\n/- ═════ MODULE: %s ═════ -/\nsection\n' "$m" >> "$OUT"
  grep -v '^import ' "modules/$m" >> "$OUT"
  printf '\nend\n' >> "$OUT"
done < modules/ORDER

printf '\n#print axioms Erdos884.erdos_884_disproof\n' >> "$OUT"
echo "Wrote $OUT ($(wc -l < "$OUT") lines)"
