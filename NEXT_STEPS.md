# Next steps

Status: the disproof is **complete and verified**. `Erdos884.lean` checks green on
Lean 4.31.0 + Mathlib via the Axle hosted engine — 0 errors, 0 `sorry`, and
`#print axioms Erdos884.erdos_884_disproof` = `[propext, Classical.choice, Quot.sound]`
(the three standard Mathlib axioms only). The statement is token-identical to
[google-deepmind/formal-conjectures `ErdosProblems/884.lean`](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/884.lean).

What remains is optional, in rough order of value.

## 1. Local / offline reproducibility (Lake project) — recommended

Right now verification runs through Axle's hosted environment. For a build any third
party can reproduce offline, convert this into a Lake project pinned to Mathlib
`v4.31.0`:

- `lakefile.toml` (or `.lean`) with a `require mathlib` at rev `v4.31.0`, a
  `lean-toolchain` of `leanprover/lean4:v4.31.0`, and a `lake-manifest.json`.
- Give each module a real header (`import Mathlib`, plus `import Erdos884.<Dep>` for its
  in-repo dependencies, in the order encoded in `modules/ORDER`) instead of relying on
  concatenation. Move them under a source root (e.g. `Erdos884/`), and let the root
  `Erdos884.lean` `import` them all rather than textually inlining them.
- `elan` is already installed on this machine (`~/.elan/bin`). Expect a one-time Mathlib
  cache download (`lake exe cache get`) of a few GB; a cold `lake build` then takes tens
  of minutes.
- Keep `scripts/verify.sh` (Axle) as a fast secondary check; add `lake build` as the
  primary.

The amalgamated single file remains useful for pasting into
[live.lean-lang.org](https://live.lean-lang.org) and for the Axle check.

## 2. Upstream the result

- **PR to `google-deepmind/formal-conjectures`** resolving `erdos_884`: replace its
  `sorry` with the proof (or a `import` of this development), following the pattern used
  for problem 258 (`@[... formal_proof using lean4 at "<url>"]`). This is a public
  contribution under your name — prepare the branch/PR for review, but you push it.
- **Gist + live link**: publish `Erdos884.lean` as a gist and link it via
  `live.lean-lang.org/#project=mathlib-v4.31.0&url=<raw-gist-url>` so anyone can run it
  in-browser.
- **Notify [erdosproblems.com](https://www.erdosproblems.com/884)**, which tracks
  formalizations of solved problems.

## 3. Cosmetic polish (low value)

The machine-written modules contain some duplicated helper lemmas, two
`set_option maxHeartbeats` bumps (in `MultiScale884.lean`), and uneven docstrings.
Harmless to correctness; worth a cleanup pass only if the code is going to be read
closely (e.g. as part of item 2).

## 4. Maintenance (not actionable now)

- Delete `modules/SieveVendored.lean` and depend on Mathlib directly once the
  fundamental theorem of the Selberg sieve is upstreamed into Mathlib.
- Routine updates if you want the development to track newer Mathlib versions.

## Provenance / licensing note

`modules/SieveVendored.lean` is vendored from
[PrimeNumberTheoremAnd](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd)
(© 2024 Arend Mellendijk, Apache-2.0); its headers are retained. The repository is
licensed Apache-2.0 to stay consistent with that code and with formal-conjectures (also
Apache-2.0) — change `LICENSE` if you prefer a different license for the original
material.
