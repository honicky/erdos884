# Next steps

Status: the disproof is **complete and verified**, two independent ways (offline
`lake build` against Mathlib `v4.31.0`, and the Axle hosted engine) — 0 errors, 0
`sorry`, and `#print axioms Erdos884.erdos_884_disproof` =
`[propext, Classical.choice, Quot.sound]` (the three standard Mathlib axioms only). The
statement is token-identical to
[google-deepmind/formal-conjectures `ErdosProblems/884.lean`](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/884.lean).

What remains is optional, in rough order of value.

## 1. Offline reproducibility (Lake project) — DONE

The repo is a Lake project pinned to Mathlib `v4.31.0` (`lakefile.toml`,
`lean-toolchain`, `lake-manifest.json`). `lake build` compiles `Erdos884.lean` offline
against the cached Mathlib and reports the axiom footprint — see the README "Offline
build" section. No further action required for basic offline reproducibility.

**Optional refinement — multi-file library.** The Lake target is currently the single
amalgamated file `Erdos884.lean` (one big compilation unit). For faster incremental
builds and more idiomatic structure, split it into a real multi-file library: give each
`modules/*.lean` a header (`import Mathlib` plus `import Erdos884.<Dep>` for its in-repo
dependencies, in the order in `modules/ORDER`), move them under `Erdos884/`, and have the
root `Erdos884.lean` `import` them instead of textually inlining. The amalgamated file
stays useful for [live.lean-lang.org](https://live.lean-lang.org) and the Axle check.

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
