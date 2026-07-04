# Blueprint: Lean formalization of Larsen's disproof of Erdős #884

Target theorem (matching google-deepmind/formal-conjectures `ErdosProblems/884.lean`):

```
¬ (sumDivisorInvPairwiseDifference =O[Filter.atTop] (1 + sumDivisorInvConsecutiveDifference))
```

as functions `ℕ → ℝ`, where for `n` with divisors `1 = d_1 < … < d_τ = n`:
- `T(n) := Σ_{i<j} 1/(d_j − d_i)`  (`sumDivisorInvPairwiseDifference`)
- `S(n) := Σ_i 1/(d_{i+1} − d_i)`  (`sumDivisorInvConsecutiveDifference`)

Source: Daniel Larsen, *A question of Erdős on reciprocals of gaps between divisors* (884.pdf),
using Tao's note (tao_erdos884.pdf) for eq. (1.2) and Lemma 2.2. We follow Larsen's multiscale
construction with several formalization-friendly modifications (documented inline below):
interval [t,2t] → (t,8t] (Chebyshev constants), all-pairs bounds instead of consecutive-pairs
wherever possible, explicit `K_i ≈ log t_i / ((i+C)·loglog t_i)` instead of log*.

Verification: every file must compile with **zero errors and zero sorries** under Axle
environment `lean-4.31.0`, single import `import Mathlib` (plus vendored sieve file).

## Internal definitions (Defs.lean)

For `A : Finset ℕ`:
- `pairSum A : ℝ := Σ_{(x,y) ∈ A×A, x < y} 1/((y:ℝ) − x)`   -- "T(A)"
- `gapSum A : ℝ` := sum of `1/(next − cur)` over consecutive pairs of the sorted list of `A`. -- "S(A)"
  Implementation: `l := A.sort (·≤·)`, `gapSum := ((l.zip l.tail).map (fun p => ((p.2:ℝ) − p.1)⁻¹)).sum`.
- Both are ≥ 0 for sets of naturals (sorted list strictly increasing).
- Bridge (Main.lean): for `n ≠ 0`, `sumDivisorInvPairwiseDifference n = pairSum n.divisors`,
  `sumDivisorInvConsecutiveDifference n = gapSum n.divisors` (via `Nat.nth (· ∣ n)` =
  increasing enumeration of `n.divisors`).

Key structural facts:
- `pairSum_nonneg`, `gapSum_nonneg`.
- **Superadditivity**: if `B₁,…,B_r` are pairwise disjoint subsets of `A`, then
  `Σ pairSum B_i ≤ pairSum A` (pairs within distinct `B_i` are distinct pairs of `A`; all terms ≥ 0).
- **Consecutive-pair decomposition**: if `f : (ℕ×ℕ) → Prop`-classes partition all pairs (x<y) of `A`,
  then `gapSum A ≤ Σ_classes (sum over ALL class pairs of 1/(y−x))` — since each consecutive pair
  is a pair. (Trivial but central: lets us bound S by all-pairs sums class by class.)
- Consecutive pairs of `A` restricted to an interval `[a,b]` with `A ∩ [a,b] = B`: consecutive pairs
  of `A` with both endpoints in `B` are consecutive pairs of `B`.

## Lemma A — Chebyshev count (Chebyshev884.lean)

`∃ T_A ≥ 3, ∀ t : ℝ ≥ T_A : 2·t/Real.log t ≤ #{p prime, t < p ≤ 8t}` (constant 2, wide margin)
(card of `Finset.filter Nat.Prime (Finset.Ioc ⌈t⌉₊ ⌊8t⌋₊)` — fix cast details as convenient).

Proof: Mathlib `Chebyshev.pi_ge'` at `8t`: `π(⌊8t⌋) ≥ ((8t−1)log2 − log(8t+2))/log(8t)`;
`Chebyshev.eventually_primeCounting_le` with `ε = 1/10`: `π(⌊t⌋) ≤ (log4 + 1/10)·t/log t` eventually.
Count = π(⌊8t⌋) − π(⌊t⌋) ≥ [8log2·(log t/log 8t) − o(1) − log4 − 1/10]·t/log t → (6log2 − 0.1)·t/log t
> 2t/log t with ~2x margin. Package as an `∃ T_A` statement via `Filter.eventually_atTop`.

## Lemma B — prime-pair bound (PairSieve.lean, SingularAvg.lean, PairCount.lean) [CRITICAL PATH]

`∃ C_B ≥ 1, T_B, ∀ t ≥ T_B, ∀ N : ℕ, 2 ≤ N → (N:ℝ) ≤ (log t)^2 →`
`  #{(p,q) : p < q ≤ 9t, p,q prime, q − p ≤ N} ≤ C_B · N · t / (log t)^2`

Decompose over gap h = q − p ∈ [1,N]:
- h odd: p,p+h both prime forces p = 2 (parity): ≤ 1 pair per h → total ≤ N. (elementary)
- h even, h ≥ 2: Selberg sieve (vendored `SieveVendored.lean`, namespace as in PNT&):
  * Sieve instance (model: `BrunTitchmarsh.primeInterSieve`): support `Finset.Icc 1 M`, `M := ⌈9t⌉₊`,
    weights 1, totalMass M, level `y := t^(1/2)`, prodPrimes `primorial ⌊z⌋` with `z := √y = t^(1/4)`,
    `nu` = multiplicative arithmetic function `ν(d) = ρ_h(d)/d`, where `ρ_h` is multiplicative,
    `ρ_h(p) := if p ∣ h then 1 else 2` on primes (number of roots of X(X+h) ≡ 0 mod p).
    Checks: `ν(p) ∈ (0,1)` for all primes (p=2: h even → ρ=1, ν=1/2; p≥3: ν ≤ 2/3 wait ρ(3)=2,ν=2/3<1 ✓).
  * `multSum d = #{n ∈ [1,M] : d ∣ n(n+h)}`; per squarefree d: `|multSum d − ν(d)·M| ≤ ρ_h(d) ≤ 2^ω(d)`
    (CRT: ρ_h(d) residues mod d, each contributing M/d ± 1).
  * `errSum ≤ Σ_{d ≤ y} 3^ω(d)·2^ω(d) ≤ Σ_{d≤y} τ_6-style ≤ y·(1+log y)^5` (TauBound.lean:
    `Σ_{d≤y} k^ω(d) ≤ Σ_{d≤y} τ_k(d) ≤ y(1+log y)^(k−1)` by induction on k via
    `τ_k = Σ_{ab=d} τ_{k−1}(a)`; only k = 6 needed, can hardcode).
  * If p,p+h both prime and p > z then p survives sieving → `pairs_h ≤ siftedSum + z`.
  * `selberg_bound_simple`: `siftedSum ≤ M/S_h + errSum` where `S_h := selbergBoundingSum`.
  * **Bounding sum lower bound (dimension 2)**: `S_h ≥ Σ_{ℓ ≤ √y, squarefree, coprime to 2h} 2^ω(ℓ)/ℓ`
    (from `selbergBoundingSum_ge_sum_div` + `g(p) ≥ ν(p) ≥ 2/p` for p ∤ 2h — read exact vendored form!)
    `≥ (Σ over coprime pairs a,b ≤ w, w := y^(1/4)) ≥ c₀·(φ(2h)/(2h))²·(log w)²`. Suggested route:
    2^ω(ℓ) = #ordered coprime factorizations ℓ=ab; restrict to a,b ≤ w;
    `Σ_{a ≤ w, sqfree, (a, 2hb)=1} 1/a ≥ (φ(2hb)/(2hb))·c·log w` — uniform elementary bound: any route OK, e.g.
    Σ_{a≤w,(a,m)=1} 1/a ≥ (φ(m)/m)·(log w)/2 − 1 for w ≥ w₀ via counting integers coprime to m in dyadic blocks
    (#{a ≤ x, (a,m)=1} ≥ x·φ(m)/m − 2^ω(m)-type is UNBOUNDED in m — instead use:
     Σ_{a ≤ w, (a,m)=1} 1/a ≥ Σ_{a≤w} 1/a · φ(m)/m via the exact identity
     Σ_{a≤w,(a,m)=1} 1/a ≥ Σ_{d|m} μ(d)/d · ⌊…⌋ — Möbius over the full harmonic sum; error Σ_{d|m}|μ(d)|·(1/d + 1/w·…);
     needs care, an easier uniform variant: restrict m squarefree z-smooth and use
     Σ_{a≤w,(a,m)=1}1/a ≥ ∏_{p≤log w}(local) — LEAVE FLEXIBLE, target statement fixed below).
    **Target statement (B.3)**: `∃ c₀ > 0, w₀, ∀ w ≥ w₀, ∀ m ≥ 1 (m = 2h ≤ 2(log t)² ≤ (log w)³):`
    `Σ_{ℓ ≤ w, sqfree, (ℓ,m)=1} 2^ω(ℓ)/ℓ ≥ c₀·(φ(m)/m)²·(log w)²`. (May assume m ≤ (log w)^3.)
  * **(B.4)**: `Σ_{h=1}^{N} (h/φ(h))² ≤ 200·N` for all N ≥ 1. Route: h/φ(h) = Σ_{d∣h} μ²(d)/φ(d);
    expand square, swap sums: ≤ N·Σ_g μ²(g)/(g·φ(g)²)·(Σ_a μ²(a)/(a·φ(a)))²; converging sums bounded
    crudely via φ(k) ≥ √(k/2) and Σ 1/k^(3/2). Also `Σ_{h≤N}(2h/φ(2h))² ≤ 4·Σ_{h≤N}(h/φ(h))²`.
  * Assemble: pairs_h ≤ 9t·(2h/φ(2h))²·(16/c₀)/(log t)² + y·(1+log y)^5 + z. Sum over even h ≤ N.
    Total ≤ C_B·N·t/(log t)² for t ≥ T_B (absorb N·(y polylog + z) ≤ (log t)²·t^(1/2)·polylog ≪ t/(log t)²·N… wait
    N ≥ 2 and t/(log t)² dominates t^(1/2+ε): ✓).

## Lemma C — selection of separated primes (Selection.lean)

Input: Lemma A, Lemma B. Let `ε := 1/(4·C_B)`, `N := ⌈ε·log t⌉`, `H := ⌈6·K·log t⌉`.
`∃ T_C, ∀ t ≥ T_C, ∀ K : ℕ, 2 ≤ K → (K:ℝ) ≤ log t/(loglog t)² →`
`∃ B : Finset ℕ, B ⊆ primes, |B| = K, B ⊆ Ioc x (x + H) for some real/nat x ∈ [t, 8t],`
`∀ p ≠ q ∈ B, N < |p − q|.`

Proof: primes in (t,8t] ≥ 2t/log t (A). Small-gap pairs (in (0,9t], superset) ≤ C_B·N·t/(log t)²
≤ C_B(εlog t + 1)t/(log t)² ≤ t/(2·log t) for εlog t ≥ 1.
Greedy within the whole interval, windowed pigeonhole:
partition (t, 8t] into ⌈7t/H⌉ ≤ 8t/H windows of length H; in each window keep a maximal
N-separated subset greedily (sorted walk); every discarded prime pairs with the previously kept
prime at gap ≤ N, injectively → total kept ≥ 2t/log t − t/(2log t) = (3/2)·t/log t.
Some window has kept-count ≥ ((3/2)t/log t)/(8t/H) = 3H/(16 log t) ≥ (9/8)K ≥ K (H = ⌈6K log t⌉). Take the K least.

## Lemma D — energy lower bound, Tao (1.2) (Energy.lean)

For finite `A ⊆ ℕ`, `k := |A| ≥ 4`, contained in a closed interval of length `H' ≥ 1`:
`pairSum A ≥ k²·log(k/2)/(4·H')`.
Proof (chains): for index-distance m ≤ k/2, split indices into m arithmetic chains; per chain,
consecutive-in-chain gaps telescope to ≤ H', AM–HM (`Finset.inner_mul_le_norm_mul_norm` not needed —
`div_add_div_same`, or `Finset.sq_sum_le_card_mul_sum_sq`-style; easiest: for positive reals with
Σ g_i ≤ H', Σ 1/g_i ≥ L²/H' via Cauchy–Schwarz `(Σ 1)² ≤ (Σ g)(Σ 1/g)`, Mathlib
`Finset.inner_mul_le_norm_mul_norm` or `Finset.sum_div_pow_mul_fract…` — use
`Finset.sq_sum_le_card_mul_sum_sq`? Simplest: `(Σ_i 1)^2 = (Σ_i √g·(1/√g))^2 ≤ (Σ g)(Σ 1/g)`
via `Finset.inner_mul_le_norm_mul_norm` or direct `Finset.sum_mul_sq_le_sq_mul_sq`).
Then Σ_{pairs at distance m} 1/gap ≥ (Σ_r (L_r − 1))²/(m·H') = (k−m)²/(m·H') (Cauchy–Schwarz over r).
Sum m = 1..⌊k/2⌋: ≥ (k/2)²/H' · Σ_{m≤k/2} 1/m ≥ (k²/4H')·log(k/2).
(Indices via `A.orderIsoOfFin`/`orderEmbOfFin` with `A.sort`.)

## Lemma E — separated gap sum (Basic.lean)

`A` finite, all pairwise gaps > N ≥ 1: `gapSum A ≤ (|A| − 1)/N`.

## Lemma F — polynomial gap bound, Tao Lemma 2.2, elementary (PolyGap.lean)

Work with real product functions, not `Polynomial`:
`P a x := ∏_{i} (x − a i)` over `Finset`/sorted lists.
(F1) If `x ≥ y ≥ max a` then `P a x − P a y ≥ (x − y)·∏_{i < k−1?}` — precise form:
for a multiset/list of reals all ≤ y: `P a x − P a y ≥ (x − y) · ∏_{i}(y − a i) / (y − a_max)`…
cleanest inductive statement: for lists `l` of reals, all elements ≤ y ≤ x:
`(∏_{a∈l}(x−a)) − (∏_{a∈l}(y−a)) ≥ (x−y)·∏_{a∈l.erase (max)}(y−a)` — DESIGN as:
`prodShift_sub_ge : ∀ (l : List ℝ) (hly : ∀ a ∈ l, a ≤ y) (hxy : y ≤ x),`
`  ∏(x−a) − ∏(y−a) ≥ (x−y)·(∏ over l minus one largest element)(y−a)`…
Simplest robust pair of lemmas:
  (F1a) monotone: `y ≤ x, ∀a∈l, a ≤ y ⟹ 0 ≤ ∏(y−a) ≤ ∏(x−a)`. (induction)
  (F1b) `∀ a∈l, a ≤ y ⟹ ∏_{a∈l}(x−a) − ∏_{a∈l}(y−a) ≥ (x−y)·∏_{a∈l'}(y−a)` where `l = a₀ :: l'`
        any decomposition (induction on l: use F1a; the head factor plays the (x−a₀) role).
        [Check: ∏ = (x−a₀)∏_{l'}(x−a) − (y−a₀)∏_{l'}(y−a) = (x−y)∏_{l'}(x−a) + (y−a₀)(∏_{l'}(x)−∏_{l'}(y))
         ≥ (x−y)∏_{l'}(y−a) by F1a twice. ✓ head can be ANY element.]
(F2) sign: reals `b : Fin k → ℝ` with all `b i ≤ M`: `0 ≤ ∏(M − b i)`.
(F3) MAIN: `a b : Fin k → ℝ` strictly increasing (or Finsets of size k), `k ≥ 1`, and
`∀ x, ∏(x − a i) = ∏(x − b i) + ℓ` with `ℓ > 0`. Then `b_max > a_max` and
`ℓ ≥ (b_max − a_max)·∏_{i : a i ≠ a_max}(a_max − a i)`.
Proof: evaluate at `b_max`: `P_a(b_max) = ℓ > 0`; if `b_max ≤ a_max`, evaluate at `a_max`:
`P_b(a_max) = −ℓ < 0` but all `b i ≤ b_max ≤ a_max` gives `P_b(a_max) ≥ 0` (F2), contradiction.
Then `ℓ = P_a(b_max) − P_a(a_max) ≥ (b_max − a_max)·∏_{i<max}(a_max − a i)` by F1b (head = a_max factor).
(F4) Coefficient/nonconstant-difference bound (for class G1): for `s ≠ s'` size-k subsets of
naturals in (x₀, x₀+H], products `d = ∏ s`, `d' = ∏ s'`; if the difference of the two degree-k
monic polynomials `∏_{p∈s}(X + (p − x₀))` is NOT constant then `|d − d'| ≥ x₀/2`, provided
`(2H)^K·16H ≤ x₀`. Suggested formal route (avoids `Polynomial` entirely):
d − d' as an integer; work instead with the DIRECT argument: let e_j := elementary symmetric sums.
`d = Σ_j e_j(h_s)·x₀^{k−j}` (h_p := p − x₀ ∈ (0,H]). If e_j(h_s) = e_j(h_{s'}) for all j < k then
difference is constant (= e_k difference). Otherwise take smallest j* with e_{j*} ≠ e'_{j*} (j* ≥ 1
since e_0 = 1; j* ≤ k−1… careful j* could = k → constant case): |d − d'| ≥ x₀^{k−j*}·(1 − Σ_{j>j*}…)
≥ x₀^{k−j*}/2 ≥ x₀/2 using |e_j| ≤ C(k,j)H^j ≤ (2H)^j… wait C(k,j)H^j ≤ 2^k H^j ≤ (2H)^j only if 2^k ≤ 2^j — FALSE for j<k.
Use |e_j| ≤ C(k,j)H^j ≤ 2^K·H^j: Σ_{j>j*}|e_j − e'_j|x₀^{k−j} ≤ 2·2^K·Σ_{j>j*}H^j x₀^{k−j}
≤ 4·2^K·H^{j*+1}x₀^{k−j*−1} (geometric, H/x₀ ≤ 1/2) ≤ x₀^{k−j*}·[4·2^K·H^{j*+1}/x₀ ≤ 4·2^K H^K·H/x₀] ≤ x₀^{k−j*}/2
when `8·2^K·H^{K+1} ≤ x₀`. So hypothesis: `8·(2H)^{K+1} ≤ x₀` (implies the above). e_j over ℤ or ℝ: use
`Finset.esymm` (Mathlib `Finset.esymm`, `Multiset.esymm`) with `Finset.prod_X_add_C_eq_sum_esymm`-style identity —
Mathlib has `Finset.prod_add` / `MvPolynomial.esymm`… the cleanest: `Finset.prod_one_add?`
For products of (x₀ + h_p): identity `∏_{p∈s}(x₀ + h_p) = Σ_{u ⊆ s} x₀^{|s|−|u|}·∏_{p∈u} h_p`
(Mathlib: `Finset.prod_add` gives ∏(f i + g i) = Σ over subsets — with f := const x₀, g := h — EXISTS as
`Finset.prod_add : ∏ i in s, (f i + g i) = Σ t in s.powerset, (∏ i in t, f i) * ∏ i in s \ t, g i`). Then
e_j-difference = Σ over j-subsets: group by size: d − d' = Σ_j x₀^{k−j}·(E_j(s) − E_j(s')) with
E_j := Σ_{u⊆s, |u|=j} ∏_{p∈u}(p − x₀) — naturals! E_j ≤ C(k,j)H^j ≤ 2^K H^j. Same argument, all in ℕ/ℝ. ✓

## Lemma G — same-ω pairs, one scale (OneScale.lean)

Setting: `B` finset of primes, `|B| = K ≥ 2`, `B ⊆ Ioc x₀ (x₀+H)` (naturals), pairwise gaps > N,
`m := ∏_{p∈B} p`, hypotheses `8·(2H)^{K+1} ≤ x₀`, `N ≥ 8·(⌈log₂(4H/N)⌉ + 1) =: N ≥ 8J`-ish.
Divisor structure: `d ∣ m ↔ d = ∏ s, s ⊆ B` (bijection `s ↦ ∏ s` from powerset to divisors;
Mathlib route: induction via `Nat.Coprime.divisors_mul` or `Nat.ArithmeticFunction` — build helper:
`divisorsProdPrimes : (∏ p∈B, p).divisors = B.powerset.image (fun s => ∏ p∈s, p)` + injectivity +
`ω(∏ s) = |s|` (`Nat.ArithmeticFunction.cardDistinctFactors`, or track directly by the bijection).
CLAIM (all-pairs where both same-#factors ≥ 2 is NOT what we sum — we sum over *consecutive divisor
pairs* whose subsets have equal size k ≥ 2):
`Σ_{(d1,d2) consecutive divisors of m, ω(d1)=ω(d2)≥2} 1/(d2−d1) ≤ 2·4^K/x₀ + 8·K·J/N²`
where `J := ⌈log₂(4H/N)⌉ + 1`.
Proof:
- consecutive ⟹ map `(d1,d2) ↦ s(d1)` injective (each divisor has ≤1 successor).
- Class G1 (poly difference nonconstant): gap ≥ x₀/2 by F4; #pairs ≤ (#divisors)² = 4^K; contribution ≤ 2·4^K/x₀.
- Class G2 (difference = positive constant ℓ): by F3 (roots −h_p… or apply F3 with the (X+h) form
  translated: use a i := −h_{p_i}? cleaner: apply F3 to polynomials in variable x shifted:
  state F3 for products ∏(x − a_i) with a_i := −h_p REAL; then a_max = −h_min(s)).
  ℓ ≥ (h_min(s) − h_min(s'))·∏_{p ∈ s \ {min}} (h_p − h_min(s)) ≥ N·D(s), D(s) := ∏_{p∈s\{min s}}(h_p − h_min(s)).
  For the consecutive pair (d1, d2): d2 − d1 = SOME constant difference for s := s(d1) → d2 − d1 ≥ N·D(s)... 
  wait: F3 orientation: d2 > d1, d2 − d1 = ℓ = P_{s(d2)} − P_{s(d1)} constant… P_{s(d2)}(x₀) = d2. So with
  a := roots of P_{s(d2)}?? CAREFUL: `P_a − P_b = ℓ > 0` in F3 has a = the LARGER product's root set = s(d2)-derived,
  b = s(d1)-derived. Conclusion: ℓ ≥ (b_max − a_max)·∏(a_max − a_i) with a-set from d2! I.e.
  d2 − d1 ≥ (h_min(s(d1)) − h_min(s(d2)))·D(s(d2)) ≥ N·D(s(d2)). And (d1,d2) ↦ s(d2) is ALSO injective
  on consecutive pairs (each d2 has ≤ 1 predecessor). Use predecessor-injectivity.
- Dyadic count: Σ over s (|s| = k, 2 ≤ k ≤ K) of 1/(N·D(s)) ≤ K·(4^{k−1}J^{k−1})/N^k summed:
  each factor (h_p − h_min(s)) lies in [N, H] wait ≥ N+1 > N ≥ 1 and ≤ H; dyadic shell
  2^{i_j} ≤ · < 2^{i_j+1}, N ≤ 2^{i_j+1}… shells indexed i with 2^i ∈ [N/2, H]: ≤ J values;
  given shells, #choices of the k−1 non-min elements ≤ ∏_j (2^{i_j+1}/N + 1) ≤ ∏ (2^{i_j+2}/N);
  #choices of min ≤ K. D(s) ≥ ∏ 2^{i_j}. Total per (k, shells): K·∏(4·2^{i_j}/N) / (N·∏2^{i_j}) = K·4^{k−1}/N^k.
  Σ over shells: J^{k−1} choices; Σ over k ≥ 2: K/N·Σ_{k≥2}(4J/N)^{k−1} ≤ K/N·(8J/N) if 4J/N ≤ 1/2. = 8KJ/N².

## Lemma H — different-ω pairs, one scale (OneScale.lean)

Same setting, plus `9^K·... : (x₀+H)^K ≤ x₀^K·2^{?}` — hypothesis `(2·(x₀+H))^{K} ≤ x₀^{K+1}/2`-ish;
concretely need: d1 < d2 ∣ m, ω(d1) ≠ ω(d2) ⟹ d2 ≥ 2·d1 (then Σ over ALL such pairs of 1/(d2−d1)
≤ Σ_{d2} 2^K·2/d2 ≤ 2^{K+1}·Σ_{1<d∣m}1/d ≤ 2^{K+1}·(2K/x₀) taking Σ_{1<d∣m}1/d ≤ exp(K/x₀)−1 ≤ 2K/x₀).
d1 < d2 forces ω1 < ω2 and d2/d1 ≥ x₀^{ω2}/(x₀+H)^{ω1} ≥ x₀/(1+H/x₀)^K ≥ x₀/2 ≥ 2 under mild hyps
((1+H/x₀)^K ≤ 2 given KH ≤ x₀/2… (1+u)^K ≤ exp(KH/x₀) ≤ 2 for KH ≤ x₀/2·log2… hypothesis `2KH ≤ x₀`).
Includes pairs with d1 = 1 (ω = 0).
Total: `Σ_{(d1,d2): d1<d2∣m, ω(d1)≠ω(d2)} 1/(d2−d1) ≤ 2^{K+3}·K/x₀`.

## Lemma I — one-scale package (OneScale.lean)

Given t ≥ T_I and K with `C_K ≤ log K` and `K ≤ log t/(loglog t)²` (C_K absolute, fixed so that
48·C_B/log K ≤ 1/4 etc.): B from Lemma C, m := ∏B. Then with L := log t:
- (I.T) `pairSum B ≥ K·log(K/2)/(16·L)`  [Lemma D, H ≤ 4KL]
- (I.S) `gapSum (m.divisors) ≤ K/N + 2·4^K/t + 8KJ/N² + 2^{K+3}K/t ≤ (25/(ε·log K))·C_B-ish·pairSum B`…
  package target: `gapSum (m.divisors) ≤ (200·C_B/log K)·pairSum B + 1/t^{1/4}`. (Constants generous;
  verify: K/N ≤ 2C_B·K/L; pairSum B ≥ K·logK/(32L) for K ≥ 4 ⟹ K/N ≤ 64·C_B/logK·pairSum B. The
  4^K/t etc. terms ≤ t^{−1/4} for K ≤ L/(LL)² and t large.)
- Every consecutive-divisor-pair class covered: (prime,prime) → consecutive in B → gaps > N →
  ≤ (K−1)/N; same-ω≥2 → Lemma G; different-ω → Lemma H.
- Also export: `m` squarefree, `ω(m) = K`, all prime factors in (t, 9t), `m ≤ (9t)^K`,
  `Σ_{1<d∣m} 1/d ≤ 2K/t`, `pairSum B ≥ 1/(32·(i+C))`-form happens at MultiScale.

## Lemma J — multiscale (MultiScale.lean)

Scale sequence: fix parameters at scale i via `t_{i+1} := ⌈Real.exp (t_i)⌉` (naturals), t_1 := T_*.
`K_i := ⌈L_i/((i+C₁)·LL_i)⌉` (L_i := log t_i, LL_i := log L_i), N_i, H_i, B_i, m_i from Lemma C/I.
n_r := ∏_{i≤r} m_i. Facts:
(J0) m_i pairwise coprime (prime factors in disjoint intervals (t_i, 9t_i), 9t_i < t_{i+1}).
     n_{i−1} < t_i^{1/4}-ish: log n_{i−1} ≤ Σ_{j<i} 2K_jL_j ≤ 3L_{i−1}² ≤ √L_i for towers.
(J1) `Σ_{d ∣ n_{i−1}} 1/d ≤ 2`.
(J2) `gapSum ((n_r).divisors) ≤ 1 + Σ_{i≤r} 2·SB_i` where SB_i := the one-scale bound (I.S RHS).
     Classes on divisor pairs d1<d2 of n_r (d^i := gcd-with-m_i component; via divisors-of-coprime-product
     equiv `Nat.divisorsEquiv`? build: d ∣ ∏m_i ↔ d = ∏ d^i, d^i ∣ m_i — `Nat.Coprime.divisors_mul` iterated):
     (a) ∃ scale with ω(d1^j) ≠ ω(d2^j): all-pairs bound Σ ≤ Σ_ℓ 4^{2K_ℓ}·2/t_ℓ·r? — organize by
         ℓ := largest active scale: Σ ≤ Σ_{ℓ≤r} (#pairs of divisors of n_ℓ)·(2/t_ℓ) ≤ Σ_ℓ 4^{Σ_{j≤ℓ}K_j}·2/t_ℓ
         ≤ Σ_ℓ t_ℓ^{1/4}·2/t_ℓ ≤ Σ_ℓ 2·t_ℓ^{−1/2} ≤ 1/2.
         Gap lower bound: |log(d2/d1)| ≥ L_i − 1 − 2√L_i − Σ_{j>i}t_j^{−1/3} ≥ 1 where i := largest ω-differing
         scale — pieces: same-ω scales j>i: |Δ_j| ≤ K_j·(H_j/t_j) ≤ t_j^{−1/3}; scales < i: |Δ_j| ≤ 2·log n_{i−1} ≤ 2√L_i;
         scale i: |Δ_i| ≥ log(t_i)·|ω-diff| − K_i·(H_i/t_i) ≥ L_i − 1. WLOG-side: take d2/d1 or d1/d2…
         both d's ≥ 1; conclude d2 − d1 ≥ max(d1,d2)·(1 − e^{−1}) ≥ t_ℓ/2.
     (b1) same-ω everywhere; i := smallest differing scale; some scale > i active:
         |Δ_i| ≥ (1/2)(9t_i)^{−K_i} vs Σ_{j>i}|Δ_j| ≤ t_{i+1}^{−1/3}·2 ≤ (1/4)(9t_i)^{−K_i};
         d2−d1 ≥ t_ℓ·(1/8)(9t_i)^{−K_i}; count ≤ 4^{Σ_{j≤ℓ}K_j} ≤ t_ℓ^{1/4}; Σ over i<ℓ≤r ≤ Σ_ℓ ℓ·8·e^{2L_i²}·t_ℓ^{−3/4}
         ≤ Σ_ℓ 8·ℓ·t_ℓ^{−1/2} ≤ 1/2.
     (b2) same-ω everywhere, differing only at scale i, nothing active above: d1 = e·a, d2 = e·b,
         e ∣ n_{i−1}, a<b ∣ m_i, ω(a)=ω(b): consecutive-in-div(n_r) ⟹ (a,b) consecutive in div(m_i);
         Σ ≤ (Σ_{e∣n_{i−1}} 1/e)·(same-ω part of gapSum-classes of m_i) ≤ 2·SB_i.
(J3) `pairSum ((n_r).divisors) ≥ Σ_{i≤r} pairSum B_i ≥ Σ_{i≤r} 1/(32(i+C₁)) ≥ (1/32)·log((r+C₁+1)/(C₁+1))`.
(J4) per-scale: SB_i ≤ δ_i·pairSum B_i + t_i^{−1/4}, δ_i := 200·C_B/log K_i, δ_i → 0 monotone-ish;
     Σ_i t_i^{−1/4} ≤ 1.
(J5) Assembly: ∀ C > 0, ∃ r₀, ∀ r ≥ r₀: pairSum(div n_r) > C·(1 + gapSum(div n_r)).
     Via A_r := Σ_{i≤r}pairSum B_i → ∞ and 1 + gapSum ≤ 4 + δ₁A_{i₁} + δ_{i₁}A_r; pick i₁ with δ_{i₁} ≤ 1/(4C),
     then r₀ with A_{r₀} ≥ 4C·(4 + δ₁·A_{i₁}).
Also n_r strictly increasing (n_{r+1} = n_r·m_{r+1}, m ≥ 2).

## Main assembly (Main.lean)

- Bridge lemmas K: `sumDivisorInvPairwiseDifference n = pairSum n.divisors` (n ≠ 0), same for S/gapSum.
  Via `Nat.nth (· ∣ n)` vs sorted divisors: `Nat.nth_count`-family, or
  `Finset.orderIsoOfFin`. Both sums: reindex `Fin card ↔ sorted list`.
- `theorem erdos_884 : ¬ (sumDivisorInvPairwiseDifference =O[Filter.atTop] (1 + sumDivisorInvConsecutiveDifference))`:
  unfold `Asymptotics.isBigO_iff`; obtain C; specialize eventual bound to n_r for r large (n_r → ∞ monotone);
  contradiction with J5 (mind ‖·‖ = |·|; T, S ≥ 0; ‖1 + S‖ = 1 + S ≥ 0 ✓).
- Optionally restate with the verbatim formal-conjectures `abbrev`s + `≪` notation for exact matching.

## Absolute constants ledger

C_B (pair sieve), ε := 1/(2C_B), C_K (min log K), C₁ (scale shift, ≥ e.g. 3 + ⌈exp(C_K)⌉ so K_i valid),
T_* := max(T_A, T_B, T_C, T_I, numeric floors) — each lemma exports its own threshold; MultiScale
consumes them. Keep every threshold as an explicit `∃`-witness, never a numeral, EXCEPT where numerals
are forced; prefer `Filter.eventually_atTop` + extraction.

## Style rules for all files

- Lean 4, Mathlib ≥ current master (Axle lean-4.31.0). `import Mathlib` only (+ SieveVendored where needed).
- No `sorry` in final artifacts. No new axioms. `noncomputable` freely.
- Prefer explicit generous constants (powers of 2) over tight ones.
- Real-number arithmetic: `positivity`, `gcongr`, `nlinarith`, `field_simp` are your friends;
  log inequalities via `Real.log_le_sub_one_of_pos`, `Real.add_one_le_exp`, `Real.log_le_log`,
  `Real.one_le_exp`… Casts: `push_cast`, `exact_mod_cast`.
- Each lemma ≤ ~150 lines of proof; if bigger, split into helper lemmas.
