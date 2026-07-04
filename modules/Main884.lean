/-!
# Erdős Problem 884 — the disproof (final statement)

Combining the multiscale construction (`exists_ratio_large`) with the bridge to the
official formal-conjectures statement (`Bridge884`), we conclude:

  it is NOT the case that
    ∑_{d < e, d,e ∣ n} 1/(e - d)  =O  1 + ∑_{consecutive divisors d < e of n} 1/(e - d)

as functions of `n → ∞`, i.e. Erdős problem #884 has a negative answer (Daniel Larsen).

In the ≪ notation of formal-conjectures, this refutes
  `sumDivisorInvPairwiseDifference ≪ 1 + sumDivisorInvConsecutiveDifference`.
-/

namespace Erdos884

theorem erdos_884_disproof :
    ¬ (sumDivisorInvPairwiseDifference =O[Filter.atTop] (1 + sumDivisorInvConsecutiveDifference)) := by
  intro h
  obtain ⟨c, hc⟩ := Asymptotics.isBigO_iff.mp h
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.mp hc
  obtain ⟨n, hn_ge, hn_ne, hlt⟩ :=
    exists_ratio_large (max c 1) (lt_of_lt_of_le one_pos (le_max_right c 1)) n₀
  have hb := hn₀ n hn_ge
  have hgap : (0 : ℝ) ≤ gapSum n.divisors := gapSum_nonneg _
  have hT : ‖sumDivisorInvPairwiseDifference n‖ = pairSum n.divisors := by
    rw [Real.norm_of_nonneg (sumDivisorInvPairwise_nonneg n hn_ne),
        sumDivisorInvPairwiseDifference_eq hn_ne]
  have hS : ‖(1 + sumDivisorInvConsecutiveDifference) n‖ = 1 + gapSum n.divisors := by
    have happ : (1 + sumDivisorInvConsecutiveDifference) n
        = 1 + sumDivisorInvConsecutiveDifference n := by
      simp [Pi.add_apply, Pi.one_apply]
    rw [happ, sumDivisorInvConsecutiveDifference_eq hn_ne,
        Real.norm_of_nonneg (by linarith)]
  rw [hT, hS] at hb
  have hchain : pairSum n.divisors ≤ max c 1 * (1 + gapSum n.divisors) :=
    hb.trans (mul_le_mul_of_nonneg_right (le_max_left c 1) (by linarith))
  exact absurd hchain (not_le.mpr hlt)

/--
The disproof in the exact shape of the google-deepmind/formal-conjectures statement
`Erdos884.erdos_884 : answer(False) ↔ Erdos884Prop`.

There `answer(False)` reduces to `False`, and `Erdos884Prop` is
`sumDivisorInvPairwiseDifference ≪ 1 + sumDivisorInvConsecutiveDifference`, where `≪` is
their notation for `Asymptotics.IsBigO Filter.atTop`. Unfolding both, that statement is
exactly the `↔` below, discharged by `erdos_884_disproof`. This is the formal proof
referenced by the `@[formal_proof using lean4 at …]` attribute on `erdos_884`.
-/
theorem erdos_884_iff_false :
    False ↔ sumDivisorInvPairwiseDifference =O[Filter.atTop]
      (1 + sumDivisorInvConsecutiveDifference) :=
  iff_of_false not_false erdos_884_disproof

end Erdos884
