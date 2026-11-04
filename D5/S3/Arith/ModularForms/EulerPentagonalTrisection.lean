/- GID: D5/S3/Arith/ModularForms/EulerPentagonalTrisection
   generality: G
   mirror-B: D5/B/S3/Arith/ModularForms/EulerPentagonalTrisection
   mirror-E: none(waiver:complete-pentagonal-three-sections)
   anchors: [mathlib/module/Mathlib.Combinatorics.Enumerative.Pentagonal.PowerSeries]
   utility: none
   digest: A complete integer reindexing identifies Euler's three Jacobi sections. -/

import D5.S3.Arith.ModularForms.WeightedJacobiSpecialization

/-! The integer classes are k=3m, k=1-3m, and k=3m-1.
Their exponents and signs are checked before regrouping the complete sum. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Arith.ModularForms.EulerPentagonalTrisection

open WeightedJacobiSpecialization
open scoped PowerSeries.WithPiTopology MvPowerSeries.WithPiTopology

private local instance : UniformSpace ℚ := ⊥
private local instance : DiscreteUniformity ℚ := ⟨rfl⟩

theorem continuous_expand (d : ℕ) (hd : d ≠ 0) :
    Continuous (PowerSeries.expand d hd : PowerSeries ℚ → PowerSeries ℚ) := by
  rw [continuous_iff_continuousAt]
  intro p
  apply (PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto _ _ _ _).2
  intro n
  by_cases hn : d ∣ n
  · obtain ⟨m, rfl⟩ := hn
    simp only [PowerSeries.coeff_expand_mul]
    exact (PowerSeries.WithPiTopology.continuous_coeff ℚ m).continuousAt
  · simp only [PowerSeries.coeff_expand_of_not_dvd d hd _ hn]
    exact tendsto_const_nhds

private def sectionIndex (p : Fin 3 × ℤ) : ℤ :=
  if p.1 = 0 then 3 * p.2 else if p.1 = 1 then 1 - 3 * p.2 else 3 * p.2 - 1

private theorem sectionIndex_bijective : Function.Bijective sectionIndex := by
  constructor
  · rintro ⟨r, m⟩ ⟨s, n⟩ h
    fin_cases r <;> fin_cases s <;> simp [sectionIndex] at h ⊢ <;> omega
  · intro k
    have hk : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
    rcases hk with hk | hk | hk
    · refine ⟨(0, k / 3), ?_⟩
      simp only [sectionIndex, ite_true]
      omega
    · refine ⟨(1, (1 - k) / 3), ?_⟩
      norm_num [sectionIndex]
      omega
    · refine ⟨(2, (k + 1) / 3), ?_⟩
      norm_num [sectionIndex]
      omega

private noncomputable def sectionEquiv : (Fin 3 × ℤ) ≃ ℤ :=
  Equiv.ofBijective sectionIndex sectionIndex_bijective

theorem pentagonal_sections (m : ℤ) :
    pentagonal (3 * m) = 3 * weightedExponent 4 4 m ∧
    pentagonal (1 - 3 * m) = 1 + 3 * weightedExponent 6 2 m ∧
    pentagonal (3 * m - 1) = 2 + 3 * weightedExponent 7 1 m := by
  have h0 := two_mul_natCast_pentagonal (3 * m)
  have h1 := two_mul_natCast_pentagonal (1 - 3 * m)
  have h2 := two_mul_natCast_pentagonal (3 * m - 1)
  have w0 := twice_weightedExponent 4 4 m
  have w1 := twice_weightedExponent 6 2 m
  have w2 := twice_weightedExponent 7 1 m
  norm_num only [Nat.cast_ofNat] at w0 w1 w2
  constructor
  · have h : (pentagonal (3 * m) : ℤ) = 3 * weightedExponent 4 4 m := by nlinarith
    exact_mod_cast h
  · constructor
    · have h : (pentagonal (1 - 3 * m) : ℤ) =
          1 + 3 * weightedExponent 6 2 m := by nlinarith
      exact_mod_cast h
    · have h : (pentagonal (3 * m - 1) : ℤ) =
          2 + 3 * weightedExponent 7 1 m := by nlinarith
      exact_mod_cast h

private theorem sign_sections (m : ℤ) :
    (-1 : ℚ) ^ (3 * m).natAbs = (-1 : ℚ) ^ m.natAbs ∧
    (-1 : ℚ) ^ (1 - 3 * m).natAbs = -((-1 : ℚ) ^ m.natAbs) ∧
    (-1 : ℚ) ^ (3 * m - 1).natAbs = -((-1 : ℚ) ^ m.natAbs) := by
  have h3 : (3 * m).negOnePow = m.negOnePow := by
    apply (Int.negOnePow_eq_iff _ _).2
    exact ⟨m, by ring⟩
  have h1 : (1 - 3 * m).negOnePow = -m.negOnePow := by
    rw [Int.negOnePow_sub, Int.negOnePow_one, h3, neg_mul, one_mul]
  have h2 : (3 * m - 1).negOnePow = -m.negOnePow := by
    rw [Int.negOnePow_sub, Int.negOnePow_one, h3, mul_neg, mul_one]
  have h0' := congrArg (fun u : ℤˣ => ((u : ℤ) : ℚ)) h3
  have h1' := congrArg (fun u : ℤˣ => ((u : ℤ) : ℚ)) h1
  have h2' := congrArg (fun u : ℤˣ => ((u : ℤ) : ℚ)) h2
  constructor
  · simpa only [Int.coe_negOnePow] using h0'
  · constructor
    · simpa only [Units.val_neg, Int.cast_neg, Int.coe_negOnePow] using h1'
    · simpa only [Units.val_neg, Int.cast_neg, Int.coe_negOnePow] using h2'

/-- Exact three-section identity for the actual Euler series, over all degrees. -/
theorem euler_three_sections :
    PowerSeries.pentagonalSeries ℚ =
      PowerSeries.expand 3 (by decide) (J 4 4) -
      PowerSeries.X * PowerSeries.expand 3 (by decide) (J 6 2) -
      PowerSeries.X ^ 2 * PowerSeries.expand 3 (by decide) (J 7 1) := by
  let term (k : ℤ) : PowerSeries ℚ :=
    PowerSeries.C ((-1 : ℚ) ^ k.natAbs) * PowerSeries.X ^ pentagonal k
  have he : HasSum term (PowerSeries.pentagonalSeries ℚ) := by
    simpa only [term, Int.coe_negOnePow, map_pow, map_neg, map_one] using
      PowerSeries.WithPiTopology.hasSum_pentagonalSeries ℚ
  let total (r : Fin 3) : PowerSeries ℚ :=
    if r = 0 then PowerSeries.expand 3 (by decide) (J 4 4)
    else if r = 1 then -(PowerSeries.X * PowerSeries.expand 3 (by decide) (J 6 2))
    else -(PowerSeries.X ^ 2 * PowerSeries.expand 3 (by decide) (J 7 1))
  have hf (r : Fin 3) : HasSum (fun m : ℤ => term (sectionEquiv (r, m))) (total r) := by
    fin_cases r
    · have h := (hasSum_J 4 4).map (PowerSeries.expand 3 (by decide)).toAddMonoidHom
        (continuous_expand 3 (by decide))
      convert h using 1
      · funext m
        change term (3 * m) = PowerSeries.expand 3 (by decide)
          (PowerSeries.C ((-1 : ℚ) ^ m.natAbs) * PowerSeries.X ^ weightedExponent 4 4 m)
        dsimp only [term]
        rw [(pentagonal_sections m).1, (sign_sections m).1]
        simp only [map_mul, map_pow, PowerSeries.expand_C, PowerSeries.expand_X, ← pow_mul]
      · simp [total]
    · have h := ((hasSum_J 6 2).map (PowerSeries.expand 3 (by decide)).toAddMonoidHom
        (continuous_expand 3 (by decide))).mul_left (-PowerSeries.X)
      convert h using 1
      · funext m
        change term (1 - 3 * m) = -PowerSeries.X * PowerSeries.expand 3 (by decide)
          (PowerSeries.C ((-1 : ℚ) ^ m.natAbs) * PowerSeries.X ^ weightedExponent 6 2 m)
        dsimp only [term]
        rw [(pentagonal_sections m).2.1, (sign_sections m).2.1]
        simp only [map_mul, map_pow, PowerSeries.expand_C, PowerSeries.expand_X,
          map_neg, map_one, pow_add, pow_one, ← pow_mul, Nat.mul_comm]
        ring
      · simp [total]
    · have h := ((hasSum_J 7 1).map (PowerSeries.expand 3 (by decide)).toAddMonoidHom
        (continuous_expand 3 (by decide))).mul_left (-PowerSeries.X ^ 2)
      convert h using 1
      · funext m
        change term (3 * m - 1) = -PowerSeries.X ^ 2 * PowerSeries.expand 3 (by decide)
          (PowerSeries.C ((-1 : ℚ) ^ m.natAbs) * PowerSeries.X ^ weightedExponent 7 1 m)
        dsimp only [term]
        rw [(pentagonal_sections m).2.2, (sign_sections m).2.2]
        simp only [map_mul, map_pow, PowerSeries.expand_C, PowerSeries.expand_X,
          map_neg, map_one, pow_add, ← pow_mul, Nat.mul_comm]
        ring
      · simp [total]
  have hall := sectionEquiv.hasSum_iff.mpr he
  have hg := hall.prod_fiberwise hf
  have heq := hg.unique (hasSum_fintype total)
  simpa [total, Fin.sum_univ_succ, sub_eq_add_neg, add_assoc] using heq

end D5.S3.Arith.ModularForms.EulerPentagonalTrisection
