/- GID: D5/S3/Arith/ModularForms/CubicThetaResidueSums
   generality: G
   mirror-B: D5/B/S3/Arith/ModularForms/CubicThetaResidueSums
   mirror-E: none(waiver:formal-cubic-residue-sums)
   anchors: [mathlib/module/Mathlib.Combinatorics.Enumerative.Pentagonal.PowerSeries]
   utility: none
   digest: The three scalar residue sums for the Jacobi cube at a cubic root. -/

import D5.S3.Arith.ModularForms.CubicThetaCubeDissection

/-! Euler's pentagonal series and an exact sign-reversing involution evaluate all residues. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Arith.ModularForms.CubicThetaResidueSums

open CubicThetaCubeDissection CubicThetaJacobiCube
open scoped PowerSeries.WithPiTopology MvPowerSeries.WithPiTopology

noncomputable def residueTerm (r : Fin 3) (m : ℤ) : PowerSeries ℚ :=
  PowerSeries.C ((-1 : ℚ) ^ m.natAbs) * PowerSeries.X ^ residueExponent m r

theorem residue_exponent_one (m : ℤ) : residueExponent m 1 = pentagonal m := by
  have h := residue_exponent_cast m 1
  have ht := twice_triangular m
  have hp := two_mul_natCast_pentagonal m
  norm_num only [Fin.val_one, Nat.cast_one, one_mul] at h
  have he : (residueExponent m 1 : ℤ) = pentagonal m := by nlinarith
  exact_mod_cast he

theorem residue_exponent_two (m : ℤ) : residueExponent m 2 = pentagonal (-m) := by
  have h := residue_exponent_cast m 2
  have ht := twice_triangular m
  have hp := two_mul_natCast_pentagonal_neg m
  change (residueExponent m 2 : ℤ) = 3 * (triangularExponent m : ℤ) + 2 * m at h
  have he : (residueExponent m 2 : ℤ) = pentagonal (-m) := by nlinarith
  exact_mod_cast he

theorem residue_exponent_reflection (m : ℤ) :
    residueExponent (1 - m) 0 = residueExponent m 0 := by
  have h := residue_exponent_cast m 0
  have h' := residue_exponent_cast (1 - m) 0
  have ht := twice_triangular m
  have ht' := twice_triangular (1 - m)
  norm_num only [Fin.val_zero, Nat.cast_zero, zero_mul, add_zero] at h h'
  have heq : (residueExponent (1 - m) 0 : ℤ) = residueExponent m 0 := by nlinarith
  exact_mod_cast heq

private theorem sign_reflection (m : ℤ) :
    (-1 : ℚ) ^ (1 - m).natAbs = -((-1 : ℚ) ^ m.natAbs) := by
  have h : (1 - m).negOnePow = -m.negOnePow := by
    rw [Int.negOnePow_sub, Int.negOnePow_one, neg_mul, one_mul]
  have hh := congrArg (fun u : ℤˣ => ((u : ℤ) : ℚ)) h
  simpa only [Units.val_neg, Int.cast_neg, Int.coe_negOnePow] using hh

private theorem term_reflection (m : ℤ) : residueTerm 0 (1 - m) = -residueTerm 0 m := by
  simp only [residueTerm, residue_exponent_reflection, sign_reflection, map_neg, neg_mul]

/-- The zero-residue sum vanishes by a complete integer involution, including both zero exponents. -/
theorem hasSum_residue_zero [TopologicalSpace ℚ] : HasSum (residueTerm 0) 0 := by
  classical
  rw [PowerSeries.WithPiTopology.hasSum_iff_hasSum_coeff]
  intro degree
  let b : ℤ := 2 * degree + 2
  let s : Finset ℤ := Finset.Icc (-b) (b + 1)
  have hout (m : ℤ) (hm : m ∉ s) : PowerSeries.coeff degree (residueTerm 0 m) = 0 := by
    have he : residueExponent m 0 ≠ degree := by
      intro he
      have hr := residue_exponent_cast m 0
      norm_num only [Fin.val_zero, Nat.cast_zero, zero_mul, add_zero] at hr
      have hb := triangular_bound m degree (by omega)
      exact hm (by simp only [s, Finset.mem_Icc] at hb ⊢; dsimp [b]; omega)
    simp only [residueTerm, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow,
      if_neg (Ne.symm he), mul_zero]
  have hsum : (∑ m ∈ s, PowerSeries.coeff degree (residueTerm 0 m)) = 0 := by
    apply Finset.sum_involution (fun m _ => 1 - m)
    · intro m _
      rw [term_reflection, map_neg, add_neg_cancel]
    · intro m _ _
      omega
    · intro m _
      change 1 - (1 - m) = m
      omega
    · intro m hm
      simp only [s, Finset.mem_Icc] at hm ⊢
      omega
  simpa only [hsum, map_zero] using hasSum_sum_of_ne_finset_zero hout

/-- The first residue is exactly Euler's actual pentagonal series. -/
theorem hasSum_residue_one [TopologicalSpace ℚ] :
    HasSum (residueTerm 1) (PowerSeries.pentagonalSeries ℚ) := by
  convert PowerSeries.WithPiTopology.hasSum_pentagonalSeries ℚ using 1
  funext m
  simp only [residueTerm, residue_exponent_one, Int.coe_negOnePow, map_pow, map_neg, map_one]

/-- The second residue is the same Euler series by integer negation. -/
theorem hasSum_residue_two [TopologicalSpace ℚ] :
    HasSum (residueTerm 2) (PowerSeries.pentagonalSeries ℚ) := by
  have h := (Equiv.neg ℤ).hasSum_iff.mpr hasSum_residue_one
  convert h using 1
  funext m
  simp only [residueTerm, Function.comp_def, Equiv.neg_apply, residue_exponent_one,
    residue_exponent_two, Int.natAbs_neg]

end D5.S3.Arith.ModularForms.CubicThetaResidueSums
