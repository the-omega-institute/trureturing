/- GID: D5/S3/Analysis/PositiveSkew
   generality: G
   mirror-B: none(waiver:covered-by-ccrgaussian-extension-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Signed positivity for a skew-adjoint element gives a contractive positive defect and an inverse identity for the sum of its defect root and the identity. -/

import OmegaBuild.Commands
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum

compile_only_with_mathlib

/-!
Omega original.

Signed positivity for a skew-adjoint element gives a contractive positive defect and an
inverse identity for the sum of its defect root and the identity.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped Ring

namespace Omega

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

omit [PartialOrder A] [StarOrderedRing A] in
private theorem signed_skew_factors (S : A) :
    Commute (1 - Complex.I • S) (1 + Complex.I • S) ∧
      (1 - Complex.I • S) * (1 + Complex.I • S) = 1 + S ^ 2 := by
  let J := Complex.I • S
  constructor
  · exact ((Commute.one_left (1 : A)).add_right (Commute.one_left J)).sub_left
      ((Commute.one_right J).add_right (Commute.refl J))
  · change (1 - J) * (1 + J) = _
    rw [show (1 - J) * (1 + J) = 1 - J * J by noncomm_ring]
    simp [J, smul_smul, Complex.I_mul_I, pow_two]

/-- For a skew-adjoint element, positivity of the two signed shifts gives both the
contraction and the factorization of its defect root. -/
theorem skew_defect {S : A} (hs : star S = -S) (hm : 0 ≤ 1 - Complex.I • S)
    (hp : 0 ≤ 1 + Complex.I • S) :
    ‖S‖ ≤ 1 ∧ 0 ≤ 1 + S ^ 2 ∧ CFC.sqrt (1 + S ^ 2) ≤ 1 ∧
      CFC.sqrt (1 + S ^ 2) = CFC.sqrt (1 - Complex.I • S) * CFC.sqrt (1 + Complex.I • S) := by
  obtain ⟨hc, he⟩ := signed_skew_factors S
  have hz : 0 ≤ 1 + S ^ 2 := he ▸ Commute.mul_nonneg hm hp hc
  have hz' : 1 + S ^ 2 = 1 - star S * S := by rw [hs, pow_two, neg_mul, sub_neg_eq_add]
  have hnorm : ‖S‖ ≤ 1 := by
    apply (sq_le_sq₀ (norm_nonneg S) zero_le_one).1
    rw [pow_two, ← CStarRing.norm_star_mul_self, one_pow]
    exact (CStarAlgebra.norm_le_one_iff_of_nonneg _ (star_mul_self_nonneg _)).2
      (sub_nonneg.mp (hz' ▸ hz))
  have hbound : 1 + S ^ 2 ≤ 1 := by
    rw [hz']
    exact sub_le_self _ (star_mul_self_nonneg _)
  have hcomm : Commute (CFC.sqrt (1 - Complex.I • S)) (CFC.sqrt (1 + Complex.I • S)) := by
    rw [CFC.sqrt_eq_real_sqrt _ hm, CFC.sqrt_eq_real_sqrt _ hp]
    exact ((hc.cfcₙ_real Real.sqrt).symm.cfcₙ_real Real.sqrt).symm
  refine ⟨hnorm, hz, ?_, ?_⟩
  · simpa only [CFC.sqrt_one] using CFC.sqrt_le_sqrt _ _ hbound
  · apply CFC.sqrt_unique _ (Commute.mul_nonneg (CFC.sqrt_nonneg _) (CFC.sqrt_nonneg _) hcomm)
    let U := CFC.sqrt (1 - Complex.I • S)
    let V := CFC.sqrt (1 + Complex.I • S)
    change (U * V) * (U * V) = _
    calc
      _ = (U * U) * (V * V) := by
        simp only [mul_assoc]
        rw [← mul_assoc V, hcomm.symm.eq, mul_assoc]
      _ = _ := by
        rw [show U * U = _ from CFC.sqrt_mul_sqrt_self _ hm,
          show V * V = _ from CFC.sqrt_mul_sqrt_self _ hp, he]

/-- The skew defect identity is preserved by congruence with an invertible element. -/
theorem skew_defect_congruence {a R : A} (ha : IsUnit a)
    (hs : 0 ≤ 1 + (a⁻¹ʳ * R * a⁻¹ʳ) ^ 2) :
    let D := a * (1 + CFC.sqrt (1 + (a⁻¹ʳ * R * a⁻¹ʳ) ^ 2)) * a
    (1 / 2 : ℝ) • (D - R * D⁻¹ʳ * R) = a * a := by
  let b := a⁻¹ʳ
  let S := b * R * b
  let P := CFC.sqrt (1 + S ^ 2)
  let C : A := 1 + P
  let D := a * C * a
  change (1 / 2 : ℝ) • (D - R * D⁻¹ʳ * R) = a * a
  have hab : a * b = 1 := Ring.mul_inverse_cancel a ha
  have hba : b * a = 1 := Ring.inverse_mul_cancel a ha
  have hC : IsUnit C := (isStrictlyPositive_one.add_nonneg (CFC.sqrt_nonneg _)).isUnit
  have hD : IsUnit D := (ha.mul hC).mul ha
  have hDi : D⁻¹ʳ = b * C⁻¹ʳ * b := by
    refine left_inv_eq_right_inv (Ring.inverse_mul_cancel D hD) ?_
    change (a * C * a) * (b * C⁻¹ʳ * b) = 1
    simp only [mul_assoc, ← mul_assoc a b, hab, one_mul,
      Ring.mul_inverse_cancel_left C _ hC]
  have hR : R = a * S * a := by
    change R = a * (b * R * b) * a
    rw [mul_assoc b R b, ← mul_assoc a b, hab, one_mul, mul_assoc, hba, mul_one]
  have hP : P * P = 1 + S ^ 2 := CFC.sqrt_mul_sqrt_self _ hs
  have hSC : Commute S C := by
    apply (Commute.one_right S).add_right
    change Commute S (CFC.sqrt (1 + S ^ 2))
    rw [CFC.sqrt_eq_real_sqrt _ hs]
    exact (((Commute.one_left S).add_left ((Commute.refl S).pow_left 2)).cfcₙ_real Real.sqrt).symm
  have hSi : S * C⁻¹ʳ = C⁻¹ʳ * S := by
    apply hC.mul_right_cancel
    rw [Ring.inverse_mul_cancel_right C S hC, mul_assoc (C⁻¹ʳ), hSC.eq,
      ← mul_assoc, Ring.inverse_mul_cancel C hC, one_mul]
  have hred : S * C⁻¹ʳ * S = P - 1 := by
    rw [hSi, mul_assoc]
    apply (Ring.inverse_mul_eq_iff_eq_mul C _ _ hC).2
    change S * S = (1 + P) * (P - 1)
    rw [show (1 + P) * (P - 1) = P * P - 1 by noncomm_ring, hP]
    simp [pow_two]
  have hRDR : R * D⁻¹ʳ * R = a * (P - 1) * a := by
    rw [hDi, hR]
    calc
      _ = a * (S * (a * b) * C⁻¹ʳ * (b * a) * S) * a := by noncomm_ring
      _ = _ := by rw [hab, hba, mul_one, mul_one, hred]
  rw [hRDR, show D - a * (P - 1) * a = a * a + a * a by
    change a * (1 + P) * a - a * (P - 1) * a = _
    noncomm_ring, ← two_smul ℝ (a * a), smul_smul]
  norm_num

/-- An invertible positive element has a strictly positive scalar lower bound. -/
theorem positive_lower_bound {a : A} (ha : 0 ≤ a) (hu : IsUnit a) :
    ∃ d : ℝ, 0 < d ∧ d • (1 : A) ≤ a := by
  cases subsingleton_or_nontrivial A with
  | inl _ => exact ⟨1, zero_lt_one, (Subsingleton.elim _ a).le⟩
  | inr _ =>
    simpa only [Algebra.algebraMap_eq_smul_one] using
      (CFC.exists_pos_algebraMap_le_iff a (IsSelfAdjoint.of_nonneg ha)).2
        (fun _ hx => (hu.isStrictlyPositive ha).spectrum_pos hx)

end Omega
