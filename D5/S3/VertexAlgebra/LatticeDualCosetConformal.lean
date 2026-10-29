/- GID: D5/S3/VertexAlgebra/LatticeDualCosetConformal
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeDualCosetConformal
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Original lattice conformal modes on dual-coset modules and their state-field calculus. -/

import D5.S3.VertexAlgebra.LatticeDualCosetModule
import D5.S3.VertexAlgebra.LatticeActualLZeroGrading
import D5.S3.VertexAlgebra.LatticeSugawaraVirasoro

/-
Classical lattice-module construction: Bakalov--Kac, math/0402315v1,
section 4.1. The original quadratic state is used as the actual module
input. The imported Sugawara proofs retain Kalle Kytölä's Apache-2.0
attribution and VirasoroProject revision
5ff4245383b2cdd4eea7a0524bc1274c32041eb4.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

namespace D5.S3.VertexAlgebra.LatticeDualCosetConformal
open LatticeGeneratingFieldLocality LatticeAllStateField
open LatticeAllStateReconstruction LatticeFiniteNegativeGeneration
open LatticeSugawaraConformal LatticeSugawaraCurrents
open LatticeActualConformalState LatticeActualStateFieldCalculus
open LatticeActualConformalWard LatticeDualCosetModule FieldNormalProduct
open StateFieldResidueReconstruction (integerBinomial)
open scoped BigOperators VertexOperator
noncomputable section

variable (D : LatticeData) (β : Charge D)

/-- The normalized mode of the original lattice omega under the actual action. -/
def moduleL (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (m : ℤ) :
    Module.End ℂ (Carrier D) :=
  ((action D β (omega D H))[[m + 1]])

def commutatorTerm (a b : Carrier D) (p q : ℤ) (j : ℕ) :
    Module.End ℂ (Carrier D) :=
  integerBinomial p j • ((action D β (mu D a j b))[[p + q - j]])

theorem commutator_terms_finite (a b : Carrier D) (p q : ℤ) :
    Function.HasFiniteSupport (commutatorTerm D β a b p q) := by
  classical
  apply (nonnegative_products_finite D a b).subset
  intro j member
  contrapose! member
  have hz : mu D a j b = 0 := by
    simpa only [Function.mem_support, not_not] using member
  simp [commutatorTerm, hz]

/-- All-integer actual module commutators; the sum has finite operator support. -/
theorem mode_commutator (a b : Carrier D) (p q : ℤ) :
    ((action D β a)[[p]]) * ((action D β b)[[q]]) -
        ((action D β b)[[q]]) * ((action D β a)[[p]]) =
      ∑ᶠ j : ℕ, commutatorTerm D β a b p q j := by
  classical
  apply LinearMap.ext
  intro v
  have h := (module_borcherds D β a b v p q 0).2.2.2
  have hr : (∑ᶠ j : ℕ,
      (((-1 : ℂ)^j) * integerBinomial 0 j) •
        (((action D β a)[[p + 0 - j]]) (((action D β b)[[q + j]]) v) -
          StateFieldResidueReconstruction.epsilon 0 •
            ((action D β b)[[q + 0 - j]]) (((action D β a)[[p + j]]) v))) =
      ((action D β a)[[p]]) (((action D β b)[[q]]) v) -
        ((action D β b)[[q]]) (((action D β a)[[p]]) v) := by
    rw [finsum_eq_single _ 0]
    · simp [integerBinomial, StateFieldResidueReconstruction.epsilon]
    · intro j hj
      simp [integerBinomial, Ring.choose_zero_pos ℤ (Nat.pos_of_ne_zero hj)]
  rw [hr] at h
  have he : (∑ᶠ j : ℕ, commutatorTerm D β a b p q j) v =
      ∑ᶠ j : ℕ, moduleLeft D β p q 0 a b v j := by
    change (LinearMap.applyₗ v) (∑ᶠ j : ℕ, commutatorTerm D β a b p q j) = _
    rw [map_finsum (LinearMap.applyₗ v) (commutator_terms_finite D β a b p q)]
    apply finsum_congr
    intro j
    simp only [commutatorTerm, moduleLeft, mu, zero_add,
      LinearMap.applyₗ_apply_apply, LinearMap.smul_apply]
  rw [he]
  exact h.symm

theorem one_mode_commutator (a b : Carrier D) (q : ℤ) :
    ((action D β a)[[1]]) * ((action D β b)[[q]]) -
        ((action D β b)[[q]]) * ((action D β a)[[1]]) =
      ((action D β (mu D a 0 b))[[q + 1]]) +
        ((action D β (mu D a 1 b))[[q]]) := by
  rw [mode_commutator]
  have hf : (∑ᶠ j : ℕ, commutatorTerm D β a b 1 q j) =
      ∑ j ∈ Finset.range 2, commutatorTerm D β a b 1 q j := by
    apply finsum_eq_sum_of_support_subset
    intro j hj
    by_contra ho
    have hz : (1 : ℕ).choose j = 0 := Nat.choose_eq_zero_of_lt (by simpa using ho)
    have hc : Ring.choose (1 : ℤ) j = 0 := by
      change Ring.choose ((1 : ℕ) : ℤ) j = 0
      rw [Ring.choose_natCast, hz]
      rfl
    exact hj (by simp [commutatorTerm, integerBinomial, hc])
  rw [hf]
  simp [Finset.sum_range_succ, commutatorTerm, integerBinomial,
    Ring.choose_one_right, add_comm q 1]

/-- The two normal-product halves are summed only after applying to a vector. -/
theorem minus_one_product_field (a b : Carrier D) :
    action D β (mu D a (-1) b) =
      (normalMinusOne (action D β a) (action D β b)).1 := by
  classical
  apply HVertexOperator.coeff_inj
  funext power
  apply LinearMap.ext
  intro v
  rw [VertexOperator.coeff_eq_ncoeff, VertexOperator.coeff_eq_ncoeff,
    (normalMinusOne (action D β a) (action D β b)).2]
  obtain ⟨_, hf, hs, h⟩ := module_borcherds D β a b v 0 (-power - 1) (-1)
  have hl : (∑ᶠ i : ℕ, moduleLeft D β 0 (-power - 1) (-1) a b v i) =
      ((action D β (mu D a (-1) b))[[-power - 1]]) v := by
    rw [finsum_eq_single _ 0]
    · simp [moduleLeft, integerBinomial, mu]
    · intro i hi
      simp [moduleLeft, integerBinomial,
        Ring.choose_zero_pos ℤ (Nat.pos_of_ne_zero hi)]
  rw [hl] at h
  simp_rw [smul_sub] at h
  change _ = ∑ᶠ i : ℕ,
    (moduleFirst D β 0 (-power - 1) (-1) a b v i -
      moduleSecond D β 0 (-power - 1) (-1) a b v i) at h
  rw [finsum_sub_distrib hf hs] at h
  simp only [moduleFirst, moduleSecond, minus_one_binomial, one_smul,
    StateFieldResidueReconstruction.epsilon, show (-1 : ℂ)^(-1 : ℤ) = -1 by norm_num,
    neg_smul, one_smul] at h
  rw [h]
  rw [finsum_neg_distrib]
  simp only [neg_neg, sub_neg_eq_add, zero_add]
  congr 1
  · apply finsum_congr
    intro i
    congr 2 <;> omega
  · apply finsum_congr
    intro i
    congr 2 <;> omega

/-- The actual current differs from the original one only in its zero mode. -/
theorem action_current (i : Fin D.rank) (m : ℤ) :
    ((action D β (currentState D i))[[m]]) = neutralMode D i m +
      (if m = 0 then (β i : ℂ) else 0) • (1 : Module.End ℂ (Carrier D)) := by
  classical
  apply Finsupp.lhom_ext'
  intro n
  apply LinearMap.ext
  intro p
  change ((action D β (currentState D i))[[m]]) (Finsupp.single n p) = _
  rw [currentState, action_current_coefficients]
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, LinearMap.add_apply,
    LinearMap.smul_apply, Module.End.one_apply]
  rw [neutralMode_single]
  by_cases hm : m < 0
  · simp [shiftedCurrentPolynomial, neutralPolynomialMode, hm, show m ≠ 0 by omega]
  · by_cases hz : m = 0
    · simp [shiftedCurrentPolynomial, neutralPolynomialMode, hm, hz,
        add_smul, Finsupp.single_add, ← Finsupp.smul_single]
    · simp [shiftedCurrentPolynomial, neutralPolynomialMode, hm, hz]

/-- Original omega acts by the half-weighted normal products of actual currents. -/
theorem moduleL_normal (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (m : ℤ) :
    moduleL D β H m = (2 : ℂ)⁻¹ •
      ∑ i : Fin D.rank, ∑ j : Fin D.rank, H i j •
        ((normalMinusOne (action D β (currentState D i))
          (action D β (currentState D j))).1)[[m + 1]] := by
  classical
  unfold moduleL omega conformalPolynomial
  rw [← Finsupp.smul_single, map_smul]
  simp_rw [Finsupp.single_finsetSum, map_sum, ← Finsupp.smul_single,
    map_smul, ← current_minus_one_current, minus_one_product_field]
  simp only [map_smul, map_sum, Pi.smul_apply, Finset.sum_apply]

/-- Energy covariance holds for every original state, not only current generators. -/
theorem energy_covariance (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (a : Carrier D) (q : ℤ) :
    moduleL D β H 0 * ((action D β a)[[q]]) -
        ((action D β a)[[q]]) * moduleL D β H 0 =
      ((action D β (sugawaraMode D H 0 a))[[q]]) -
        ((q : ℂ) + 1) • ((action D β a)[[q]]) := by
  have h := one_mode_commutator D β (omega D H) a q
  rw [omega_product, omega_product,
    show (1 : ℤ) - 1 = 0 by norm_num,
    show (0 : ℤ) - 1 = -1 by norm_num,
    sugawaraMode_minus_one_eq_translation D H hHG hGH,
    module_input_derivative D β] at h
  change _ - _ = _
  change ((action D β (omega D H))[[1]]) * _ - _ *
    ((action D β (omega D H))[[1]]) = _
  rw [h]
  simp only [Int.cast_add, Int.cast_one, add_sub_cancel_right]
  apply LinearMap.ext
  intro v
  simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply]
  rw [neg_smul, sub_eq_add_neg, add_comm]

end
end D5.S3.VertexAlgebra.LatticeDualCosetConformal
