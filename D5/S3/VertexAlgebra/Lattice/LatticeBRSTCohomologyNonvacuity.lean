/- GID: D5/S3/VertexAlgebra/Lattice/LatticeBRSTCohomologyNonvacuity
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/LatticeBRSTCohomologyNonvacuity
   mirror-E: none(waiver:algebraic-original-brst-cohomology)
   anchors: []
   utility: none
   digest: The all-state original vacuum coefficient annihilates total charge and separates the critical quotient vacuum. -/

/- Original tensor-state BRST cohomology. The supplier chain retains the
Bakalov--Kac lattice, Scott Carnahan field and residue calculus, Kalle Kytölä
Sugawara and Mathlib attribution. No literature novelty is asserted. -/

import D5.S3.VertexAlgebra.Lattice.LatticeBRSTCohomologyLaws

/-! The actual all-state vacuum coefficient separates the original BRST vacuum. -/

set_option autoImplicit false

open scoped BigOperators TensorProduct VertexOperator

namespace D5.S3.VertexAlgebra.LatticeBRSTCohomologyField

open LatticeGeneratingFieldLocality (LatticeData Carrier Charge Oscillator)
open LatticeFiniteNegativeGeneration (neutralMode neutralPolynomialMode)
open LatticeSugawaraCurrents
open LatticeMatterGhostCoupling (State summand T)
open D5.S3.Quantum.Fermionic
open CountableOccupationFock (Fock)
open BcGhostFock (b c)
open private epsilon_create epsilon_b epsilon_vacuum from
  D5.S3.Quantum.Fermionic.BcGhostVirasoro

noncomputable section

variable (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)

private def matterVacuumCoeff : Carrier D →ₗ[ℂ] ℂ :=
  (MvPolynomial.lcoeff ℂ 0).comp (Finsupp.lapply (0 : Charge D))

private theorem matterCoeff_negative_current (i : Fin D.rank) (m : ℤ)
    (hm : m < 0) (v : Carrier D) : matterVacuumCoeff D (neutralMode D i m v) = 0 := by
  classical
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => simp only [map_add, hv, hw, add_zero]
  | single β p =>
    rw [neutralMode_single]
    by_cases hβ : β = 0
    · subst β
      change MvPolynomial.constantCoeff
        ((Finsupp.single (0 : Charge D) (neutralPolynomialMode D i 0 m p)) 0) = 0
      rw [Finsupp.single_eq_same]
      simp only [neutralPolynomialMode, if_pos hm, LinearMap.mulLeft_apply,
        map_mul, MvPolynomial.constantCoeff_X, zero_mul]
    · simp [matterVacuumCoeff, Finsupp.single_apply, hβ, Ne.symm hβ]

private theorem matterCoeff_negative_sugawara (m : ℤ) (hm : m < 0) (v : Carrier D) :
    matterVacuumCoeff D (sugawaraMode D H m v) = 0 := by
  have quad (i j : Fin D.rank) :
      matterVacuumCoeff D (((quadraticSummand D i j)[[m + 1]]) v) = 0 := by
    rw [quadraticSummand_coefficient,
      map_finsum _ (normalSummand_finite D i j m v)]
    apply finsum_eq_zero_of_forall_eq_zero
    intro k
    by_cases hk : k < 0
    · simp only [normalSummand, if_pos hk, Module.End.mul_apply]
      exact matterCoeff_negative_current D i k hk _
    · simp only [normalSummand, if_neg hk, Module.End.mul_apply]
      exact matterCoeff_negative_current D j (m - k) (by omega) _
  rw [sugawaraMode_coefficient_sum]
  simp only [LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum,
    quad, smul_zero, Finset.sum_const_zero]

private theorem ghostCoeff_c (p : ℤ) (hp : p ≤ 1) (v : Fock) :
    BcGhostVirasoro.epsilon (c p v) = 0 := by
  rw [c, if_pos hp]
  exact epsilon_create _ v

private theorem ghostCoeff_cubic (p q : ℤ) (v : Fock) :
    BcGhostVirasoro.epsilon (BcGhostBRST.cubic p q v) = 0 := by
  by_cases hp : p ≤ 1
  · by_cases hq : q ≤ 1
    · simp only [BcGhostBRST.cubic, if_pos hp, if_pos hq, Module.End.mul_apply]
      exact ghostCoeff_c p hp _
    · by_cases hk : -p - q ≤ -2
      · simp only [BcGhostBRST.cubic, if_pos hp, if_neg hq, if_pos hk,
          LinearMap.neg_apply, Module.End.mul_apply, map_neg, ghostCoeff_c p hp, neg_zero]
      · simp only [BcGhostBRST.cubic, if_pos hp, if_neg hq, if_neg hk,
          Module.End.mul_apply, ghostCoeff_c p hp]
  · by_cases hq : q ≤ 1
    · by_cases hk : -p - q ≤ -2
      · simp only [BcGhostBRST.cubic, if_neg hp, if_pos hq, if_pos hk,
          Module.End.mul_apply, ghostCoeff_c q hq]
      · simp only [BcGhostBRST.cubic, if_neg hp, if_pos hq, if_neg hk,
          LinearMap.neg_apply, Module.End.mul_apply, map_neg, ghostCoeff_c q hq, neg_zero]
    · have hk : -p - q ≤ -2 := by omega
      simp only [BcGhostBRST.cubic, if_neg hp, if_neg hq, if_pos hk, Module.End.mul_apply]
      exact epsilon_b _ hk _

private theorem ghostCoeff_charge (v : Fock) :
    BcGhostVirasoro.epsilon (BcGhostBRST.Qg v) = 0 := by
  change BcGhostVirasoro.epsilon (∑ᶠ pq : ℤ × ℤ, BcGhostBRST.cubicTerm pq v) = 0
  rw [map_finsum _ (BcGhostBRST.cubicTerm_finite v)]
  apply finsum_eq_zero_of_forall_eq_zero
  intro pq
  simp only [BcGhostBRST.cubicTerm, LinearMap.smul_apply, map_smul,
    ghostCoeff_cubic, smul_zero]

/-- The actual original tensor-vacuum coefficient, defined on every original state. -/
def vacuumCoeff : State D →ₗ[ℂ] ℂ :=
  TensorProduct.lift ((matterVacuumCoeff D).smulRight BcGhostVirasoro.epsilon)

@[simp] theorem vacuumCoeff_tmul (v : Carrier D) (w : Fock) :
    vacuumCoeff D (v ⊗ₜ[ℂ] w) = matterVacuumCoeff D v * BcGhostVirasoro.epsilon w := by
  rw [vacuumCoeff, TensorProduct.lift.tmul, LinearMap.smulRight_apply,
    LinearMap.smul_apply, smul_eq_mul]

private theorem vacuumCoeff_summand (m : ℤ) (x : State D) :
    vacuumCoeff D (summand D H m x) = 0 := by
  induction x using TensorProduct.inductionOn with
  | tmul v w =>
    rw [summand, TensorProduct.map_tmul, vacuumCoeff_tmul]
    by_cases hm : m < 0
    · rw [matterCoeff_negative_sugawara D H m hm, zero_mul]
    · rw [ghostCoeff_c (-m) (by omega), mul_zero]
  | add x y hx hy => simp only [map_add, hx, hy, add_zero]

private theorem vacuumCoeff_matter_charge (x : State D) :
    vacuumCoeff D (T D H x) = 0 := by
  change vacuumCoeff D (∑ᶠ m : ℤ, summand D H m x) = 0
  rw [map_finsum _ (LatticeMatterGhostCoupling.summand_finite D H x)]
  exact finsum_eq_zero_of_forall_eq_zero (fun m => vacuumCoeff_summand D H m x)

private theorem vacuumCoeff_ghost_charge (x : State D) :
    vacuumCoeff D (LatticeBRST.ghostCharge D x) = 0 := by
  induction x using TensorProduct.inductionOn with
  | tmul v w =>
    simp only [LatticeBRST.ghostCharge, TensorProduct.map_tmul, LinearMap.id_apply,
      vacuumCoeff_tmul, ghostCoeff_charge, mul_zero]
  | add x y hx hy => simp only [map_add, hx, hy, add_zero]

/-- The separating coefficient kills the ORIGINAL total charge, for arbitrary D/H. -/
theorem vacuumCoeff_charge (x : State D) :
    vacuumCoeff D (LatticeBRST.totalCharge D H x) = 0 := by
  simp only [LatticeBRST.totalCharge, LinearMap.add_apply, map_add,
    vacuumCoeff_matter_charge, vacuumCoeff_ghost_charge, add_zero]

theorem vacuumCoeff_vacuum :
    vacuumCoeff D (LatticeMatterGhostStateField.vacuum D) = 1 := by
  rw [LatticeMatterGhostStateField.vacuum, vacuumCoeff_tmul, epsilon_vacuum]
  simp [matterVacuumCoeff, LatticeAllStateField.vacuum]

/-- Actual non-exactness, not an assumption about the quotient. -/
theorem vacuum_not_boundary : ¬ ∃ x : State D,
    LatticeBRST.totalCharge D H x = LatticeMatterGhostStateField.vacuum D := by
  rintro ⟨x, hx⟩
  have h := congrArg (vacuumCoeff D) hx
  rw [vacuumCoeff_charge, vacuumCoeff_vacuum] at h
  exact zero_ne_one h

variable (h26 : D.rank = 26)
  (hHG : H * LatticeSugawaraCurrents.gramComplex D = 1)
  (hGH : LatticeSugawaraCurrents.gramComplex D * H = 1)

/-- The actual vacuum coefficient itself descends to the actual cohomology. -/
def vacuumEvaluation : Cohomology D H h26 hHG hGH →ₗ[ℂ] ℂ :=
  (boundaries D H h26 hHG hGH).liftQ
    ((vacuumCoeff D).comp (cycles D H).subtype) (by
      intro a ha
      obtain ⟨x, hx⟩ := (mem_boundaries D H h26 hHG hGH a).mp ha
      change vacuumCoeff D (a : State D) = 0
      rw [← hx, vacuumCoeff_charge])

@[simp] theorem vacuumEvaluation_classOf (a : cycles D H) :
    vacuumEvaluation D H h26 hHG hGH (classOf D H h26 hHG hGH a) =
      vacuumCoeff D (a : State D) := rfl

theorem vacuumEvaluation_vacuum :
    vacuumEvaluation D H h26 hHG hGH (vacuum D H h26 hHG hGH) = 1 := by
  calc
    _ = vacuumCoeff D (cycleVacuum D H : State D) :=
      vacuumEvaluation_classOf D H h26 hHG hGH (cycleVacuum D H)
    _ = 1 := vacuumCoeff_vacuum D

theorem vacuum_ne_zero : vacuum D H h26 hHG hGH ≠ 0 := by
  intro hv
  have h := vacuumEvaluation_vacuum D H h26 hHG hGH
  rw [hv, map_zero] at h
  exact zero_ne_one h

theorem cohomology_nontrivial : Nontrivial (Cohomology D H h26 hHG hGH) :=
  (nontrivial_iff_vacuum_not_boundary D H h26 hHG hGH).mpr (vacuum_not_boundary D H)

end
end D5.S3.VertexAlgebra.LatticeBRSTCohomologyField
