/- GID: D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PairingDefectAlgebra
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PairingDefectAlgebra
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Quadratic covariance changes pairing polynomials by a partial-pairing convolution. -/

import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.AssignmentMomentReindex
import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.PartialPairingPolynomial
import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.QuadraticCubicExpansion

/-! Subset moments and the exact algebra of the finite pairing-defect convolution. -/

open scoped BigOperators

namespace D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer

noncomputable section
set_option autoImplicit false
attribute [local instance] Classical.propDecidable

variable {κ ι A : Type*} [Fintype κ] [DecidableEq κ] [Fintype ι]
  [CommRing A] [Algebra ℝ A]

/-- The original family moment on a subset of labels. -/
def subsetFamilyMoment (ℓ : A →ₗ[ℝ] ℝ) (Y : ι → A) (f : κ → ι → ℝ)
    (U : Finset κ) : ℝ := ℓ (∏ i ∈ U, ∑ d, f i d • Y d)

/-- The existing ordered distinct-index moment, with a canonical enumeration of labels. -/
def subsetDistinctMoment (ℓ : A →ₗ[ℝ] ℝ) (Y : ι → A) (f : κ → ι → ℝ)
    (U : Finset κ) : ℝ :=
  distinctIndexMoment ℓ Y (fun j : Fin (Fintype.card U) =>
    f (((Fintype.equivFin U).symm j).val))

/-- The scalar sum of the weight product attached to a label subset. -/
def subsetWeightSum (f : κ → ι → ℝ) (U : Finset κ) : ℝ :=
  indexSum (fun d => ∏ i ∈ U, f i d)

/-- The distinct-index moment minus its perfect-pairing polynomial. -/
def subsetPairingDefect (ℓ : A →ₗ[ℝ] ℝ) (Y : ι → A) (f : κ → ι → ℝ)
    (U : Finset κ) : ℝ :=
  subsetDistinctMoment ℓ Y f U -
    finitePairingPolynomial U (subsetDistinctMoment ℓ Y f)

private theorem subset_pair_covariance
    (ℓ : A →ₗ[ℝ] ℝ) (Y : ι → A) (a b : ℝ)
    (h1 : ℓ 1 = 1) (h0 : ∀ d, ℓ (Y d) = 0)
    (hquad : ∀ d, Y d ^ 2 = a • Y d + algebraMap ℝ A b)
    (f : κ → ι → ℝ) (E : Finset κ) (hE : E.card = 2) :
    subsetFamilyMoment ℓ Y f E = subsetDistinctMoment ℓ Y f E + b * subsetWeightSum f E := by
  let e : E ≃ Fin 2 := Fintype.equivOfCardEq (by simpa using hE)
  let g : Fin 2 → ι → ℝ := fun i => f (e.symm i).val
  have hV : subsetFamilyMoment ℓ Y f E = quadraticFamilyMoment ℓ Y g := by
    unfold subsetFamilyMoment quadraticFamilyMoment
    congr 1
    rw [← Finset.prod_attach E]
    apply Fintype.prod_equiv e
    intro i
    simp only [g, Equiv.symm_apply_apply]
  have hR : subsetDistinctMoment ℓ Y f E = distinctIndexMoment ℓ Y g := by
    unfold subsetDistinctMoment
    rw [← retained_assignment_reindex ℓ Y E f]
    exact assignment_moment_reindex ℓ Y e (fun i : E => f i.val)
  have hT : subsetWeightSum f E = indexSum (g 0 * g 1) := by
    unfold subsetWeightSum indexSum
    apply Finset.sum_congr rfl
    intro d hd
    change (∏ i ∈ E, f i d) = g 0 d * g 1 d
    rw [← Finset.prod_attach E]
    have hp : (∏ i : E, f i.val d) = ∏ j : Fin 2, g j d := by
      apply Fintype.prod_equiv e
      intro i
      simp only [g, Equiv.symm_apply_apply]
    simpa only [Finset.attach_eq_univ, Fin.prod_univ_two, Pi.mul_apply] using hp
  have hg : (![g 0, g 1] : Fin 2 → ι → ℝ) = g := by
    funext i
    fin_cases i <;> rfl
  rw [hV, hR, hT]
  simpa only [hg] using quadratic_second_moment_eq ℓ Y a b h1 h0 hquad (g 0) (g 1)

private theorem subset_pairing_polynomial_expansion
    (ℓ : A →ₗ[ℝ] ℝ) (Y : ι → A) (a b : ℝ)
    (h1 : ℓ 1 = 1) (h0 : ∀ d, ℓ (Y d) = 0)
    (hquad : ∀ d, Y d ^ 2 = a • Y d + algebraMap ℝ A b)
    (f : κ → ι → ℝ) (U : Finset κ) :
    finitePairingPolynomial U (subsetFamilyMoment ℓ Y f) =
      ∑ P : Finset (Finset κ) with IsPartialPairing U P,
        b ^ P.card * (∏ E ∈ P, subsetWeightSum f E) *
          finitePairingPolynomial (U \ pairingSupport P) (subsetDistinctMoment ℓ Y f) := by
  have hV : finitePairingPolynomial U (subsetFamilyMoment ℓ Y f) =
      finitePairingPolynomial U
        (fun E => b * subsetWeightSum f E + subsetDistinctMoment ℓ Y f E) := by
    unfold finitePairingPolynomial
    apply Finset.sum_congr rfl
    intro M hM
    apply Finset.prod_congr rfl
    intro E hE
    have hcard : E.card = 2 := ((Finset.mem_filter.mp hM).2).1.1 E hE
    rw [subset_pair_covariance ℓ Y a b h1 h0 hquad f E hcard, add_comm]
  rw [hV, finitePairingPolynomial_add]
  apply Finset.sum_congr rfl
  intro P hP
  simp only [Finset.prod_mul_distrib, Finset.prod_const]

/-- Subtracting the family covariance pairing polynomial from the partial-pairing
convolution of distinct moments gives the same convolution of distinct pairing defects.
This identity needs no bound on any distinct-index moment and applies at every finite order. -/
theorem subset_pairing_defect_convolution
    (ℓ : A →ₗ[ℝ] ℝ) (Y : ι → A) (a b : ℝ)
    (h1 : ℓ 1 = 1) (h0 : ∀ d, ℓ (Y d) = 0)
    (hquad : ∀ d, Y d ^ 2 = a • Y d + algebraMap ℝ A b)
    (f : κ → ι → ℝ) (U : Finset κ) :
    (∑ P : Finset (Finset κ) with IsPartialPairing U P,
      b ^ P.card * (∏ E ∈ P, subsetWeightSum f E) *
        subsetDistinctMoment ℓ Y f (U \ pairingSupport P)) -
      finitePairingPolynomial U (subsetFamilyMoment ℓ Y f) =
    ∑ P : Finset (Finset κ) with IsPartialPairing U P,
      b ^ P.card * (∏ E ∈ P, subsetWeightSum f E) *
        subsetPairingDefect ℓ Y f (U \ pairingSupport P) := by
  rw [subset_pairing_polynomial_expansion ℓ Y a b h1 h0 hquad f U,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro P hP
  unfold subsetPairingDefect
  ring

end
end D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
