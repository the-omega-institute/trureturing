/- GID: D5/S3/VertexAlgebra/TwistedGround/FlipAverage
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/FlipAverage
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Trace]
   utility: none
   digest: The flip-average trace of the selected actual ground representation is one. -/

import D5.S3.VertexAlgebra.TwistedGround.InvariantPairing
import D5.S3.VertexAlgebra.TwistedGround.GaussElimination

/-! The Frobenius-Schur trace is evaluated on the originally selected representation. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.TwistedGround.FlipAverage

open LatticeGeneratingFieldLocality LatticeTwistedGroundRealization
open LatticeTwistedGroundRealization.SignQuotient
open LatticeHalfFockChargedTensorCoefficients LatticeHalfFockGradedTrace
open TwistedGround.OperatorAlgebra
open scoped BigOperators

noncomputable section

private theorem trace_flip_pullback {ι : Type*} [Finite ι]
    (T : Module.End ℂ (ι → ℂ))
    (L : Module.End ℂ (LinearMap.BilinForm ℂ (ι → ℂ)))
    (hL : ∀ B x y, L B x y = B (T y) (T x)) :
    LinearMap.trace ℂ _ L = LinearMap.trace ℂ _ (T * T) := by
  classical
  let := Fintype.ofFinite ι
  let b := Pi.basisFun ℂ ι
  let e := b.linearMap b.dualBasis
  have coordinates (B : LinearMap.BilinForm ℂ (ι → ℂ)) (i j : ι) :
      e.repr B (i, j) = B (b j) (b i) := by
    simp [e, Module.Basis.linearMap_repr_apply, Matrix.stdBasis,
      LinearMap.toMatrix_apply]
  have elementary (i j : ι) (x y : ι → ℂ) :
      e (i, j) x y = x j * y i := by
    simp [e, Module.Basis.linearMap_apply, Matrix.toLin_apply,
      Matrix.stdBasis_eq_single, Matrix.mulVec, dotProduct, b,
      Matrix.single, ite_and]
  rw [LinearMap.trace_eq_matrix_trace ℂ e,
    LinearMap.trace_eq_matrix_trace ℂ b, LinearMap.toMatrix_mul]
  simp only [Matrix.trace]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Matrix.diag, LinearMap.toMatrix_apply]
  rw [coordinates, hL, elementary]
  simp [b, mul_comm]

attribute [local instance] InvariantPairing.reducedFintype
  InvariantPairing.quotientFintype InvariantPairing.cardInvertible

/-- The Frobenius-Schur average on the originally selected ground has positive sign. -/
theorem actual_flip_average_trace (D : LatticeData) (hu : IsUnit D.G.det) :
    LinearMap.trace ℂ (LinearMap.BilinForm ℂ (ActualGround D hu))
      (LinearMap.BilinForm.flipHom.toLinearMap.comp
        (Representation.linHom (groundRepresentation D hu)
          (groundRepresentation D hu).dual).averageMap) = 1 := by
  classical
  let rho := groundRepresentation D hu
  let forms := Representation.linHom rho rho.dual
  let flip : Module.End ℂ (LinearMap.BilinForm ℂ (ActualGround D hu)) :=
    LinearMap.BilinForm.flipHom.toLinearMap
  have contraction (g : Extension D ⧸ K D) :
      LinearMap.trace ℂ _ (flip.comp (forms g)) = rho.character (g⁻¹ * g⁻¹) := by
    rw [Representation.character, map_mul]
    exact trace_flip_pullback (rho g⁻¹) _ (by intro B x y; rfl)
  have expanded : LinearMap.trace ℂ _ (flip.comp forms.averageMap) =
      (Fintype.card (Extension D ⧸ K D) : ℂ)⁻¹ *
        ∑ g : Extension D ⧸ K D, rho.character (g * g) := by
    have averaged : forms.averageMap =
        (Fintype.card (Extension D ⧸ K D) : ℂ)⁻¹ •
          ∑ g : Extension D ⧸ K D, forms g := by
      simp [Representation.averageMap, GroupAlgebra.average, map_sum, invOf_eq_inv]
    change LinearMap.trace ℂ _ (flip * forms.averageMap) = _
    rw [averaged, mul_smul_comm, Finset.mul_sum, map_smul, map_sum]
    simp only [smul_eq_mul, Module.End.mul_eq_comp, contraction]
    congr 1
    exact Fintype.sum_equiv (Equiv.inv (Extension D ⧸ K D))
      (fun g => rho.character (g⁻¹ * g⁻¹))
      (fun g => rho.character (g * g)) (by intro g; rfl)
  have squared (s : F₂) (a : ModTwoCharge D) :
      rho.character (((quotientEquiv D).symm (⟨s, a⟩ : ReducedExtension D)) *
        ((quotientEquiv D).symm (⟨s, a⟩ : ReducedExtension D))) =
        complexSign (modTwoCocycle D a a) *
          (Module.finrank ℂ (ActualGround D hu) : ℂ) := by
    rw [← map_mul, reduced_square]
    exact InvariantPairing.central_character D hu _
  let e := (quotientEquiv D).toEquiv.trans (InvariantPairing.reducedCoordinates D)
  have sum_squares : (∑ g : Extension D ⧸ K D, rho.character (g * g)) =
      2 * (2 : ℂ) ^ groundRank D hu *
        (Module.finrank ℂ (ActualGround D hu) : ℂ) := by
    rw [← e.symm.sum_comp]
    change (∑ x : F₂ × ModTwoCharge D,
      rho.character (((quotientEquiv D).symm ⟨x.1, x.2⟩) *
        ((quotientEquiv D).symm ⟨x.1, x.2⟩))) = _
    rw [Fintype.sum_prod_type]
    simp_rw [squared]
    rw [show (∑ s : F₂, ∑ a : ModTwoCharge D,
      complexSign (modTwoCocycle D a a) *
        (Module.finrank ℂ (ActualGround D hu) : ℂ)) =
      2 * ((∑ a : ModTwoCharge D, complexSign (modTwoCocycle D a a)) *
        (Module.finrank ℂ (ActualGround D hu) : ℂ)) by simp [Finset.sum_mul, F₂]]
    rw [GaussElimination.actual_quadratic_gauss_sum D hu]
    ring
  have card : Fintype.card (Extension D ⧸ K D) = 2 * 2 ^ D.rank := by
    rw [Fintype.card_congr (quotientEquiv D).toEquiv,
      Fintype.card_congr (InvariantPairing.reducedCoordinates D)]
    simp [F₂, ModTwoCharge]
  have rank_eq : D.rank = groundRank D hu + groundRank D hu :=
    (Classical.choose_spec
      (Classical.choose_spec (actual_twisted_ground_representation D hu))).1
  change LinearMap.trace ℂ _ (flip.comp forms.averageMap) = _
  rw [expanded, sum_squares, actual_ground_finrank, card]
  have half : D.rank / 2 = groundRank D hu := by rw [rank_eq]; omega
  simp only [half, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]
  rw [rank_eq, pow_add]
  field_simp

end
end D5.S3.VertexAlgebra.TwistedGround.FlipAverage
