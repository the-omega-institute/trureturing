/- GID: D5/S3/VertexAlgebra/TwistedGround/InvariantPairing
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/InvariantPairing
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A finite invariant bilinear pairing on the selected actual twisted ground. -/

import D5.S3.VertexAlgebra.LatticeHalfFockGradedTrace
import Mathlib.RepresentationTheory.Character
import Mathlib.LinearAlgebra.Matrix.BilinearForm

/-! Finite averaging on the representation selected by the actual ground existence theorem. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.TwistedGround.InvariantPairing

open LatticeGeneratingFieldLocality LatticeTwistedGroundRealization
open LatticeTwistedGroundRealization.SignQuotient
open LatticeHalfFockChargedTensorCoefficients LatticeHalfFockGradedTrace
open TwistedGround.OperatorAlgebra
open scoped BigOperators

noncomputable section

def reducedCoordinates (D : LatticeData) :
    ReducedExtension D ≃ F₂ × ModTwoCharge D where
  toFun x := (x.sign, x.charge)
  invFun x := ⟨x.1, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

local instance reducedFintype (D : LatticeData) : Fintype (ReducedExtension D) :=
  Fintype.ofEquiv (F₂ × ModTwoCharge D) (reducedCoordinates D).symm

local instance quotientFintype (D : LatticeData) : Fintype (Extension D ⧸ K D) :=
  Fintype.ofEquiv (ReducedExtension D) (quotientEquiv D).toEquiv.symm

local instance cardInvertible (D : LatticeData) :
    Invertible (Fintype.card (Extension D ⧸ K D) : ℂ) :=
  invertibleOfNonzero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)

def formRepresentation (D : LatticeData) (hu : IsUnit D.G.det) :
    Representation ℂ (Extension D ⧸ K D) (LinearMap.BilinForm ℂ (ActualGround D hu)) :=
  Representation.linHom (groundRepresentation D hu) (groundRepresentation D hu).dual

def formAverage (D : LatticeData) (hu : IsUnit D.G.det) :
    Module.End ℂ (LinearMap.BilinForm ℂ (ActualGround D hu)) :=
  (formRepresentation D hu).averageMap

private theorem reduced_central (D : LatticeData) (s : F₂) :
    (quotientEquiv D).symm (⟨s, 0⟩ : ReducedExtension D) =
      QuotientGroup.mk (⟨s, 0⟩ : Extension D) := by
  apply (quotientEquiv D).injective
  rw [MulEquiv.apply_symm_apply]
  change (⟨s, 0⟩ : ReducedExtension D) = reduction D ⟨s, 0⟩
  ext <;> simp [reduction, reduceCharge]

private theorem selected_central (D : LatticeData) (hu : IsUnit D.G.det) (s : F₂) :
    groundRepresentation D hu (QuotientGroup.mk (⟨s, 0⟩ : Extension D)) =
      complexSign s • (1 : Module.End ℂ (ActualGround D hu)) := by
  have selected := Classical.choose_spec
    (Classical.choose_spec (actual_twisted_ground_representation D hu))
  fin_cases s
  · change groundRepresentation D hu 1 = _
    simp [complexSign]
  · simpa [complexSign, F₂, groundRepresentation, ActualGround, groundRank] using selected.2.2.1

theorem central_character (D : LatticeData) (hu : IsUnit D.G.det) (s : F₂) :
    (groundRepresentation D hu).character
      ((quotientEquiv D).symm (⟨s, 0⟩ : ReducedExtension D)) =
        complexSign s * (Module.finrank ℂ (ActualGround D hu) : ℂ) := by
  rw [reduced_central, Representation.character, selected_central]
  simp

private theorem character_square_sum (D : LatticeData) (hu : IsUnit D.G.det) :
    ∑ g : Extension D ⧸ K D, (groundRepresentation D hu).character g ^ 2 =
      2 * (Module.finrank ℂ (ActualGround D hu) : ℂ) ^ 2 := by
  classical
  let e := (quotientEquiv D).toEquiv.trans (reducedCoordinates D)
  rw [← e.symm.sum_comp]
  change (∑ x : F₂ × ModTwoCharge D,
    (groundRepresentation D hu).character ((quotientEquiv D).symm ⟨x.1, x.2⟩) ^ 2) = _
  rw [Fintype.sum_prod_type]
  have terms (s : F₂) (a : ModTwoCharge D) :
      (groundRepresentation D hu).character
        ((quotientEquiv D).symm (⟨s, a⟩ : ReducedExtension D)) ^ 2 =
          if a = 0 then (Module.finrank ℂ (ActualGround D hu) : ℂ) ^ 2 else 0 := by
    split_ifs with ha
    · subst a
      rw [central_character, mul_pow]
      have sign : complexSign s ^ 2 = 1 := by
        simpa [pow_two] using sign_square s
      rw [sign, one_mul]
    · have charge : quotientCharge D
          ((quotientEquiv D).symm (⟨s, a⟩ : ReducedExtension D)) = a := by
        simp [quotientCharge]
      rw [Representation.character,
        actual_quotient_charge_ground_trace_zero D hu _ (by rw [charge]; exact ha),
        zero_pow (by decide)]
  simp_rw [terms]
  simp [F₂]

theorem average_trace (D : LatticeData) (hu : IsUnit D.G.det) :
    LinearMap.trace ℂ (LinearMap.BilinForm ℂ (ActualGround D hu))
      (formAverage D hu) = 1 := by
  classical
  have character_sum : ∑ g : Extension D ⧸ K D,
      (formRepresentation D hu).character g =
        2 * (Module.finrank ℂ (ActualGround D hu) : ℂ) ^ 2 := by
    simp only [formRepresentation, Representation.char_linHom,
      Representation.char_dual, ← pow_two]
    rw [Fintype.sum_equiv (Equiv.inv (Extension D ⧸ K D))
      (fun g => (groundRepresentation D hu).character g⁻¹ ^ 2)
      (fun g => (groundRepresentation D hu).character g ^ 2) (by intro g; simp)]
    exact character_square_sum D hu
  have card : Fintype.card (Extension D ⧸ K D) = 2 * 2 ^ D.rank := by
    rw [Fintype.card_congr (quotientEquiv D).toEquiv,
      Fintype.card_congr (reducedCoordinates D)]
    simp [F₂, ModTwoCharge]
  have rank_eq : D.rank = groundRank D hu + groundRank D hu :=
    (Classical.choose_spec
      (Classical.choose_spec (actual_twisted_ground_representation D hu))).1
  have dimension : (Module.finrank ℂ (ActualGround D hu) : ℂ) ^ 2 =
      (2 : ℂ) ^ D.rank := by
    rw [actual_ground_finrank, rank_eq]
    have half : (groundRank D hu + groundRank D hu) / 2 = groundRank D hu := by omega
    simp only [half, Nat.cast_pow, Nat.cast_ofNat, pow_two, pow_add]
  change LinearMap.trace ℂ _ ((formRepresentation D hu).averageMap) = _
  have expansion : LinearMap.trace ℂ _ ((formRepresentation D hu).averageMap) =
      (Fintype.card (Extension D ⧸ K D) : ℂ)⁻¹ *
        ∑ g : Extension D ⧸ K D, (formRepresentation D hu).character g := by
    simp [Representation.averageMap, GroupAlgebra.average, Representation.character,
      map_sum, invOf_eq_inv]
  rw [expansion, character_sum, dimension, card]
  simp only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]
  exact inv_mul_cancel₀ (mul_ne_zero (by norm_num) (pow_ne_zero _ (by norm_num)))

private theorem average_nonzero (D : LatticeData) (hu : IsUnit D.G.det) :
    formAverage D hu ≠ 0 := by
  intro vanished
  have trace := average_trace D hu
  rw [vanished, map_zero] at trace
  exact zero_ne_one trace

theorem averaged_invariant (D : LatticeData) (hu : IsUnit D.G.det)
    (B : LinearMap.BilinForm ℂ (ActualGround D hu))
    (g : Extension D ⧸ K D) (u v : ActualGround D hu) :
    formAverage D hu B (groundRepresentation D hu g u) (groundRepresentation D hu g v) =
      formAverage D hu B u v := by
  have invariant := (formRepresentation D hu).averageMap_invariant B g⁻¹
  have evaluated := congrArg (fun form : LinearMap.BilinForm ℂ (ActualGround D hu) =>
    form u v) invariant
  simpa [formRepresentation, Representation.linHom, Representation.dual,
    formAverage] using evaluated

private def radical (D : LatticeData) (hu : IsUnit D.G.det)
    (B : LinearMap.BilinForm ℂ (ActualGround D hu))
    (invariant : ∀ (g : Extension D ⧸ K D) (u v : ActualGround D hu),
      B (groundRepresentation D hu g u) (groundRepresentation D hu g v) = B u v) :
    Subrepresentation (groundRepresentation D hu) where
  toSubmodule := {
    carrier := {u | ∀ v, B u v = 0}
    zero_mem' := by simp
    add_mem' := by intro u v hx hy w; simp [LinearMap.BilinForm.add_left, hx w, hy w]
    smul_mem' := by intro c u hx v; simp [LinearMap.BilinForm.smul_left, hx v] }
  apply_mem_toSubmodule g u hx v := by
    have inverse : groundRepresentation D hu g (groundRepresentation D hu g⁻¹ v) = v := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]
      rfl
    rw [← inverse, invariant]
    exact hx _

theorem invariant_nondegenerate (D : LatticeData) (hu : IsUnit D.G.det)
    (B : LinearMap.BilinForm ℂ (ActualGround D hu)) (nonzero : B ≠ 0)
    (invariant : ∀ (g : Extension D ⧸ K D) (u v : ActualGround D hu),
      B (groundRepresentation D hu g u) (groundRepresentation D hu g v) = B u v) :
    B.Nondegenerate := by
  let : (groundRepresentation D hu).IsIrreducible :=
    (Classical.choose_spec
      (Classical.choose_spec (actual_twisted_ground_representation D hu))).2.1
  apply LinearMap.BilinForm.Nondegenerate.ofSeparatingLeft
  rcases eq_bot_or_eq_top (radical D hu B invariant) with bottom | top
  · intro u hx
    have member : u ∈ radical D hu B invariant := hx
    rw [bottom] at member
    exact member
  · exfalso
    apply nonzero
    apply LinearMap.ext
    intro u
    apply LinearMap.ext
    intro v
    have member : u ∈ radical D hu B invariant := by rw [top]; trivial
    exact member v

theorem ground_signed_adjoint (D : LatticeData) (hu : IsUnit D.G.det)
    (B : LinearMap.BilinForm ℂ (ActualGround D hu))
    (invariant : ∀ (g : Extension D ⧸ K D) (u v : ActualGround D hu),
      B (groundRepresentation D hu g u) (groundRepresentation D hu g v) = B u v)
    (charge : Charge D) (u v : ActualGround D hu) :
    B (groundAction D hu charge u) v =
      paritySign (bilinear D charge charge / 2) * B u (groundAction D hu charge v) := by
  have square := (Classical.choose_spec
    (Classical.choose_spec (actual_twisted_ground_representation D hu))).2.2.2.2.2.1 charge
  have inverse : groundAction D hu charge (groundAction D hu charge v) =
      paritySign (bilinear D charge charge / 2) • v := by
    change ((groundAction D hu charge) ^ 2) v = _
    rw [show groundAction D hu charge ^ 2 =
      paritySign (bilinear D charge charge / 2) • 1 from square]
    rfl
  have pairing := invariant (groundLift D charge) u (groundAction D hu charge v)
  change B (groundAction D hu charge u)
    (groundAction D hu charge (groundAction D hu charge v)) = _ at pairing
  rw [inverse, LinearMap.BilinForm.smul_right] at pairing
  have sign : paritySign (bilinear D charge charge / 2) ^ 2 = 1 := by
    simp [paritySign]
  calc
    B (groundAction D hu charge u) v =
        paritySign (bilinear D charge charge / 2) ^ 2 *
          B (groundAction D hu charge u) v := by rw [sign, one_mul]
    _ = paritySign (bilinear D charge charge / 2) * B u (groundAction D hu charge v) := by
      rw [pow_two, mul_assoc, pairing]

/-- The pairing is complex bilinear. Symmetry is a separate quadratic Gauss-sign assertion. -/
structure GroundPairing (D : LatticeData) (hu : IsUnit D.G.det) where
  form : LinearMap.BilinForm ℂ (ActualGround D hu)
  nondegenerate : form.Nondegenerate
  invariant : ∀ (g : Extension D ⧸ K D) (u v : ActualGround D hu),
    form (groundRepresentation D hu g u) (groundRepresentation D hu g v) = form u v
  signed_adjoint : ∀ (charge : Charge D) (u v : ActualGround D hu),
    form (groundAction D hu charge u) v =
      paritySign (bilinear D charge charge / 2) * form u (groundAction D hu charge v)

theorem actual_ground_pairing (D : LatticeData) (hu : IsUnit D.G.det) :
    Nonempty (GroundPairing D hu) := by
  classical
  let basis := (Pi.basisFun ℂ (Half (groundRank D hu))).linearMap
    (Pi.basisFun ℂ (Half (groundRank D hu))).dualBasis
  have seed : ∃ i, formAverage D hu (basis i) ≠ 0 := by
    by_contra absent
    push_neg at absent
    apply average_nonzero D hu
    exact basis.ext (fun i => by simpa using absent i)
  obtain ⟨i, nonzero⟩ := seed
  refine ⟨{
    form := formAverage D hu (basis i)
    nondegenerate := invariant_nondegenerate D hu _ nonzero (averaged_invariant D hu (basis i))
    invariant := averaged_invariant D hu (basis i)
    signed_adjoint := ground_signed_adjoint D hu _ (averaged_invariant D hu (basis i)) }⟩

#print axioms actual_ground_pairing

end

end D5.S3.VertexAlgebra.TwistedGround.InvariantPairing
