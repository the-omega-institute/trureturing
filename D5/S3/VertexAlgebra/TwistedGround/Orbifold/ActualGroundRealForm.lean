/- GID: D5/S3/VertexAlgebra/TwistedGround/Orbifold/ActualGroundRealForm
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/Orbifold/ActualGroundRealForm
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.InnerProductSpace.PiL2]
   utility: none
   digest: Positive real form of the actual selected twisted ground pairing. -/

import Mathlib.Analysis.InnerProductSpace.PiL2
import D5.S3.VertexAlgebra.TwistedGround.ActualPairingSymmetry

/-!
The Hermitian average uses the selected finite quotient action. Its conjugate-linear
comparison operator is defined against the same bilinear ground factor as actualForm.
For the moonshine context, see Borcherds (1992), Theorems 5.1 and 6.1,
and Dong–Lin, Unitary vertex operator algebras, Theorems 4.12, 4.14 and 4.15.
The normalization of the selected ground factor is proved here by finite-dimensional
duality and the scalar commutant.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators

namespace D5.S3.VertexAlgebra.TwistedGround.Orbifold.ActualGroundRealForm

open LatticeGeneratingFieldLocality LatticeTwistedGroundRealization
open LatticeTwistedGroundRealization.SignQuotient
open LatticeHalfFockChargedTensorCoefficients
open InvariantPairing OperatorAlgebra

open private selected_central from
  D5.S3.VertexAlgebra.TwistedGround.InvariantPairing
open private selectedGroundPairing from
  D5.S3.VertexAlgebra.TwistedGround.ActualChargedAdjoint
open private ground_pairing_symmetric from
  D5.S3.VertexAlgebra.TwistedGround.ActualPairingSymmetry

local instance quotientFintype (D : LatticeData) : Fintype (Extension D ⧸ K D) :=
  Fintype.ofEquiv (F₂ × ModTwoCharge D)
    ((reducedCoordinates D).symm.trans (quotientEquiv D).toEquiv.symm)

variable (D : LatticeData) (hu : IsUnit D.G.det)

local notation "V" => ActualGround D hu
local notation "G" => Extension D ⧸ K D
local notation "ρ" => groundRepresentation D hu
/-- The ground factor of the literal selected tensor pairing `actualForm`. -/
abbrev selectedGroundForm : LinearMap.BilinForm ℂ V := (selectedGroundPairing D hu).form

local notation "B₀" => selectedGroundForm D hu

/-- A complex form conjugate-linear in its first slot and linear in its second. -/
private abbrev Sesq (W : Type*) [AddCommGroup W] [Module ℂ W] :=
  W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ

private def euclideanCoordinates :
    V ≃ₗ[ℂ] EuclideanSpace ℂ (Half (groundRank D hu)) :=
  (WithLp.linearEquiv 2 ℂ V).symm

/-- The normalized Euclidean Hermitian average over the selected quotient representation. -/
def hermitianAverage : Sesq V :=
  (Fintype.card G : ℂ)⁻¹ • ∑ g : G,
    let f := (euclideanCoordinates D hu).toLinearMap.comp (ρ g)
    ((innerₛₗ ℂ).comp f).compl₂ f

private theorem hermitianAverage_apply (x y : V) :
    hermitianAverage D hu x y =
      (Fintype.card G : ℝ)⁻¹ * ∑ g : G,
        inner ℂ (euclideanCoordinates D hu (ρ g x)) (euclideanCoordinates D hu (ρ g y)) := by
  simp [hermitianAverage, LinearMap.compl₂_apply, LinearMap.sum_apply, smul_eq_mul]

private theorem average_conj_symm (x y : V) :
    star (hermitianAverage D hu x y) = hermitianAverage D hu y x := by
  simp only [hermitianAverage_apply, Complex.star_def, map_mul, map_sum,
    Complex.conj_ofReal, inner_conj_symm]

private theorem average_pos (x : V) (hx : x ≠ 0) :
    0 < (hermitianAverage D hu x x).re := by
  rw [hermitianAverage_apply, Complex.re_ofReal_mul]
  have card_pos : 0 < (Fintype.card G : ℝ) := by
    exact_mod_cast Fintype.card_pos (α := G)
  apply mul_pos (inv_pos.mpr card_pos)
  change 0 < Complex.reLm _
  rw [map_sum Complex.reLm]
  apply Finset.sum_pos
  · intro g _
    apply (re_inner_self_pos (𝕜 := ℂ)).2
    exact (euclideanCoordinates D hu).injective.ne
      (by simpa using (Representation.apply_bijective ρ g).injective.ne hx)
  · exact Finset.univ_nonempty

private theorem average_invariant (g : G) (x y : V) :
    hermitianAverage D hu (ρ g x) (ρ g y) = hermitianAverage D hu x y := by
  simp only [hermitianAverage_apply, ← Module.End.mul_apply, ← map_mul]
  congr 1
  exact Equiv.sum_comp (Equiv.mulRight g)
    (fun k : G => inner ℂ (euclideanCoordinates D hu (ρ k x)) (euclideanCoordinates D hu (ρ k y)))

private theorem average_self_im (x : V) : (hermitianAverage D hu x x).im = 0 :=
  Complex.conj_eq_iff_im.mp (average_conj_symm D hu x x)

private theorem average_separating (x : V)
    (h : ∀ y, hermitianAverage D hu x y = 0) : x = 0 := by
  by_contra hx
  exact (ne_of_gt (average_pos D hu x hx)) (by rw [h x, Complex.zero_re])

private def coordinateConj : V →ₗ⋆[ℂ] V where
  toFun x i := star (x i)
  map_add' x y := by ext i; exact star_add (x i) (y i)
  map_smul' c x := by ext i; exact map_mul (starRingEnd ℂ) c (x i)

private theorem coordinateConj_involutive : Function.Involutive (coordinateConj D hu) := by
  intro x
  funext i
  exact star_star (x i)

private def linearizedAverage : LinearMap.BilinForm ℂ V :=
  (hermitianAverage D hu).comp (coordinateConj D hu)

private theorem linearizedAverage_nondegenerate : (linearizedAverage D hu).Nondegenerate := by
  apply LinearMap.BilinForm.Nondegenerate.ofSeparatingLeft
  intro x hx
  have hz : coordinateConj D hu x = 0 := average_separating D hu _ hx
  exact (coordinateConj_involutive D hu).injective (by simpa using hz)

private def pairingAdjoint : V →ₗ⋆[ℂ] V :=
  (coordinateConj D hu).comp
    (((linearizedAverage D hu).toDual (linearizedAverage_nondegenerate D hu)).symm.toLinearMap
      |>.comp B₀)

private theorem adjoint_eval (x y : V) :
    hermitianAverage D hu (pairingAdjoint D hu x) y = B₀ x y :=
  LinearMap.BilinForm.apply_toDual_symm_apply (hB := linearizedAverage_nondegenerate D hu)
    (B₀ x) y

private theorem adjoint_commutes (g : G) (x : V) :
    pairingAdjoint D hu (ρ g x) = ρ g (pairingAdjoint D hu x) := by
  have h (y : V) :
      hermitianAverage D hu (pairingAdjoint D hu (ρ g x)) (ρ g y) =
        hermitianAverage D hu (ρ g (pairingAdjoint D hu x)) (ρ g y) := by
    rw [adjoint_eval, average_invariant, adjoint_eval]
    exact (selectedGroundPairing D hu).invariant g x y
  apply sub_eq_zero.mp
  apply average_separating D hu
  intro y
  obtain ⟨z, rfl⟩ := (Representation.apply_bijective ρ g).surjective y
  rw [map_sub, LinearMap.sub_apply, sub_eq_zero]
  exact h z

private theorem adjoint_injective : Function.Injective (pairingAdjoint D hu) := by
  intro x y h
  apply sub_eq_zero.mp
  apply (selectedGroundPairing D hu).nondegenerate.1
  intro z
  rw [LinearMap.BilinForm.sub_left, ← adjoint_eval, ← adjoint_eval, h, sub_self]

private theorem adjoint_square_scalar :
    ∃ c : ℂ, ∀ x : V, pairingAdjoint D hu (pairingAdjoint D hu x) = c • x := by
  let A := pairingAdjoint D hu
  let square : Module.End ℂ V := A.comp A
  have commutes (g : G) : square * ρ g = ρ g * square := by
    apply LinearMap.ext
    intro x
    change A (A (ρ g x)) = ρ g (A (A x))
    rw [adjoint_commutes, adjoint_commutes]
  have rank_eq : D.rank = groundRank D hu + groundRank D hu :=
    (Classical.choose_spec
      (Classical.choose_spec (actual_twisted_ground_representation D hu))).1
  have central : ρ (QuotientGroup.mk (⟨1, 0⟩ : Extension D)) = -(1 : Module.End ℂ V) := by
    simpa [complexSign] using selected_central D hu 1
  obtain ⟨algebra⟩ := actual_operator_algebra D hu (groundRank D hu) rank_eq ρ central
  obtain ⟨c, hc⟩ := (algebra.scalar_commutant square).mp
    (fun charge => commutes (chargeLift D charge))
  exact ⟨c, fun x => DFunLike.congr_fun hc x⟩

private theorem adjoint_square_positive :
    ∃ s : ℝ, 0 < s ∧ ∀ x : V, pairingAdjoint D hu (pairingAdjoint D hu x) = (s : ℂ) • x := by
  obtain ⟨c, square⟩ := adjoint_square_scalar D hu
  let A := pairingAdjoint D hu
  let H := hermitianAverage D hu
  let u : V := fun _ => 1
  have u_ne : u ≠ 0 := fun h => one_ne_zero (congrFun h (0 : Half (groundRank D hu)))
  have Au_ne : A u ≠ 0 := fun h => u_ne
    (adjoint_injective D hu (h.trans (map_zero A).symm))
  have hu_pos := average_pos D hu u u_ne
  have ha_pos := average_pos D hu (A u) Au_ne
  have symm := ground_pairing_symmetric D hu (selectedGroundPairing D hu)
  have identity : star c * H u u = H (A u) (A u) := calc
    _ = H (A (A u)) u := by
      rw [square, H.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul]
      rfl
    _ = B₀ (A u) u := adjoint_eval D hu _ _
    _ = B₀ u (A u) := symm.eq _ _
    _ = _ := (adjoint_eval D hu u (A u)).symm
  have him := congrArg Complex.im identity
  change (star c * H u u).im = (H (A u) (A u)).im at him
  rw [Complex.mul_im, Complex.star_def, Complex.conj_im, average_self_im D hu u,
    average_self_im D hu (A u), mul_zero, zero_add] at him
  have ci : c.im = 0 :=
    neg_eq_zero.mp ((mul_eq_zero.mp him).resolve_right (ne_of_gt hu_pos))
  have hre := congrArg Complex.re identity
  change (star c * H u u).re = (H (A u) (A u)).re at hre
  rw [Complex.mul_re, Complex.star_def, Complex.conj_re, average_self_im D hu u,
    mul_zero, sub_zero] at hre
  have cr : 0 < c.re := (mul_pos_iff_of_pos_right hu_pos).mp (hre ▸ ha_pos)
  have cast_re : (c.re : ℂ) = c := Complex.ext rfl (by simpa using ci.symm)
  exact ⟨c.re, cr, fun x => by rw [cast_re, ← square]⟩

/-- Ground conjugation and its precise normalization against the averaged metric. -/
structure GroundRealForm (B : LinearMap.BilinForm ℂ V) where
  hermitian_symm : ∀ x y, star (hermitianAverage D hu x y) = hermitianAverage D hu y x
  hermitian_pos : ∀ x, x ≠ 0 → 0 < (hermitianAverage D hu x x).re
  hermitian_invariant : ∀ (g : G) x y,
    hermitianAverage D hu (ρ g x) (ρ g y) = hermitianAverage D hu x y
  adjoint : V →ₗ⋆[ℂ] V
  adjoint_eval : ∀ x y, hermitianAverage D hu (adjoint x) y = B x y
  adjoint_commutes : ∀ (g : G) x, adjoint (ρ g x) = ρ g (adjoint x)
  scale : ℝ
  scale_pos : 0 < scale
  conjugation : V →ₗ⋆[ℂ] V
  conjugation_eq : conjugation = (scale : ℂ)⁻¹ • adjoint
  involutive : Function.Involutive conjugation
  commutes : ∀ (g : G) x, conjugation (ρ g x) = ρ g (conjugation x)
  normalization : ∀ x y, B (conjugation x) y = (scale : ℂ) * hermitianAverage D hu x y
  pairing_reality : ∀ x y, B (conjugation x) (conjugation y) = star (B x y)
  positive : ∀ x, x ≠ 0 → (B (conjugation x) x).im = 0 ∧ 0 < (B (conjugation x) x).re

/-- The selected twisted ground of a unimodular lattice has a positive real form. -/
theorem actual_ground_real_form (p : {D : LatticeData // IsUnit D.G.det}) :
    Nonempty (GroundRealForm p.1 p.2 (selectedGroundForm p.1 p.2)) := by
  rcases p with ⟨D, hu⟩
  let A := pairingAdjoint D hu
  let H := hermitianAverage D hu
  obtain ⟨s, hs, square⟩ := adjoint_square_positive D hu
  let r := Real.sqrt s
  have hr : 0 < r := Real.sqrt_pos.mpr hs
  have hr_ne : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hr)
  have hrs : (r : ℂ) * (r : ℂ) = (s : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hs.le]
  have star_inv : starRingEnd ℂ ((r : ℂ)⁻¹) = (r : ℂ)⁻¹ := by
    rw [map_inv₀, Complex.conj_ofReal]
  let J : ActualGround D hu →ₗ⋆[ℂ] ActualGround D hu := (r : ℂ)⁻¹ • A
  have involution : Function.Involutive J := by
    intro x
    change (r : ℂ)⁻¹ • A ((r : ℂ)⁻¹ • A x) = x
    rw [A.map_smulₛₗ, star_inv, square, ← hrs, mul_smul,
      inv_smul_smul₀ hr_ne, inv_smul_smul₀ hr_ne]
  have normalization (x y : ActualGround D hu) :
      selectedGroundForm D hu (J x) y = (r : ℂ) * H x y := by
    change selectedGroundForm D hu ((r : ℂ)⁻¹ • A x) y = (r : ℂ) * H x y
    rw [LinearMap.BilinForm.smul_left, ← adjoint_eval D hu (A x) y, square, ← hrs,
      H.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, map_mul, Complex.conj_ofReal,
      mul_assoc (r : ℂ) (r : ℂ) (H x y), inv_mul_cancel_left₀ hr_ne]
  have symm := ground_pairing_symmetric D hu (selectedGroundPairing D hu)
  refine ⟨{
    hermitian_symm := average_conj_symm D hu
    hermitian_pos := average_pos D hu
    hermitian_invariant := average_invariant D hu
    adjoint := A
    adjoint_eval := adjoint_eval D hu
    adjoint_commutes := adjoint_commutes D hu
    scale := r
    scale_pos := hr
    conjugation := J
    conjugation_eq := rfl
    involutive := involution
    commutes := ?_
    normalization := normalization
    pairing_reality := ?_
    positive := ?_ }⟩
  · intro g x
    change (r : ℂ)⁻¹ • A (groundRepresentation D hu g x) =
      groundRepresentation D hu g ((r : ℂ)⁻¹ • A x)
    rw [adjoint_commutes, map_smul]
  · intro x y
    calc
      selectedGroundForm D hu (J x) (J y) = (r : ℂ) * H x (J y) := normalization _ _
      _ = star ((r : ℂ) * H (J y) x) := by
        rw [Complex.star_def, map_mul, Complex.conj_ofReal, ← Complex.star_def, average_conj_symm]
      _ = star (selectedGroundForm D hu (J (J y)) x) := by rw [normalization]
      _ = star (selectedGroundForm D hu x y) := by rw [involution, symm.eq y x]
  · intro x hx
    rw [normalization, Complex.re_ofReal_mul, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, average_self_im, mul_zero, zero_mul, zero_add]
    exact ⟨rfl, mul_pos hr (average_pos D hu x hx)⟩

/--
info: 'D5.S3.VertexAlgebra.TwistedGround.Orbifold.ActualGroundRealForm.actual_ground_real_form' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms actual_ground_real_form

end D5.S3.VertexAlgebra.TwistedGround.Orbifold.ActualGroundRealForm
