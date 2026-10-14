/- GID: D5/S3/VertexAlgebra/VertexOperatorTensorProduct
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/VertexOperatorTensorProduct
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Pointwise finite integer-mode convolution on arbitrary algebraic tensors. -/

/-
proof_shape: diagonal_finite: content; mode_bounded: content
escape_witness: State-dependent two-sided diagonal bounds permit bilinear
extension to every algebraic tensor and imply all-state Laurent truncation.
admission_basis: escape-witness
Classical source: algebraic tensor products of formal fields.
The operator tensor product does not supply a Koszul state-assignment rule.
-/

import Mathlib.Algebra.Vertex.VertexOperator
import Mathlib.LinearAlgebra.TensorProduct.Map
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace D5.S3.VertexAlgebra.VertexOperatorTensorProduct

open scoped TensorProduct VertexOperator

universe u v

variable {U : Type u} {V : Type v}
variable [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V]

def upper (A : VertexOperator ℂ U) (vector : U) : ℤ :=
  -((HahnModule.of ℂ).symm (A vector)).order - 1

theorem mode_zero_above (A : VertexOperator ℂ U) (vector : U) (index : ℤ)
    (bound : upper A vector < index) : (A[[index]]) vector = 0 := by
  apply VertexOperator.ncoeff_eq_zero_of_lt_order
  dsimp [upper] at bound
  omega

def diagonal (A : VertexOperator ℂ U) (B : VertexOperator ℂ V)
    (index : ℤ) (left : U) (right : V) (first : ℤ) : U ⊗[ℂ] V :=
  (A[[first]]) left ⊗ₜ[ℂ] (B[[index - 1 - first]]) right

theorem diagonal_support (A : VertexOperator ℂ U) (B : VertexOperator ℂ V)
    (index : ℤ) (left : U) (right : V) :
    Function.support (diagonal A B index left right) ⊆
      Set.Icc (index - 1 - upper B right) (upper A left) := by
  intro first member
  change diagonal A B index left right first ≠ 0 at member
  constructor
  · by_contra bound
    have vanish := mode_zero_above B right (index - 1 - first) (by omega)
    exact member (by simp [diagonal, vanish])
  · by_contra bound
    have vanish := mode_zero_above A left first (by omega)
    exact member (by simp [diagonal, vanish])

theorem diagonal_finite (A : VertexOperator ℂ U) (B : VertexOperator ℂ V)
    (index : ℤ) (left : U) (right : V) :
    Function.HasFiniteSupport (diagonal A B index left right) :=
  (Set.finite_Icc _ _).subset (diagonal_support A B index left right)

def pureMode (A : VertexOperator ℂ U) (B : VertexOperator ℂ V)
    (index : ℤ) (left : U) (right : V) : U ⊗[ℂ] V :=
  ∑ᶠ first : ℤ, diagonal A B index left right first

def modeBilinear (A : VertexOperator ℂ U) (B : VertexOperator ℂ V)
    (index : ℤ) : U →ₗ[ℂ] V →ₗ[ℂ] U ⊗[ℂ] V where
  toFun left := {
    toFun := pureMode A B index left
    map_add' first second := by
      simp only [pureMode, diagonal, map_add, TensorProduct.tmul_add]
      exact finsum_add_distrib (diagonal_finite A B index left first)
        (diagonal_finite A B index left second)
    map_smul' scalar right := by
      simp only [pureMode, diagonal, map_smul, TensorProduct.tmul_smul]
      exact (smul_finsum' scalar (diagonal_finite A B index left right)).symm }
  map_add' first second := by
    ext right
    change pureMode A B index (first + second) right =
      pureMode A B index first right + pureMode A B index second right
    simp only [pureMode, diagonal, map_add, TensorProduct.add_tmul]
    exact finsum_add_distrib (diagonal_finite A B index first right)
      (diagonal_finite A B index second right)
  map_smul' scalar left := by
    ext right
    change pureMode A B index (scalar • left) right = scalar • pureMode A B index left right
    simp only [pureMode, diagonal, map_smul]
    exact (smul_finsum' scalar (diagonal_finite A B index left right)).symm

def mode (A : VertexOperator ℂ U) (B : VertexOperator ℂ V)
    (index : ℤ) : Module.End ℂ (U ⊗[ℂ] V) :=
  TensorProduct.lift (modeBilinear A B index)

theorem mode_tmul (A : VertexOperator ℂ U) (B : VertexOperator ℂ V)
    (index : ℤ) (left : U) (right : V) :
    mode A B index (left ⊗ₜ[ℂ] right) =
      ∑ᶠ first : ℤ, (A[[first]]) left ⊗ₜ[ℂ] (B[[index - 1 - first]]) right := by
  rfl

theorem mode_tmul_zero (A : VertexOperator ℂ U) (B : VertexOperator ℂ V)
    (index : ℤ) (left : U) (right : V)
    (bound : upper A left + upper B right + 1 < index) :
    mode A B index (left ⊗ₜ[ℂ] right) = 0 := by
  rw [mode_tmul]
  apply finsum_eq_zero_of_forall_eq_zero
  intro first
  by_cases firstBound : upper A left < first
  · simp [mode_zero_above A left first firstBound]
  · have secondBound : upper B right < index - 1 - first := by omega
    simp [mode_zero_above B right (index - 1 - first) secondBound]

theorem mode_bounded (A : VertexOperator ℂ U) (B : VertexOperator ℂ V)
    (vector : U ⊗[ℂ] V) : ∃ bound : ℤ, ∀ index : ℤ, bound < index →
      mode A B index vector = 0 := by
  induction vector using TensorProduct.induction_on with
  | zero => exact ⟨0, fun _ _ => map_zero _⟩
  | tmul left right =>
      exact ⟨upper A left + upper B right + 1,
        fun index bound => mode_tmul_zero A B index left right bound⟩
  | add first second firstIH secondIH =>
      obtain ⟨firstBound, firstVan⟩ := firstIH
      obtain ⟨secondBound, secondVan⟩ := secondIH
      refine ⟨max firstBound secondBound, ?_⟩
      intro index bound
      rw [map_add, firstVan index (lt_of_le_of_lt (le_max_left _ _) bound),
        secondVan index (lt_of_le_of_lt (le_max_right _ _) bound), add_zero]

def field (A : VertexOperator ℂ U) (B : VertexOperator ℂ V) :
    VertexOperator ℂ (U ⊗[ℂ] V) :=
  VertexOperator.of_coeff (fun power => mode A B (-power - 1)) (by
    intro vector
    obtain ⟨bound, vanishes⟩ := mode_bounded A B vector
    refine ⟨-bound - 1, ?_⟩
    intro power member
    change mode A B (-power - 1) vector ≠ 0 at member
    by_contra below
    exact member (vanishes (-power - 1) (by omega)))

theorem field_mode (A : VertexOperator ℂ U) (B : VertexOperator ℂ V) (index : ℤ) :
    (field A B)[[index]] = mode A B index := by
  simp only [field, VertexOperator.ncoeff_of_coeff]
  congr 1
  omega

theorem field_add_left (A C : VertexOperator ℂ U) (B : VertexOperator ℂ V) :
    field (A + C) B = field A B + field C B := by
  apply HVertexOperator.coeff_inj
  funext power
  simp only [map_add, Pi.add_apply, VertexOperator.coeff_eq_ncoeff, field_mode]
  apply TensorProduct.ext
  ext left right
  change pureMode (A + C) B (-power - 1) left right =
    pureMode A B (-power - 1) left right + pureMode C B (-power - 1) left right
  simp only [pureMode, diagonal, map_add, Pi.add_apply, LinearMap.add_apply,
    TensorProduct.add_tmul]
  exact finsum_add_distrib (diagonal_finite A B _ left right)
    (diagonal_finite C B _ left right)

theorem field_add_right (A : VertexOperator ℂ U) (B D : VertexOperator ℂ V) :
    field A (B + D) = field A B + field A D := by
  apply HVertexOperator.coeff_inj
  funext power
  simp only [map_add, Pi.add_apply, VertexOperator.coeff_eq_ncoeff, field_mode]
  apply TensorProduct.ext
  ext left right
  change pureMode A (B + D) (-power - 1) left right =
    pureMode A B (-power - 1) left right + pureMode A D (-power - 1) left right
  simp only [pureMode, diagonal, map_add, Pi.add_apply, LinearMap.add_apply,
    TensorProduct.tmul_add]
  exact finsum_add_distrib (diagonal_finite A B _ left right)
    (diagonal_finite A D _ left right)

theorem field_smul_left (scalar : ℂ) (A : VertexOperator ℂ U)
    (B : VertexOperator ℂ V) : field (scalar • A) B = scalar • field A B := by
  apply HVertexOperator.coeff_inj
  funext power
  simp only [map_smul, Pi.smul_apply, VertexOperator.coeff_eq_ncoeff, field_mode]
  apply TensorProduct.ext
  ext left right
  change pureMode (scalar • A) B (-power - 1) left right =
    scalar • pureMode A B (-power - 1) left right
  simp only [pureMode, diagonal, map_smul, Pi.smul_apply, LinearMap.smul_apply]
  exact (smul_finsum' scalar (diagonal_finite A B _ left right)).symm

theorem field_smul_right (scalar : ℂ) (A : VertexOperator ℂ U)
    (B : VertexOperator ℂ V) : field A (scalar • B) = scalar • field A B := by
  apply HVertexOperator.coeff_inj
  funext power
  simp only [map_smul, Pi.smul_apply, VertexOperator.coeff_eq_ncoeff, field_mode]
  apply TensorProduct.ext
  ext left right
  change pureMode A (scalar • B) (-power - 1) left right =
    scalar • pureMode A B (-power - 1) left right
  simp only [pureMode, diagonal, map_smul, Pi.smul_apply, LinearMap.smul_apply,
    TensorProduct.tmul_smul]
  exact (smul_finsum' scalar (diagonal_finite A B _ left right)).symm

def fieldBilinear : VertexOperator ℂ U →ₗ[ℂ] VertexOperator ℂ V →ₗ[ℂ]
    VertexOperator ℂ (U ⊗[ℂ] V) where
  toFun A := {
    toFun := field A
    map_add' := field_add_right A
    map_smul' := fun scalar B => field_smul_right scalar A B }
  map_add' A C := by
    apply LinearMap.ext
    intro B
    exact field_add_left A C B
  map_smul' scalar A := by
    apply LinearMap.ext
    intro B
    exact field_smul_left scalar A B

def identityField (W : Type*) [AddCommGroup W] [Module ℂ W] : VertexOperator ℂ W :=
  VertexOperator.of_coeff (fun power => if power = 0 then LinearMap.id else 0) (by
    intro vector
    refine ⟨0, ?_⟩
    intro power member
    by_contra below
    have nonzero : power ≠ 0 := by omega
    exact member (by simp [nonzero]))

theorem identityField_mode (index : ℤ) :
    (identityField U)[[index]] = if index = -1 then LinearMap.id else 0 := by
  change (if (-index - 1 : ℤ) = 0 then LinearMap.id else 0) =
    if index = -1 then LinearMap.id else 0
  have equivalent : (-index - 1 : ℤ) = 0 ↔ index = -1 := by omega
  simp only [equivalent]

theorem field_identity_left (B : VertexOperator ℂ V) (index : ℤ) :
    (field (identityField U) B)[[index]] = TensorProduct.map LinearMap.id (B[[index]]) := by
  rw [field_mode]
  apply TensorProduct.ext
  ext left right
  change (∑ᶠ first : ℤ, ((identityField U)[[first]]) left ⊗ₜ[ℂ]
    (B[[index - 1 - first]]) right) = left ⊗ₜ[ℂ] (B[[index]]) right
  rw [finsum_eq_single _ (-1)]
  · simp [identityField_mode]
  · intro first unequal
    simp [identityField_mode, unequal]

theorem field_identity_right (A : VertexOperator ℂ U) (index : ℤ) :
    (field A (identityField V))[[index]] = TensorProduct.map (A[[index]]) LinearMap.id := by
  rw [field_mode]
  apply TensorProduct.ext
  ext left right
  change (∑ᶠ first : ℤ, (A[[first]]) left ⊗ₜ[ℂ]
    ((identityField V)[[index - 1 - first]]) right) = (A[[index]]) left ⊗ₜ[ℂ] right
  rw [finsum_eq_single _ index]
  · simp [identityField_mode]
  · intro first unequal
    have shifted : index - 1 - first ≠ -1 := by omega
    simp [identityField_mode, shifted]

def derivative (A : VertexOperator ℂ U) : VertexOperator ℂ U :=
  VertexOperator.of_coeff (fun power => ((power + 1 : ℤ) : ℂ) • A[[-power - 2]]) (by
    intro vector
    refine ⟨-upper A vector - 2, ?_⟩
    intro power member
    by_contra below
    have vanished := mode_zero_above A vector (-power - 2) (by omega)
    exact member (by simp [vanished]))

theorem derivative_mode (A : VertexOperator ℂ U) (index : ℤ) :
    (derivative A)[[index]] = -(index : ℂ) • A[[index - 1]] := by
  simp only [derivative, VertexOperator.ncoeff_of_coeff]
  have coefficient : (-index - 1 + 1 : ℤ) = -index := by omega
  have shifted : -(-index - 1) - 2 = index - 1 := by omega
  simp only [coefficient, shifted, Int.cast_neg]

theorem derivative_leibniz (A : VertexOperator ℂ U) (B : VertexOperator ℂ V) :
    derivative (field A B) = field (derivative A) B + field A (derivative B) := by
  apply HVertexOperator.coeff_inj
  funext power
  simp only [map_add, Pi.add_apply, VertexOperator.coeff_eq_ncoeff, derivative_mode, field_mode]
  apply TensorProduct.ext
  ext left right
  let index : ℤ := -power - 1
  let base := diagonal A B (index - 1) left right
  have baseFinite : Function.HasFiniteSupport base := diagonal_finite A B _ left right
  have firstFinite : Function.HasFiniteSupport (fun first : ℤ =>
      -((first + 1 : ℤ) : ℂ) • base first) :=
    baseFinite.smul_right (fun first => -((first + 1 : ℤ) : ℂ))
  have secondFinite : Function.HasFiniteSupport (fun first : ℤ =>
      -((index - 1 - first : ℤ) : ℂ) • base first) :=
    baseFinite.smul_right (fun first => -((index - 1 - first : ℤ) : ℂ))
  have reindex : pureMode (derivative A) B index left right =
      ∑ᶠ first : ℤ, -((first + 1 : ℤ) : ℂ) • base first := by
    apply finsum_eq_of_bijective (fun first : ℤ => first - 1)
      (by constructor
          · intro first second equal; dsimp at equal; omega
          · intro first; refine ⟨first + 1, ?_⟩; dsimp; omega)
    intro first
    simp only [diagonal, derivative_mode, LinearMap.smul_apply]
    dsimp [base, diagonal]
    have firstShift : first - 1 + 1 = first := by omega
    have secondShift : index - 1 - 1 - (first - 1) = index - 1 - first := by omega
    rw [firstShift, secondShift]
    rfl
  have secondLaw : pureMode A (derivative B) index left right =
      ∑ᶠ first : ℤ, -((index - 1 - first : ℤ) : ℂ) • base first := by
    apply finsum_congr
    intro first
    simp only [diagonal, derivative_mode, LinearMap.smul_apply, TensorProduct.tmul_smul]
    dsimp [base, diagonal]
    have secondShift : index - 1 - first - 1 = index - 1 - 1 - first := by omega
    rw [secondShift]
  change -(index : ℂ) • pureMode A B (index - 1) left right =
    pureMode (derivative A) B index left right + pureMode A (derivative B) index left right
  rw [reindex, secondLaw, ← finsum_add_distrib firstFinite secondFinite]
  change -(index : ℂ) • (∑ᶠ first : ℤ, base first) = _
  rw [smul_finsum' _ baseFinite]
  apply finsum_congr
  intro first
  rw [← add_smul]
  congr 1
  push_cast
  ring

def tensorTranslation (left : Module.End ℂ U) (right : Module.End ℂ V) :
    Module.End ℂ (U ⊗[ℂ] V) :=
  TensorProduct.map left LinearMap.id + TensorProduct.map LinearMap.id right

theorem translation_left (A : VertexOperator ℂ U) (B : VertexOperator ℂ V)
    (translation : Module.End ℂ U)
    (covariance : ∀ index : ℤ, translation * A[[index]] - A[[index]] * translation =
      -(index : ℂ) • A[[index - 1]]) (index : ℤ) :
    TensorProduct.map translation (LinearMap.id : Module.End ℂ V) * (field A B)[[index]] -
      (field A B)[[index]] * TensorProduct.map translation LinearMap.id =
      (field (derivative A) B)[[index]] := by
  have embedded (first : ℤ) :
      TensorProduct.map translation (LinearMap.id : Module.End ℂ V) *
          (field A (identityField V))[[first]] -
        (field A (identityField V))[[first]] * TensorProduct.map translation LinearMap.id =
          (field (derivative A) (identityField V))[[first]] := by
    rw [field_identity_right, field_identity_right]
    apply TensorProduct.ext
    ext left right
    change translation ((A[[first]]) left) ⊗ₜ[ℂ] right -
      (A[[first]]) (translation left) ⊗ₜ[ℂ] right =
        ((derivative A)[[first]]) left ⊗ₜ[ℂ] right
    rw [← TensorProduct.sub_tmul]
    have relation := congrArg (fun value : Module.End ℂ U => value left) (covariance first)
    have pointwise : translation ((A[[first]]) left) - (A[[first]]) (translation left) =
        ((derivative A)[[first]]) left := by
      simpa only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply,
        derivative_mode] using relation
    rw [pointwise]
  simp only [field_mode]
  apply TensorProduct.ext
  ext left right
  let lifted : Module.End ℂ (U ⊗[ℂ] V) := TensorProduct.map translation LinearMap.id
  have finite := diagonal_finite A B index left right
  have mappedFinite : Function.HasFiniteSupport (fun first : ℤ =>
      lifted (diagonal A B index left right first)) := finite.fun_comp (map_zero lifted)
  have inputFinite := diagonal_finite A B index (translation left) right
  have move : lifted (∑ᶠ first : ℤ, diagonal A B index left right first) =
      ∑ᶠ first : ℤ, lifted (diagonal A B index left right first) :=
    lifted.toAddMonoidHom.map_finsum finite
  change lifted (pureMode A B index left right) -
    pureMode A B index (translation left) right = pureMode (derivative A) B index left right
  simp only [pureMode]
  rw [move, ← finsum_sub_distrib mappedFinite inputFinite]
  apply finsum_congr
  intro first
  have relation := congrArg (fun value : Module.End ℂ (U ⊗[ℂ] V) =>
    value (left ⊗ₜ[ℂ] (B[[index - 1 - first]]) right)) (embedded first)
  simpa only [diagonal, lifted, field_identity_right, Module.End.mul_apply,
    LinearMap.sub_apply, TensorProduct.map_tmul, LinearMap.id_apply] using relation

theorem translation_right (A : VertexOperator ℂ U) (B : VertexOperator ℂ V)
    (translation : Module.End ℂ V)
    (covariance : ∀ index : ℤ, translation * B[[index]] - B[[index]] * translation =
      -(index : ℂ) • B[[index - 1]]) (index : ℤ) :
    TensorProduct.map (LinearMap.id : Module.End ℂ U) translation * (field A B)[[index]] -
      (field A B)[[index]] * TensorProduct.map LinearMap.id translation =
      (field A (derivative B))[[index]] := by
  have embedded (second : ℤ) :
      TensorProduct.map (LinearMap.id : Module.End ℂ U) translation *
          (field (identityField U) B)[[second]] -
        (field (identityField U) B)[[second]] * TensorProduct.map LinearMap.id translation =
          (field (identityField U) (derivative B))[[second]] := by
    rw [field_identity_left, field_identity_left]
    apply TensorProduct.ext
    ext left right
    change left ⊗ₜ[ℂ] translation ((B[[second]]) right) -
      left ⊗ₜ[ℂ] (B[[second]]) (translation right) =
        left ⊗ₜ[ℂ] ((derivative B)[[second]]) right
    rw [← TensorProduct.tmul_sub]
    have relation := congrArg (fun value : Module.End ℂ V => value right) (covariance second)
    have pointwise : translation ((B[[second]]) right) - (B[[second]]) (translation right) =
        ((derivative B)[[second]]) right := by
      simpa only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply,
        derivative_mode] using relation
    rw [pointwise]
  simp only [field_mode]
  apply TensorProduct.ext
  ext left right
  let lifted : Module.End ℂ (U ⊗[ℂ] V) := TensorProduct.map LinearMap.id translation
  have finite := diagonal_finite A B index left right
  have mappedFinite : Function.HasFiniteSupport (fun first : ℤ =>
      lifted (diagonal A B index left right first)) := finite.fun_comp (map_zero lifted)
  have inputFinite := diagonal_finite A B index left (translation right)
  have move : lifted (∑ᶠ first : ℤ, diagonal A B index left right first) =
      ∑ᶠ first : ℤ, lifted (diagonal A B index left right first) :=
    lifted.toAddMonoidHom.map_finsum finite
  change lifted (pureMode A B index left right) -
    pureMode A B index left (translation right) = pureMode A (derivative B) index left right
  simp only [pureMode]
  rw [move, ← finsum_sub_distrib mappedFinite inputFinite]
  apply finsum_congr
  intro first
  have relation := congrArg (fun value : Module.End ℂ (U ⊗[ℂ] V) =>
    value ((A[[first]]) left ⊗ₜ[ℂ] right)) (embedded (index - 1 - first))
  simpa only [diagonal, lifted, field_identity_left, Module.End.mul_apply,
    LinearMap.sub_apply, TensorProduct.map_tmul, LinearMap.id_apply] using relation

theorem translation_covariant (A : VertexOperator ℂ U) (B : VertexOperator ℂ V)
    (leftTranslation : Module.End ℂ U) (rightTranslation : Module.End ℂ V)
    (leftCovariance : ∀ index : ℤ,
      leftTranslation * A[[index]] - A[[index]] * leftTranslation =
        -(index : ℂ) • A[[index - 1]])
    (rightCovariance : ∀ index : ℤ,
      rightTranslation * B[[index]] - B[[index]] * rightTranslation =
        -(index : ℂ) • B[[index - 1]]) (index : ℤ) :
    tensorTranslation leftTranslation rightTranslation * (field A B)[[index]] -
      (field A B)[[index]] * tensorTranslation leftTranslation rightTranslation =
        -(index : ℂ) • (field A B)[[index - 1]] := by
  have leibniz := congrArg (fun value => value[[index]]) (derivative_leibniz A B)
  simp only [derivative_mode, map_add, Pi.add_apply] at leibniz
  unfold tensorTranslation
  rw [add_mul, mul_add]
  calc
    _ = (TensorProduct.map leftTranslation LinearMap.id * (field A B)[[index]] -
        (field A B)[[index]] * TensorProduct.map leftTranslation LinearMap.id) +
        (TensorProduct.map LinearMap.id rightTranslation * (field A B)[[index]] -
        (field A B)[[index]] * TensorProduct.map LinearMap.id rightTranslation) := by abel
    _ = (field (derivative A) B)[[index]] + (field A (derivative B))[[index]] := by
      rw [translation_left A B leftTranslation leftCovariance,
        translation_right A B rightTranslation rightCovariance]
    _ = _ := leibniz.symm

end D5.S3.VertexAlgebra.VertexOperatorTensorProduct
