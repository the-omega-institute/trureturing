/- GID: D5/S3/Geometry/Orthogonality/SpinCovers/SU4SO6Surjectivity
   generality: G
   mirror-B: none(waiver:existing-library-proof-without-a-dedicated-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Surjectivity of the exterior-square homomorphism follows by lifting pairs of reflections to products of unitary skew forms. -/

import OmegaBuild.Commands
import D5.S3.Geometry.Orthogonality.SpinCovers.SU4SO6Cover
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Tactic.LinearCombination

/-! Omega original.

Surjectivity of the exterior-square homomorphism follows by lifting pairs of
reflections to products of unitary skew forms. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix
open scoped ComplexConjugate Matrix InnerProductSpace
open Submodule

namespace OmegaMath.SU4SO6Cover

private abbrev E := EuclideanSpace ℝ (Fin 6)
private abbrev SO6 := Matrix.specialOrthogonalGroup (Fin 6) ℝ

local notation "form" => unnormalizedSelfDualMatrix

private theorem form_skew (x : Fin 6 → ℝ) : (form x)ᵀ = -form x := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [unnormalizedSelfDualMatrix, skewMatrix]

private theorem form_add_mul (x y : Fin 6 → ℝ) :
    form x * (form y)ᴴ + form y * (form x)ᴴ =
      (2 * (↑(x ⬝ᵥ y) : ℂ)) • (1 : C4) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [unnormalizedSelfDualMatrix, skewMatrix, Matrix.add_apply, Matrix.vecMul,
      Fin.sum_univ_succ, dotProduct] <;> ring_nf <;> simp [Complex.I_sq] <;> ring

private theorem form_det (x : Fin 6 → ℝ) :
    (form x).det = (↑(x ⬝ᵥ x) : ℂ) ^ 2 := by
  rw [det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, det_fin_three,
    submatrix_apply, Fin.zero_succAbove, Fin.succ_zero_eq_one, Fin.succ_one_eq_two,
    show (2 : Fin 3).succ = (3 : Fin 4) from rfl,
    show (1 : Fin 4).succAbove (2 : Fin 3) = 3 from rfl,
    show (2 : Fin 4).succAbove (1 : Fin 3) = 1 from rfl,
    show (2 : Fin 4).succAbove (2 : Fin 3) = 3 from rfl,
    show (3 : Fin 4).succAbove (1 : Fin 3) = 1 from rfl,
    show (3 : Fin 4).succAbove (2 : Fin 3) = 2 from rfl]
  norm_num [unnormalizedSelfDualMatrix, skewMatrix, dotProduct, Fin.sum_univ_succ]
  ring_nf
  simp [Complex.I_sq]
  ring_nf

private def unitSkew (x : Fin 6 → ℝ) (hx : x ⬝ᵥ x = 1) : SU4 :=
  ⟨form x, Matrix.mem_specialUnitaryGroup_iff.mpr <|
    ⟨Matrix.mem_unitaryGroup_iff.mpr (by
      have h := form_add_mul x x
      rw [hx] at h
      simp only [Complex.ofReal_one, mul_one, ← two_smul ℂ] at h
      exact smul_right_injective C4 (by norm_num : (2 : ℂ) ≠ 0) h),
     by simp [form_det, hx]⟩⟩

private def conjCoords (x : Fin 6 → ℝ) : Fin 6 → ℝ :=
  ![x 0, x 1, x 2, -x 3, -x 4, -x 5]

private theorem form_conj (x : Fin 6 → ℝ) : (form x).map conj = form (conjCoords x) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [unnormalizedSelfDualMatrix, skewMatrix, conjCoords] <;> ring

private theorem form_sub (a : ℝ) (x y : Fin 6 → ℝ) :
    form (a • x - y) = (a : ℂ) • form x - form y := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [unnormalizedSelfDualMatrix, skewMatrix, Pi.smul_apply, smul_eq_mul] <;> ring

private theorem asLinear_mul (A B : R6) :
    (A * B).toEuclideanLin = A.toEuclideanLin ∘ₗ B.toEuclideanLin := by
  let b := (EuclideanSpace.basisFun (Fin 6) ℝ).toBasis
  exact Matrix.toLin_mul b b b A B

private theorem asLinear_one : (1 : R6).toEuclideanLin = LinearMap.id :=
  Matrix.toLin_one (EuclideanSpace.basisFun (Fin 6) ℝ).toBasis

private def asIsometry (A : SO6) : E ≃ₗᵢ[ℝ] E :=
  LinearIsometryEquiv.ofLinearIsometry
    ⟨(A : R6).toEuclideanLin, by
      have h := (Matrix.mem_orthogonalGroup_iff' (Fin 6) ℝ).mp
        (Matrix.mem_specialOrthogonalGroup_iff.mp A.prop).1
      intro x
      apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
      have hadj := Matrix.toEuclideanLin_conjTranspose_eq_adjoint (A : R6)
      have hlin :
          (A : R6).toEuclideanLin.adjoint ∘ₗ (A : R6).toEuclideanLin = LinearMap.id := by
        rw [← hadj, ← asLinear_mul]
        change ((A : R6)ᵀ * (A : R6)).toEuclideanLin = _
        rw [h, asLinear_one]
      rw [← @real_inner_self_eq_norm_sq E, ← @real_inner_self_eq_norm_sq E,
        ← LinearMap.adjoint_inner_left, ← LinearMap.comp_apply, hlin, LinearMap.id_apply]⟩
    (↑(A⁻¹) : R6).toEuclideanLin
    (by rw [← asLinear_mul, ← Submonoid.coe_mul, mul_inv_cancel,
      Submonoid.coe_one, asLinear_one])
    (by rw [← asLinear_mul, ← Submonoid.coe_mul, inv_mul_cancel,
      Submonoid.coe_one, asLinear_one])

private theorem asIsometry_toLinear (A : SO6) :
    (asIsometry A).toLinearMap = (A : R6).toEuclideanLin := rfl

private def lift : SU4 →* (E ≃ₗᵢ[ℝ] E) where
  toFun U := asIsometry (so6Cover U)
  map_one' := by
    apply LinearIsometryEquiv.ext
    intro x
    change (asIsometry (so6Cover 1)).toLinearMap x = x
    rw [map_one, asIsometry_toLinear, Submonoid.coe_one, asLinear_one, LinearMap.id_apply]
  map_mul' U V := by
    apply LinearIsometryEquiv.ext
    intro x
    change (asIsometry (so6Cover (U * V))).toLinearMap x =
      ((asIsometry (so6Cover U)).toLinearMap ∘ₗ (asIsometry (so6Cover V)).toLinearMap) x
    rw [map_mul, asIsometry_toLinear, Submonoid.coe_mul, asLinear_mul,
      asIsometry_toLinear, asIsometry_toLinear]

private theorem lift_apply (U : SU4) (x : E) (i : Fin 6) :
    (lift U x) i = (so6OfSU4 U *ᵥ (fun k => x k)) i := rfl

private theorem dot_self (x : E) : (fun i => x i) ⬝ᵥ (fun i => x i) = ‖x‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [pow_two, dotProduct]

private def conjVec (x : E) : E := WithLp.toLp 2 (conjCoords (fun i => x i))

private theorem conjVec_apply (x : E) (i : Fin 6) :
    conjVec x i = conjCoords (fun k => x k) i := rfl

private def reflect (x : E) : E ≃ₗᵢ[ℝ] E := ((ℝ ∙ x)ᗮ : Submodule ℝ E).reflection

private theorem reflect_mul_self (x : E) : reflect x * reflect x = 1 :=
  (ℝ ∙ x)ᗮ.reflection_mul_reflection

private theorem form_injective : Function.Injective form := by
  intro x y h
  rw [unnormalizedSelfDualMatrix_eq, unnormalizedSelfDualMatrix_eq] at h
  apply selfDualChart_injective
  exact smul_right_injective C4 (by
    exact_mod_cast (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)).ne') h

private theorem form_action (U : SU4) (y : Fin 6 → ℝ) :
    (U : C4) * form y * (U : C4)ᵀ = form (so6OfSU4 U *ᵥ y) := by
  rw [unnormalizedSelfDualMatrix_eq, unnormalizedSelfDualMatrix_eq,
    mul_smul_comm, smul_mul_assoc, so6OfSU4_action]

private theorem unitSkew_action (x y : Fin 6 → ℝ) (hx : x ⬝ᵥ x = 1) :
    so6OfSU4 (unitSkew x hx) *ᵥ conjCoords y = (2 * (x ⬝ᵥ y)) • x - y := by
  have hAdj : (form y)ᴴ = -(form y).map conj := by
    ext i j
    have h := congrArg (fun M : C4 => M i j) (form_skew y)
    change form y j i = -form y i j at h
    simpa only [conjTranspose_apply, Complex.star_def, Matrix.neg_apply, Matrix.map_apply,
      map_neg] using congrArg (conj : ℂ → ℂ) h
  have hUnit : (form x)ᴴ * form x = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp (Matrix.mem_specialUnitaryGroup_iff.mp (unitSkew x hx).prop).1
  have h := congrArg (fun M : C4 => M * form x) (form_add_mul x y)
  rw [Matrix.add_mul, Matrix.mul_assoc (form y), hUnit, Matrix.mul_one, smul_mul_assoc,
    Matrix.one_mul] at h
  apply form_injective
  rw [← form_action, ← form_conj, form_sub]
  change form x * (form y).map conj * (form x)ᵀ =
    ((↑(2 * (x ⬝ᵥ y)) : ℂ)) • form x - form y
  simp only [form_skew, ← neg_eq_iff_eq_neg.mpr hAdj, Matrix.mul_neg, Matrix.neg_mul, neg_neg]
  push_cast
  exact eq_sub_of_add_eq h

private theorem lift_reflect_unit (x y : E) (hx : ‖x‖ = 1) :
    lift (unitSkew (fun i => x i) (by rw [dot_self, hx, one_pow])) (conjVec y) = -reflect x y := by
  have hn : (fun i => x i) ⬝ᵥ (fun i => x i) = 1 := by rw [dot_self, hx, one_pow]
  have hxy : (fun i => x i) ⬝ᵥ (fun i => y i) = inner ℝ x y := by
    simp [PiLp.inner_apply, dotProduct, mul_comm]
  have h := unitSkew_action (fun i => x i) (fun i => y i) hn
  have hInner : inner ℝ x y / ‖x‖ ^ 2 = inner ℝ x y := by rw [hx, one_pow, div_one]
  rw [reflect, Submodule.reflection_orthogonal_apply, neg_neg, Submodule.reflection_singleton_apply,
    RCLike.ofReal_real_eq_id]
  simp only [id, hInner]
  ext i
  rw [lift_apply]
  simpa only [conjVec_apply, hxy, Pi.sub_apply, Pi.smul_apply, PiLp.sub_apply,
    PiLp.smul_apply, two_nsmul, two_mul, add_smul, Pi.add_apply, PiLp.add_apply] using congrFun h i

private theorem pair_in_range (x y : E) (hx : x ≠ 0) (hy : y ≠ 0) :
    reflect x * reflect y ∈ lift.range := by
  let u := ‖x‖⁻¹ • x
  let v := ‖y‖⁻¹ • y
  have hu : ‖u‖ = 1 := by
    simp [u, norm_smul, norm_ne_zero_iff.mpr hx]
  have hv : ‖v‖ = 1 := by
    simp [v, norm_smul, norm_ne_zero_iff.mpr hy]
  have hxu : reflect u = reflect x := by
    exact congrArg (fun K : Submodule ℝ E => Kᗮ.reflection)
      (Submodule.span_singleton_smul_eq (inv_ne_zero (norm_ne_zero_iff.mpr hx)).isUnit x)
  have hyv : reflect v = reflect y := by
    exact congrArg (fun K : Submodule ℝ E => Kᗮ.reflection)
      (Submodule.span_singleton_smul_eq (inv_ne_zero (norm_ne_zero_iff.mpr hy)).isUnit y)
  let U := unitSkew (fun i => u i) (by rw [dot_self, hu, one_pow])
  let V := unitSkew (fun i => v i) (by rw [dot_self, hv, one_pow])
  use U * V⁻¹
  change lift (U * V⁻¹) = _
  rw [map_mul, map_inv]
  apply LinearIsometryEquiv.ext
  intro z
  have hV : (lift V)⁻¹ z = conjVec (-reflect y z) := by
    apply (lift V).injective
    have h := lift_reflect_unit v (-reflect y z) hv
    change lift V (conjVec (-reflect y z)) = _ at h
    rw [hyv, map_neg, neg_neg] at h
    rw [h]
    change (lift V * (lift V)⁻¹) z = (reflect y * reflect y) z
    rw [mul_inv_cancel, reflect_mul_self]
  change lift U ((lift V)⁻¹ z) = reflect x (reflect y z)
  rw [hV]
  have h := lift_reflect_unit u (-reflect y z) hu
  change lift U (conjVec (-reflect y z)) = _ at h
  rw [h, hxu, map_neg, neg_neg]

private theorem nonzero_reflections (l : List E) :
    ∃ l' : List E, (∀ x ∈ l', x ≠ 0) ∧ (l'.map reflect).prod = (l.map reflect).prod := by
  induction l with
  | nil => exact ⟨[], by simp, rfl⟩
  | cons x xs ih =>
    obtain ⟨l', hl', hp⟩ := ih
    by_cases hx : x = 0
    · subst x
      have hz : reflect 0 = 1 := by
        apply LinearIsometryEquiv.ext
        intro z
        change (ℝ ∙ (0 : E))ᗮ.reflection z = z
        apply Submodule.reflection_mem_subspace_eq_self
        simp
      exact ⟨l', hl', by simpa [hz] using hp⟩
    · refine ⟨x :: l', ?_, by simp [hp]⟩
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hx
      · exact hl' y hy

private def linearEnd : (E ≃ₗᵢ[ℝ] E) →* Module.End ℝ E where
  toFun f := f.toLinearMap
  map_one' := rfl
  map_mul' _ _ := rfl

private theorem reflection_det (x : E) (hx : x ≠ 0) :
    LinearMap.det (linearEnd (reflect x)) = -1 := by
  change LinearMap.det ((ℝ ∙ x)ᗮ : Submodule ℝ E).reflection.toLinearMap = _
  rw [Submodule.det_reflection, Submodule.orthogonal_orthogonal, finrank_span_singleton hx, pow_one]

private theorem reflections_det (l : List E) (hl : ∀ x ∈ l, x ≠ 0) :
    LinearMap.det (linearEnd ((l.map reflect).prod)) = (-1) ^ l.length := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    have hx : x ≠ 0 := hl _ (List.mem_cons_self ..)
    have ht : ∀ y ∈ xs, y ≠ 0 := fun y hy => hl y (List.mem_cons_of_mem x hy)
    simp only [List.map_cons, List.prod_cons, map_mul, List.length_cons, pow_succ]
    rw [reflection_det x hx, ih ht, mul_comm]

private theorem reflections_in_range (l : List E) :
    (∀ x ∈ l, x ≠ 0) → Even l.length → (l.map reflect).prod ∈ lift.range := by
  induction l using List.twoStepInduction with
  | nil => simp
  | singleton x => simp
  | cons_cons x y zs ih _ =>
    intro hn he
    have hx : x ≠ 0 := hn x (by simp)
    have hy : y ≠ 0 := hn y (by simp)
    have ht : ∀ z ∈ zs, z ≠ 0 := fun z hz => hn z (by simp [hz])
    have hEven : Even zs.length := by simpa [Nat.even_add] using he
    simpa [mul_assoc] using
      lift.range.mul_mem (pair_in_range x y hx hy) (ih ht hEven)

/-- Every special orthogonal transformation of the six real Hodge coordinates
has a determinant-one unitary lift. -/
theorem so6Cover_surjective : Function.Surjective so6Cover := by
  intro A
  obtain ⟨l, _, hl⟩ := (asIsometry A).reflections_generate_dim
  obtain ⟨l', hn, he⟩ := nonzero_reflections l
  change asIsometry A = (l.map reflect).prod at hl
  have heq : asIsometry A = (l'.map reflect).prod := hl.trans he.symm
  have hd : LinearMap.det (linearEnd (asIsometry A)) = 1 := by
    change LinearMap.det (A : R6).toEuclideanLin = _
    rw [Matrix.toEuclideanLin_eq_toLin_orthonormal, LinearMap.det_toLin]
    exact (Matrix.mem_specialOrthogonalGroup_iff.mp A.prop).2
  rw [heq, reflections_det l' hn] at hd
  have hEven := (neg_one_pow_eq_one_iff_even (by norm_num : (-1 : ℝ) ≠ 1)).mp hd
  obtain ⟨U, hU⟩ := reflections_in_range l' hn hEven
  refine ⟨U, Subtype.ext ?_⟩
  apply Matrix.toEuclideanLin.injective
  exact congrArg (fun f : E ≃ₗᵢ[ℝ] E => f.toLinearMap) (hU.trans heq.symm)

end OmegaMath.SU4SO6Cover
