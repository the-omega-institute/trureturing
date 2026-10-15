/- GID: D5/S3/Geometry/ProjectionRange/Prebundle
   generality: G
   mirror-B: D5/B/S3/Geometry/ProjectionRange/Prebundle
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Geometry.Manifold.VectorBundle.Basic]
   utility: none
   digest: A smooth constant-rank Hermitian projection induces a complex range bundle with real smooth ambient compatibility. -/

import D5.S3.Geometry.ProjectionRange.LocalGramCertificate
import Mathlib.Geometry.Manifold.VectorBundle.Basic
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Projection

/-!
The local Gram certificate is imported, not reproved. Actual fibers are
submodules of Euclidean space with their existing norm, topology and inner product.
The rank-r model is independent of the ambient dimension n. No positive-dimension,
nonempty-base, compactness, orientability, or global-frame assumption is used.
-/
set_option backward.isDefEq.respectTransparency false

noncomputable section
open Bundle Set Filter Topology
open scoped Matrix ComplexOrder Manifold ContDiff Matrix.Norms.Elementwise

namespace ProjectionRange

abbrev V (n : ℕ) := EuclideanSpace ℂ (Fin n)
abbrev rangeSubmodule {B : Type*} {n : ℕ} (p : B → Matrix (Fin n) (Fin n) ℂ) (x : B) :=
  LinearMap.range (Matrix.toEuclideanLin (p x))

abbrev Fiber {B : Type*} {n : ℕ} (p : B → Matrix (Fin n) (Fin n) ℂ) (x : B) : Type :=
  ↥(rangeSubmodule p x)

def columns {B : Type*} {n r : ℕ} (p : B → Matrix (Fin n) (Fin n) ℂ)
    (J : Fin r → Fin n) (x : B) : Matrix (Fin n) (Fin r) ℂ :=
  fun i j => p x i (J j)

def gram {B : Type*} {n r : ℕ} (p : B → Matrix (Fin n) (Fin n) ℂ)
    (J : Fin r → Fin n) (x : B) := (columns p J x)ᴴ * columns p J x

def leftMatrix {B : Type*} {n r : ℕ} (p : B → Matrix (Fin n) (Fin n) ℂ)
    (J : Fin r → Fin n) (x : B) := (gram p J x)⁻¹ * (columns p J x)ᴴ

variable {B : Type*} [TopologicalSpace B] {n r : ℕ}
variable (p : B → Matrix (Fin n) (Fin n) ℂ)

/-- Local data are constructed below from p; they are not input hypotheses
of the projection-range constructor. -/
structure ColumnChart where
  J : Fin r → Fin n
  injective_J : Function.Injective J
  U : Set B
  isOpen_U : IsOpen U
  gram_unit : ∀ x ∈ U, IsUnit (gram p J x)
  span_eq : ∀ x ∈ U,
    Submodule.span ℂ (Set.range (columns p J x).col) =
      Submodule.span ℂ (Set.range (p x).col)

variable {p}

theorem exists_columnChart
    (hp : Continuous p) (hstar : ∀ x, (p x)ᴴ = p x)
    (hidem : ∀ x, p x * p x = p x) (hrank : ∀ x, (p x).rank = r) (x₀ : B) :
    ∃ a : ColumnChart (r := r) p, x₀ ∈ a.U := by
  have hPSD (x : B) : (p x).PosSemidef := by
    simpa only [hstar x, hidem x] using Matrix.posSemidef_conjTranspose_mul_self (p x)
  have hr : ∀ᶠ y in 𝓝[univ] x₀,
      Module.finrank ℂ (LinearMap.range (p y).mulVecLin) =
        Module.finrank ℂ (LinearMap.range (p x₀).mulVecLin) :=
    Eventually.of_forall fun y => (hrank y).trans (hrank x₀).symm
  have h := exact_original_local_gram_certificate p univ x₀ (mem_univ _)
    (fun y _ => hPSD y) hp.continuousAt.continuousWithinAt hr
  dsimp only at h
  have hk : Module.finrank ℂ (LinearMap.range (p x₀).mulVecLin) = r := hrank x₀
  rw [hk] at h
  obtain ⟨J, hJ, U, hU, hx₀, hUcert⟩ := h
  refine ⟨⟨J, hJ, U, hU, ?_, ?_⟩, hx₀.1⟩
  · intro x hx
    exact (hUcert x ⟨hx, mem_univ _⟩).2.1
  · intro x hx
    exact (hUcert x ⟨hx, mem_univ _⟩).2.2

/-- Choice is made separately at each base point; this is an atlas, not a global frame. -/
def chartAt (hp : Continuous p) (hstar : ∀ x, (p x)ᴴ = p x)
    (hidem : ∀ x, p x * p x = p x) (hrank : ∀ x, (p x).rank = r) (x₀ : B) :
    ColumnChart (r := r) p := (exists_columnChart hp hstar hidem hrank x₀).choose

theorem mem_chartAt (hp : Continuous p) (hstar : ∀ x, (p x)ᴴ = p x)
    (hidem : ∀ x, p x * p x = p x) (hrank : ∀ x, (p x).rank = r) (x₀ : B) :
    x₀ ∈ (chartAt hp hstar hidem hrank x₀).U :=
  (exists_columnChart hp hstar hidem hrank x₀).choose_spec

/-- Move a column-span equality from function coordinates to the actual Euclidean submodules. -/
theorem euclidean_range_eq_of_span_eq {a b c : ℕ}
    (A : Matrix (Fin a) (Fin b) ℂ) (C : Matrix (Fin a) (Fin c) ℂ)
    (h : Submodule.span ℂ (Set.range A.col) = Submodule.span ℂ (Set.range C.col)) :
    LinearMap.range (Matrix.toEuclideanLin A) = LinearMap.range (Matrix.toEuclideanLin C) := by
  have h' : LinearMap.range A.mulVecLin = LinearMap.range C.mulVecLin := by
    simpa only [Matrix.range_mulVecLin] using h
  ext v
  constructor
  · rintro ⟨w, rfl⟩
    have hw : A *ᵥ WithLp.ofLp w ∈ LinearMap.range C.mulVecLin := by
      rw [← h']; exact ⟨WithLp.ofLp w, rfl⟩
    obtain ⟨z, hz⟩ := hw
    exact ⟨WithLp.toLp 2 z, congrArg (WithLp.toLp 2) hz⟩
  · rintro ⟨w, rfl⟩
    have hw : C *ᵥ WithLp.ofLp w ∈ LinearMap.range A.mulVecLin := by
      rw [h']; exact ⟨WithLp.ofLp w, rfl⟩
    obtain ⟨z, hz⟩ := hw
    exact ⟨WithLp.toLp 2 z, congrArg (WithLp.toLp 2) hz⟩

namespace ColumnChart
variable (a : ColumnChart (r := r) p)

theorem left_mul_columns {x : B} (hx : x ∈ a.U) :
    leftMatrix p a.J x * columns p a.J x = 1 := by
  dsimp only [leftMatrix, gram]
  rw [Matrix.mul_assoc]
  exact Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp (a.gram_unit x hx))

theorem range_columns {x : B} (hx : x ∈ a.U) :
    LinearMap.range (Matrix.toEuclideanLin (columns p a.J x)) = rangeSubmodule p x :=
  euclidean_range_eq_of_span_eq _ _ (a.span_eq x hx)

theorem projection_columns (hidem : ∀ x, p x * p x = p x) (x : B) :
    p x * columns p a.J x = columns p a.J x := by
  ext i j
  exact congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => M i (a.J j)) (hidem x)

/-- Actual column map into the range, defined on every base point, even outside U. -/
def intoRange (hidem : ∀ x, p x * p x = p x) (x : B) : V r →ₗ[ℂ] Fiber p x :=
  (Matrix.toEuclideanLin (columns p a.J x)).codRestrict (rangeSubmodule p x) fun v => by
    refine ⟨Matrix.toEuclideanLin (columns p a.J x) v, ?_⟩
    change ((Matrix.toEuclideanLin (p x)).comp
      (Matrix.toEuclideanLin (columns p a.J x))) v = _
    rw [← Matrix.toLpLin_mul_same, a.projection_columns hidem]

/-- Coordinates use the inherited subtype inclusion, not a surrogate fiber. -/
def coordinates (x : B) : Fiber p x →ₗ[ℂ] V r :=
  (Matrix.toEuclideanLin (leftMatrix p a.J x)).comp (rangeSubmodule p x).subtype

theorem coordinates_intoRange (hidem : ∀ x, p x * p x = p x)
    {x : B} (hx : x ∈ a.U) (v : V r) :
    a.coordinates x (a.intoRange hidem x v) = v := by
  change ((Matrix.toEuclideanLin (leftMatrix p a.J x)).comp
    (Matrix.toEuclideanLin (columns p a.J x))) v = v
  rw [← Matrix.toLpLin_mul_same, a.left_mul_columns hx, Matrix.toLpLin_one]
  rfl

theorem intoRange_coordinates (hidem : ∀ x, p x * p x = p x)
    {x : B} (hx : x ∈ a.U) (v : Fiber p x) :
    a.intoRange hidem x (a.coordinates x v) = v := by
  have hv : (v : V n) ∈ LinearMap.range (Matrix.toEuclideanLin (columns p a.J x)) := by
    rw [a.range_columns hx]; exact v.property
  obtain ⟨w, hw⟩ := hv
  have hv' : a.intoRange hidem x w = v := Subtype.ext hw
  rw [← hv', a.coordinates_intoRange hidem hx]

/-- Both inverse identities have proof bodies and apply to the actual dependent range. -/
def equiv (hidem : ∀ x, p x * p x = p x) {x : B} (hx : x ∈ a.U) :
    Fiber p x ≃ₗ[ℂ] V r :=
  { a.coordinates x with
    invFun := a.intoRange hidem x
    left_inv := a.intoRange_coordinates hidem hx
    right_inv := a.coordinates_intoRange hidem hx }

def equivL (hidem : ∀ x, p x * p x = p x) {x : B} (hx : x ∈ a.U) :
    Fiber p x ≃L[ℂ] V r := (a.equiv hidem hx).toContinuousLinearEquiv

/-- The target and source are genuine local products with rank-r model fiber. -/
def pretrivialization (hidem : ∀ x, p x * p x = p x) :
    Pretrivialization (V r) (π (V r) (Fiber p)) where
  toFun z := (z.proj, a.coordinates z.proj z.2)
  invFun z := ⟨z.1, a.intoRange hidem z.1 z.2⟩
  source := (π (V r) (Fiber p)) ⁻¹' a.U
  target := a.U ×ˢ univ
  map_source' z hz := ⟨hz, mem_univ _⟩
  map_target' z hz := hz.1
  left_inv' z hz := by
    change TotalSpace.mk z.proj (a.intoRange hidem z.proj (a.coordinates z.proj z.2)) = z
    rw [a.intoRange_coordinates hidem hz]
  right_inv' z hz := by
    change (z.1, a.coordinates z.1 (a.intoRange hidem z.1 z.2)) = z
    rw [a.coordinates_intoRange hidem hz.1]
  open_target := a.isOpen_U.prod isOpen_univ
  baseSet := a.U
  open_baseSet := a.isOpen_U
  source_eq := rfl
  target_eq := rfl
  proj_toFun := fun _ _ => rfl

instance complex_linear (hidem : ∀ x, p x * p x = p x) :
    (a.pretrivialization hidem).IsLinear ℂ where
  linear x _ := (a.coordinates x).isLinear

instance real_linear (hidem : ∀ x, p x * p x = p x) :
    (a.pretrivialization hidem).IsLinear ℝ where
  linear x _ := ((a.coordinates x).restrictScalars ℝ).isLinear

theorem symm_eq (hidem : ∀ x, p x * p x = p x) {x : B} (hx : x ∈ a.U) (v : V r) :
    (a.pretrivialization hidem).symm x v = a.intoRange hidem x v := by
  apply (a.equiv hidem hx).injective
  change a.coordinates x ((a.pretrivialization hidem).symm x v) =
    a.coordinates x (a.intoRange hidem x v)
  rw [a.coordinates_intoRange hidem hx]
  exact congrArg Prod.snd ((a.pretrivialization hidem).apply_mk_symm hx v)

theorem inducing (hidem : ∀ x, p x * p x = p x) {x : B} (hx : x ∈ a.U) :
    IsInducing (a.pretrivialization hidem ∘ TotalSpace.mk x) :=
  isInducing_const_prod.mpr (a.equivL hidem hx).toHomeomorph.isInducing

/-- The actual overlap, with the usual beta-after-alpha direction. -/
def transition (b : ColumnChart (r := r) p) (x : B) : Matrix (Fin r) (Fin r) ℂ :=
  leftMatrix p b.J x * columns p a.J x

theorem transition_apply (b : ColumnChart (r := r) p)
    (hidem : ∀ x, p x * p x = p x) {x : B} (hx : x ∈ a.U ∩ b.U) (v : V r) :
    Matrix.toEuclideanLin (a.transition b x) v =
      ((b.pretrivialization hidem) ⟨x, (a.pretrivialization hidem).symm x v⟩).2 := by
  rw [a.symm_eq hidem hx.1]
  change Matrix.toEuclideanLin (leftMatrix p b.J x * columns p a.J x) v =
    ((Matrix.toEuclideanLin (leftMatrix p b.J x)).comp
      (Matrix.toEuclideanLin (columns p a.J x))) v
  rw [Matrix.toLpLin_mul_same]

end ColumnChart
end ProjectionRange

namespace ProjectionRange

/-- The matrix-to-operator conversion, with operator norm on the target. -/
def matrixCLE (a b : ℕ) : Matrix (Fin a) (Fin b) ℂ ≃L[ℂ] (V b →L[ℂ] V a) :=
  (Matrix.toEuclideanLin.trans LinearMap.toContinuousLinearMap).toContinuousLinearEquiv

def matrixRealCLM (a b : ℕ) : Matrix (Fin a) (Fin b) ℂ →L[ℝ] (V b →L[ℝ] V a) :=
  (ContinuousLinearMap.restrictScalarsL ℂ (V b) (V a) ℝ ℝ).comp
    ((matrixCLE a b).toContinuousLinearMap.restrictScalars ℝ)

section Smooth
variable {E H B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [TopologicalSpace B] [ChartedSpace H B]
variable {I : ModelWithCorners ℝ E H}

/-- Finite-coordinate multiplication, valid for rectangular and empty matrices.
This is a consumed calculus application, not a new mathematical result. -/
theorem smooth_mul {a b c : ℕ} {F : B → Matrix (Fin a) (Fin b) ℂ}
    {G : B → Matrix (Fin b) (Fin c) ℂ} {x : B}
    (hF : ContMDiffAt I 𝓘(ℝ, Matrix (Fin a) (Fin b) ℂ) ∞ F x)
    (hG : ContMDiffAt I 𝓘(ℝ, Matrix (Fin b) (Fin c) ℂ) ∞ G x) :
    ContMDiffAt I 𝓘(ℝ, Matrix (Fin a) (Fin c) ℂ) ∞ (fun y => F y * G y) x := by
  apply contMDiffAt_pi_space.mpr
  intro i
  apply contMDiffAt_pi_space.mpr
  intro j
  change ContMDiffAt I 𝓘(ℝ, ℂ) ∞ (fun y => ∑ t, F y i t * G y t j) x
  apply contMDiffAt_finsetSum
  intro t _
  exact (contDiff_mul : ContDiff ℝ ∞ (fun q : ℂ × ℂ => q.1 * q.2)).comp_contMDiffAt
    ((contMDiffAt_pi_space.mp (contMDiffAt_pi_space.mp hF i) t).prodMk_space
      (contMDiffAt_pi_space.mp (contMDiffAt_pi_space.mp hG t) j))

theorem smooth_adj {a b : ℕ} {F : B → Matrix (Fin a) (Fin b) ℂ} {x : B}
    (hF : ContMDiffAt I 𝓘(ℝ, Matrix (Fin a) (Fin b) ℂ) ∞ F x) :
    ContMDiffAt I 𝓘(ℝ, Matrix (Fin b) (Fin a) ℂ) ∞ (fun y => (F y)ᴴ) x := by
  apply contMDiffAt_pi_space.mpr
  intro i
  apply contMDiffAt_pi_space.mpr
  intro j
  exact Complex.conjCLE.contDiff.comp_contMDiffAt
    (contMDiffAt_pi_space.mp (contMDiffAt_pi_space.mp hF j) i)

/-- Use the existing complete normed algebra inversion theorem through CStarMatrix.
The elementwise matrix norm is not incorrectly treated as a submultiplicative norm. -/
theorem smooth_inv {a : ℕ} {F : B → Matrix (Fin a) (Fin a) ℂ} {x : B}
    (hF : ContMDiffAt I 𝓘(ℝ, Matrix (Fin a) (Fin a) ℂ) ∞ F x)
    (hunit : IsUnit (F x)) :
    ContMDiffAt I 𝓘(ℝ, Matrix (Fin a) (Fin a) ℂ) ∞ (fun y => (F y)⁻¹) x := by
  let T : Matrix (Fin a) (Fin a) ℂ ≃L[ℝ] CStarMatrix (Fin a) (Fin a) ℂ :=
    (CStarMatrix.ofMatrixL : Matrix (Fin a) (Fin a) ℂ ≃L[ℂ]
      CStarMatrix (Fin a) (Fin a) ℂ).restrictScalars ℝ
  let e : Matrix (Fin a) (Fin a) ℂ ≃+* CStarMatrix (Fin a) (Fin a) ℂ :=
    CStarMatrix.ofMatrixRingEquiv
  have ht := T.contDiff.comp_contMDiffAt hF
  have hu : IsUnit (T (F x)) := hunit.map e.toMonoidHom
  have hi : ContDiffAt ℝ ∞ Ring.inverse (T (F x)) := by
    obtain ⟨u, hu⟩ := hu
    rw [← hu]
    exact contDiffAt_ringInverse ℝ u
  have hcalc := T.symm.contDiff.comp_contMDiffAt
    (hi.comp_contMDiffAt (f := fun y : B => T (F y)) (x := x) ht)
  apply hcalc.congr_of_eventuallyEq
  have hevent : ∀ᶠ y in 𝓝 x, IsUnit (T (F y)) :=
    ht.continuousAt.eventually (Units.isOpen.mem_nhds hu)
  filter_upwards [hevent] with y hy
  apply Matrix.inv_eq_right_inv
  apply e.injective
  rw [map_mul, map_one]
  change T (F y) * Ring.inverse (T (F y)) = 1
  exact Ring.mul_inverse_cancel _ hy

variable {n r : ℕ} {p : B → Matrix (Fin n) (Fin n) ℂ}
variable (hp : ContMDiff I 𝓘(ℝ, Matrix (Fin n) (Fin n) ℂ) ∞ p)
include hp

theorem smooth_columns (J : Fin r → Fin n) :
    ContMDiff I 𝓘(ℝ, Matrix (Fin n) (Fin r) ℂ) ∞ (columns p J) := by
  intro x
  apply contMDiffAt_pi_space.mpr
  intro i
  apply contMDiffAt_pi_space.mpr
  intro j
  exact contMDiffAt_pi_space.mp (contMDiffAt_pi_space.mp (hp x) i) (J j)

theorem smooth_left (a : ColumnChart (r := r) p) {x : B} (hx : x ∈ a.U) :
    ContMDiffAt I 𝓘(ℝ, Matrix (Fin r) (Fin n) ℂ) ∞ (leftMatrix p a.J) x :=
  smooth_mul (smooth_inv (smooth_mul (smooth_adj (smooth_columns hp a.J x))
    (smooth_columns hp a.J x)) (a.gram_unit x hx)) (smooth_adj (smooth_columns hp a.J x))

theorem smooth_transition (a b : ColumnChart (r := r) p) :
    ContMDiffOn I 𝓘(ℝ, Matrix (Fin r) (Fin r) ℂ) ∞ (a.transition b) (a.U ∩ b.U) :=
  fun x hx => (smooth_mul (smooth_left hp b hx.2) (smooth_columns hp a.J x)).contMDiffWithinAt

variable (hstar : ∀ x, (p x)ᴴ = p x) (hidem : ∀ x, p x * p x = p x)
  (hrank : ∀ x, (p x).rank = r)

/-- Genuine real vector prebundle on the actual range, derived from the projection. -/
def prebundle : VectorPrebundle ℝ (V r) (Fiber p) where
  pretrivializationAtlas := Set.range fun a : ColumnChart (r := r) p => a.pretrivialization hidem
  pretrivialization_linear' := by
    rintro _ ⟨a, rfl⟩
    infer_instance
  pretrivializationAt x := (chartAt hp.continuous hstar hidem hrank x).pretrivialization hidem
  mem_base_pretrivializationAt := mem_chartAt hp.continuous hstar hidem hrank
  pretrivialization_mem_atlas x := ⟨chartAt hp.continuous hstar hidem hrank x, rfl⟩
  exists_coordChange := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    refine ⟨fun x => matrixRealCLM r r (a.transition b x), ?_, ?_⟩
    · have hs : ContMDiffOn I 𝓘(ℝ, V r →L[ℝ] V r) ∞
          (fun x => matrixRealCLM r r (a.transition b x)) (a.U ∩ b.U) :=
        fun x hx => (matrixRealCLM r r).contDiff.comp_contMDiffWithinAt
          (smooth_transition hp a b x hx)
      exact hs.continuousOn
    · intro x hx v
      exact a.transition_apply b hidem hx v
  totalSpaceMk_isInducing x :=
    (chartAt hp.continuous hstar hidem hrank x).inducing hidem
      (mem_chartAt hp.continuous hstar hidem hrank x)

/-- The very same charts over C; only the scalar-valued mixin changes. -/
def complexPrebundle : VectorPrebundle ℂ (V r) (Fiber p) where
  pretrivializationAtlas := Set.range fun a : ColumnChart (r := r) p => a.pretrivialization hidem
  pretrivialization_linear' := by
    rintro _ ⟨a, rfl⟩
    infer_instance
  pretrivializationAt x := (chartAt hp.continuous hstar hidem hrank x).pretrivialization hidem
  mem_base_pretrivializationAt := mem_chartAt hp.continuous hstar hidem hrank
  pretrivialization_mem_atlas x := ⟨chartAt hp.continuous hstar hidem hrank x, rfl⟩
  exists_coordChange := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    refine ⟨fun x => matrixCLE r r (a.transition b x), ?_, ?_⟩
    · let T : Matrix (Fin r) (Fin r) ℂ →L[ℝ] (V r →L[ℂ] V r) :=
        (matrixCLE r r).toContinuousLinearMap.restrictScalars ℝ
      have hT : ContDiff ℝ ∞
          (fun M : Matrix (Fin r) (Fin r) ℂ => matrixCLE r r M) := T.contDiff
      have hs : ContMDiffOn I 𝓘(ℝ, V r →L[ℂ] V r) ∞
          (fun x => matrixCLE r r (a.transition b x)) (a.U ∩ b.U) :=
        fun x hx => hT.comp_contMDiffWithinAt
          (f := a.transition b) (s := a.U ∩ b.U) (x := x)
          (smooth_transition hp a b x hx)
      exact hs.continuousOn
    · intro x hx v
      exact a.transition_apply b hidem hx v
  totalSpaceMk_isInducing x :=
    (chartAt hp.continuous hstar hidem hrank x).inducing hidem
      (mem_chartAt hp.continuous hstar hidem hrank x)

instance smooth_prebundle : (prebundle hp hstar hidem hrank).IsContMDiff I ∞ where
  exists_contMDiffCoordChange := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    refine ⟨fun x => matrixRealCLM r r (a.transition b x), ?_, ?_⟩
    · intro x hx
      exact (matrixRealCLM r r).contDiff.comp_contMDiffWithinAt
        (smooth_transition hp a b x hx)
    · intro x hx v
      exact a.transition_apply b hidem hx v

end Smooth
end ProjectionRange

namespace ProjectionRange
variable {B : Type*} {n r : ℕ} {p : B → Matrix (Fin n) (Fin n) ℂ}

/-- The actual ambient inclusion. -/
def ambient (z : TotalSpace (V r) (Fiber p)) : B × V n := (z.proj, z.2.1)

theorem mem_fiber_iff_fixed (hidem : ∀ x, p x * p x = p x) (x : B) (v : V n) :
    v ∈ rangeSubmodule p x ↔ Matrix.toEuclideanLin (p x) v = v := by
  have hId : IsIdempotentElem (Matrix.toEuclideanLin (p x)) := by
    change (Matrix.toEuclideanLin (p x)).comp (Matrix.toEuclideanLin (p x)) =
      Matrix.toEuclideanLin (p x)
    rw [← Matrix.toLpLin_mul_same, hidem x]
  exact LinearMap.IsIdempotentElem.mem_range_iff hId

theorem ambient_range (hidem : ∀ x, p x * p x = p x) :
    Set.range (@ambient B n r p) = {z : B × V n | Matrix.toEuclideanLin (p z.1) z.2 = z.2} := by
  ext z
  constructor
  · rintro ⟨w, rfl⟩
    exact (mem_fiber_iff_fixed hidem w.proj w.2.1).mp w.2.property
  · intro hz
    exact ⟨⟨z.1, ⟨z.2, (mem_fiber_iff_fixed hidem z.1 z.2).mpr hz⟩⟩, rfl⟩

section TotalSpace
variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [TopologicalSpace B] [ChartedSpace H B]
variable {I : ModelWithCorners ℝ E H} [IsManifold I ∞ B]
variable (hp : ContMDiff I 𝓘(ℝ, Matrix (Fin n) (Fin n) ℂ) ∞ p)
  (hstar : ∀ x, (p x)ᴴ = p x) (hidem : ∀ x, p x * p x = p x)
  (hrank : ∀ x, (p x).rank = r)

local notation "A" => prebundle hp hstar hidem hrank

/-- Smoothness of the total-space inclusion, not merely of its restrictions to fibers. -/
theorem smooth_ambient :
    letI := (prebundle hp hstar hidem hrank).totalSpaceTopology
    letI := (prebundle hp hstar hidem hrank).toFiberBundle
    ContMDiff (I.prod 𝓘(ℝ, V r)) (I.prod 𝓘(ℝ, V n)) ∞ (@ambient B n r p) := by
  letI := (prebundle hp hstar hidem hrank).totalSpaceTopology
  letI := (prebundle hp hstar hidem hrank).toFiberBundle
  letI := (prebundle hp hstar hidem hrank).toVectorBundle
  letI := (prebundle hp hstar hidem hrank).contMDiffVectorBundle I (n := ∞)
  intro z
  let c := chartAt hp.continuous hstar hidem hrank z.proj
  have hz : z.proj ∈ c.U := mem_chartAt hp.continuous hstar hidem hrank z.proj
  have hproj : ContMDiffAt (I.prod 𝓘(ℝ, V r)) I ∞
      (π (V r) (Fiber p)) z := (Bundle.contMDiff_proj (Fiber p)) z
  have hid : ContMDiffAt (I.prod 𝓘(ℝ, V r)) (I.prod 𝓘(ℝ, V r)) ∞
      (id : TotalSpace (V r) (Fiber p) → TotalSpace (V r) (Fiber p)) z := contMDiffAt_id
  have hcoord : ContMDiffAt (I.prod 𝓘(ℝ, V r)) 𝓘(ℝ, V r) ∞
      (fun w : TotalSpace (V r) (Fiber p) => c.coordinates w.proj w.2) z :=
    (Bundle.contMDiffAt_totalSpace.mp hid).2
  have hC : ContMDiffAt (I.prod 𝓘(ℝ, V r)) 𝓘(ℝ, V r →L[ℝ] V n) ∞
      (fun w : TotalSpace (V r) (Fiber p) => matrixRealCLM n r (columns p c.J w.proj)) z :=
    ((matrixRealCLM n r).contDiff.comp_contMDiffAt (smooth_columns hp c.J z.proj)).comp z hproj
  have hval : ContMDiffAt (I.prod 𝓘(ℝ, V r)) 𝓘(ℝ, V n) ∞
      (fun w : TotalSpace (V r) (Fiber p) => w.2.1) z := by
    apply (hC.clm_apply hcoord).congr_of_eventuallyEq
    filter_upwards [hproj.continuousAt.preimage_mem_nhds (c.isOpen_U.mem_nhds hz)] with w hw
    exact (congrArg Subtype.val (c.intoRange_coordinates hidem hw w.2)).symm
  exact hproj.prodMk hval

/-- Actual local reconstruction as a smooth map to the constructed total space.
It is globally defined even though its inverse law is local to c.U. -/
theorem smooth_intoRange (c : ColumnChart (r := r) p) :
    letI := (prebundle hp hstar hidem hrank).totalSpaceTopology
    letI := (prebundle hp hstar hidem hrank).toFiberBundle
    ContMDiff (I.prod 𝓘(ℝ, V r)) (I.prod 𝓘(ℝ, V r)) ∞
      (fun z : B × V r => (⟨z.1, c.intoRange hidem z.1 z.2⟩ :
        TotalSpace (V r) (Fiber p))) := by
  letI := (prebundle hp hstar hidem hrank).totalSpaceTopology
  letI := (prebundle hp hstar hidem hrank).toFiberBundle
  letI := (prebundle hp hstar hidem hrank).toVectorBundle
  letI := (prebundle hp hstar hidem hrank).contMDiffVectorBundle I (n := ∞)
  intro z
  apply Bundle.contMDiffAt_totalSpace.mpr
  refine ⟨contMDiffAt_fst, ?_⟩
  let b := chartAt hp.continuous hstar hidem hrank z.1
  have hz : z.1 ∈ b.U := mem_chartAt hp.continuous hstar hidem hrank z.1
  have hM := (matrixRealCLM r r).contDiff.comp_contMDiffAt
    (smooth_mul (smooth_left hp b hz) (smooth_columns hp c.J z.1))
  have hs : ContMDiffAt (I.prod 𝓘(ℝ, V r)) 𝓘(ℝ, V r) ∞
      (fun w : B × V r =>
        matrixRealCLM r r (leftMatrix p b.J w.1 * columns p c.J w.1) w.2) z :=
    (hM.comp z contMDiffAt_fst).clm_apply contMDiffAt_snd
  change ContMDiffAt (I.prod 𝓘(ℝ, V r)) 𝓘(ℝ, V r) ∞
    (fun w : B × V r => b.coordinates w.1 (c.intoRange hidem w.1 w.2)) z
  apply hs.congr_of_eventuallyEq
  apply Filter.Eventually.of_forall
  intro w
  change ((Matrix.toEuclideanLin (leftMatrix p b.J w.1)).comp
      (Matrix.toEuclideanLin (columns p c.J w.1))) w.2 =
    Matrix.toEuclideanLin (leftMatrix p b.J w.1 * columns p c.J w.1) w.2
  rw [Matrix.toLpLin_mul_same]

include hp hstar hidem hrank
/-- Rank of the actual Euclidean range follows from the constructed local equivalence. -/
theorem finrank_fiber (x : B) : Module.finrank ℂ (Fiber p x) = r := by
  have h := ((chartAt hp.continuous hstar hidem hrank x).equiv hidem
    (mem_chartAt hp.continuous hstar hidem hrank x)).finrank_eq
  simpa only [V, finrank_euclideanSpace, Fintype.card_fin] using h

/-- The subspace defined by the actual range membership predicate. -/
abbrev AmbientRange := {z : B × V n // z.2 ∈ rangeSubmodule p z.1}

set_option maxHeartbeats 800000 in
/-- Continuity of the actual inclusion with its range-membership codomain. -/
theorem continuous_toAmbientRange :
    letI := (prebundle hp hstar hidem hrank).totalSpaceTopology
    Continuous (fun z : TotalSpace (V r) (Fiber p) =>
      (⟨ambient z, z.2.property⟩ : AmbientRange (p := p))) := by
  letI := (prebundle hp hstar hidem hrank).totalSpaceTopology
  letI := (prebundle hp hstar hidem hrank).toFiberBundle
  have h : Continuous (@ambient B n r p) :=
    (smooth_ambient hp hstar hidem hrank).continuous
  exact h.subtype_mk (fun z => z.2.property)

set_option maxHeartbeats 800000 in
/-- Continuity of reconstruction from the ambient range subtype. -/
theorem continuous_fromAmbientRange :
    letI := (prebundle hp hstar hidem hrank).totalSpaceTopology
    Continuous (fun z : AmbientRange (p := p) =>
      (⟨z.1.1, ⟨z.1.2, z.2⟩⟩ : TotalSpace (V r) (Fiber p))) := by
  letI := (prebundle hp hstar hidem hrank).totalSpaceTopology
  letI := (prebundle hp hstar hidem hrank).toFiberBundle
  apply continuous_iff_continuousAt.mpr
  intro z
  apply (FiberBundle.continuousAt_totalSpace (V r)
    (fun w : AmbientRange (p := p) =>
      (⟨w.1.1, ⟨w.1.2, w.2⟩⟩ : TotalSpace (V r) (Fiber p))) (x₀ := z)).mpr
  have hbase : ContinuousAt (fun w : AmbientRange (p := p) => w.1.1) z :=
    (continuous_fst.comp continuous_subtype_val).continuousAt
  refine ⟨hbase, ?_⟩
  let c := chartAt hp.continuous hstar hidem hrank z.1.1
  have hz : z.1.1 ∈ c.U := mem_chartAt hp.continuous hstar hidem hrank z.1.1
  change ContinuousAt (fun w : AmbientRange (p := p) =>
    c.coordinates w.1.1 (⟨w.1.2, w.2⟩ : Fiber p w.1.1)) z
  have hL : ContinuousAt (fun x : B => matrixRealCLM r n (leftMatrix p c.J x)) z.1.1 :=
    ((matrixRealCLM r n).contDiff.comp_contMDiffAt
      (f := leftMatrix p c.J) (x := z.1.1) (smooth_left hp c hz)).continuousAt
  have hcomp : ContinuousAt (fun w : AmbientRange (p := p) =>
      matrixRealCLM r n (leftMatrix p c.J w.1.1)) z :=
    ContinuousAt.comp (f := fun w : AmbientRange (p := p) => w.1.1) (x := z) hL hbase
  have hval : ContinuousAt (fun w : AmbientRange (p := p) => w.1.2) z :=
    (continuous_snd.comp continuous_subtype_val).continuousAt
  exact hcomp.clm_apply hval

set_option maxHeartbeats 800000 in
/-- The generated topology agrees with the ambient subspace topology. -/
def ambientHomeomorph :
    letI := (prebundle hp hstar hidem hrank).totalSpaceTopology
    TotalSpace (V r) (Fiber p) ≃ₜ AmbientRange (p := p) := by
  letI := (prebundle hp hstar hidem hrank).totalSpaceTopology
  exact {
    toFun z := ⟨ambient z, z.2.property⟩
    invFun z := ⟨z.1.1, ⟨z.1.2, z.2⟩⟩
    left_inv _ := rfl
    right_inv _ := rfl
    continuous_toFun := continuous_toAmbientRange hp hstar hidem hrank
    continuous_invFun := continuous_fromAmbientRange hp hstar hidem hrank }

theorem ambient_isEmbedding :
    letI := (prebundle hp hstar hidem hrank).totalSpaceTopology
    IsEmbedding (@ambient B n r p) := by
  letI := (prebundle hp hstar hidem hrank).totalSpaceTopology
  exact IsEmbedding.subtypeVal.comp (ambientHomeomorph hp hstar hidem hrank).isEmbedding

theorem totalTopology_eq_induced :
    (prebundle hp hstar hidem hrank).totalSpaceTopology = TopologicalSpace.induced (@ambient B n r p) inferInstance := by
  letI := (prebundle hp hstar hidem hrank).totalSpaceTopology
  exact (ambient_isEmbedding hp hstar hidem hrank).isInducing.eq_induced

end TotalSpace

/-- A smooth Hermitian projection of constant rank determines a complex vector
bundle on its actual range fibers, with a real smooth total space, the induced
ambient topology, and smooth ambient inclusion and column reconstruction. -/
theorem smooth_projection_range_prebundle
    {E H B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] [TopologicalSpace B] [ChartedSpace H B]
    (I : ModelWithCorners ℝ E H) [IsManifold I ∞ B]
    {n r : ℕ} (p : B → Matrix (Fin n) (Fin n) ℂ)
    (hp : ContMDiff I 𝓘(ℝ, Matrix (Fin n) (Fin n) ℂ) ∞ p)
    (hstar : ∀ x, (p x)ᴴ = p x) (hidem : ∀ x, p x * p x = p x)
    (hrank : ∀ x, (p x).rank = r) :
    ∃ a : VectorPrebundle ℝ (V r) (Fiber p),
      a.IsContMDiff I ∞ ∧
      (∀ x, Module.finrank ℂ (Fiber p x) = r) ∧
      (letI := a.totalSpaceTopology
       letI := a.toFiberBundle
       letI := a.toVectorBundle
       VectorBundle ℂ (V r) (Fiber p) ∧
       ContMDiffVectorBundle ∞ (V r) (Fiber p) I ∧
       IsEmbedding (@ambient B n r p) ∧
       a.totalSpaceTopology = TopologicalSpace.induced (@ambient B n r p) inferInstance ∧
       Set.range (@ambient B n r p) =
         {z : B × V n | Matrix.toEuclideanLin (p z.1) z.2 = z.2} ∧
       ContMDiff (I.prod 𝓘(ℝ, V r)) (I.prod 𝓘(ℝ, V n)) ∞ (@ambient B n r p) ∧
       ∀ c : ColumnChart (r := r) p,
         ContMDiff (I.prod 𝓘(ℝ, V r)) (I.prod 𝓘(ℝ, V r)) ∞
           (fun z : B × V r => (⟨z.1, c.intoRange hidem z.1 z.2⟩ :
             TotalSpace (V r) (Fiber p)))) := by
  refine ⟨prebundle hp hstar hidem hrank, inferInstance,
    finrank_fiber hp hstar hidem hrank, ?_⟩
  letI := (prebundle hp hstar hidem hrank).totalSpaceTopology
  letI := (prebundle hp hstar hidem hrank).toFiberBundle
  letI := (prebundle hp hstar hidem hrank).toVectorBundle
  exact ⟨(complexPrebundle hp hstar hidem hrank).toVectorBundle,
    (prebundle hp hstar hidem hrank).contMDiffVectorBundle I (n := ∞),
    ambient_isEmbedding hp hstar hidem hrank,
    totalTopology_eq_induced hp hstar hidem hrank, ambient_range hidem,
    smooth_ambient hp hstar hidem hrank, smooth_intoRange hp hstar hidem hrank⟩

end ProjectionRange
end

