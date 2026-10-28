/- GID: D5/S3/Geometry/ProjectionRange/ActualRangeTensor
   generality: G
   mirror-B: D5/B/S3/Geometry/ProjectionRange/ActualRangeTensor
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual range lifts and canonical complex tensor charts consumed by whole ST37. -/

/-
These declarations are consumed on the live proof path of
Original8340Global.whole_original_ST37. They retain actual complex matrices,
canonical Euclidean/tensor structures and the original natural-number cases.
They receive no independent new-content credit: their retention is as consumed
helpers for the whole original theorem. The associated public-declaration
escape audit is separate from Lean acceptance; no declared_validated result is
claimed without a successful source-bound native registration report.
-/

import D5.S3.Geometry.ProjectionRange.Prebundle
import Mathlib.Analysis.InnerProductSpace.TensorProduct
import Mathlib.LinearAlgebra.TensorProduct.Pi

set_option backward.isDefEq.respectTransparency false

/-! Actual tensor-product charts with the canonical tensor inner product. -/
noncomputable section
open Bundle Set Topology
open scoped TensorProduct Manifold ContDiff Matrix Matrix.Norms.Elementwise
attribute [local instance] TensorProduct.instNormedAddCommGroup
  TensorProduct.instInnerProductSpace

namespace ProjectionRange
section SmoothLift
variable {E H B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [TopologicalSpace B] [ChartedSpace H B]
  {I : ModelWithCorners ℝ E H} [IsManifold I ∞ B]
  {E' H' M : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [TopologicalSpace H'] [TopologicalSpace M] [ChartedSpace H' M]
  {IM : ModelWithCorners ℝ E' H'} [IsManifold IM ∞ M]
  {n r : ℕ} {p : B → Matrix (Fin n) (Fin n) ℂ}
  (hp : ContMDiff I 𝓘(ℝ, Matrix (Fin n) (Fin n) ℂ) ∞ p)
  (hstar : ∀ x, (p x)ᴴ = p x) (hidem : ∀ x, p x * p x = p x)
  (hrank : ∀ x, (p x).rank = r)

/-- A map into the actual range bundle is smooth when its ambient value is smooth. -/
theorem smooth_range_lift (f : M → B) (u : ∀ z, ProjectionRange.Fiber p (f z))
    (hf : ContMDiff IM I ∞ f)
    (hu : ContMDiff IM 𝓘(ℝ, V n) ∞ (fun z => (u z : V n))) :
    letI := (ProjectionRange.prebundle hp hstar hidem hrank).totalSpaceTopology
    letI := (ProjectionRange.prebundle hp hstar hidem hrank).toFiberBundle
    ContMDiff IM (I.prod 𝓘(ℝ, V r)) ∞
      (fun z => (⟨f z, u z⟩ : TotalSpace (V r) (ProjectionRange.Fiber p))) := by
  letI := (ProjectionRange.prebundle hp hstar hidem hrank).totalSpaceTopology
  letI := (ProjectionRange.prebundle hp hstar hidem hrank).toFiberBundle
  letI := (ProjectionRange.prebundle hp hstar hidem hrank).toVectorBundle
  letI := (ProjectionRange.prebundle hp hstar hidem hrank).contMDiffVectorBundle I (n := ∞)
  intro z
  apply Bundle.contMDiffAt_totalSpace.mpr
  refine ⟨hf z, ?_⟩
  let c := chartAt hp.continuous hstar hidem hrank (f z)
  have hz : f z ∈ c.U := mem_chartAt hp.continuous hstar hidem hrank (f z)
  exact (((matrixRealCLM r n).contDiff.comp_contMDiffAt
    (smooth_left hp c hz)).comp z (hf z)).clm_apply (hu z)

end SmoothLift

namespace ActualTensor

variable {B : Type*} [TopologicalSpace B] {n r d : ℕ}
variable {p : B → Matrix (Fin n) (Fin n) ℂ}
abbrev Model (r d : ℕ) := V r ⊗[ℂ] V d
instance tensorRealNormedSpace
    (U V : Type*) [NormedAddCommGroup U] [InnerProductSpace ℂ U]
    [NormedSpace ℝ U] [IsScalarTower ℝ ℂ U]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] :
    NormedSpace ℝ (U ⊗[ℂ] V) :=
  { TensorProduct.leftModule with
    norm_smul_le := fun t z => by
      rw [← algebraMap_smul ℂ t z]
      exact (norm_smul_le (algebraMap ℝ ℂ t) z).trans_eq (by rw [norm_algebraMap']) }

abbrev Fiber (p : B → Matrix (Fin n) (Fin n) ℂ) (d : ℕ) (x : B) :=
  ProjectionRange.Fiber p x ⊗[ℂ] V d

/-- Fixed tensor coefficients; the norm and inner product remain canonical. -/
def coefficients (U : Type*) [AddCommGroup U] [Module ℂ U] (d : ℕ) :
    U ⊗[ℂ] V d ≃ₗ[ℂ] (Fin d → U) :=
  (TensorProduct.congr (LinearEquiv.refl ℂ U)
    (EuclideanSpace.equiv (Fin d) ℂ).toLinearEquiv).trans
    (TensorProduct.piScalarRight ℂ ℂ U (Fin d))

theorem coefficients_tmul (U : Type*) [AddCommGroup U] [Module ℂ U]
    (u : U) (w : V d) (i : Fin d) :
    coefficients U d (u ⊗ₜ[ℂ] w) i = w i • u := by
  simp [coefficients]

theorem coefficients_map {U V' : Type*} [AddCommGroup U] [Module ℂ U]
    [AddCommGroup V'] [Module ℂ V'] (f : U →ₗ[ℂ] V')
    (z : U ⊗[ℂ] V d) (i : Fin d) :
    coefficients V' d (TensorProduct.map f LinearMap.id z) i =
      f (coefficients U d z i) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul u w => simp [coefficients_tmul]
  | add z w hz hw => simp only [map_add, Pi.add_apply, hz, hw]

theorem coefficients_expand (U : Type*) [AddCommGroup U] [Module ℂ U]
    (z : U ⊗[ℂ] V d) :
    z = ∑ i, coefficients U d z i ⊗ₜ[ℂ] EuclideanSpace.single i (1 : ℂ) := by
  apply (coefficients U d).injective
  ext j
  simp [coefficients_tmul, PiLp.single_apply]

def coordinates (a : ColumnChart (r := r) p) (x : B) :
    Fiber p d x →ₗ[ℂ] Model r d :=
  TensorProduct.map (a.coordinates x) LinearMap.id

def intoRange (a : ColumnChart (r := r) p)
    (hidem : ∀ x, p x * p x = p x) (x : B) :
    Model r d →ₗ[ℂ] Fiber p d x :=
  TensorProduct.map (a.intoRange hidem x) LinearMap.id

theorem coordinates_intoRange (a : ColumnChart (r := r) p)
    (hidem : ∀ x, p x * p x = p x) {x : B} (hx : x ∈ a.U) (z : Model r d) :
    coordinates a x (intoRange a hidem x z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul u w => simp [coordinates, intoRange, a.coordinates_intoRange hidem hx]
  | add u w hu hw => simp only [map_add, hu, hw]

theorem intoRange_coordinates (a : ColumnChart (r := r) p)
    (hidem : ∀ x, p x * p x = p x) {x : B} (hx : x ∈ a.U) (z : Fiber p d x) :
    intoRange a hidem x (coordinates a x z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul u w => simp [coordinates, intoRange, a.intoRange_coordinates hidem hx]
  | add u w hu hw => simp only [map_add, hu, hw]

def equiv (a : ColumnChart (r := r) p)
    (hidem : ∀ x, p x * p x = p x) {x : B} (hx : x ∈ a.U) :
    Fiber p d x ≃ₗ[ℂ] Model r d :=
  { coordinates a x with
    invFun := intoRange a hidem x
    left_inv := intoRange_coordinates a hidem hx
    right_inv := coordinates_intoRange a hidem hx }

def pretrivialization (a : ColumnChart (r := r) p)
    (hidem : ∀ x, p x * p x = p x) :
    Pretrivialization (Model r d) (π (Model r d) (Fiber p d)) where
  toFun z := (z.proj, coordinates a z.proj z.2)
  invFun z := ⟨z.1, intoRange a hidem z.1 z.2⟩
  source := (π (Model r d) (Fiber p d)) ⁻¹' a.U
  target := a.U ×ˢ univ
  map_source' z hz := ⟨hz, mem_univ _⟩
  map_target' z hz := hz.1
  left_inv' z hz := by
    change TotalSpace.mk z.proj (intoRange a hidem z.proj (coordinates a z.proj z.2)) = z
    rw [intoRange_coordinates a hidem hz]
  right_inv' z hz := by
    change (z.1, coordinates a z.1 (intoRange a hidem z.1 z.2)) = z
    rw [coordinates_intoRange a hidem hz.1]
  open_target := a.isOpen_U.prod isOpen_univ
  baseSet := a.U
  open_baseSet := a.isOpen_U
  source_eq := rfl
  target_eq := rfl
  proj_toFun := fun _ _ => rfl

instance complex_linear (a : ColumnChart (r := r) p)
    (hidem : ∀ x, p x * p x = p x) :
    (pretrivialization (d := d) a hidem).IsLinear ℂ where
  linear x _ := (coordinates a x).isLinear

instance real_linear (a : ColumnChart (r := r) p)
    (hidem : ∀ x, p x * p x = p x) :
    (pretrivialization (d := d) a hidem).IsLinear ℝ where
  linear x _ := ((coordinates (d := d) a x).restrictScalars ℝ).isLinear

theorem symm_eq (a : ColumnChart (r := r) p)
    (hidem : ∀ x, p x * p x = p x) {x : B} (hx : x ∈ a.U) (z : Model r d) :
    (pretrivialization a hidem).symm x z = intoRange a hidem x z := by
  apply (equiv a hidem hx).injective
  change coordinates a x ((pretrivialization a hidem).symm x z) =
    coordinates a x (intoRange a hidem x z)
  rw [coordinates_intoRange a hidem hx]
  exact congrArg Prod.snd ((pretrivialization a hidem).apply_mk_symm hx z)

def tensorOperator (r d : ℕ) :
    (V r →L[ℂ] V r) →L[ℂ] (Model r d →L[ℂ] Model r d) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun f => f.rTensor (V d)
      map_add' := fun f g => ContinuousLinearMap.rTensor_add _ f g
      map_smul' := fun c f => ContinuousLinearMap.rTensor_smul _ c f }

def transitionComplex (a b : ColumnChart (r := r) p) (x : B) :
    Model r d →L[ℂ] Model r d := tensorOperator r d (matrixCLE r r (a.transition b x))

def transitionReal (r d : ℕ) :
    Matrix (Fin r) (Fin r) ℂ →L[ℝ] (Model r d →L[ℝ] Model r d) :=
  (ContinuousLinearMap.restrictScalarsL ℂ (Model r d) (Model r d) ℝ ℝ).comp
    (((tensorOperator r d).restrictScalars ℝ).comp
      ((matrixCLE r r).toContinuousLinearMap.restrictScalars ℝ))

theorem transition_apply (a b : ColumnChart (r := r) p)
    (hidem : ∀ x, p x * p x = p x) {x : B} (hx : x ∈ a.U ∩ b.U) (z : Model r d) :
    transitionComplex a b x z =
      ((pretrivialization b hidem) ⟨x, (pretrivialization a hidem).symm x z⟩).2 := by
  rw [symm_eq a hidem hx.1]
  change transitionComplex a b x z = coordinates b x (intoRange a hidem x z)
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul u w =>
    change (matrixCLE r r (a.transition b x) u) ⊗ₜ[ℂ] w =
      (b.coordinates x (a.intoRange hidem x u)) ⊗ₜ[ℂ] w
    congr 1
    have hh := a.transition_apply b hidem hx u
    rw [ProjectionRange.ColumnChart.symm_eq a hidem hx.1] at hh
    exact hh
  | add u w hu hw => simp only [map_add, hu, hw]

section Smooth
variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [ChartedSpace H B]
variable {I : ModelWithCorners ℝ E H}
variable (hp : ContMDiff I 𝓘(ℝ, Matrix (Fin n) (Fin n) ℂ) ∞ p)
  (hstar : ∀ x, (p x)ᴴ = p x) (hidem : ∀ x, p x * p x = p x)
  (hrank : ∀ x, (p x).rank = r)

def prebundle : VectorPrebundle ℝ (Model r d) (Fiber p d) where
  pretrivializationAtlas := Set.range fun a : ColumnChart (r := r) p => pretrivialization a hidem
  pretrivialization_linear' := by rintro _ ⟨a,rfl⟩; infer_instance
  pretrivializationAt x := pretrivialization (chartAt hp.continuous hstar hidem hrank x) hidem
  mem_base_pretrivializationAt := mem_chartAt hp.continuous hstar hidem hrank
  pretrivialization_mem_atlas x := ⟨chartAt hp.continuous hstar hidem hrank x,rfl⟩
  exists_coordChange := by
    rintro _ ⟨a,rfl⟩ _ ⟨b,rfl⟩
    refine ⟨fun x => transitionReal r d (a.transition b x), ?_, ?_⟩
    · have hs : ContMDiffOn I 𝓘(ℝ, Model r d →L[ℝ] Model r d) ∞
          (fun x => transitionReal r d (a.transition b x)) (a.U ∩ b.U) :=
        fun x hx => (transitionReal r d).contDiff.comp_contMDiffWithinAt
          (smooth_transition hp a b x hx)
      exact hs.continuousOn
    · intro x hx z
      exact transition_apply a b hidem hx z
  totalSpaceMk_isInducing x := by
    exact isInducing_const_prod.mpr
      ((equiv (chartAt hp.continuous hstar hidem hrank x) hidem
        (mem_chartAt hp.continuous hstar hidem hrank x)).toContinuousLinearEquiv.toHomeomorph.isInducing)

def complexPrebundle : VectorPrebundle ℂ (Model r d) (Fiber p d) where
  pretrivializationAtlas := Set.range fun a : ColumnChart (r := r) p => pretrivialization a hidem
  pretrivialization_linear' := by rintro _ ⟨a,rfl⟩; infer_instance
  pretrivializationAt x := pretrivialization (chartAt hp.continuous hstar hidem hrank x) hidem
  mem_base_pretrivializationAt := mem_chartAt hp.continuous hstar hidem hrank
  pretrivialization_mem_atlas x := ⟨chartAt hp.continuous hstar hidem hrank x,rfl⟩
  exists_coordChange := by
    rintro _ ⟨a,rfl⟩ _ ⟨b,rfl⟩
    refine ⟨transitionComplex a b, ?_, ?_⟩
    · let T := ((tensorOperator r d).restrictScalars ℝ).comp
        ((matrixCLE r r).toContinuousLinearMap.restrictScalars ℝ)
      have hs : ContMDiffOn I 𝓘(ℝ, Model r d →L[ℂ] Model r d) ∞
          (transitionComplex a b) (a.U ∩ b.U) :=
        fun x hx => T.contDiff.comp_contMDiffWithinAt (smooth_transition hp a b x hx)
      exact hs.continuousOn
    · intro x hx z
      exact transition_apply a b hidem hx z
  totalSpaceMk_isInducing x := by
    exact isInducing_const_prod.mpr
      ((equiv (chartAt hp.continuous hstar hidem hrank x) hidem
        (mem_chartAt hp.continuous hstar hidem hrank x)).toContinuousLinearEquiv.toHomeomorph.isInducing)

instance smooth_prebundle : (prebundle (d := d) hp hstar hidem hrank).IsContMDiff I ∞ where
  exists_contMDiffCoordChange := by
    rintro _ ⟨a,rfl⟩ _ ⟨b,rfl⟩
    refine ⟨fun x => transitionReal r d (a.transition b x), ?_, ?_⟩
    · intro x hx
      exact (transitionReal r d).contDiff.comp_contMDiffWithinAt
        (smooth_transition hp a b x hx)
    · intro x hx z
      exact transition_apply a b hidem hx z

end Smooth
section SmoothCoefficients
variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [ChartedSpace H B]
  {I : ModelWithCorners ℝ E H} [IsManifold I ∞ B]
  (hp : ContMDiff I 𝓘(ℝ, Matrix (Fin n) (Fin n) ℂ) ∞ p)
  (hstar : ∀ x, (p x)ᴴ = p x) (hidem : ∀ x, p x * p x = p x)
  (hrank : ∀ x, (p x).rank = r)

/-- Each ambient coefficient is smooth on the actual tensor total space. -/
theorem smooth_coefficient (i : Fin d) :
    letI := (prebundle (d := d) hp hstar hidem hrank).totalSpaceTopology
    letI := (prebundle (d := d) hp hstar hidem hrank).toFiberBundle
    ContMDiff (I.prod 𝓘(ℝ, Model r d)) 𝓘(ℝ, V n) ∞
      (fun z : TotalSpace (Model r d) (Fiber p d) =>
        (coefficients (ProjectionRange.Fiber p z.proj) d z.2 i : V n)) := by
  letI := (prebundle (d := d) hp hstar hidem hrank).totalSpaceTopology
  letI := (prebundle (d := d) hp hstar hidem hrank).toFiberBundle
  letI := (prebundle (d := d) hp hstar hidem hrank).toVectorBundle
  letI := (prebundle (d := d) hp hstar hidem hrank).contMDiffVectorBundle I (n := ∞)
  intro z
  let c := chartAt hp.continuous hstar hidem hrank z.proj
  have hz : z.proj ∈ c.U := mem_chartAt hp.continuous hstar hidem hrank z.proj
  have hproj : ContMDiffAt (I.prod 𝓘(ℝ, Model r d)) I ∞
      (fun w : TotalSpace (Model r d) (Fiber p d) => w.proj) z :=
    Bundle.contMDiffAt_proj (Fiber p d) (IB := I) (F := Model r d) (n := ∞) (p := z)
  have hid : ContMDiffAt (I.prod 𝓘(ℝ, Model r d)) (I.prod 𝓘(ℝ, Model r d)) ∞
      (id : TotalSpace (Model r d) (Fiber p d) → TotalSpace (Model r d) (Fiber p d)) z :=
    contMDiffAt_id
  have hcoord : ContMDiffAt (I.prod 𝓘(ℝ, Model r d)) 𝓘(ℝ, Model r d) ∞
      (fun w : TotalSpace (Model r d) (Fiber p d) => coordinates c w.proj w.2) z :=
    (Bundle.contMDiffAt_totalSpace.mp hid).2
  let Ccomplex : Model r d →ₗ[ℂ] V r :=
    (LinearMap.proj i).comp (coefficients (V r) d).toLinearMap
  let C : Model r d →L[ℝ] V r := Ccomplex.toContinuousLinearMap.restrictScalars ℝ
  have hC := C.contDiff.comp_contMDiffAt hcoord
  have hM := ((matrixRealCLM n r).contDiff.comp_contMDiffAt
    (smooth_columns hp c.J z.proj)).comp z hproj
  apply (hM.clm_apply hC).congr_of_eventuallyEq
  filter_upwards [hproj.continuousAt.preimage_mem_nhds (c.isOpen_U.mem_nhds hz)] with w hw
  have he := congrArg (fun t : Fiber p d w.proj =>
    (coefficients (ProjectionRange.Fiber p w.proj) d t i : V n))
    (intoRange_coordinates c hidem hw w.2)
  simp only [intoRange, coefficients_map] at he
  change Matrix.toEuclideanLin (columns p c.J w.proj)
      (coefficients (V r) d (coordinates c w.proj w.2) i) =
    (coefficients (ProjectionRange.Fiber p w.proj) d w.2 i : V n) at he
  change (coefficients (ProjectionRange.Fiber p w.proj) d w.2 i : V n) =
    Matrix.toEuclideanLin (columns p c.J w.proj)
      (coefficients (V r) d (coordinates c w.proj w.2) i)
  exact he.symm

variable {E' H' M : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [TopologicalSpace H'] [TopologicalSpace M] [ChartedSpace H' M]
  {IM : ModelWithCorners ℝ E' H'} [IsManifold IM ∞ M]

/-- A finite tensor sum of smooth ambient range vectors is a smooth total-space map. -/
theorem smooth_tensor_sum (f : M → B)
    (u : Fin d → ∀ z, ProjectionRange.Fiber p (f z))
    (hf : ContMDiff IM I ∞ f)
    (hu : ∀ i, ContMDiff IM 𝓘(ℝ, V n) ∞ (fun z => (u i z : V n))) :
    letI := (prebundle (d := d) hp hstar hidem hrank).totalSpaceTopology
    letI := (prebundle (d := d) hp hstar hidem hrank).toFiberBundle
    ContMDiff IM (I.prod 𝓘(ℝ, Model r d)) ∞
      (fun z => (⟨f z, ∑ i, u i z ⊗ₜ[ℂ] EuclideanSpace.single i (1 : ℂ)⟩ :
        TotalSpace (Model r d) (Fiber p d))) := by
  letI := (prebundle (d := d) hp hstar hidem hrank).totalSpaceTopology
  letI := (prebundle (d := d) hp hstar hidem hrank).toFiberBundle
  letI := (prebundle (d := d) hp hstar hidem hrank).toVectorBundle
  letI := (prebundle (d := d) hp hstar hidem hrank).contMDiffVectorBundle I (n := ∞)
  intro z
  apply Bundle.contMDiffAt_totalSpace.mpr
  refine ⟨hf z, ?_⟩
  let c := chartAt hp.continuous hstar hidem hrank (f z)
  have hz : f z ∈ c.U := mem_chartAt hp.continuous hstar hidem hrank (f z)
  have hM := ((matrixRealCLM r n).contDiff.comp_contMDiffAt
    (smooth_left hp c hz)).comp z (hf z)
  have hs : ContMDiffAt IM 𝓘(ℝ, Model r d) ∞
      (fun w => ∑ i, c.coordinates (f w) (u i w) ⊗ₜ[ℂ] EuclideanSpace.single i (1 : ℂ)) z := by
    apply contMDiffAt_finsetSum
    intro i hi
    let Tcomplex : V r →ₗ[ℂ] Model r d :=
      (TensorProduct.mk ℂ (V r) (V d)).flip (EuclideanSpace.single i (1 : ℂ))
    let T : V r →L[ℝ] Model r d :=
      Tcomplex.toContinuousLinearMap.restrictScalars ℝ
    change ContMDiffAt IM 𝓘(ℝ, Model r d) ∞
      (fun w => T (matrixRealCLM r n (leftMatrix p c.J (f w)) (u i w : V n))) z
    exact T.contDiff.comp_contMDiffAt (hM.clm_apply (hu i z))
  change ContMDiffAt IM 𝓘(ℝ, Model r d) ∞
    (fun w => coordinates c (f w)
      (∑ i, u i w ⊗ₜ[ℂ] EuclideanSpace.single i (1 : ℂ))) z
  simpa only [coordinates, map_sum, TensorProduct.map_tmul, LinearMap.id_apply] using hs

end SmoothCoefficients

end ActualTensor
end ProjectionRange
