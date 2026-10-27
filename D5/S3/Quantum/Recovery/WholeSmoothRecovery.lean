/- GID: D5/S3/Quantum/Recovery/WholeSmoothRecovery
   generality: G
   mirror-B: D5/B/S3/Quantum/Recovery/WholeSmoothRecovery
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Whole ST37 for actual complex channels, CFC functions and canonical tensor bundles. -/

import Lean
import D5.S3.SpectralTopology.ActualSpectralWhitening
import D5.S3.Quantum.Recovery.ActualChannelAlgebra
import D5.S3.Quantum.Recovery.PointwiseTensorRecovery
import D5.S3.Quantum.Recovery.MatrixUnitDecoder
import D5.S3.Quantum.Transport.MatrixUnitDyson
import D5.S3.Geometry.ProjectionRange.ActualRangeTensor
import D5.S3.Quantum.QuantumChannels.IptPptSquaredEquivalence
/-! The original ST37 target on actual smooth channels. -/
noncomputable section
open Bundle Filter Set Topology
open scoped BigOperators Matrix MatrixOrder ComplexOrder Topology Manifold ContDiff TensorProduct
  Matrix.Norms.Elementwise
open D5.S3.Quantum.Recovery.SpectralTransposeRecovery
open D5.S3.Quantum.Recovery.MatrixUnitDecoder
open D5.S3.Quantum.Foundation.FiniteKrausChannel
open PhyslibLeaf
set_option backward.isDefEq.respectTransparency true
set_option diagnostics false
attribute [local instance] TensorProduct.instNormedAddCommGroup
  TensorProduct.instInnerProductSpace
attribute [local instance] Matrix.seminormedAddCommGroup
  Matrix.normedAddCommGroup Matrix.normedSpace
attribute [local irreducible] spectralInverseSqrt spectralSupport
namespace Original8340Global

-- Select the existing CLM operator norm at the original matrix norms and topology.
private abbrev explicitCLMnorm (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    [NormedSpace 𝕜 ℂ]
    (m n p q : Type*) [Fintype m] [Fintype n] [Fintype p] [Fintype q] :
    NormedAddCommGroup (Matrix m n ℂ →L[𝕜] Matrix p q ℂ) :=
  ContinuousLinearMap.toNormedAddCommGroup
    (E := Matrix m n ℂ) (F := Matrix p q ℂ) (σ₁₂ := RingHom.id 𝕜)
attribute [local instance 2000] explicitCLMnorm
private abbrev explicitCLMnormedSpace (𝕜 𝕜' : Type*)
    [NontriviallyNormedField 𝕜] [NormedField 𝕜']
    [NormedSpace 𝕜 ℂ] [NormedSpace 𝕜' ℂ] [SMulCommClass 𝕜 𝕜' ℂ]
    (m n p q : Type*) [Fintype m] [Fintype n] [Fintype p] [Fintype q] :
    NormedSpace 𝕜' (Matrix m n ℂ →L[𝕜] Matrix p q ℂ) :=
  ContinuousLinearMap.toNormedSpace
    (E := Matrix m n ℂ) (F := Matrix p q ℂ)
    (σ₁₂ := RingHom.id 𝕜) (𝕜' := 𝕜')
attribute [local instance 2000] explicitCLMnormedSpace
private abbrev normedTopology (V : Type*) (nV : NormedAddCommGroup V) :
    TopologicalSpace V :=
  nV.toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
private abbrev normedIdentityChart (V : Type*) (nV : NormedAddCommGroup V) :
    @ChartedSpace V (normedTopology V nV) V (normedTopology V nV) :=
  @chartedSpaceSelf V (normedTopology V nV)
-- The norm-model and imported Matrix topologies are definitionally equal.
-- Explicit Matrix topology spelling selects the canonical instance; it installs no topology.
private abbrev matrixIdentityChart (m n : Type*) [Fintype m] [Fintype n] :
    @ChartedSpace (Matrix m n ℂ)
      (normedTopology _ (Matrix.normedAddCommGroup : NormedAddCommGroup (Matrix m n ℂ)))
      (Matrix m n ℂ) (inferInstanceAs (TopologicalSpace (Matrix m n ℂ))) :=
  normedIdentityChart (Matrix m n ℂ)
    (Matrix.normedAddCommGroup : NormedAddCommGroup (Matrix m n ℂ))
attribute [local instance 2000] matrixIdentityChart
private abbrev matrixLieAddGroup (m n : Type*) [Fintype m] [Fintype n] :
    LieAddGroup 𝓘(ℝ, Matrix m n ℂ) ∞ (Matrix m n ℂ) :=
  instNormedSpaceLieAddGroup (𝕜 := ℝ) (E := Matrix m n ℂ) (n := ∞)
private abbrev matrixContMDiffAdd (m n : Type*) [Fintype m] [Fintype n] :
    ContMDiffAdd 𝓘(ℝ, Matrix m n ℂ) ∞ (Matrix m n ℂ) :=
  instContMDiffAddSelf
attribute [local instance 2000] matrixLieAddGroup matrixContMDiffAdd
-- Reuse the operator norm's bounded-convergence uniformity (Operator/Basic).
private abbrev clmIdentityChart (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    [NormedSpace 𝕜 ℂ]
    (m n p q : Type*) [Fintype m] [Fintype n] [Fintype p] [Fintype q] :
    @ChartedSpace (Matrix m n ℂ →L[𝕜] Matrix p q ℂ)
      (normedTopology _ (explicitCLMnorm 𝕜 m n p q))
      (Matrix m n ℂ →L[𝕜] Matrix p q ℂ)
      (ContinuousLinearMap.topologicalSpace
        (E := Matrix m n ℂ) (F := Matrix p q ℂ) (σ := RingHom.id 𝕜)) :=
  normedIdentityChart (Matrix m n ℂ →L[𝕜] Matrix p q ℂ)
    (explicitCLMnorm 𝕜 m n p q)
attribute [local instance 2000] clmIdentityChart
set_option maxHeartbeats 3000000 in -- Canonical structures; original ceiling.
private theorem st37_matrix_unit_slice
    {E H B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] [TopologicalSpace B] [ChartedSpace H B] [CompactSpace B]
    (I : ModelWithCorners ℝ E H) [IsManifold I ∞ B]
    {d n : ℕ}
    (pi : B → Matrix (Fin d) (Fin d) ℂ → Matrix (Fin n) (Fin n) ℂ)
    (hpi : ContMDiff (I.prod 𝓘(ℝ, Matrix (Fin d) (Fin d) ℂ))
      𝓘(ℝ, Matrix (Fin n) (Fin n) ℂ) ∞
      (fun z : B × Matrix (Fin d) (Fin d) ℂ => pi z.1 z.2))
    (i j : Fin d) : ContMDiff I
      𝓘(ℝ, Matrix (Fin n) (Fin n) ℂ) ∞ (fun x => pi x (Matrix.single i j 1)) :=
  hpi.comp (contMDiff_id.prodMk contMDiff_const)

-- Consumed finite tensor calculation at the original complex Euclidean structures.
set_option maxHeartbeats 3000000 in -- Canonical structures; original ceiling.
private theorem st37_tensor_sum_inner {d n : ℕ}
    (AA : (Fin d × Fin n) → Matrix (Fin n) (Fin d) ℂ)
    (u w : EuclideanSpace ℂ (Fin d)) :
    inner ℂ (∑ mu, (AA mu).toEuclideanLin u ⊗ₜ[ℂ] EuclideanSpace.single mu (1 : ℂ))
      (∑ mu, (AA mu).toEuclideanLin w ⊗ₜ[ℂ] EuclideanSpace.single mu (1 : ℂ)) =
    inner ℂ u ((∑ mu, (LinearMap.adjoint (AA mu).toEuclideanLin).comp
      (AA mu).toEuclideanLin) w) := by
  calc
    _ = ∑ mu, inner ℂ ((AA mu).toEuclideanLin u) ((AA mu).toEuclideanLin w) := by
      simp only [sum_inner, inner_sum, TensorProduct.inner_tmul,
        EuclideanSpace.inner_single_left, map_one, PiLp.single_apply,
        mul_ite, mul_one, mul_zero]
      simp
    _ = _ := by
      simp only [LinearMap.sum_apply, LinearMap.comp_apply,
        ← LinearMap.adjoint_inner_right]
      exact (inner_sum (𝕜 := ℂ) (E := EuclideanSpace ℂ (Fin d)) Finset.univ _ _).symm

set_option maxHeartbeats 3000000 in -- Canonical structures; original ceiling.
private theorem st37_tensor_sum_smooth
    {E H B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] [TopologicalSpace B] [ChartedSpace H B]
    (I : ModelWithCorners ℝ E H) [IsManifold I ∞ B] {d n : ℕ}
    (AA : B → (Fin d × Fin n) → Matrix (Fin n) (Fin d) ℂ)
    (hAA : ∀ mu, ContMDiff I 𝓘(ℝ, Matrix (Fin n) (Fin d) ℂ) ∞ (fun x => AA x mu)) :
    ContMDiff (I.prod 𝓘(ℝ, EuclideanSpace ℂ (Fin d)))
      𝓘(ℝ, EuclideanSpace ℂ (Fin n) ⊗[ℂ] EuclideanSpace ℂ (Fin d × Fin n)) ∞
      (fun z : B × EuclideanSpace ℂ (Fin d) => ∑ mu,
        (AA z.1 mu).toEuclideanLin z.2 ⊗ₜ[ℂ] EuclideanSpace.single mu (1 : ℂ)) := by
  apply ContMDiff.sum
  intro mu hmu
  let Tcomplex : EuclideanSpace ℂ (Fin n) →ₗ[ℂ]
      EuclideanSpace ℂ (Fin n) ⊗[ℂ] EuclideanSpace ℂ (Fin d × Fin n) :=
    (TensorProduct.mk ℂ _ _).flip (EuclideanSpace.single mu (1 : ℂ))
  let T := Tcomplex.toContinuousLinearMap.restrictScalars ℝ
  have ha : ContMDiff (I.prod 𝓘(ℝ, EuclideanSpace ℂ (Fin d)))
      𝓘(ℝ, EuclideanSpace ℂ (Fin d) →L[ℝ] EuclideanSpace ℂ (Fin n)) ∞
      (fun z : B × EuclideanSpace ℂ (Fin d) =>
        ProjectionRange.matrixRealCLM n d (AA z.1 mu)) :=
    ((ProjectionRange.matrixRealCLM n d).contDiff.comp_contMDiff (hAA mu)).comp
      contMDiff_fst
  exact T.contDiff.comp_contMDiff (ha.clm_apply contMDiff_snd)

-- Transport the full dependent conclusion at the original range and tensor structures.
private def st37_pointwise_statement {d n : ℕ}
    (Q : Matrix (Fin n) (Fin n) ℂ)
    (N : Matrix (Fin d) (Fin d) ℂ → Matrix (Fin n) (Fin n) ℂ)
    (v : Fin d) : Prop :=
    let P := spectralSupport Q
    let W := spectralInverseSqrt Q
    let F := fun i j => W * N (Matrix.single i j 1) * W
    let EK := LinearMap.range P.toEuclideanLin
    let FK := LinearMap.range (F v v).toEuclideanLin
    let L := EuclideanSpace ℂ (Fin d)
    let Vn := EuclideanSpace ℂ (Fin n)
    letI : NormedAddCommGroup (FK ⊗[ℂ] L) :=
      TensorProduct.instNormedAddCommGroup (𝕜 := ℂ) (E := FK) (F := L)
    letI : InnerProductSpace ℂ (FK ⊗[ℂ] L) :=
      TensorProduct.instInnerProductSpace (𝕜 := ℂ) (E := FK) (F := L)
    ∃ Theta : (FK) ⊗[ℂ] L ≃ₗᵢ[ℂ] EK,
      ∃ B : Vn →ₗ[ℂ] (Fin d → FK),
      ∃ sigma sigmaInv : FK →ₗ[ℂ] FK,
      (∀ (w : FK) (i : Fin d),
        (Theta (w ⊗ₜ[ℂ] EuclideanSpace.single i 1) : Vn) = (F i v).toEuclideanLin w) ∧
      (∀ y : EK, Theta.symm y = ∑ i, B y i ⊗ₜ[ℂ] EuclideanSpace.single i (1 : ℂ)) ∧
      (∀ (y : Vn) (i : Fin d), (B y i : Vn) = (F v i).toEuclideanLin y) ∧
      (LinearMap.adjoint (𝕜 := ℂ) (E := (FK) ⊗[ℂ] L) (F := EK) Theta.toLinearMap) = Theta.symm.toLinearMap ∧
      (LinearMap.adjoint (𝕜 := ℂ) (E := EK) (F := Vn) EK.subtype).comp EK.subtype = LinearMap.id ∧
      EK.subtype.comp (LinearMap.adjoint (𝕜 := ℂ) (E := EK) (F := Vn) EK.subtype) = P.toEuclideanLin ∧
      (LinearMap.adjoint (𝕜 := ℂ) (E := FK) (F := Vn) FK.subtype).comp FK.subtype = LinearMap.id ∧
      FK.subtype.comp (LinearMap.adjoint (𝕜 := ℂ) (E := FK) (F := Vn) FK.subtype) = (F v v).toEuclideanLin ∧
      (∀ w : FK, (sigma w : Vn) = (Q).toEuclideanLin w) ∧
      LinearMap.IsPositive (𝕜 := ℂ) (E := FK) sigma ∧
      (∀ w : FK, w ≠ 0 → 0 < (inner ℂ w (sigma w)).re) ∧
      sigma.comp sigmaInv = LinearMap.id ∧
      sigmaInv.comp sigma = LinearMap.id ∧
      LinearMap.trace ℂ (FK) sigma = 1 ∧
      (∀ z : (FK) ⊗[ℂ] L,
        (Q).toEuclideanLin (Theta z : Vn) =
        (Theta (TensorProduct.map sigma LinearMap.id z) : Vn)) ∧
      (let U : (FK) ⊗[ℂ] L →ₗ[ℂ] Vn :=
        EK.subtype.comp Theta.toLinearMap
       ∀ T : Matrix (Fin d) (Fin d) ℂ,
         (N T).toEuclideanLin =
         (U.comp (TensorProduct.map sigma T.toEuclideanLin)).comp (LinearMap.adjoint (𝕜 := ℂ) (E := (FK) ⊗[ℂ] L) (F := Vn) U)) ∧
      (∀ w : FK, (sigmaInv w : Vn) = (W * W).toEuclideanLin w)

-- Reuse the complete pointwise construction, including its existing inverse formula.
set_option maxHeartbeats 3000000 in -- Canonical structures; original ceiling.
private theorem st37_actual_pointwise {d n : ℕ} (hd : 0 < d)
    (N : Matrix (Fin d) (Fin d) ℂ →L[ℂ] Matrix (Fin n) (Fin n) ℂ)
    (hCP : MatrixMap.IsCompletelyPositive N.toLinearMap)
    (hTP : ∀ X, Matrix.trace (N X) = Matrix.trace X)
    (hLeft : ∃ R : MatrixMap (Fin n) (Fin d) ℂ,
      R.IsCompletelyPositive ∧ (∀ X, Matrix.trace (R X) = Matrix.trace X) ∧
      ∀ X, R (N X) = X) (v : Fin d) :
    st37_pointwise_statement (N 1) (fun T => N T) v := by
  classical
  let Q := N 1
  have hN_apply (T : Matrix (Fin d) (Fin d) ℂ) : N.toLinearMap T = N T := rfl
  obtain ⟨R, hRC, hRT, hRL⟩ := hLeft
  obtain ⟨hNE, hETP⟩ := actual_sqrt_columns_kraus (N).toLinearMap (hCP) (hTP)
  obtain ⟨hRA, hATP⟩ := actual_sqrt_columns_kraus R hRC hRT
  have hleft (T : Matrix (Fin d) (Fin d) ℂ) :
      (∑ b, sqrtColumn R b *
        (∑ a, sqrtColumn (N).toLinearMap a * T * (sqrtColumn (N).toLinearMap a)ᴴ) *
          (sqrtColumn R b)ᴴ) = T := by
    rw [← hNE T, ← hRA]
    exact hRL T
  have hn : Nonempty (Fin n) := by
    by_contra hz
    letI : IsEmpty (Fin n) := not_nonempty_iff.mp hz
    have hh := hTP (1 : Matrix (Fin d) (Fin d) ℂ)
    have hd0 : (d : ℂ) = 0 := by simpa using hh.symm
    exact (Nat.ne_of_gt hd) (Nat.cast_eq_zero.mp hd0)
  letI : Nonempty (Fin n) := hn
  have hq : (∑ a, sqrtColumn (N).toLinearMap a *
      (sqrtColumn (N).toLinearMap a)ᴴ) = Q := by
    simpa only [Q, Matrix.mul_one, hN_apply] using (hNE 1).symm
  have hnval (T : Matrix (Fin d) (Fin d) ℂ) :
      (∑ a, sqrtColumn (N).toLinearMap a * T *
        (sqrtColumn (N).toLinearMap a)ᴴ) = N T := by
    simpa only [hN_apply] using (hNE T).symm
  let NX : Matrix (Fin d) (Fin d) ℂ → Matrix (Fin n) (Fin n) ℂ := fun T =>
    ∑ a, sqrtColumn N.toLinearMap a * T * (sqrtColumn N.toLinearMap a)ᴴ
  have hnfun : NX = fun T => N T := funext hnval
  have hc := Original8340InheritedCoreAttempt.whole_pointwise_core_attempt
    (sqrtColumn (N).toLinearMap) hETP (sqrtColumn R) hATP hleft v v
  change st37_pointwise_statement
    (∑ a, sqrtColumn N.toLinearMap a * (sqrtColumn N.toLinearMap a)ᴴ) NX v at hc
  rw [hq, hnfun] at hc
  exact hc

set_option maxHeartbeats 3000000 in -- Canonical structures; original ceiling.
private theorem st37_bundle_geometry
    {E H B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] [TopologicalSpace B] [ChartedSpace H B] [CompactSpace B]
    (I : ModelWithCorners ℝ E H) [IsManifold I ∞ B]
    {d n k : ℕ} (hd : 0 < d)
    (N : B → (Matrix (Fin d) (Fin d) ℂ →L[ℂ] Matrix (Fin n) (Fin n) ℂ))
    (hCP : ∀ x, MatrixMap.IsCompletelyPositive (N x).toLinearMap)
    (hTP : ∀ x X, Matrix.trace (N x X) = Matrix.trace X)
    (hLeft : ∀ x, ∃ R : MatrixMap (Fin n) (Fin d) ℂ,
      R.IsCompletelyPositive ∧ (∀ X, Matrix.trace (R X) = Matrix.trace X) ∧
      ∀ X, R (N x X) = X) :
    let v : Fin d := ⟨0, hd⟩
    let Q := fun x => N x 1
    let P := fun x => spectralSupport (Q x)
    let W := fun x => spectralInverseSqrt (Q x)
    let pi := fun x A => W x * N x A * W x
    let F := fun x i j => pi x (Matrix.single i j 1)
    let EK := ProjectionRange.Fiber P
    let FK := ProjectionRange.Fiber (fun x => F x v v)
    let L := EuclideanSpace ℂ (Fin d)
    let Vn := EuclideanSpace ℂ (Fin n)
    let Vk := EuclideanSpace ℂ (Fin k)
    let Vkd := EuclideanSpace ℂ (Fin (k * d))
    ∀ (hQ : ContMDiff I 𝓘(ℝ, Matrix (Fin n) (Fin n) ℂ) ∞ Q)
      (hP : ContMDiff I 𝓘(ℝ, Matrix (Fin n) (Fin n) ℂ) ∞ P)
      (hW : ContMDiff I 𝓘(ℝ, Matrix (Fin n) (Fin n) ℂ) ∞ W)
      (hPstar : ∀ x, (P x)ᴴ = P x)
      (hPidem : ∀ x, P x * P x = P x)
      (hPrank : ∀ x, (P x).rank = k * d)
      (hFsm : ∀ i j, ContMDiff I 𝓘(ℝ, Matrix (Fin n) (Fin n) ℂ) ∞
        (fun x => F x i j))
      (hFstar : ∀ x i j, (F x i j)ᴴ = F x j i)
      (hFidem : ∀ x, F x v v * F x v v = F x v v)
      (hFrank : ∀ x, (F x v v).rank = k),
    ∃ (aE : VectorPrebundle ℝ Vkd EK) (aF : VectorPrebundle ℝ Vk FK)
        (aT : VectorPrebundle ℝ (Vk ⊗[ℂ] L) (fun x => FK x ⊗[ℂ] L))
        (hE : aE.IsContMDiff I ∞) (hF : aF.IsContMDiff I ∞)
        (hT : aT.IsContMDiff I ∞),
      letI := aE.totalSpaceTopology
      letI := aE.toFiberBundle
      letI := aE.toVectorBundle
      letI := aF.totalSpaceTopology
      letI := aF.toFiberBundle
      letI := aF.toVectorBundle
      letI := aT.totalSpaceTopology
      letI := aT.toFiberBundle
      letI := aT.toVectorBundle
      VectorBundle ℂ Vkd EK ∧ VectorBundle ℂ Vk FK ∧
      VectorBundle ℂ (Vk ⊗[ℂ] L) (fun x => FK x ⊗[ℂ] L) ∧
      (∀ x, Module.finrank ℂ (EK x) = k * d ∧ Module.finrank ℂ (FK x) = k) ∧
      aE.totalSpaceTopology = TopologicalSpace.induced
        (fun z : TotalSpace Vkd EK => (z.proj, (z.2 : Vn))) inferInstance ∧
      aF.totalSpaceTopology = TopologicalSpace.induced
        (fun z : TotalSpace Vk FK => (z.proj, (z.2 : Vn))) inferInstance ∧
      IsEmbedding (fun z : TotalSpace Vkd EK => (z.proj, (z.2 : Vn))) ∧
      IsEmbedding (fun z : TotalSpace Vk FK => (z.proj, (z.2 : Vn))) ∧
      ContMDiff (I.prod 𝓘(ℝ, Vkd)) (I.prod 𝓘(ℝ, Vn)) ∞
        (fun z : TotalSpace Vkd EK => (z.proj, (z.2 : Vn))) ∧
      ContMDiff (I.prod 𝓘(ℝ, Vk)) (I.prod 𝓘(ℝ, Vn)) ∞
        (fun z : TotalSpace Vk FK => (z.proj, (z.2 : Vn))) ∧
      (∀ x, (aT.pretrivializationAt x).baseSet = (aF.pretrivializationAt x).baseSet) ∧
      (∀ x y, y ∈ (aF.pretrivializationAt x).baseSet → ∀ (u : FK y) (w : L),
        (aT.pretrivializationAt x) ⟨y, u ⊗ₜ[ℂ] w⟩ =
          (y, ((aF.pretrivializationAt x) ⟨y, u⟩).2 ⊗ₜ[ℂ] w)) ∧
      ∃ (Theta : ∀ x, (FK x ⊗[ℂ] L) ≃ₗᵢ[ℂ] EK x)
        (back : ∀ x, Vn →ₗ[ℂ] (Fin d → FK x))
        (sigma sigmaInv : ∀ x, FK x →ₗ[ℂ] FK x),
        (∀ x (u : FK x) i, (Theta x (u ⊗ₜ[ℂ] EuclideanSpace.single i 1) : Vn) =
          (F x i v).toEuclideanLin u) ∧
        (∀ x (u : EK x), (Theta x).symm u =
          ∑ i, back x u i ⊗ₜ[ℂ] EuclideanSpace.single i 1) ∧
        (∀ x y i, (back x y i : Vn) = (F x v i).toEuclideanLin y) ∧
        (∀ x, LinearMap.adjoint (Theta x).toLinearMap = (Theta x).symm.toLinearMap) ∧
        (∀ x, (LinearMap.adjoint (ProjectionRange.rangeSubmodule P x).subtype).comp
          (ProjectionRange.rangeSubmodule P x).subtype = LinearMap.id) ∧
        (∀ x, (ProjectionRange.rangeSubmodule P x).subtype.comp
          (LinearMap.adjoint (ProjectionRange.rangeSubmodule P x).subtype) =
            (P x).toEuclideanLin) ∧
        (∀ x, (LinearMap.adjoint (ProjectionRange.rangeSubmodule (fun y => F y v v) x).subtype).comp
          (ProjectionRange.rangeSubmodule (fun y => F y v v) x).subtype = LinearMap.id) ∧
        (∀ x, (ProjectionRange.rangeSubmodule (fun y => F y v v) x).subtype.comp
          (LinearMap.adjoint (ProjectionRange.rangeSubmodule (fun y => F y v v) x).subtype) =
            (F x v v).toEuclideanLin) ∧
        ContMDiff (I.prod 𝓘(ℝ, Vk ⊗[ℂ] L)) (I.prod 𝓘(ℝ, Vkd)) ∞
          (fun z : TotalSpace (Vk ⊗[ℂ] L) (fun x => FK x ⊗[ℂ] L) =>
            (⟨z.proj, Theta z.proj z.2⟩ : TotalSpace Vkd EK)) ∧
        ContMDiff (I.prod 𝓘(ℝ, Vkd)) (I.prod 𝓘(ℝ, Vk ⊗[ℂ] L)) ∞
          (fun z : TotalSpace Vkd EK =>
            (⟨z.proj, (Theta z.proj).symm z.2⟩ :
              TotalSpace (Vk ⊗[ℂ] L) (fun x => FK x ⊗[ℂ] L))) ∧
        (∀ x (u : FK x), (sigma x u : Vn) = (Q x).toEuclideanLin u) ∧
        (∀ x (u : FK x), (sigmaInv x u : Vn) = (W x * W x).toEuclideanLin u) ∧
        ContMDiff (I.prod 𝓘(ℝ, Vk)) (I.prod 𝓘(ℝ, Vk)) ∞
          (fun z : TotalSpace Vk FK => (⟨z.proj, sigma z.proj z.2⟩ : TotalSpace Vk FK)) ∧
        ContMDiff (I.prod 𝓘(ℝ, Vk)) (I.prod 𝓘(ℝ, Vk)) ∞
          (fun z : TotalSpace Vk FK => (⟨z.proj, sigmaInv z.proj z.2⟩ : TotalSpace Vk FK)) ∧
        (∀ x, LinearMap.IsPositive (sigma x) ∧
          (∀ u : FK x, u ≠ 0 → 0 < (inner ℂ u (sigma x u)).re) ∧
          (sigma x).comp (sigmaInv x) = LinearMap.id ∧
          (sigmaInv x).comp (sigma x) = LinearMap.id ∧
          LinearMap.trace ℂ (FK x) (sigma x) = 1) ∧
        (∀ x z, (Q x).toEuclideanLin (Theta x z : Vn) =
          (Theta x (TensorProduct.map (sigma x) LinearMap.id z) : Vn)) ∧
        (∀ x T, let U := (ProjectionRange.rangeSubmodule P x).subtype.comp (Theta x).toLinearMap;
          (N x T).toEuclideanLin =
          (U.comp (TensorProduct.map (sigma x) T.toEuclideanLin)).comp (LinearMap.adjoint U)) := by
  classical
  intro v Q P W pi F EK FK L Vn Vk Vkd
  intro hQ hP hW hPstar hPidem hPrank hFsm hFstar hFidem hFrank
  let aE := ProjectionRange.prebundle hP hPstar hPidem hPrank
  let aF := ProjectionRange.prebundle (hFsm v v) (fun x => hFstar x v v) hFidem hFrank
  let aT := ProjectionRange.ActualTensor.prebundle (d := d) (hFsm v v)
    (fun x => hFstar x v v) hFidem hFrank
  refine ⟨aE, aF, aT, inferInstance, inferInstance, inferInstance, ?_⟩
  letI := aE.totalSpaceTopology
  letI := aE.toFiberBundle
  letI := aE.toVectorBundle
  letI := aF.totalSpaceTopology
  letI := aF.toFiberBundle
  letI := aF.toVectorBundle
  letI := aT.totalSpaceTopology
  letI := aT.toFiberBundle
  letI := aT.toVectorBundle
  refine ⟨(ProjectionRange.complexPrebundle hP hPstar hPidem hPrank).toVectorBundle,
    (ProjectionRange.complexPrebundle (hFsm v v) (fun x => hFstar x v v)
      hFidem hFrank).toVectorBundle,
    (ProjectionRange.ActualTensor.complexPrebundle (d := d) (hFsm v v)
      (fun x => hFstar x v v) hFidem hFrank).toVectorBundle,
    (fun x => ⟨ProjectionRange.finrank_fiber hP hPstar hPidem hPrank x,
      ProjectionRange.finrank_fiber (hFsm v v) (fun x => hFstar x v v)
        hFidem hFrank x⟩),
    ProjectionRange.totalTopology_eq_induced hP hPstar hPidem hPrank,
    ProjectionRange.totalTopology_eq_induced (hFsm v v) (fun x => hFstar x v v)
      hFidem hFrank,
    ProjectionRange.ambient_isEmbedding hP hPstar hPidem hPrank,
    ProjectionRange.ambient_isEmbedding (hFsm v v) (fun x => hFstar x v v) hFidem hFrank,
    ProjectionRange.smooth_ambient hP hPstar hPidem hPrank,
    ProjectionRange.smooth_ambient (hFsm v v) (fun x => hFstar x v v) hFidem hFrank,
    (fun x => rfl), (fun x y hy u w => rfl), ?_⟩
  letI := aE.contMDiffVectorBundle I (n := ∞)
  letI := aF.contMDiffVectorBundle I (n := ∞)
  letI := aT.contMDiffVectorBundle I (n := ∞)
  let EK := ProjectionRange.Fiber P
  let FK := ProjectionRange.Fiber (fun x => F x v v)
  let Vk := EuclideanSpace ℂ (Fin k)
  let Vkd := EuclideanSpace ℂ (Fin (k * d))
  have hwitness (x : B) : ∃ Theta : (FK x) ⊗[ℂ] L ≃ₗᵢ[ℂ] EK x,
    ∃ B : Vn →ₗ[ℂ] (Fin d → FK x),
    ∃ sigma sigmaInv : FK x →ₗ[ℂ] FK x,
    (∀ (w : FK x) (i : Fin d),
      (Theta (w ⊗ₜ[ℂ] EuclideanSpace.single i 1) : Vn) = (F x i v).toEuclideanLin w) ∧
    (∀ y : EK x, Theta.symm y = ∑ i, B y i ⊗ₜ[ℂ] EuclideanSpace.single i (1 : ℂ)) ∧
    (∀ (y : Vn) (i : Fin d), (B y i : Vn) = (F x v i).toEuclideanLin y) ∧
    (LinearMap.adjoint (𝕜 := ℂ) (E := (FK x) ⊗[ℂ] L) (F := EK x) Theta.toLinearMap) = Theta.symm.toLinearMap ∧
    (LinearMap.adjoint (𝕜 := ℂ) (E := EK x) (F := Vn) (ProjectionRange.rangeSubmodule P x).subtype).comp (ProjectionRange.rangeSubmodule P x).subtype = LinearMap.id ∧
    (ProjectionRange.rangeSubmodule P x).subtype.comp (LinearMap.adjoint (𝕜 := ℂ) (E := EK x) (F := Vn) (ProjectionRange.rangeSubmodule P x).subtype) = (P x).toEuclideanLin ∧
    (LinearMap.adjoint (𝕜 := ℂ) (E := FK x) (F := Vn) (ProjectionRange.rangeSubmodule (fun y => F y v v) x).subtype).comp (ProjectionRange.rangeSubmodule (fun y => F y v v) x).subtype = LinearMap.id ∧
    (ProjectionRange.rangeSubmodule (fun y => F y v v) x).subtype.comp (LinearMap.adjoint (𝕜 := ℂ) (E := FK x) (F := Vn) (ProjectionRange.rangeSubmodule (fun y => F y v v) x).subtype) = (F x v v).toEuclideanLin ∧
    (∀ w : FK x, (sigma w : Vn) = (Q x).toEuclideanLin w) ∧
    LinearMap.IsPositive (𝕜 := ℂ) (E := FK x) sigma ∧
    (∀ w : FK x, w ≠ 0 → 0 < (inner ℂ w (sigma w)).re) ∧
    sigma.comp sigmaInv = LinearMap.id ∧
    sigmaInv.comp sigma = LinearMap.id ∧
    LinearMap.trace ℂ (FK x) sigma = 1 ∧
    (∀ z : (FK x) ⊗[ℂ] L,
      (Q x).toEuclideanLin (Theta z : Vn) =
      (Theta (TensorProduct.map sigma LinearMap.id z) : Vn)) ∧
    (let U : (FK x) ⊗[ℂ] L →ₗ[ℂ] Vn :=
      (ProjectionRange.rangeSubmodule P x).subtype.comp Theta.toLinearMap
     ∀ T : Matrix (Fin d) (Fin d) ℂ,
       (N x T).toEuclideanLin =
       (U.comp (TensorProduct.map sigma T.toEuclideanLin)).comp (LinearMap.adjoint (𝕜 := ℂ) (E := (FK x) ⊗[ℂ] L) (F := Vn) U)) ∧
    (∀ w : FK x, (sigmaInv w : Vn) = (W x * W x).toEuclideanLin w) := by
    exact st37_actual_pointwise hd (N x) (hCP x) (hTP x) (hLeft x) v
  choose Theta back sigma sigmaInv hpoint using hwitness
  have htm := fun x => (hpoint x).1
  have hback := fun x => (hpoint x).2.1
  have hbackval := fun x => (hpoint x).2.2.1
  have hadj := fun x => (hpoint x).2.2.2.1
  have hEL := fun x => (hpoint x).2.2.2.2.1
  have hER := fun x => (hpoint x).2.2.2.2.2.1
  have hFL := fun x => (hpoint x).2.2.2.2.2.2.1
  have hFR := fun x => (hpoint x).2.2.2.2.2.2.2.1
  have hsig := fun x => (hpoint x).2.2.2.2.2.2.2.2.1
  have hpos := fun x => (hpoint x).2.2.2.2.2.2.2.2.2.1
  have hstrict := fun x => (hpoint x).2.2.2.2.2.2.2.2.2.2.1
  have hright := fun x => (hpoint x).2.2.2.2.2.2.2.2.2.2.2.1
  have hleft := fun x => (hpoint x).2.2.2.2.2.2.2.2.2.2.2.2.1
  have htrace := fun x => (hpoint x).2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hinter := fun x => (hpoint x).2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hfactor := fun x => (hpoint x).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hinv := fun x => (hpoint x).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hprojE : ContMDiff (I.prod 𝓘(ℝ, Vkd)) I ∞
      (fun z : TotalSpace Vkd EK => z.proj) := Bundle.contMDiff_proj EK (IB := I) (F := Vkd) (n := ∞)
  have hprojF : ContMDiff (I.prod 𝓘(ℝ, Vk)) I ∞
      (fun z : TotalSpace Vk FK => z.proj) := Bundle.contMDiff_proj FK (IB := I) (F := Vk) (n := ∞)
  have hprojT : ContMDiff (I.prod 𝓘(ℝ, Vk ⊗[ℂ] L)) I ∞
      (fun z : TotalSpace (Vk ⊗[ℂ] L) (fun x => FK x ⊗[ℂ] L) => z.proj) :=
    Bundle.contMDiff_proj (fun x => FK x ⊗[ℂ] L)
      (IB := I) (F := Vk ⊗[ℂ] L) (n := ∞)
  have hvalE : ContMDiff (I.prod 𝓘(ℝ, Vkd)) 𝓘(ℝ, Vn) ∞
      (fun z : TotalSpace Vkd EK => (z.2 : Vn)) :=
    (ProjectionRange.smooth_ambient hP hPstar hPidem hPrank).snd
  have hvalF : ContMDiff (I.prod 𝓘(ℝ, Vk)) 𝓘(ℝ, Vn) ∞
      (fun z : TotalSpace Vk FK => (z.2 : Vn)) :=
    (ProjectionRange.smooth_ambient (hFsm v v) (fun x => hFstar x v v) hFidem hFrank).snd
  have hforw : ContMDiff (I.prod 𝓘(ℝ, Vk ⊗[ℂ] L)) (I.prod 𝓘(ℝ, Vkd)) ∞
      (fun z : TotalSpace (Vk ⊗[ℂ] L) (fun x => FK x ⊗[ℂ] L) =>
        (⟨z.proj, Theta z.proj z.2⟩ : TotalSpace Vkd EK)) := by
    refine ProjectionRange.smooth_range_lift (I := I)
      (IM := I.prod 𝓘(ℝ, Vk ⊗[ℂ] L)) (p := P) (r := k * d)
      hP hPstar hPidem hPrank
      (fun z : TotalSpace (Vk ⊗[ℂ] L) (fun x => FK x ⊗[ℂ] L) => z.proj)
      (fun z => Theta z.proj z.2) hprojT ?_
    have hs : ContMDiff (I.prod 𝓘(ℝ, Vk ⊗[ℂ] L)) 𝓘(ℝ, Vn) ∞
        (fun z : TotalSpace (Vk ⊗[ℂ] L) (fun x => FK x ⊗[ℂ] L) =>
          ∑ i, (F z.proj i v).toEuclideanLin
            (ProjectionRange.ActualTensor.coefficients (FK z.proj) d z.2 i : Vn)) := by
      apply ContMDiff.sum
      intro i hi
      have hm := ((ProjectionRange.matrixRealCLM n n).contDiff.comp_contMDiff
        (hFsm i v)).comp hprojT
      exact hm.clm_apply (ProjectionRange.ActualTensor.smooth_coefficient
        (hFsm v v) (fun x => hFstar x v v) hFidem hFrank i)
    convert hs using 1
    funext z
    conv_lhs => rw [ProjectionRange.ActualTensor.coefficients_expand (FK z.proj) z.2]
    simp only [map_sum]
    change (ProjectionRange.rangeSubmodule P z.proj).subtype
      (∑ i, Theta z.proj
        (ProjectionRange.ActualTensor.coefficients (FK z.proj) d z.2 i ⊗ₜ[ℂ]
          EuclideanSpace.single i (1 : ℂ))) = _
    rw [map_sum]
    exact Finset.sum_congr rfl (fun i _ => htm z.proj _ i)
  have hbacksm : ContMDiff (I.prod 𝓘(ℝ, Vkd)) (I.prod 𝓘(ℝ, Vk ⊗[ℂ] L)) ∞
      (fun z : TotalSpace Vkd EK =>
        (⟨z.proj, (Theta z.proj).symm z.2⟩ :
          TotalSpace (Vk ⊗[ℂ] L) (fun x => FK x ⊗[ℂ] L))) := by
    have hs := ProjectionRange.ActualTensor.smooth_tensor_sum
      (IM := I.prod 𝓘(ℝ, Vkd)) (d := d) (hFsm v v) (fun x => hFstar x v v) hFidem hFrank
      (fun z : TotalSpace Vkd EK => z.proj)
      (fun i z => back z.proj z.2 i) hprojE
      (fun i => by
        have hm := ((ProjectionRange.matrixRealCLM n n).contDiff.comp_contMDiff
          (hFsm v i)).comp hprojE
        convert hm.clm_apply hvalE using 1
        funext z
        exact hbackval z.proj z.2 i)
    simpa only [hback] using hs
  have hsigsm : ContMDiff (I.prod 𝓘(ℝ, Vk)) (I.prod 𝓘(ℝ, Vk)) ∞
      (fun z : TotalSpace Vk FK => (⟨z.proj, sigma z.proj z.2⟩ : TotalSpace Vk FK)) := by
    refine ProjectionRange.smooth_range_lift (I := I) (IM := I.prod 𝓘(ℝ, Vk))
      (p := fun x => F x v v) (r := k) (hFsm v v) (fun x => hFstar x v v)
      hFidem hFrank (fun z : TotalSpace Vk FK => z.proj)
      (fun z => sigma z.proj z.2) hprojF ?_
    have hm := ((ProjectionRange.matrixRealCLM n n).contDiff.comp_contMDiff hQ).comp hprojF
    convert hm.clm_apply hvalF using 1
    funext z
    exact hsig z.proj z.2
  have hW2 : ContMDiff I 𝓘(ℝ, Matrix (Fin n) (Fin n) ℂ) ∞
      (fun x => W x * W x) := fun x => ProjectionRange.smooth_mul (hW x) (hW x)
  have hinvsm : ContMDiff (I.prod 𝓘(ℝ, Vk)) (I.prod 𝓘(ℝ, Vk)) ∞
      (fun z : TotalSpace Vk FK => (⟨z.proj, sigmaInv z.proj z.2⟩ : TotalSpace Vk FK)) := by
    refine ProjectionRange.smooth_range_lift (I := I) (IM := I.prod 𝓘(ℝ, Vk))
      (p := fun x => F x v v) (r := k) (hFsm v v) (fun x => hFstar x v v)
      hFidem hFrank (fun z : TotalSpace Vk FK => z.proj)
      (fun z => sigmaInv z.proj z.2) hprojF ?_
    have hm := ((ProjectionRange.matrixRealCLM n n).contDiff.comp_contMDiff hW2).comp hprojF
    convert hm.clm_apply hvalF using 1
    funext z
    exact hinv z.proj z.2
  exact ⟨Theta, back, sigma, sigmaInv, htm, hback, hbackval, hadj,
    hEL, hER, hFL, hFR, hforw, hbacksm, hsig, hinv, hsigsm, hinvsm,
    (fun x => ⟨hpos x, hstrict x, hright x, hleft x, htrace x⟩), hinter, hfactor⟩

set_option maxHeartbeats 3000000 in -- Canonical structures; original ceiling.
theorem whole_original_ST37
    {E H B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] [TopologicalSpace B] [ChartedSpace H B] [CompactSpace B]
    (I : ModelWithCorners ℝ E H) [IsManifold I ∞ B]
    {d n k : ℕ} (hd : 0 < d)
    (N : B → (Matrix (Fin d) (Fin d) ℂ →L[ℂ] Matrix (Fin n) (Fin n) ℂ))
    (hN : ContMDiff I 𝓘(ℝ, Matrix (Fin d) (Fin d) ℂ →L[ℂ]
      Matrix (Fin n) (Fin n) ℂ) ∞ N)
    (hCP : ∀ x, MatrixMap.IsCompletelyPositive (N x).toLinearMap)
    (hTP : ∀ x X, Matrix.trace (N x X) = Matrix.trace X)
    (hLeft : ∀ x, ∃ R : MatrixMap (Fin n) (Fin d) ℂ,
      R.IsCompletelyPositive ∧ (∀ X, Matrix.trace (R X) = Matrix.trace X) ∧
      ∀ X, R (N x X) = X)
    (hRank : ∀ x, (N x 1).rank = k * d) :
    let v : Fin d := ⟨0, hd⟩
    let Q := fun x => N x 1
    let P := fun x => spectralSupport (Q x)
    let W := fun x => spectralInverseSqrt (Q x)
    let pi := fun x A => W x * N x A * W x
    let F := fun x i j => pi x (Matrix.single i j 1)
    let EK := ProjectionRange.Fiber P
    let FK := ProjectionRange.Fiber (fun x => F x v v)
    let L := EuclideanSpace ℂ (Fin d)
    let Vn := EuclideanSpace ℂ (Fin n)
    let Vk := EuclideanSpace ℂ (Fin k)
    let Vkd := EuclideanSpace ℂ (Fin (k * d))
    let Env := EuclideanSpace ℂ (Fin d × Fin n)
    let J := fun x => inputChoi (N x).toLinearMap
    let A := fun x mu => sqrtColumn (N x).toLinearMap mu
    let reset := fun x b => Matrix.single v b (1 : ℂ) * (1 - P x)
    let Kdec := fun x => Sum.elim (decoderKraus (F x) v) (reset x)
    let D := fun x => MatrixMap.of_kraus (Kdec x) (Kdec x)
    letI : NormedAddCommGroup (Vk ⊗[ℂ] L) := TensorProduct.instNormedAddCommGroup
    letI : InnerProductSpace ℂ (Vk ⊗[ℂ] L) := TensorProduct.instInnerProductSpace
    letI : ∀ x, NormedAddCommGroup (FK x ⊗[ℂ] L) := fun _ =>
      TensorProduct.instNormedAddCommGroup
    letI : ∀ x, InnerProductSpace ℂ (FK x ⊗[ℂ] L) := fun _ =>
      TensorProduct.instInnerProductSpace
    letI : NormedAddCommGroup (Vn ⊗[ℂ] Env) := TensorProduct.instNormedAddCommGroup
    letI : InnerProductSpace ℂ (Vn ⊗[ℂ] Env) := TensorProduct.instInnerProductSpace
    ContMDiff I 𝓘(ℝ, Matrix (Fin n) (Fin n) ℂ) ∞ Q ∧
    ContMDiff I 𝓘(ℝ, Matrix (Fin n) (Fin n) ℂ) ∞ P ∧
    ContMDiff I 𝓘(ℝ, Matrix (Fin n) (Fin n) ℂ) ∞ W ∧
    ContMDiff (I.prod 𝓘(ℝ, Matrix (Fin d) (Fin d) ℂ))
      𝓘(ℝ, Matrix (Fin n) (Fin n) ℂ) ∞ (fun z : B × Matrix (Fin d) (Fin d) ℂ => pi z.1 z.2) ∧
    (∀ x, pi x 1 = P x ∧
      (∀ T, (pi x T)ᴴ = pi x Tᴴ) ∧
      (∀ T U, pi x T * pi x U = pi x (T * U)) ∧
      (∀ T, Q x * pi x T = pi x T * Q x) ∧
      (∀ T, N x T = Q x * pi x T)) ∧
    (∀ b, ContMDiff I 𝓘(ℝ, Matrix (Fin d) (Fin n) ℂ) ∞
      (fun x => decoderKraus (F x) v b)) ∧
    (∀ b, ContMDiff I 𝓘(ℝ, Matrix (Fin d) (Fin n) ℂ) ∞ (fun x => reset x b)) ∧
    ContMDiff (I.prod 𝓘(ℝ, Matrix (Fin n) (Fin n) ℂ))
      𝓘(ℝ, Matrix (Fin d) (Fin d) ℂ) ∞ (fun z : B × Matrix (Fin n) (Fin n) ℂ => D z.1 z.2) ∧
    (∀ x, (D x).IsCompletelyPositive ∧
      (∀ X, Matrix.trace (D x X) = Matrix.trace X) ∧
      (∀ T, D x (N x T) = T) ∧
      (∀ (q : ℕ) (X : Matrix (Fin d × Fin q) (Fin d × Fin q) ℂ),
        MatrixMap.kron (D x) LinearMap.id
          (MatrixMap.kron (N x).toLinearMap LinearMap.id X) = X) ∧
      (∀ X i j, D x X i j = Matrix.trace (F x j i * X) +
        Matrix.trace ((1 - P x) * X) * Matrix.single v v (1 : ℂ) i j) ∧
      (∀ X i j, D x X i j = Matrix.trace
        (N x (Matrix.single j i 1) * (W x * X * W x)) +
        Matrix.trace ((1 - P x) * X) * Matrix.single v v (1 : ℂ) i j)) ∧
    (∃ (aE : VectorPrebundle ℝ Vkd EK) (aF : VectorPrebundle ℝ Vk FK)
        (aT : VectorPrebundle ℝ (Vk ⊗[ℂ] L) (fun x => FK x ⊗[ℂ] L))
        (hE : aE.IsContMDiff I ∞) (hF : aF.IsContMDiff I ∞)
        (hT : aT.IsContMDiff I ∞),
      letI := aE.totalSpaceTopology
      letI := aE.toFiberBundle
      letI := aE.toVectorBundle
      letI := aF.totalSpaceTopology
      letI := aF.toFiberBundle
      letI := aF.toVectorBundle
      letI := aT.totalSpaceTopology
      letI := aT.toFiberBundle
      letI := aT.toVectorBundle
      VectorBundle ℂ Vkd EK ∧ VectorBundle ℂ Vk FK ∧
      VectorBundle ℂ (Vk ⊗[ℂ] L) (fun x => FK x ⊗[ℂ] L) ∧
      (∀ x, Module.finrank ℂ (EK x) = k * d ∧ Module.finrank ℂ (FK x) = k) ∧
      aE.totalSpaceTopology = TopologicalSpace.induced
        (fun z : TotalSpace Vkd EK => (z.proj, (z.2 : Vn))) inferInstance ∧
      aF.totalSpaceTopology = TopologicalSpace.induced
        (fun z : TotalSpace Vk FK => (z.proj, (z.2 : Vn))) inferInstance ∧
      IsEmbedding (fun z : TotalSpace Vkd EK => (z.proj, (z.2 : Vn))) ∧
      IsEmbedding (fun z : TotalSpace Vk FK => (z.proj, (z.2 : Vn))) ∧
      ContMDiff (I.prod 𝓘(ℝ, Vkd)) (I.prod 𝓘(ℝ, Vn)) ∞
        (fun z : TotalSpace Vkd EK => (z.proj, (z.2 : Vn))) ∧
      ContMDiff (I.prod 𝓘(ℝ, Vk)) (I.prod 𝓘(ℝ, Vn)) ∞
        (fun z : TotalSpace Vk FK => (z.proj, (z.2 : Vn))) ∧
      (∀ x, (aT.pretrivializationAt x).baseSet = (aF.pretrivializationAt x).baseSet) ∧
      (∀ x y, y ∈ (aF.pretrivializationAt x).baseSet → ∀ (u : FK y) (w : L),
        (aT.pretrivializationAt x) ⟨y, u ⊗ₜ[ℂ] w⟩ =
          (y, ((aF.pretrivializationAt x) ⟨y, u⟩).2 ⊗ₜ[ℂ] w)) ∧
      ∃ (Theta : ∀ x, (FK x ⊗[ℂ] L) ≃ₗᵢ[ℂ] EK x)
        (back : ∀ x, Vn →ₗ[ℂ] (Fin d → FK x))
        (sigma sigmaInv : ∀ x, FK x →ₗ[ℂ] FK x),
        (∀ x (u : FK x) i, (Theta x (u ⊗ₜ[ℂ] EuclideanSpace.single i 1) : Vn) =
          (F x i v).toEuclideanLin u) ∧
        (∀ x (u : EK x), (Theta x).symm u =
          ∑ i, back x u i ⊗ₜ[ℂ] EuclideanSpace.single i 1) ∧
        (∀ x y i, (back x y i : Vn) = (F x v i).toEuclideanLin y) ∧
        (∀ x, LinearMap.adjoint (Theta x).toLinearMap = (Theta x).symm.toLinearMap) ∧
        (∀ x, (LinearMap.adjoint (ProjectionRange.rangeSubmodule P x).subtype).comp
          (ProjectionRange.rangeSubmodule P x).subtype = LinearMap.id) ∧
        (∀ x, (ProjectionRange.rangeSubmodule P x).subtype.comp
          (LinearMap.adjoint (ProjectionRange.rangeSubmodule P x).subtype) =
            (P x).toEuclideanLin) ∧
        (∀ x, (LinearMap.adjoint (ProjectionRange.rangeSubmodule (fun y => F y v v) x).subtype).comp
          (ProjectionRange.rangeSubmodule (fun y => F y v v) x).subtype = LinearMap.id) ∧
        (∀ x, (ProjectionRange.rangeSubmodule (fun y => F y v v) x).subtype.comp
          (LinearMap.adjoint (ProjectionRange.rangeSubmodule (fun y => F y v v) x).subtype) =
            (F x v v).toEuclideanLin) ∧
        ContMDiff (I.prod 𝓘(ℝ, Vk ⊗[ℂ] L)) (I.prod 𝓘(ℝ, Vkd)) ∞
          (fun z : TotalSpace (Vk ⊗[ℂ] L) (fun x => FK x ⊗[ℂ] L) =>
            (⟨z.proj, Theta z.proj z.2⟩ : TotalSpace Vkd EK)) ∧
        ContMDiff (I.prod 𝓘(ℝ, Vkd)) (I.prod 𝓘(ℝ, Vk ⊗[ℂ] L)) ∞
          (fun z : TotalSpace Vkd EK =>
            (⟨z.proj, (Theta z.proj).symm z.2⟩ :
              TotalSpace (Vk ⊗[ℂ] L) (fun x => FK x ⊗[ℂ] L))) ∧
        (∀ x (u : FK x), (sigma x u : Vn) = (Q x).toEuclideanLin u) ∧
        (∀ x (u : FK x), (sigmaInv x u : Vn) = (W x * W x).toEuclideanLin u) ∧
        ContMDiff (I.prod 𝓘(ℝ, Vk)) (I.prod 𝓘(ℝ, Vk)) ∞
          (fun z : TotalSpace Vk FK => (⟨z.proj, sigma z.proj z.2⟩ : TotalSpace Vk FK)) ∧
        ContMDiff (I.prod 𝓘(ℝ, Vk)) (I.prod 𝓘(ℝ, Vk)) ∞
          (fun z : TotalSpace Vk FK => (⟨z.proj, sigmaInv z.proj z.2⟩ : TotalSpace Vk FK)) ∧
        (∀ x, LinearMap.IsPositive (sigma x) ∧
          (∀ u : FK x, u ≠ 0 → 0 < (inner ℂ u (sigma x u)).re) ∧
          (sigma x).comp (sigmaInv x) = LinearMap.id ∧
          (sigmaInv x).comp (sigma x) = LinearMap.id ∧
          LinearMap.trace ℂ (FK x) (sigma x) = 1) ∧
        (∀ x z, (Q x).toEuclideanLin (Theta x z : Vn) =
          (Theta x (TensorProduct.map (sigma x) LinearMap.id z) : Vn)) ∧
        (∀ x T, let U := (ProjectionRange.rangeSubmodule P x).subtype.comp (Theta x).toLinearMap;
          (N x T).toEuclideanLin =
          (U.comp (TensorProduct.map (sigma x) T.toEuclideanLin)).comp (LinearMap.adjoint U))) ∧
    ContMDiff I 𝓘(ℝ, Matrix (Fin d × Fin n) (Fin d × Fin n) ℂ) ∞ J ∧
    (∀ x, (J x).PosSemidef ∧ (J x).rank = k ∧
      J x = (MatrixMap.choi_matrix (N x).toLinearMap).submatrix Prod.swap Prod.swap) ∧
    ContMDiff I 𝓘(ℝ, Matrix (Fin d × Fin n) (Fin d × Fin n) ℂ) ∞
      (fun x => CFC.sqrt (J x)) ∧
    (∀ mu, ContMDiff I 𝓘(ℝ, Matrix (Fin n) (Fin d) ℂ) ∞ (fun x => A x mu)) ∧
    (∀ x T, N x T = ∑ mu, A x mu * T * (A x mu)ᴴ) ∧
    (∀ x, (∑ mu, (A x mu)ᴴ * A x mu) = 1) ∧
    (∃ V : B → (L →ₗᵢ[ℂ] Vn ⊗[ℂ] Env),
      (∀ x u, V x u = ∑ mu, (A x mu).toEuclideanLin u ⊗ₜ[ℂ] EuclideanSpace.single mu 1) ∧
      ContMDiff (I.prod 𝓘(ℝ, L)) 𝓘(ℝ, Vn ⊗[ℂ] Env) ∞ (fun z : B × L => V z.1 z.2) ∧
      (∀ x T a b, N x T a b = ∑ mu, ∑ i, ∑ j,
        inner ℂ (EuclideanSpace.single a 1 ⊗ₜ[ℂ] EuclideanSpace.single mu 1)
          (V x (EuclideanSpace.single i 1)) * T i j *
        star (inner ℂ (EuclideanSpace.single b 1 ⊗ₜ[ℂ] EuclideanSpace.single mu 1)
          (V x (EuclideanSpace.single j 1))))) := by
  trace "ST37: explicit spectral interface whole proof entered"
  classical

  have hNr : ContMDiff I 𝓘(ℝ, Matrix (Fin d) (Fin d) ℂ →L[ℝ]
      Matrix (Fin n) (Fin n) ℂ) ∞ (fun x => (N x).restrictScalars ℝ) := (ContinuousLinearMap.restrictScalarsIsometry ℂ
    (Matrix (Fin d) (Fin d) ℂ) (Matrix (Fin n) (Fin n) ℂ) ℝ ℝ).toContinuousLinearMap.contDiff.comp_contMDiff hN
  have hQ : ContMDiff I 𝓘(ℝ, Matrix (Fin n) (Fin n) ℂ) ∞ (fun x => N x 1) :=
    hNr.clm_apply contMDiff_const
  have hN_apply (x : B) (T : Matrix (Fin d) (Fin d) ℂ) :
      (N x).toLinearMap T = N x T := rfl
  have hPSD (x : B) : (N x 1).PosSemidef := by
    obtain ⟨K, hK⟩ := MatrixMap.IsCompletelyPositive.exists_kraus (N x).toLinearMap (hCP x)
    have he : N x 1 = ∑ a, K a * (K a)ᴴ := by
      simpa [MatrixMap.of_kraus, Matrix.mul_one] using
        congrArg (fun f : MatrixMap (Fin d) (Fin n) ℂ => f 1) hK
    rw [he]
    exact Matrix.nonneg_iff_posSemidef.mp
      (Finset.sum_nonneg fun a _ => (Matrix.posSemidef_self_mul_conjTranspose (K a)).nonneg)
  obtain ⟨hP, hW, hS⟩ := actual_constant_rank_whitening_smooth I (fun x => N x 1) hQ hPSD hRank
  have hAct : ContMDiff (I.prod 𝓘(ℝ, Matrix (Fin d) (Fin d) ℂ))
      𝓘(ℝ, Matrix (Fin n) (Fin n) ℂ) ∞
      (fun z : B × Matrix (Fin d) (Fin d) ℂ => N z.1 z.2) :=
    (hNr.comp contMDiff_fst).clm_apply contMDiff_snd
  have hWp : ContMDiff (I.prod 𝓘(ℝ, Matrix (Fin d) (Fin d) ℂ))
      𝓘(ℝ, Matrix (Fin n) (Fin n) ℂ) ∞
      (fun z : B × Matrix (Fin d) (Fin d) ℂ => spectralInverseSqrt (N z.1 1)) :=
    hW.comp contMDiff_fst
  have hpi : ContMDiff (I.prod 𝓘(ℝ, Matrix (Fin d) (Fin d) ℂ))
      𝓘(ℝ, Matrix (Fin n) (Fin n) ℂ) ∞
      (fun z : B × Matrix (Fin d) (Fin d) ℂ => spectralInverseSqrt (N z.1 1) * N z.1 z.2 * spectralInverseSqrt (N z.1 1)) := by
    intro z
    exact ProjectionRange.smooth_mul (ProjectionRange.smooth_mul (hWp z) (hAct z)) (hWp z)
  let v : Fin d := ⟨0, hd⟩
  let Q : B → Matrix (Fin n) (Fin n) ℂ := fun x => N x 1
  let P : B → Matrix (Fin n) (Fin n) ℂ := fun x => spectralSupport (Q x)
  let W : B → Matrix (Fin n) (Fin n) ℂ := fun x => spectralInverseSqrt (Q x)
  let pi : B → Matrix (Fin d) (Fin d) ℂ → Matrix (Fin n) (Fin n) ℂ :=
    fun x T => W x * N x T * W x
  let F : B → Fin d → Fin d → Matrix (Fin n) (Fin n) ℂ :=
    fun x i j => pi x (Matrix.single i j 1)
  have hpi_bridge (x : B) (T : Matrix (Fin d) (Fin d) ℂ) :
      pi x T = W x * (N x).toLinearMap T * W x := rfl
  have hAlg (x : B) : pi x 1 = P x ∧
      (∀ T, (pi x T)ᴴ = pi x Tᴴ) ∧
      (∀ T U, pi x T * pi x U = pi x (T * U)) ∧
      (∀ T, Q x * pi x T = pi x T * Q x) ∧
      (∀ T, N x T = Q x * pi x T) :=
    by
      have hs := actual_cptp_left_inverse_spectral_algebra hd
        (N x).toLinearMap (hCP x) (hTP x) (hLeft x)
      simpa only [hpi_bridge, W, P, Q, hN_apply] using hs
  have hPstar (x) : (P x)ᴴ = P x := (support_range (Q x) (hPSD x)).2.1.eq
  have hPidem (x) : P x * P x = P x := (support_range (Q x) (hPSD x)).2.2
  have hPrank (x) : (P x).rank = k * d := by
    have hr (T : Matrix (Fin n) (Fin n) ℂ) :
        T.rank = Module.finrank ℂ (LinearMap.range T.toEuclideanLin) := by
      rw [Matrix.toEuclideanLin_eq_toLin_orthonormal]
      exact Matrix.rank_eq_finrank_range_toLin T _ _
    rw [hr, (support_range (Q x) (hPSD x)).1, ← hr]
    exact hRank x
  have hFsm (i j : Fin d) : ContMDiff I
      𝓘(ℝ, Matrix (Fin n) (Fin n) ℂ) ∞ (fun x => F x i j) :=
    st37_matrix_unit_slice I pi hpi i j
  have hFstar (x) (i j : Fin d) : (F x i j)ᴴ = F x j i := by
    simpa only [F, pi, Matrix.conjTranspose_single, star_one] using
      (hAlg x).2.1 (Matrix.single i j 1)
  have hFmul (x) (i j a b : Fin d) :
      F x i j * F x a b = if j = a then F x i b else 0 := by
    have hh := (hAlg x).2.2.1 (Matrix.single i j 1) (Matrix.single a b 1)
    by_cases hj : j = a
    · subst a
      simpa only [F, pi, Matrix.single_mul_single_same, one_mul, ite_true] using hh
    · have hz : Matrix.single i j (1 : ℂ) * Matrix.single a b (1 : ℂ) = 0 :=
        Matrix.single_mul_single_of_ne (c := (1 : ℂ)) (i := i) (j := j)
          (k := a) (h := hj) (d := (1 : ℂ))
      simpa only [F, pi, hz, map_zero, Matrix.mul_zero,
        Matrix.zero_mul, if_neg hj] using hh
  have hFidem (x) : F x v v * F x v v = F x v v := by simpa using hFmul x v v v v
  have hFrank (x) : (F x v v).rank = k :=
    actual_cptp_left_inverse_syndrome_rank hd (N x).toLinearMap
      (hCP x) (hTP x) (hLeft x) (hPrank x)
  have hDecK (b : Fin n) : ContMDiff I 𝓘(ℝ, Matrix (Fin d) (Fin n) ℂ) ∞
      (fun x => decoderKraus (F x) v b) := by
    apply contMDiff_pi_space.mpr
    intro i
    apply contMDiff_pi_space.mpr
    intro c
    exact contMDiff_pi_space.mp (contMDiff_pi_space.mp (hFsm v i) b) c
  have hReset (b : Fin n) : ContMDiff I 𝓘(ℝ, Matrix (Fin d) (Fin n) ℂ) ∞
      (fun x => Matrix.single v b (1 : ℂ) * (1 - P x)) := by
    intro x
    exact ProjectionRange.smooth_mul contMDiffAt_const
      ((contMDiff_const.sub hP) x)
  let KK : B → (Fin n ⊕ Fin n) → Matrix (Fin d) (Fin n) ℂ := fun x => Sum.elim (decoderKraus (F x) v)
    (fun b => Matrix.single v b (1 : ℂ) * (1 - P x))
  have hKK (b : Fin n ⊕ Fin n) :
      ContMDiff I 𝓘(ℝ, Matrix (Fin d) (Fin n) ℂ) ∞ (fun x => KK x b) := by
    cases b with
    | inl b => exact hDecK b
    | inr b => exact hReset b
  have hDsm : ContMDiff (I.prod 𝓘(ℝ, Matrix (Fin n) (Fin n) ℂ))
      𝓘(ℝ, Matrix (Fin d) (Fin d) ℂ) ∞
      (fun z : B × Matrix (Fin n) (Fin n) ℂ =>
        MatrixMap.of_kraus (KK z.1) (KK z.1) z.2) := by
    have hKs (b : Fin n ⊕ Fin n) :
        ContMDiff (I.prod 𝓘(ℝ, Matrix (Fin n) (Fin n) ℂ))
          𝓘(ℝ, Matrix (Fin d) (Fin n) ℂ) ∞
          (fun z : B × Matrix (Fin n) (Fin n) ℂ => KK z.1 b) :=
      (hKK b).comp contMDiff_fst
    have hs : ContMDiff (I.prod 𝓘(ℝ, Matrix (Fin n) (Fin n) ℂ))
        𝓘(ℝ, Matrix (Fin d) (Fin d) ℂ) ∞
        (fun z : B × Matrix (Fin n) (Fin n) ℂ =>
          ∑ b, KK z.1 b * z.2 * (KK z.1 b)ᴴ) := by
      apply ContMDiff.sum
      intro b hb z
      exact ProjectionRange.smooth_mul
        (ProjectionRange.smooth_mul (hKs b z) contMDiffAt_snd)
        (ProjectionRange.smooth_adj (hKs b z))
    simpa only [MatrixMap.of_kraus, LinearMap.sum_apply, LinearMap.coe_mk,
      AddHom.coe_mk] using hs
  have hFsum (x : B) : (∑ i, F x i i) = P x := by
    calc
      _ = W x * N x (∑ i, Matrix.single i i 1) * W x := by
        simp only [F, pi, map_sum, Matrix.mul_sum, Matrix.sum_mul]
      _ = P x := by rw [Matrix.sum_single_one]; exact (hAlg x).1
  have hDtrace (x : B) (X : Matrix (Fin n) (Fin n) ℂ) (i j : Fin d) :
      MatrixMap.of_kraus (KK x) (KK x) X i j =
        Matrix.trace (F x j i * X) + Matrix.trace ((1 - P x) * X) *
          Matrix.single v v (1 : ℂ) i j := by
    have hh := congrArg (fun M : Matrix (Fin d) (Fin d) ℂ => M i j)
      (D5.S3.Quantum.Recovery.KrausCompletion.complete_kraus_action
        (decoderKraus (F x) v) (P x) v (hPstar x) (hPidem x) X)
    have hKcomplete :
        D5.S3.Quantum.Recovery.KrausCompletion.completeKraus
          (decoderKraus (F x) v) (P x) v = KK x := by
      funext b
      cases b <;> rfl
    rw [hKcomplete] at hh
    simpa only [MatrixMap.of_kraus, LinearMap.sum_apply, LinearMap.coe_mk,
      AddHom.coe_mk, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
      decoder_trace_pairing (F x) (hFmul x) (hFstar x) v X i j] using hh
  have hDtranspose (x : B) (X : Matrix (Fin n) (Fin n) ℂ) (i j : Fin d) :
      MatrixMap.of_kraus (KK x) (KK x) X i j =
        Matrix.trace (N x (Matrix.single j i 1) * (W x * X * W x)) +
          Matrix.trace ((1 - P x) * X) * Matrix.single v v (1 : ℂ) i j := by
    rw [hDtrace]
    congr 1
    calc
      Matrix.trace (F x j i * X) =
        Matrix.trace (W x * (N x (Matrix.single j i 1) * (W x * X))) := by
          simp only [F, pi, Matrix.mul_assoc]
      _ = Matrix.trace ((N x (Matrix.single j i 1) * (W x * X)) * W x) :=
        Matrix.trace_mul_comm _ _
      _ = _ := by simp only [Matrix.mul_assoc]
  have hDTP (x : B) (X : Matrix (Fin n) (Fin n) ℂ) :
      Matrix.trace (MatrixMap.of_kraus (KK x) (KK x) X) = Matrix.trace X := by
    change (∑ i, MatrixMap.of_kraus (KK x) (KK x) X i i) = Matrix.trace X
    simp_rw [hDtrace]
    rw [Finset.sum_add_distrib]
    have hr : (∑ i : Fin d, Matrix.trace ((1 - P x) * X) *
        Matrix.single v v (1 : ℂ) i i) = Matrix.trace ((1 - P x) * X) := by
      simp [Matrix.single, Matrix.of_apply]
    rw [hr, ← Matrix.trace_sum, ← Matrix.sum_mul, hFsum, ← Matrix.trace_add,
      ← Matrix.add_mul, add_sub_cancel, Matrix.one_mul]
  have hDrec (x : B) (T : Matrix (Fin d) (Fin d) ℂ) :
      MatrixMap.of_kraus (KK x) (KK x) (N x T) = T := by
    have hQP : Q x * P x = Q x := by
      have hh := (hAlg x).2.2.2.2 (1 : Matrix (Fin d) (Fin d) ℂ)
      change Q x = Q x * pi x 1 at hh
      rw [(hAlg x).1] at hh
      exact hh.symm
    have hPQ : P x * Q x = Q x := by
      have hh := congrArg Matrix.conjTranspose hQP
      have hQstar : (Q x)ᴴ = Q x := (hPSD x).isHermitian.eq
      simpa only [Matrix.conjTranspose_mul, hPstar x, hQstar] using hh
    have hzero : (1 - P x) * N x T = 0 := by
      calc
        (1 - P x) * N x T = (1 - P x) * (Q x * pi x T) :=
          congrArg (fun Y => (1 - P x) * Y) ((hAlg x).2.2.2.2 T)
        _ = ((1 - P x) * Q x) * pi x T := (Matrix.mul_assoc _ _ _).symm
        _ = 0 := by
          rw [Matrix.sub_mul, Matrix.one_mul, hPQ, sub_self, Matrix.zero_mul]
    have hpair (i j : Fin d) : F x j i * N x T =
        N x (Matrix.single j i 1 * T) := by
      calc
        _ = F x j i * (Q x * pi x T) := by rw [(hAlg x).2.2.2.2 T]
        _ = Q x * (F x j i * pi x T) := by
          rw [← Matrix.mul_assoc, ← (hAlg x).2.2.2.1 (Matrix.single j i 1),
            Matrix.mul_assoc]
        _ = Q x * pi x (Matrix.single j i 1 * T) := by
          rw [show F x j i * pi x T = pi x (Matrix.single j i 1 * T) from
            (hAlg x).2.2.1 (Matrix.single j i 1) T]
        _ = _ := ((hAlg x).2.2.2.2 _).symm
    ext i j
    rw [hDtrace, hzero, Matrix.trace_zero, zero_mul, add_zero, hpair, hTP]
    simp only [Matrix.trace_single_mul, one_smul]
  have hDref (x : B) (q : ℕ)
      (X : Matrix (Fin d × Fin q) (Fin d × Fin q) ℂ) :
      MatrixMap.kron (MatrixMap.of_kraus (KK x) (KK x)) LinearMap.id
        (MatrixMap.kron (N x).toLinearMap LinearMap.id X) = X := by
    ext ⟨i,u⟩ ⟨j,w⟩
    rw [D5.S3.Quantum.QuantumChannels.IptPptSquaredEquivalence.kron_id_apply]
    have hh : (fun a b => MatrixMap.kron (N x).toLinearMap LinearMap.id X
        (a,u) (b,w)) = N x (fun a b => X (a,u) (b,w)) := by
      ext a b
      exact D5.S3.Quantum.QuantumChannels.IptPptSquaredEquivalence.kron_id_apply
        (N x).toLinearMap q X (a,u) (b,w)
    rw [hh]
    exact congrArg (fun M : Matrix (Fin d) (Fin d) ℂ => M i j)
      (hDrec x (fun a b => X (a,u) (b,w)))
  have hJsm : ContMDiff I 𝓘(ℝ, Matrix (Fin d × Fin n) (Fin d × Fin n) ℂ) ∞
      (fun x => inputChoi (N x).toLinearMap) := by
    apply contMDiff_pi_space.mpr
    intro a
    apply contMDiff_pi_space.mpr
    intro b
    exact contMDiff_pi_space.mp (contMDiff_pi_space.mp
      (hNr.clm_apply (contMDiff_const (c := Matrix.single a.1 b.1 1))) a.2) b.2
  have hJrank (x : B) : (inputChoi (N x).toLinearMap).rank = k :=
    actual_inputChoi_rank hd (N x).toLinearMap (hCP x) (hTP x) (hLeft x) (hPrank x)
  have actual_finite_constant_rank_sqrt_smooth
      {a : Type}
      [Fintype a] [DecidableEq a]
      {rank : ℕ} (Q : B → Matrix a a ℂ)
      (hQ : ContMDiff I 𝓘(ℝ, Matrix a a ℂ) ∞ Q)
      (hPSD : ∀ x, (Q x).PosSemidef)
      (hRank : ∀ x, (Q x).rank = rank) :
      ContMDiff I 𝓘(ℝ, Matrix a a ℂ) ∞ (fun x => CFC.sqrt (Q x)) := by
    classical
    let e : Fin (Fintype.card a) ≃ a := (Fintype.equivFin a).symm
    let Qf := fun x => (Q x).submatrix e e
    have hQf : ContMDiff I 𝓘(ℝ, Matrix (Fin (Fintype.card a))
        (Fin (Fintype.card a)) ℂ) ∞ Qf := by
      apply contMDiff_pi_space.mpr
      intro i
      apply contMDiff_pi_space.mpr
      intro j
      exact contMDiff_pi_space.mp (contMDiff_pi_space.mp hQ (e i)) (e j)
    have hPf (x) : (Qf x).PosSemidef := (hPSD x).submatrix e
    have hRf (x) : (Qf x).rank = rank := (Matrix.rank_submatrix (Q x) e e).trans (hRank x)
    obtain ⟨_, _, hS⟩ := actual_constant_rank_whitening_smooth I Qf hQf hPf hRf
    have hroot (x) : CFC.sqrt (Q x) = (CFC.sqrt (Qf x)).submatrix e.symm e.symm := by
      apply CFC.sqrt_unique
      · rw [Matrix.submatrix_mul_equiv, CFC.sqrt_mul_sqrt_self _ (hPf x).nonneg]
        ext i j
        simp only [Qf, Matrix.submatrix_apply, Equiv.apply_symm_apply]
      · exact ((Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (Qf x))).submatrix
          e.symm).nonneg
    apply contMDiff_pi_space.mpr
    intro i
    apply contMDiff_pi_space.mpr
    intro j
    have hs := contMDiff_pi_space.mp (contMDiff_pi_space.mp hS (e.symm i)) (e.symm j)
    simpa only [hroot, Matrix.submatrix_apply] using hs
  have hJsqrt : ContMDiff I 𝓘(ℝ, Matrix (Fin d × Fin n) (Fin d × Fin n) ℂ) ∞
      (fun x => CFC.sqrt (inputChoi (N x).toLinearMap)) :=
    actual_finite_constant_rank_sqrt_smooth (fun x => inputChoi (N x).toLinearMap)
      hJsm (fun x => inputChoi_posSemidef (N x).toLinearMap (hCP x)) hJrank
  have hAsm (mu : Fin d × Fin n) : ContMDiff I
      𝓘(ℝ, Matrix (Fin n) (Fin d) ℂ) ∞ (fun x => sqrtColumn (N x).toLinearMap mu) := by
    apply contMDiff_pi_space.mpr
    intro a
    apply contMDiff_pi_space.mpr
    intro i
    exact contMDiff_pi_space.mp (contMDiff_pi_space.mp hJsqrt (i,a)) mu
  let L := EuclideanSpace ℂ (Fin d)
  let Vn := EuclideanSpace ℂ (Fin n)
  let Env := EuclideanSpace ℂ (Fin d × Fin n)
  letI : NormedAddCommGroup (Vn ⊗[ℂ] Env) := TensorProduct.instNormedAddCommGroup
  letI : InnerProductSpace ℂ (Vn ⊗[ℂ] Env) := TensorProduct.instInnerProductSpace
  let AA : B → (Fin d × Fin n) → Matrix (Fin n) (Fin d) ℂ :=
    fun x mu => sqrtColumn (N x).toLinearMap mu
  let U : B → (L →ₗ[ℂ] Vn ⊗[ℂ] Env) := fun x => ∑ mu,
    (((TensorProduct.mk ℂ Vn Env).flip (EuclideanSpace.single mu (1 : ℂ))).comp
      (AA x mu).toEuclideanLin)
  have hU (x : B) (u : L) : U x u = ∑ mu,
      (AA x mu).toEuclideanLin u ⊗ₜ[ℂ] EuclideanSpace.single mu (1 : ℂ) := by
    simp only [U, LinearMap.sum_apply, LinearMap.comp_apply,
      LinearMap.flip_apply, TensorProduct.mk_apply]
  have hGram (x : B) :
      (∑ mu, (LinearMap.adjoint (AA x mu).toEuclideanLin).comp
        (AA x mu).toEuclideanLin) = LinearMap.id := by
    simp_rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
      ← Matrix.toLpLin_mul_same]
    have hh := congrArg Matrix.toEuclideanLin
      (actual_sqrt_columns_kraus (N x).toLinearMap (hCP x) (hTP x)).2
    simpa only [AA, map_sum, Matrix.toEuclideanLin, Matrix.toLpLin_one] using hh
  have hInner (x : B) (u w : L) : inner ℂ (U x u) (U x w) = inner ℂ u w := by
    rw [hU, hU, st37_tensor_sum_inner, hGram]
    rfl
  let VV : B → (L →ₗᵢ[ℂ] Vn ⊗[ℂ] Env) := fun x => (U x).isometryOfInner (hInner x)
  have hVsm : ContMDiff (I.prod 𝓘(ℝ, L)) 𝓘(ℝ, Vn ⊗[ℂ] Env) ∞
      (fun z : B × L => VV z.1 z.2) := by
    have hs := st37_tensor_sum_smooth I AA hAsm
    change ContMDiff (I.prod 𝓘(ℝ, L)) 𝓘(ℝ, Vn ⊗[ℂ] Env) ∞
      (fun z : B × L => U z.1 z.2)
    simpa only [hU] using hs
  have hVcoeff (x : B) (a : Fin n) (mu : Fin d × Fin n) (i : Fin d) :
      inner ℂ (EuclideanSpace.single a 1 ⊗ₜ[ℂ] EuclideanSpace.single mu (1 : ℂ))
        (VV x (EuclideanSpace.single i 1)) = AA x mu a i := by
    change inner ℂ (EuclideanSpace.single a 1 ⊗ₜ[ℂ] EuclideanSpace.single mu (1 : ℂ))
      (U x (EuclideanSpace.single i 1)) = _
    rw [hU]
    simp [inner_sum, TensorProduct.inner_tmul, EuclideanSpace.inner_single_left,
      Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.mulVec_single]
  have hVreal (x : B) (T : Matrix (Fin d) (Fin d) ℂ) (a b : Fin n) :
      N x T a b = ∑ mu, ∑ i, ∑ j,
        inner ℂ (EuclideanSpace.single a 1 ⊗ₜ[ℂ] EuclideanSpace.single mu (1 : ℂ))
          (VV x (EuclideanSpace.single i 1)) * T i j *
        star (inner ℂ (EuclideanSpace.single b 1 ⊗ₜ[ℂ] EuclideanSpace.single mu (1 : ℂ))
          (VV x (EuclideanSpace.single j 1))) := by
    simp only [hVcoeff]
    have hh := congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => M a b)
      ((actual_sqrt_columns_kraus (N x).toLinearMap (hCP x) (hTP x)).1 T)
    simp only [AA, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Finset.sum_mul, Finset.mul_sum, mul_assoc] at hh ⊢
    rw [hN_apply] at hh
    exact hh.trans (Finset.sum_congr rfl fun mu _ => Finset.sum_comm)
  refine ⟨hQ, hP, hW, hpi, hAlg, hDecK, hReset, hDsm, ?_, ?_, hJsm,
    (fun x => ⟨inputChoi_posSemidef (N x).toLinearMap (hCP x), hJrank x,
      inputChoi_index_swap (N x).toLinearMap⟩), hJsqrt, hAsm,
    (fun x => (actual_sqrt_columns_kraus (N x).toLinearMap (hCP x) (hTP x)).1),
    (fun x => (actual_sqrt_columns_kraus (N x).toLinearMap (hCP x) (hTP x)).2), ⟨VV, hU, hVsm, hVreal⟩⟩

  · intro x
    exact ⟨MatrixMap.of_kraus_isCompletelyPositive (KK x), hDTP x, hDrec x, hDref x,
      hDtrace x, hDtranspose x⟩
  · exact st37_bundle_geometry I hd N hCP hTP hLeft
      hQ hP hW hPstar hPidem hPrank hFsm hFstar hFidem hFrank

end Original8340Global


namespace Original8340Global
open D5.S3.Quantum.Transport.MatrixUnitDyson
open D5.S3.Quantum.Transport.MatrixUnitGenerator
open D5.S3.Quantum.QuantumChannels.IptPptSquaredEquivalence
open scoped Matrix.Norms.L2Operator

/- Transient exact application of the existing results to the controlled interval
of ST40, on the actual ST37 spectral
representation. `D` is the velocity of the actual matrix units, with genuine ambient
path velocity at zero when the entire interval is a singleton. No evolution, transport, decoder, or
reference-system identity is an input. The weight transported by this evolution
is deliberately distinguished from the preset weight of the channel family. -/
set_option maxHeartbeats 3000000 in
example
    {E H B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] [TopologicalSpace B] [ChartedSpace H B] [CompactSpace B]
    (I : ModelWithCorners ℝ E H) [IsManifold I ∞ B]
    {d n k : ℕ} (hd : 0 < d)
    (N : B → (Matrix (Fin d) (Fin d) ℂ →L[ℂ] Matrix (Fin n) (Fin n) ℂ))
    (hN : ContMDiff I 𝓘(ℝ, Matrix (Fin d) (Fin d) ℂ →L[ℂ]
      Matrix (Fin n) (Fin n) ℂ) ∞ N)
    (hCP : ∀ x, MatrixMap.IsCompletelyPositive (N x).toLinearMap)
    (hTP : ∀ x A, Matrix.trace (N x A) = Matrix.trace A)
    (hLeft : ∀ x, ∃ R : MatrixMap (Fin n) (Fin d) ℂ,
      R.IsCompletelyPositive ∧ (∀ X, Matrix.trace (R X) = Matrix.trace X) ∧
      ∀ A, R (N x A) = A)
    (hRank : ∀ x, (N x 1).rank = k * d)
    (path : ℝ → B) (T : ℝ) (hT : 0 ≤ T)
    (D : ℝ → Fin d → Fin d → Matrix (Fin n) (Fin n) ℂ)
    (hpath :
      let W := fun t => spectralInverseSqrt (N (path t) 1)
      let F := fun t i j => W t * N (path t) (Matrix.single i j 1) * W t
      (∀ i j, ContinuousOn (fun t => F t i j) (Icc 0 T)) ∧
      (∀ i j, ContinuousOn (fun t => D t i j) (Icc 0 T)) ∧
      (∀ t ∈ Icc 0 T, ∀ i j a b,
        HasDerivWithinAt (fun u => F u i j a b) (D t i j a b) (Icc 0 T) t) ∧
      (T = 0 → ∀ i j a b,
        HasDerivAt (fun u => F u i j a b) (D 0 i j a b) 0))
    (hL : ℝ → Matrix (Fin d) (Fin d) ℂ)
    (hLc : ContinuousOn hL (Icc 0 T))
    (hLh : ∀ t ∈ Icc 0 T, (hL t).IsHermitian)
    (hbar Delta : ℝ) (hhbar : 0 < hbar) (hDelta : 0 < Delta) :
    let v : Fin d := ⟨0, hd⟩
    let Q := fun x => N x 1
    let P := fun x => spectralSupport (Q x)
    let W := fun x => spectralInverseSqrt (Q x)
    let pi := fun x A => W x * N x A * W x
    let piM := fun x => (LinearMap.mulLeftRight ℂ (W x, W x)).comp (N x).toLinearMap
    let F := fun t i j => pi (path t) (Matrix.single i j 1)
    let K := fun t => transportGenerator (F t) (D t)
    let G := dysonSeries K
    let a : ℂ := -Complex.I / (hbar : ℂ)
    let c : ℂ := Complex.I * (hbar : ℂ)
    let VL := dysonSeries (fun t => a • hL t)
    let phase := fun t => Complex.exp (-Complex.I * (Delta : ℂ) * (t : ℂ) / (hbar : ℂ))
    let Hphys := fun t => c • K t + pi (path t) (hL t) +
      (Delta : ℂ) • (1 - P (path t))
    let V := fun t => G t * (pi (path 0) (VL t) + phase t • (1 - P (path 0)))
    let Kdec := fun x => Sum.elim (decoderKraus (fun i j => pi x (Matrix.single i j 1)) v)
      (fun b => Matrix.single v b (1 : ℂ) * (1 - P x))
    let decoder := fun x => MatrixMap.of_kraus (Kdec x) (Kdec x)
    let encode := fun R => (LinearMap.mulLeft ℂ R).comp (piM (path 0))
    let AdV := fun t => MatrixMap.of_kraus (fun _ : Unit => V t) (fun _ : Unit => V t)
    let AdL := fun t => MatrixMap.of_kraus (fun _ : Unit => VL t) (fun _ : Unit => VL t)
    (VL 0 = 1 ∧ ContinuousOn VL (Icc 0 T) ∧
      ∀ t ∈ Icc 0 T, (VL t)ᴴ * VL t = 1 ∧ VL t * (VL t)ᴴ = 1 ∧
        HasDerivWithinAt VL (a • (hL t * VL t)) (Icc 0 T) t ∧
        c • (a • (hL t * VL t)) = hL t * VL t) ∧
    (V 0 = 1 ∧ ContinuousOn V (Icc 0 T) ∧
      ∀ t ∈ Icc 0 T, (Hphys t).IsHermitian ∧
        (V t)ᴴ * V t = 1 ∧ V t * (V t)ᴴ = 1 ∧
        HasDerivWithinAt V (a • (Hphys t * V t)) (Icc 0 T) t ∧
        c • (a • (Hphys t * V t)) = Hphys t * V t) ∧
    (∀ (R : Matrix (Fin n) (Fin n) ℂ)
      (hcomm : ∀ i j, R * F 0 i j = F 0 i j * R)
      (hsupport : P (path 0) * R = R)
      (htrace : Matrix.trace (F 0 v v * R) = 1),
      ∀ t ∈ Icc 0 T,
        let Rt := G t * R * (G t)ᴴ
        P (path t) * Rt = Rt ∧ Rt * P (path t) = Rt ∧
        (∀ A, Rt * pi (path t) A = pi (path t) A * Rt) ∧
        Matrix.trace (F t v v * Rt) = 1 ∧ Matrix.trace Rt = Matrix.trace R ∧
        (R.PosSemidef → Rt.PosSemidef) ∧
        (∀ A : Matrix (Fin d) (Fin d) ℂ,
          V t * (R * pi (path 0) A) * (V t)ᴴ =
            Rt * pi (path t) (VL t * A * (VL t)ᴴ) ∧
          decoder (path t) (V t * (R * pi (path 0) A) * (V t)ᴴ) =
            VL t * A * (VL t)ᴴ) ∧
        (∀ (q : ℕ) (X : Matrix (Fin d × Fin q) (Fin d × Fin q) ℂ),
          MatrixMap.kron (decoder (path t)) LinearMap.id
            (MatrixMap.kron (AdV t) LinearMap.id
              (MatrixMap.kron (encode R) LinearMap.id X)) =
            MatrixMap.kron (AdL t) LinearMap.id X)) ∧
    (∀ t ∈ Icc 0 T,
      (G t * Q (path 0) * (G t)ᴴ).PosSemidef ∧
      (∀ A : Matrix (Fin d) (Fin d) ℂ,
        V t * N (path 0) A * (V t)ᴴ =
          (G t * Q (path 0) * (G t)ᴴ) * pi (path t) (VL t * A * (VL t)ᴴ) ∧
        decoder (path t) (V t * N (path 0) A * (V t)ᴴ) = VL t * A * (VL t)ᴴ) ∧
      (∀ (q : ℕ) (X : Matrix (Fin d × Fin q) (Fin d × Fin q) ℂ),
        MatrixMap.kron (decoder (path t)) LinearMap.id
          (MatrixMap.kron (AdV t) LinearMap.id
            (MatrixMap.kron (N (path 0)).toLinearMap LinearMap.id X)) =
          MatrixMap.kron (AdL t) LinearMap.id X)) := by
  classical
  let v : Fin d := ⟨0, hd⟩
  letI : Nonempty (Fin d) := ⟨v⟩
  let Q := fun x => N x 1
  let P := fun x => spectralSupport (Q x)
  let W := fun x => spectralInverseSqrt (Q x)
  let pi := fun x A => W x * N x A * W x
  let piM := fun x => (LinearMap.mulLeftRight ℂ (W x, W x)).comp (N x).toLinearMap
  let F := fun t i j => pi (path t) (Matrix.single i j 1)
  let K := fun t => transportGenerator (F t) (D t)
  let G := dysonSeries K
  let a : ℂ := -Complex.I / (hbar : ℂ)
  let c : ℂ := Complex.I * (hbar : ℂ)
  let b : ℂ := -Complex.I * (Delta : ℂ) / (hbar : ℂ)
  let VL := dysonSeries (fun t => a • hL t)
  let phase := fun t => Complex.exp (-Complex.I * (Delta : ℂ) * (t : ℂ) / (hbar : ℂ))
  let Hphys := fun t => c • K t + pi (path t) (hL t) + (Delta : ℂ) • (1 - P (path t))
  let C0 : Matrix (Fin n) (Fin n) ℂ := 1 - P (path 0)
  let bracket := fun t => pi (path 0) (VL t) + phase t • C0
  let V := fun t => G t * bracket t
  let Kdec := fun x => Sum.elim (decoderKraus (fun i j => pi x (Matrix.single i j 1)) v)
    (fun b => Matrix.single v b (1 : ℂ) * (1 - P x))
  let decoder := fun x => MatrixMap.of_kraus (Kdec x) (Kdec x)
  let encode := fun R => (LinearMap.mulLeft ℂ R).comp (piM (path 0))
  let AdV := fun t => MatrixMap.of_kraus (fun _ : Unit => V t) (fun _ : Unit => V t)
  let AdL := fun t => MatrixMap.of_kraus (fun _ : Unit => VL t) (fun _ : Unit => VL t)
  have hpiM (x) (A) : piM x A = pi x A := rfl
  have hbar0 : (hbar : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hhbar
  have hca : c * a = 1 := by
    dsimp [c, a]
    field_simp [hbar0] <;> ring_nf <;> simp [Complex.I_sq]
  have hcb : c * b = (Delta : ℂ) := by
    dsimp [c, b]
    field_simp [hbar0] <;> ring_nf <;> simp [Complex.I_sq]
  have hastar : star a = -a := by simp [a, Complex.star_def]
  have hcstar : star c = -c := by simp [c, Complex.star_def]
  have hbstar : star b = -b := by simp [b, Complex.star_def]
  -- The existing whole theorem supplies this exact spectral representation and
  -- this exact decoder. No replacement decoder is selected.
  have h37 := whole_original_ST37 I hd N hN hCP hTP hLeft hRank
  rcases h37 with ⟨_, _, _, _, hAlg, _, _, _, hDec, _⟩
  have hpi1 (x) : pi x 1 = P x := (hAlg x).1
  have hpis (x) (A) : (pi x A)ᴴ = pi x Aᴴ := (hAlg x).2.1 A
  have hpim (x) (A B) : pi x A * pi x B = pi x (A * B) := (hAlg x).2.2.1 A B
  have hQcomm (x) (A) : Q x * pi x A = pi x A * Q x := (hAlg x).2.2.2.1 A
  have hNfactor (x) (A) : N x A = Q x * pi x A := (hAlg x).2.2.2.2 A
  have hPstar (x) : (P x)ᴴ = P x := by
    rw [← hpi1, hpis, Matrix.conjTranspose_one]
  have hPP (x) : P x * P x = P x := by
    rw [← hpi1, hpim, Matrix.one_mul]
  have hPpi (x) (A) : P x * pi x A = pi x A := by
    rw [← hpi1, hpim, Matrix.one_mul]
  have hpiP (x) (A) : pi x A * P x = pi x A := by
    rw [← hpi1, hpim, Matrix.mul_one]
  have hpiC (A) : pi (path 0) A * C0 = 0 := by
    dsimp [C0]
    rw [Matrix.mul_sub, Matrix.mul_one, hpiP, sub_self]
  have hCpi (A) : C0 * pi (path 0) A = 0 := by
    dsimp [C0]
    rw [Matrix.sub_mul, Matrix.one_mul, hPpi, sub_self]
  have hCC : C0 * C0 = C0 := by
    calc
      C0 * C0 = 1 - P (path 0) - P (path 0) + P (path 0) * P (path 0) := by
        dsimp [C0]
        noncomm_ring
      _ = C0 := by rw [hPP]; dsimp [C0]; noncomm_ring
  have hCstar : C0ᴴ = C0 := by simp only [C0, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_one, hPstar]
  have hFm (t) (i j k l : Fin d) :
      F t i j * F t k l = if j = k then F t i l else 0 := by
    have hh := hpim (path t) (Matrix.single i j 1) (Matrix.single k l 1)
    by_cases hj : j = k
    · subst k
      simpa only [F, Matrix.single_mul_single_same, one_mul, if_pos rfl] using hh
    · have hz : Matrix.single i j (1 : ℂ) * Matrix.single k l (1 : ℂ) = 0 :=
        Matrix.single_mul_single_of_ne (c := (1 : ℂ)) (i := i) (j := j)
          (k := k) (h := hj) (d := (1 : ℂ))
      simpa only [F, pi, hz, map_zero, Matrix.mul_zero, Matrix.zero_mul, if_neg hj] using hh
  have hFs (t) (i j : Fin d) : (F t i j)ᴴ = F t j i := by
    simpa only [F, Matrix.conjTranspose_single, star_one] using
      hpis (path t) (Matrix.single i j 1)
  have hrepr (x) (A : Matrix (Fin d) (Fin d) ℂ) :
      representedMatrix (fun i j => pi x (Matrix.single i j 1)) A = pi x A := by
    have he : (∑ i, ∑ j, A i j • Matrix.single i j (1 : ℂ)) = A := by
      simpa only [Matrix.smul_single, smul_eq_mul, mul_one] using Matrix.sum_sum_single A
    calc
      _ = piM x (∑ i, ∑ j, A i j • Matrix.single i j (1 : ℂ)) := by
        simp only [representedMatrix, map_sum, map_smul, hpiM]
      _ = pi x A := by rw [he, hpiM]
  rcases hpath with ⟨hFcont, hDcont, hentry, hzeroVelocity⟩
  have hpositive (hp : 0 < T) : wholeConclusion F D T :=
    (constructive_transport (d := Fin d) (n := Fin n)).2
      F D T hp hFcont hDcont hentry (fun t _ => hFm t) (fun t _ => hFs t)
  have hKcont : ContinuousOn K (Icc 0 T) := by
    change ContinuousOn
      (fun t => (Fintype.card (Fin d) : ℂ)⁻¹ • (∑ i, ∑ j, D t i j * F t j i) -
        (∑ i, F t i i) * (∑ i, D t i i)) (Icc 0 T)
    exact ((continuousOn_finsetSum _ fun i _ =>
      continuousOn_finsetSum _ fun j _ => (hDcont i j).mul (hFcont j i)).const_smul _).sub
        ((continuousOn_finsetSum _ fun i _ => hFcont i i).mul
          (continuousOn_finsetSum _ fun i _ => hDcont i i))
  have hKskew (t) (ht : t ∈ Icc 0 T) : (K t)ᴴ = -K t := by
    by_cases hz : T = 0
    · have ht0 : t = 0 := le_antisymm (ht.2.trans_eq hz) ht.1
      subst t
      exact (generator_from_real_path F (D 0) 0 hFm hFs (hzeroVelocity hz)).1
    · exact ((hpositive (lt_of_le_of_ne hT (Ne.symm hz))).1 t ht).1
  obtain ⟨_, _, _, _, _, hGcont, _, hGderiv, hGzero, _⟩ :=
    (constructive_transport (d := Fin d) (n := Fin n)).1 K T hT hKcont
  have hGu := unitary_of_skew_evolution K G T hT hGderiv hKskew hGzero
  have hGcancel (t) (ht : t ∈ Icc 0 T) (X : Matrix (Fin n) (Fin n) ℂ) :
      (G t)ᴴ * (G t * X) = X := by
    rw [← Matrix.mul_assoc, (hGu t ht).1, Matrix.one_mul]
  have hFt : ∀ t ∈ Icc 0 T, ∀ i j, F t i j = G t * F 0 i j * (G t)ᴴ := by
    by_cases hz : T = 0
    · intro t ht i j
      have ht0 : t = 0 := le_antisymm (ht.2.trans_eq hz) ht.1
      simp only [ht0, G, hGzero, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
    · have hp : 0 < T := lt_of_le_of_ne hT (Ne.symm hz)
      have hh := hpositive hp
      rcases hh with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, htr, _⟩
      exact fun t ht i j => (htr t ht i j).2
  have hpit (t) (ht : t ∈ Icc 0 T) (A : Matrix (Fin d) (Fin d) ℂ) :
      pi (path t) A = G t * pi (path 0) A * (G t)ᴴ := by
    rw [← hrepr (path t), ← hrepr (path 0)]
    simp only [representedMatrix, Matrix.mul_sum, Matrix.sum_mul,
      Matrix.mul_smul, Matrix.smul_mul]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    exact congrArg (fun X => A i j • X) (hFt t ht i j)
  have hPt (t) (ht : t ∈ Icc 0 T) : P (path t) = G t * P (path 0) * (G t)ᴴ := by
    simpa only [hpi1] using hpit t ht (1 : Matrix (Fin d) (Fin d) ℂ)
  obtain ⟨_, _, _, _, _, hVLcont, _, hVLderiv, hVLzero, _⟩ :=
    (constructive_transport (d := Fin d) (n := Fin d)).1
      (fun t => a • hL t) T hT (hLc.const_smul a)
  have hVLskew (t) (ht : t ∈ Icc 0 T) : (a • hL t)ᴴ = -(a • hL t) := by
    rw [Matrix.conjTranspose_smul, (hLh t ht).eq, hastar, neg_smul]
  have hVLu := unitary_of_skew_evolution (fun t => a • hL t) VL T hT
    hVLderiv hVLskew hVLzero
  have hVLd (t) (ht : t ∈ Icc 0 T) :
      HasDerivWithinAt VL (a • (hL t * VL t)) (Icc 0 T) t := by
    simpa only [Matrix.smul_mul] using hVLderiv t ht
  have hphaseform (t : ℝ) : phase t = Complex.exp (b * (t : ℂ)) := by
    dsimp [phase, b]
    congr 1
    ring
  have hphase0 : phase 0 = 1 := by simp [phase]
  have hphased (t : ℝ) : HasDerivAt phase (phase t * b) t := by
    have hh := ((Complex.ofRealCLM.hasDerivAt (x := t)).const_mul b).cexp
    simpa only [mul_one, ← hphaseform] using hh
  have hphaseunit (t : ℝ) : star (phase t) * phase t = 1 := by
    rw [hphaseform]
    change starRingEnd ℂ (Complex.exp (b * (t : ℂ))) * Complex.exp (b * (t : ℂ)) = 1
    rw [← Complex.exp_conj, ← Complex.exp_add]
    have hz : starRingEnd ℂ (b * (t : ℂ)) + b * (t : ℂ) = 0 := by
      change star (b * (t : ℂ)) + b * (t : ℂ) = 0
      rw [star_mul', hbstar]
      simp
    rw [hz, Complex.exp_zero]
  have hbracketd (t) (ht : t ∈ Icc 0 T) :
      HasDerivWithinAt bracket
        (a • (pi (path 0) (hL t) * pi (path 0) (VL t)) +
          (phase t * b) • C0) (Icc 0 T) t := by
    have hh := (((piM (path 0)).toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt
      (x := VL t)).comp_hasDerivWithinAt t (hVLd t ht)
    have hmap : piM (path 0) (a • (hL t * VL t)) =
        a • (pi (path 0) (hL t) * pi (path 0) (VL t)) := by
      rw [map_smul, hpiM, ← hpim]
    change HasDerivWithinAt (fun s => pi (path 0) (VL s))
      (piM (path 0) (a • (hL t * VL t))) (Icc 0 T) t at hh
    rw [hmap] at hh
    simpa only [bracket] using hh.add ((hphased t).hasDerivWithinAt.smul_const C0)
  have hbracketcont : ContinuousOn bracket (Icc 0 T) := by
    intro t ht
    exact (hbracketd t ht).continuousWithinAt
  have hbracketunit (t) (ht : t ∈ Icc 0 T) :
      (bracket t)ᴴ * bracket t = 1 ∧ bracket t * (bracket t)ᴴ = 1 := by
    have hcorner : pi (path 0) ((VL t)ᴴ) * pi (path 0) (VL t) = P (path 0) := by
      rw [hpim, (hVLu t ht).1, hpi1]
    have hleft : (bracket t)ᴴ * bracket t = 1 := by
      simp only [bracket, Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
        hCstar, Matrix.add_mul, Matrix.mul_add, Matrix.mul_smul,
        Matrix.smul_mul, smul_smul, hpis, hcorner, hpiC, hCpi, hCC,
        hphaseunit, one_smul, smul_zero, zero_add, add_zero]
      exact add_sub_cancel _ _
    exact ⟨hleft, mul_eq_one_comm.mp hleft⟩
  have hVzero : V 0 = 1 := by
    simp only [V, bracket, hGzero, hVLzero, hphase0, hpi1, one_smul, Matrix.one_mul, C0]
    exact add_sub_cancel _ _
  have hVcont : ContinuousOn V (Icc 0 T) := hGcont.mul hbracketcont
  have hVu (t) (ht : t ∈ Icc 0 T) : (V t)ᴴ * V t = 1 ∧ V t * (V t)ᴴ = 1 := by
    have hh : (V t)ᴴ * V t = 1 := by
      simp only [V, Matrix.conjTranspose_mul, Matrix.mul_assoc, hGcancel t ht, (hGu t ht).1,
        Matrix.one_mul, (hbracketunit t ht).1]
    exact ⟨hh, mul_eq_one_comm.mp hh⟩
  have hHherm (t) (ht : t ∈ Icc 0 T) : (Hphys t).IsHermitian := by
    change (Hphys t)ᴴ = Hphys t
    simp only [Hphys, Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
      hKskew t ht, hcstar, smul_neg, neg_smul, neg_neg, hpis, (hLh t ht).eq,
      Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hPstar,
      show star (Delta : ℂ) = (Delta : ℂ) from Complex.conj_ofReal Delta]
  have hVd (t) (ht : t ∈ Icc 0 T) :
      HasDerivWithinAt V (a • (Hphys t * V t)) (Icc 0 T) t := by
    let Bdot := a • (pi (path 0) (hL t) * pi (path 0) (VL t)) + (phase t * b) • C0
    have hp := (hGderiv t ht).mul (hbracketd t ht)
    have hpiG : pi (path t) (hL t) * G t = G t * pi (path 0) (hL t) := by
      rw [hpit t ht]
      simp only [Matrix.mul_assoc, hGcancel t ht, (hGu t ht).1, Matrix.mul_one]
    have hCG : (1 - P (path t)) * G t = G t * C0 := by
      rw [Matrix.sub_mul, Matrix.one_mul, hPt t ht]
      simp only [Matrix.mul_assoc, hGcancel t ht, (hGu t ht).1, Matrix.mul_one]
      simp only [C0, Matrix.mul_sub, Matrix.mul_one]
    have hphysical : c • ((K t * G t) * bracket t + G t * Bdot) = Hphys t * V t := by
      have hterm1 : pi (path t) (hL t) * V t =
          G t * (pi (path 0) (hL t) * pi (path 0) (VL t)) := by
        dsimp [V]
        rw [← Matrix.mul_assoc, hpiG, Matrix.mul_assoc]
        dsimp [bracket]
        rw [Matrix.mul_add, Matrix.mul_smul, hpiC, smul_zero, add_zero]
      have hterm2 : (1 - P (path t)) * V t = G t * (phase t • C0) := by
        dsimp [V]
        rw [← Matrix.mul_assoc, hCG, Matrix.mul_assoc]
        dsimp [bracket]
        rw [Matrix.mul_add, Matrix.mul_smul, hCpi, hCC, zero_add]
      rw [Hphys, Matrix.add_mul, Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul,
        hterm1, hterm2]
      dsimp [Bdot]
      simp only [smul_add, Matrix.mul_add, Matrix.mul_smul, smul_smul, hca, one_smul]
      have hphasecoef : c * (phase t * b) = (Delta : ℂ) * phase t := by
        calc
          _ = (c * b) * phase t := by ring
          _ = _ := by rw [hcb]
      rw [hphasecoef]
      simp only [V, Matrix.mul_assoc, Matrix.mul_smul, smul_smul]
    have htarget : (K t * G t) * bracket t + G t * Bdot = a • (Hphys t * V t) := by
      rw [← hphysical, smul_smul, mul_comm a c, hca, one_smul]
    change HasDerivWithinAt V ((K t * G t) * bracket t + G t * Bdot) (Icc 0 T) t at hp
    rw [htarget] at hp
    exact hp
  have hDtrace (x) (X : Matrix (Fin n) (Fin n) ℂ) (i j : Fin d) :
      decoder x X i j = Matrix.trace (pi x (Matrix.single j i 1) * X) +
        Matrix.trace ((1 - P x) * X) * Matrix.single v v (1 : ℂ) i j :=
    (hDec x).2.2.2.2.1 X i j
  have hAdV (t) (X : Matrix (Fin n) (Fin n) ℂ) : AdV t X = V t * X * (V t)ᴴ := by
    simp [AdV, MatrixMap.of_kraus]
  have hAdL (t) (A : Matrix (Fin d) (Fin d) ℂ) : AdL t A = VL t * A * (VL t)ᴴ := by
    simp [AdL, MatrixMap.of_kraus]
  have hweights : ∀ (R : Matrix (Fin n) (Fin n) ℂ)
      (hcomm : ∀ i j, R * F 0 i j = F 0 i j * R)
      (hsupport : P (path 0) * R = R)
      (htrace : Matrix.trace (F 0 v v * R) = 1),
      ∀ t ∈ Icc 0 T,
        let Rt := G t * R * (G t)ᴴ
        P (path t) * Rt = Rt ∧ Rt * P (path t) = Rt ∧
        (∀ A, Rt * pi (path t) A = pi (path t) A * Rt) ∧
        Matrix.trace (F t v v * Rt) = 1 ∧ Matrix.trace Rt = Matrix.trace R ∧
        (R.PosSemidef → Rt.PosSemidef) ∧
        (∀ A : Matrix (Fin d) (Fin d) ℂ,
          V t * (R * pi (path 0) A) * (V t)ᴴ =
            Rt * pi (path t) (VL t * A * (VL t)ᴴ) ∧
          decoder (path t) (V t * (R * pi (path 0) A) * (V t)ᴴ) = VL t * A * (VL t)ᴴ) ∧
        (∀ (q : ℕ) (X : Matrix (Fin d × Fin q) (Fin d × Fin q) ℂ),
          MatrixMap.kron (decoder (path t)) LinearMap.id
            (MatrixMap.kron (AdV t) LinearMap.id
              (MatrixMap.kron (encode R) LinearMap.id X)) =
            MatrixMap.kron (AdL t) LinearMap.id X) := by
    intro R hcomm hsupport htrace t ht
    let Rt := G t * R * (G t)ᴴ
    have hcommA (A : Matrix (Fin d) (Fin d) ℂ) : R * pi (path 0) A = pi (path 0) A * R := by
      rw [← hrepr (path 0)]
      simp only [representedMatrix, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      exact congrArg (fun X => A i j • X) (hcomm i j)
    have hCR : C0 * R = 0 := by simp only [C0, Matrix.sub_mul, Matrix.one_mul, hsupport, sub_self]
    have hRtsupport : P (path t) * Rt = Rt := by
      rw [hPt t ht]
      dsimp [Rt]
      calc
        _ = G t * (P (path 0) * R) * (G t)ᴴ := by
          simp only [Matrix.mul_assoc, hGcancel t ht, (hGu t ht).1, Matrix.one_mul]
        _ = _ := by rw [hsupport]
    have hRtcomm (A) : Rt * pi (path t) A = pi (path t) A * Rt := by
      rw [hpit t ht]
      dsimp [Rt]
      calc
        _ = G t * (R * pi (path 0) A) * (G t)ᴴ := by
          simp only [Matrix.mul_assoc, hGcancel t ht, (hGu t ht).1, Matrix.one_mul]
        _ = G t * (pi (path 0) A * R) * (G t)ᴴ := by rw [hcommA]
        _ = _ := by simp only [Matrix.mul_assoc, hGcancel t ht, (hGu t ht).1, Matrix.one_mul]
    have hRtP : Rt * P (path t) = Rt := by rw [← hpi1, hRtcomm, hpi1, hRtsupport]
    have hRttrace : Matrix.trace (F t v v * Rt) = 1 := by
      rw [hFt t ht]
      dsimp [Rt]
      calc
        _ = Matrix.trace (G t * (F 0 v v * R) * (G t)ᴴ) := by
          simp only [Matrix.mul_assoc, hGcancel t ht, (hGu t ht).1, Matrix.one_mul]
        _ = Matrix.trace (F 0 v v * R) := by
          rw [Matrix.trace_mul_comm, hGcancel t ht]
        _ = 1 := htrace
    have hRtfulltrace : Matrix.trace Rt = Matrix.trace R := by
      dsimp [Rt]
      rw [Matrix.trace_mul_comm, hGcancel t ht]
    have houtput (A : Matrix (Fin d) (Fin d) ℂ) :
        V t * (R * pi (path 0) A) * (V t)ᴴ = Rt * pi (path t) (VL t * A * (VL t)ᴴ) := by
      have hBR : bracket t * (R * pi (path 0) A) = R * pi (path 0) (VL t * A) := by
        dsimp [bracket]
        rw [Matrix.add_mul, Matrix.smul_mul]
        have hz : C0 * (R * pi (path 0) A) = 0 := by
          rw [← Matrix.mul_assoc, hCR, Matrix.zero_mul]
        rw [hz, smul_zero, add_zero, ← Matrix.mul_assoc, ← hcommA,
          Matrix.mul_assoc, hpim]
      have hBoutput : bracket t * (R * pi (path 0) A) * (bracket t)ᴴ =
          R * pi (path 0) (VL t * A * (VL t)ᴴ) := by
        rw [hBR]
        dsimp [bracket]
        rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, hCstar,
          Matrix.mul_add, Matrix.mul_smul, hpis]
        have hz : (R * pi (path 0) (VL t * A)) * C0 = 0 := by
          rw [Matrix.mul_assoc, hpiC, Matrix.mul_zero]
        rw [hz, smul_zero, add_zero, Matrix.mul_assoc, hpim]
      calc
        _ = G t * (bracket t * (R * pi (path 0) A) * (bracket t)ᴴ) * (G t)ᴴ := by
          simp only [V, Matrix.conjTranspose_mul, Matrix.mul_assoc]
        _ = G t * (R * pi (path 0) (VL t * A * (VL t)ᴴ)) * (G t)ᴴ := by rw [hBoutput]
        _ = _ := by
          rw [hpit t ht]
          dsimp [Rt]
          simp only [Matrix.mul_assoc, hGcancel t ht, (hGu t ht).1, Matrix.one_mul]
    have hdecode (A : Matrix (Fin d) (Fin d) ℂ) :
        decoder (path t) (V t * (R * pi (path 0) A) * (V t)ᴴ) = VL t * A * (VL t)ᴴ := by
      rw [houtput]
      have hz : (1 - P (path t)) * (Rt * pi (path t) (VL t * A * (VL t)ᴴ)) = 0 := by
        rw [← Matrix.mul_assoc, Matrix.sub_mul, Matrix.one_mul, hRtsupport,
          sub_self, Matrix.zero_mul]
      ext i j
      rw [hDtrace, hz, Matrix.trace_zero, zero_mul, add_zero]
      change Matrix.trace (F t j i * (Rt * pi (path t) (VL t * A * (VL t)ᴴ))) = _
      rw [← hrepr (path t)]
      exact weighted_pairing (F t) (hFm t) v Rt
        (fun u w => hRtcomm (Matrix.single u w 1)) hRttrace _ i j
    refine ⟨hRtsupport, hRtP, hRtcomm, hRttrace, hRtfulltrace,
      (fun hR => hR.mul_mul_conjTranspose_same (G t)),
      (fun A => ⟨houtput A, hdecode A⟩), ?_⟩
    intro q X
    ext ⟨i,u⟩ ⟨j,w⟩
    simpa only [kron_id_apply, hAdV, hAdL, encode, LinearMap.comp_apply,
      LinearMap.mulLeft_apply, hpiM] using
      congrArg (fun M : Matrix (Fin d) (Fin d) ℂ => M i j)
        (hdecode (fun a b => X (a,u) (b,w)))
  have hQ0support : P (path 0) * Q (path 0) = Q (path 0) := by
    have hh : Q (path 0) = Q (path 0) * P (path 0) := by
      simpa only [Q, hpi1] using hNfactor (path 0) (1 : Matrix (Fin d) (Fin d) ℂ)
    rw [← hpi1, ← hQcomm, hpi1, ← hh]
  have hQ0trace : Matrix.trace (F 0 v v * Q (path 0)) = 1 := by
    calc
      _ = Matrix.trace (Q (path 0) * pi (path 0) (Matrix.single v v 1)) := by
        rw [hQcomm]
      _ = Matrix.trace (N (path 0) (Matrix.single v v 1)) := by rw [hNfactor]
      _ = 1 := by rw [hTP]; simp
  have hQ0pos : (Q (path 0)).PosSemidef := by
    obtain ⟨AA, hAA⟩ := MatrixMap.IsCompletelyPositive.exists_kraus
      (N (path 0)).toLinearMap (hCP (path 0))
    have he : Q (path 0) = ∑ z, AA z * (AA z)ᴴ := by
      simpa [Q, MatrixMap.of_kraus, Matrix.mul_one] using
        congrArg (fun f : MatrixMap (Fin d) (Fin n) ℂ => f 1) hAA
    rw [he]
    exact Matrix.nonneg_iff_posSemidef.mp
      (Finset.sum_nonneg fun z _ => (Matrix.posSemidef_self_mul_conjTranspose (AA z)).nonneg)
  have hencodeQ : encode (Q (path 0)) = (N (path 0)).toLinearMap := by
    apply LinearMap.ext
    intro A
    exact (hNfactor (path 0) A).symm
  refine ⟨⟨hVLzero, hVLcont, ?_⟩, ⟨hVzero, hVcont, ?_⟩, hweights, ?_⟩
  · intro t ht
    exact ⟨(hVLu t ht).1, (hVLu t ht).2, hVLd t ht, by rw [smul_smul, hca, one_smul]⟩
  · intro t ht
    exact ⟨hHherm t ht, (hVu t ht).1, (hVu t ht).2, hVd t ht,
      by rw [smul_smul, hca, one_smul]⟩
  · intro t ht
    have hw := hweights (Q (path 0))
      (fun i j => hQcomm (path 0) (Matrix.single i j 1)) hQ0support hQ0trace t ht
    refine ⟨hw.2.2.2.2.2.1 hQ0pos, ?_, ?_⟩
    · intro A
      simpa only [← hNfactor (path 0) A] using hw.2.2.2.2.2.2.1 A
    · intro q X
      simpa only [hencodeQ] using hw.2.2.2.2.2.2.2 q X

end Original8340Global
