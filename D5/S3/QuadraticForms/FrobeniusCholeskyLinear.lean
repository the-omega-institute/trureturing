/- GID: D5/S3/QuadraticForms/FrobeniusCholeskyLinear
   generality: G
   mirror-B: D5/B/S3/QuadraticForms/FrobeniusCholeskyLinear
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Arithmetic recipes and rank-preserving characteristic-two matrix fibers. -/

/-
admission_basis: escape-witness
admission_theorem: adaptedIndices_spec
escape_witness: adaptedIndices_spec
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/24291
Coordinate columns are identity submatrices and index selections use greedyRoleScanFrom.
The unseeded independent-column and spanning claims apply the frozen minimum-cost basis theorem.
The seeded scan statements allow arbitrary lists and independent initial sets.
D5.S3.Estimation.ExperimentCost.MinimumCostRoleBasis.IsRoleBasis: declaration statement_id=sha256:a7314376031344f2fd7a2a51a1270cb9c1be00cdaf84d56088f3607048355fc9
D5.S3.Estimation.ExperimentCost.MinimumCostRoleBasis.greedyRoleScan: declaration statement_id=sha256:f8f5b6faba28894c2462b64069ba35b0e4908ae2401137bd295b01e330f23587
D5.S3.Estimation.ExperimentCost.MinimumCostRoleBasis.greedyRoleScanFrom: declaration statement_id=sha256:fc3d30f574cb1dbd5dfa4a6769a0de818a67ccb44cce89df5eb54722be0c56f0
D5.S3.Estimation.ExperimentCost.MinimumCostRoleBasis.greedy_role_scan_is_minimum_cost_basis: declaration statement_id=sha256:4debc8898102e484c0aa789cca28cb064e11fc67d13ff476986126cd1a63b2ae
D5.S3.Estimation.ExperimentCost.MinimumCostRoleBasis.instDecidableEq_d5: declaration statement_id=sha256:53fdb48bd71c5f81577fc7e746b20281fe7d85f5392a98f11c5ad17685672c41
D5.S3.Estimation.ExperimentCost.MinimumCostRoleBasis.linearRoleMatroid: declaration statement_id=sha256:fea38fa63812ff0931965c3ca5fff8c54b0df4f19d6347d8916075ccb52cc320
D5.S3.Estimation.ExperimentCost.MinimumCostRoleBasis.linearRoleMatroid_indep_iff: declaration statement_id=sha256:5bd8bf76d7da4d2c6c66e058e7ce532a9f2557b93a59861af15b5e438f71905b
minorCoordinates: proof_shape: bind-only; escape_witness: none; consumers: FrobeniusCholeskyLinear.frameCoordinates_left, FrobeniusCholeskyLinear.frameTransport, FrobeniusCholeskyLinear.frameTransport_apply, FrobeniusCholeskyLinear.frameTransport_range, FrobeniusCholeskyLinear.minorCoordinates_reconstruct, FrobeniusCholeskyLinear.minorKernel, FrobeniusCholeskyLinear.minorKernel_free, FrobeniusCholeskyLinear.minorKernel_mem
minorKernel: proof_shape: bind-only; escape_witness: none; consumers: FrobeniusCholeskyLinear.minorKernel_free, FrobeniusCholeskyLinear.minorKernel_mem, FrobeniusCholeskyLinear.minorKernel_span, FrobeniusCholeskyResult.kernelRecipeChoice_spec, FrobeniusCholeskyResult.kernelRecipe_matches
mul_coordinateColumns: proof_shape: bind-only; escape_witness: none; consumers: FrobeniusCholeskyLinear.frameTransport_selected, FrobeniusCholeskyLinear.minorKernel_mem
minorCoordinates_reconstruct: proof_shape: bind-only; escape_witness: none; consumers: FrobeniusCholeskyLinear.minorKernel_mem
minorKernel_mem: proof_shape: bind-only; escape_witness: none; consumers: FrobeniusCholeskyLinear.minorKernel_span, FrobeniusCholeskyResult.kernelRecipeChoice_spec
minorKernel_free: proof_shape: bind-only; escape_witness: none; consumers: FrobeniusCholeskyLinear.minorKernel_span
kernel_zero_of_free_zero: proof_shape: bind-only; escape_witness: none; consumers: FrobeniusCholeskyLinear.minorKernel_span
sum_free_delta: proof_shape: bind-only; escape_witness: none; consumers: FrobeniusCholeskyLinear.minorKernel_span
minorKernel_span: proof_shape: bind-only; escape_witness: none; consumers: FrobeniusCholeskyResult.kernelRecipeChoice_spec
frameTransport: proof_shape: bind-only; escape_witness: none; consumers: FrobeniusCholeskyLinear.adaptedFrame_transport, FrobeniusCholeskyLinear.frameTransport_apply, FrobeniusCholeskyLinear.frameTransport_bijOn_range, FrobeniusCholeskyLinear.frameTransport_injective, FrobeniusCholeskyLinear.frameTransport_inverse, FrobeniusCholeskyLinear.frameTransport_range, FrobeniusCholeskyLinear.frameTransport_selected, FrobeniusCholeskyLinear.frameTransport_selected_range_iff, FrobeniusCholeskyResult.pairLeaf_spec, FrobeniusCholeskyResult.transportMatrixRecipe_apply
frameCoordinates_left: proof_shape: bind-only; escape_witness: none; consumers: FrobeniusCholeskyLinear.frameTransport_apply
frameTransport_apply: proof_shape: bind-only; escape_witness: none; consumers: FrobeniusCholeskyLinear.frameTransport_bijOn_range, FrobeniusCholeskyLinear.frameTransport_inverse, FrobeniusCholeskyLinear.frameTransport_selected
frameTransport_range: proof_shape: bind-only; escape_witness: none; consumers: FrobeniusCholeskyLinear.frameTransport_bijOn_range
frameTransport_inverse: proof_shape: bind-only; escape_witness: none; consumers: FrobeniusCholeskyLinear.frameTransport_injective, FrobeniusCholeskyLinear.frameTransport_selected_range_iff
frameTransport_injective: proof_shape: bind-only; escape_witness: none; consumers: FrobeniusCholeskyLinear.frameTransport_bijOn_range
frameTransport_selected: proof_shape: bind-only; escape_witness: none; consumers: FrobeniusCholeskyLinear.frameTransport_selected_range_iff
frameTransport_selected_range_iff: proof_shape: bind-only; escape_witness: none; consumers: FrobeniusCholeskyLinear.adaptedFrame_transport
frameTransport_bijOn_range: proof_shape: bind-only; escape_witness: none; consumers: FrobeniusCholeskyLinear.adaptedFrame_transport
adaptedFrame_transport: proof_shape: bind-only; escape_witness: none; consumers: FrobeniusCholeskyResult.pairLeaf_spec
greedy_mono: proof_shape: content; escape_witness: D5.S3.QuadraticForms.FrobeniusCholeskyLinear.greedy_mono; consumers: FrobeniusCholeskyLinear.adaptedIndices_spec, FrobeniusCholeskyLinear.greedy_extension_span, FrobeniusCholeskyLinear.greedy_spans
greedy_independent: proof_shape: content; escape_witness: D5.S3.QuadraticForms.FrobeniusCholeskyLinear.greedy_independent; consumers: FrobeniusCholeskyLinear.adaptedIndices_spec, FrobeniusCholeskyLinear.greedy_extension_card
greedy_spans: proof_shape: content; escape_witness: D5.S3.QuadraticForms.FrobeniusCholeskyLinear.greedy_spans; consumers: FrobeniusCholeskyLinear.greedy_extension_span
selectedColumns_independent: proof_shape: bind-only; escape_witness: none; consumers: FrobeniusCholeskyLinear.selectedIndices_card, FrobeniusCholeskyResult.kernelRecipeChoice_spec
selectedColumns_span: proof_shape: bind-only; escape_witness: none; consumers: FrobeniusCholeskyLinear.selectedIndices_card, FrobeniusCholeskyLinear.selected_columns_reconstruct, FrobeniusCholeskyResult.kernelRecipeChoice_spec
selectedIndices_card: proof_shape: bind-only; escape_witness: none; consumers: FrobeniusCholeskyResult.kernelRecipeChoice_spec
selected_columns_reconstruct: proof_shape: bind-only; escape_witness: none; consumers: FrobeniusCholeskyResult.kernelRecipeChoice_spec
greedy_bounded: proof_shape: content; escape_witness: D5.S3.QuadraticForms.FrobeniusCholeskyLinear.greedy_bounded; consumers: FrobeniusCholeskyLinear.greedy_extension_span
greedy_extension_span: proof_shape: content; escape_witness: D5.S3.QuadraticForms.FrobeniusCholeskyLinear.greedy_bounded; consumers: FrobeniusCholeskyLinear.adaptedIndices_spec
greedy_extension_card: proof_shape: content; escape_witness: D5.S3.QuadraticForms.FrobeniusCholeskyLinear.greedy_independent; consumers: FrobeniusCholeskyLinear.adaptedIndices_spec
minorRowCodes: proof_shape: bind-only; escape_witness: none; consumers: FrobeniusCholeskyLinear.firstMinorRows, FrobeniusCholeskyLinear.firstMinorRows_det, FrobeniusCholeskyLinear.minorRowCodesNonempty
minorRowCodesNonempty: proof_shape: bind-only; escape_witness: none; consumers: FrobeniusCholeskyLinear.firstMinorRows, FrobeniusCholeskyLinear.firstMinorRows_det
firstMinorRows: proof_shape: bind-only; escape_witness: none; consumers: FrobeniusCholeskyLinear.firstMinorRows_det, FrobeniusCholeskyResult.pairLeaf_spec
firstMinorRows_det: proof_shape: bind-only; escape_witness: none; consumers: FrobeniusCholeskyResult.pairLeaf_spec
adaptedIndices_spec: proof_shape: content; escape_witness: D5.S3.QuadraticForms.FrobeniusCholeskyLinear.greedy_bounded; consumers: FrobeniusCholeskyResult.adaptedRecipeChoice_spec
-/

import D5.S3.Estimation.ExperimentCost.MinimumCostRoleBasis
import D5.S3.QuadraticForms.FrobeniusCholeskyRecipes

namespace D5.S3.QuadraticForms.FrobeniusCholeskyLinear

open D5.S3.Estimation.ExperimentCost.MinimumCostRoleBasis

open D5.S3.QuadraticForms.FrobeniusCholeskyRecipes

open scoped BigOperators Matrix

variable {m n r : ℕ} {F K : Type} [Field F] [Field K]

noncomputable def minorCoordinates (A : Matrix (Fin m) (Fin n) F)
    (I : Fin r → Fin m) (J : Fin r → Fin n) (v : Fin m → F) : Fin r → F :=
  (A.submatrix I J)⁻¹ *ᵥ (v ∘ I)

noncomputable def minorKernel (A : Matrix (Fin m) (Fin n) F)
    (I : Fin r → Fin m) (J : Fin r → Fin n) (j : Fin n) : Fin n → F :=
  Pi.single j 1 - ((1 : Matrix (Fin n) (Fin n) F).submatrix id J) *ᵥ minorCoordinates A I J (fun i => A i j)

private theorem mul_coordinateColumns (A : Matrix (Fin m) (Fin n) F)
    (J : Fin r → Fin n) :
    A * ((1 : Matrix (Fin n) (Fin n) F).submatrix id J) = A.submatrix id J := by
  exact Matrix.mul_submatrix_one (Equiv.refl (Fin n)) J A

private theorem minorCoordinates_reconstruct (A : Matrix (Fin m) (Fin n) F)
    (I : Fin r → Fin m) (J : Fin r → Fin n)
    (hdet : (A.submatrix I J).det ≠ 0)
    (hspan : ∀ j, ∃ a : Fin r → F, ∀ i, A i j = ∑ k, A i (J k) * a k)
    (j : Fin n) :
    (A.submatrix id J) *ᵥ minorCoordinates A I J (fun i => A i j) = fun i => A i j := by
  obtain ⟨a, ha⟩ := hspan j
  have hDa : (A.submatrix I J) *ᵥ a = (fun i => A i j) ∘ I := by
    funext k
    exact (ha (I k)).symm
  have hcoord : minorCoordinates A I J (fun i => A i j) = a := by
    rw [minorCoordinates, ← hDa, Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet), Matrix.one_mulVec]
  rw [hcoord]
  exact funext fun i => (ha i).symm

theorem minorKernel_mem (A : Matrix (Fin m) (Fin n) F)
    (I : Fin r → Fin m) (J : Fin r → Fin n)
    (hdet : (A.submatrix I J).det ≠ 0)
    (hspan : ∀ j, ∃ a : Fin r → F, ∀ i, A i j = ∑ k, A i (J k) * a k)
    (j : Fin n) : A *ᵥ minorKernel A I J j = 0 := by
  rw [minorKernel, Matrix.mulVec_sub, Matrix.mulVec_mulVec,
    mul_coordinateColumns, minorCoordinates_reconstruct A I J hdet hspan,
    Matrix.mulVec_single_one]
  ext i
  simp

private theorem minorKernel_free (A : Matrix (Fin m) (Fin n) F)
    (I : Fin r → Fin m) (J : Fin r → Fin n) (j l : Fin n)
    (hl : l ∉ Set.range J) :
    minorKernel A I J j l = (Pi.single j (1 : F) : Fin n → F) l := by
  have hzero : ∀ a, (1 : Matrix (Fin n) (Fin n) F) l (J a) = 0 := by
    intro a
    exact Matrix.one_apply_ne (fun he => hl ⟨a, he.symm⟩)
  change (Pi.single j (1 : F) : Fin n → F) l -
    (∑ a : Fin r, (1 : Matrix (Fin n) (Fin n) F) l (J a) *
      minorCoordinates A I J (fun i => A i j) a) =
        (Pi.single j (1 : F) : Fin n → F) l
  simp only [hzero, zero_mul, Finset.sum_const_zero, sub_zero]

private theorem kernel_zero_of_free_zero (A : Matrix (Fin m) (Fin n) F)
    (I : Fin r → Fin m) (J : Fin r → Fin n) (hJ : Function.Injective J)
    (hdet : (A.submatrix I J).det ≠ 0) (v : Fin n → F)
    (hv : A *ᵥ v = 0) (hfree : ∀ l, l ∉ Set.range J → v l = 0) : v = 0 := by
  have hsmall : (A.submatrix I J) *ᵥ (v ∘ J) = 0 := by
    funext a
    change (∑ b, A (I a) (J b) * v (J b)) = 0
    rw [Fintype.sum_of_injective J hJ
      (fun b => A (I a) (J b) * v (J b))
      (fun l => A (I a) l * v l)
      (fun l hl => by rw [hfree l hl, mul_zero]) (fun _ => rfl)]
    exact congrFun hv (I a)
  have hcoeff : v ∘ J = 0 := by
    exact Matrix.eq_zero_of_mulVec_eq_zero hdet hsmall
  funext l
  by_cases hl : l ∈ Set.range J
  · obtain ⟨a, rfl⟩ := hl
    exact congrFun hcoeff a
  · exact hfree l hl

private theorem sum_free_delta (J : Fin r → Fin n)
    (f : {j // j ∉ Set.range J} → F) (l : {j // j ∉ Set.range J}) :
    (∑ j, f j * (Pi.single j.val (1 : F) : Fin n → F) l.val) = f l := by
  classical
  calc
    _ = f l * (Pi.single l.val (1 : F) : Fin n → F) l.val :=
      Finset.sum_eq_single l (fun b _ hbl => by
        have hb : l.val ≠ b.val := fun h => hbl (Subtype.ext h.symm)
        simp [Pi.single_apply, hb]) (by simp)
    _ = f l := by simp

theorem minorKernel_span (A : Matrix (Fin m) (Fin n) F)
    (I : Fin r → Fin m) (J : Fin r → Fin n) (hJ : Function.Injective J)
    (hdet : (A.submatrix I J).det ≠ 0)
    (hspan : ∀ j, ∃ a : Fin r → F, ∀ i, A i j = ∑ k, A i (J k) * a k) :
    Submodule.span F (Set.range (fun j : {j // j ∉ Set.range J} => minorKernel A I J j.val)) =
      LinearMap.ker A.mulVecLin := by
  classical
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact minorKernel_mem A I J hdet hspan j.val
  · intro v hv
    rw [Submodule.mem_span_range_iff_exists_fun]
    refine ⟨fun j => v j.val, ?_⟩
    apply sub_eq_zero.mp
    apply kernel_zero_of_free_zero A I J hJ hdet
    · change A.mulVecLin _ = 0
      simp only [map_sub, map_sum, map_smul, Matrix.mulVecLin_apply,
        minorKernel_mem A I J hdet hspan, smul_zero, Finset.sum_const_zero,
        LinearMap.mem_ker.mp hv, sub_self]
    · intro l hl
      simp only [Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
        minorKernel_free A I J _ _ hl]
      exact sub_eq_zero.mpr (sum_free_delta J (fun j => v j.val) ⟨l, hl⟩)

noncomputable def frameTransport (P Q : Matrix (Fin m) (Fin r) F)
    (I : Fin r → Fin m) (v : Fin m → F) : Fin m → F :=
  Q *ᵥ minorCoordinates P I id v

private theorem frameCoordinates_left (P : Matrix (Fin m) (Fin r) F)
    (I : Fin r → Fin m) (hP : (P.submatrix I id).det ≠ 0) (a : Fin r → F) :
    minorCoordinates P I id (P *ᵥ a) = a := by
  have hrestrict : (P *ᵥ a) ∘ I = (P.submatrix I id) *ᵥ a := rfl
  rw [minorCoordinates, hrestrict, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hP), Matrix.one_mulVec]

private theorem frameTransport_apply (P Q : Matrix (Fin m) (Fin r) F)
    (I : Fin r → Fin m) (hP : (P.submatrix I id).det ≠ 0) (a : Fin r → F) :
    frameTransport P Q I (P *ᵥ a) = Q *ᵥ a := by
  rw [frameTransport, frameCoordinates_left P I hP]

private theorem frameTransport_range (P Q : Matrix (Fin m) (Fin r) F)
    (I : Fin r → Fin m) (v : Fin m → F) :
    frameTransport P Q I v ∈ LinearMap.range Q.mulVecLin := by
  exact ⟨minorCoordinates P I id v, rfl⟩

private theorem frameTransport_inverse (P Q : Matrix (Fin m) (Fin r) F)
    (I J : Fin r → Fin m)
    (hP : (P.submatrix I id).det ≠ 0) (hQ : (Q.submatrix J id).det ≠ 0)
    (v : Fin m → F) (hv : v ∈ LinearMap.range P.mulVecLin) :
    frameTransport Q P J (frameTransport P Q I v) = v := by
  obtain ⟨a, rfl⟩ := hv
  rw [Matrix.mulVecLin_apply, frameTransport_apply P Q I hP,
    frameTransport_apply Q P J hQ]

private theorem frameTransport_injective (P Q : Matrix (Fin m) (Fin r) F)
    (I J : Fin r → Fin m)
    (hP : (P.submatrix I id).det ≠ 0) (hQ : (Q.submatrix J id).det ≠ 0) :
    Set.InjOn (frameTransport P Q I) (LinearMap.range P.mulVecLin) := by
  intro v hv w hw he
  have h := congrArg (frameTransport Q P J) he
  simpa [frameTransport_inverse P Q I J hP hQ v hv,
    frameTransport_inverse P Q I J hP hQ w hw] using h

private theorem frameTransport_selected {k : ℕ}
    (P Q : Matrix (Fin m) (Fin r) F) (I : Fin r → Fin m)
    (hP : (P.submatrix I id).det ≠ 0) (S : Fin k → Fin r) (a : Fin k → F) :
    frameTransport P Q I ((P.submatrix id S) *ᵥ a) = (Q.submatrix id S) *ᵥ a := by
  rw [← mul_coordinateColumns P S, ← Matrix.mulVec_mulVec,
    frameTransport_apply P Q I hP, Matrix.mulVec_mulVec, mul_coordinateColumns]

private theorem frameTransport_selected_range_iff {k : ℕ}
    (P Q : Matrix (Fin m) (Fin r) F) (I J : Fin r → Fin m)
    (hP : (P.submatrix I id).det ≠ 0) (hQ : (Q.submatrix J id).det ≠ 0)
    (S : Fin k → Fin r) (v : Fin m → F)
    (hv : v ∈ LinearMap.range P.mulVecLin) :
    frameTransport P Q I v ∈ LinearMap.range (Q.submatrix id S).mulVecLin ↔
      v ∈ LinearMap.range (P.submatrix id S).mulVecLin := by
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a, ?_⟩
    have hh := congrArg (frameTransport Q P J) ha
    simpa only [Matrix.mulVecLin_apply, frameTransport_selected Q P J hQ,
      frameTransport_inverse P Q I J hP hQ v hv] using hh
  · rintro ⟨a, rfl⟩
    exact ⟨a, (frameTransport_selected P Q I hP S a).symm⟩

private theorem frameTransport_bijOn_range (P Q : Matrix (Fin m) (Fin r) F)
    (I J : Fin r → Fin m)
    (hP : (P.submatrix I id).det ≠ 0) (hQ : (Q.submatrix J id).det ≠ 0) :
    Set.BijOn (frameTransport P Q I) (LinearMap.range P.mulVecLin)
      (LinearMap.range Q.mulVecLin) := by
  refine ⟨fun v _ => frameTransport_range P Q I v,
    frameTransport_injective P Q I J hP hQ, ?_⟩
  rintro w ⟨a, rfl⟩
  exact ⟨P *ᵥ a, ⟨a, rfl⟩, frameTransport_apply P Q I hP a⟩

theorem adaptedFrame_transport {k : ℕ}
    (A U : Matrix (Fin m) (Fin m) F) (P Q : Matrix (Fin m) (Fin r) F)
    (I J : Fin r → Fin m) (S : Fin k → Fin r)
    (hP : (P.submatrix I id).det ≠ 0) (hQ : (Q.submatrix J id).det ≠ 0)
    (hPk : LinearMap.range P.mulVecLin = LinearMap.ker A.mulVecLin)
    (hQk : LinearMap.range Q.mulVecLin = LinearMap.ker U.transpose.mulVecLin)
    (hPs : LinearMap.range (P.submatrix id S).mulVecLin = LinearMap.range A.mulVecLin)
    (hQs : LinearMap.range (Q.submatrix id S).mulVecLin = LinearMap.range U.mulVecLin) :
    Set.BijOn (frameTransport P Q I) {v | A *ᵥ v = 0} {w | U.transpose *ᵥ w = 0} ∧
      ∀ v, A *ᵥ v = 0 →
        (frameTransport P Q I v ∈ LinearMap.range U.mulVecLin ↔
          v ∈ LinearMap.range A.mulVecLin) := by
  constructor
  · have hh := frameTransport_bijOn_range P Q I J hP hQ
    rw [hPk, hQk] at hh
    exact hh
  · intro v hv
    have hv' : v ∈ LinearMap.range P.mulVecLin := by
      rw [hPk]
      exact hv
    rw [← hQs, ← hPs]
    exact frameTransport_selected_range_iff P Q I J hP hQ S v hv'

open Set Submodule
open scoped Classical

variable {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]
    {ι : Type}

private theorem greedy_mono (v : ι → V) (l : List ι) (s : Finset ι) :
    s ⊆ greedyRoleScanFrom (K := F) v s l := by
  classical
  induction l generalizing s with
  | nil => exact fun _ h => h
  | cons i l ih =>
      dsimp only [greedyRoleScanFrom]
      split_ifs with h
      · exact (Finset.subset_insert i s).trans (ih (insert i s))
      · exact ih s

private theorem greedy_independent (v : ι → V) (l : List ι) (s : Finset ι)
    (hs : LinearIndepOn F v (s : Set ι)) :
    LinearIndepOn F v (greedyRoleScanFrom (K := F) v s l : Set ι) := by
  classical
  induction l generalizing s with
  | nil => exact hs
  | cons i l ih =>
      dsimp only [greedyRoleScanFrom]
      split_ifs with h
      · apply ih
        simpa only [linearRoleMatroid_indep_iff, Finset.coe_insert] using h
      · exact ih s hs

private theorem greedy_spans (v : ι → V) (l : List ι) (s : Finset ι)
    (hs : LinearIndepOn F v (s : Set ι)) :
    ∀ i ∈ l, v i ∈ span F (v '' (greedyRoleScanFrom (K := F) v s l : Set ι)) := by
  classical
  induction l generalizing s with
  | nil => simp
  | cons a l ih =>
      intro i hi
      dsimp only [greedyRoleScanFrom]
      split_ifs with ha
      · have hs' : LinearIndepOn F v ((insert a s : Finset ι) : Set ι) := by
          simpa only [linearRoleMatroid_indep_iff, Finset.coe_insert] using ha
        rcases List.mem_cons.mp hi with rfl | hi
        · apply subset_span
          exact ⟨i, greedy_mono (F := F) v l (insert i s) (Finset.mem_insert_self i s), rfl⟩
        · exact ih (insert a s) hs' i hi
      · have hv : v a ∈ span F (v '' (s : Set ι)) := by
          by_contra hv
          apply ha
          exact hs.insert hv
        rcases List.mem_cons.mp hi with rfl | hi
        · exact (span_mono (Set.image_mono (greedy_mono (F := F) v l s))) hv
        · exact ih s hs i hi


section BaseChange

variable {K : Type} [Field K] {m : ℕ}

end BaseChange

section Selection

variable {m n : ℕ}

theorem selectedColumns_independent (A : Matrix (Fin m) (Fin n) F) :
    LinearIndependent F (A.submatrix id ((((greedyRoleScanFrom (K := F) A.col ∅ (List.ofFn id))).orderEmbOfFin rfl))).col := by
  classical
  have hd : ∀ inst : DecidableEq (Fin n),
      @List.dedup (Fin n) inst (List.ofFn id) = List.ofFn id :=
    fun _ => List.dedup_eq_self.mpr (List.nodup_ofFn.mpr Function.injective_id)
  have h := (greedy_role_scan_is_minimum_cost_basis (K := F) A.col
    (fun _ => (0 : ℝ)) (List.ofFn id) (by simp) (by simp)).1.1
  have hs : LinearIndepOn F A.col
      (greedyRoleScanFrom (K := F) A.col ∅ (List.ofFn id) : Set (Fin n)) := by
    simpa only [greedyRoleScan, hd] using h
  exact hs.comp ((greedyRoleScanFrom (K := F) A.col ∅ (List.ofFn id)).orderIsoOfFin rfl)
    ((greedyRoleScanFrom (K := F) A.col ∅ (List.ofFn id)).orderIsoOfFin rfl).injective


theorem selectedColumns_span (A : Matrix (Fin m) (Fin n) F) :
    span F (Set.range (A.submatrix id ((((greedyRoleScanFrom (K := F) A.col ∅ (List.ofFn id))).orderEmbOfFin rfl))).col) =
      span F (Set.range A.col) := by
  classical
  have hd : ∀ inst : DecidableEq (Fin n),
      @List.dedup (Fin n) inst (List.ofFn id) = List.ofFn id :=
    fun _ => List.dedup_eq_self.mpr (List.nodup_ofFn.mpr Function.injective_id)
  have h := (greedy_role_scan_is_minimum_cost_basis (K := F) A.col
    (fun _ => (0 : ℝ)) (List.ofFn id) (by simp) (by simp)).1.2
  change span F (Set.range (A.col ∘
    ((greedyRoleScanFrom (K := F) A.col ∅ (List.ofFn id)).orderEmbOfFin rfl))) = _
  rw [Set.range_comp]
  simpa only [Finset.range_orderEmbOfFin, greedyRoleScan, hd] using h


theorem selectedIndices_card (A : Matrix (Fin m) (Fin n) F) :
    ((greedyRoleScanFrom (K := F) A.col ∅ (List.ofFn id))).card = A.rank := by
  calc
    ((greedyRoleScanFrom (K := F) A.col ∅ (List.ofFn id))).card =
        Module.finrank F (span F (Set.range (A.submatrix id ((((greedyRoleScanFrom (K := F) A.col ∅ (List.ofFn id))).orderEmbOfFin rfl))).col)) := by
          simpa using (finrank_span_eq_card (selectedColumns_independent A)).symm
    _ = A.rank := by rw [selectedColumns_span, Matrix.rank_eq_finrank_span_cols]

theorem selected_columns_reconstruct (A : Matrix (Fin m) (Fin n) F) :
    ∀ j, ∃ a : Fin ((greedyRoleScanFrom (K := F) A.col ∅ (List.ofFn id))).card → F,
      ∀ i, A i j = ∑ k, A i ((((greedyRoleScanFrom (K := F) A.col ∅ (List.ofFn id))).orderEmbOfFin rfl) k) * a k := by
  intro j
  have hj : A.col j ∈ span F (Set.range (A.submatrix id ((((greedyRoleScanFrom (K := F) A.col ∅ (List.ofFn id))).orderEmbOfFin rfl))).col) := by
    rw [selectedColumns_span]
    exact subset_span (Set.mem_range_self j)
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun F).mp hj
  refine ⟨a, ?_⟩
  intro i
  have h := congrFun ha i
  simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.col_apply,
    Matrix.submatrix_apply, id_eq, mul_comm] using h.symm

end Selection

private theorem greedy_bounded (v : ι → V) (l : List ι) (s : Finset ι) :
    greedyRoleScanFrom (K := F) v s l ⊆ s ∪ l.toFinset := by
  classical
  induction l generalizing s with
  | nil => simp [greedyRoleScanFrom]
  | cons i l ih =>
      dsimp only [greedyRoleScanFrom]
      split_ifs with hi
      · intro j hj
        have hh := ih (insert i s) hj
        simp only [Finset.mem_union, Finset.mem_insert] at hh
        simp only [List.toFinset_cons, Finset.mem_union, Finset.mem_insert]
        rcases hh with (rfl | hs) | hl
        · exact Or.inr (Or.inl rfl)
        · exact Or.inl hs
        · exact Or.inr (Or.inr hl)

      · intro j hj
        have hh := ih s hj
        simpa only [List.toFinset_cons, Finset.mem_union, Finset.mem_insert] using
          (show j ∈ s ∨ j = i ∨ j ∈ l.toFinset from (Finset.mem_union.mp hh).elim Or.inl (fun h => Or.inr (Or.inr h)))
private theorem greedy_extension_span (v : ι → V) (l : List ι) (s : Finset ι)
    (p : Submodule F V) (hs : ∀ i ∈ s, v i ∈ p) (hl : ∀ i ∈ l, v i ∈ p)
    (hI : LinearIndepOn F v (s : Set ι))
    (hspan : p ≤ span F (v '' (s : Set ι)) ⊔ span F (v '' (l.toFinset : Set ι))) :
    span F (v '' (greedyRoleScanFrom (K := F) v s l : Set ι)) = p := by
  classical
  apply le_antisymm
  · rw [span_le]
    rintro _ ⟨i, hi, rfl⟩
    have hh := greedy_bounded (F := F) v l s hi
    rcases Finset.mem_union.mp hh with his | hil
    · exact hs i his
    · exact hl i (List.mem_toFinset.mp hil)
  · refine hspan.trans (sup_le ?_ ?_)
    · exact span_mono (Set.image_mono (greedy_mono (F := F) v l s))
    · rw [span_le]
      rintro _ ⟨i, hi, rfl⟩
      exact greedy_spans (F := F) v l s hI i (List.mem_toFinset.mp hi)

private theorem greedy_extension_card (v : ι → V) (l : List ι) (s : Finset ι)
    (hs : LinearIndepOn F v (s : Set ι)) :
    (greedyRoleScanFrom (K := F) v s l).card =
      Module.finrank F (span F (v '' (greedyRoleScanFrom (K := F) v s l : Set ι))) := by
  classical
  have hh := greedy_independent v l s hs
  have he : Set.range (fun i : (greedyRoleScanFrom (K := F) v s l : Set ι) => v i.val) =
      v '' (greedyRoleScanFrom (K := F) v s l : Set ι) := by
    exact (image_eq_range v (greedyRoleScanFrom (K := F) v s l : Set ι)).symm
  have hh' : LinearIndependent F (fun i : (greedyRoleScanFrom (K := F) v s l : Set ι) => v i.val) := hh
  have hc := finrank_span_eq_card hh'
  rw [he] at hc
  simpa using hc.symm

noncomputable def minorRowCodes {m r : ℕ} (A : Matrix (Fin m) (Fin r) F) :
    Finset (Fin (Fintype.card (Fin r → Fin m))) := by
  classical
  exact Finset.univ.filter (fun i =>
    (A.submatrix ((Fintype.equivFin (Fin r → Fin m)).symm i) id).det ≠ 0)

theorem minorRowCodesNonempty {m r : ℕ} (A : Matrix (Fin m) (Fin r) F)
    (hA : LinearIndependent F A.col) : (minorRowCodes A).Nonempty := by
  classical
  obtain ⟨I, hI⟩ := (independent_columns_iff_minor A).mp hA
  refine ⟨Fintype.equivFin _ I, ?_⟩
  simpa [minorRowCodes] using hI

noncomputable def firstMinorRows {m r : ℕ} (A : Matrix (Fin m) (Fin r) F)
    (hA : LinearIndependent F A.col) : Fin r → Fin m :=
  (Fintype.equivFin (Fin r → Fin m)).symm
    ((minorRowCodes A).min' (minorRowCodesNonempty A hA))

theorem firstMinorRows_det {m r : ℕ} (A : Matrix (Fin m) (Fin r) F)
    (hA : LinearIndependent F A.col) :
    (A.submatrix (firstMinorRows A hA) id).det ≠ 0 := by
  classical
  have hh := Finset.min'_mem (minorRowCodes A) (minorRowCodesNonempty A hA)
  exact (Finset.mem_filter.mp hh).2


theorem adaptedIndices_spec {a b : ℕ} (v : Fin a → V) (w : Fin b → V)
    (hv : LinearIndependent F v) (p : Submodule F V)
    (hin : ∀ i, v i ∈ p) (hw : span F (Set.range w) = p) :
    Finset.univ.image Sum.inl ⊆ (greedyRoleScanFrom (K := F) (Sum.elim v w) (Finset.univ.image Sum.inl) (List.ofFn (fun j => Sum.inr j))) ∧
      LinearIndepOn F (Sum.elim v w) ((greedyRoleScanFrom (K := F) (Sum.elim v w) (Finset.univ.image Sum.inl) (List.ofFn (fun j => Sum.inr j))) : Set (Fin a ⊕ Fin b)) ∧
      span F ((Sum.elim v w) '' ((greedyRoleScanFrom (K := F) (Sum.elim v w) (Finset.univ.image Sum.inl) (List.ofFn (fun j => Sum.inr j))) : Set (Fin a ⊕ Fin b))) = p ∧
      ((greedyRoleScanFrom (K := F) (Sum.elim v w) (Finset.univ.image Sum.inl) (List.ofFn (fun j => Sum.inr j)))).card = Module.finrank F p := by
  classical
  let f : Fin a ⊕ Fin b → V := Sum.elim v w
  let s : Finset (Fin a ⊕ Fin b) := Finset.univ.image Sum.inl
  let l : List (Fin a ⊕ Fin b) := List.ofFn (fun j => Sum.inr j)
  have hs : LinearIndepOn F f (s : Set (Fin a ⊕ Fin b)) := by
    have hh := hv.linearIndepOn_univ.image_of_comp Sum.inl f
    simpa [s, Finset.coe_image] using hh
  have hsi : ∀ i ∈ s, f i ∈ p := by
    intro i hi
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hi
    exact hin j
  have hli : ∀ i ∈ l, f i ∈ p := by
    intro i hi
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hi
    rw [← hw]
    exact subset_span (Set.mem_range_self j)
  have hsp : p ≤ span F (f '' (s : Set (Fin a ⊕ Fin b))) ⊔
      span F (f '' (l.toFinset : Set (Fin a ⊕ Fin b))) := by
    rw [← hw]
    refine le_sup_of_le_right (span_mono ?_)
    rintro _ ⟨j, rfl⟩
    exact ⟨Sum.inr j, by simp [l], rfl⟩
  have he := greedy_extension_span f l s p hsi hli hs
    (by simpa only [List.coe_toFinset] using hsp)
  refine ⟨greedy_mono (F := F) f l s, greedy_independent f l s hs, he, ?_⟩
  change (greedyRoleScanFrom (K := F) f s l).card = Module.finrank F p
  have hc := greedy_extension_card f l s hs
  rw [he] at hc
  exact hc

open scoped Matrix BigOperators

end D5.S3.QuadraticForms.FrobeniusCholeskyLinear
