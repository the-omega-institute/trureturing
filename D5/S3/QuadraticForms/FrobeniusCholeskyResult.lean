/- GID: D5/S3/QuadraticForms/FrobeniusCholeskyResult
   generality: G
   mirror-B: D5/B/S3/QuadraticForms/FrobeniusCholeskyResult
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Arithmetic recipes and rank-preserving characteristic-two matrix fibers. -/

/-
admission_basis: open-problem-resolution (#23137; Proved)
admission_theorem: result
escape_witness: none
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/24291
The public claim uses the source fibers and finite arithmetic syntax.
Its recipe evaluation is Matrix.map; the construction uses coordinate choices and zero tests.
The dimension induction is uniform over all characteristic-two fields.
D5.S3.Estimation.ExperimentCost.MinimumCostRoleBasis.IsRoleBasis: declaration statement_id=sha256:a7314376031344f2fd7a2a51a1270cb9c1be00cdaf84d56088f3607048355fc9
D5.S3.Estimation.ExperimentCost.MinimumCostRoleBasis.greedyRoleScan: declaration statement_id=sha256:f8f5b6faba28894c2462b64069ba35b0e4908ae2401137bd295b01e330f23587
D5.S3.Estimation.ExperimentCost.MinimumCostRoleBasis.greedyRoleScanFrom: declaration statement_id=sha256:fc3d30f574cb1dbd5dfa4a6769a0de818a67ccb44cce89df5eb54722be0c56f0
D5.S3.Estimation.ExperimentCost.MinimumCostRoleBasis.greedy_role_scan_is_minimum_cost_basis: declaration statement_id=sha256:4debc8898102e484c0aa789cca28cb064e11fc67d13ff476986126cd1a63b2ae
D5.S3.Estimation.ExperimentCost.MinimumCostRoleBasis.instDecidableEq_d5: declaration statement_id=sha256:53fdb48bd71c5f81577fc7e746b20281fe7d85f5392a98f11c5ad17685672c41
D5.S3.Estimation.ExperimentCost.MinimumCostRoleBasis.linearRoleMatroid: declaration statement_id=sha256:fea38fa63812ff0931965c3ca5fff8c54b0df4f19d6347d8916075ccb52cc320
D5.S3.Estimation.ExperimentCost.MinimumCostRoleBasis.linearRoleMatroid_indep_iff: declaration statement_id=sha256:5bd8bf76d7da4d2c6c66e058e7ce532a9f2557b93a59861af15b5e438f71905b
D5.S3.Estimation.ExperimentCost.MinimumCostRoleBasis.linearRoleMatroid_indep_iff._simp_1: declaration statement_id=sha256:97ec095040d50375f35893dfbf385a37fd6e2c5ffa4be506d18d27651e8f11d9
FrameRecipe: proof_shape: bind-only; escape_witness: none; consumers: FrobeniusCholeskyResult.adaptedRecipeChoice, FrobeniusCholeskyResult.adaptedRecipeChoice_spec, FrobeniusCholeskyResult.kernelAfterImage, FrobeniusCholeskyResult.kernelRecipeChoice_spec, FrobeniusCholeskyResult.kernelTransportRecipes_spec, FrobeniusCholeskyResult.pairCodes, FrobeniusCholeskyResult.pairCodes_spec
adaptedRecipeChoice: proof_shape: bind-only; escape_witness: none; consumers: FrobeniusCholeskyResult.adaptedRecipeChoice_spec, FrobeniusCholeskyResult.kernelAfterImage, FrobeniusCholeskyResult.kernelRecipeChoice_spec
adaptedRecipeChoice_spec: proof_shape: content; escape_witness: none; consumers: FrobeniusCholeskyResult.kernelRecipeChoice_spec
KernelFrameRecipe: proof_shape: bind-only; escape_witness: none; consumers: FrobeniusCholeskyResult.kernelAfterImage, FrobeniusCholeskyResult.kernelAfterMinor, FrobeniusCholeskyResult.kernelRecipeChoice, FrobeniusCholeskyResult.kernelRecipeChoice_spec, FrobeniusCholeskyResult.kernelTransportChoice, FrobeniusCholeskyResult.kernelTransportRecipes_spec, FrobeniusCholeskyResult.pairCodes, FrobeniusCholeskyResult.pairCodes_spec
kernelAfterImage: proof_shape: bind-only; escape_witness: none; consumers: FrobeniusCholeskyResult.kernelAfterMinor, FrobeniusCholeskyResult.kernelRecipeChoice_spec
kernelAfterMinor: proof_shape: bind-only; escape_witness: none; consumers: FrobeniusCholeskyResult.kernelRecipeChoice, FrobeniusCholeskyResult.kernelRecipeChoice_spec
kernelRecipeChoice: proof_shape: bind-only; escape_witness: none; consumers: FrobeniusCholeskyResult.kernelRecipeChoice_spec, FrobeniusCholeskyResult.kernelTransportChoice, FrobeniusCholeskyResult.kernelTransportRecipes_spec
kernelRecipe_matches: proof_shape: content; escape_witness: none; consumers: FrobeniusCholeskyResult.kernelRecipeChoice_spec
kernelRecipeChoice_spec: proof_shape: content; escape_witness: none; consumers: FrobeniusCholeskyResult.kernelTransportRecipes_spec
recipeMul: proof_shape: bind-only; escape_witness: none; consumers: FrobeniusCholeskyResult.recipeMul_eval, FrobeniusCholeskyResult.transportMatrixRecipe, FrobeniusCholeskyResult.transportMatrixRecipe_apply
recipeMul_eval: proof_shape: bind-only; escape_witness: none; consumers: FrobeniusCholeskyResult.transportMatrixRecipe_apply
transportMatrixRecipe: proof_shape: bind-only; escape_witness: none; consumers: FrobeniusCholeskyResult.pairLeaf, FrobeniusCholeskyResult.pairLeaf_spec, FrobeniusCholeskyResult.transportMatrixRecipe_apply
transportMatrixRecipe_apply: proof_shape: content; escape_witness: none; consumers: FrobeniusCholeskyResult.pairLeaf_spec
pairLeaf: proof_shape: bind-only; escape_witness: none; consumers: FrobeniusCholeskyResult.pairCodes, FrobeniusCholeskyResult.pairCodes_spec, FrobeniusCholeskyResult.pairLeaf_spec
pairLeaf_spec: proof_shape: content; escape_witness: none; consumers: FrobeniusCholeskyResult.pairCodes_spec
pairCodes: proof_shape: bind-only; escape_witness: none; consumers: FrobeniusCholeskyResult.kernelTransportChoice, FrobeniusCholeskyResult.kernelTransportRecipes_spec, FrobeniusCholeskyResult.pairCodes_spec
pairCodes_spec: proof_shape: content; escape_witness: none; consumers: FrobeniusCholeskyResult.kernelTransportRecipes_spec
kernelTransportChoice: proof_shape: bind-only; escape_witness: none; consumers: FrobeniusCholeskyResult.kernelTransportRecipes, FrobeniusCholeskyResult.kernelTransportRecipes_spec
kernelTransportRecipes: proof_shape: bind-only; escape_witness: none; consumers: FrobeniusCholeskyResult.kernelTransportRecipes_spec, FrobeniusCholeskyResult.recursionColumn, FrobeniusCholeskyResult.recursionColumn_eval, FrobeniusCholeskyResult.recursionTransport_spec, FrobeniusCholeskyResult.uniform_rank_recipe
kernelTransportRecipes_spec: proof_shape: content; escape_witness: none; consumers: FrobeniusCholeskyResult.recursionTransport_spec
recursionColumn: proof_shape: bind-only; escape_witness: none; consumers: FrobeniusCholeskyResult.recursionColumn_eval, FrobeniusCholeskyResult.uniform_rank_recipe
recursionColumn_eval: proof_shape: content; escape_witness: none; consumers: FrobeniusCholeskyResult.uniform_rank_recipe
recursionTransport_spec: proof_shape: content; escape_witness: none; consumers: FrobeniusCholeskyResult.uniform_rank_recipe
uniform_rank_recipe: proof_shape: content; escape_witness: none; consumers: FrobeniusCholeskyResult.result
claim: proof_shape: bind-only; escape_witness: none; consumers: FrobeniusCholeskyResult.result
result: proof_shape: content; escape_witness: none; consumers: settling result
-/

import D5.S3.QuadraticForms.FrobeniusCholeskyRecipes
import D5.S3.Estimation.ExperimentCost.MinimumCostRoleBasis
import D5.S3.QuadraticForms.FrobeniusCholeskyLinear
import D5.S3.QuadraticForms.FrobeniusCholeskyRecursion

namespace D5.S3.QuadraticForms.FrobeniusCholeskyResult

open D5.S3.Estimation.ExperimentCost.MinimumCostRoleBasis

open D5.S3.QuadraticForms.FrobeniusCholeskyRecipes
open D5.S3.QuadraticForms.FrobeniusCholeskyLinear
open D5.S3.QuadraticForms.FrobeniusCholeskyRecursion

open Set Submodule

open scoped Matrix BigOperators

private structure FrameRecipe (n m a : ℕ) where
  d : ℕ
  frame : Matrix (Fin m) (Fin d) (Recipe n)
  rows : Fin d → Fin m
  inner : Fin a → Fin d

private noncomputable def adaptedRecipeChoice {n m a b : ℕ}
    (v : Fin a → Fin m → Recipe n) (w : Fin b → Fin m → Recipe n) :
    RecipeChoice n (Option (FrameRecipe n m a)) := by
  classical
  let z := Sum.elim v w
  let s : Finset (Fin a ⊕ Fin b) := Finset.univ.image Sum.inl
  let l : List (Fin a ⊕ Fin b) := List.ofFn (fun j => Sum.inr j)
  exact (greedyChoice z l s).bind fun t =>
    if ht : s ⊆ t then
      let P : Matrix (Fin m) (Fin t.card) (Recipe n) := fun i j => z (t.equivFin.symm j) i
      let S : Fin a → Fin t.card := fun j => t.equivFin ⟨Sum.inl j, ht (by simp [s])⟩
      (minorChoiceFrom m t.card P (rowChoices m t.card)).bind fun o =>
        .pure (o.map (fun I => ⟨t.card, P, I, S⟩))
    else .pure none

variable {n m a b : ℕ} {F : Type} [Field F] [DecidableEq F] [CharP F 2]

private theorem adaptedRecipeChoice_spec (X : Matrix (Fin n) (Fin n) F)
    (v : Fin a → Fin m → Recipe n) (w : Fin b → Fin m → Recipe n)
    (hv : LinearIndependent F (fun j i => (v j i).eval X))
    (p : Submodule F (Fin m → F))
    (hin : ∀ j, (fun i => (v j i).eval X) ∈ p)
    (hw : span F (Set.range (fun j i => (w j i).eval X)) = p) :
    ∃ c : FrameRecipe n m a,
      (adaptedRecipeChoice v w).evaluate X = some c ∧
      (((c.frame.map (Recipe.eval X)).submatrix c.rows id).det ≠ 0) ∧
      Function.Injective c.inner ∧
      span F (Set.range (c.frame.map (Recipe.eval X)).col) = p ∧
      (∀ j, (c.frame.map (Recipe.eval X)).col (c.inner j) = fun i => (v j i).eval X) ∧
      c.d = Module.finrank F p := by
  classical
  let ve : Fin a → Fin m → F := fun j i => (v j i).eval X
  let we : Fin b → Fin m → F := fun j i => (w j i).eval X
  let z := Sum.elim v w
  let ze := Sum.elim ve we
  let s : Finset (Fin a ⊕ Fin b) := Finset.univ.image Sum.inl
  let l : List (Fin a ⊕ Fin b) := List.ofFn (fun j => Sum.inr j)
  let t := (greedyRoleScanFrom (K := F) (Sum.elim ve we) (Finset.univ.image Sum.inl) (List.ofFn (fun j => Sum.inr j)))
  have ht := adaptedIndices_spec ve we hv p hin hw
  have hs : LinearIndepOn F ze (s : Set (Fin a ⊕ Fin b)) := by
    have hh := hv.linearIndepOn_univ.image_of_comp Sum.inl ze
    simpa [s, Finset.coe_image] using hh
  have hze : (fun j i => (z j i).eval X) = ze := by
    funext j i
    cases j <;> rfl
  have hg : (greedyChoice z l s).evaluate X = t := by
    rw [greedyChoice_eval X z l s (by simpa only [hze] using hs), hze]
  let e := t.equivFin.symm
  let P : Matrix (Fin m) (Fin t.card) (Recipe n) := fun i j => z (e j) i
  let S : Fin a → Fin t.card := fun j => t.equivFin ⟨Sum.inl j, ht.1 (by simp)⟩
  have hS : Function.Injective S := by
    intro j k hjk
    have hh := congrArg (fun q => (t.equivFin.symm q).val) hjk
    simpa only [S, Equiv.symm_apply_apply, Sum.inl.injEq] using hh
  have hPe : (P.map (Recipe.eval X)).col = (fun j => ze (e j)) := by
    funext j i
    change (z (e j) i).eval X = ze (e j) i
    exact congrFun (congrFun hze (e j)) i
  have hPi : LinearIndependent F (P.map (Recipe.eval X)).col := by
    rw [hPe]
    exact ht.2.1.comp e e.injective
  obtain ⟨I, hI, hdet⟩ := minorChoice_exists X m t.card P hPi
  let c : FrameRecipe n m a := ⟨t.card, P, I, S⟩
  have heval : (adaptedRecipeChoice v w).evaluate X = some c := by
    unfold adaptedRecipeChoice
    change ((greedyChoice z l s).bind _).evaluate X = some c
    rw [choice_bind_eval, hg, dif_pos ht.1]
    change ((minorChoiceFrom m t.card P (rowChoices m t.card)).bind _).evaluate X = some c
    rw [choice_bind_eval, hI]
    rfl
  have hr : Set.range (P.map (Recipe.eval X)).col = ze '' (t : Set (Fin a ⊕ Fin b)) := by
    rw [hPe]
    ext y
    constructor
    · rintro ⟨j, rfl⟩; exact ⟨(e j).val, (e j).property, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      refine ⟨t.equivFin ⟨j, hj⟩, ?_⟩
      simp [e]
  have hPv : ∀ j, (P.map (Recipe.eval X)).col (S j) = ve j := by
    intro j
    rw [hPe]
    simp [S, e, ze]
  refine ⟨c, heval, hdet, hS, ?_, hPv, ht.2.2.2⟩
  rw [hr]
  exact ht.2.2.1

open Set Submodule

open scoped Matrix BigOperators

private structure KernelFrameRecipe (n m : ℕ) where
  k : ℕ
  code : FrameRecipe n m k

private noncomputable def kernelAfterImage {n m : ℕ}
    (A M : Matrix (Fin m) (Fin m) (Recipe n))
    (t : Finset (Fin m)) (I : Fin t.card → Fin m) (s : Finset (Fin m)) :
    RecipeChoice n (Option (KernelFrameRecipe n m)) := by
  classical
  let J : Fin t.card → Fin m := t.orderEmbOfFin rfl
  let L : Fin s.card → Fin m := s.orderEmbOfFin rfl
  exact (adaptedRecipeChoice (fun j i => M i (L j))
    (fun j => recipeKernel A I J j)).bind fun f =>
      .pure (f.map (fun c => ⟨s.card, c⟩))

private noncomputable def kernelAfterMinor {n m : ℕ}
    (A M : Matrix (Fin m) (Fin m) (Recipe n)) (t : Finset (Fin m)) :
    Option (Fin t.card → Fin m) → RecipeChoice n (Option (KernelFrameRecipe n m))
  | none => .pure none
  | some I => (greedyChoice M.col (List.ofFn id) ∅).bind (kernelAfterImage A M t I)

private noncomputable def kernelRecipeChoice {n m : ℕ}
    (A M : Matrix (Fin m) (Fin m) (Recipe n)) :
    RecipeChoice n (Option (KernelFrameRecipe n m)) := by
  classical
  exact (greedyChoice A.col (List.ofFn id) ∅).bind fun t =>
    let J : Fin t.card → Fin m := t.orderEmbOfFin rfl
    (minorChoiceFrom m t.card (A.submatrix id J) (rowChoices m t.card)).bind
      (kernelAfterMinor A M t)

variable {n m : ℕ} {F : Type} [Field F] [DecidableEq F] [CharP F 2]

private theorem kernelRecipe_matches {r : ℕ} (X : Matrix (Fin n) (Fin n) F)
    (A : Matrix (Fin m) (Fin m) (Recipe n)) (I J : Fin r → Fin m) (j : Fin m) :
    (fun i => (recipeKernel A I J j i).eval X) = minorKernel (A.map (Recipe.eval X)) I J j := by
  rw [recipeKernel_eval]
  rfl

private theorem kernelRecipeChoice_spec (X : Matrix (Fin n) (Fin n) F)
    (A M : Matrix (Fin m) (Fin m) (Recipe n))
    (hAM : A.map (Recipe.eval X) * M.map (Recipe.eval X) = 0) :
    ∃ f : KernelFrameRecipe n m,
      (kernelRecipeChoice A M).evaluate X = some f ∧
      (((f.code.frame.map (Recipe.eval X)).submatrix f.code.rows id).det ≠ 0) ∧
      Function.Injective f.code.inner ∧
      LinearMap.range (f.code.frame.map (Recipe.eval X)).mulVecLin =
        LinearMap.ker (A.map (Recipe.eval X)).mulVecLin ∧
      LinearMap.range ((f.code.frame.map (Recipe.eval X)).submatrix id f.code.inner).mulVecLin =
        LinearMap.range (M.map (Recipe.eval X)).mulVecLin ∧
      f.code.d = m - (A.map (Recipe.eval X)).rank ∧
      f.k = (M.map (Recipe.eval X)).rank := by
  classical
  let Ae := A.map (Recipe.eval X)
  let Me := M.map (Recipe.eval X)
  let t := (greedyRoleScanFrom (K := F) Ae.col ∅ (List.ofFn id))
  let J := (((greedyRoleScanFrom (K := F) Ae.col ∅ (List.ofFn id))).orderEmbOfFin rfl)
  let s := (greedyRoleScanFrom (K := F) Me.col ∅ (List.ofFn id))
  let L := (((greedyRoleScanFrom (K := F) Me.col ∅ (List.ofFn id))).orderEmbOfFin rfl)
  have hgA : (greedyChoice A.col (List.ofFn id) ∅).evaluate X = t := by
    rw [greedyChoice_eval X A.col (List.ofFn id) ∅ (by simp)]
    rfl
  have hgM : (greedyChoice M.col (List.ofFn id) ∅).evaluate X = s := by
    rw [greedyChoice_eval X M.col (List.ofFn id) ∅ (by simp)]
    rfl
  have hAi : LinearIndependent F ((A.submatrix id J).map (Recipe.eval X)).col :=
    selectedColumns_independent Ae
  obtain ⟨I, hI, hdet⟩ := minorChoice_exists X m t.card (A.submatrix id J) hAi
  have hd : (Ae.submatrix I J).det ≠ 0 := hdet
  let v : Fin s.card → Fin m → Recipe n := fun j i => M i (L j)
  let w : Fin m → Fin m → Recipe n := fun j => recipeKernel A I J j
  have hv : LinearIndependent F (fun j i => (v j i).eval X) :=
    selectedColumns_independent Me
  have hin : ∀ j, (fun i => (v j i).eval X) ∈ LinearMap.ker Ae.mulVecLin := by
    intro j
    change Ae *ᵥ (fun i => Me i (L j)) = 0
    funext i
    exact congrFun (congrFun hAM i) (L j)
  have hwe : (fun j i => (w j i).eval X) = fun j => minorKernel Ae I J j := by
    funext j
    exact kernelRecipe_matches X A I J j
  have hw : span F (Set.range (fun j i => (w j i).eval X)) = LinearMap.ker Ae.mulVecLin := by
    rw [hwe]
    apply le_antisymm
    · rw [span_le]
      rintro _ ⟨j, rfl⟩
      exact minorKernel_mem Ae I J hd (selected_columns_reconstruct Ae) j
    · rw [← minorKernel_span Ae I J J.injective hd (selected_columns_reconstruct Ae)]
      exact span_mono (by rintro _ ⟨j, rfl⟩; exact ⟨j.val, rfl⟩)
  obtain ⟨c, hc, hcdet, hci, hcspan, hcinner, hcdim⟩ :=
    adaptedRecipeChoice_spec X v w hv (LinearMap.ker Ae.mulVecLin) hin hw
  let f : KernelFrameRecipe n m := ⟨s.card, c⟩
  have heval : (kernelRecipeChoice A M).evaluate X = some f := by
    unfold kernelRecipeChoice
    change ((greedyChoice A.col (List.ofFn id) ∅).bind _).evaluate X = some f
    rw [choice_bind_eval, hgA]
    change ((minorChoiceFrom m t.card (A.submatrix id J) (rowChoices m t.card)).bind
      (kernelAfterMinor A M t)).evaluate X = some f
    rw [choice_bind_eval, hI]
    change ((greedyChoice M.col (List.ofFn id) ∅).bind (kernelAfterImage A M t I)).evaluate X = some f
    rw [choice_bind_eval, hgM]
    unfold kernelAfterImage
    change ((adaptedRecipeChoice v w).bind _).evaluate X = some f
    rw [choice_bind_eval, hc]
    rfl
  have hker : LinearMap.range (c.frame.map (Recipe.eval X)).mulVecLin = LinearMap.ker Ae.mulVecLin := by
    rw [Matrix.range_mulVecLin, hcspan]
  have hinner : LinearMap.range ((c.frame.map (Recipe.eval X)).submatrix id c.inner).mulVecLin =
      LinearMap.range Me.mulVecLin := by
    rw [Matrix.range_mulVecLin, Matrix.range_mulVecLin]
    have he : ((c.frame.map (Recipe.eval X)).submatrix id c.inner).col =
        (Me.submatrix id L).col := funext hcinner
    rw [he]
    exact selectedColumns_span Me
  have hn := Ae.mulVecLin.finrank_range_add_finrank_ker
  have ht : Ae.rank + Module.finrank F (LinearMap.ker Ae.mulVecLin) = m := by
    simpa only [Matrix.rank, Module.finrank_pi, Module.finrank_self, Fintype.card_fin, mul_one] using hn
  refine ⟨f, heval, hcdet, hci, hker, hinner, ?_, selectedIndices_card Me⟩
  change c.d = m - Ae.rank
  omega

open scoped Matrix BigOperators

private def recipeMul {n a b c : ℕ} (A : Matrix (Fin a) (Fin b) (Recipe n))
    (D : Matrix (Fin b) (Fin c) (Recipe n)) : Matrix (Fin a) (Fin c) (Recipe n) :=
  fun i j => recipeMulVec A (fun k => D k j) i

private theorem recipeMul_eval {n a b c : ℕ} {F : Type} [Field F] [DecidableEq F]
    (X : Matrix (Fin n) (Fin n) F) (A : Matrix (Fin a) (Fin b) (Recipe n))
    (D : Matrix (Fin b) (Fin c) (Recipe n)) :
    (recipeMul A D).map (Recipe.eval X) = A.map (Recipe.eval X) * D.map (Recipe.eval X) := by
  ext i j
  exact congrFun (recipeMulVec_eval X A (fun k => D k j)) i

private noncomputable def transportMatrixRecipe {n m d : ℕ}
    (P Q : Matrix (Fin m) (Fin d) (Recipe n)) (I : Fin d → Fin m) :
    Matrix (Fin m) (Fin m) (Recipe n) :=
  recipeMul (recipeMul Q (recipeInverse d (P.submatrix I id)))
    (recipeCoordinateColumns I).transpose

variable {n m d k : ℕ} {F : Type} [Field F] [DecidableEq F] [CharP F 2]

private theorem transportMatrixRecipe_apply (X : Matrix (Fin n) (Fin n) F)
    (P Q : Matrix (Fin m) (Fin d) (Recipe n)) (I : Fin d → Fin m) (v : Fin m → F) :
    (transportMatrixRecipe P Q I).map (Recipe.eval X) *ᵥ v =
      frameTransport (P.map (Recipe.eval X)) (Q.map (Recipe.eval X)) I v := by
  have hrow : ((recipeCoordinateColumns (n := n) I).map (Recipe.eval X)).transpose *ᵥ v = v ∘ I := by
    rw [recipeCoordinateColumns_eval]
    funext i
    simp [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.submatrix_apply,
      Matrix.one_apply]
  simp only [transportMatrixRecipe, recipeMul_eval, recipeInverse_eval,
    Matrix.transpose_map, ← Matrix.mulVec_mulVec, hrow]
  rfl

private noncomputable def pairLeaf {n m d k : ℕ}
    (P Q : Matrix (Fin m) (Fin d) (Recipe n)) (I : Fin d → Fin m)
    (S T : Fin k → Fin d) : Matrix (Fin m) (Fin m) (Recipe n) := by
  classical
  exact if h : Function.Injective S ∧ Function.Injective T then
    let σ := Classical.choose (Equiv.Perm.exists_extending_pair S T h.1 h.2)
    transportMatrixRecipe P (Q.submatrix id σ) I
  else fun _ _ => .zero

private theorem pairLeaf_spec (X : Matrix (Fin n) (Fin n) F)
    (A U : Matrix (Fin m) (Fin m) F)
    (P Q : Matrix (Fin m) (Fin d) (Recipe n)) (I J : Fin d → Fin m)
    (S T : Fin k → Fin d)
    (hS : Function.Injective S) (hT : Function.Injective T)
    (hP : ((P.map (Recipe.eval X)).submatrix I id).det ≠ 0)
    (hQ : ((Q.map (Recipe.eval X)).submatrix J id).det ≠ 0)
    (hPk : LinearMap.range (P.map (Recipe.eval X)).mulVecLin = LinearMap.ker A.mulVecLin)
    (hQk : LinearMap.range (Q.map (Recipe.eval X)).mulVecLin = LinearMap.ker U.transpose.mulVecLin)
    (hPs : LinearMap.range ((P.map (Recipe.eval X)).submatrix id S).mulVecLin = LinearMap.range A.mulVecLin)
    (hQt : LinearMap.range ((Q.map (Recipe.eval X)).submatrix id T).mulVecLin = LinearMap.range U.mulVecLin) :
    Set.BijOn (fun v => (pairLeaf P Q I S T).map (Recipe.eval X) *ᵥ v)
      {v | A *ᵥ v = 0} {w | U.transpose *ᵥ w = 0} ∧
      ∀ v, A *ᵥ v = 0 →
        ((pairLeaf P Q I S T).map (Recipe.eval X) *ᵥ v ∈ LinearMap.range U.mulVecLin ↔
          v ∈ LinearMap.range A.mulVecLin) := by
  classical
  let σ := Classical.choose (Equiv.Perm.exists_extending_pair S T hS hT)
  have hσ : ∀ j, σ (S j) = T j := Classical.choose_spec
    (Equiv.Perm.exists_extending_pair S T hS hT)
  let Pe := P.map (Recipe.eval X)
  let Qe := Q.map (Recipe.eval X)
  let R := Qe.submatrix id σ
  have hRQ : Set.range R.col = Set.range Qe.col := by
    ext y
    constructor
    · rintro ⟨j, rfl⟩; exact ⟨σ j, rfl⟩
    · rintro ⟨j, rfl⟩
      refine ⟨σ.symm j, ?_⟩
      funext i
      change Qe i (σ (σ.symm j)) = Qe i j
      rw [Equiv.apply_symm_apply]
  have hRi : LinearIndependent F R.col := by
    exact ((independent_columns_iff_minor Qe).mpr ⟨J, hQ⟩).comp σ σ.injective
  let JR := firstMinorRows R hRi
  have hRk : LinearMap.range R.mulVecLin = LinearMap.ker U.transpose.mulVecLin := by
    rw [Matrix.range_mulVecLin, hRQ, ← Matrix.range_mulVecLin]
    exact hQk
  have hRs : R.submatrix id S = Qe.submatrix id T := by
    ext i j
    exact congrArg (Qe i) (hσ j)
  have hRs' : LinearMap.range (R.submatrix id S).mulVecLin = LinearMap.range U.mulVecLin := by
    rw [hRs]
    exact hQt
  have hh := adaptedFrame_transport A U Pe R I JR S hP (firstMinorRows_det R hRi)
    hPk hRk hPs hRs'
  have hleaf : pairLeaf P Q I S T = transportMatrixRecipe P (Q.submatrix id σ) I := by
    unfold pairLeaf
    exact dif_pos ⟨hS, hT⟩
  have he : (fun v => (pairLeaf P Q I S T).map (Recipe.eval X) *ᵥ v) =
      frameTransport Pe R I := by
    funext v
    rw [hleaf]
    exact transportMatrixRecipe_apply X P (Q.submatrix id σ) I v
  constructor
  · rw [he]
    exact hh.1
  · intro v hv
    rw [congrFun he v]
    exact hh.2 v hv

private noncomputable def pairCodes {n m : ℕ} (f g : KernelFrameRecipe n m) :
    Matrix (Fin m) (Fin m) (Recipe n) := by
  classical
  rcases f with ⟨k, ⟨d, P, I, S⟩⟩
  rcases g with ⟨k', ⟨d', Q, _, T⟩⟩
  exact if hd : d' = d then
    if hk : k' = k then
      pairLeaf P (Q.submatrix id (Fin.cast hd.symm)) I S
        (fun j => Fin.cast hd (T (Fin.cast hk.symm j)))
    else fun _ _ => .zero
  else fun _ _ => .zero

private theorem pairCodes_spec (X : Matrix (Fin n) (Fin n) F)
    (A U : Matrix (Fin m) (Fin m) F) (f g : KernelFrameRecipe n m)
    (hd : g.code.d = f.code.d) (hk : g.k = f.k)
    (hS : Function.Injective f.code.inner) (hT : Function.Injective g.code.inner)
    (hP : ((f.code.frame.map (Recipe.eval X)).submatrix f.code.rows id).det ≠ 0)
    (hQ : ((g.code.frame.map (Recipe.eval X)).submatrix g.code.rows id).det ≠ 0)
    (hPk : LinearMap.range (f.code.frame.map (Recipe.eval X)).mulVecLin = LinearMap.ker A.mulVecLin)
    (hQk : LinearMap.range (g.code.frame.map (Recipe.eval X)).mulVecLin = LinearMap.ker U.transpose.mulVecLin)
    (hPs : LinearMap.range ((f.code.frame.map (Recipe.eval X)).submatrix id f.code.inner).mulVecLin = LinearMap.range A.mulVecLin)
    (hQt : LinearMap.range ((g.code.frame.map (Recipe.eval X)).submatrix id g.code.inner).mulVecLin = LinearMap.range U.mulVecLin) :
    Set.BijOn (fun v => (pairCodes f g).map (Recipe.eval X) *ᵥ v)
      {v | A *ᵥ v = 0} {w | U.transpose *ᵥ w = 0} ∧
      ∀ v, A *ᵥ v = 0 →
        ((pairCodes f g).map (Recipe.eval X) *ᵥ v ∈ LinearMap.range U.mulVecLin ↔
          v ∈ LinearMap.range A.mulVecLin) := by
  classical
  rcases f with ⟨k, ⟨d, P, I, S⟩⟩
  rcases g with ⟨k', ⟨d', Q, J, T⟩⟩
  change d' = d at hd
  change k' = k at hk
  subst d'
  subst k'
  simpa [pairCodes] using pairLeaf_spec X A U P Q I J S T hS hT hP hQ hPk hQk hPs hQt

private noncomputable def kernelTransportChoice {n m : ℕ}
    (A U : Matrix (Fin m) (Fin m) (Recipe n)) :
    RecipeChoice n (Matrix (Fin m) (Fin m) (Recipe n)) :=
  (kernelRecipeChoice A A).bind fun of =>
    match of with
    | none => .pure (fun _ _ => .zero)
    | some f => (kernelRecipeChoice U.transpose U).bind fun og =>
      match og with
      | none => .pure (fun _ _ => .zero)
      | some g => .pure (pairCodes f g)

private noncomputable def kernelTransportRecipes {n m : ℕ}
    (A U : Matrix (Fin m) (Fin m) (Recipe n)) : Matrix (Fin m) (Fin m) (Recipe n) :=
  fun i j => ((kernelTransportChoice A U).bind (fun P => .pure (P i j))).reify

private theorem kernelTransportRecipes_spec (X : Matrix (Fin n) (Fin n) F)
    (A U : Matrix (Fin m) (Fin m) (Recipe n))
    (hA : A.map (Recipe.eval X) * A.map (Recipe.eval X) = 0)
    (hU : (U.map (Recipe.eval X)).transpose * U.map (Recipe.eval X) = 0)
    (hr : (U.map (Recipe.eval X)).rank = (A.map (Recipe.eval X)).rank) :
    Set.BijOn (fun v => (kernelTransportRecipes A U).map (Recipe.eval X) *ᵥ v)
      {v | A.map (Recipe.eval X) *ᵥ v = 0}
      {w | (U.map (Recipe.eval X)).transpose *ᵥ w = 0} ∧
      ∀ v, A.map (Recipe.eval X) *ᵥ v = 0 →
        ((kernelTransportRecipes A U).map (Recipe.eval X) *ᵥ v ∈
            LinearMap.range (U.map (Recipe.eval X)).mulVecLin ↔
          v ∈ LinearMap.range (A.map (Recipe.eval X)).mulVecLin) := by
  classical
  let Ae := A.map (Recipe.eval X)
  let Ue := U.map (Recipe.eval X)
  obtain ⟨f, hf, hP, hS, hPk, hPs, hd, hk⟩ := kernelRecipeChoice_spec X A A hA
  obtain ⟨g, hg, hQ, hT, hQk, hQt, hd', hk'⟩ :=
    kernelRecipeChoice_spec X U.transpose U hU
  have hdd : g.code.d = f.code.d := by
    rw [hd', Matrix.transpose_map, Matrix.rank_transpose, hr, hd]
  have hkk : g.k = f.k := by rw [hk', hr, hk]
  have hchoice : (kernelTransportChoice A U).evaluate X = pairCodes f g := by
    simp only [kernelTransportChoice, choice_bind_eval, hf, hg, RecipeChoice.evaluate]
  have he : (kernelTransportRecipes A U).map (Recipe.eval X) =
      (pairCodes f g).map (Recipe.eval X) := by
    ext i j
    change (((kernelTransportChoice A U).bind (fun P => .pure (P i j))).reify).eval X = _
    rw [choice_reify_eval, choice_bind_eval, hchoice]
    rfl
  rw [he]
  exact pairCodes_spec X Ae Ue f g hdd hkk hS hT hP hQ hPk hQk hPs hQt

open scoped Matrix BigOperators

private noncomputable def recursionColumn {n : ℕ} (p : Matrix (Fin n) (Fin n) (Recipe n)) :
    Fin n → Recipe (n+1) :=
  recipeMulVec (fun i j => Recipe.rename Fin.castSucc Fin.castSucc (kernelTransportRecipes (fun i j => Recipe.entry i j) p i j))
    (fun i => .entry i.castSucc (Fin.last n))

private theorem recursionColumn_eval {n : ℕ} {F : Type} [Field F] [DecidableEq F]
    (p : Matrix (Fin n) (Fin n) (Recipe n))
    (X : Matrix (Fin (n+1)) (Fin (n+1)) F) :
    (fun i => (recursionColumn p i).eval X) =
      ((((fun p => kernelTransportRecipes (fun i j => Recipe.entry i j) p) p)).map (Recipe.eval ((fun X : Matrix (Fin (n+1)) (Fin (n+1)) F => X.submatrix Fin.castSucc Fin.castSucc) X))) *ᵥ (fun X : Matrix (Fin (n+1)) (Fin (n+1)) F => fun i : Fin n => X i.castSucc (Fin.last n)) X := by
  let R : Matrix (Fin n) (Fin n) (Recipe (n+1)) :=
    fun i j => Recipe.rename Fin.castSucc Fin.castSucc (kernelTransportRecipes (fun i j => Recipe.entry i j) p i j)
  calc
    _ = R.map (Recipe.eval X) *ᵥ (fun X : Matrix (Fin (n+1)) (Fin (n+1)) F => fun i : Fin n => X i.castSucc (Fin.last n)) X :=
      recipeMulVec_eval X R (fun i => Recipe.entry i.castSucc (Fin.last n))
    _ = _ := by
      congr 1
      ext i j
      exact recipe_rename_eval X Fin.castSucc Fin.castSucc ((fun p => kernelTransportRecipes (fun i j => Recipe.entry i j) p) p i j)

private theorem recursionTransport_spec {n : ℕ} {F : Type} [Field F] [DecidableEq F] [CharP F 2]
    (p : Matrix (Fin n) (Fin n) (Recipe n)) (A : Matrix (Fin n) (Fin n) F)
    (hA : A ∈ B F n) (hU : ((p).map (Recipe.eval A)) ∈ C F n)
    (hr : (((p).map (Recipe.eval A))).rank = A.rank) :
    Set.BijOn (fun v => ((((fun p => kernelTransportRecipes (fun i j => Recipe.entry i j) p) p)).map (Recipe.eval A)) *ᵥ v)
      {v | A *ᵥ v = 0} {w | (((p).map (Recipe.eval A))).transpose *ᵥ w = 0} ∧
      ∀ v, A *ᵥ v = 0 →
        (((((fun p => kernelTransportRecipes (fun i j => Recipe.entry i j) p) p)).map (Recipe.eval A)) *ᵥ v ∈ LinearMap.range (((p).map (Recipe.eval A))).mulVecLin ↔
          v ∈ LinearMap.range A.mulVecLin) := by
  exact kernelTransportRecipes_spec A (fun i j => Recipe.entry i j) p hA.2 hU.2 hr

private theorem uniform_rank_recipe (n : ℕ) :
    ∃ p : Matrix (Fin n) (Fin n) (Recipe n),
      ∀ (F : Type) [Field F] [DecidableEq F] [CharP F 2],
        Set.BijOn ((fun X => (p).map (Recipe.eval X))) (B F n) (C F n) ∧
          ∀ X ∈ B F n, (((p).map (Recipe.eval X))).rank = X.rank := by
  classical
  induction n with
  | zero =>
    refine ⟨fun i _ => Fin.elim0 i, ?_⟩
    intro F instF instD instC
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · intro X _
      constructor
      · intro i
        exact Fin.elim0 i
      · ext i
        exact Fin.elim0 i
    · intro X _ Y _ _
      ext i
      exact Fin.elim0 i
    · intro U hU
      refine ⟨0, ?_, ?_⟩
      · constructor
        · intro i
          exact Fin.elim0 i
        · simp
      · ext i
        exact Fin.elim0 i
    · intro X _
      congr 1
      ext i
      exact Fin.elim0 i
  | succ n ih =>
    obtain ⟨p, hp⟩ := ih
    let q := recursionColumn p
    refine ⟨recursiveRecipe p q, ?_⟩
    intro F instF instD instC
    obtain ⟨hf, hr⟩ := hp F
    let f := (fun X => (p).map (Recipe.eval (F := F) X))
    let ψ : Matrix (Fin n) (Fin n) F → (Fin n → F) → (Fin n → F) :=
      fun A v => ((((fun p => kernelTransportRecipes (fun i j => Recipe.entry i j) p) p)).map (Recipe.eval A)) *ᵥ v
    have hψ : ∀ A ∈ B F n, Set.BijOn (ψ A)
        {v | A *ᵥ v = 0} {w | (f A).transpose *ᵥ w = 0} := by
      intro A hA
      exact (recursionTransport_spec p A hA (hf.mapsTo hA) (hr A hA)).1
    have hψr : ∀ A ∈ B F n, ∀ v, A *ᵥ v = 0 →
        (ψ A v ∈ LinearMap.range (f A).mulVecLin ↔ v ∈ LinearMap.range A.mulVecLin) := by
      intro A hA
      exact (recursionTransport_spec p A hA (hf.mapsTo hA) (hr A hA)).2
    have heq : ∀ X : Matrix (Fin (n+1)) (Fin (n+1)) F,
        (((recursiveRecipe p q)).map (Recipe.eval X)) = recursiveStep f ψ X := by
      intro X
      rw [recursiveRecipe_eval, recursionColumn_eval]
      rfl
    refine ⟨(recursiveStep_bijOn f ψ hf hψ).congr (fun X _ => (heq X).symm), ?_⟩
    intro X hX
    rw [heq]
    exact recursiveStep_rank f ψ hf.mapsTo hr hψr X hX

def claim : Prop :=
  ∀ e : ℕ, 1 ≤ e → ∀ n : ℕ,
    ∃ p : Matrix (Fin n) (Fin n) (Recipe n),
      ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F 2],
        Fintype.card F = 2 ^ e →
          Set.BijOn ((fun X => (p).map (Recipe.eval X))) (B F n) (C F n) ∧
          (∀ X : Matrix (Fin n) (Fin n) F,
            X ∈ B F n → (((p).map (Recipe.eval X))).rank = X.rank) ∧
          (∀ X : Matrix (Fin n) (Fin n) F,
            X ∈ B F n →
              ((p).map (Recipe.eval (X.map (frobenius F 2)))) = (((p).map (Recipe.eval X))).map (frobenius F 2))

theorem result : claim := by
  intro e he n
  obtain ⟨p, hp⟩ := uniform_rank_recipe n
  refine ⟨p, ?_⟩
  intro F instF instFin instD instC hcard
  exact ⟨(hp F).1, (hp F).2, fun X _ => recipe_map_frobenius X p⟩

end D5.S3.QuadraticForms.FrobeniusCholeskyResult
