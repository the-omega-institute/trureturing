/- GID: D5/S3/QuadraticForms/FrobeniusCholeskyRecipes
   generality: G
   mirror-B: D5/B/S3/QuadraticForms/FrobeniusCholeskyRecipes
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Arithmetic recipes and rank-preserving characteristic-two matrix fibers. -/

/-
admission_basis: escape-witness
admission_theorem: greedyChoice_eval
escape_witness: greedyChoice_eval
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/24291
Matrix recipe evaluation is Matrix.map composed with Recipe.eval.
The square-zero and Gram-zero fibers retain the source matrix conditions.
Coordinate recipes evaluate to identity submatrices; the seeded scan is greedyRoleScanFrom.
D5.S3.Estimation.ExperimentCost.MinimumCostRoleBasis.greedyRoleScanFrom: declaration statement_id=sha256:fc3d30f574cb1dbd5dfa4a6769a0de818a67ccb44cce89df5eb54722be0c56f0
D5.S3.Estimation.ExperimentCost.MinimumCostRoleBasis.instDecidableEq_d5: declaration statement_id=sha256:53fdb48bd71c5f81577fc7e746b20281fe7d85f5392a98f11c5ad17685672c41
D5.S3.Estimation.ExperimentCost.MinimumCostRoleBasis.linearRoleMatroid: declaration statement_id=sha256:fea38fa63812ff0931965c3ca5fff8c54b0df4f19d6347d8916075ccb52cc320
D5.S3.Estimation.ExperimentCost.MinimumCostRoleBasis.linearRoleMatroid_indep_iff._simp_1: declaration statement_id=sha256:97ec095040d50375f35893dfbf385a37fd6e2c5ffa4be506d18d27651e8f11d9
B: proof_shape: bind-only; escape_witness: none; consumers: FrobeniusCholeskyRecursion.B_decompose, FrobeniusCholeskyRecursion.B_last_zero, FrobeniusCholeskyRecursion.mem_B_border_iff, FrobeniusCholeskyRecursion.recursiveStep_bijOn, FrobeniusCholeskyRecursion.recursiveStep_rank, FrobeniusCholeskyResult.claim, FrobeniusCholeskyResult.recursionTransport_spec, FrobeniusCholeskyResult.result, FrobeniusCholeskyResult.uniform_rank_recipe
C: proof_shape: bind-only; escape_witness: none; consumers: FrobeniusCholeskyRecursion.C_decompose, FrobeniusCholeskyRecursion.mem_C_border_iff, FrobeniusCholeskyRecursion.recursiveStep_bijOn, FrobeniusCholeskyRecursion.recursiveStep_rank, FrobeniusCholeskyResult.claim, FrobeniusCholeskyResult.recursionTransport_spec, FrobeniusCholeskyResult.result, FrobeniusCholeskyResult.uniform_rank_recipe
Recipe: proof_shape: bind-only; escape_witness: none; consumers: FrobeniusCholeskyRecipes.Recipe.eval, FrobeniusCholeskyRecipes.Recipe.firstNonzero, FrobeniusCholeskyRecipes.Recipe.sum, FrobeniusCholeskyRecipes.RecipeChoice.bind, FrobeniusCholeskyRecipes.RecipeChoice.evaluate, FrobeniusCholeskyRecipes.RecipeChoice.reify, FrobeniusCholeskyRecipes.candidateRecipes, FrobeniusCholeskyRecipes.candidate_independent_iff, FrobeniusCholeskyRecipes.choice_bind_eval, FrobeniusCholeskyRecipes.choice_reify_eval, FrobeniusCholeskyRecipes.firstNonzero_eval, FrobeniusCholeskyRecipes.greedyChoice, FrobeniusCholeskyRecipes.greedyChoice_eval, FrobeniusCholeskyRecipes.minorChoiceFrom, FrobeniusCholeskyRecipes.minorChoice_exists, FrobeniusCholeskyRecipes.minorChoice_none_iff, FrobeniusCholeskyRecipes.minorChoice_sound, FrobeniusCholeskyRecipes.minorConditional, FrobeniusCholeskyRecipes.minorConditional_eval, FrobeniusCholeskyRecipes.recipeAdjugate, FrobeniusCholeskyRecipes.recipeAdjugate_eval, FrobeniusCholeskyRecipes.recipeCoordinateColumns, FrobeniusCholeskyRecipes.recipeCoordinateColumns_eval, FrobeniusCholeskyRecipes.recipeDet, FrobeniusCholeskyRecipes.recipeDet_eval, FrobeniusCholeskyRecipes.recipeInverse, FrobeniusCholeskyRecipes.recipeInverse_eval, FrobeniusCholeskyRecipes.recipeKernel, FrobeniusCholeskyRecipes.recipeKernel_eval, FrobeniusCholeskyRecipes.recipeMulVec, FrobeniusCholeskyRecipes.recipeMulVec_eval, FrobeniusCholeskyRecipes.recipe_eval_map, FrobeniusCholeskyRecipes.recipe_map_frobenius, FrobeniusCholeskyRecipes.recipe_map_map, FrobeniusCholeskyRecipes.recipe_sum_eval, FrobeniusCholeskyRecursion.Recipe.rename, FrobeniusCholeskyRecursion.recipe_rename_eval, FrobeniusCholeskyRecursion.recursiveRecipe, FrobeniusCholeskyRecursion.recursiveRecipe_eval, FrobeniusCholeskyResult.adaptedRecipeChoice, FrobeniusCholeskyResult.adaptedRecipeChoice_spec, FrobeniusCholeskyResult.claim, FrobeniusCholeskyResult.kernelAfterImage, FrobeniusCholeskyResult.kernelAfterMinor, FrobeniusCholeskyResult.kernelRecipeChoice, FrobeniusCholeskyResult.kernelRecipeChoice_spec, FrobeniusCholeskyResult.kernelRecipe_matches, FrobeniusCholeskyResult.kernelTransportChoice, FrobeniusCholeskyResult.kernelTransportRecipes, FrobeniusCholeskyResult.kernelTransportRecipes_spec, FrobeniusCholeskyResult.pairCodes, FrobeniusCholeskyResult.pairCodes_spec, FrobeniusCholeskyResult.pairLeaf, FrobeniusCholeskyResult.pairLeaf_spec, FrobeniusCholeskyResult.recipeMul, FrobeniusCholeskyResult.recipeMul_eval, FrobeniusCholeskyResult.recursionColumn, FrobeniusCholeskyResult.recursionColumn_eval, FrobeniusCholeskyResult.recursionTransport_spec, FrobeniusCholeskyResult.result, FrobeniusCholeskyResult.transportMatrixRecipe, FrobeniusCholeskyResult.transportMatrixRecipe_apply, FrobeniusCholeskyResult.uniform_rank_recipe
Recipe.eval: proof_shape: bind-only; escape_witness: none; consumers: FrobeniusCholeskyRecipes.RecipeChoice.evaluate, FrobeniusCholeskyRecipes.candidate_independent_iff, FrobeniusCholeskyRecipes.choice_bind_eval, FrobeniusCholeskyRecipes.choice_reify_eval, FrobeniusCholeskyRecipes.firstNonzero_eval, FrobeniusCholeskyRecipes.greedyChoice_eval, FrobeniusCholeskyRecipes.minorChoice_exists, FrobeniusCholeskyRecipes.minorChoice_none_iff, FrobeniusCholeskyRecipes.minorChoice_sound, FrobeniusCholeskyRecipes.minorConditional_eval, FrobeniusCholeskyRecipes.recipeAdjugate_eval, FrobeniusCholeskyRecipes.recipeCoordinateColumns_eval, FrobeniusCholeskyRecipes.recipeDet_eval, FrobeniusCholeskyRecipes.recipeInverse_eval, FrobeniusCholeskyRecipes.recipeKernel_eval, FrobeniusCholeskyRecipes.recipeMulVec_eval, FrobeniusCholeskyRecipes.recipe_eval_map, FrobeniusCholeskyRecipes.recipe_map_frobenius, FrobeniusCholeskyRecipes.recipe_map_map, FrobeniusCholeskyRecipes.recipe_sum_eval, FrobeniusCholeskyRecursion.recipe_rename_eval, FrobeniusCholeskyRecursion.recursiveRecipe_eval, FrobeniusCholeskyResult.adaptedRecipeChoice_spec, FrobeniusCholeskyResult.claim, FrobeniusCholeskyResult.kernelRecipeChoice_spec, FrobeniusCholeskyResult.kernelRecipe_matches, FrobeniusCholeskyResult.kernelTransportRecipes_spec, FrobeniusCholeskyResult.pairCodes_spec, FrobeniusCholeskyResult.pairLeaf_spec, FrobeniusCholeskyResult.recipeMul_eval, FrobeniusCholeskyResult.recursionColumn_eval, FrobeniusCholeskyResult.recursionTransport_spec, FrobeniusCholeskyResult.result, FrobeniusCholeskyResult.transportMatrixRecipe_apply, FrobeniusCholeskyResult.uniform_rank_recipe
recipe_eval_map: proof_shape: content; escape_witness: D5.S3.QuadraticForms.FrobeniusCholeskyRecipes.recipe_eval_map; consumers: FrobeniusCholeskyRecipes.recipe_map_map
recipe_map_map: proof_shape: content; escape_witness: D5.S3.QuadraticForms.FrobeniusCholeskyRecipes.recipe_eval_map; consumers: FrobeniusCholeskyRecipes.recipe_map_frobenius
recipe_map_frobenius: proof_shape: content; escape_witness: D5.S3.QuadraticForms.FrobeniusCholeskyRecipes.recipe_eval_map; consumers: FrobeniusCholeskyResult.result
Recipe.sum: proof_shape: bind-only; escape_witness: none; consumers: FrobeniusCholeskyRecipes.recipeDet, FrobeniusCholeskyRecipes.recipeDet_eval, FrobeniusCholeskyRecipes.recipeMulVec, FrobeniusCholeskyRecipes.recipeMulVec_eval, FrobeniusCholeskyRecipes.recipe_sum_eval, FrobeniusCholeskyRecursion.recursiveRecipe, FrobeniusCholeskyRecursion.recursiveRecipe_eval
recipe_sum_eval: proof_shape: bind-only; escape_witness: none; consumers: FrobeniusCholeskyRecipes.recipeDet_eval, FrobeniusCholeskyRecipes.recipeMulVec_eval, FrobeniusCholeskyRecursion.recursiveRecipe_eval
recipeDet: proof_shape: bind-only; escape_witness: none; consumers: FrobeniusCholeskyRecipes.minorChoiceFrom, FrobeniusCholeskyRecipes.minorChoice_none_iff, FrobeniusCholeskyRecipes.minorChoice_sound, FrobeniusCholeskyRecipes.minorConditional, FrobeniusCholeskyRecipes.minorConditional_eval, FrobeniusCholeskyRecipes.recipeAdjugate, FrobeniusCholeskyRecipes.recipeDet_eval, FrobeniusCholeskyRecipes.recipeInverse, FrobeniusCholeskyRecipes.recipeInverse_eval
recipeDet_eval: proof_shape: content; escape_witness: D5.S3.QuadraticForms.FrobeniusCholeskyRecipes.recipeDet_eval; consumers: FrobeniusCholeskyRecipes.minorChoice_none_iff, FrobeniusCholeskyRecipes.minorChoice_sound, FrobeniusCholeskyRecipes.minorConditional_eval, FrobeniusCholeskyRecipes.recipeAdjugate_eval, FrobeniusCholeskyRecipes.recipeInverse_eval
recipeAdjugate: proof_shape: bind-only; escape_witness: none; consumers: FrobeniusCholeskyRecipes.recipeAdjugate_eval, FrobeniusCholeskyRecipes.recipeInverse, FrobeniusCholeskyRecipes.recipeInverse_eval
recipeAdjugate_eval: proof_shape: content; escape_witness: D5.S3.QuadraticForms.FrobeniusCholeskyRecipes.recipeDet_eval; consumers: FrobeniusCholeskyRecipes.recipeInverse_eval
recipeInverse: proof_shape: bind-only; escape_witness: none; consumers: FrobeniusCholeskyRecipes.recipeInverse_eval, FrobeniusCholeskyRecipes.recipeKernel, FrobeniusCholeskyRecipes.recipeKernel_eval, FrobeniusCholeskyResult.transportMatrixRecipe, FrobeniusCholeskyResult.transportMatrixRecipe_apply
recipeInverse_eval: proof_shape: content; escape_witness: D5.S3.QuadraticForms.FrobeniusCholeskyRecipes.recipeDet_eval; consumers: FrobeniusCholeskyRecipes.recipeKernel_eval, FrobeniusCholeskyResult.transportMatrixRecipe_apply
independent_columns_iff_minor: proof_shape: bind-only; escape_witness: none; consumers: FrobeniusCholeskyLinear.minorRowCodesNonempty, FrobeniusCholeskyRecipes.minorChoice_exists, FrobeniusCholeskyRecipes.minorConditional_eval, FrobeniusCholeskyResult.pairLeaf_spec
rowChoices: proof_shape: bind-only; escape_witness: none; consumers: FrobeniusCholeskyRecipes.mem_rowChoices, FrobeniusCholeskyRecipes.minorChoice_exists, FrobeniusCholeskyRecipes.minorConditional, FrobeniusCholeskyRecipes.minorConditional_eval, FrobeniusCholeskyResult.adaptedRecipeChoice, FrobeniusCholeskyResult.adaptedRecipeChoice_spec, FrobeniusCholeskyResult.kernelRecipeChoice, FrobeniusCholeskyResult.kernelRecipeChoice_spec
mem_rowChoices: proof_shape: bind-only; escape_witness: none; consumers: FrobeniusCholeskyRecipes.minorChoice_exists, FrobeniusCholeskyRecipes.minorConditional_eval
Recipe.firstNonzero: proof_shape: bind-only; escape_witness: none; consumers: FrobeniusCholeskyRecipes.firstNonzero_eval, FrobeniusCholeskyRecipes.minorConditional, FrobeniusCholeskyRecipes.minorConditional_eval
firstNonzero_eval: proof_shape: content; escape_witness: D5.S3.QuadraticForms.FrobeniusCholeskyRecipes.firstNonzero_eval; consumers: FrobeniusCholeskyRecipes.minorConditional_eval
minorConditional: proof_shape: bind-only; escape_witness: none; consumers: FrobeniusCholeskyRecipes.greedyChoice, FrobeniusCholeskyRecipes.greedyChoice_eval, FrobeniusCholeskyRecipes.minorConditional_eval
minorConditional_eval: proof_shape: content; escape_witness: D5.S3.QuadraticForms.FrobeniusCholeskyRecipes.firstNonzero_eval; consumers: FrobeniusCholeskyRecipes.greedyChoice_eval
RecipeChoice: proof_shape: bind-only; escape_witness: none; consumers: FrobeniusCholeskyRecipes.RecipeChoice.bind, FrobeniusCholeskyRecipes.RecipeChoice.evaluate, FrobeniusCholeskyRecipes.RecipeChoice.reify, FrobeniusCholeskyRecipes.choice_bind_eval, FrobeniusCholeskyRecipes.choice_reify_eval, FrobeniusCholeskyRecipes.greedyChoice, FrobeniusCholeskyRecipes.greedyChoice_eval, FrobeniusCholeskyRecipes.minorChoiceFrom, FrobeniusCholeskyRecipes.minorChoice_none_iff, FrobeniusCholeskyRecipes.minorChoice_sound, FrobeniusCholeskyResult.adaptedRecipeChoice, FrobeniusCholeskyResult.adaptedRecipeChoice_spec, FrobeniusCholeskyResult.kernelAfterImage, FrobeniusCholeskyResult.kernelAfterMinor, FrobeniusCholeskyResult.kernelRecipeChoice, FrobeniusCholeskyResult.kernelRecipeChoice_spec, FrobeniusCholeskyResult.kernelTransportChoice, FrobeniusCholeskyResult.kernelTransportRecipes, FrobeniusCholeskyResult.kernelTransportRecipes_spec
RecipeChoice.evaluate: proof_shape: bind-only; escape_witness: none; consumers: FrobeniusCholeskyRecipes.choice_bind_eval, FrobeniusCholeskyRecipes.choice_reify_eval, FrobeniusCholeskyRecipes.greedyChoice_eval, FrobeniusCholeskyRecipes.minorChoice_exists, FrobeniusCholeskyRecipes.minorChoice_none_iff, FrobeniusCholeskyRecipes.minorChoice_sound, FrobeniusCholeskyResult.adaptedRecipeChoice_spec, FrobeniusCholeskyResult.kernelRecipeChoice_spec, FrobeniusCholeskyResult.kernelTransportRecipes_spec
RecipeChoice.reify: proof_shape: bind-only; escape_witness: none; consumers: FrobeniusCholeskyRecipes.choice_reify_eval, FrobeniusCholeskyResult.kernelTransportRecipes, FrobeniusCholeskyResult.kernelTransportRecipes_spec
choice_reify_eval: proof_shape: content; escape_witness: D5.S3.QuadraticForms.FrobeniusCholeskyRecipes.choice_reify_eval; consumers: FrobeniusCholeskyResult.kernelTransportRecipes_spec
RecipeChoice.bind: proof_shape: bind-only; escape_witness: none; consumers: FrobeniusCholeskyRecipes.choice_bind_eval, FrobeniusCholeskyResult.adaptedRecipeChoice, FrobeniusCholeskyResult.adaptedRecipeChoice_spec, FrobeniusCholeskyResult.kernelAfterImage, FrobeniusCholeskyResult.kernelAfterMinor, FrobeniusCholeskyResult.kernelRecipeChoice, FrobeniusCholeskyResult.kernelRecipeChoice_spec, FrobeniusCholeskyResult.kernelTransportChoice, FrobeniusCholeskyResult.kernelTransportRecipes, FrobeniusCholeskyResult.kernelTransportRecipes_spec
choice_bind_eval: proof_shape: content; escape_witness: D5.S3.QuadraticForms.FrobeniusCholeskyRecipes.choice_bind_eval; consumers: FrobeniusCholeskyResult.adaptedRecipeChoice_spec, FrobeniusCholeskyResult.kernelRecipeChoice_spec, FrobeniusCholeskyResult.kernelTransportRecipes_spec
minorChoiceFrom: proof_shape: bind-only; escape_witness: none; consumers: FrobeniusCholeskyRecipes.minorChoice_exists, FrobeniusCholeskyRecipes.minorChoice_none_iff, FrobeniusCholeskyRecipes.minorChoice_sound, FrobeniusCholeskyResult.adaptedRecipeChoice, FrobeniusCholeskyResult.adaptedRecipeChoice_spec, FrobeniusCholeskyResult.kernelRecipeChoice, FrobeniusCholeskyResult.kernelRecipeChoice_spec
minorChoice_none_iff: proof_shape: content; escape_witness: D5.S3.QuadraticForms.FrobeniusCholeskyRecipes.minorChoice_none_iff; consumers: FrobeniusCholeskyRecipes.minorChoice_exists
minorChoice_sound: proof_shape: content; escape_witness: D5.S3.QuadraticForms.FrobeniusCholeskyRecipes.minorChoice_sound; consumers: FrobeniusCholeskyRecipes.minorChoice_exists
minorChoice_exists: proof_shape: content; escape_witness: D5.S3.QuadraticForms.FrobeniusCholeskyRecipes.minorChoice_none_iff; consumers: FrobeniusCholeskyResult.adaptedRecipeChoice_spec, FrobeniusCholeskyResult.kernelRecipeChoice_spec
recipeMulVec: proof_shape: bind-only; escape_witness: none; consumers: FrobeniusCholeskyRecipes.recipeKernel, FrobeniusCholeskyRecipes.recipeKernel_eval, FrobeniusCholeskyRecipes.recipeMulVec_eval, FrobeniusCholeskyResult.recipeMul, FrobeniusCholeskyResult.recipeMul_eval, FrobeniusCholeskyResult.recursionColumn, FrobeniusCholeskyResult.recursionColumn_eval
recipeMulVec_eval: proof_shape: bind-only; escape_witness: none; consumers: FrobeniusCholeskyRecipes.recipeKernel_eval, FrobeniusCholeskyResult.recipeMul_eval, FrobeniusCholeskyResult.recursionColumn_eval
candidateRecipes: proof_shape: bind-only; escape_witness: none; consumers: FrobeniusCholeskyRecipes.candidate_independent_iff, FrobeniusCholeskyRecipes.greedyChoice, FrobeniusCholeskyRecipes.greedyChoice_eval
candidate_independent_iff: proof_shape: bind-only; escape_witness: none; consumers: FrobeniusCholeskyRecipes.greedyChoice_eval
greedyChoice: proof_shape: bind-only; escape_witness: none; consumers: FrobeniusCholeskyRecipes.greedyChoice_eval, FrobeniusCholeskyResult.adaptedRecipeChoice, FrobeniusCholeskyResult.adaptedRecipeChoice_spec, FrobeniusCholeskyResult.kernelAfterMinor, FrobeniusCholeskyResult.kernelRecipeChoice, FrobeniusCholeskyResult.kernelRecipeChoice_spec
greedyScanStep: proof_shape: bind-only; escape_witness: none; consumers: FrobeniusCholeskyRecipes.greedyChoice_eval
greedyChoice_eval: proof_shape: content; escape_witness: D5.S3.QuadraticForms.FrobeniusCholeskyRecipes.greedyChoice_eval; consumers: FrobeniusCholeskyResult.adaptedRecipeChoice_spec, FrobeniusCholeskyResult.kernelRecipeChoice_spec
recipeCoordinateColumns: proof_shape: bind-only; escape_witness: none; consumers: FrobeniusCholeskyRecipes.recipeCoordinateColumns_eval, FrobeniusCholeskyRecipes.recipeKernel, FrobeniusCholeskyRecipes.recipeKernel_eval, FrobeniusCholeskyResult.transportMatrixRecipe, FrobeniusCholeskyResult.transportMatrixRecipe_apply
recipeCoordinateColumns_eval: proof_shape: bind-only; escape_witness: none; consumers: FrobeniusCholeskyRecipes.recipeKernel_eval, FrobeniusCholeskyResult.transportMatrixRecipe_apply
recipeKernel: proof_shape: bind-only; escape_witness: none; consumers: FrobeniusCholeskyRecipes.recipeKernel_eval, FrobeniusCholeskyResult.kernelAfterImage, FrobeniusCholeskyResult.kernelRecipeChoice_spec, FrobeniusCholeskyResult.kernelRecipe_matches
recipeKernel_eval: proof_shape: content; escape_witness: D5.S3.QuadraticForms.FrobeniusCholeskyRecipes.recipeDet_eval; consumers: FrobeniusCholeskyResult.kernelRecipe_matches
-/

import D5.S3.Estimation.ExperimentCost.MinimumCostRoleBasis
import Mathlib.LinearAlgebra.Matrix.Nonsingular
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Algebra.CharP.Lemmas

namespace D5.S3.QuadraticForms.FrobeniusCholeskyRecipes



def B (F : Type) [Field F] (n : ℕ) : Set (Matrix (Fin n) (Fin n) F) :=
  {X | X.IsUpperTriangular ∧ X * X = 0}

def C (F : Type) [Field F] (n : ℕ) : Set (Matrix (Fin n) (Fin n) F) :=
  {U | U.IsUpperTriangular ∧ U.transpose * U = 0}

inductive Recipe (n : ℕ) : Type
  | zero : Recipe n
  | one : Recipe n
  | entry : Fin n → Fin n → Recipe n
  | add : Recipe n → Recipe n → Recipe n
  | mul : Recipe n → Recipe n → Recipe n
  | inv : Recipe n → Recipe n
  | iteZero : Recipe n → Recipe n → Recipe n → Recipe n

def Recipe.eval {n : ℕ} {F : Type} [Field F] [DecidableEq F]
    (X : Matrix (Fin n) (Fin n) F) : Recipe n → F
  | .zero => 0
  | .one => 1
  | .entry i j => X i j
  | .add a b => a.eval X + b.eval X
  | .mul a b => a.eval X * b.eval X
  | .inv a => (a.eval X)⁻¹
  | .iteZero a b c => if a.eval X = 0 then b.eval X else c.eval X


variable {n : ℕ} {F K : Type} [Field F] [Field K]
    [DecidableEq F] [DecidableEq K]

private theorem recipe_eval_map (σ : F →+* K)
    (X : Matrix (Fin n) (Fin n) F) (p : Recipe n) :
    p.eval (X.map σ) = σ (p.eval X) := by
  induction p with
  | zero => simp [Recipe.eval]
  | one => simp [Recipe.eval]
  | entry i j => rfl
  | add a b ha hb => simp [Recipe.eval, ha, hb]
  | mul a b ha hb => simp [Recipe.eval, ha, hb]
  | inv a ha => simp [Recipe.eval, ha]
  | iteZero a b c ha hb hc =>
      by_cases h : a.eval X = 0
      · simp [Recipe.eval, ha, hb, hc, h]
      · simp [Recipe.eval, ha, hb, hc, h]

private theorem recipe_map_map (σ : F →+* K)
    (X : Matrix (Fin n) (Fin n) F)
    (p : Matrix (Fin n) (Fin n) (Recipe n)) :
    ((p).map (Recipe.eval (X.map σ))) = (((p).map (Recipe.eval X))).map σ := by
  ext i j
  exact recipe_eval_map σ X (p i j)

theorem recipe_map_frobenius [CharP F 2]
    (X : Matrix (Fin n) (Fin n) F)
    (p : Matrix (Fin n) (Fin n) (Recipe n)) :
    ((p).map (Recipe.eval (X.map (frobenius F 2)))) =
      (((p).map (Recipe.eval X))).map (frobenius F 2) := by
  exact recipe_map_map (frobenius F 2) X p

open D5.S3.Estimation.ExperimentCost.MinimumCostRoleBasis

open scoped BigOperators Matrix

variable {n : ℕ} {F : Type} [Field F] [DecidableEq F]

def Recipe.sum (l : List (Recipe n)) : Recipe n :=
  l.foldr Recipe.add Recipe.zero

theorem recipe_sum_eval (X : Matrix (Fin n) (Fin n) F) (l : List (Recipe n)) :
    (Recipe.sum l).eval X = (l.map (Recipe.eval X)).sum := by
  exact (List.foldr_map_hom (g := Recipe.eval X)
    (f := Recipe.add) (f' := (· + ·)) (a := Recipe.zero) (l := l)
    (fun _ _ => rfl)).symm

def recipeDet : (r : ℕ) → Matrix (Fin r) (Fin r) (Recipe n) → Recipe n
  | 0, _ => .one
  | r+1, M => Recipe.sum (List.ofFn (fun j : Fin (r+1) =>
      .mul (M 0 j) (recipeDet r (M.submatrix Fin.succ j.succAbove))))

private theorem recipeDet_eval [CharP F 2] (X : Matrix (Fin n) (Fin n) F) :
    ∀ (r : ℕ) (M : Matrix (Fin r) (Fin r) (Recipe n)),
      (recipeDet r M).eval X = (M.map (Recipe.eval X)).det := by
  intro r
  induction r with
  | zero => intro M; simp [recipeDet, Recipe.eval, Matrix.det_isEmpty]
  | succ r ih =>
      intro M
      rw [recipeDet, recipe_sum_eval, Matrix.det_succ_row_zero]
      simp only [List.map_ofFn, List.sum_ofFn, Function.comp_def, Recipe.eval, ih,
        Matrix.map_apply, CharTwo.neg_eq, one_pow, one_mul]
      rfl

def recipeAdjugate : (r : ℕ) → Matrix (Fin r) (Fin r) (Recipe n) →
    Matrix (Fin r) (Fin r) (Recipe n)
  | 0, _ => Fin.elim0
  | r+1, M => fun i j => recipeDet r (M.submatrix j.succAbove i.succAbove)

private theorem recipeAdjugate_eval [CharP F 2] (X : Matrix (Fin n) (Fin n) F)
    (r : ℕ) (M : Matrix (Fin r) (Fin r) (Recipe n)) :
    (recipeAdjugate r M).map (Recipe.eval X) = (M.map (Recipe.eval X)).adjugate := by
  cases r with
  | zero => ext i; exact Fin.elim0 i
  | succ r =>
      ext i j
      rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
      simp only [CharTwo.neg_eq, one_pow, one_mul]
      change (recipeDet r (M.submatrix j.succAbove i.succAbove)).eval X = _
      exact recipeDet_eval X r _

def recipeInverse (r : ℕ) (M : Matrix (Fin r) (Fin r) (Recipe n)) :
    Matrix (Fin r) (Fin r) (Recipe n) :=
  fun i j => .mul (.inv (recipeDet r M)) (recipeAdjugate r M i j)

theorem recipeInverse_eval [CharP F 2] (X : Matrix (Fin n) (Fin n) F)
    (r : ℕ) (M : Matrix (Fin r) (Fin r) (Recipe n)) :
    (recipeInverse r M).map (Recipe.eval X) = (M.map (Recipe.eval X))⁻¹ := by
  ext i j
  simp only [recipeInverse, Matrix.map_apply, Recipe.eval, recipeDet_eval,
    Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply, smul_eq_mul]
  congr 1
  exact congrFun (congrFun (recipeAdjugate_eval X r M) i) j

theorem independent_columns_iff_minor {F : Type} [Field F]
    (A : Matrix (Fin m) (Fin r) F) :
    LinearIndependent F A.col ↔
      ∃ I : Fin r → Fin m, (A.submatrix I id).det ≠ 0 := by
  classical
  constructor
  · intro h
    have hfull : A.rank = r := by
      have hh : LinearIndependent F A.transpose.row := h
      simpa using hh.rank_matrix
    obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' F A.row
    letI : Fintype κ := Fintype.ofInjective a ha
    have hc : Fintype.card κ = r := by
      calc
        Fintype.card κ = Module.finrank F (Submodule.span F (Set.range (A.row ∘ a))) :=
          (finrank_span_eq_card hli).symm
        _ = A.rank := by rw [hspan, A.rank_eq_finrank_span_row]
        _ = r := hfull
    let e : Fin r ≃ κ := Fintype.equivOfCardEq (by simp [hc])
    refine ⟨a ∘ e, ?_⟩
    have hh : LinearIndependent F (A.submatrix (a ∘ e) id).row := by
      change LinearIndependent F (A.row ∘ a ∘ e)
      exact hli.comp e e.injective
    exact Matrix.nonsingular_iff_det_ne_zero.mp (.of_linearIndependent_row hh)
  · rintro ⟨I, hI⟩
    apply Matrix.mulVec_injective_iff.mp
    intro v w hvw
    apply Matrix.mulVec_injective_of_det_ne_zero hI
    funext i
    exact congrFun hvw (I i)

open scoped Classical

noncomputable def rowChoices (m r : ℕ) : List (Fin r → Fin m) :=
  List.ofFn (Fintype.equivFin (Fin r → Fin m)).symm

private theorem mem_rowChoices (m r : ℕ) (I : Fin r → Fin m) :
    I ∈ rowChoices m r := by
  apply List.mem_ofFn.mpr
  exact ⟨Fintype.equivFin _ I, (Fintype.equivFin _).symm_apply_apply I⟩

def Recipe.firstNonzero (tests : List (Recipe n)) (yes no : Recipe n) : Recipe n :=
  match tests with
  | [] => no
  | a :: l => .iteZero a (Recipe.firstNonzero l yes no) yes

private theorem firstNonzero_eval (X : Matrix (Fin n) (Fin n) F)
    (tests : List (Recipe n)) (yes no : Recipe n) :
    (Recipe.firstNonzero tests yes no).eval X =
      if ∃ a ∈ tests, a.eval X ≠ 0 then yes.eval X else no.eval X := by
  induction tests with
  | nil => simp [Recipe.firstNonzero]
  | cons a l ih =>
      by_cases ha : a.eval X = 0
      · simp [Recipe.firstNonzero, Recipe.eval, ha, ih]
      · simp [Recipe.firstNonzero, Recipe.eval, ha]

noncomputable def minorConditional (m r : ℕ)
    (M : Matrix (Fin m) (Fin r) (Recipe n)) (yes no : Recipe n) : Recipe n :=
  Recipe.firstNonzero ((rowChoices m r).map (fun I => recipeDet r (M.submatrix I id))) yes no

private theorem minorConditional_eval [CharP F 2]
    (X : Matrix (Fin n) (Fin n) F) (m r : ℕ)
    (M : Matrix (Fin m) (Fin r) (Recipe n)) (yes no : Recipe n) :
    (minorConditional m r M yes no).eval X =
      if LinearIndependent F (M.map (Recipe.eval X)).col
      then yes.eval X else no.eval X := by
  rw [minorConditional, firstNonzero_eval]
  have hh : (∃ a ∈ (rowChoices m r).map (fun I => recipeDet r (M.submatrix I id)),
      a.eval X ≠ 0) ↔ LinearIndependent F (M.map (Recipe.eval X)).col := by
    rw [independent_columns_iff_minor]
    constructor
    · rintro ⟨a, ha, hne⟩
      obtain ⟨I, _, rfl⟩ := List.mem_map.mp ha
      refine ⟨I, ?_⟩
      simpa only [recipeDet_eval, Matrix.submatrix_map] using hne
    · rintro ⟨I, hI⟩
      refine ⟨recipeDet r (M.submatrix I id), List.mem_map.mpr ⟨I, mem_rowChoices m r I, rfl⟩, ?_⟩
      simpa only [recipeDet_eval, Matrix.submatrix_map] using hI
  simp only [hh]

inductive RecipeChoice (n : ℕ) (α : Type) : Type
  | pure : α → RecipeChoice n α
  | branch : Recipe n → RecipeChoice n α → RecipeChoice n α → RecipeChoice n α

def RecipeChoice.evaluate {α : Type} (X : Matrix (Fin n) (Fin n) F) : RecipeChoice n α → α
  | .pure a => a
  | .branch a b c => if a.eval X = 0 then b.evaluate X else c.evaluate X

def RecipeChoice.reify : RecipeChoice n (Recipe n) → Recipe n
  | .pure a => a
  | .branch a b c => .iteZero a b.reify c.reify

theorem choice_reify_eval (X : Matrix (Fin n) (Fin n) F)
    (q : RecipeChoice n (Recipe n)) : q.reify.eval X = (q.evaluate X).eval X := by
  induction q with
  | pure a => rfl
  | branch a b c hb hc =>
      by_cases ha : a.eval X = 0 <;>
        simp [RecipeChoice.reify, RecipeChoice.evaluate, Recipe.eval, ha, hb, hc]

def RecipeChoice.bind {α β : Type} : RecipeChoice n α → (α → RecipeChoice n β) → RecipeChoice n β
  | .pure a, k => k a
  | .branch a b c, k => .branch a (b.bind k) (c.bind k)

theorem choice_bind_eval {α β : Type} (X : Matrix (Fin n) (Fin n) F)
    (q : RecipeChoice n α) (k : α → RecipeChoice n β) :
    (q.bind k).evaluate X = (k (q.evaluate X)).evaluate X := by
  induction q with
  | pure a => rfl
  | branch a b c hb hc =>
      by_cases ha : a.eval X = 0 <;> simp [RecipeChoice.bind, RecipeChoice.evaluate, ha, hb, hc]

def minorChoiceFrom (m r : ℕ) (M : Matrix (Fin m) (Fin r) (Recipe n)) :
    List (Fin r → Fin m) → RecipeChoice n (Option (Fin r → Fin m))
  | [] => .pure none
  | I :: l => .branch (recipeDet r (M.submatrix I id))
      (minorChoiceFrom m r M l) (.pure (some I))

private theorem minorChoice_none_iff [CharP F 2]
    (X : Matrix (Fin n) (Fin n) F) (m r : ℕ)
    (M : Matrix (Fin m) (Fin r) (Recipe n)) (l : List (Fin r → Fin m)) :
    (minorChoiceFrom m r M l).evaluate X = none ↔
      ∀ I ∈ l, ((M.map (Recipe.eval X)).submatrix I id).det = 0 := by
  induction l with
  | nil => simp [minorChoiceFrom, RecipeChoice.evaluate]
  | cons I l ih =>
      by_cases h : ((M.submatrix I id).map (Recipe.eval X)).det = 0
      · simpa [minorChoiceFrom, RecipeChoice.evaluate, recipeDet_eval, Matrix.submatrix_map, h] using ih
      · simp [minorChoiceFrom, RecipeChoice.evaluate, recipeDet_eval, Matrix.submatrix_map, h]

private theorem minorChoice_sound [CharP F 2]
    (X : Matrix (Fin n) (Fin n) F) (m r : ℕ)
    (M : Matrix (Fin m) (Fin r) (Recipe n)) (l : List (Fin r → Fin m))
    (I : Fin r → Fin m) (hI : (minorChoiceFrom m r M l).evaluate X = some I) :
    I ∈ l ∧ ((M.map (Recipe.eval X)).submatrix I id).det ≠ 0 := by
  induction l with
  | nil => simp [minorChoiceFrom, RecipeChoice.evaluate] at hI
  | cons J l ih =>
      by_cases h : ((M.submatrix J id).map (Recipe.eval X)).det = 0
      · have hh : (minorChoiceFrom m r M l).evaluate X = some I := by
          simpa [minorChoiceFrom, RecipeChoice.evaluate, recipeDet_eval, Matrix.submatrix_map, h] using hI
        exact ⟨List.mem_cons_of_mem J (ih hh).1, (ih hh).2⟩
      · have hh : J = I := by
          simpa [minorChoiceFrom, RecipeChoice.evaluate, recipeDet_eval, Matrix.submatrix_map, h] using hI
        subst I
        exact ⟨List.mem_cons_self, by simpa only [Matrix.submatrix_map] using h⟩

theorem minorChoice_exists [CharP F 2]
    (X : Matrix (Fin n) (Fin n) F) (m r : ℕ)
    (M : Matrix (Fin m) (Fin r) (Recipe n))
    (hM : LinearIndependent F (M.map (Recipe.eval X)).col) :
    ∃ I, (minorChoiceFrom m r M (rowChoices m r)).evaluate X = some I ∧
      ((M.map (Recipe.eval X)).submatrix I id).det ≠ 0 := by
  obtain ⟨J, hJ⟩ := (independent_columns_iff_minor _).mp hM
  cases he : (minorChoiceFrom m r M (rowChoices m r)).evaluate X with
  | none =>
      exact False.elim (hJ ((minorChoice_none_iff X m r M _).mp he J (mem_rowChoices m r J)))
  | some I => exact ⟨I, rfl, (minorChoice_sound X m r M _ I he).2⟩

def recipeMulVec {m r : ℕ} (A : Matrix (Fin m) (Fin r) (Recipe n))
    (v : Fin r → Recipe n) : Fin m → Recipe n :=
  fun i => Recipe.sum (List.ofFn (fun j => .mul (A i j) (v j)))

theorem recipeMulVec_eval {m r : ℕ} (X : Matrix (Fin n) (Fin n) F)
    (A : Matrix (Fin m) (Fin r) (Recipe n)) (v : Fin r → Recipe n) :
    (fun i => (recipeMulVec A v i).eval X) =
      A.map (Recipe.eval X) *ᵥ (fun j => (v j).eval X) := by
  funext i
  simp [recipeMulVec, recipe_sum_eval, Recipe.eval, Matrix.mulVec, dotProduct,
    List.map_ofFn, List.sum_ofFn, Function.comp_def]

section GreedyRecipes

variable {ι : Type}

noncomputable def candidateRecipes {m : ℕ} (v : ι → Fin m → Recipe n)
    (s : Finset ι) (i : ι) : Matrix (Fin m) (Fin (s.card+1)) (Recipe n) :=
  fun row col => Fin.cases (v i row)
    (fun a => v ((s.equivFin.symm a).val) row) col

private theorem candidate_independent_iff [CharP F 2] {m : ℕ}
    (X : Matrix (Fin n) (Fin n) F) (v : ι → Fin m → Recipe n) (s : Finset ι) (i : ι)
    (hs : LinearIndepOn F (fun j row => (v j row).eval X) (s : Set ι)) :
    LinearIndependent F ((candidateRecipes v s i).map (Recipe.eval X)).col ↔
      (fun row => (v i row).eval X) ∉
        Submodule.span F ((fun j row => (v j row).eval X) '' (s : Set ι)) := by
  classical
  let z : ↥s → Fin m → F := fun j row => (v j.val row).eval X
  let e := s.equivFin.symm
  have hz : LinearIndependent F (z ∘ e) := hs.comp e e.injective
  have hr : Set.range (z ∘ e) = (fun j row => (v j row).eval X) '' (s : Set ι) := by
    ext w
    constructor
    · rintro ⟨a, rfl⟩; exact ⟨(e a).val, (e a).property, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      refine ⟨s.equivFin ⟨j, hj⟩, ?_⟩
      simp [z, e]
  have hc : ((candidateRecipes v s i).map (Recipe.eval X)).col =
      Fin.cons (fun row => (v i row).eval X) (z ∘ e) := by
    ext j row
    refine Fin.cases ?_ (fun a => ?_) j <;> rfl
  rw [hc, linearIndependent_finCons, hr]
  exact and_iff_right hz

noncomputable def greedyChoice {m : ℕ} (v : ι → Fin m → Recipe n) :
    List ι → Finset ι → RecipeChoice n (Finset ι)
  | [], s => .pure s
  | i :: l, s => .branch
      (minorConditional m (s.card+1) (candidateRecipes v s i) .one .zero)
      (greedyChoice v l s) (greedyChoice v l (insert i s))

private theorem greedyScanStep {F : Type} [Field F]
    {V : Type} [AddCommGroup V] [Module F V]
    (v : ι → V) (l : List ι) (s : Finset ι) (i : ι)
    (hs : LinearIndepOn F v (s : Set ι)) :
    greedyRoleScanFrom (K := F) v s (i :: l) =
      if v i ∈ Submodule.span F (v '' (s : Set ι)) then
        greedyRoleScanFrom (K := F) v s l
      else greedyRoleScanFrom (K := F) v (insert i s) l := by
  classical
  by_cases h : v i ∈ Submodule.span F (v '' (s : Set ι))
  · by_cases hi : i ∈ s
    · simp [greedyRoleScanFrom, linearRoleMatroid_indep_iff, Finset.coe_insert,
        Finset.insert_eq_of_mem, Set.insert_eq_of_mem hi, hi, hs, h]
    · have hn : ¬ LinearIndepOn F v (insert i (s : Set ι)) := by
        intro hn
        exact hn.notMem_span_of_insert hi h
      simp [greedyRoleScanFrom, linearRoleMatroid_indep_iff, hn, h]
  · have hh := hs.insert h
    simp [greedyRoleScanFrom, linearRoleMatroid_indep_iff, hh, h]
    <;> rfl

theorem greedyChoice_eval [CharP F 2] {m : ℕ}
    (X : Matrix (Fin n) (Fin n) F) (v : ι → Fin m → Recipe n)
    (l : List ι) (s : Finset ι)
    (hs : LinearIndepOn F (fun j row => (v j row).eval X) (s : Set ι)) :
    (greedyChoice v l s).evaluate X =
      greedyRoleScanFrom (K := F) (fun j row => (v j row).eval X) s l := by
  classical
  induction l generalizing s with
  | nil => rfl
  | cons i l ih =>
      rw [greedyScanStep _ l s i hs]
      by_cases hi : (fun row => (v i row).eval X) ∈
          Submodule.span F ((fun j row => (v j row).eval X) '' (s : Set ι))
      · simpa [greedyChoice, RecipeChoice.evaluate, minorConditional_eval,
          candidate_independent_iff X v s i hs, hi, Recipe.eval] using ih s hs
      · have hs' : LinearIndepOn F (fun j row => (v j row).eval X) ((insert i s : Finset ι) : Set ι) := by
          simpa only [Finset.coe_insert] using hs.insert hi
        simpa [greedyChoice, RecipeChoice.evaluate, minorConditional_eval,
          candidate_independent_iff X v s i hs, hi, Recipe.eval] using ih (insert i s) hs'

end GreedyRecipes

def recipeCoordinateColumns {m r : ℕ} (J : Fin r → Fin m) :
    Matrix (Fin m) (Fin r) (Recipe n) :=
  fun i a => if i = J a then .one else .zero

theorem recipeCoordinateColumns_eval {m r : ℕ}
    (X : Matrix (Fin n) (Fin n) F) (J : Fin r → Fin m) :
    (recipeCoordinateColumns (n := n) J).map (Recipe.eval X) =
      ((1 : Matrix (Fin m) (Fin m) F).submatrix id J) := by
  classical
  ext i a
  by_cases h : i = J a <;> simp [recipeCoordinateColumns, Recipe.eval, Matrix.submatrix_apply, Matrix.one_apply, h, eq_comm]

def recipeKernel {m r : ℕ} (A : Matrix (Fin m) (Fin m) (Recipe n))
    (I J : Fin r → Fin m) (j : Fin m) : Fin m → Recipe n :=
  fun i => .add (if i = j then .one else .zero)
    (recipeMulVec (recipeCoordinateColumns J)
      (recipeMulVec (recipeInverse r (A.submatrix I J)) (fun a => A (I a) j)) i)

theorem recipeKernel_eval [CharP F 2] {m r : ℕ}
    (X : Matrix (Fin n) (Fin n) F) (A : Matrix (Fin m) (Fin m) (Recipe n))
    (I J : Fin r → Fin m) (j : Fin m) :
    (fun i => (recipeKernel A I J j i).eval X) =
      Pi.single j 1 -
        ((1 : Matrix (Fin m) (Fin m) F).submatrix id J) *ᵥ
          (((A.map (Recipe.eval X)).submatrix I J)⁻¹ *ᵥ
            (fun a => (A (I a) j).eval X)) := by
  classical
  have hinner := recipeMulVec_eval X (recipeInverse r (A.submatrix I J))
    (fun a => A (I a) j)
  rw [recipeInverse_eval, ← Matrix.submatrix_map] at hinner
  have hmul := recipeMulVec_eval X (recipeCoordinateColumns (n := n) J)
    (recipeMulVec (recipeInverse r (A.submatrix I J)) (fun a => A (I a) j))
  rw [hinner, recipeCoordinateColumns_eval] at hmul
  funext i
  have hbase : (if i = j then Recipe.one else Recipe.zero : Recipe n).eval X =
      (Pi.single j (1 : F) : Fin m → F) i := by
    by_cases h : i = j <;> simp [h, Recipe.eval, Pi.single_apply, eq_comm]
  change (if i = j then Recipe.one else Recipe.zero : Recipe n).eval X + _ = _
  rw [hbase, congrFun hmul i]
  exact (CharTwo.sub_eq_add _ _).symm

end D5.S3.QuadraticForms.FrobeniusCholeskyRecipes
