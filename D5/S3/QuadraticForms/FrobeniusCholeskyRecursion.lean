/- GID: D5/S3/QuadraticForms/FrobeniusCholeskyRecursion
   generality: G
   mirror-B: D5/B/S3/QuadraticForms/FrobeniusCholeskyRecursion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Arithmetic recipes and rank-preserving characteristic-two matrix fibers. -/

/-
admission_basis: escape-witness
admission_theorem: recursiveStep_bijOn
escape_witness: recursiveStep_bijOn
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/24291
The border uses Matrix.fromBlocks and finSumFinEquiv; zero extension uses LinearMap.pi.
The final diagonal is the sum of the final-column coordinates.
border: proof_shape: bind-only; escape_witness: none; consumers: FrobeniusCholeskyRecursion.B_decompose, FrobeniusCholeskyRecursion.C_decompose, FrobeniusCholeskyRecursion.border_cast_cast, FrobeniusCholeskyRecursion.border_cast_last, FrobeniusCholeskyRecursion.border_column_span, FrobeniusCholeskyRecursion.border_gram_cast_cast, FrobeniusCholeskyRecursion.border_gram_cast_last, FrobeniusCholeskyRecursion.border_gram_last_cast, FrobeniusCholeskyRecursion.border_gram_last_last, FrobeniusCholeskyRecursion.border_gram_zero_iff, FrobeniusCholeskyRecursion.border_last_cast, FrobeniusCholeskyRecursion.border_last_last, FrobeniusCholeskyRecursion.border_mul_cast_cast, FrobeniusCholeskyRecursion.border_mul_cast_last, FrobeniusCholeskyRecursion.border_rank, FrobeniusCholeskyRecursion.border_square_zero_iff, FrobeniusCholeskyRecursion.border_upper, FrobeniusCholeskyRecursion.border_upper_iff, FrobeniusCholeskyRecursion.finalColumn_border, FrobeniusCholeskyRecursion.gram_border_rank, FrobeniusCholeskyRecursion.mem_B_border_iff, FrobeniusCholeskyRecursion.mem_C_border_iff, FrobeniusCholeskyRecursion.principal_border, FrobeniusCholeskyRecursion.rebuild_upper, FrobeniusCholeskyRecursion.recursiveRecipe_eval, FrobeniusCholeskyRecursion.recursiveStep, FrobeniusCholeskyRecursion.recursiveStep_bijOn, FrobeniusCholeskyRecursion.recursiveStep_rank, FrobeniusCholeskyResult.uniform_rank_recipe
border_cast_cast: proof_shape: bind-only; escape_witness: none; consumers: FrobeniusCholeskyRecursion.border_column_span, FrobeniusCholeskyRecursion.border_gram_cast_cast, FrobeniusCholeskyRecursion.border_gram_cast_last, FrobeniusCholeskyRecursion.border_gram_last_cast, FrobeniusCholeskyRecursion.border_mul_cast_cast, FrobeniusCholeskyRecursion.border_mul_cast_last, FrobeniusCholeskyRecursion.border_upper, FrobeniusCholeskyRecursion.border_upper_iff, FrobeniusCholeskyRecursion.principal_border, FrobeniusCholeskyRecursion.rebuild_upper, FrobeniusCholeskyRecursion.recursiveRecipe_eval
border_cast_last: proof_shape: bind-only; escape_witness: none; consumers: FrobeniusCholeskyRecursion.border_column_span, FrobeniusCholeskyRecursion.border_gram_cast_last, FrobeniusCholeskyRecursion.border_gram_last_cast, FrobeniusCholeskyRecursion.border_gram_last_last, FrobeniusCholeskyRecursion.border_mul_cast_cast, FrobeniusCholeskyRecursion.border_mul_cast_last, FrobeniusCholeskyRecursion.finalColumn_border, FrobeniusCholeskyRecursion.rebuild_upper, FrobeniusCholeskyRecursion.recursiveRecipe_eval
border_last_cast: proof_shape: bind-only; escape_witness: none; consumers: FrobeniusCholeskyRecursion.border_column_span, FrobeniusCholeskyRecursion.border_gram_cast_cast, FrobeniusCholeskyRecursion.border_gram_cast_last, FrobeniusCholeskyRecursion.border_gram_last_cast, FrobeniusCholeskyRecursion.border_mul_cast_cast, FrobeniusCholeskyRecursion.border_upper, FrobeniusCholeskyRecursion.rebuild_upper, FrobeniusCholeskyRecursion.recursiveRecipe_eval
border_last_last: proof_shape: bind-only; escape_witness: none; consumers: FrobeniusCholeskyRecursion.border_column_span, FrobeniusCholeskyRecursion.border_gram_cast_last, FrobeniusCholeskyRecursion.border_gram_last_cast, FrobeniusCholeskyRecursion.border_gram_last_last, FrobeniusCholeskyRecursion.border_mul_cast_last, FrobeniusCholeskyRecursion.rebuild_upper, FrobeniusCholeskyRecursion.recursiveRecipe_eval
border_upper: proof_shape: bind-only; escape_witness: none; consumers: FrobeniusCholeskyRecursion.border_upper_iff
border_mul_cast_cast: proof_shape: bind-only; escape_witness: none; consumers: FrobeniusCholeskyRecursion.border_square_zero_iff
border_mul_cast_last: proof_shape: bind-only; escape_witness: none; consumers: FrobeniusCholeskyRecursion.border_square_zero_iff
border_gram_cast_cast: proof_shape: bind-only; escape_witness: none; consumers: FrobeniusCholeskyRecursion.border_gram_zero_iff
border_gram_cast_last: proof_shape: bind-only; escape_witness: none; consumers: FrobeniusCholeskyRecursion.border_gram_zero_iff
border_gram_last_last: proof_shape: bind-only; escape_witness: none; consumers: FrobeniusCholeskyRecursion.border_gram_zero_iff
last_diagonal_unique: proof_shape: bind-only; escape_witness: none; consumers: FrobeniusCholeskyRecursion.border_gram_zero_iff
border_gram_last_cast: proof_shape: bind-only; escape_witness: none; consumers: FrobeniusCholeskyRecursion.border_gram_zero_iff
border_gram_zero_iff: proof_shape: bind-only; escape_witness: none; consumers: FrobeniusCholeskyRecursion.mem_C_border_iff
border_square_zero_iff: proof_shape: bind-only; escape_witness: none; consumers: FrobeniusCholeskyRecursion.mem_B_border_iff
border_upper_iff: proof_shape: bind-only; escape_witness: none; consumers: FrobeniusCholeskyRecursion.mem_B_border_iff, FrobeniusCholeskyRecursion.mem_C_border_iff
mem_B_border_iff: proof_shape: bind-only; escape_witness: none; consumers: FrobeniusCholeskyRecursion.B_decompose, FrobeniusCholeskyRecursion.recursiveStep_bijOn
mem_C_border_iff: proof_shape: bind-only; escape_witness: none; consumers: FrobeniusCholeskyRecursion.C_decompose, FrobeniusCholeskyRecursion.recursiveStep_bijOn
embedLinear: proof_shape: bind-only; escape_witness: none; consumers: FrobeniusCholeskyRecursion.appendVec_mem_map_iff, FrobeniusCholeskyRecursion.border_column_span, FrobeniusCholeskyRecursion.border_rank, FrobeniusCholeskyRecursion.embedLinear_injective
embedLinear_injective: proof_shape: bind-only; escape_witness: none; consumers: FrobeniusCholeskyRecursion.border_rank
border_column_span: proof_shape: bind-only; escape_witness: none; consumers: FrobeniusCholeskyRecursion.border_rank
appendVec_mem_map_iff: proof_shape: bind-only; escape_witness: none; consumers: FrobeniusCholeskyRecursion.border_rank
border_rank: proof_shape: bind-only; escape_witness: none; consumers: FrobeniusCholeskyRecursion.gram_border_rank, FrobeniusCholeskyRecursion.recursiveStep_rank
sum_image_eq_zero: proof_shape: bind-only; escape_witness: none; consumers: FrobeniusCholeskyRecursion.gram_border_rank
gram_border_rank: proof_shape: bind-only; escape_witness: none; consumers: FrobeniusCholeskyRecursion.recursiveStep_rank
principal_border: proof_shape: bind-only; escape_witness: none; consumers: FrobeniusCholeskyRecursion.recursiveStep_bijOn
finalColumn_border: proof_shape: bind-only; escape_witness: none; consumers: FrobeniusCholeskyRecursion.recursiveStep_bijOn
rebuild_upper: proof_shape: bind-only; escape_witness: none; consumers: FrobeniusCholeskyRecursion.B_decompose, FrobeniusCholeskyRecursion.C_decompose
B_last_zero: proof_shape: bind-only; escape_witness: none; consumers: FrobeniusCholeskyRecursion.B_decompose
B_decompose: proof_shape: bind-only; escape_witness: none; consumers: FrobeniusCholeskyRecursion.recursiveStep_bijOn, FrobeniusCholeskyRecursion.recursiveStep_rank
C_decompose: proof_shape: bind-only; escape_witness: none; consumers: FrobeniusCholeskyRecursion.recursiveStep_bijOn
recursiveStep: proof_shape: bind-only; escape_witness: none; consumers: FrobeniusCholeskyRecursion.recursiveStep_bijOn, FrobeniusCholeskyRecursion.recursiveStep_rank, FrobeniusCholeskyResult.uniform_rank_recipe
recursiveStep_bijOn: proof_shape: content; escape_witness: D5.S3.QuadraticForms.FrobeniusCholeskyRecursion.recursiveStep_bijOn; consumers: FrobeniusCholeskyResult.uniform_rank_recipe
recursiveStep_rank: proof_shape: bind-only; escape_witness: none; consumers: FrobeniusCholeskyResult.uniform_rank_recipe
Recipe.rename: proof_shape: bind-only; escape_witness: none; consumers: FrobeniusCholeskyRecursion.recipe_rename_eval, FrobeniusCholeskyRecursion.recursiveRecipe, FrobeniusCholeskyRecursion.recursiveRecipe_eval, FrobeniusCholeskyResult.recursionColumn, FrobeniusCholeskyResult.recursionColumn_eval
recipe_rename_eval: proof_shape: content; escape_witness: D5.S3.QuadraticForms.FrobeniusCholeskyRecursion.recipe_rename_eval; consumers: FrobeniusCholeskyRecursion.recursiveRecipe_eval, FrobeniusCholeskyResult.recursionColumn_eval
recursiveRecipe: proof_shape: bind-only; escape_witness: none; consumers: FrobeniusCholeskyRecursion.recursiveRecipe_eval, FrobeniusCholeskyResult.uniform_rank_recipe
recursiveRecipe_eval: proof_shape: content; escape_witness: D5.S3.QuadraticForms.FrobeniusCholeskyRecursion.recipe_rename_eval; consumers: FrobeniusCholeskyResult.uniform_rank_recipe
-/

import D5.S3.QuadraticForms.FrobeniusCholeskyRecipes

namespace D5.S3.QuadraticForms.FrobeniusCholeskyRecursion

open D5.S3.QuadraticForms.FrobeniusCholeskyRecipes

open scoped BigOperators Matrix

variable {n : ℕ} {F : Type} [Field F]

def border (A : Matrix (Fin n) (Fin n) F) (w : Fin n → F) (c : F) :
    Matrix (Fin (n+1)) (Fin (n+1)) F :=
  (Matrix.fromBlocks A (Matrix.replicateCol (Fin 1) w)
    (0 : Matrix (Fin 1) (Fin n) F)
    (Matrix.replicateCol (Fin 1) (Function.const (Fin 1) c))).submatrix
      finSumFinEquiv.symm finSumFinEquiv.symm

@[simp] private theorem border_cast_cast (A : Matrix (Fin n) (Fin n) F)
    (w : Fin n → F) (c : F) (i j : Fin n) :
    border A w c i.castSucc j.castSucc = A i j := by
  simp [border]

@[simp] private theorem border_cast_last (A : Matrix (Fin n) (Fin n) F)
    (w : Fin n → F) (c : F) (i : Fin n) :
    border A w c i.castSucc (Fin.last n) = w i := by
  simp [border]

@[simp] private theorem border_last_cast (A : Matrix (Fin n) (Fin n) F)
    (w : Fin n → F) (c : F) (j : Fin n) :
    border A w c (Fin.last n) j.castSucc = 0 := by
  simp [border]

@[simp] private theorem border_last_last (A : Matrix (Fin n) (Fin n) F)
    (w : Fin n → F) (c : F) :
    border A w c (Fin.last n) (Fin.last n) = c := by
  simp [border]

private theorem border_upper (A : Matrix (Fin n) (Fin n) F)
    (w : Fin n → F) (c : F) (hA : A.IsUpperTriangular) :
    (border A w c).IsUpperTriangular := by
  intro i j
  refine Fin.lastCases ?_ (fun i => ?_) i
  · refine Fin.lastCases ?_ (fun j => ?_) j
    · intro hij; exact False.elim (lt_irrefl _ hij)
    · intro _; simp
  · refine Fin.lastCases ?_ (fun j => ?_) j
    · intro hij; exact False.elim (not_lt_of_ge (Fin.le_last _) hij)
    · intro hij; simpa using hA (Fin.castSucc_lt_castSucc_iff.mp hij)

private theorem border_mul_cast_cast (A D : Matrix (Fin n) (Fin n) F)
    (v w : Fin n → F) (c d : F) (i j : Fin n) :
    (border A v c * border D w d) i.castSucc j.castSucc = (A * D) i j := by
  simp [Matrix.mul_apply, Fin.sum_univ_castSucc]

private theorem border_mul_cast_last (A D : Matrix (Fin n) (Fin n) F)
    (v w : Fin n → F) (c d : F) (i : Fin n) :
    (border A v c * border D w d) i.castSucc (Fin.last n) =
      (A *ᵥ w) i + v i * d := by
  simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc]

private theorem border_gram_cast_cast (A : Matrix (Fin n) (Fin n) F)
    (w : Fin n → F) (c : F) (i j : Fin n) :
    ((border A w c).transpose * border A w c) i.castSucc j.castSucc =
      (A.transpose * A) i j := by
  simp [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_castSucc]

private theorem border_gram_cast_last (A : Matrix (Fin n) (Fin n) F)
    (w : Fin n → F) (c : F) (i : Fin n) :
    ((border A w c).transpose * border A w c) i.castSucc (Fin.last n) =
      (A.transpose *ᵥ w) i := by
  simp [Matrix.mul_apply, Matrix.transpose_apply, Matrix.mulVec, dotProduct,
    Fin.sum_univ_castSucc]

private theorem border_gram_last_last (A : Matrix (Fin n) (Fin n) F)
    (w : Fin n → F) (c : F) :
    ((border A w c).transpose * border A w c) (Fin.last n) (Fin.last n) =
      (∑ i, w i ^ 2) + c ^ 2 := by
  simp [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_castSucc, pow_two]

private theorem last_diagonal_unique [CharP F 2] (w : Fin n → F) (c : F) :
    (∑ i, w i ^ 2) + c ^ 2 = 0 ↔ c = ∑ i, w i := by
  rw [← CharTwo.sum_sq Finset.univ w, CharTwo.add_eq_zero]
  constructor
  · intro h
    exact (frobenius F 2).injective h.symm
  · intro h
    rw [h]

private theorem border_gram_last_cast (A : Matrix (Fin n) (Fin n) F)
    (w : Fin n → F) (c : F) (i : Fin n) :
    ((border A w c).transpose * border A w c) (Fin.last n) i.castSucc =
      (A.transpose *ᵥ w) i := by
  simp [Matrix.mul_apply, Matrix.transpose_apply, Matrix.mulVec, dotProduct,
    Fin.sum_univ_castSucc, mul_comm]

private theorem border_gram_zero_iff [CharP F 2]
    (A : Matrix (Fin n) (Fin n) F) (w : Fin n → F) (c : F) :
    (border A w c).transpose * border A w c = 0 ↔
      A.transpose * A = 0 ∧ A.transpose *ᵥ w = 0 ∧ c = ∑ i, w i := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · ext i j
      simpa [border_gram_cast_cast] using congrFun (congrFun h i.castSucc) j.castSucc
    · funext i
      simpa [border_gram_cast_last] using congrFun (congrFun h i.castSucc) (Fin.last n)
    · apply (last_diagonal_unique w c).mp
      simpa [border_gram_last_last] using congrFun (congrFun h (Fin.last n)) (Fin.last n)
  · rintro ⟨hA, hw, hc⟩
    ext i j
    refine Fin.lastCases ?_ (fun i => ?_) i
    · refine Fin.lastCases ?_ (fun j => ?_) j
      · simpa [border_gram_last_last] using (last_diagonal_unique w c).mpr hc
      · simpa [border_gram_last_cast] using congrFun hw j
    · refine Fin.lastCases ?_ (fun j => ?_) j
      · simpa [border_gram_cast_last] using congrFun hw i
      · simpa [border_gram_cast_cast] using congrFun (congrFun hA i) j

private theorem border_square_zero_iff (A : Matrix (Fin n) (Fin n) F)
    (v : Fin n → F) :
    border A v 0 * border A v 0 = 0 ↔ A * A = 0 ∧ A *ᵥ v = 0 := by
  constructor
  · intro h
    constructor
    · ext i j
      simpa [border_mul_cast_cast] using congrFun (congrFun h i.castSucc) j.castSucc
    · funext i
      simpa [border_mul_cast_last] using congrFun (congrFun h i.castSucc) (Fin.last n)
  · rintro ⟨hA, hv⟩
    ext i j
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simp [Matrix.mul_apply, Fin.sum_univ_castSucc, border]
    · refine Fin.lastCases ?_ (fun j => ?_) j
      · simpa [border_mul_cast_last] using congrFun hv i
      · simpa [border_mul_cast_cast] using congrFun (congrFun hA i) j

private theorem border_upper_iff (A : Matrix (Fin n) (Fin n) F)
    (v : Fin n → F) (c : F) :
    (border A v c).IsUpperTriangular ↔ A.IsUpperTriangular := by
  constructor
  · intro h i j hij
    rw [← border_cast_cast A v c i j]
    exact h hij
  · exact border_upper A v c

private theorem mem_B_border_iff (A : Matrix (Fin n) (Fin n) F) (v : Fin n → F) :
    border A v 0 ∈ B F (n+1) ↔ A ∈ B F n ∧ A *ᵥ v = 0 := by
  simp only [B, Set.mem_ofPred_eq, border_upper_iff, border_square_zero_iff, and_assoc]

private theorem mem_C_border_iff [CharP F 2]
    (A : Matrix (Fin n) (Fin n) F) (w : Fin n → F) (c : F) :
    border A w c ∈ C F (n+1) ↔
      A ∈ C F n ∧ A.transpose *ᵥ w = 0 ∧ c = ∑ i, w i := by
  simp only [C, Set.mem_ofPred_eq, border_upper_iff, border_gram_zero_iff, and_assoc]

open scoped Classical

private def embedLinear : (Fin n → F) →ₗ[F] (Fin (n+1) → F) :=
  LinearMap.pi (Fin.lastCases
    (motive := fun _ : Fin (n+1) => (Fin n → F) →ₗ[F] F)
    0 (fun i => LinearMap.proj i))

private theorem embedLinear_injective : Function.Injective (embedLinear (n := n) (F := F)) := by
  intro a b hab
  funext i
  simpa [embedLinear] using congrFun hab i.castSucc

private theorem border_column_span (A : Matrix (Fin n) (Fin n) F)
    (v : Fin n → F) (c : F) :
    Submodule.span F (Set.range (border A v c).col) =
      (Submodule.span F (Set.range A.col)).map embedLinear ⊔
        Submodule.span F {(Fin.lastCases c v)} := by
  have hcol (j : Fin n) : (border A v c).col j.castSucc = embedLinear (A.col j) := by
    funext i
    refine Fin.lastCases ?_ (fun i => ?_) i <;>
      simp [Matrix.col_apply, embedLinear]
  have hlast : (border A v c).col (Fin.last n) = (Fin.lastCases c v) := by
    funext i
    refine Fin.lastCases ?_ (fun i => ?_) i <;> simp [Matrix.col_apply]
  have hrange : Set.range (border A v c).col =
      embedLinear '' Set.range A.col ∪ {(Fin.lastCases c v)} := by
    ext z
    constructor
    · rintro ⟨j, rfl⟩
      refine Fin.lastCases ?_ (fun j => ?_) j
      · exact Or.inr hlast
      · exact Or.inl ⟨A.col j, ⟨j, rfl⟩, (hcol j).symm⟩
    · rintro (⟨_, ⟨j, rfl⟩, rfl⟩ | hz)
      · exact ⟨j.castSucc, hcol j⟩
      · exact ⟨Fin.last n, hlast.trans hz.symm⟩
  rw [hrange, Submodule.span_union, Submodule.span_image]

private theorem appendVec_mem_map_iff (p : Submodule F (Fin n → F))
    (v : Fin n → F) (c : F) :
    (Fin.lastCases c v) ∈ p.map embedLinear ↔ v ∈ p ∧ c = 0 := by
  constructor
  · rintro ⟨u, hu, he⟩
    have huv : u = v := by
      funext i
      simpa [embedLinear] using congrFun he i.castSucc
    have hc : c = 0 := by
      simpa [embedLinear] using (congrFun he (Fin.last n)).symm
    exact ⟨huv ▸ hu, hc⟩
  · rintro ⟨hv, rfl⟩
    refine ⟨v, hv, ?_⟩
    funext i
    refine Fin.lastCases ?_ (fun i => ?_) i <;> simp [embedLinear]

private theorem border_rank (A : Matrix (Fin n) (Fin n) F)
    (v : Fin n → F) (c : F) :
    (border A v c).rank = A.rank +
      if v ∈ LinearMap.range A.mulVecLin ∧ c = 0 then 0 else 1 := by
  classical
  let p := Submodule.span F (Set.range A.col)
  have hdim : Module.finrank F (p.map embedLinear) = Module.finrank F p :=
    (Submodule.equivMapOfInjective embedLinear embedLinear_injective p).finrank_eq.symm
  rw [Matrix.rank_eq_finrank_span_cols, border_column_span,
    Matrix.rank_eq_finrank_span_cols, Matrix.range_mulVecLin]
  change Module.finrank F (p.map embedLinear ⊔ Submodule.span F {(Fin.lastCases c v)} :
      Submodule F (Fin (n+1) → F)) =
    Module.finrank F p + if v ∈ p ∧ c = 0 then 0 else 1
  by_cases h : v ∈ p ∧ c = 0
  · have hm : (Fin.lastCases c v) ∈ p.map embedLinear := (appendVec_mem_map_iff p v c).mpr h
    rw [if_pos h, sup_eq_left.mpr ((Submodule.span_singleton_le_iff_mem _ _).mpr hm),
      hdim, add_zero]
  · have hm : (Fin.lastCases c v) ∉ p.map embedLinear := by
      exact fun hm => h ((appendVec_mem_map_iff p v c).mp hm)
    rw [if_neg h, Submodule.finrank_sup_span_singleton hm, hdim]

private theorem sum_image_eq_zero [CharP F 2] (A : Matrix (Fin n) (Fin n) F)
    (hA : A.transpose * A = 0) (a : Fin n → F) : ∑ i, (A *ᵥ a) i = 0 := by
  have hsq : (∑ i, (A *ᵥ a) i) ^ 2 = 0 := by
    rw [CharTwo.sum_sq]
    simp only [pow_two]
    change (A *ᵥ a) ⬝ᵥ (A *ᵥ a) = 0
    rw [← Matrix.dotProduct_transpose_mulVec A a (A *ᵥ a),
      Matrix.mulVec_mulVec, hA, Matrix.zero_mulVec, dotProduct_zero]
  exact eq_zero_of_pow_eq_zero hsq

private theorem gram_border_rank [CharP F 2]
    (A : Matrix (Fin n) (Fin n) F) (hA : A.transpose * A = 0) (w : Fin n → F) :
    (border A w (∑ i, w i)).rank = A.rank +
      if w ∈ LinearMap.range A.mulVecLin then 0 else 1 := by
  classical
  rw [border_rank]
  congr 1
  by_cases hw : w ∈ LinearMap.range A.mulVecLin
  · obtain ⟨a, rfl⟩ := hw
    simp [LinearMap.mem_range_self, sum_image_eq_zero A hA a]
  · simp [hw]

@[simp] private theorem principal_border (A : Matrix (Fin n) (Fin n) F)
    (v : Fin n → F) (c : F) : (fun X : Matrix (Fin (n+1)) (Fin (n+1)) F => X.submatrix Fin.castSucc Fin.castSucc) (border A v c) = A := by
  ext i j
  exact border_cast_cast A v c i j

@[simp] private theorem finalColumn_border (A : Matrix (Fin n) (Fin n) F)
    (v : Fin n → F) (c : F) : (fun X : Matrix (Fin (n+1)) (Fin (n+1)) F => fun i : Fin n => X i.castSucc (Fin.last n)) (border A v c) = v := by
  funext i
  exact border_cast_last A v c i

private theorem rebuild_upper (X : Matrix (Fin (n+1)) (Fin (n+1)) F)
    (hX : X.IsUpperTriangular) :
    border ((fun X : Matrix (Fin (n+1)) (Fin (n+1)) F => X.submatrix Fin.castSucc Fin.castSucc) X) ((fun X : Matrix (Fin (n+1)) (Fin (n+1)) F => fun i : Fin n => X i.castSucc (Fin.last n)) X) (X (Fin.last n) (Fin.last n)) = X := by
  ext i j
  refine Fin.lastCases ?_ (fun i => ?_) i
  · refine Fin.lastCases ?_ (fun j => ?_) j
    · simp
    · rw [border_last_cast]
      exact (hX (show j.castSucc < Fin.last n from j.isLt)).symm
  · refine Fin.lastCases ?_ (fun j => ?_) j
    · simp []
    · simp []

private theorem B_last_zero (X : Matrix (Fin (n+1)) (Fin (n+1)) F)
    (hX : X ∈ B F (n+1)) : X (Fin.last n) (Fin.last n) = 0 := by
  have hbelow (i : Fin n) : X (Fin.last n) i.castSucc = 0 :=
    hX.1 (Fin.castSucc_lt_last i)
  have hh := congrFun (congrFun hX.2 (Fin.last n)) (Fin.last n)
  apply mul_self_eq_zero.mp
  simpa [Matrix.mul_apply, Fin.sum_univ_castSucc, hbelow] using hh

private theorem B_decompose (X : Matrix (Fin (n+1)) (Fin (n+1)) F)
    (hX : X ∈ B F (n+1)) :
    (fun X : Matrix (Fin (n+1)) (Fin (n+1)) F => X.submatrix Fin.castSucc Fin.castSucc) X ∈ B F n ∧ (fun X : Matrix (Fin (n+1)) (Fin (n+1)) F => X.submatrix Fin.castSucc Fin.castSucc) X *ᵥ (fun X : Matrix (Fin (n+1)) (Fin (n+1)) F => fun i : Fin n => X i.castSucc (Fin.last n)) X = 0 ∧
      border ((fun X : Matrix (Fin (n+1)) (Fin (n+1)) F => X.submatrix Fin.castSucc Fin.castSucc) X) ((fun X : Matrix (Fin (n+1)) (Fin (n+1)) F => fun i : Fin n => X i.castSucc (Fin.last n)) X) 0 = X := by
  have he : border ((fun X : Matrix (Fin (n+1)) (Fin (n+1)) F => X.submatrix Fin.castSucc Fin.castSucc) X) ((fun X : Matrix (Fin (n+1)) (Fin (n+1)) F => fun i : Fin n => X i.castSucc (Fin.last n)) X) 0 = X := by
    rw [← B_last_zero X hX]
    exact rebuild_upper X hX.1
  have hb : border ((fun X : Matrix (Fin (n+1)) (Fin (n+1)) F => X.submatrix Fin.castSucc Fin.castSucc) X) ((fun X : Matrix (Fin (n+1)) (Fin (n+1)) F => fun i : Fin n => X i.castSucc (Fin.last n)) X) 0 ∈ B F (n+1) := by
    exact Set.mem_of_eq_of_mem he hX
  exact ⟨((mem_B_border_iff _ _).mp hb).1, ((mem_B_border_iff _ _).mp hb).2, he⟩

private theorem C_decompose [CharP F 2]
    (U : Matrix (Fin (n+1)) (Fin (n+1)) F) (hU : U ∈ C F (n+1)) :
    (fun X : Matrix (Fin (n+1)) (Fin (n+1)) F => X.submatrix Fin.castSucc Fin.castSucc) U ∈ C F n ∧ ((fun X : Matrix (Fin (n+1)) (Fin (n+1)) F => X.submatrix Fin.castSucc Fin.castSucc) U).transpose *ᵥ (fun X : Matrix (Fin (n+1)) (Fin (n+1)) F => fun i : Fin n => X i.castSucc (Fin.last n)) U = 0 ∧
      border ((fun X : Matrix (Fin (n+1)) (Fin (n+1)) F => X.submatrix Fin.castSucc Fin.castSucc) U) ((fun X : Matrix (Fin (n+1)) (Fin (n+1)) F => fun i : Fin n => X i.castSucc (Fin.last n)) U) (∑ i, (fun X : Matrix (Fin (n+1)) (Fin (n+1)) F => fun i : Fin n => X i.castSucc (Fin.last n)) U i) = U := by
  have he := rebuild_upper U hU.1
  have hb : border ((fun X : Matrix (Fin (n+1)) (Fin (n+1)) F => X.submatrix Fin.castSucc Fin.castSucc) U) ((fun X : Matrix (Fin (n+1)) (Fin (n+1)) F => fun i : Fin n => X i.castSucc (Fin.last n)) U) (U (Fin.last n) (Fin.last n)) ∈ C F (n+1) := by
    exact Set.mem_of_eq_of_mem he hU
  have hh := (mem_C_border_iff _ _ _).mp hb
  refine ⟨hh.1, hh.2.1, ?_⟩
  rw [← hh.2.2]
  exact he

def recursiveStep
    (f : Matrix (Fin n) (Fin n) F → Matrix (Fin n) (Fin n) F)
    (ψ : Matrix (Fin n) (Fin n) F → (Fin n → F) → (Fin n → F))
    (X : Matrix (Fin (n+1)) (Fin (n+1)) F) :
    Matrix (Fin (n+1)) (Fin (n+1)) F :=
  let w := ψ ((fun X : Matrix (Fin (n+1)) (Fin (n+1)) F => X.submatrix Fin.castSucc Fin.castSucc) X) ((fun X : Matrix (Fin (n+1)) (Fin (n+1)) F => fun i : Fin n => X i.castSucc (Fin.last n)) X)
  border (f ((fun X : Matrix (Fin (n+1)) (Fin (n+1)) F => X.submatrix Fin.castSucc Fin.castSucc) X)) w (∑ i, w i)

theorem recursiveStep_bijOn [CharP F 2]
    (f : Matrix (Fin n) (Fin n) F → Matrix (Fin n) (Fin n) F)
    (ψ : Matrix (Fin n) (Fin n) F → (Fin n → F) → (Fin n → F))
    (hf : Set.BijOn f (B F n) (C F n))
    (hψ : ∀ A ∈ B F n, Set.BijOn (ψ A)
      {v | A *ᵥ v = 0} {w | (f A).transpose *ᵥ w = 0}) :
    Set.BijOn (recursiveStep f ψ) (B F (n+1)) (C F (n+1)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro X hX
    obtain ⟨hA, hv, _⟩ := B_decompose X hX
    exact (mem_C_border_iff _ _ _).mpr
      ⟨hf.mapsTo hA, (hψ _ hA).mapsTo hv, rfl⟩
  · intro X hX Y hY he
    obtain ⟨hA, hv, hXe⟩ := B_decompose X hX
    obtain ⟨hD, hu, hYe⟩ := B_decompose Y hY
    have htop : f ((fun X : Matrix (Fin (n+1)) (Fin (n+1)) F => X.submatrix Fin.castSucc Fin.castSucc) X) = f ((fun X : Matrix (Fin (n+1)) (Fin (n+1)) F => X.submatrix Fin.castSucc Fin.castSucc) Y) := by
      simpa only [recursiveStep, principal_border] using congrArg (fun X : Matrix (Fin (n+1)) (Fin (n+1)) F => X.submatrix Fin.castSucc Fin.castSucc) he
    have hAD : (fun X : Matrix (Fin (n+1)) (Fin (n+1)) F => X.submatrix Fin.castSucc Fin.castSucc) X = (fun X : Matrix (Fin (n+1)) (Fin (n+1)) F => X.submatrix Fin.castSucc Fin.castSucc) Y := hf.injOn hA hD htop
    have hw : ψ ((fun X : Matrix (Fin (n+1)) (Fin (n+1)) F => X.submatrix Fin.castSucc Fin.castSucc) X) ((fun X : Matrix (Fin (n+1)) (Fin (n+1)) F => fun i : Fin n => X i.castSucc (Fin.last n)) X) = ψ ((fun X : Matrix (Fin (n+1)) (Fin (n+1)) F => X.submatrix Fin.castSucc Fin.castSucc) Y) ((fun X : Matrix (Fin (n+1)) (Fin (n+1)) F => fun i : Fin n => X i.castSucc (Fin.last n)) Y) := by
      simpa only [recursiveStep, finalColumn_border] using congrArg (fun X : Matrix (Fin (n+1)) (Fin (n+1)) F => fun i : Fin n => X i.castSucc (Fin.last n)) he
    rw [hAD] at hw hv
    have hvu := (hψ _ hD).injOn hv hu hw
    rw [← hXe, ← hYe, hAD, hvu]
  · intro U hU
    obtain ⟨hD, hw, hUe⟩ := C_decompose U hU
    obtain ⟨A, hA, hAf⟩ := hf.surjOn hD
    rw [← hAf] at hw
    obtain ⟨v, hv, hψv⟩ := (hψ A hA).surjOn hw
    refine ⟨border A v 0, (mem_B_border_iff _ _).mpr ⟨hA, hv⟩, ?_⟩
    simpa only [recursiveStep, principal_border, finalColumn_border, hAf, hψv] using hUe

theorem recursiveStep_rank [CharP F 2]
    (f : Matrix (Fin n) (Fin n) F → Matrix (Fin n) (Fin n) F)
    (ψ : Matrix (Fin n) (Fin n) F → (Fin n → F) → (Fin n → F))
    (hf : Set.MapsTo f (B F n) (C F n))
    (hr : ∀ A ∈ B F n, (f A).rank = A.rank)
    (hψ : ∀ A ∈ B F n, ∀ v, A *ᵥ v = 0 →
      (ψ A v ∈ LinearMap.range (f A).mulVecLin ↔ v ∈ LinearMap.range A.mulVecLin))
    (X : Matrix (Fin (n+1)) (Fin (n+1)) F) (hX : X ∈ B F (n+1)) :
    (recursiveStep f ψ X).rank = X.rank := by
  obtain ⟨hA, hv, he⟩ := B_decompose X hX
  rw [recursiveStep, gram_border_rank _ (hf hA).2, hr _ hA, hψ _ hA _ hv]
  calc
    _ = (border ((fun X : Matrix (Fin (n+1)) (Fin (n+1)) F => X.submatrix Fin.castSucc Fin.castSucc) X) ((fun X : Matrix (Fin (n+1)) (Fin (n+1)) F => fun i : Fin n => X i.castSucc (Fin.last n)) X) 0).rank := by
      rw [border_rank]
      simp only [and_true]
    _ = X.rank := congrArg Matrix.rank he

def Recipe.rename {k n : ℕ} (I J : Fin k → Fin n) : Recipe k → Recipe n
  | .zero => .zero
  | .one => .one
  | .entry i j => .entry (I i) (J j)
  | .add a b => .add (Recipe.rename I J a) (Recipe.rename I J b)
  | .mul a b => .mul (Recipe.rename I J a) (Recipe.rename I J b)
  | .inv a => .inv (Recipe.rename I J a)
  | .iteZero a b c => .iteZero (Recipe.rename I J a) (Recipe.rename I J b) (Recipe.rename I J c)

theorem recipe_rename_eval [DecidableEq F] {k : ℕ}
    (X : Matrix (Fin n) (Fin n) F) (I J : Fin k → Fin n) (p : Recipe k) :
    (Recipe.rename I J p).eval X = p.eval (X.submatrix I J) := by
  induction p with
  | zero => rfl
  | one => rfl
  | entry i j => rfl
  | add a b ha hb => simp [Recipe.rename, Recipe.eval, ha, hb]
  | mul a b ha hb => simp [Recipe.rename, Recipe.eval, ha, hb]
  | inv a ha => simp [Recipe.rename, Recipe.eval, ha]
  | iteZero a b c ha hb hc => simp [Recipe.rename, Recipe.eval, ha, hb, hc]

def recursiveRecipe (p : Matrix (Fin n) (Fin n) (Recipe n))
    (q : Fin n → Recipe (n+1)) : Matrix (Fin (n+1)) (Fin (n+1)) (Recipe (n+1)) :=
  fun i j => Fin.lastCases
    (Fin.lastCases (Recipe.sum (List.ofFn q)) q i)
    (fun j => Fin.lastCases .zero (fun i => Recipe.rename Fin.castSucc Fin.castSucc (p i j)) i) j

theorem recursiveRecipe_eval [DecidableEq F]
    (p : Matrix (Fin n) (Fin n) (Recipe n)) (q : Fin n → Recipe (n+1))
    (X : Matrix (Fin (n+1)) (Fin (n+1)) F) :
    (((recursiveRecipe p q)).map (Recipe.eval X)) =
      border (((p).map (Recipe.eval ((fun X : Matrix (Fin (n+1)) (Fin (n+1)) F => X.submatrix Fin.castSucc Fin.castSucc) X)))) (fun i => (q i).eval X) (∑ i, (q i).eval X) := by
  ext i j
  refine Fin.lastCases ?_ (fun i => ?_) i
  · refine Fin.lastCases ?_ (fun j => ?_) j
    · simp [Matrix.map_apply, recursiveRecipe, recipe_sum_eval, List.map_ofFn,
        List.sum_ofFn, Function.comp_def]
    · simp [Matrix.map_apply, recursiveRecipe, Recipe.eval]
  · refine Fin.lastCases ?_ (fun j => ?_) j
    · simp [Matrix.map_apply, recursiveRecipe]
    · simpa only [Matrix.map_apply, recursiveRecipe, Fin.lastCases_castSucc, border_cast_cast] using recipe_rename_eval X Fin.castSucc Fin.castSucc (p i j)

end D5.S3.QuadraticForms.FrobeniusCholeskyRecursion
