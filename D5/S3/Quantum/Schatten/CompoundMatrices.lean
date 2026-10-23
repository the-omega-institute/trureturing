/- GID: D5/S3/Quantum/Schatten/CompoundMatrices
   generality: G
   mirror-B: D5/B/S3/Quantum/Schatten/CompoundMatrices
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compound matrix singular values and sorted products. -/

/-
Attributed source: leanprover-community/physlib, revision b9043cc548ef6d63a28454cf3a57fb12a0c2e142.
Original module: QuantumInfo/ForMathlib/Majorization.lean.
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
Full license: docs/reports/inoutbalance/physlib-LICENSE.txt.
Retire this transplant when an equivalent consumed declaration exists in the
repository-pinned Mathlib, replacing it by direct application.
No mathematical originality is claimed for the attributed source.
-/
module

public import D5.S3.Quantum.Schatten.MatrixSimilarity

@[expose] public section

open Finset BigOperators Matrix

variable {d : Type*} [Fintype d] [DecidableEq d]

noncomputable section

/-! ## Sorted singular values -/

/-- The singular values of a square complex matrix `A`, defined as the square
roots of the eigenvalues of `A†A`. These are indexed by `d` without a
particular ordering.

Note: We use `A.conjTranspose` as the argument to `isHermitian_mul_conjTranspose_self`
so that the underlying Hermitian matrix is `A† * A` (matching the convention in `schattenNorm`). -/
def singularValues (A : Matrix d d ℂ) : d → ℝ :=
  fun i => Real.sqrt ((isHermitian_mul_conjTranspose_self A.conjTranspose).eigenvalues i)

/-- Singular values are nonneg. -/
lemma singularValues_nonneg (A : Matrix d d ℂ) (i : d) :
    0 ≤ singularValues A i :=
  Real.sqrt_nonneg _

/-- The sorted singular values of a square complex matrix, in decreasing order,
indexed by `Fin (Fintype.card d)`.

We define them by sorting the multiset of singular values. -/
noncomputable def singularValuesSorted (A : Matrix d d ℂ) :
    Fin (Fintype.card d) → ℝ :=
  fun i =>
    let vals : Multiset ℝ := Finset.univ.val.map (singularValues A)
    let sorted := vals.sort (· ≥ ·)
    sorted.get ⟨i.val, by rw [Multiset.length_sort]; show i.val < (Multiset.map (singularValues A) univ.val).card; rw [Multiset.card_map]; simp [Finset.card_univ]⟩

/-- Sorted singular values are nonneg. -/
lemma singularValuesSorted_nonneg (A : Matrix d d ℂ) (i : Fin (Fintype.card d)) :
    0 ≤ singularValuesSorted A i := by
  have h_nonneg : ∀ i, 0 ≤ (singularValues A i) := by
    exact singularValues_nonneg A
  have h_sorted_nonneg : ∀ {l : List ℝ}, (∀ x ∈ l, 0 ≤ x) → ∀ i < l.length, 0 ≤ l[i]! := by
    aesop
  contrapose! h_sorted_nonneg
  use Multiset.sort (Finset.univ.val.map (singularValues A)) (· ≥ ·)
  refine' ⟨_, i, _, _⟩
  · aesop
  · simp [Finset.card_univ]
  · convert h_sorted_nonneg using 1
    unfold singularValuesSorted; aesop

/-- The sum `∑ singularValues A i ^ p` equals the sum over sorted singular values. -/
lemma sum_singularValues_rpow_eq_sum_sorted (A : Matrix d d ℂ) (p : ℝ) :
    ∑ i : d, singularValues A i ^ p =
    ∑ i : Fin (Fintype.card d), singularValuesSorted A i ^ p := by
  have h_perm : Multiset.map (fun i => singularValues A i) Finset.univ.val = Multiset.map (fun i => singularValuesSorted A i) Finset.univ.val := by
    have h_multiset : Multiset.map (fun i => singularValues A i) Finset.univ.val = Multiset.sort (Multiset.map (fun i => singularValues A i) Finset.univ.val) (· ≥ ·) := by
      aesop
    convert h_multiset using 1
    refine' congr_arg _ (List.ext_get _ _) <;> simp [singularValuesSorted]
  have h_sum_eq : Multiset.sum (Multiset.map (fun x => x ^ p) (Multiset.map (fun i => singularValues A i) Finset.univ.val)) = Multiset.sum (Multiset.map (fun x => x ^ p) (Multiset.map (fun i => singularValuesSorted A i) Finset.univ.val)) := by
    rw [h_perm]
  convert h_sum_eq using 1
  · erw [Multiset.map_map, Finset.sum_eq_multiset_sum]
    rfl
  · simp [Finset.sum]
    rfl

/-! ## Weak log-majorization and its consequences -/

/-- Sorted singular values are antitone (decreasing). -/
lemma singularValuesSorted_antitone (A : Matrix d d ℂ) :
    Antitone (singularValuesSorted A) := by
  intro i j hij
  have h_sorted : List.Pairwise (· ≥ ·) (Finset.univ.val.map (singularValues A) |>.sort (· ≥ ·)) := by
    exact Multiset.pairwise_sort _ _
  exact h_sorted.rel_get_of_le hij

/-- The product of nonneg antitone sequences is antitone. -/
lemma antitone_mul_of_antitone_nonneg {n : ℕ}
    {f g : Fin n → ℝ} (hf : Antitone f) (hg : Antitone g)
    (hf_nn : ∀ i, 0 ≤ f i) (hg_nn : ∀ i, 0 ≤ g i) :
    Antitone (fun i => f i * g i) := by
  exact fun i j hij => mul_le_mul (hf hij) (hg hij) (hg_nn _) (hf_nn _)

/-! ### Compound matrices and auxiliary lemmas for Horn's inequality

The proof of Horn's inequality uses the *compound matrix* (or *k-th exterior power*
of a matrix).  For a `d × d` matrix `M` and `k ≤ card d`, the `k`-th compound matrix
`C_k(M)` is indexed by `k`-element subsets of the index type, with entry `(S, T)` being
the minor `det M[S, T]`.

The key properties are:
1. **Cauchy–Binet**: `C_k(M N) = C_k(M) · C_k(N)`.
2. **Spectral characterisation**: the largest singular value of `C_k(M)` is
   `∏_{i=1}^k σ↓ᵢ(M)`.
3. **Operator-norm submultiplicativity**: `σ₁(A B) ≤ σ₁(A) · σ₁(B)`.

Combining these gives Horn's inequality:
  `∏ σ↓(AB) = σ₁(C_k(AB)) = σ₁(C_k(A) C_k(B)) ≤ σ₁(C_k(A)) σ₁(C_k(B))
            = (∏ σ↓(A))(∏ σ↓(B))`.
-/

namespace AllOrdered

/-- A `LinearOrder` on any `Fintype`, obtained classically via well-ordering. -/
scoped instance fintypeLinearOrderClassical (α : Type*) [Fintype α] [DecidableEq α] :
    LinearOrder α := by
  classical
  exact linearOrderOfSTO (WellOrderingRel)

end AllOrdered

open scoped AllOrdered

/-- The `k`-th compound (exterior-power) matrix of `M`. -/
noncomputable def compoundMatrix (M : Matrix d d ℂ) (k : ℕ) :
    Matrix {S : Finset d // S.card = k} {S : Finset d // S.card = k} ℂ :=
  fun S T =>
    @Matrix.det (Fin k) _ _ ℂ _
      (M.submatrix (fun i => S.1.orderEmbOfFin S.2 i) (fun j => T.1.orderEmbOfFin T.2 j))

set_option maxHeartbeats 400000 in
/-- **Cauchy–Binet formula** for rectangular matrices: if `A` is `m × n` and `B` is
`n × m`, then `det(A * B) = ∑_S det(A[:,S]) * det(B[S,:])` where the sum is
over `m`-element subsets `S` of the column/row index. -/
lemma cauchyBinet {m : ℕ} {n : Type*} [Fintype n] [DecidableEq n] [LinearOrder n]
    {R : Type*} [CommRing R]
    (A : Matrix (Fin m) n R) (B : Matrix n (Fin m) R) :
    (A * B).det = ∑ S : {S : Finset n // S.card = m},
      (A.submatrix id (S.1.orderEmbOfFin S.2)).det *
      (B.submatrix (S.1.orderEmbOfFin S.2) id).det := by
  have h_cauchy_binet : ∀ (A : Matrix (Fin m) n R) (B : Matrix n (Fin m) R), Matrix.det (A * B) = ∑ σ : Fin m → n, (∏ i, A i (σ i)) * Matrix.det (Matrix.of (fun i j ↦ B (σ i) j)) := by
    simp [Matrix.det_apply']
    simp [Matrix.mul_apply, Finset.mul_sum]
    intro A B; rw [← Finset.sum_comm]; congr; ext x; simp [mul_comm]
    simp only [prod_sum, sum_mul]
    refine' Finset.sum_bij (fun f _ => fun i => f (x.symm i) (Finset.mem_univ _)) _ _ _ _
    · simp
    · simp only [univ_pi_univ, mem_univ, funext_iff, forall_true_left, forall_const]
      exact fun a₁ a₂ h i => by simpa using h (x i)
    · simp only [mem_univ, univ_pi_univ, exists_const, forall_const]
      exact fun b => ⟨fun i _ => b (x i), by ext i; simp⟩
    · simp only [univ_pi_univ, mem_univ, prod_mul_distrib, prod_attach_univ,
      Equiv.symm_apply_apply, forall_const]
      intro a
      rw [← Equiv.prod_comp x.symm]
      ring_nf
      rw [← Equiv.prod_comp x.symm]
      simp only [mul_comm, mul_assoc]
      conv_rhs => rw [← Equiv.prod_comp x]
      simp [Equiv.symm_apply_apply]
  -- Split the sum into injective and non-injective functions.
  have h_split : ∑ σ : Fin m → n, (∏ i, A i (σ i)) * Matrix.det (Matrix.of (fun i j ↦ B (σ i) j)) = ∑ σ : Fin m → n, if Function.Injective σ then (∏ i, A i (σ i)) * Matrix.det (Matrix.of (fun i j ↦ B (σ i) j)) else 0 := by
    refine Finset.sum_congr rfl fun σ _ => ?_
    split_ifs with hσ <;> simp_all [Function.Injective]
    obtain ⟨i, j, hij, hne⟩ := hσ
    exact mul_eq_zero_of_right _ (Matrix.det_zero_of_row_eq hne (by ext1; simp only [of_apply, hij]))
  -- Group the sum by the image of the injective functions.
  have h_group : ∑ σ : Fin m → n, (if Function.Injective σ then (∏ i, A i (σ i)) * Matrix.det (Matrix.of (fun i j ↦ B (σ i) j)) else 0) = ∑ S : {S : Finset n // S.card = m}, ∑ σ : Fin m → n, (if Function.Injective σ ∧ Finset.image σ Finset.univ = S.val then (∏ i, A i (σ i)) * Matrix.det (Matrix.of (fun i j ↦ B (σ i) j)) else 0) := by
    rw [← Finset.sum_comm, Finset.sum_congr rfl]
    intro σ _
    by_cases hσ : Function.Injective σ
    · simp [hσ]
      rw [Finset.sum_eq_single ⟨Finset.image σ Finset.univ, by simp [Finset.card_image_of_injective _ hσ]⟩]
      · simp
      · grind
      · simp
    · simp [hσ]
  -- For each subset $S$ of size $m$, the inner sum is equal to the product of the determinants of the submatrices of $A$ and $B$ corresponding to $S$.
  have h_inner : ∀ S : {S : Finset n // S.card = m}, ∑ σ : Fin m → n, (if Function.Injective σ ∧ Finset.image σ Finset.univ = S.val then (∏ i, A i (σ i)) * Matrix.det (Matrix.of (fun i j ↦ B (σ i) j)) else 0) = Matrix.det (Matrix.submatrix A id (S.val.orderEmbOfFin S.property)) * Matrix.det (Matrix.submatrix B (S.val.orderEmbOfFin S.property) id) := by
    intro S
    have h_inner_sum : ∑ σ : Fin m → n, (if Function.Injective σ ∧ Finset.image σ Finset.univ = S.val then (∏ i, A i (σ i)) * Matrix.det (Matrix.of (fun i j ↦ B (σ i) j)) else 0) = ∑ τ : Equiv.Perm (Fin m), (∏ i, A i (S.val.orderEmbOfFin S.property (τ i))) * Matrix.det (Matrix.of (fun i j ↦ B (S.val.orderEmbOfFin S.property (τ i)) j)) := by
      have h_inner_sum : Finset.filter (fun σ : Fin m → n => Function.Injective σ ∧ Finset.image σ Finset.univ = S.val) Finset.univ = Finset.image (fun τ : Equiv.Perm (Fin m) => fun i => S.val.orderEmbOfFin S.property (τ i)) Finset.univ := by
        ext σ
        simp [Finset.mem_image]
        constructor
        · intro hσ
          obtain ⟨a, ha⟩ : ∃ a : Fin m → Fin m, ∀ i, σ i = S.val.orderEmbOfFin S.property (a i) := by
            have h_exists_a : ∀ i, ∃ a : Fin m, σ i = S.val.orderEmbOfFin S.property a := by
              intro i
              have h_exists_a : σ i ∈ S.val := by
                exact hσ.2 ▸ Finset.mem_image_of_mem _ (Finset.mem_univ _)
              have h_exists_a : Finset.image (fun a : Fin m => S.val.orderEmbOfFin S.property a) Finset.univ = S.val := by
                refine' Finset.eq_of_subset_of_card_le (Finset.image_subset_iff.mpr fun a _ => Finset.orderEmbOfFin_mem _ _ _) _
                rw [Finset.card_image_of_injective _ fun a b h => by simpa [Fin.ext_iff] using h]; simp [S.2]
              grind
            exact ⟨fun i => Classical.choose (h_exists_a i), fun i => Classical.choose_spec (h_exists_a i)⟩
          have ha_inj : Function.Injective a := by
            exact fun i j hij => hσ.1 <| by simp [ha, hij]
          exact ⟨Equiv.ofBijective a ⟨ha_inj, Finite.injective_iff_surjective.mp ha_inj⟩, funext fun i => ha i ▸ rfl⟩
        · rintro ⟨a, rfl⟩
          constructor
          · exact fun i j hij => a.injective <| by simpa using hij
          · refine Finset.eq_of_subset_of_card_le (Finset.image_subset_iff.mpr fun i _ => Finset.orderEmbOfFin_mem _ _ _) ?_
            rw [Finset.card_image_of_injective _ fun i j hij => by simpa [Fin.ext_iff] using hij]; simp [S.2]
      rw [← Finset.sum_filter, h_inner_sum, Finset.sum_image]
      exact fun τ _ τ' _ h => Equiv.Perm.ext fun i => by simpa using congr_fun h i
    rw [h_inner_sum, Matrix.det_apply', Matrix.det_apply']
    simp [Matrix.det_apply', Finset.sum_mul]
    refine' Finset.sum_bij (fun σ _ => σ⁻¹) _ _ _ _ <;> simp [Equiv.Perm.sign_inv]
    · exact fun b => ⟨b⁻¹, inv_inv b⟩
    · intro σ
      rw [← Equiv.prod_comp σ⁻¹]
      simp [mul_assoc, mul_left_comm, Finset.mul_sum]
      refine' Finset.sum_bij (fun τ _ => σ * τ) _ _ _ _ <;> simp [Equiv.Perm.sign_mul]
      · exact fun b => ⟨σ⁻¹ * b, by simp⟩
      · cases' Int.units_eq_one_or (Equiv.Perm.sign σ) with h h <;> simp [h]
  rw [h_cauchy_binet, h_split, h_group, Finset.sum_congr rfl fun S hS => h_inner S]

/--
The `compoundMatrix` of a product is the product of the `compoundMatrix`s.
-/
lemma compoundMatrix_mul (M N : Matrix d d ℂ) (k : ℕ) :
    compoundMatrix (M * N) k = compoundMatrix M k * compoundMatrix N k := by
  ext1
  apply cauchyBinet

set_option backward.isDefEq.respectTransparency false in
/-- `compoundMatrix` commutes with `conjTranspose`. -/
lemma compoundMatrix_conjTranspose (M : Matrix d d ℂ) (k : ℕ) :
    compoundMatrix M.conjTranspose k = (compoundMatrix M k).conjTranspose := by
  ext1
  unfold compoundMatrix
  rw [Matrix.conjTranspose_apply, ← Matrix.det_conjTranspose]
  simp

set_option backward.isDefEq.respectTransparency false in
/--
The compound matrix of a diagonal matrix is diagonal, with entries being
products of eigenvalues over k-subsets. -/
lemma compoundMatrix_diagonal (f : d → ℂ) (k : ℕ) :
    compoundMatrix (Matrix.diagonal f) k =
    Matrix.diagonal (fun S : {S : Finset d // S.card = k} =>
      ∏ i : Fin k, f (S.1.orderEmbOfFin S.2 i)) := by
  ext S T; by_cases h : S = T <;> simp_all [Matrix.diagonal]
  · refine' Matrix.det_of_isUpperTriangular _ |> fun h => h.trans _
    · intro i j hij; aesop
    · aesop
  · -- Since $S \neq T$, there exists some $i \in S$ such that $i \notin T$.
    obtain ⟨i, hiS, hiT⟩ : ∃ i ∈ S.val, i ∉ T.val := by
      contrapose! h
      exact Subtype.ext (Finset.eq_of_subset_of_card_le h (by simp [S.2, T.2]))
    obtain ⟨j, hj⟩ : ∃ j : Fin k, (S.val.orderEmbOfFin S.2) j = i := by
      have h_row_zero : Finset.image (fun j : Fin k => S.val.orderEmbOfFin S.2 j) Finset.univ = S.val := by
        refine' Finset.eq_of_subset_of_card_le (Finset.image_subset_iff.mpr fun j _ => Finset.orderEmbOfFin_mem _ _ _) _
        simp [Finset.card_image_of_injective, Function.Injective, *]
      exact Exists.elim (Finset.mem_image.mp (h_row_zero.symm ▸ hiS)) fun j hj => ⟨j, hj.2⟩
    -- Since the row corresponding to $i$ in the submatrix is all zeros, the determinant of this submatrix is zero.
    have h_det_zero : Matrix.det (Matrix.of (fun i j => if (S.val.orderEmbOfFin S.2 i) = (T.val.orderEmbOfFin T.2 j) then f (T.val.orderEmbOfFin T.2 j) else 0) : Matrix (Fin k) (Fin k) ℂ) = 0 := by
      rw [Matrix.det_eq_zero_of_row_eq_zero j]; aesop
    exact h_det_zero

/-- The compound matrix of a unitary matrix is unitary. -/
lemma compoundMatrix_unitary (U : Matrix d d ℂ)
    (hU : U ∈ Matrix.unitaryGroup d ℂ) (k : ℕ) :
    compoundMatrix U k ∈ Matrix.unitaryGroup {S : Finset d // S.card = k} ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose,
    ← compoundMatrix_conjTranspose, ← compoundMatrix_mul,
    show Uᴴ * U = 1 by exact Matrix.mem_unitaryGroup_iff'.mp hU]
  simpa using compoundMatrix_diagonal (1 : d → ℂ) k

/--
The eigenvalues of the compound matrix of a Hermitian matrix are the products
of eigenvalues over k-subsets. More precisely, the singular values of
`compoundMatrix M k` are the square roots of products of eigenvalues of M†M
over k-subsets.
-/
lemma singularValues_compoundMatrix_eq (M : Matrix d d ℂ) (k : ℕ) :
    ∀ (S : {S : Finset d // S.card = k}),
    ∃ (j : {S : Finset d // S.card = k}),
    singularValues (compoundMatrix M k) j =
    ∏ i : Fin k, singularValues M (S.1.orderEmbOfFin S.2 i) := by
  unfold singularValues
  intro S
  have h_eigenvalues : ∃ σ : {S : Finset d // S.card = k} ≃ {S : Finset d // S.card = k}, (Matrix.IsHermitian.eigenvalues (isHermitian_mul_conjTranspose_self (compoundMatrix M k).conjTranspose) ∘ σ) = fun S => ∏ i : Fin k, (Matrix.IsHermitian.eigenvalues (isHermitian_mul_conjTranspose_self M.conjTranspose)) (S.1.orderEmbOfFin S.2 i) := by
    apply IsHermitian.eigenvalues_eq_of_unitary_similarity_diagonal
    rotate_right
    exact compoundMatrix (Matrix.IsHermitian.eigenvectorUnitary (isHermitian_mul_conjTranspose_self M.conjTranspose)) k
    · exact compoundMatrix_unitary _ (by simp [Matrix.unitaryGroup]) _
    · have h_compoundMatrix_mul : compoundMatrix (M.conjTranspose * M) k = compoundMatrix M.conjTranspose k * compoundMatrix M k := by
        exact compoundMatrix_mul _ _ _
      have h_compoundMatrix_conjTranspose : compoundMatrix M.conjTranspose k = (compoundMatrix M k).conjTranspose := by
        exact compoundMatrix_conjTranspose M k
      have := Matrix.IsHermitian.spectral_theorem (isHermitian_mul_conjTranspose_self M.conjTranspose)
      convert congr_arg (fun x => compoundMatrix x k) this using 1 <;> simp [h_compoundMatrix_mul, h_compoundMatrix_conjTranspose]
      rw [compoundMatrix_mul, compoundMatrix_mul]
      rw [← compoundMatrix_conjTranspose]
      rw [compoundMatrix_diagonal]; simp [Matrix.mul_assoc]
      congr! 3
  obtain ⟨σ, hσ⟩ := h_eigenvalues
  use σ S; simp_all [funext_iff]
  rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num [Finset.prod_nonneg, Real.sqrt_nonneg]
  · rw [← Finset.prod_mul_distrib, Finset.prod_congr rfl fun _ _ => Real.mul_self_sqrt (_)]
    intro i hi; exact (by
    apply Matrix.eigenvalues_conjTranspose_mul_self_nonneg)
  · refine' Finset.prod_nonneg fun i _ => _
    exact eigenvalues_conjTranspose_mul_self_nonneg M _

/-- The product of nonneg values over a k-subset is at most the product of the
    k largest values. -/
lemma prod_le_prod_sorted {n : ℕ} {f : Fin n → ℝ}
    (hf : Antitone f) (hf_nn : ∀ i, 0 ≤ f i)
    (k : ℕ) (hk : k ≤ n)
    (g : Fin k → Fin n) (hg : Function.Injective g) :
    ∏ i : Fin k, f (g i) ≤ ∏ i : Fin k, f ⟨i.val, by omega⟩ := by
  -- The sorted values at positions g(i) are bounded by the sorted values at positions i,
  -- because g is injective so g(i) ≥ i (in the sorted sense), and f is antitone.
  -- We use the fact that for injective g : Fin k → Fin n, sorting g gives values ≥ identity.
  -- First sort g to get g' with g'(0) < g'(1) < ... < g'(k-1)
  -- Then g'(i) ≥ i since we're choosing k distinct values from Fin n
  -- So f(g'(i)) ≤ f(i) by antitonicity
  -- And the product is preserved under sorting (it's the same set of values)
  have h_exists_sorted : ∃ (g' : Fin k → Fin n),
      Function.Injective g' ∧ StrictMono g' ∧
      Finset.image g Finset.univ = Finset.image g' Finset.univ := by
    exact ⟨Finset.orderEmbOfFin (Finset.image g Finset.univ) (by simp [Finset.card_image_of_injective _ hg]),
      fun a b h => by simpa using h,
      fun a b h => by simpa using h,
      by ext x; simp⟩
  obtain ⟨g', hg'_inj, hg'_mono, hg'_eq⟩ := h_exists_sorted
  have h_prod_eq : ∏ i : Fin k, f (g i) = ∏ i : Fin k, f (g' i) := by
    rw [← Finset.prod_image (f := f) (fun a _ b _ h => hg (by simpa using h)),
        ← Finset.prod_image (f := f) (fun a _ b _ h => hg'_inj (by simpa using h))]
    exact Finset.prod_congr hg'_eq (fun _ _ => rfl)
  rw [h_prod_eq]
  apply Finset.prod_le_prod₀ (fun i _ => hf_nn _) (fun i _ => ?_)
  apply hf
  -- Need: i.val ≤ (g' i).val for strictly monotone g'
  -- By induction: g'(0) ≥ 0, and g'(j+1) > g'(j) ≥ j implies g'(j+1) ≥ j+1
  suffices h : ∀ (m : ℕ) (hm : m < k), m ≤ (g' ⟨m, hm⟩).val from h i.val i.isLt
  intro m hm
  induction m with
  | zero => exact Nat.zero_le _
  | succ m ih =>
    have ihm := ih (by omega)
    have := hg'_mono (show (⟨m, by omega⟩ : Fin k) < ⟨m + 1, hm⟩ by simp [Fin.lt_def])
    omega

/-- The 0th sorted singular value is the maximum of the singular values. -/
lemma singularValuesSorted_zero_eq_sup {e : Type*} [Fintype e] [DecidableEq e]
    (A : Matrix e e ℂ) (h : 0 < Fintype.card e) :
    singularValuesSorted A ⟨0, h⟩ = Finset.sup' Finset.univ
      (Finset.univ_nonempty_iff.mpr (Fintype.card_pos_iff.mp h))
      (singularValues A) := by
  refine' le_antisymm _ _
  · -- Since the list is sorted in decreasing order, every element in the list is less than or equal to the supremum of the original set.
    have h_le_sup : ∀ x ∈ Multiset.sort (Multiset.map (singularValues A) Finset.univ.val) (· ≥ ·), x ≤ Finset.sup' Finset.univ (Finset.univ_nonempty_iff.mpr ⟨Classical.choose (Finset.card_pos.mp h)⟩) (singularValues A) := by
      aesop
    exact h_le_sup _ (by simp [singularValuesSorted])
  · have h_max_le_ge : ∀ i, singularValues A i ≤ singularValuesSorted A ⟨0, h⟩ := by
      intro i
      have h_max_le_ge : ∀ j, singularValuesSorted A j ≤ singularValuesSorted A ⟨0, h⟩ := by
        exact fun j => singularValuesSorted_antitone A (Nat.zero_le _)
      exact (by
      have h_max_le_ge : ∃ j, singularValues A i = singularValuesSorted A j := by
        have h_exists_j : singularValues A i ∈ Multiset.sort (Finset.univ.val.map (singularValues A)) (· ≥ ·) := by
          simp [Multiset.mem_sort]
        obtain ⟨j, hj⟩ := List.mem_iff_get.mp h_exists_j
        exact ⟨⟨j, by simpa using j.2⟩, hj.symm⟩
      aesop)
    exact Finset.sup'_le _ _ fun i _ => h_max_le_ge i

/-- Each singular value appears in the sorted list. -/
lemma singularValues_mem_sorted {e : Type*} [Fintype e] [DecidableEq e]
    (A : Matrix e e ℂ) (i : e) :
    ∃ j : Fin (Fintype.card e), singularValues A i = singularValuesSorted A j := by
  have h_mem : singularValues A i ∈ Multiset.sort (Finset.univ.val.map (singularValues A)) (· ≥ ·) := by
    simp [Multiset.mem_sort]
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h_mem
  exact ⟨⟨j, by simpa using j.2⟩, hj.symm⟩

/-- Each sorted singular value appears among the original singular values. -/
lemma singularValuesSorted_mem_values {e : Type*} [Fintype e] [DecidableEq e]
    (A : Matrix e e ℂ) (j : Fin (Fintype.card e)) :
    ∃ i : e, singularValuesSorted A j = singularValues A i := by
  have h_mem : singularValuesSorted A j ∈ Multiset.sort (Finset.univ.val.map (singularValues A)) (· ≥ ·) := by
    simp [singularValuesSorted]
  rw [Multiset.mem_sort] at h_mem
  simp at h_mem
  obtain ⟨i, hi⟩ := h_mem
  exact ⟨i, hi.symm⟩

/-- Stronger version of `singularValues_compoundMatrix_eq` that exposes the permutation. -/
lemma singularValues_compoundMatrix_perm (M : Matrix d d ℂ) (k : ℕ) :
    ∃ σ : {S : Finset d // S.card = k} ≃ {S : Finset d // S.card = k},
    ∀ S, singularValues (compoundMatrix M k) (σ S) =
    ∏ i : Fin k, singularValues M (S.1.orderEmbOfFin S.2 i) := by
  unfold singularValues
  have h_eigenvalues : ∃ σ : {S : Finset d // S.card = k} ≃ {S : Finset d // S.card = k}, (Matrix.IsHermitian.eigenvalues (isHermitian_mul_conjTranspose_self (compoundMatrix M k).conjTranspose) ∘ σ) = fun S => ∏ i : Fin k, (Matrix.IsHermitian.eigenvalues (isHermitian_mul_conjTranspose_self M.conjTranspose)) (S.1.orderEmbOfFin S.2 i) := by
    apply IsHermitian.eigenvalues_eq_of_unitary_similarity_diagonal
    rotate_right
    exact compoundMatrix (Matrix.IsHermitian.eigenvectorUnitary (isHermitian_mul_conjTranspose_self M.conjTranspose)) k
    · exact compoundMatrix_unitary _ (by simp [Matrix.unitaryGroup]) _
    · have h_compoundMatrix_mul : compoundMatrix (M.conjTranspose * M) k = compoundMatrix M.conjTranspose k * compoundMatrix M k := by
        exact compoundMatrix_mul _ _ _
      have h_compoundMatrix_conjTranspose : compoundMatrix M.conjTranspose k = (compoundMatrix M k).conjTranspose := by
        exact compoundMatrix_conjTranspose M k
      have := Matrix.IsHermitian.spectral_theorem (isHermitian_mul_conjTranspose_self M.conjTranspose)
      convert congr_arg (fun x => compoundMatrix x k) this using 1 <;> simp [h_compoundMatrix_mul, h_compoundMatrix_conjTranspose]
      rw [compoundMatrix_mul, compoundMatrix_mul]
      rw [← compoundMatrix_conjTranspose]
      rw [compoundMatrix_diagonal]; simp [Matrix.mul_assoc]
      congr! 3
  obtain ⟨σ, hσ⟩ := h_eigenvalues
  use σ
  intro S
  simp_all [funext_iff]
  rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num [Finset.prod_nonneg, Real.sqrt_nonneg]
  · rw [← Finset.prod_mul_distrib, Finset.prod_congr rfl fun _ _ => Real.mul_self_sqrt (_)]
    intro i hi; exact (by apply Matrix.eigenvalues_conjTranspose_mul_self_nonneg)
  · refine Finset.prod_nonneg fun i _ => ?_
    exact eigenvalues_conjTranspose_mul_self_nonneg M _

/-- Converse of `singularValues_compoundMatrix_eq`: every singular value of the
    compound matrix is a product of singular values of M over some k-subset. -/
lemma singularValues_compoundMatrix_rev (M : Matrix d d ℂ) (k : ℕ)
    (j : {S : Finset d // S.card = k}) :
    ∃ (S : {S : Finset d // S.card = k}),
    singularValues (compoundMatrix M k) j =
    ∏ i : Fin k, singularValues M (S.1.orderEmbOfFin S.2 i) := by
  obtain ⟨σ, hσ⟩ := singularValues_compoundMatrix_perm M k
  exact ⟨σ.symm j, by rw [← hσ]; simp⟩

set_option backward.isDefEq.respectTransparency false in
/-- There exists a bijection `σ : Fin (card d) ≃ d` such that
    `singularValues M (σ i) = singularValuesSorted M i` for all `i`. -/
lemma exists_sorting_equiv (M : Matrix d d ℂ) :
    ∃ σ : Fin (Fintype.card d) ≃ d,
    ∀ i, singularValues M (σ i) = singularValuesSorted M i := by
  -- Apply the lemma `exists_subset_prod_eq_sorted_prod` to obtain the bijection `σ`.
  have h_bij : ∃ σ : Fin (Fintype.card d) ≃ d, ∀ i, singularValues M (σ i) = singularValuesSorted M i := by
    have h_perm : Multiset.ofList (List.ofFn (singularValuesSorted M)) = Multiset.ofList (List.ofFn (singularValues M ∘ (Fintype.equivFin d).symm)) := by
      have h_multiset : Multiset.ofList (List.ofFn (singularValues M ∘ (Fintype.equivFin d).symm)) = Finset.univ.val.map (singularValues M) := by
        have h_multiset : Finset.univ.val = Multiset.map (fun i => (Fintype.equivFin d).symm i) (Finset.univ.val) := by
          exact Eq.symm (Multiset.map_univ_val_equiv (Fintype.equivFin d |> Equiv.symm))
        rw [h_multiset, Multiset.map_map]
        aesop
      have h_multiset_sorted : Multiset.ofList (List.ofFn (singularValuesSorted M)) = Multiset.map (singularValues M) Finset.univ.val := by
        have h_multiset_sorted_eq : List.ofFn (singularValuesSorted M) = Multiset.sort (Multiset.map (singularValues M) Finset.univ.val) (· ≥ ·) := by
          refine' List.ext_get _ _ <;> simp [List.ofFn_eq_map] at *; aesop (simp_config := { singlePass := true })
        exact h_multiset_sorted_eq ▸ by simp
      rw [h_multiset, h_multiset_sorted]
    have h_perm : List.Perm (List.ofFn (singularValuesSorted M)) (List.ofFn (singularValues M ∘ (Fintype.equivFin d).symm)) := by
      exact Multiset.coe_eq_coe.mp h_perm
    have h_perm : ∃ σ : Fin (Fintype.card d) ≃ Fin (Fintype.card d), ∀ i, singularValuesSorted M i = singularValues M (Fintype.equivFin d |>.symm (σ i)) := by
      have h_perm : ∀ {l1 l2 : List ℝ}, l1.Perm l2 → ∃ σ : Fin l1.length ≃ Fin l2.length, ∀ i, l1.get i = l2.get (σ i) := by
        intros l1 l2 h_perm; induction' h_perm with l1 l2 h_perm ih <;> simp_all
        · obtain ⟨σ, hσ⟩ := ‹∃ σ : Fin l2.length ≃ Fin h_perm.length, ∀ i : Fin l2.length, l2[i] = h_perm[σ i]›; use Equiv.ofBijective (fun i => Fin.cases 0 (fun i => Fin.succ (σ i)) i) ⟨fun i j hij => ?_, fun i => ?_⟩
          simp_all [Fin.forall_fin_succ]
          · rcases i with ⟨_ | i, hi⟩ <;> rcases j with ⟨_ | j, hj⟩ <;> simp_all [Fin.ext_iff]
            simpa [Fin.ext_iff] using σ.injective (Fin.ext hij)
          · refine i.cases ?_ ?_
            · simp [Fin.exists_fin_succ]
            · simp only [Fin.exists_fin_succ, Fin.cases_zero, Fin.cases_succ, Fin.succ_inj]
              exact fun i => Or.inr ⟨σ.symm i, by simp⟩
        · refine' ⟨Equiv.swap ⟨0, by simp⟩ ⟨1, by simp⟩, _⟩; simp [Fin.forall_fin_succ]; aesop
        · rename_i h₁ h₂ h₃ h₄
          obtain ⟨σ₁, hσ₁⟩ := h₃
          obtain ⟨σ₂, hσ₂⟩ := h₄
          use σ₁.trans σ₂
          simp [hσ₁, hσ₂]
      obtain ⟨σ, hσ⟩ := h_perm ‹_›
      refine ⟨Equiv.ofBijective (fun i => ⟨σ ⟨i, ?_⟩, ?_⟩) ⟨?_, ?_⟩, ?_⟩
      · simp
      · exact lt_of_lt_of_le (Fin.is_lt _) (by simp)
      · norm_num [Function.Injective, Function.Surjective]
        exact fun i j hij => Fin.ext <| by simpa [Fin.ext_iff] using σ.injective <| Fin.ext hij
      · intro b
        obtain ⟨a, ha⟩ : ∃ a : Fin (List.ofFn (singularValuesSorted M)).length, σ a = ⟨b, by simp⟩ := by
          exact σ.surjective _
        use ⟨a, lt_of_lt_of_le a.2 (by simp)⟩
        exact Fin.ext (by simp [ha])
      · intro i
        specialize hσ ⟨i, by simp⟩
        simp_all
    exact ⟨Equiv.trans h_perm.choose (Fintype.equivFin d |> Equiv.symm), fun i => h_perm.choose_spec i ▸ rfl⟩
  exact ⟨h_bij.choose, fun i => by simpa only [Equiv.symm_apply_eq] using h_bij.choose_spec i⟩

/-- For any k-subset S of d, the product of singular values over S is ≤ the
    product of the top k sorted singular values. -/
lemma prod_singularValues_subset_le_sorted_prod (M : Matrix d d ℂ) (k : ℕ)
    (hk : k ≤ Fintype.card d) (S : {S : Finset d // S.card = k}) :
    ∏ i : Fin k, singularValues M (S.1.orderEmbOfFin S.2 i) ≤
    ∏ i : Fin k, singularValuesSorted M ⟨i.val, by omega⟩ := by
  obtain ⟨σ, hσ⟩ := exists_sorting_equiv M
  -- Define g : Fin k → Fin (card d) as σ⁻¹ ∘ (S.orderEmbOfFin)
  set g : Fin k → Fin (Fintype.card d) := fun i => σ.symm (S.1.orderEmbOfFin S.2 i)
  have hg_eq : ∀ i, singularValues M (S.1.orderEmbOfFin S.2 i) = singularValuesSorted M (g i) := by
    intro i
    simp [g]
    rw [← hσ]
    simp
  simp_rw [hg_eq]
  apply prod_le_prod_sorted (singularValuesSorted_antitone M) (singularValuesSorted_nonneg M) k hk g
  intro i j hij
  simpa [g] using congr_arg σ hij

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
lemma exists_subset_prod_eq_sorted_prod (M : Matrix d d ℂ) (k : ℕ)
    (hk : k ≤ Fintype.card d) :
    ∃ S : {S : Finset d // S.card = k},
    ∏ i : Fin k, singularValues M (S.1.orderEmbOfFin S.2 i) =
    ∏ i : Fin k, singularValuesSorted M ⟨i.val, by omega⟩ := by
  by_contra h_contra
  obtain ⟨σ, hσ⟩ : ∃ σ : Fin (Fintype.card d) ≃ d, ∀ i : Fin (Fintype.card d), singularValues M (σ i) = singularValuesSorted M i := by
    have h_perm : Multiset.ofList (List.ofFn (singularValuesSorted M)) = Multiset.ofList (List.ofFn (singularValues M ∘ (Fintype.equivFin d).symm)) := by
      have h_perm : Multiset.ofList (List.ofFn (singularValuesSorted M)) = Multiset.ofList (List.ofFn (singularValues M ∘ (Fintype.equivFin d).symm)) := by
        have h_sorted : List.ofFn (singularValuesSorted M) = Multiset.sort (Multiset.map (singularValues M) Finset.univ.val) (· ≥ ·) := by
          refine' List.ext_get _ _ <;> simp
          exact fun n i => rfl
        simp [h_sorted, List.ofFn_eq_map]
        refine' Multiset.eq_of_le_of_card_le _ _ <;> simp [Multiset.le_iff_count]
        intro a; rw [Multiset.count_map]; simp [List.count]
        rw [← Multiset.toFinset_card_of_nodup] <;> norm_num [Finset.card_image_of_injective, Function.Injective]
        · rw [List.countP_eq_length_filter]
          simp [Finset.card]
          rw [← List.toFinset_card_of_nodup] <;> norm_num [List.nodup_finRange]
          · rw [Finset.card_filter]; simp [eq_comm, Fintype.equivFin]
            rw [← Multiset.toFinset_card_of_nodup] <;> norm_num [Finset.card_image_of_injective, Function.Injective]
            · refine' le_of_eq _; rw [Finset.card_filter, Finset.card_filter]; rw [← Finset.sum_bij (fun x _ => (Fintype.equivFin d) x)]; aesop
              · exact fun x _ y _ h => Fintype.equivFin d |>.injective h ▸ rfl
              · exact fun b _ => ⟨(Fintype.equivFin d).symm b, Finset.mem_univ _, by simp⟩
              · simp [Fintype.equivFin]
            · exact Multiset.Nodup.filter _ (Finset.nodup _)
          · exact List.Nodup.filter _ (List.nodup_finRange _)
        · exact Multiset.Nodup.filter _ (Finset.nodup _)
      exact h_perm.trans (by simp)
    have h_perm : List.Perm (List.ofFn (singularValuesSorted M)) (List.ofFn (singularValues M ∘ (Fintype.equivFin d).symm)) := by
      exact Multiset.coe_eq_coe.mp h_perm
    have h_perm : ∃ σ : Fin (Fintype.card d) ≃ Fin (Fintype.card d), List.ofFn (singularValuesSorted M) = List.map (fun i => singularValues M ((Fintype.equivFin d).symm (σ i))) (List.finRange (Fintype.card d)) := by
      have := h_perm
      have h_perm : ∀ {l₁ l₂ : List ℝ}, List.Perm l₁ l₂ → ∃ σ : Fin l₁.length ≃ Fin l₂.length, l₁ = List.map (fun i => l₂.get (σ i)) (List.finRange l₁.length) := by
        intro l₁ l₂ h_perm
        induction' h_perm with l₁ l₂ h_perm ih
        · aesop
        · rename_i a_ih
          obtain ⟨σ, hσ⟩ := a_ih
          use Equiv.ofBijective (fun i => Fin.cases ⟨0, by simp⟩ (fun i => Fin.succ (σ i)) i) ⟨fun i j hij => ?_, fun i => ?_⟩
          · simp [List.finRange_succ] at *
            exact hσ
          · rcases i with ⟨_ | i, hi⟩ <;> rcases j with ⟨_ | j, hj⟩ <;> simp [Fin.ext_iff] at hij ⊢
            simpa [Fin.ext_iff] using σ.injective (Fin.ext hij) |> fun h => by simpa [Fin.ext_iff] using h;
          · rcases i with ⟨_ | i, hi⟩
            · exact ⟨⟨0, by simp⟩, rfl⟩
            · exact ⟨Fin.succ (σ.symm ⟨i, by simpa using hi⟩), by simp⟩
        · use Equiv.swap ⟨0, by simp⟩ ⟨1, by simp⟩; simp [List.finRange_succ]
          refine' List.ext_get _ _ <;> simp [Function.comp]
          intro n hn; rcases n with (_ | _ | n) <;> trivial
        · rename_i h₁ h₂ h₃ h₄
          obtain ⟨σ₁, hσ₁⟩ := h₃
          obtain ⟨σ₂, hσ₂⟩ := h₄
          use σ₁.trans σ₂
          simp [hσ₁, hσ₂]
      obtain ⟨σ, hσ⟩ := h_perm ‹_›
      simp [List.ofFn_eq_map] at hσ ⊢
      generalize_proofs at *; (
      exact ⟨Equiv.ofBijective (fun i => ⟨σ ⟨i, by simp⟩, by solve_by_elim⟩) ⟨fun i j hij => by simpa [Fin.ext_iff] using σ.injective (Fin.ext <| by simpa [Fin.ext_iff] using hij), fun i => by
        obtain ⟨a, ha⟩ := σ.surjective ⟨i, by simp⟩
        exact ⟨⟨a, by simpa using a.2⟩, Fin.ext <| by simpa [Fin.ext_iff] using congr_arg Fin.val ha⟩⟩, fun i => by simpa [Fin.ext_iff] using congr_arg (fun l => l[i]!) hσ⟩)
    obtain ⟨σ, hσ⟩ := h_perm
    use Equiv.ofBijective (fun i => (Fintype.equivFin d).symm (σ i)) ⟨fun i j hij => by simpa [Fin.ext_iff] using σ.injective (by simpa [Fin.ext_iff] using hij), fun i => by
      exact ⟨σ.symm (Fintype.equivFin d i), by simp⟩;⟩
    intro i
    replace hσ := congr_arg (fun l => l[i]!) hσ
    simp_all
  refine' h_contra ⟨⟨Finset.image σ (Finset.univ.filter fun i => i.val < k), _⟩, _⟩ <;> simp_all
  rw [Finset.card_image_of_injective _ σ.injective, Finset.card_eq_of_bijective]
  use fun i hi => ⟨i, by linarith⟩
  all_goals norm_num [Fin.ext_iff] at *
  have h_prod_eq : ∏ x ∈ Finset.image σ (Finset.univ.filter fun i : Fin (Fintype.card d) => i.val < k), singularValues M x = ∏ i : Fin k, singularValuesSorted M ⟨i.val, by omega⟩ := by
    rw [Finset.prod_image] <;> simp [hσ]
    refine' Finset.prod_bij (fun i hi => ⟨i, by linarith [Fin.is_lt i, Finset.mem_filter.mp hi]⟩) _ _ _ _ <;> simp [Fin.ext_iff]
    exact fun b => ⟨⟨b, by linarith [Fin.is_lt b]⟩, by simp, rfl⟩
  convert h_prod_eq using 1
  rw [← Finset.prod_image]
  · congr! 1
    refine' Finset.eq_of_subset_of_card_le (Finset.image_subset_iff.mpr fun i _ => _) _ <;> simp [Finset.card_image_of_injective, Function.Injective]
    rw [Finset.card_eq_of_bijective]
    use fun i hi => ⟨i, by linarith⟩
    · exact fun a ha => ⟨a, Finset.mem_filter.mp ha |>.2, rfl⟩
    · grind
    · simp +contextual [Fin.ext_iff]
  · exact fun x _ y _ hxy => by simpa [Fin.ext_iff] using hxy

lemma prod_singularValuesSorted_eq_compoundSV (M : Matrix d d ℂ) (k : ℕ)
    (hk : k ≤ Fintype.card d) :
    ∏ i : Fin k, singularValuesSorted M ⟨i.val, by omega⟩ =
    singularValuesSorted (compoundMatrix M k) ⟨0, by
      have : Fintype.card {S : Finset d // S.card = k} = (Fintype.card d).choose k := by
        simp [Fintype.card_subtype]
      rw [this]; exact Nat.choose_pos hk⟩ := by
  set hcard : 0 < Fintype.card {S : Finset d // S.card = k} := by
    simp [Fintype.card_subtype]; exact Nat.choose_pos hk
  apply le_antisymm
  · obtain ⟨S₀, hS₀⟩ := exists_subset_prod_eq_sorted_prod M k hk
    obtain ⟨j₀, hj₀⟩ := singularValues_compoundMatrix_eq M k S₀
    obtain ⟨idx, hidx⟩ := singularValues_mem_sorted (compoundMatrix M k) j₀
    rw [← hS₀, ← hj₀, hidx]
    have : NeZero (Fintype.card {S : Finset d // S.card = k}) := ⟨by omega⟩
    exact singularValuesSorted_antitone (compoundMatrix M k) (Fin.zero_le idx)
  · obtain ⟨j, hj⟩ := singularValuesSorted_mem_values (compoundMatrix M k) ⟨0, hcard⟩
    obtain ⟨S, hS⟩ := singularValues_compoundMatrix_rev M k j
    rw [hj, hS]
    exact prod_singularValues_subset_le_sorted_prod M k hk S

/--
The **Rayleigh quotient bound**:
For a Hermitian matrix H with eigenvalues λ, we have
`v† H v ≤ (max λ) · v† v` for all v. -/
lemma IsHermitian.inner_le_sup_eigenvalue_mul_inner
    {e : Type*} [Fintype e] [DecidableEq e]
    (H : Matrix e e ℂ) (hH : H.IsHermitian)
    (he : 0 < Fintype.card e)
    (v : e → ℂ) :
    Complex.re (star v ⬝ᵥ H.mulVec v) ≤
    Finset.sup' Finset.univ
      (Finset.univ_nonempty_iff.mpr (Fintype.card_pos_iff.mp he))
      hH.eigenvalues * Complex.re (star v ⬝ᵥ v) := by
  have := hH.spectral_theorem
  -- Let $w = U^* v$, then $v^* H v = w^* D w$.
  set w : e → ℂ := star (hH.eigenvectorUnitary : Matrix e e ℂ) |> Matrix.mulVec <| v
  have h_eq : (star v ⬝ᵥ H *ᵥ v).re = (star w ⬝ᵥ (Matrix.diagonal (RCLike.ofReal ∘ hH.eigenvalues)) *ᵥ w).re := by
    replace this := congr_arg (fun m => star v ⬝ᵥ m *ᵥ v) this; simp_all [Matrix.mul_assoc]
    simp +zetaDelta at *
    simp [Matrix.dotProduct_mulVec, Matrix.star_mulVec]
    congr! 3
    ext i j; simp [Matrix.mul_apply, Matrix.diagonal]
  -- Since $D$ is diagonal with eigenvalues $\lambda_i$, we have $w^* D w = \sum_{i} \lambda_i |w_i|^2$.
  have h_diag : (star w ⬝ᵥ (Matrix.diagonal (RCLike.ofReal ∘ hH.eigenvalues)) *ᵥ w).re = ∑ i, (hH.eigenvalues i) * ‖w i‖ ^ 2 := by
    simp [dotProduct, Matrix.mulVec, Finset.mul_sum _ _ _, mul_assoc, mul_comm,]
    simp [Complex.normSq, Complex.sq_norm, diagonal]
    rw [← Finset.sum_sub_distrib]; refine' Finset.sum_congr rfl fun i hi => _; rw [Finset.sum_eq_single i, Finset.sum_eq_single i] <;> simp +contextual; ring_nf
    · exact fun j hj => Or.inl (by rw [if_neg (Ne.symm hj)]; norm_num)
    · exact fun j hj => Or.inl (by rw [if_neg (Ne.symm hj)]; norm_num)
  -- Since $U$ is unitary, we have $\|w\|^2 = \|v\|^2$.
  have h_unitary : ∑ i, ‖w i‖ ^ 2 = (star v ⬝ᵥ v).re := by
    have h_unitary : ∀ (U : Matrix e e ℂ), U.conjTranspose * U = 1 → ∀ (v : e → ℂ), ∑ i, ‖(U.mulVec v) i‖ ^ 2 = ∑ i, ‖v i‖ ^ 2 := by
      intro U hU v
      have h_unitary : (star (U.mulVec v) ⬝ᵥ U.mulVec v) = (star v ⬝ᵥ v) := by
        have h_unitary : (star (U.mulVec v) ⬝ᵥ U.mulVec v) = (star v ⬝ᵥ (Uᴴ * U).mulVec v) := by
          simp [Matrix.mulVec, dotProduct]
          simp [Matrix.mul_apply, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _, Finset.sum_mul]
          exact Finset.sum_comm.trans (Finset.sum_congr rfl fun _ _ => Finset.sum_comm) |> Eq.trans <| Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
        rw [h_unitary, hU, Matrix.one_mulVec]
      convert congr_arg Complex.re h_unitary using 1 <;> simp [sq]; ring_nf!
      · simp [dotProduct, sq]; ring_nf!
        simp [Complex.normSq, Complex.sq_norm]; ring_nf!
      · simp [dotProduct]
        simp [← sq, Complex.normSq_apply, Complex.sq_norm]
    convert h_unitary (star (hH.eigenvectorUnitary : Matrix e e ℂ)) _ v using 1 <;> norm_num [Matrix.mulVec, dotProduct]
    · norm_num [Complex.normSq, Complex.sq_norm]
    · simp [Matrix.star_eq_conjTranspose]
      simp [Matrix.IsHermitian.eigenvectorUnitary]
  rw [h_eq, h_diag, ← h_unitary, Finset.mul_sum _ _ _]
  exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (Finset.le_sup' (fun i => hH.eigenvalues i) (Finset.mem_univ i)) (sq_nonneg _)


end
