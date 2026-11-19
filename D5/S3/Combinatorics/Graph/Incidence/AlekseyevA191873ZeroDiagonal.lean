/- GID: D5/S3/Combinatorics/Graph/Incidence/AlekseyevA191873ZeroDiagonal
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Incidence/AlekseyevA191873ZeroDiagonal
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Zero-diagonal and unrestricted rectangle-free maxima agree for n at least three. -/

/-
admission_basis: open-problem-resolution (#23717; Proved).
Direct frozen dependencies:
  D5/S0/Automata/TwoStateCertificateWidth.rotate_ne
    (declaration statement_id: sha256:c19f186363328657bba190013f2e602d331392250cff0fd1cb4db82fc358b2f8).
  D5/S3/Combinatorics/Graph/Domination/TrapezohedralMinimalDomination.rotate_twice_ne
    (declaration statement_id: sha256:4db858c0807bdecf3630d04b87692291da0363c836a439d43858ecccf66b4d99).
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/29985.
The public predicates inline the one-entry count from #23717; the proofs use
hammingNorm (Function.uncurry M) through weight_encoding without a duplicate definition.
result: proof_shape: content; escape_witness: zero_transversal.
The Hall obstruction, cyclic lower bound, and full-row estimate occur in result.
binary_ne_one: proof_shape: bind-only; escape_witness: none; consumers: zero_transversal.
weight_encoding: proof_shape: bind-only; escape_witness: none; consumers: weight_rows, permute_columns, transpose_weight, trim_matrix, free_weight_lt, matrixGraph_card, result.
weight_rows: proof_shape: bind-only; escape_witness: none; consumers: full_row_bound, cycle_matrix.
weight_le: proof_shape: bind-only; escape_witness: none; consumers: free_weight_lt.
zero_transversal: proof_shape: content; escape_witness: none; consumers: result.
permute_columns: proof_shape: bind-only; escape_witness: none; consumers: result.
full_row_bound: proof_shape: content; escape_witness: none; consumers: result.
transpose_weight: proof_shape: bind-only; escape_witness: none; consumers: result.
transpose_free: proof_shape: bind-only; escape_witness: none; consumers: result.
rotate_no_fixed: proof_shape: bind-only; escape_witness: none; consumers: cycle_matrix.
cycle_matrix: proof_shape: content; escape_witness: none; consumers: result.
trim_matrix: proof_shape: bind-only; escape_witness: none; consumers: result.
free_weight_lt: proof_shape: bind-only; escape_witness: none; consumers: result.
matrixGraph_le: proof_shape: bind-only; escape_witness: none; consumers: matrix_weight_le_zarankiewicz.
matrixGraph_card: proof_shape: bind-only; escape_witness: none; consumers: matrix_weight_le_zarankiewicz, extremizer.
rectangle_to_copy: proof_shape: bind-only; escape_witness: none; consumers: matrixGraph_free.
copy_to_rectangle: proof_shape: bind-only; escape_witness: none; consumers: matrixGraph_free.
matrixGraph_free: proof_shape: bind-only; escape_witness: none; consumers: matrix_weight_le_zarankiewicz, extremizer.
matrixGraph_adjMatrix: proof_shape: bind-only; escape_witness: none; consumers: extremizer.
matrix_weight_le_zarankiewicz: proof_shape: bind-only; escape_witness: none; consumers: extremizer.
extremizer: proof_shape: bind-only; escape_witness: none; consumers: result.
-/

import D5.S0.Automata.TwoStateCertificateWidth
import D5.S3.Combinatorics.Graph.Domination.TrapezohedralMinimalDomination
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Combinatorics.SimpleGraph.Extremal.Zarankiewicz
import Mathlib.InformationTheory.Hamming

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace D5.S3.Combinatorics.Graph.Incidence.AlekseyevA191873ZeroDiagonal

/-- Four ones in any two distinct rows and any two distinct columns. -/
def HasRectangle {n : ℕ} (M : Matrix (Fin n) (Fin n) (Fin 2)) : Prop :=
  ∃ (i i' j j' : Fin n), i ≠ i' ∧ j ≠ j' ∧
    M i j = 1 ∧ M i j' = 1 ∧ M i' j = 1 ∧ M i' j' = 1

/-- Attained weights with no rectangle and all main-diagonal entries zero. -/
def diagonalWeights (n : ℕ) : Set ℕ :=
  {w | ∃ (M : Matrix (Fin n) (Fin n) (Fin 2)),
    ¬ HasRectangle M ∧ (∀ (i : Fin n), M i i = 0) ∧ ((Finset.univ : Finset (Fin n × Fin n)).filter
      (fun ij => M ij.1 ij.2 = 1)).card = w}

/-- Physically possible entry counts that force a rectangle in every binary matrix. -/
def forcingCounts (n : ℕ) : Set ℕ :=
  {k | k ≤ n * n ∧ ∀ (M : Matrix (Fin n) (Fin n) (Fin 2)),
    ((Finset.univ : Finset (Fin n × Fin n)).filter
      (fun ij => M ij.1 ij.2 = 1)).card = k → HasRectangle M}

/-- Alekseyev's conjecture in OEIS A191873: for every n at least three,
the diagonal-constrained extremum equals the unrestricted Zarankiewicz number
and is one less than the least number of entries forcing a rectangle.
The extrema and threshold must exist; they are not extra hypotheses. -/
def claim : Prop :=
  ∀ (n : ℕ), 3 ≤ n → ∃ (d k : ℕ),
    IsGreatest (diagonalWeights n) d ∧
    IsLeast (forcingCounts n) k ∧
    d = SimpleGraph.zarankiewicz n n 2 2 ∧ d + 1 = k


open Finset

private theorem binary_ne_one (x : Fin 2) : x ≠ 1 ↔ x = 0 := by
  exact ⟨fun h => not_not.mp (mt (Fin.eq_one_of_ne_zero x) h),
    fun h => by simpa only [h] using (show (0 : Fin 2) ≠ 1 by decide)⟩

private theorem weight_encoding {n : ℕ} (M : Matrix (Fin n) (Fin n) (Fin 2)) :
    hammingNorm (Function.uncurry M) =
      ((Finset.univ : Finset (Fin n × Fin n)).filter (fun ij => M ij.1 ij.2 = 1)).card := by
  unfold hammingNorm
  congr 1
  ext ij
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Function.uncurry]
  exact ⟨Fin.eq_one_of_ne_zero _, fun h => by simp only [h, ne_eq, one_ne_zero, not_false_eq_true]⟩

private theorem weight_rows {n : ℕ} (M : Matrix (Fin n) (Fin n) (Fin 2)) :
    hammingNorm (Function.uncurry M) = ∑ i, ((univ : Finset (Fin n)).filter (fun j => M i j = 1)).card := by
  classical
  simp only [weight_encoding, Finset.card_filter]
  rw [← Finset.univ_product_univ, Finset.sum_product]

private theorem weight_le {n : ℕ} (M : Matrix (Fin n) (Fin n) (Fin 2)) :
    hammingNorm (Function.uncurry M) ≤ n * n := by
  exact (hammingNorm_le_card_fintype).trans (by simp)

private theorem zero_transversal {n : ℕ} (M : Matrix (Fin n) (Fin n) (Fin 2))
    (hR : ¬ HasRectangle M) (hr : ∀ i, ∃ j, M i j = 0)
    (hc : ∀ j, ∃ i, M i j = 0) :
    ∃ e : Equiv.Perm (Fin n), ∀ i, M i (e i) = 0 := by
  classical
  let t : Fin n → Finset (Fin n) := fun i => univ.filter (fun j => M i j = 0)
  have hall : ∀ s : Finset (Fin n), s.card ≤ (s.biUnion t).card := by
    intro s
    by_contra! h
    let u := s.biUnion t
    change u.card < s.card at h
    have hu : ∀ i ∈ s, ∀ j ∈ uᶜ, M i j = 1 := by
      intro i hi j hj
      by_contra h1
      have h0 := (binary_ne_one _).mp h1
      have : j ∈ u := mem_biUnion.mpr ⟨i, hi, by simp [t, h0]⟩
      exact (mem_compl.mp hj) this
    have hs : 1 < s.card := by
      by_contra! hsmall
      obtain ⟨i, hi⟩ := Finset.card_pos.mp (by omega : 0 < s.card)
      obtain ⟨j, hj⟩ := hr i
      have hju : j ∈ u := mem_biUnion.mpr ⟨i, hi, by simp [t, hj]⟩
      have : 0 < u.card := Finset.card_pos.mpr ⟨j, hju⟩
      omega
    have ht : 1 < (uᶜ).card := by
      have hsu : s.card ≤ n := by exact card_finset_fin_le s
      have heq : (uᶜ).card = n - u.card := by simp [Finset.card_compl]
      by_contra! hh
      have hsall : s = univ := eq_univ_of_card s (by simpa using (show s.card = n by omega))
      have huall : u = univ := by
        apply eq_univ_of_forall
        intro j
        obtain ⟨i, hi⟩ := hc j
        exact mem_biUnion.mpr ⟨i, by simp [hsall], by simp [t, hi]⟩
      have : u.card = n := by simp [huall]
      omega
    obtain ⟨i, hi, i', hi', hii⟩ := Finset.one_lt_card.mp hs
    obtain ⟨j, hj, j', hj', hjj⟩ := Finset.one_lt_card.mp ht
    exact hR ⟨i, i', j, j', hii, hjj, hu i hi j hj, hu i hi j' hj',
      hu i' hi' j hj, hu i' hi' j' hj'⟩
  obtain ⟨f, hf, ht⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective' t).mp hall
  exact ⟨Equiv.ofBijective f ((Finite.injective_iff_bijective).mp hf),
    fun i => (mem_filter.mp (ht i)).2⟩

private theorem permute_columns {n : ℕ} (M : Matrix (Fin n) (Fin n) (Fin 2))
    (e : Equiv.Perm (Fin n)) :
    hammingNorm (Function.uncurry (fun i j => M i (e j))) = hammingNorm (Function.uncurry M) ∧
    (¬ HasRectangle M → ¬ HasRectangle (fun i j => M i (e j))) := by
  classical
  constructor
  · simp only [weight_encoding]
    apply Finset.card_bij (fun ij _ => (ij.1, e ij.2))
    · intro a ha
      simpa using ha
    · intro a ha b hb hab
      apply Prod.ext
      · have hh := congrArg (fun p : Fin n × Fin n => p.1) hab
        exact hh
      · exact e.injective (congrArg (fun p : Fin n × Fin n => p.2) hab)
    · intro b hb
      exact ⟨(b.1, e.symm b.2), by simpa using hb, by simp⟩
  · rintro h ⟨i,i',j,j',hi,hj,h1,h2,h3,h4⟩
    exact h ⟨i,i',e j,e j',hi,fun he => hj (e.injective he),h1,h2,h3,h4⟩

private theorem full_row_bound {n : ℕ} (M : Matrix (Fin n) (Fin n) (Fin 2))
    (hR : ¬ HasRectangle M) (i : Fin n) (hi : ∀ j, M i j = 1) :
    hammingNorm (Function.uncurry M) < 2*n := by
  classical
  let d : Fin n → ℕ := fun r => ((univ : Finset (Fin n)).filter (fun j => M r j = 1)).card
  have hrow : ∀ r, r ≠ i → d r ≤ 1 := by
    intro r hr
    apply Finset.card_le_one.mpr
    intro j hj k hk
    by_contra hjk
    exact hR ⟨r,i,j,k,hr,hjk,(mem_filter.mp hj).2,(mem_filter.mp hk).2,hi j,hi k⟩
  have hid : d i = n := by simp [d, hi]
  have hsum : ∑ r ∈ (univ : Finset (Fin n)).erase i, d r ≤ n-1 := by
    calc
      _ ≤ ∑ r ∈ (univ : Finset (Fin n)).erase i, 1 :=
        sum_le_sum (fun r hr => hrow r (mem_erase.mp hr).1)
      _ = n-1 := by simp
  rw [weight_rows, ← sum_erase_add _ _ (mem_univ i)]
  change (∑ r ∈ univ.erase i, d r) + d i < 2*n
  rw [hid]
  have := i.isLt
  omega

private theorem transpose_weight {n : ℕ} (M : Matrix (Fin n) (Fin n) (Fin 2)) :
    hammingNorm (Function.uncurry M.transpose) = hammingNorm (Function.uncurry M) := by
  classical
  simp only [weight_encoding]
  apply Finset.card_bij (fun ij _ => (ij.2, ij.1))
  · intro a ha
    exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp ha).2⟩
  · intro a ha b hb hab; exact (Prod.swap_injective hab)
  · intro b hb; exact ⟨(b.2,b.1), mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hb).2⟩, rfl⟩

private theorem transpose_free {n : ℕ} (M : Matrix (Fin n) (Fin n) (Fin 2))
    (hR : ¬ HasRectangle M) : ¬ HasRectangle M.transpose := by
  rintro ⟨i,i',j,j',hi,hj,a,b,c,d⟩
  exact hR ⟨j,j',i,i',hj,hi,a,c,b,d⟩


private theorem rotate_no_fixed {n : ℕ} (hn : 3 ≤ n) (i : Fin n) : finRotate n i ≠ i := by
  exact D5.S0.Automata.TwoStateCertificateWidth.rotate_ne (by omega) i

private theorem cycle_matrix {n : ℕ} (hn : 3 ≤ n) :
    ∃ M : Matrix (Fin n) (Fin n) (Fin 2), ¬ HasRectangle M ∧ hammingNorm (Function.uncurry M) = 2*n := by
  classical
  let f := finRotate n
  have hperiod : ∀ i : Fin n, f (f i) ≠ i := by
    exact fun i => D5.S3.Combinatorics.Graph.Domination.TrapezohedralMinimalDomination.rotate_twice_ne hn i
  let M : Matrix (Fin n) (Fin n) (Fin 2) := fun i j => if j=i ∨ j=f i then 1 else 0
  have hs : ∀ i j, M i j = 1 ↔ j=i ∨ j=f i := by
    intro i j
    simp only [M, ite_eq_left_iff, zero_ne_one, imp_false, not_not]
  refine ⟨M, ?_, ?_⟩
  · rintro ⟨i,k,j,l,hik,hjl,h1,h2,h3,h4⟩
    rcases (hs i j).mp h1 with h1|h1 <;>
      rcases (hs i l).mp h2 with h2|h2 <;>
      rcases (hs k j).mp h3 with h3|h3 <;>
      rcases (hs k l).mp h4 with h4|h4
    all_goals try { exact hjl (h1.trans h2.symm) }
    all_goals try { exact hik (h1.symm.trans h3) }
    all_goals try { exact hik ((finRotate n).injective (h1.symm.trans h3)) }
    all_goals try { exact hik (h2.symm.trans h4) }
    all_goals try { exact hik ((finRotate n).injective (h2.symm.trans h4)) }
    all_goals
      have ht := hperiod i
      have ht' := hperiod k
      apply ht
      dsimp [f] at *
      grind
  · rw [weight_rows]
    have hrow : ∀ i, ((univ : Finset (Fin n)).filter (fun j => M i j = 1)).card = 2 := by
      intro i
      have heq : (univ.filter (fun j => M i j = 1)) = {i, f i} := by
        ext j
        simp [hs]
      rw [heq, card_pair (Ne.symm (rotate_no_fixed hn i))]
    simp_rw [hrow]
    simp [Nat.mul_comm]


private theorem trim_matrix {n : ℕ} (M : Matrix (Fin n) (Fin n) (Fin 2))
    (hR : ¬ HasRectangle M) (k : ℕ) (hk : k ≤ hammingNorm (Function.uncurry M)) :
    ∃ B : Matrix (Fin n) (Fin n) (Fin 2), ¬ HasRectangle B ∧ hammingNorm (Function.uncurry B) = k := by
  classical
  rw [weight_encoding] at hk
  obtain ⟨s,hs,hcard⟩ := Finset.exists_subset_card_eq hk
  let B : Matrix (Fin n) (Fin n) (Fin 2) := fun i j => if (i,j) ∈ s then 1 else 0
  have hb : ∀ i j, B i j = 1 ↔ (i,j) ∈ s := by
    intro i j
    simp only [B, ite_eq_left_iff, zero_ne_one, imp_false, not_not]
  have hm : ∀ i j, B i j = 1 → M i j = 1 := by
    intro i j hij
    exact (mem_filter.mp (hs ((hb i j).mp hij))).2
  refine ⟨B, ?_, ?_⟩
  · rintro ⟨i,i',j,j',hi,hj,a,b,c,d⟩
    exact hR ⟨i,i',j,j',hi,hj,hm i j a,hm i j' b,hm i' j c,hm i' j' d⟩
  · rw [← hcard]
    simp only [weight_encoding]
    congr 1
    ext p
    simp only [mem_filter, mem_univ, true_and, hb]

private theorem free_weight_lt {n : ℕ} (hn : 3 ≤ n)
    (M : Matrix (Fin n) (Fin n) (Fin 2)) (hR : ¬ HasRectangle M) :
    hammingNorm (Function.uncurry M) < n*n := by
  classical
  have hle := weight_le M
  by_contra hh
  have heq : hammingNorm (Function.uncurry M) = n*n := by omega
  have hall : (univ.filter (fun p : Fin n × Fin n => M p.1 p.2 = 1)) = univ :=
    eq_univ_of_card _ (by simpa only [weight_encoding, Fintype.card_prod, Fintype.card_fin] using heq)
  have hfull : ∀ i j, M i j = 1 := by
    intro i j
    have hmem : (i,j) ∈ (univ.filter (fun p : Fin n × Fin n => M p.1 p.2 = 1)) := by
      rw [hall]
      exact mem_univ _
    exact (mem_filter.mp hmem).2
  let a : Fin n := ⟨0,by omega⟩
  let b : Fin n := ⟨1,by omega⟩
  have hab : a ≠ b := by exact not_eq_of_beq_eq_false rfl
  exact hR ⟨a,b,a,b,hab,hab,hfull a a,hfull a b,hfull b a,hfull b b⟩


open Finset SimpleGraph

private def matrixGraph {n : ℕ} (M : Matrix (Fin n) (Fin n) (Fin 2)) :
    SimpleGraph (Fin n ⊕ Fin n) :=
  SimpleGraph.fromRel fun x y => match x, y with
    | .inl i, .inr j => M i j = 1
    | _, _ => False

private theorem matrixGraph_le {n : ℕ} (M : Matrix (Fin n) (Fin n) (Fin 2)) :
    matrixGraph M ≤ completeBipartiteGraph (Fin n) (Fin n) := by
  intro x y h
  cases x <;> cases y <;> simp_all [matrixGraph, SimpleGraph.fromRel]

private theorem matrixGraph_card {n : ℕ} (M : Matrix (Fin n) (Fin n) (Fin 2)) :
    letI := Classical.decRel (matrixGraph M).Adj
    (matrixGraph M).edgeFinset.card = hammingNorm (Function.uncurry M) := by
  classical
  symm
  simp only [weight_encoding]
  apply Finset.card_bij (fun ij _ => s(Sum.inl ij.1, Sum.inr ij.2))
  · intro a ha
    simpa [matrixGraph, SimpleGraph.fromRel] using ha
  · intro a ha b hb hab
    simpa [Sym2.eq_iff, Prod.ext_iff] using hab
  · intro e
    induction e using Sym2.inductionOn with
    | _ x y =>
      cases x with
      | inl i =>
        cases y with
        | inl k => simp [matrixGraph, SimpleGraph.fromRel]
        | inr j =>
          intro h
          exact ⟨(i,j), by simpa [matrixGraph, SimpleGraph.fromRel] using h, rfl⟩
      | inr j =>
        cases y with
        | inl i =>
          intro h
          exact ⟨(i,j), by simpa [matrixGraph, SimpleGraph.fromRel] using h, Sym2.eq_swap⟩
        | inr l => simp [matrixGraph, SimpleGraph.fromRel]

private theorem rectangle_to_copy {n : ℕ} (M : Matrix (Fin n) (Fin n) (Fin 2))
    (h : HasRectangle M) :
    Nonempty (Copy (completeBipartiteGraph (Fin 2) (Fin 2)) (matrixGraph M)) := by
  classical
  obtain ⟨i,k,j,l,hik,hjl,a,b,c,d⟩ := h
  apply completeBipartiteGraph_isContained_iff.mpr
  refine ⟨{Sum.inl i, Sum.inl k}, {Sum.inr j, Sum.inr l}, ?_, ?_, ?_⟩
  · simp [hik]
  · simp [hjl]
  · intro x hx y hy
    simp only [Finset.mem_coe, mem_insert, mem_singleton] at hx hy
    rcases hx with rfl|rfl <;> rcases hy with rfl|rfl
    all_goals simpa [matrixGraph, SimpleGraph.fromRel] using (by assumption : M _ _ = 1)

private theorem copy_to_rectangle {n : ℕ} (M : Matrix (Fin n) (Fin n) (Fin 2))
    (f : Copy (completeBipartiteGraph (Fin 2) (Fin 2)) (matrixGraph M)) :
    HasRectangle M := by
  have a := f.toHom.map_adj (show (completeBipartiteGraph (Fin 2) (Fin 2)).Adj
    (.inl 0) (.inr 0) by simp)
  have b := f.toHom.map_adj (show (completeBipartiteGraph (Fin 2) (Fin 2)).Adj
    (.inl 0) (.inr 1) by simp)
  have c := f.toHom.map_adj (show (completeBipartiteGraph (Fin 2) (Fin 2)).Adj
    (.inl 1) (.inr 0) by simp)
  have d := f.toHom.map_adj (show (completeBipartiteGraph (Fin 2) (Fin 2)).Adj
    (.inl 1) (.inr 1) by simp)
  have hi : f (.inl 0) ≠ f (.inl 1) := fun h => by
    have := f.injective h
    simp at this
  have hj : f (.inr 0) ≠ f (.inr 1) := fun h => by
    have := f.injective h
    simp at this
  change (matrixGraph M).Adj (f (.inl 0)) (f (.inr 0)) at a
  change (matrixGraph M).Adj (f (.inl 0)) (f (.inr 1)) at b
  change (matrixGraph M).Adj (f (.inl 1)) (f (.inr 0)) at c
  change (matrixGraph M).Adj (f (.inl 1)) (f (.inr 1)) at d
  cases he0 : f (.inl 0) with
  | inl i =>
    cases he1 : f (.inr 0) with
    | inl q => rw [he0,he1] at a; simp [matrixGraph, SimpleGraph.fromRel] at a
    | inr j =>
      cases he2 : f (.inr 1) with
      | inl q => rw [he0,he2] at b; simp [matrixGraph, SimpleGraph.fromRel] at b
      | inr l =>
        cases he3 : f (.inl 1) with
        | inr q => rw [he3,he1] at c; simp [matrixGraph, SimpleGraph.fromRel] at c
        | inl k =>
          refine ⟨i,k,j,l,?_,?_,?_,?_,?_,?_⟩
          · simpa [he0,he3] using hi
          · simpa [he1,he2] using hj
          · rw [he0,he1] at a; simpa [matrixGraph, SimpleGraph.fromRel] using a
          · rw [he0,he2] at b; simpa [matrixGraph, SimpleGraph.fromRel] using b
          · rw [he3,he1] at c; simpa [matrixGraph, SimpleGraph.fromRel] using c
          · rw [he3,he2] at d; simpa [matrixGraph, SimpleGraph.fromRel] using d
  | inr j =>
    cases he1 : f (.inr 0) with
    | inr q => rw [he0,he1] at a; simp [matrixGraph, SimpleGraph.fromRel] at a
    | inl i =>
      cases he2 : f (.inr 1) with
      | inr q => rw [he0,he2] at b; simp [matrixGraph, SimpleGraph.fromRel] at b
      | inl k =>
        cases he3 : f (.inl 1) with
        | inl q => rw [he3,he1] at c; simp [matrixGraph, SimpleGraph.fromRel] at c
        | inr l =>
          refine ⟨i,k,j,l,?_,?_,?_,?_,?_,?_⟩
          · simpa [he1,he2] using hj
          · simpa [he0,he3] using hi
          · rw [he0,he1] at a; simpa [matrixGraph, SimpleGraph.fromRel] using a
          · rw [he3,he1] at c; simpa [matrixGraph, SimpleGraph.fromRel] using c
          · rw [he0,he2] at b; simpa [matrixGraph, SimpleGraph.fromRel] using b
          · rw [he3,he2] at d; simpa [matrixGraph, SimpleGraph.fromRel] using d

private theorem matrixGraph_free {n : ℕ} (M : Matrix (Fin n) (Fin n) (Fin 2)) :
    (completeBipartiteGraph (Fin 2) (Fin 2)).Free (matrixGraph M) ↔ ¬ HasRectangle M := by
  exact ⟨fun h hR => h (rectangle_to_copy M hR), fun h ⟨f⟩ => h (copy_to_rectangle M f)⟩

private theorem matrixGraph_adjMatrix {n : ℕ} (G : SimpleGraph (Fin n ⊕ Fin n)) [DecidableRel G.Adj]
    (hG : G ≤ completeBipartiteGraph (Fin n) (Fin n)) :
    matrixGraph ((G.adjMatrix (Fin 2)).submatrix Sum.inl Sum.inr) = G := by
  classical
  ext x y
  cases x with
  | inl i =>
    cases y with
    | inl k =>
      have : ¬ G.Adj (.inl i) (.inl k) := fun h => by simpa using hG h
      simp [matrixGraph, SimpleGraph.fromRel,this]
    | inr j => simp [matrixGraph, SimpleGraph.fromRel, SimpleGraph.adjMatrix, Matrix.submatrix]
  | inr j =>
    cases y with
    | inl i => simp [matrixGraph, SimpleGraph.fromRel, SimpleGraph.adjMatrix, Matrix.submatrix, G.adj_comm]
    | inr l =>
      have : ¬ G.Adj (.inr j) (.inr l) := fun h => by simpa using hG h
      simp [matrixGraph, SimpleGraph.fromRel,this]

private theorem matrix_weight_le_zarankiewicz {n : ℕ}
    (M : Matrix (Fin n) (Fin n) (Fin 2)) (hR : ¬ HasRectangle M) :
    hammingNorm (Function.uncurry M) ≤ SimpleGraph.zarankiewicz n n 2 2 := by
  classical
  have h := (SimpleGraph.zarankiewicz_le_iff (V := Fin n) (W := Fin n)
    (α := Fin 2) (β := Fin 2) (by simp) (by simp) (by simp) (by simp)
    (SimpleGraph.zarankiewicz n n 2 2)).mp le_rfl
    (matrixGraph_le M) ((matrixGraph_free M).mpr hR)
  simpa only [matrixGraph_card] using h

private theorem extremizer {n : ℕ} :
    ∃ M : Matrix (Fin n) (Fin n) (Fin 2), ¬ HasRectangle M ∧
      hammingNorm (Function.uncurry M) = SimpleGraph.zarankiewicz n n 2 2 ∧
      ∀ A : Matrix (Fin n) (Fin n) (Fin 2), ¬ HasRectangle A → hammingNorm (Function.uncurry A) ≤ hammingNorm (Function.uncurry M) := by
  classical
  let s : Finset (Matrix (Fin n) (Fin n) (Fin 2)) := univ.filter (fun M => ¬ HasRectangle M)
  have hs : s.Nonempty := by
    refine ⟨0, mem_filter.mpr ⟨mem_univ _, ?_⟩⟩
    simp [HasRectangle]
  obtain ⟨M,hM,hmax⟩ := Finset.exists_max_image s (fun M => hammingNorm (Function.uncurry M)) hs
  have hR : ¬ HasRectangle M := (mem_filter.mp hM).2
  have hmax' : ∀ A : Matrix (Fin n) (Fin n) (Fin 2), ¬ HasRectangle A → hammingNorm (Function.uncurry A) ≤ hammingNorm (Function.uncurry M) := by
    intro A hA
    exact hmax A (mem_filter.mpr ⟨mem_univ _,hA⟩)
  refine ⟨M,hR,le_antisymm (matrix_weight_le_zarankiewicz M hR) ?_,hmax'⟩
  apply (SimpleGraph.zarankiewicz_le_iff (V := Fin n) (W := Fin n)
    (α := Fin 2) (β := Fin 2) (by simp) (by simp) (by simp) (by simp) (hammingNorm (Function.uncurry M))).mpr
  intro G _ hG hf
  have hA : ¬ HasRectangle ((G.adjMatrix (Fin 2)).submatrix Sum.inl Sum.inr) := (matrixGraph_free _).mp (by
    rwa [matrixGraph_adjMatrix G hG])
  have hcard := matrixGraph_card ((G.adjMatrix (Fin 2)).submatrix Sum.inl Sum.inr)
  rw [matrixGraph_adjMatrix G hG] at hcard
  convert hcard.trans_le (hmax' _ hA)

theorem result : D5.S3.Combinatorics.Graph.Incidence.AlekseyevA191873ZeroDiagonal.claim := by
  classical
  intro n hn
  obtain ⟨M,hR,hZ,hmax⟩ := extremizer (n := n)
  obtain ⟨C,hC,hCw⟩ := cycle_matrix hn
  have hlower : 2*n ≤ hammingNorm (Function.uncurry M) := by
    exact le_of_eq_of_le (id (Eq.symm hCw)) (hmax C hC)
  have hr : ∀ i, ∃ j, M i j = 0 := by
    intro i
    by_contra! hh
    have hi : ∀ j, M i j = 1 := by
      exact fun j => Fin.eq_one_of_ne_zero (M i j) (hh j)
    have := full_row_bound M hR i hi
    omega
  have hc : ∀ j, ∃ i, M i j = 0 := by
    intro j
    by_contra! hh
    have hi : ∀ i, M.transpose j i = 1 := by
      exact fun i => Fin.eq_one_of_ne_zero (M.transpose j i) (hh i)
    have h := full_row_bound M.transpose (transpose_free M hR) j hi
    rw [transpose_weight] at h
    omega
  obtain ⟨e,he⟩ := zero_transversal M hR hr hc
  let B : Matrix (Fin n) (Fin n) (Fin 2) := fun i j => M i (e j)
  have hBw : hammingNorm (Function.uncurry B) = hammingNorm (Function.uncurry M) := (permute_columns M e).1
  have hBR : ¬ HasRectangle B := (permute_columns M e).2 hR
  refine ⟨hammingNorm (Function.uncurry M), hammingNorm (Function.uncurry M)+1, ?_, ?_, hZ, rfl⟩
  · constructor
    · exact ⟨B,hBR,he,by simpa only [weight_encoding] using hBw⟩
    · rintro w ⟨A,hA,_,hAw⟩
      rw [← weight_encoding] at hAw
      rw [← hAw]
      exact hmax A hA
  · constructor
    · refine ⟨by have h := free_weight_lt hn M hR; omega, ?_⟩
      intro A hA
      rw [← weight_encoding] at hA
      by_contra! hh
      have := hmax A hh
      omega
    · intro k hk
      by_contra! hh
      obtain ⟨A,hA,hAw⟩ := trim_matrix M hR k (by omega)
      exact hA (hk.2 A (by simpa only [weight_encoding] using hAw))


end D5.S3.Combinatorics.Graph.Incidence.AlekseyevA191873ZeroDiagonal
