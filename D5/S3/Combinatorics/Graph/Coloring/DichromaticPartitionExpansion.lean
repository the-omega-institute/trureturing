/- GID: D5/S3/Combinatorics/Graph/Coloring/DichromaticPartitionExpansion
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Coloring/DichromaticPartitionExpansion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Acyclic colourings as finite vertex partitions with injective block names. -/

import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Basic.Real.Basic
import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Order.Partition.Finpartition
import Mathlib.RingTheory.Polynomial.Pochhammer

/-! The falling-factorial expansion of the dichromatic polynomial of a finite digraph. -/

namespace D5.S3.Combinatorics.Graph.Coloring.DichromaticPartitionExpansion

open Classical Finset Polynomial
open scoped BigOperators

noncomputable section

variable {V : Type*}

/-- The induced digraph on `s` has no directed cycle of positive length. The indices
are cyclic, so lengths one and two detect loops and digons respectively. -/
def AcyclicOn (D : Digraph V) (s : Set V) : Prop :=
  ∀ (k : ℕ) (v : Fin (k + 1) → V), Function.Injective v → (∀ i, v i ∈ s) →
    ¬ (∀ i, D.Adj (v i) (v (i + 1)))

/-- Maps of vertices to palette names whose fibres induce acyclic digraphs. -/
def AcyclicColoring (D : Digraph V) (α : Type*) :=
  {f : V → α // ∀ a, AcyclicOn D (f ⁻¹' {a})}

variable [Fintype V] [DecidableEq V]

/-- Unlabelled partitions of all vertices. In the `Finpartition` order, smaller means finer. -/
abbrev VertexPartition (V : Type*) [Fintype V] [DecidableEq V] :=
  Finpartition (univ : Finset V)

/-- Every block of the partition induces an acyclic digraph. -/
def IsAcyclic (D : Digraph V) (P : VertexPartition V) : Prop :=
  ∀ B ∈ P.parts, AcyclicOn D (B : Set V)

/-- A partition's weight in the real falling-factorial extension. -/
def partitionWeight (x : ℝ) (P : VertexPartition V) : ℝ :=
  (descPochhammer ℝ P.parts.card).eval x / x ^ Fintype.card V

/-- Acyclic block partitions with a separate palette label for each block. -/
private abbrev LabelledPartition (D : Digraph V) (α : Type*) :=
  Σ P : {P : VertexPartition V // IsAcyclic D P}, P.val.parts ↪ α

private def blockOf (P : VertexPartition V) (v : V) : P.parts :=
  ⟨P.part v, P.part_mem.mpr (mem_univ v)⟩

private theorem blockOf_surjective (P : VertexPartition V) : Function.Surjective (blockOf P) := by
  intro B
  obtain ⟨v, hv⟩ := P.nonempty_of_mem_parts B.property
  exact ⟨v, Subtype.ext (P.part_eq_of_mem B.property hv)⟩

private def fiberPartition {α : Type*} (f : V → α) : VertexPartition V := by
  classical
  exact Finpartition.ofSetoid (Setoid.ker f)

private theorem mem_fiberPartition {α : Type*} (f : V → α) (v w : V) :
    w ∈ (fiberPartition f).part v ↔ f v = f w := by
  classical
  exact Finpartition.mem_part_ofSetoid_iff_rel (s := Setoid.ker f)

private def decode {D : Digraph V} {α : Type*} (x : LabelledPartition D α) :
    AcyclicColoring D α := by
  refine ⟨fun v ↦ x.2 (blockOf x.1.val v), ?_⟩
  intro a k v hv hcolor
  have he (i : Fin (k + 1)) : blockOf x.1.val (v i) = blockOf x.1.val (v 0) :=
    x.2.injective ((hcolor i : x.2 (blockOf x.1.val (v i)) = a).trans (hcolor 0).symm)
  apply x.1.property _ (blockOf x.1.val (v 0)).property k v hv
  intro i
  rw [← he i]
  exact x.1.val.mem_part_self.mpr (mem_univ _)

private theorem fiberPartition_decode {D : Digraph V} {α : Type*} (x : LabelledPartition D α) :
    fiberPartition (decode x).val = x.1.val := by
  let Q := fiberPartition (decode x).val
  let P := x.1.val
  have hpart (v : V) : Q.part v = P.part v := by
    ext w
    rw [mem_fiberPartition]
    change x.2 (blockOf P v) = x.2 (blockOf P w) ↔ w ∈ P.part v
    rw [x.2.injective.eq_iff]
    exact ⟨fun h ↦ P.mem_part_iff_part_eq_part (mem_univ _) (mem_univ _) |>.mpr
      (congrArg Subtype.val h.symm), fun h ↦ Subtype.ext
      ((P.mem_part_iff_part_eq_part (mem_univ _) (mem_univ _)).mp h).symm⟩
  apply Finpartition.ext
  ext B
  constructor
  · intro hB
    obtain ⟨v, hv⟩ := Q.nonempty_of_mem_parts hB
    rw [← Q.part_eq_of_mem hB hv, hpart]
    exact P.part_mem.mpr (mem_univ _)
  · intro hB
    obtain ⟨v, hv⟩ := P.nonempty_of_mem_parts hB
    rw [← P.part_eq_of_mem hB hv, ← hpart]
    exact Q.part_mem.mpr (mem_univ _)

private theorem decode_bijective (D : Digraph V) (α : Type*) :
    Function.Bijective (decode : LabelledPartition D α → AcyclicColoring D α) := by
  constructor
  · rintro ⟨P, e⟩ ⟨Q, d⟩ h
    have hp : P = Q := Subtype.ext ((fiberPartition_decode ⟨P, e⟩).symm.trans
      ((congrArg (fun c : AcyclicColoring D α ↦ fiberPartition c.val) h).trans
        (fiberPartition_decode ⟨Q, d⟩)))
    subst Q
    have he : e = d := by
      ext B
      obtain ⟨v, rfl⟩ := blockOf_surjective P.val B
      exact congrFun (congrArg Subtype.val h) v
    subst d
    rfl
  · intro f
    let P := fiberPartition f.val
    have hc : IsAcyclic D P := by
      intro B hB
      obtain ⟨v, hv⟩ := P.nonempty_of_mem_parts hB
      intro k vs hi hs
      apply f.property (f.val v) k vs hi
      intro i
      have hh := hs i
      rw [← P.part_eq_of_mem hB hv] at hh
      exact ((mem_fiberPartition f.val v (vs i)).mp hh).symm
    let repr (B : P.parts) := Classical.choose (blockOf_surjective P B)
    have hrepr (B : P.parts) : blockOf P (repr B) = B :=
      Classical.choose_spec (blockOf_surjective P B)
    let e : P.parts ↪ α := ⟨fun B ↦ f.val (repr B), by
      intro B C h
      have hm := (mem_fiberPartition f.val (repr B) (repr C)).mpr h
      have hp : blockOf P (repr C) = blockOf P (repr B) :=
        Subtype.ext (P.part_eq_of_mem (blockOf P (repr B)).property hm)
      simpa only [hrepr] using hp.symm⟩
    refine ⟨⟨⟨P, hc⟩, e⟩, Subtype.ext (funext fun v ↦ ?_)⟩
    have hm : repr (blockOf P v) ∈ P.part v := by
      have hp := congrArg Subtype.val (hrepr (blockOf P v))
      change P.part (repr (blockOf P v)) = P.part v at hp
      rw [← hp]
      exact P.mem_part_self.mpr (mem_univ _)
    exact ((mem_fiberPartition f.val v _).mp hm).symm

/-- The polynomial obtained by assigning distinct names to the acyclic blocks. -/
def dichromaticPolynomial (D : Digraph V) : ℝ[X] := by
  classical
  exact ∑ P : {P : VertexPartition V // IsAcyclic D P}, descPochhammer ℝ P.val.parts.card

/-- At every natural palette size, including zero, the polynomial counts all maps
whose colour classes induce acyclic digraphs. -/
theorem eval_dichromaticPolynomial_nat (D : Digraph V) (q : ℕ) :
    (dichromaticPolynomial D).eval (q : ℝ) = (Nat.card (AcyclicColoring D (Fin q)) : ℝ) := by
  classical
  let e := Equiv.ofBijective _ (decode_bijective D (Fin q))
  rw [Nat.card_congr e.symm, Nat.card_sigma, Nat.cast_sum, dichromaticPolynomial,
    Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro P _
  rw [descPochhammer_eval_eq_descFactorial]
  congr 1
  simp only [Nat.card_eq_fintype_card, Fintype.card_embedding_eq, Fintype.card_fin,
    Fintype.card_coe]

/-- The values at natural palette sizes characterize the real polynomial. -/
theorem eq_dichromaticPolynomial_of_eval_nat (D : Digraph V) (p : ℝ[X])
    (hp : ∀ q : ℕ, p.eval (q : ℝ) = (Nat.card (AcyclicColoring D (Fin q)) : ℝ)) :
    p = dichromaticPolynomial D := by
  apply Polynomial.eq_of_infinite_eval_eq
  refine (Set.infinite_range_of_injective (Nat.cast_injective (R := ℝ))).mono ?_
  rintro _ ⟨q, rfl⟩
  exact (hp q).trans (eval_dichromaticPolynomial_nat D q).symm

/-- The normalized polynomial is the total real weight of the acyclic partitions. -/
theorem dichromaticPolynomial_div_eq_sum_weight (D : Digraph V) (x : ℝ) :
    (dichromaticPolynomial D).eval x / x ^ Fintype.card V =
      ∑ P : VertexPartition V, if IsAcyclic D P then partitionWeight x P else 0 := by
  classical
  simp only [dichromaticPolynomial, Polynomial.eval_finsetSum, div_eq_mul_inv, Finset.sum_mul]
  rw [← Finset.sum_filter]
  exact (Finset.sum_subtype (p := IsAcyclic D) (univ.filter (IsAcyclic D))
    (by simp) (partitionWeight x)).symm

/-- Acyclicity of the blocks is preserved by refinement. -/
theorem isAcyclic_of_le (D : Digraph V) {P Q : VertexPartition V} (h : P ≤ Q)
    (hQ : IsAcyclic D Q) : IsAcyclic D P := by
  intro B hB k v hinj hv
  obtain ⟨C, hC, hBC⟩ := h hB
  exact hQ C hC k v hinj (fun i ↦ hBC (hv i))

/-- Every map is an acyclic colouring if the entire digraph is acyclic. -/
theorem dichromaticPolynomial_eq_pow_of_acyclic (D : Digraph V)
    (hD : AcyclicOn D Set.univ) :
    dichromaticPolynomial D = X ^ Fintype.card V := by
  classical
  let e (q : ℕ) : AcyclicColoring D (Fin q) ≃ (V → Fin q) :=
    { toFun := Subtype.val
      invFun := fun f ↦ ⟨f, fun _ k v hv _ ↦ hD k v hv fun _ ↦ Set.mem_univ _⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  symm
  apply eq_dichromaticPolynomial_of_eval_nat
  intro q
  rw [Nat.card_congr (e q)]
  simp [Nat.card_eq_fintype_card]

/-- A loop prevents every colour map from being acyclic. -/
theorem dichromaticPolynomial_eq_zero_of_loop (D : Digraph V) (v : V) (hv : D.Adj v v) :
    dichromaticPolynomial D = 0 := by
  symm
  apply eq_dichromaticPolynomial_of_eval_nat
  intro q
  have empty : IsEmpty (AcyclicColoring D (Fin q)) := ⟨fun f ↦
    f.property (f.val v) 0 (fun _ ↦ v)
      (fun a b _ ↦ Fin.ext (by have ha := a.isLt; have hb := b.isLt; omega))
      (fun _ ↦ rfl) (fun _ ↦ hv)⟩
  simp

/-- At orders zero and one the dichromatic polynomial is a monomial or zero. -/
theorem dichromaticPolynomial_small (D : Digraph V) (hn : Fintype.card V ≤ 1) :
    dichromaticPolynomial D = X ^ Fintype.card V ∨ dichromaticPolynomial D = 0 := by
  by_cases loops : ∃ v : V, D.Adj v v
  · obtain ⟨v, hv⟩ := loops
    exact Or.inr (dichromaticPolynomial_eq_zero_of_loop D v hv)
  · refine Or.inl (dichromaticPolynomial_eq_pow_of_acyclic D ?_)
    intro k v hinj _ hadj
    have hk := (Fintype.card_le_of_injective v hinj).trans hn
    rw [Fintype.card_fin] at hk
    have hk0 : k = 0 := by omega
    subst k
    exact loops ⟨v 0, by simpa only [show (0 + 1 : Fin 1) = 0 by decide] using hadj 0⟩

/-- The total weight of all partitions is one wherever the normalizing power is nonzero. -/
theorem sum_partitionWeight (x : ℝ) (hx : x ^ Fintype.card V ≠ 0) :
    ∑ P : VertexPartition V, partitionWeight x P = 1 := by
  classical
  let D : Digraph V := ⊥
  have acyclic (s : Set V) : AcyclicOn D s := by
    intro k v _ _ h
    exact h 0
  have h := dichromaticPolynomial_div_eq_sum_weight D x
  rw [dichromaticPolynomial_eq_pow_of_acyclic D (acyclic _), eval_pow, eval_X, div_self hx] at h
  simpa only [IsAcyclic, acyclic, implies_true, ite_true] using h.symm

/-- Each real partition weight is nonnegative in the interval of the conjecture
for digraphs of order at least two. -/
theorem partitionWeight_nonneg (P : VertexPartition V) {x : ℝ}
    (hn : 2 ≤ Fintype.card V) (hx : (Fintype.card V : ℝ) - 1 ≤ x) :
    0 ≤ partitionWeight x P := by
  have hb : (P.parts.card : ℝ) ≤ Fintype.card V := by
    exact_mod_cast (P.card_parts_le_card.trans_eq Finset.card_univ)
  have hn' : (2 : ℝ) ≤ Fintype.card V := by exact_mod_cast hn
  have hn'' : (1 : ℝ) ≤ (Fintype.card V : ℝ) - 1 := by
    exact (le_sub_iff_add_le).2 (by simpa only [one_add_one_eq_two] using hn')
  exact div_nonneg (descPochhammer_nonneg ((sub_le_sub_right hb 1).trans hx))
    (pow_nonneg (zero_le_one.trans (hn''.trans hx)) _)

end
end D5.S3.Combinatorics.Graph.Coloring.DichromaticPartitionExpansion
