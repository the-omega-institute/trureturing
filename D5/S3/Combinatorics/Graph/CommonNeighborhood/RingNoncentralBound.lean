/- GID: D5/S3/Combinatorics/Graph/CommonNeighborhood/RingNoncentralBound
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/CommonNeighborhood/RingNoncentralBound
   mirror-E: none(waiver:structural-proof)
   anchors: [lake/module/D5.S3.Combinatorics.Graph.CommonNeighborhood.NeighbourhoodCliqueBound]
   utility: none
   digest: The noncentral commuting graph of every finite noncommutative associative ring has n >= z + 2 >= 3 and common-neighbourhood energy at most n(n - z - 2) < 2(n - 1)(n - 2). -/

/- Escape audit unfinished for result: https://github.com/the-omega-institute/trureturing/issues/32738 -/
import D5.S3.Combinatorics.Graph.CommonNeighborhood.NeighbourhoodCliqueBound

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-! Strict common-neighbourhood energy bound for the commuting graph of a finite ring. -/

noncomputable section

namespace D5.S3.Combinatorics.Graph.CommonNeighborhood.RingNoncentralBound

attribute [local instance] Classical.propDecidable

/-
proof_shape:
  ringCenter, Vertex, commutingGraph, centralizer: definitions
  mem_centralizer: bind-only (consumers: degree_and_center_le_centralizer)
  degree_and_center_le_centralizer, twice_degree_bound: content (consumer: result)
  result: content
direct frozen dependencies:
  D5/S3/Combinatorics/Graph/CommonNeighborhood/NeighbourhoodCliqueBound.result
    (statement_id sha256:6fcb98eb465071d206530ed3b2e307ffef56bce840c1e7703998475368c42ded)
escape_witness: the ring centralizer of a noncentral element is a proper additive subgroup
  (closed under addition and negation because multiplication distributes), so by Lagrange's
  index bound it has at most half the elements while containing the center, the element and all
  its graph neighbours; this gives 2 deg(x) <= n - z - 2, which the neighbourhood-clique bound
  converts into E_CN <= n max(n - z - 4, 0).
admission_basis: escape-witness
-/

open Finset
open D5.S3.Combinatorics.Graph.SubgroupGenerating.CyclicExtensionRefutation

/-- The center of a ring: the elements commuting with every element. -/
def ringCenter (R : Type) [Mul R] : Set R := {x | ∀ y, x * y = y * x}

/-- The vertices are the individual noncentral elements. -/
abbrev Vertex (R : Type) [Mul R] := {x : R // x ∉ ringCenter R}

/-- Distinct noncentral elements are adjacent precisely when they commute. -/
def commutingGraph (R : Type) [Mul R] : SimpleGraph (Vertex R) where
  Adj x y := x ≠ y ∧ x.val * y.val = y.val * x.val
  symm := ⟨by intro x y h; exact ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨by intro x h; exact h.1 rfl⟩

section Centralizer

variable {R : Type} [NonUnitalRing R]

/-- The additive subgroup of elements commuting with `x`. -/
private def centralizer (x : R) : AddSubgroup R where
  carrier := {y | x * y = y * x}
  zero_mem' := show x * 0 = 0 * x by rw [mul_zero, zero_mul]
  add_mem' := by
    intro a b (ha : x * a = a * x) (hb : x * b = b * x)
    show x * (a + b) = (a + b) * x
    rw [mul_add, add_mul, ha, hb]
  neg_mem' := by
    intro a (ha : x * a = a * x)
    show x * -a = -a * x
    rw [mul_neg, neg_mul, ha]

private theorem mem_centralizer {x y : R} : y ∈ centralizer x ↔ x * y = y * x := Iff.rfl

variable [Fintype R]

/-- The center, `x` and its graph neighbours are disjoint inside the centralizer of `x`. -/
private theorem degree_and_center_le_centralizer (x : Vertex R) :
    (commutingGraph R).degree x + Fintype.card (ringCenter R) + 1 ≤
      Fintype.card (centralizer x.val) := by
  let Z : Finset R := univ.filter (fun y => y ∈ ringCenter R)
  let K : Finset R := univ.filter (fun y => y ∈ centralizer x.val)
  let N : Finset R := univ.filter
    (fun y => y ∉ ringCenter R ∧ y ≠ x.val ∧ x.val * y = y * x.val)
  let e : (commutingGraph R).neighborSet x ≃
      {y : R // y ∉ ringCenter R ∧ y ≠ x.val ∧ x.val * y = y * x.val} :=
    { toFun := fun y => ⟨y.val.val, y.val.property,
        fun h => y.property.1 (Subtype.ext h.symm), y.property.2⟩
      invFun := fun y => ⟨⟨y.val, y.property.1⟩,
        ⟨fun h => y.property.2.1 (congrArg Subtype.val h.symm), y.property.2.2⟩⟩
      left_inv := by intro y; rfl
      right_inv := by intro y; rfl }
  have hN : (commutingGraph R).degree x = N.card := by
    rw [← SimpleGraph.card_neighborSet_eq_degree]
    exact (Fintype.card_congr e).trans (Fintype.card_subtype _)
  have hZ : Z.card = Fintype.card (ringCenter R) := (Fintype.card_subtype _).symm
  have hK : K.card = Fintype.card (centralizer x.val) := (Fintype.card_subtype _).symm
  have hx : x.val ∉ N := by simp [N]
  have hdis : Disjoint Z (insert x.val N) := by
    apply Finset.disjoint_left.mpr
    intro y hy hz
    have hyZ : y ∈ ringCenter R := (mem_filter.mp hy).2
    rcases mem_insert.mp hz with h | h
    · subst y; exact x.property hyZ
    · exact (mem_filter.mp h).2.1 hyZ
  have hsub : Z ∪ insert x.val N ⊆ K := by
    intro y hy
    apply mem_filter.mpr
    refine ⟨mem_univ _, ?_⟩
    rw [mem_centralizer]
    rcases mem_union.mp hy with h | h
    · exact ((mem_filter.mp h).2 x.val).symm
    · rcases mem_insert.mp h with h | h
      · subst y; rfl
      · exact (mem_filter.mp h).2.2.2
  have hc := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdis, Finset.card_insert_of_notMem hx,
    hZ, hK, ← hN] at hc
  omega

/-- Each noncentral centralizer is a proper additive subgroup, so it has at most half the
elements; hence `2 deg(x) ≤ n - z - 2`. -/
private theorem twice_degree_bound (x : Vertex R) :
    2 * ((commutingGraph R).degree x : ℤ) + 2 * Fintype.card (ringCenter R) + 2 ≤
      Fintype.card R := by
  let K := centralizer x.val
  have hproper : K ≠ ⊤ := by
    intro h
    apply x.property
    intro y
    have hy : y ∈ K := h ▸ AddSubgroup.mem_top y
    exact hy
  have hindex : 2 ≤ K.index := K.one_lt_index_of_ne_top hproper
  have hcard : 2 * Fintype.card K ≤ Fintype.card R := by
    calc
      2 * Fintype.card K = Fintype.card K * 2 := Nat.mul_comm _ _
      _ ≤ Fintype.card K * K.index := Nat.mul_le_mul_left _ hindex
      _ = Fintype.card R := by simpa only [Nat.card_eq_fintype_card] using K.card_mul_index
  have hd := degree_and_center_le_centralizer x
  have : 2 * (commutingGraph R).degree x + 2 * Fintype.card (ringCenter R) + 2 ≤
      Fintype.card R := by
    dsimp [K] at hcard
    omega
  exact_mod_cast this

end Centralizer

/-- For every finite associative ring `R` (not necessarily unital) with two non-commuting
elements, write `z` for the order of its center and `n` for the number of noncentral elements.
Then `z ≥ 1`, `n ≥ z + 2 ≥ 3`, and the common-neighbourhood energy of the commuting graph on
the noncentral elements is at most `n·max(n - z - 4, 0) ≤ n(n - z - 2)`, which is strictly below
the complete-graph value `2(n - 1)(n - 2)`. -/
theorem result (R : Type) [NonUnitalRing R] [Fintype R]
    (noncommutative : ∃ a b : R, a * b ≠ b * a) :
    1 ≤ Fintype.card (ringCenter R) ∧
      Fintype.card (ringCenter R) + 2 ≤ Fintype.card (Vertex R) ∧
      3 ≤ Fintype.card (Vertex R) ∧
      graphEnergy (commutingGraph R) .commonNeighbour ≤
        (Fintype.card (Vertex R) : ℝ) *
          max ((Fintype.card (Vertex R) : ℝ) - Fintype.card (ringCenter R) - 4) 0 ∧
      (Fintype.card (Vertex R) : ℝ) *
          max ((Fintype.card (Vertex R) : ℝ) - Fintype.card (ringCenter R) - 4) 0 ≤
        (Fintype.card (Vertex R) : ℝ) *
          ((Fintype.card (Vertex R) : ℝ) - Fintype.card (ringCenter R) - 2) ∧
      (Fintype.card (Vertex R) : ℝ) *
          ((Fintype.card (Vertex R) : ℝ) - Fintype.card (ringCenter R) - 2) <
        2 * ((Fintype.card (Vertex R) : ℝ) - 1) * ((Fintype.card (Vertex R) : ℝ) - 2) := by
  obtain ⟨a, b, hab⟩ := noncommutative
  have ha : a ∉ ringCenter R := fun h => hab (h b)
  have hz : 1 ≤ Fintype.card (ringCenter R) := by
    have : (0 : R) ∈ ringCenter R := fun y => by simp
    exact Fintype.card_pos_iff.mpr ⟨⟨0, this⟩⟩
  have hn : Fintype.card (Vertex R) + Fintype.card (ringCenter R) = Fintype.card R := by
    have h1 := Fintype.card_subtype_compl (fun x : R => x ∈ ringCenter R)
    have h2 : Fintype.card (ringCenter R) ≤ Fintype.card R :=
      Fintype.card_le_of_injective Subtype.val Subtype.val_injective
    have h3 : Fintype.card {x : R // x ∈ ringCenter R} = Fintype.card (ringCenter R) := rfl
    simp only [Vertex] at h1 ⊢
    omega
  have hdeg := twice_degree_bound (⟨a, ha⟩ : Vertex R)
  have hd0 : (0 : ℤ) ≤ (commutingGraph R).degree ⟨a, ha⟩ := Nat.cast_nonneg _
  have hni : (Fintype.card (Vertex R) : ℤ) + Fintype.card (ringCenter R) = Fintype.card R := by
    exact_mod_cast hn
  have hgap : Fintype.card (ringCenter R) + 2 ≤ Fintype.card (Vertex R) := by
    have : (Fintype.card (ringCenter R) : ℤ) + 2 ≤ Fintype.card (Vertex R) := by linarith
    exact_mod_cast this
  refine ⟨hz, hgap, by omega, ?_, ?_, ?_⟩
  · obtain ⟨hE, -⟩ := NeighbourhoodCliqueBound.result (commutingGraph R)
    refine hE.trans ?_
    calc 2 * ∑ v, max (((commutingGraph R).degree v : ℝ) - 1) 0
        ≤ ∑ _v : Vertex R,
          max ((Fintype.card (Vertex R) : ℝ) - Fintype.card (ringCenter R) - 4) 0 := by
          rw [Finset.mul_sum]
          apply Finset.sum_le_sum
          intro v _
          have hv := twice_degree_bound v
          have hvr : 2 * ((commutingGraph R).degree v : ℝ) + 2 * Fintype.card (ringCenter R) + 2 ≤
              Fintype.card R := by exact_mod_cast hv
          have hnr : (Fintype.card (Vertex R) : ℝ) + Fintype.card (ringCenter R) =
              Fintype.card R := by exact_mod_cast hn
          have hd : (0 : ℝ) ≤ (commutingGraph R).degree v := Nat.cast_nonneg _
          rcases le_total (((commutingGraph R).degree v : ℝ) - 1) 0 with h | h
          · rw [max_eq_right h]; linarith [le_max_right
              ((Fintype.card (Vertex R) : ℝ) - Fintype.card (ringCenter R) - 4) 0]
          · rw [max_eq_left h]; linarith [le_max_left
              ((Fintype.card (Vertex R) : ℝ) - Fintype.card (ringCenter R) - 4) 0]
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  · apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    have hg : ((Fintype.card (ringCenter R) : ℝ) + 2) ≤ Fintype.card (Vertex R) := by
      exact_mod_cast hgap
    exact max_le (by linarith) (by linarith)
  · have h3 : (3 : ℝ) ≤ Fintype.card (Vertex R) := by exact_mod_cast (by omega : 3 ≤ _)
    have hz1 : (1 : ℝ) ≤ Fintype.card (ringCenter R) := by exact_mod_cast hz
    nlinarith

#print axioms result

end D5.S3.Combinatorics.Graph.CommonNeighborhood.RingNoncentralBound
