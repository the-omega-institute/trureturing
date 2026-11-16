/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/SymmetricSaturatedDecomposition
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/SymmetricSaturatedDecomposition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Girth]
   utility: none
   digest: The exact B/B double-star is closed. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.SymmetricSaturatedCore
import D5.S3.Combinatorics.Graph.HypercubeCritical.SmallRegularCycle
import Batteries.Tactic.OpenPrivate

/-! Actual extraction of the eight-cycle and double-star in the B/B case. -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.SymmetricSaturatedDecomposition

open SimpleGraph
open scoped BigOperators

attribute [local instance] Classical.propDecidable

open private degree_two_neighbor_degree_two symmetric_saturated_core from
  D5.S3.Combinatorics.Graph.HypercubeCritical.SymmetricSaturatedCore
open private small_two_regular_cycle from
  D5.S3.Combinatorics.Graph.HypercubeCritical.SmallRegularCycle

variable {V : Type*} [Fintype V]
variable {H : SimpleGraph V}

private theorem global_degree_two_count
    {L R : Finset V}
    (hpart : H.IsBipartiteWith (L : Set V) (R : Set V))
    (hpositive : ∀ v, 0 < H.degree v)
    (hL2 : (L.filter fun v => H.degree v = 2).card = 4)
    (hR2 : (R.filter fun v => H.degree v = 2).card = 4) :
    ((Finset.univ : Finset V).filter fun v => H.degree v = 2).card = 8 := by
  classical
  have he : (Finset.univ : Finset V).filter (fun v => H.degree v = 2) =
      (L.filter fun v => H.degree v = 2) ∪ (R.filter fun v => H.degree v = 2) := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    constructor
    · intro hv
      obtain ⟨w, hvw⟩ := (H.degree_pos_iff_exists_adj v).mp (hpositive v)
      rcases hpart.mem_of_adj hvw with h | h
      · exact Or.inl ⟨h.1, hv⟩
      · exact Or.inr ⟨h.1, hv⟩
    · rintro (⟨_, hv⟩ | ⟨_, hv⟩) <;> exact hv
  have hd : Disjoint (L.filter fun v => H.degree v = 2)
      (R.filter fun v => H.degree v = 2) := by
    apply Finset.disjoint_left.mpr
    intro v hvL hvR
    exact Set.disjoint_left.mp hpart.disjoint
      (Finset.mem_filter.mp hvL).1 (Finset.mem_filter.mp hvR).1
  rw [he, Finset.card_union_of_disjoint hd, hL2, hR2]

private theorem eight_cycle_of_degree_two
    (hclosed : ∀ {x y}, H.degree x = 2 → H.Adj x y → H.degree y = 2)
    (hg : (8 : ℕ∞) ≤ H.egirth)
    (hcount : ((Finset.univ : Finset V).filter fun v => H.degree v = 2).card = 8) :
    ∃ e : cycleGraph 8 ↪g H, ∀ v, H.degree v = 2 ↔ ∃ i, e i = v := by
  classical
  let T : Set V := {v | H.degree v = 2}
  let K : SimpleGraph T := H.induce T
  have hT : Fintype.card T = 8 := by
    rw [← Set.toFinset_card]
    have he : T.toFinset = (Finset.univ : Finset V).filter (fun v => H.degree v = 2) := by
      ext v
      simp [T]
    rw [he, hcount]
  have hne : Nonempty T := Fintype.card_pos_iff.mp (by omega)
  let : Nonempty T := hne
  have hdegree (x : T) : K.degree x = 2 := by
    have hsub : H.neighborSet x.val ⊆ T := by
      intro y hxy
      exact hclosed x.property hxy
    exact (H.degree_induce_of_neighborSet_subset hsub).trans x.property
  have hKg : (8 : ℕ∞) ≤ K.egirth :=
    hg.trans (SimpleGraph.Embedding.induce T).isContained.egirth_le
  obtain ⟨a, p, _hp, hlen, _hcover, hiso⟩ :=
    small_two_regular_cycle K hdegree hKg (by omega)
  have hl : p.length = 8 := hlen.trans hT
  have hi : Nonempty (cycleGraph 8 ≃g K) := hl ▸ hiso
  obtain ⟨e⟩ := hi
  let f : cycleGraph 8 ↪g H :=
    { toFun := fun i => (e i).val
      inj' := fun i j he => e.injective (Subtype.ext he)
      map_rel_iff' := by intro i j; exact e.map_rel_iff }
  refine ⟨f, ?_⟩
  intro v
  constructor
  · intro hv
    let y : T := ⟨v, hv⟩
    refine ⟨e.symm y, ?_⟩
    change (e (e.symm y)).val = v
    simp [y]
  · rintro ⟨i, rfl⟩
    exact (e i).property

private theorem saturated_decomposition
    {L R : Finset V}
    (hpart : H.IsBipartiteWith (L : Set V) (R : Set V))
    (hdeg : ∀ x, H.degree x = 1 ∨ H.degree x = 2 ∨ H.degree x = 3)
    (hsat : ∀ x, (∑ y ∈ H.neighborFinset x, H.degree y) = H.degree x + 2)
    (hg : (8 : ℕ∞) ≤ H.egirth)
    (hL1 : (L.filter fun x => H.degree x = 1).card = 2)
    (hR1 : (R.filter fun x => H.degree x = 1).card = 2)
    (hL2 : (L.filter fun x => H.degree x = 2).card = 4)
    (hR2 : (R.filter fun x => H.degree x = 2).card = 4)
    (hL3 : (L.filter fun x => H.degree x = 3).card = 1)
    (hR3 : (R.filter fun x => H.degree x = 3).card = 1) :
    ∃ a b, ∃ e : cycleGraph 8 ↪g H,
      a ∈ L ∧ b ∈ R ∧ H.degree a = 3 ∧ H.degree b = 3 ∧ H.Adj a b ∧
      H.neighborFinset a = insert b (R.filter fun y => H.degree y = 1) ∧
      H.neighborFinset b = insert a (L.filter fun x => H.degree x = 1) ∧
      (∀ v, H.degree v = 2 ↔ ∃ i, e i = v) := by
  classical
  have hpositive (x : V) : 0 < H.degree x := by
    rcases hdeg x with h | h | h <;> omega
  have hcount := global_degree_two_count hpart hpositive hL2 hR2
  obtain ⟨e, he⟩ := eight_cycle_of_degree_two
    (degree_two_neighbor_degree_two hdeg hsat) hg hcount
  obtain ⟨a, b, haL, hbR, ha3, hb3, hab, hNa, hNb, _, _⟩ :=
    symmetric_saturated_core hpart hdeg hsat hL3 hR3 hL1 hR1
  exact ⟨a, b, e, haL, hbR, ha3, hb3, hab, hNa, hNb, he⟩

end D5.S3.Combinatorics.Graph.HypercubeCritical.SymmetricSaturatedDecomposition
