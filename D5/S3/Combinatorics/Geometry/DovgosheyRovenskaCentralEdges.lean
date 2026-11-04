/- GID: D5/S3/Combinatorics/Geometry/DovgosheyRovenskaCentralEdges
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Geometry/DovgosheyRovenskaCentralEdges
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Combinatorics/Geometry/DovgosheyRovenskaCentralEdges.claim; result=D5/S3/Combinatorics/Geometry/DovgosheyRovenskaCentralEdges.result; claim=D5/S3/Combinatorics/Geometry/DovgosheyRovenskaCentralEdges.claim
   digest: A four-point ultrametric has more central edges than a three-central metric. -/
/-
result:
  proof_shape: bind-only (finite cases, upstream metric facts, normalization)
  escape_witness: none
  admission_basis: open-problem-resolution (#22906; Refuted)
Direct frozen dependencies: none (Mathlib only).

Private proof declarations, all proof_shape: bind-only; escape_witness: none:
  fx_injective -> xMetric (finite injectivity)
  xUltra -> result (induced p-adic ultrametric)
  xdist -> xcenter, xdiam, xcondition, xedge_set (p-adic norms, finite cases)
  xcenter -> xcondition, xedge_set, xcenter_card (finite witnesses)
  xdiam -> xcondition (diameter bounds)
  xcondition -> result (partition and finite graph equalities)
  xedge_set -> xedge_card (finite unordered-edge enumeration)
  xedge_card -> result (finite cardinality)
  xcenter_card -> result (finite cardinality)
  fy_injective -> yMetric (finite injectivity)
  ydist -> ycenter, yedge_set (induced distance)
  ycenter -> yedge_set, ycenter_card (finite witnesses)
  yedge_set -> yedge_card (finite unordered-edge enumeration)
  yedge_card -> result (finite cardinality)
  ycenter_card -> result (finite cardinality)
The arrows name consumers, not additional mathematical assertions.
Definitions use the metric, graph, diameter, bipartite, star, map and cardinality
owners from Mathlib. No D5 owner for distance centers or these two metric graphs
was found on origin/dev. The literal source predicates are retained.
The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).
-/

import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.Combinatorics.SimpleGraph.Star

namespace D5.S3.Combinatorics.Geometry.DovgosheyRovenskaCentralEdges

noncomputable section

def center (X : Type) [MetricSpace X] : Set ℝ :=
  {t | 0 ≤ t ∧ ∀ p : X, ∃ y : X, dist y p = t}


def centralGraph (X : Type) [MetricSpace X] : SimpleGraph X :=
  SimpleGraph.fromRel fun u v => dist u v ∈ center X

noncomputable def diametricalGraph (X : Type) [MetricSpace X] : SimpleGraph X :=
  SimpleGraph.fromRel fun u v => dist u v = Metric.diam (Set.univ : Set X)

def conditionI (X : Type) [MetricSpace X] : Prop :=
  ∃ (A B : Set X) (a : A) (b : B),
    Disjoint A B ∧ A ∪ B = Set.univ ∧ min (Nat.card A) (Nat.card B) = 2 ∧
    diametricalGraph X =
      (completeBipartiteGraph A B).map
        (Sum.elim (fun x : A => (x : X)) (fun x : B => (x : X))) ∧
    centralGraph X = diametricalGraph X ⊔
      (SimpleGraph.starGraph a).map (fun x : A => (x : X)) ⊔
      (SimpleGraph.starGraph b).map (fun x : B => (x : X))

def claim : Prop :=
  ∀ (X : Type) [Fintype X] [MetricSpace X],
    IsUltrametricDist X → 4 ≤ Fintype.card X → Nat.card (center X) = 3 →
    (conditionI X ↔
      ∀ (Y : Type) [Fintype Y] [MetricSpace Y],
        Nat.card (center Y) = 3 → Fintype.card Y = Fintype.card X →
        Nat.card (centralGraph X).edgeSet ≤ Nat.card (centralGraph Y).edgeSet)

private def fx : Fin 4 → ℚ_[2] := ![0, 1, 2, 3]

private theorem fx_injective : Function.Injective fx := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [fx]

private instance xMetric : MetricSpace (Fin 4) := MetricSpace.induced fx fx_injective inferInstance
private instance xUltra : IsUltrametricDist (Fin 4) :=
  ⟨fun x y z => IsUltrametricDist.dist_triangle_max (fx x) (fx y) (fx z)⟩

private theorem xdist (i j : Fin 4) : dist i j =
    if i = j then 0 else if i.1 % 2 = j.1 % 2 then (1/2 : ℝ) else 1 := by
  have hn2 : ‖(2 : ℚ_[2])‖ = (1/2 : ℝ) := by
    simpa using (Padic.norm_p (p := 2))
  have hn3 : ‖(3 : ℚ_[2])‖ = (1 : ℝ) := by
    exact ((Padic.norm_natCast_eq_one_iff (p := 2) (n := 3)).2 (by decide))
  change dist (fx i) (fx j) = _
  fin_cases i <;> fin_cases j <;>
    simp [fx, dist_eq_norm, norm_neg, hn2, hn3] <;>
    norm_num <;>
    try simpa using hn2

private theorem xcenter : center (Fin 4) = ({0, (1/2 : ℝ), 1} : Set ℝ) := by
  ext t
  constructor
  · intro ht
    rcases ht with ⟨ht0, htall⟩
    rcases htall (0 : Fin 4) with ⟨y, hy⟩
    fin_cases y
    · simp at hy
      exact Or.inl hy.symm
    · simp [xdist] at hy
      exact Or.inr (Or.inr hy.symm)
    · simp [xdist] at hy
      norm_num at hy
      exact Or.inr (Or.inl hy.symm)
    · simp [xdist] at hy
      exact Or.inr (Or.inr hy.symm)
  · intro ht
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
    rcases ht with rfl | rfl | rfl
    · constructor
      · norm_num
      · intro p
        fin_cases p
        · exact ⟨0, by simp⟩
        · exact ⟨1, by simp⟩
        · exact ⟨2, by simp⟩
        · exact ⟨3, by simp⟩
    · constructor
      · norm_num
      · intro p
        fin_cases p
        · exact ⟨2, by simp [xdist]⟩
        · exact ⟨3, by simp [xdist]⟩
        · exact ⟨0, by simp [xdist]⟩
        · exact ⟨1, by simp [xdist]⟩
    · constructor
      · norm_num
      · intro p
        fin_cases p
        · exact ⟨1, by simp [xdist]⟩
        · exact ⟨0, by simp [xdist]⟩
        · exact ⟨1, by simp [xdist]⟩
        · exact ⟨0, by simp [xdist]⟩


private theorem xdiam : Metric.diam (Set.univ : Set (Fin 4)) = 1 := by
  apply le_antisymm
  · apply Metric.diam_le_of_forall_dist_le (by norm_num)
    intro x _ y _
    rw [xdist]
    split <;> (try split) <;> norm_num
  · have hb : Bornology.IsBounded (Set.univ : Set (Fin 4)) :=
      (Set.toFinite _).isBounded
    have h := Metric.dist_le_diam_of_mem hb (show (0 : Fin 4) ∈ (Set.univ : Set (Fin 4)) by simp)
      (show (1 : Fin 4) ∈ (Set.univ : Set (Fin 4)) by simp)
    simpa [xdist] using h

private theorem xcondition : conditionI (Fin 4) := by
  let A : Set (Fin 4) := {0, 2}
  let B : Set (Fin 4) := {1, 3}
  let a : A := ⟨0, by simp [A]⟩
  let b : B := ⟨1, by simp [B]⟩
  refine ⟨A, B, a, b, ?_, ?_, ?_, ?_, ?_⟩
  · simp [A, B, Set.disjoint_left]
  · ext x
    fin_cases x <;> simp [A, B]
  · norm_num [A, B, Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card]
  · ext u v
    fin_cases u <;> fin_cases v <;>
      simp [diametricalGraph, xdiam, xdist, A, B, SimpleGraph.fromRel_adj,
        SimpleGraph.map_adj', completeBipartiteGraph_adj]
  · ext u v
    fin_cases u <;> fin_cases v <;>
      simp [centralGraph, xcenter, xdist, diametricalGraph, xdiam, A, B, a, b,
        SimpleGraph.fromRel_adj, SimpleGraph.map_adj', SimpleGraph.starGraph_adj]


private theorem xedge_set : (centralGraph (Fin 4)).edgeSet =
    {s((0 : Fin 4), 1), s(0, 2), s(0, 3), s(1, 2), s(1, 3), s(2, 3)} := by
  ext e
  induction e using Sym2.ind with | h u v =>
    fin_cases u <;> fin_cases v <;>
      simp [centralGraph, xcenter, xdist, SimpleGraph.fromRel_adj, Sym2.eq_swap]

private theorem xedge_card : Nat.card (centralGraph (Fin 4)).edgeSet = 6 := by
  rw [xedge_set, Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card]
  norm_num


private theorem xcenter_card : Nat.card (center (Fin 4)) = 3 := by
  rw [xcenter, Nat.card_coe_set_eq]
  norm_num

private def fy : Fin 4 → ℝ := ![0, 4, 5, 9]

private theorem fy_injective : Function.Injective fy := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp [fy] at h ⊢

private instance yMetric : MetricSpace (Fin 4) := MetricSpace.induced fy fy_injective inferInstance

private theorem ydist (i j : Fin 4) : dist i j = dist (fy i) (fy j) := by
  exact Eq.symm (Isometry.dist_eq (fun x1 => congrFun rfl) i j)

private theorem ycenter : center (Fin 4) = ({0, 4, 5} : Set ℝ) := by
  ext t
  constructor
  · intro ht
    rcases ht with ⟨ht0, htall⟩
    have hc : t = 0 ∨ t = 4 ∨ t = 5 ∨ t = 9 := by
      rcases htall (0 : Fin 4) with ⟨y, hy⟩
      fin_cases y
      · rw [ydist] at hy
        norm_num [fy, Real.dist_eq] at hy
        exact Or.inl hy.symm
      · rw [ydist] at hy
        norm_num [fy, Real.dist_eq] at hy
        exact Or.inr (Or.inl hy.symm)
      · rw [ydist] at hy
        norm_num [fy, Real.dist_eq] at hy
        exact Or.inr (Or.inr (Or.inl hy.symm))
      · rw [ydist] at hy
        norm_num [fy, Real.dist_eq] at hy
        exact Or.inr (Or.inr (Or.inr hy.symm))
    rcases hc with rfl | rfl | rfl | rfl
    · simp
    · simp
    · simp
    · rcases htall (1 : Fin 4) with ⟨y, hy⟩
      fin_cases y <;> rw [ydist] at hy <;> norm_num [fy, Real.dist_eq] at hy
  · intro ht
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
    rcases ht with rfl | rfl | rfl
    · constructor
      · norm_num
      · intro p
        fin_cases p
        · exact ⟨0, by rw [ydist]; norm_num [fy, Real.dist_eq]⟩
        · exact ⟨1, by rw [ydist]; norm_num [fy, Real.dist_eq]⟩
        · exact ⟨2, by rw [ydist]; norm_num [fy, Real.dist_eq]⟩
        · exact ⟨3, by rw [ydist]; norm_num [fy, Real.dist_eq]⟩
    · constructor
      · norm_num
      · intro p
        fin_cases p
        · exact ⟨1, by rw [ydist]; norm_num [fy, Real.dist_eq]⟩
        · exact ⟨0, by rw [ydist]; norm_num [fy, Real.dist_eq]⟩
        · exact ⟨3, by rw [ydist]; norm_num [fy, Real.dist_eq]⟩
        · exact ⟨2, by rw [ydist]; norm_num [fy, Real.dist_eq]⟩
    · constructor
      · norm_num
      · intro p
        fin_cases p
        · exact ⟨2, by rw [ydist]; norm_num [fy, Real.dist_eq]⟩
        · exact ⟨3, by rw [ydist]; norm_num [fy, Real.dist_eq]⟩
        · exact ⟨0, by rw [ydist]; norm_num [fy, Real.dist_eq]⟩
        · exact ⟨1, by rw [ydist]; norm_num [fy, Real.dist_eq]⟩

private theorem yedge_set : (centralGraph (Fin 4)).edgeSet =
    {s((0 : Fin 4), 1), s(0, 2), s(1, 3), s(2, 3)} := by
  ext e
  induction e using Sym2.ind with | h u v =>
    fin_cases u <;> fin_cases v <;>
      simp [centralGraph, ycenter, ydist, fy,
        Real.dist_eq, abs_of_nonpos, Sym2.eq_swap] <;>
      norm_num

private theorem yedge_card : Nat.card (centralGraph (Fin 4)).edgeSet = 4 := by
  rw [yedge_set, Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card]
  norm_num


private theorem ycenter_card : Nat.card (center (Fin 4)) = 3 := by
  rw [ycenter, Nat.card_coe_set_eq]
  norm_num

theorem result : ¬ claim := by
  intro h
  have hh := @h (Fin 4) inferInstance xMetric xUltra (by norm_num) xcenter_card
  have hf := hh.mp xcondition
  have hi := @hf (Fin 4) inferInstance yMetric ycenter_card (by norm_num)
  rw [xedge_card, yedge_card] at hi
  norm_num at hi

end
end D5.S3.Combinatorics.Geometry.DovgosheyRovenskaCentralEdges
