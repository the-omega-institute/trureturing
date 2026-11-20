/- GID: D5/S3/Combinatorics/Graph/Walks/GanTanHuangConjecture17Refutation
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/Walks/GanTanHuangConjecture17Refutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected, mathlib/module/Mathlib.Combinatorics.SimpleGraph.Finite]
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Combinatorics/Graph/Walks/GanTanHuangConjecture17Refutation.claim; result=D5/S3/Combinatorics/Graph/Walks/GanTanHuangConjecture17Refutation.result; claim=D5/S3/Combinatorics/Graph/Walks/GanTanHuangConjecture17Refutation.claim
   digest: Six clique vertices with three private leaves each refute the stated long-path threshold. -/

/-
proof_shape: result: content
escape_witness: each of the seven interior vertices of a hypothetical nine-vertex path
  in the constructed graph must be a core vertex, yielding an injection from Fin 7 to Fin 6.
admission_basis: open-problem-resolution (#31996; Refuted)
Direct frozen dependencies: none (pinned Mathlib only).
Live Mathlib interfaces: adjacency gives reachability, neighbor-set cardinality gives
degree, and Fintype.card_le_of_injective bounds the number of interior vertices.
The designated refutation result is exempt from four-slot escape registration (CLAUDE.md §3.9).
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Tactic.NormNum

/-! A finite counterexample to Gan, Tan and Huang's conjectured long-path threshold. -/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Graph.Walks.GanTanHuangConjecture17Refutation

/-- The statement of Conjecture 1.7, with signed floor division and a rational threshold. -/
def claim : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V) (d k : ℕ),
    let n := Fintype.card V
    let q : ℤ := ((k : ℤ) - 3) / 4
    0 < k → k ≤ d → d < n → G.Connected →
    (q : ℚ) * ((n : ℚ) - 1) / d
        + (1 - (q : ℚ) / d) * (((n : ℚ) - 1) * q / ((q : ℚ) + d * ((d : ℚ) - 1)))
        + 2 ≤ (Set.ncard {v | d ≤ (G.neighborSet v).ncard} : ℚ) →
    ∃ path : Fin (k + 1) → V, Function.Injective path ∧
      ∀ i : Fin k, G.Adj (path i.castSucc) (path i.succ)

private abbrev Vertex := Sum (Fin 6) (Fin 6 × Fin 3)

private def graph : SimpleGraph Vertex where
  Adj
    | .inl i, .inl j => i ≠ j
    | .inl i, .inr p => i = p.1
    | .inr p, .inl i => p.1 = i
    | .inr _, .inr _ => False
  symm.symm u v h := by
    cases u <;> cases v
    · exact Ne.symm h
    · exact Eq.symm h
    · exact Eq.symm h
    · exact h
  loopless.irrefl v h := by
    cases v
    · exact h rfl
    · exact h

private instance : DecidableRel graph.Adj := by
  intro u v
  cases u <;> cases v <;> unfold graph <;> infer_instance

/-- The 24-vertex graph with six core vertices and three leaves per core vertex is a counterexample. -/
theorem result : ¬ claim := by
  intro h
  have vertexCount : Fintype.card Vertex = 24 := by decide
  have connected : graph.Connected := by
    have reachCore (i : Fin 6) : graph.Reachable (.inl 0) (.inl i) := by
      by_cases hi : (0 : Fin 6) = i
      · rw [← hi]
      · exact (show graph.Adj (.inl 0) (.inl i) from hi).reachable
    have reach (v : Vertex) : graph.Reachable (.inl 0) v := by
      cases v with
      | inl i => exact reachCore i
      | inr p =>
        exact (reachCore p.1).trans (show graph.Adj (.inl p.1) (.inr p) from rfl).reachable
    let _ : Nonempty Vertex := ⟨.inl 0⟩
    exact ⟨fun u v => (reach u).symm.trans (reach v)⟩
  have coreDegree : ∀ i : Fin 6, graph.degree (.inl i) = 8 := by decide
  have leafDegree : ∀ p : Fin 6 × Fin 3, graph.degree (.inr p) = 1 := by decide
  have highVertices : {v | 8 ≤ (graph.neighborSet v).ncard} =
      Set.range (Sum.inl : Fin 6 → Vertex) := by
    ext v
    change (8 ≤ (graph.neighborSet v).ncard) ↔ v ∈ Set.range Sum.inl
    rw [SimpleGraph.ncard_neighborSet]
    cases v with
    | inl i => exact iff_of_true (by rw [coreDegree]) ⟨i, rfl⟩
    | inr p =>
      refine iff_of_false (by rw [leafDegree]; decide) ?_
      rintro ⟨i, hi⟩
      cases hi
  have highCount : Set.ncard {v | 8 ≤ (graph.neighborSet v).ncard} = 6 := by
    rw [highVertices, Set.ncard_range_of_injective Sum.inl_injective,
      Nat.card_eq_fintype_card, Fintype.card_fin]
  have threshold :
      let q : ℤ := ((8 : ℤ) - 3) / 4
      (q : ℚ) * ((24 : ℚ) - 1) / 8
        + (1 - (q : ℚ) / 8) * (((24 : ℚ) - 1) * q / ((q : ℚ) + 8 * ((8 : ℚ) - 1)))
        + 2 = (298 : ℚ) / 57 := by norm_num
  obtain ⟨path, injective, adjacent⟩ :=
    h Vertex graph 8 8 (by decide) (by decide) (by rw [vertexCount]; decide) connected (by
      rw [vertexCount, highCount]
      exact threshold.le.trans (by norm_num))
  -- A leaf has just one neighbor, so both neighbors of an interior vertex force it into the core.
  have leafNeighbor {p : Fin 6 × Fin 3} {v : Vertex}
      (hv : graph.Adj (.inr p) v) : v = .inl p.1 := by
    cases v with
    | inl i => exact congrArg Sum.inl (Eq.symm hv)
    | inr _ => exact False.elim hv
  have interiorCore (i : Fin 7) : ∃ c : Fin 6, path i.succ.castSucc = .inl c := by
    have left : graph.Adj (path i.succ.castSucc) (path i.castSucc.castSucc) :=
      (adjacent i.castSucc).symm
    have right : graph.Adj (path i.succ.castSucc) (path i.succ.succ) :=
      adjacent i.succ
    cases middle : path i.succ.castSucc with
    | inl c => exact ⟨c, rfl⟩
    | inr p =>
      rw [middle] at left right
      have equalEnds := injective ((leafNeighbor left).trans (leafNeighbor right).symm)
      have equalIndices := congrArg Fin.val equalEnds
      change i.val = i.val + 1 + 1 at equalIndices
      omega
  choose core atCore using interiorCore
  have coreInjective : Function.Injective core := by
    intro i j same
    have verticesEqual : path i.succ.castSucc = path j.succ.castSucc := by
      rw [atCore i, atCore j, same]
    exact Fin.succ_injective _ (Fin.castSucc_injective _ (injective verticesEqual))
  have impossible : 7 ≤ 6 := by
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective core coreInjective
  omega

#print axioms claim
#print axioms result

end D5.S3.Combinatorics.Graph.Walks.GanTanHuangConjecture17Refutation
