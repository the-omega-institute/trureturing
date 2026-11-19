import Mathlib.Data.Nat.Bitwise

/-! Connected triangle-free cubic graphs on twelve vertices can be searched
by labeling the vertices in order of discovery. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyFourGraphSearch

private abbrev Graph := Array Nat

private def adjacent (g : Graph) (v w : Nat) : Bool :=
  g[v]!.testBit w

private def degree (g : Graph) (v : Nat) : Nat :=
  (List.range 12).countP (adjacent g v)

private def join (g : Graph) (v w : Nat) : Graph :=
  (g.set! v (g[v]! ||| (1 <<< w))).set! w (g[w]! ||| (1 <<< v))

private def canJoin (g : Graph) (v w : Nat) : Bool :=
  degree g w < 3 && !(adjacent g v w) && (g[v]! &&& g[w]!) == 0

private def extensions (vertex discovered : Nat) :
    List Nat → Graph → Nat → List (Graph × Nat)
  | [], graph, left =>
    if discovered + left ≤ 12 then
      let fresh := List.range' discovered left
      [(fresh.foldl (fun g w => join g vertex w) graph, discovered + left)]
    else []
  | next :: rest, graph, left =>
    let skip := extensions vertex discovered rest graph left
    if left > 0 && canJoin graph vertex next then
      skip ++ extensions vertex discovered rest (join graph vertex next) (left - 1)
    else skip

private def search : Nat → Nat → Nat → Graph → List Graph
  | 0, _, _, graph => [graph]
  | fuel + 1, vertex, discovered, graph =>
    if vertex < discovered then
      let candidates := List.range' (vertex + 1) (discovered - (vertex + 1))
      (extensions vertex discovered candidates graph (3 - degree graph vertex)).flatMap
        fun (extended, newCount) => search fuel (vertex + 1) newCount extended
    else []

private def candidates : List Graph :=
  search 12 0 1 (Array.replicate 12 0)

/-- Specify which already discovered vertices are joined to the current
vertex. The remaining edges introduce fresh vertices in discovery order. -/
private def extendWith (vertex discovered : Nat) (graph : Graph) (left : Nat)
    (chosen : List Nat) : Graph × Nat :=
  let joined := chosen.foldl (fun g w => join g vertex w) graph
  let fresh := List.range' discovered (left - chosen.length)
  (fresh.foldl (fun g w => join g vertex w) joined, discovered + fresh.length)

private def Choices (vertex : Nat) : List Nat → Graph → Nat → List Nat → Prop
  | [], _, _, chosen => chosen = []
  | next :: rest, graph, left, chosen =>
    Choices vertex rest graph left chosen ∨
      (0 < left ∧ canJoin graph vertex next = true ∧
        ∃ tail, chosen = next :: tail ∧
          Choices vertex rest (join graph vertex next) (left - 1) tail)

private theorem extendWith_mem (vertex discovered : Nat) (available : List Nat)
    (graph : Graph) (left : Nat) (chosen : List Nat)
    (hchoices : Choices vertex available graph left chosen)
    (hbound : discovered + (left - chosen.length) ≤ 12) :
    extendWith vertex discovered graph left chosen ∈
      extensions vertex discovered available graph left := by
  induction available generalizing graph left chosen with
  | nil =>
    have hnil : chosen = [] := hchoices
    subst chosen
    simpa [extendWith, extensions, hbound] using hbound
  | cons next rest ih =>
    rcases hchoices with hskip | ⟨hleft, hj, tail, rfl, htail⟩
    · have hm := ih graph left chosen hskip hbound
      by_cases h : left > 0 ∧ canJoin graph vertex next = true
      · simpa [extensions, h] using Or.inl (b := extendWith vertex discovered graph left chosen ∈
          extensions vertex discovered rest (join graph vertex next) (left - 1)) hm
      · simpa [extensions, h] using hm
    · have he : left - (next :: tail).length = (left - 1) - tail.length := by
        simp [Nat.sub_sub, Nat.add_comm]
      have hbound' : discovered + (left - 1 - tail.length) ≤ 12 := by
        simpa only [← he] using hbound
      have hm := ih (join graph vertex next) (left - 1) tail htail hbound'
      simp only [extensions, hleft, hj, ite_true, Bool.and_true, decide_true, List.mem_append]
      refine Or.inr ?_
      have hs : left - (tail.length + 1) = left - 1 - tail.length := by omega
      simpa [extendWith, hs] using hm

/-- Follow the choices given by a labeled graph for the remaining vertices. -/
private def FollowsDiscovery : Nat → Nat → Nat → Graph → Graph → Prop
  | 0, _, _, graph, target => target = graph
  | fuel + 1, vertex, discovered, graph, target =>
    vertex < discovered ∧
      ∃ chosen,
        let available := List.range' (vertex + 1) (discovered - (vertex + 1))
        let left := 3 - degree graph vertex
        let updated := extendWith vertex discovered graph left chosen
        Choices vertex available graph left chosen ∧
          discovered + (left - chosen.length) ≤ 12 ∧
          FollowsDiscovery fuel (vertex + 1) updated.2 updated.1 target

private theorem mem_search {fuel vertex discovered : Nat} {graph target : Graph}
    (h : FollowsDiscovery fuel vertex discovered graph target) :
    target ∈ search fuel vertex discovered graph := by
  induction fuel generalizing vertex discovered graph with
  | zero =>
    have htarget : target = graph := h
    simp [search, htarget]
  | succ fuel ih =>
    obtain ⟨hvertex, chosen, hchoices, hbound, hnext⟩ := h
    rw [search, if_pos hvertex]
    exact List.mem_flatMap.mpr ⟨_, extendWith_mem _ _ _ _ _ chosen hchoices hbound, ih hnext⟩

#print axioms mem_search


end D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyFourGraphSearch
