/- GID: D5/S3/Geometry/OriginalLabelTwoSum/ProtectedG1
   generality: G
   mirror-B: D5/B/S3/Geometry/OriginalLabelTwoSum/ProtectedG1
   mirror-E: none(waiver:actual-g1-prescribed-protection)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Acyclic]
   utility: none
   digest: Actual marked G1 graph rows consume forward native protection and its standalone core replay. -/
import D5.S3.Geometry.FinitePrescribedPairProtection
import D5.S3.Geometry.OriginalLabelTwoSum.GraphDataCore
import D5.S3.Geometry.OriginalLabelTwoSum.CutWalk
import D5.S3.Geometry.OriginalLabelTwoSum.Cone

/-! SOURCE ONLY, UNCOMPILED. The literal original labels h,a,c,e,1,2,3
are retained, including the left ghost h and the removed interface label e in
the ambient type. The finite graph and marked tree are constructed here; rows
are computed using GraphData.path_eq. No root equation or final certificate is
an input. Planarity is ordinary geometry (two triangles on opposite sides of h,
and a wheel in the outer bridge collar); no formal plane-embedding theorem is
claimed. The explicit straight-line drawing is checked separately in Python.
The native proof concerns precisely this actual graph, not all plane graphs. -/
noncomputable section
open Finset SimpleGraph
namespace D5.S3.Geometry.OriginalLabelTwoSum.ProtectedG1
open FiniteElementaryCollapse FiniteRelativeSimplicialCollapse

abbrev Label := Fin 7
abbrev h : Label := 0
abbrev a : Label := 1
abbrev c : Label := 2
abbrev e : Label := 3
abbrev one : Label := 4
abbrev two : Label := 5
abbrev three : Label := 6

private def edgeGraph {V : Type*} [DecidableEq V] (F : Finset (Sym2 V))
    (hn : ∀ v, s(v,v) ∉ F) : SimpleGraph V where
  Adj x y := s(x,y) ∈ F
  symm := by intro x y hx; simpa only [Sym2.eq_swap] using hx
  loopless := hn

private def leftEnds (i : Fin 4) : Fin 5 × Fin 5 :=
  ![(0,1),(1,2),(1,3),(0,4)] i
private def leftChordEnds (i : Fin 2) : Fin 5 × Fin 5 :=
  ![(0,2),(0,3)] i
private def leftTree : SimpleGraph (Fin 5) :=
  edgeGraph {s(0,1),s(1,2),s(1,3),s(0,4)} (by decide)
private def leftGraph : SimpleGraph (Fin 5) :=
  edgeGraph {s(0,1),s(1,2),s(1,3),s(0,4),s(0,2),s(0,3)} (by decide)
private def leftSide (i : Fin 4) : Finset (Fin 5) :=
  ![{1,2,3},{2},{3},{4}] i
private theorem leftBridge (i : Fin 4) :
    leftTree.IsBridge s((leftEnds i).1,(leftEnds i).2) := by
  apply CutWalk.bridge_of_predicate (fun v => v ∉ leftSide i)
  · exact (by decide : ∀ i : Fin 4, (leftEnds i).1 ∉ leftSide i) i
  · exact (by decide : ∀ i : Fin 4, ¬ (leftEnds i).2 ∉ leftSide i) i
  · exact (by decide : ∀ (i : Fin 4) (x y : Fin 5), leftTree.Adj x y →
      s(x,y) ≠ s((leftEnds i).1,(leftEnds i).2) →
      (x ∉ leftSide i ↔ y ∉ leftSide i)) i
private theorem leftTree_isTree : leftTree.IsTree where
  connected := by
    apply SimpleGraph.connected_iff_exists_forall_reachable.mpr
    refine ⟨(0 : Fin 5),?_⟩
    intro v
    fin_cases v
    · exact (show leftTree.Walk 0 0 from .nil).reachable
    · exact (show leftTree.Walk 0 1 from (.cons (show leftTree.Adj 0 1 from by decide) .nil)).reachable
    · exact (show leftTree.Walk 0 2 from (.cons (show leftTree.Adj 0 1 from by decide) (.cons (show leftTree.Adj 1 2 from by decide) .nil))).reachable
    · exact (show leftTree.Walk 0 3 from (.cons (show leftTree.Adj 0 1 from by decide) (.cons (show leftTree.Adj 1 3 from by decide) .nil))).reachable
    · exact (show leftTree.Walk 0 4 from (.cons (show leftTree.Adj 0 4 from by decide) .nil)).reachable
  isAcyclic := SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mpr (by
    intro x y hxy
    have cover : ∀ x y : Fin 5, leftTree.Adj x y →
        ∃ i : Fin 4, s(x,y) = s((leftEnds i).1,(leftEnds i).2) := by decide
    obtain ⟨i,hi⟩ := cover x y hxy
    rw [hi]
    exact leftBridge i)

/-- Actual left graph, spanning tree, original edge labels and all chords. -/
def left : GraphData (Fin 5) Label where
  graph := leftGraph
  tree := leftTree
  tree_le := by decide
  isTree := leftTree_isTree
  ground := {h,a,c,e}
  edge := ![s(0,1),s(1,2),s(1,3),s(0,4),s(0,0),s(0,0),s(0,0)]
  tree_edges := by decide
  labels_injective := by decide
  chords := Fin 2
  start i := (leftChordEnds i).1
  finish i := (leftChordEnds i).2
  chord_adj := by decide
  chord_not_tree := by decide
  chord_cover := by decide

private def leftChordPath (i : Fin 2) :
    left.tree.Walk (left.start i) (left.finish i) := by
  fin_cases i
  · exact (.cons (show left.tree.Adj 0 1 from by decide) (.cons (show left.tree.Adj 1 2 from by decide) .nil))
  · exact (.cons (show left.tree.Adj 0 1 from by decide) (.cons (show left.tree.Adj 1 3 from by decide) .nil))
private theorem leftChordPath_isPath (i : Fin 2) :
    (leftChordPath i).IsPath := by
  fin_cases i <;> simp [leftChordPath,left,leftChordEnds,
    SimpleGraph.Walk.cons_isPath_iff]

/-- Rows derived from the actual unique marked-tree paths, with original labels. -/
theorem left_rows (i : Fin 2) : left.rows.row i =
  ![{h,a},{h,c}] i := by
  have hp := left.path_eq i (leftChordPath i) (leftChordPath_isPath i)
  change ({h,a,c,e} : Finset Label).filter (fun j => left.edge j ∈ (left.path i).edges) = _
  rw [hp]
  fin_cases i <;> decide

private def parentEnds (i : Fin 6) : Fin 7 × Fin 7 :=
  ![(0,1),(1,2),(1,3),(5,0),(5,4),(5,6)] i
private def parentChordEnds (i : Fin 4) : Fin 7 × Fin 7 :=
  ![(0,2),(0,3),(4,6),(6,0)] i
private def parentTree : SimpleGraph (Fin 7) :=
  edgeGraph {s(0,1),s(1,2),s(1,3),s(5,0),s(5,4),s(5,6)} (by decide)
private def parentGraph : SimpleGraph (Fin 7) :=
  edgeGraph {s(0,1),s(1,2),s(1,3),s(5,0),s(5,4),s(5,6),s(0,2),s(0,3),s(4,6),s(6,0)} (by decide)
private def parentSide (i : Fin 6) : Finset (Fin 7) :=
  ![{1,2,3},{2},{3},{0,1,2,3},{4},{6}] i
private theorem parentBridge (i : Fin 6) :
    parentTree.IsBridge s((parentEnds i).1,(parentEnds i).2) := by
  apply CutWalk.bridge_of_predicate (fun v => v ∉ parentSide i)
  · exact (by decide : ∀ i : Fin 6, (parentEnds i).1 ∉ parentSide i) i
  · exact (by decide : ∀ i : Fin 6, ¬ (parentEnds i).2 ∉ parentSide i) i
  · exact (by decide : ∀ (i : Fin 6) (x y : Fin 7), parentTree.Adj x y →
      s(x,y) ≠ s((parentEnds i).1,(parentEnds i).2) →
      (x ∉ parentSide i ↔ y ∉ parentSide i)) i
private theorem parentTree_isTree : parentTree.IsTree where
  connected := by
    apply SimpleGraph.connected_iff_exists_forall_reachable.mpr
    refine ⟨(5 : Fin 7),?_⟩
    intro v
    fin_cases v
    · exact (show parentTree.Walk 5 0 from (.cons (show parentTree.Adj 5 0 from by decide) .nil)).reachable
    · exact (show parentTree.Walk 5 1 from (.cons (show parentTree.Adj 5 0 from by decide) (.cons (show parentTree.Adj 0 1 from by decide) .nil))).reachable
    · exact (show parentTree.Walk 5 2 from (.cons (show parentTree.Adj 5 0 from by decide) (.cons (show parentTree.Adj 0 1 from by decide) (.cons (show parentTree.Adj 1 2 from by decide) .nil)))).reachable
    · exact (show parentTree.Walk 5 3 from (.cons (show parentTree.Adj 5 0 from by decide) (.cons (show parentTree.Adj 0 1 from by decide) (.cons (show parentTree.Adj 1 3 from by decide) .nil)))).reachable
    · exact (show parentTree.Walk 5 4 from (.cons (show parentTree.Adj 5 4 from by decide) .nil)).reachable
    · exact (show parentTree.Walk 5 5 from .nil).reachable
    · exact (show parentTree.Walk 5 6 from (.cons (show parentTree.Adj 5 6 from by decide) .nil)).reachable
  isAcyclic := SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mpr (by
    intro x y hxy
    have cover : ∀ x y : Fin 7, parentTree.Adj x y →
        ∃ i : Fin 6, s(x,y) = s((parentEnds i).1,(parentEnds i).2) := by decide
    obtain ⟨i,hi⟩ := cover x y hxy
    rw [hi]
    exact parentBridge i)

/-- Actual parent graph, spanning tree, original edge labels and all chords. -/
def parent : GraphData (Fin 7) Label where
  graph := parentGraph
  tree := parentTree
  tree_le := by decide
  isTree := parentTree_isTree
  ground := {h,a,c,one,two,three}
  edge := ![s(0,1),s(1,2),s(1,3),s(0,0),s(5,0),s(5,4),s(5,6)]
  tree_edges := by decide
  labels_injective := by decide
  chords := Fin 4
  start i := (parentChordEnds i).1
  finish i := (parentChordEnds i).2
  chord_adj := by decide
  chord_not_tree := by decide
  chord_cover := by decide

private def parentChordPath (i : Fin 4) :
    parent.tree.Walk (parent.start i) (parent.finish i) := by
  fin_cases i
  · exact (.cons (show parent.tree.Adj 0 1 from by decide) (.cons (show parent.tree.Adj 1 2 from by decide) .nil))
  · exact (.cons (show parent.tree.Adj 0 1 from by decide) (.cons (show parent.tree.Adj 1 3 from by decide) .nil))
  · exact (.cons (show parent.tree.Adj 4 5 from by decide) (.cons (show parent.tree.Adj 5 6 from by decide) .nil))
  · exact (.cons (show parent.tree.Adj 6 5 from by decide) (.cons (show parent.tree.Adj 5 0 from by decide) .nil))
private theorem parentChordPath_isPath (i : Fin 4) :
    (parentChordPath i).IsPath := by
  fin_cases i <;> simp [parentChordPath,parent,parentChordEnds,
    SimpleGraph.Walk.cons_isPath_iff]

/-- Rows derived from the actual unique marked-tree paths, with original labels. -/
theorem parent_rows (i : Fin 4) : parent.rows.row i =
  ![{h,a},{h,c},{two,three},{three,one}] i := by
  have hp := parent.path_eq i (parentChordPath i) (parentChordPath_isPath i)
  change ({h,a,c,one,two,three} : Finset Label).filter (fun j => parent.edge j ∈ (parent.path i).edges) = _
  rw [hp]
  fin_cases i <;> decide

/-- Physical inclusion of the five old vertices; the new vertices are 5 and 6. -/
def oldVertex (v : Fin 5) : Fin 7 := ⟨v.val,by omega⟩

/-- Delete the actual old bridge 04 and add the wheel spokes/rim edges. This
is an adjacency identity of the constructed graph, not an assumed root formula. -/
theorem physical_attachment : ∀ x y : Fin 7, parent.graph.Adj x y ↔
    (∃ u v : Fin 5, left.graph.Adj u v ∧ s(u,v) ≠ s(0,4) ∧
      oldVertex u = x ∧ oldVertex v = y) ∨
    s(x,y) ∈ ({s(5,0),s(5,4),s(5,6),s(4,6),s(6,0)} : Finset (Sym2 (Fin 7))) := by
  decide

/-- Seven physical vertices, ten distinct physical edges and six tree labels. -/
theorem physical_counts : Fintype.card (Fin 7) = 7 ∧
    ({s(0,1),s(1,2),s(1,3),s(5,0),s(5,4),s(5,6),
      s(0,2),s(0,3),s(4,6),s(6,0)} : Finset (Sym2 (Fin 7))).card = 10 ∧
    parent.ground.card = 6 := by decide

/-- Actual graph adjacency is exactly this ten-edge list, in either orientation. -/
theorem physical_edges : ∀ x y : Fin 7, parent.graph.Adj x y ↔
    s(x,y) ∈ ({s(0,1),s(1,2),s(1,3),s(5,0),s(5,4),s(5,6),
      s(0,2),s(0,3),s(4,6),s(6,0)} : Finset (Sym2 (Fin 7))) := by decide

/-- Literal left root on ALL h,a,c,e, with h a ghost. -/
def leftRoot : Family Label := facets {{a,e},{c,e}}
/-- Literal parent root; no old ghost label is discarded from its full ground. -/
def parentRoot : Family Label :=
  facets {{a,one,two,three},{c,one,two,three},{a,c,h,one},{a,c,h,two}}

theorem left_root : left.rows.root = leftRoot := by
  apply SetLike.ext
  intro s
  change (∃ i : Fin 2, s ⊆ left.ground \ left.rows.row i) ↔ s ∈ leftRoot
  simp_rw [left_rows]
  exact (by decide : ∀ s : Finset Label,
    (∃ i : Fin 2, s ⊆ left.ground \ (![{h,a},{h,c}] i)) ↔ s ∈ leftRoot) s

theorem parent_root : parent.rows.root = parentRoot := by
  apply SetLike.ext
  intro s
  change (∃ i : Fin 4, s ⊆ parent.ground \ parent.rows.row i) ↔ s ∈ parentRoot
  simp_rw [parent_rows]
  exact (by decide : ∀ s : Finset Label,
    (∃ i : Fin 4, s ⊆ parent.ground \ (![{h,a},{h,c},{two,three},{three,one}] i)) ↔
      s ∈ parentRoot) s

/-- Full marked grounds and the genuine left ghost; e is removed only from
the parent's tree ground, while the ambient Label type is unchanged. -/
theorem full_grounds : left.ground = {h,a,c,e} ∧
    parent.ground = {h,a,c,one,two,three} ∧
    h ∈ left.ground ∧ ({h} : Finset Label) ∉ leftRoot ∧ e ∉ parent.ground := by decide

/-- Unprotected base after the two lifted vertical pairs. -/
def B0 : Family Label := facets
  {{c,one,two,three},{a,c,h,one},{a,c,h,two}}
/-- Terminal base is a genuine cone at c. -/
def Bf : Family Label := facets {{c,three},{a,c,h,one},{a,c,h,two}}
/-- Core computed by protection: its collar is retained only on the core. -/
def C : Family Label := Bf ⊔ delta {c,one,two}
/-- The one outside critical top. -/
def q : Finset Label := {a,one,two}

private def leftLowers : List (Finset Label) := [{a},{e}]
private def leftApices : List Label := [e,c]
private def leftLower (i : Fin 2) := leftLowers[i.val]'(by simp [leftLowers]; exact i.isLt)
private def leftApex (i : Fin 2) := leftApices[i.val]'(by simp [leftApices]; exact i.isLt)
private def leftState (n : Nat) : Family Label := cut (leftRoot) (leftLowers.take n).toFinset
private theorem leftFacts : ∀ i : Fin 2,
    (leftLower i).Nonempty ∧ leftApex i ∉ leftLower i ∧
    insert (leftApex i) (leftLower i) ∈ leftState i.val ∧
    ∀ s ∈ leftState i.val, leftLower i ⊆ s →
      s = leftLower i ∨ s = insert (leftApex i) (leftLower i) := by decide
private def leftPair (i : Fin 2) : CollapsePair Label :=
  emitPair (leftState i.val) (leftLower i) (leftApex i)
    (leftFacts i).1 (leftFacts i).2.1 (leftFacts i).2.2.1 (leftFacts i).2.2.2
private theorem leftNext (i : Fin 2) :
    (leftPair i).retained = project (leftState (i.val+1)) := by
  rw [leftPair,emitPair_retained]
  congr 1
  fin_cases i <;> apply SetLike.ext <;> intro s <;>
    simp [leftState,leftLowers,leftLower,cut]
private def leftStep (i : Fin 2) :
    Sequence (project (leftState i.val)) (project (leftState (i.val+1))) :=
  (Sequence.step (leftPair i) (Sequence.refl _)).cast rfl (leftNext i)
private theorem leftFinal : leftState 2 = (delta {c}) := by
  apply SetLike.ext
  exact (by decide : ∀ s : Finset Label, s ∈ leftState 2 ↔ s ∈ (delta {c}))

/-- Genuine left native sequence, from finite current-coface proofs. -/
def leftSequence : Sequence (project (leftRoot)) (project (delta {c})) :=
  ((leftStep 0).append (leftStep 1)).cast
    (by simp [leftState]) (congrArg project leftFinal)

private def verticalLowers : List (Finset Label) := [{a,one,three},{a,three}]
private def verticalApices : List Label := [two,two]
private def verticalLower (i : Fin 2) := verticalLowers[i.val]'(by simp [verticalLowers]; exact i.isLt)
private def verticalApex (i : Fin 2) := verticalApices[i.val]'(by simp [verticalApices]; exact i.isLt)
private def verticalState (n : Nat) : Family Label := cut (parentRoot) (verticalLowers.take n).toFinset
private theorem verticalFacts : ∀ i : Fin 2,
    (verticalLower i).Nonempty ∧ verticalApex i ∉ verticalLower i ∧
    insert (verticalApex i) (verticalLower i) ∈ verticalState i.val ∧
    ∀ s ∈ verticalState i.val, verticalLower i ⊆ s →
      s = verticalLower i ∨ s = insert (verticalApex i) (verticalLower i) := by decide
private def verticalPair (i : Fin 2) : CollapsePair Label :=
  emitPair (verticalState i.val) (verticalLower i) (verticalApex i)
    (verticalFacts i).1 (verticalFacts i).2.1 (verticalFacts i).2.2.1 (verticalFacts i).2.2.2
private theorem verticalNext (i : Fin 2) :
    (verticalPair i).retained = project (verticalState (i.val+1)) := by
  rw [verticalPair,emitPair_retained]
  congr 1
  fin_cases i <;> apply SetLike.ext <;> intro s <;>
    simp [verticalState,verticalLowers,verticalLower,cut]
private def verticalStep (i : Fin 2) :
    Sequence (project (verticalState i.val)) (project (verticalState (i.val+1))) :=
  (Sequence.step (verticalPair i) (Sequence.refl _)).cast rfl (verticalNext i)
private theorem verticalFinal : verticalState 2 = (B0 ⊔ delta q) := by
  apply SetLike.ext
  exact (by decide : ∀ s : Finset Label, s ∈ verticalState 2 ↔ s ∈ (B0 ⊔ delta q))

/-- Genuine vertical native sequence, from finite current-coface proofs. -/
def verticalSequence : Sequence (project (parentRoot)) (project (B0 ⊔ delta q)) :=
  ((verticalStep 0).append (verticalStep 1)).cast
    (by simp [verticalState]) (congrArg project verticalFinal)

private def baseLowers : List (Finset Label) := [{one,two,three},{one,two},{one,three},{two,three}]
private def baseApices : List Label := [c,c,c,c]
private def baseLower (i : Fin 4) := baseLowers[i.val]'(by simp [baseLowers]; exact i.isLt)
private def baseApex (i : Fin 4) := baseApices[i.val]'(by simp [baseApices]; exact i.isLt)
private def baseState (n : Nat) : Family Label := cut (B0) (baseLowers.take n).toFinset
private theorem baseFacts : ∀ i : Fin 4,
    (baseLower i).Nonempty ∧ baseApex i ∉ baseLower i ∧
    insert (baseApex i) (baseLower i) ∈ baseState i.val ∧
    ∀ s ∈ baseState i.val, baseLower i ⊆ s →
      s = baseLower i ∨ s = insert (baseApex i) (baseLower i) := by decide
private def basePair (i : Fin 4) : CollapsePair Label :=
  emitPair (baseState i.val) (baseLower i) (baseApex i)
    (baseFacts i).1 (baseFacts i).2.1 (baseFacts i).2.2.1 (baseFacts i).2.2.2
private theorem baseNext (i : Fin 4) :
    (basePair i).retained = project (baseState (i.val+1)) := by
  rw [basePair,emitPair_retained]
  congr 1
  fin_cases i <;> apply SetLike.ext <;> intro s <;>
    simp [baseState,baseLowers,baseLower,cut]
private def baseStep (i : Fin 4) :
    Sequence (project (baseState i.val)) (project (baseState (i.val+1))) :=
  (Sequence.step (basePair i) (Sequence.refl _)).cast rfl (baseNext i)
private theorem baseFinal : baseState 4 = (Bf) := by
  apply SetLike.ext
  exact (by decide : ∀ s : Finset Label, s ∈ baseState 4 ↔ s ∈ (Bf))

/-- Genuine base native sequence, from finite current-coface proofs. -/
def baseSequence : Sequence (project (B0)) (project (Bf)) :=
  ((baseStep 0).append (baseStep 1).append (baseStep 2).append (baseStep 3)).cast
    (by simp [baseState]) (congrArg project baseFinal)

/-- The input left list is derived, not supplied; it has one vertical move. -/
theorem left_order : leftSequence.pairs.map (fun P => (P.lower,P.upper)) =
    [({a},{a,e}),({e},{e,c})] := by
  simp [leftSequence,leftStep,Sequence.pairs_cast,Sequence.pairs_append,
    Sequence.pairs,leftPair,emitPair,leftLower,leftApex,leftLowers,leftApices,
    CollapsePair.upper] <;> decide

/-- The actual unprotected link list is descending by Y size, with 12 included. -/
theorem base_order : baseSequence.pairs.map (fun P => (P.lower,P.upper)) =
    [({one,two,three},{c,one,two,three}),({one,two},{c,one,two}),
      ({one,three},{c,one,three}),({two,three},{c,two,three})] := by
  simp [baseSequence,baseStep,Sequence.pairs_cast,Sequence.pairs_append,
    Sequence.pairs,basePair,emitPair,baseLower,baseApex,baseLowers,baseApices,
    CollapsePair.upper] <;> decide

private theorem singleton_facets (t : Finset Label) : facets {t} = delta t := by
  apply SetLike.ext
  intro s
  change (∃ q ∈ ({t} : Finset (Finset Label)), s ⊆ q) ↔ s ⊆ t
  simp

private theorem project_union_simplices (K : Family Label) (H : Finset (Finset Label)) :
    project K ⊔ FinitePrescribedPairProtection.simplices H = project (K ⊔ facets H) := by
  ext s
  change (s.Nonempty ∧ s ∈ K) ∨
    (s.Nonempty ∧ ∃ t ∈ H, s ⊆ t) ↔
    s.Nonempty ∧ (s ∈ K ∨ ∃ t ∈ H, s ⊆ t)
  tauto

/-- T2 computes exactly the blocked 12 pair from this genuine base list. -/
theorem skipped_order :
    (FinitePrescribedPairProtection.skipped baseSequence.pairs {q}).map (fun P => (P.lower,P.upper)) =
      [({one,two},{c,one,two})] := by
  simp [baseSequence,baseStep,Sequence.pairs_cast,Sequence.pairs_append,Sequence.pairs,basePair,emitPair,baseLower,baseApex,baseLowers,baseApices,CollapsePair.upper,FinitePrescribedPairProtection.skipped,FinitePrescribedPairProtection.emitted,FinitePrescribedPairProtection.blocked,q,Finset.subset_iff] <;> decide

/-- The three later emitted link pairs are actual forward scan output. -/
theorem emitted_order :
    (FinitePrescribedPairProtection.emitted baseSequence.pairs {q}).map (fun P => (P.lower,P.upper)) =
      [({one,two,three},{c,one,two,three}),({one,three},{c,one,three}),
        ({two,three},{c,two,three})] := by
  simp [baseSequence,baseStep,Sequence.pairs_cast,Sequence.pairs_append,Sequence.pairs,basePair,emitPair,baseLower,baseApex,baseLowers,baseApices,CollapsePair.upper,FinitePrescribedPairProtection.skipped,FinitePrescribedPairProtection.emitted,FinitePrescribedPairProtection.blocked,q,Finset.subset_iff] <;> decide

/-- The native scan also computes the exact ORIGINAL base indices. -/
theorem scan_indices :
    FinitePrescribedPairProtection.skippedIndices baseSequence.pairs {q} = [1] ∧
    FinitePrescribedPairProtection.emittedIndices baseSequence.pairs {q} = [0,2,3] := by
  simp [baseSequence,baseStep,Sequence.pairs_cast,Sequence.pairs_append,Sequence.pairs,basePair,emitPair,baseLower,baseApex,baseLowers,baseApices,CollapsePair.upper,FinitePrescribedPairProtection.skippedIndices,FinitePrescribedPairProtection.emittedIndices,FinitePrescribedPairProtection.skippedIndexed,FinitePrescribedPairProtection.emittedIndexed,FinitePrescribedPairProtection.blocked,q,Finset.subset_iff] <;> decide

private theorem skipped_tops : FinitePrescribedPairProtection.skippedTops baseSequence.pairs {q} =
    {{c,one,two}} := by
  simp [FinitePrescribedPairProtection.skippedTops,baseSequence,baseStep,Sequence.pairs_cast,Sequence.pairs_append,Sequence.pairs,basePair,emitPair,baseLower,baseApex,baseLowers,baseApices,CollapsePair.upper,FinitePrescribedPairProtection.skipped,FinitePrescribedPairProtection.emitted,FinitePrescribedPairProtection.blocked,q,Finset.subset_iff] <;> decide

/-- The actual generic core is exactly the displayed G1 core. -/
theorem core_identity : FinitePrescribedPairProtection.core baseSequence {q} = project C := by
  unfold FinitePrescribedPairProtection.core
  rw [skipped_tops,project_union_simplices,singleton_facets]
  rfl

private theorem base_union_identity : project B0 ⊔ FinitePrescribedPairProtection.simplices {q} =
    project (B0 ⊔ delta q) := by
  rw [project_union_simplices,singleton_facets]
private theorem endpoint_identity : FinitePrescribedPairProtection.core baseSequence {q} ⊔
    FinitePrescribedPairProtection.simplices {q} = project (C ⊔ delta q) := by
  rw [core_identity,project_union_simplices,singleton_facets]

/-- This is the genuine generic consumer: T2 constructs the protected suffix. -/
def protectedSuffix : Sequence (project (B0 ⊔ delta q)) (project (C ⊔ delta q)) :=
  (FinitePrescribedPairProtection.protectedReplay baseSequence {q}).cast base_union_identity endpoint_identity

/-- Actual parent main sequence, with its vertical block and protected suffix. -/
def main : Sequence (project parent.rows.root) (project (C ⊔ delta q)) :=
  (verticalSequence.append protectedSuffix).cast (congrArg project parent_root).symm rfl

/-- All five actual main pairs, including the two original lifted vertical moves. -/
theorem main_order : main.pairs.map (fun P => (P.lower,P.upper)) =
    [({a,one,three},{a,one,two,three}),({a,three},{a,two,three}),
      ({one,two,three},{c,one,two,three}),({one,three},{c,one,three}),
      ({two,three},{c,two,three})] := by
  simp only [main,Sequence.pairs_cast,Sequence.pairs_append,List.map_append,
    protectedSuffix,FinitePrescribedPairProtection.protectedReplay_pairs]
  rw [emitted_order]
  simp [verticalSequence,verticalStep,Sequence.pairs_cast,Sequence.pairs_append,
    Sequence.pairs,verticalPair,emitPair,verticalLower,verticalApex,
    verticalLowers,verticalApices,CollapsePair.upper] <;> decide

/-- Full raw boundary includes the empty face; q itself is absent from C. -/
theorem critical_data : CriticalData C {q} := by
  have hc := FinitePrescribedPairProtection.critical_boundary baseSequence {q}
    (by decide : ∀ t ∈ ({q} : Finset (Finset Label)), t ∉ project B0)
    (by decide : ∀ t ∈ ({q} : Finset (Finset Label)), ∀ s,
      s.Nonempty → s ⊂ t → s ∈ project B0)
  constructor
  · decide
  · intro t ht hC
    have hn : t.Nonempty := (by decide : ∀ t ∈ ({q} : Finset (Finset Label)),
      t.Nonempty) t ht
    apply hc.1 t ht
    rw [core_identity]
    exact ⟨hn,hC⟩
  · intro t ht s hst
    by_cases h0 : s = ∅
    · subst s
      exact (by decide : (∅ : Finset Label) ∈ C)
    · have hs := hc.2 t ht s (Finset.nonempty_iff_ne_empty.mpr h0) hst
      rw [core_identity] at hs
      exact hs.2
  · decide

/-- The source's existing native cone theorem supplies the terminal core tail. -/
def coneTail : Sequence (project Bf) (project (delta {c})) :=
  collapseCone parent.ground Bf c (by decide) (by decide) (by decide)

/-- The skipped pair is run on C ALONE before appending the actual cone tail. -/
def collar : Sequence (project C) (project Bf) :=
  (FinitePrescribedPairProtection.standaloneReplay baseSequence {q}).cast core_identity rfl

theorem collar_order : collar.pairs.map (fun P => (P.lower,P.upper)) =
    [({one,two},{c,one,two})] := by
  rw [collar,Sequence.pairs_cast,FinitePrescribedPairProtection.standaloneReplay_pairs,skipped_order]

/-- Separate core collapse constructed from original-order skipped replay. -/
def separate : Sequence (project C) (project (delta {c})) := collar.append coneTail

/-- Actual graph-derived strong certificate, with no supplied certificate input. -/
def certificate : Certificate parent.ground parent.rows.root where
  supported := parent.rows.root_supported
  core := C
  critical := {q}
  vertex := c
  vertex_mem := by decide
  core_supported := by decide
  critical_supported := by decide
  cells := critical_data
  main := main.cast rfl (by rw [endpoint,singleton_facets])
  separate := separate

/-- The standalone collar has exactly two current cofaces in C. -/
theorem standalone_cofaces : ∀ s : Finset Label,
    (s ∈ project C ∧ {one,two} ⊆ s) ↔
      s = {one,two} ∨ s = {c,one,two} := by decide

/-- On the full endpoint the same lower has the THIRD coface q=a12. -/
theorem full_endpoint_cofaces : ∀ s : Finset Label,
    (s ∈ project (C ⊔ delta q) ∧ {one,two} ⊆ s) ↔
      s = {one,two} ∨ s = {c,one,two} ∨ s = q := by decide

/-- Exact collar deletion, in its correct current ambient only. -/
theorem collar_deletion : cut C {{one,two}} = Bf := by
  apply SetLike.ext
  exact (by decide : ∀ s : Finset Label, s ∈ cut C {{one,two}} ↔ s ∈ Bf)

/-- Exact cone-tail list from the existing descending-fibre constructor. -/
theorem coneTail_order : coneTail.pairs.map (fun P => (P.lower,P.upper)) =
    (fibres ((parent.ground.erase c).powerset.filter
      (fun t => t.Nonempty ∧ t ∈ Bf))).map (fun t => (t,insert c t)) := by
  simp only [coneTail,collapseCone,Sequence.pairs_cast,rectangle_order,
    Finset.empty_union]

namespace Regression
abbrev RLabel := Fin 4
/-- a=0,b=1,c=2,d=3, with no hidden label deletion. -/
def initial : Family RLabel := facets {{0,1,2},{0,2,3},{1,2,3}}
def critical : Finset RLabel := {0,1,3}
private def lowers : List (Finset RLabel) := [{0,1},{0,2},{1,2},{0},{1},{2}]
private def apices : List RLabel := [2,3,3,3,3,3]
private def lower (i : Fin 6) := lowers[i.val]'(by simp [lowers]; exact i.isLt)
private def apex (i : Fin 6) := apices[i.val]'(by simp [apices]; exact i.isLt)
private def state (n : Nat) : Family RLabel := cut initial (lowers.take n).toFinset
private theorem facts : ∀ i : Fin 6,
    (lower i).Nonempty ∧ apex i ∉ lower i ∧ insert (apex i) (lower i) ∈ state i.val ∧
    ∀ s ∈ state i.val, lower i ⊆ s → s = lower i ∨ s = insert (apex i) (lower i) := by
  decide
private def pair (i : Fin 6) : CollapsePair RLabel :=
  emitPair (state i.val) (lower i) (apex i)
    (facts i).1 (facts i).2.1 (facts i).2.2.1 (facts i).2.2.2
private theorem next (i : Fin 6) : (pair i).retained = project (state (i.val+1)) := by
  rw [pair,emitPair_retained]
  congr 1
  fin_cases i <;> apply SetLike.ext <;> intro s <;> simp [state,lowers,lower,cut]
private def step (i : Fin 6) :
    Sequence (project (state i.val)) (project (state (i.val+1))) :=
  (Sequence.step (pair i) (Sequence.refl _)).cast rfl (next i)
private theorem finalState : state 6 = delta {3} := by
  apply SetLike.ext
  exact (by decide : ∀ s : Finset RLabel, s ∈ state 6 ↔ s ∈ delta {3})

/-- Genuine six-step source sequence, not a hand-supplied desired replay. -/
def original : Sequence (project initial) (project (delta {3})) :=
  ((((((step 0).append (step 1)).append (step 2)).append (step 3)).append
    (step 4)).append (step 5)).cast (by simp [state]) (congrArg project finalState)

theorem original_order : original.pairs.map (fun P => (P.lower,P.upper)) =
    [({0,1},{0,1,2}),({0,2},{0,2,3}),({1,2},{1,2,3}),
      ({0},{0,3}),({1},{1,3}),({2},{2,3})] := by
  simp [original,step,Sequence.pairs_cast,Sequence.pairs_append,Sequence.pairs,
    pair,emitPair,lower,apex,lowers,apices,CollapsePair.upper] <;> decide

theorem input_critical_data : CriticalData initial {critical} := by
  constructor <;> decide

/-- Every pair is skipped recursively, including lowers outside original abd. -/
theorem all_skipped :
    FinitePrescribedPairProtection.skipped original.pairs {critical} = original.pairs ∧
    FinitePrescribedPairProtection.emitted original.pairs {critical} = [] := by
  simp [original,step,Sequence.pairs_cast,Sequence.pairs_append,Sequence.pairs,
    pair,emitPair,lower,apex,lowers,apices,CollapsePair.upper,
    FinitePrescribedPairProtection.skipped,FinitePrescribedPairProtection.emitted,
    FinitePrescribedPairProtection.blocked,critical,Finset.subset_iff] <;> decide

/-- The protected core really is all of B0 in this recursive-skip example. -/
theorem core_is_initial : FinitePrescribedPairProtection.core original {critical} =
    project initial := by
  unfold FinitePrescribedPairProtection.core FinitePrescribedPairProtection.skippedTops
  rw [all_skipped.1]
  simp only [original,step,Sequence.pairs_cast,Sequence.pairs_append,Sequence.pairs,
    List.map_append,List.map_cons,List.map_nil,pair,emitPair,CollapsePair.upper,
    lower,apex,lowers,apices]
  ext s
  revert s
  decide

/-- Original-order replay is a constructed native consumer of the generic theorem. -/
def forward : Sequence (project initial) (project (delta {3})) :=
  (FinitePrescribedPairProtection.standaloneReplay original {critical}).cast core_is_initial rfl

theorem forward_order : forward.pairs.map (fun P => (P.lower,P.upper)) =
    original.pairs.map (fun P => (P.lower,P.upper)) := by
  rw [forward,Sequence.pairs_cast,FinitePrescribedPairProtection.standaloneReplay_pairs,
    all_skipped.1]

/-- Reverse replay would start with c,cd, but c has seven CURRENT cofaces. -/
theorem reverse_first_has_seven :
    ((Finset.univ : Finset (Finset RLabel)).filter
      (fun s => s ∈ project initial ∧ ({2} : Finset RLabel) ⊆ s)).card = 7 ∧
    ¬ ({2} : Finset RLabel) ⊆ critical := by decide

/-- The actual seven faces, showing exactly why the reversed first pair fails. -/
theorem reverse_first_cofaces : ∀ s : Finset RLabel,
    (s ∈ project initial ∧ {2} ⊆ s) ↔
      s ∈ ({ {2},{0,2},{1,2},{2,3},{0,1,2},{0,2,3},{1,2,3} } : Finset (Finset RLabel)) := by
  decide
end Regression

end D5.S3.Geometry.OriginalLabelTwoSum.ProtectedG1
