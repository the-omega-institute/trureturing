/- GID: D5/S3/Combinatorics/Graph/Jacobi/BranchingHairTree
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Jacobi/BranchingHairTree
   mirror-E: none(waiver:actual-finite-flag-graft)
   anchors: []
   utility: none
   digest: Actual colored binary hair trees and cyclic-flag subdivision grafts. -/

import D5.S3.Combinatorics.Graph.Jacobi.CyclicFlagDiagram
import D5.S3.Combinatorics.Graph.Jacobi.HairTreeShape

/-! Open binary hair trees and their actual subdivision graft on cyclic-flag diagrams. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Graph.Jacobi


/-- A finite colored rooted hair tree before its stem is connected. Its root
is the unique fixed point of the partial edge pairing, not an anchor vertex. -/
structure OpenHair where
  Flag : Type
  finiteFlag : Finite Flag
  root : Flag
  edge : Flag → Flag
  edge_involutive : Function.Involutive edge
  edge_fixed_iff : ∀ f, edge f = f ↔ f = root
  next : Flag → Flag
  next_cube : ∀ f, next (next (next f)) = f
  color : Flag → Option LeafLabel
  color_none_iff : ∀ f, color f = none ↔ next f ≠ f

attribute [instance] OpenHair.finiteFlag

namespace OpenHair

private theorem edge_root (T : OpenHair) : T.edge T.root = T.root :=
  (T.edge_fixed_iff T.root).mpr rfl

private theorem edge_ne_root (T : OpenHair) {f : T.Flag} (h : f ≠ T.root) :
    T.edge f ≠ T.root := by
  intro he
  apply h
  have := congrArg T.edge he
  simpa only [T.edge_involutive f, edge_root] using this

noncomputable def leaf (c : Color) : OpenHair where
  Flag := Unit
  finiteFlag := inferInstance
  root := ()
  edge := id
  edge_involutive := fun _ => rfl
  edge_fixed_iff := fun f => by cases f; simp
  next := id
  next_cube := fun _ => rfl
  color := fun _ => some (.ordinary c)
  color_none_iff := fun _ => by simp

abbrev NodeFlag (L R : OpenHair) := Fin 3 ⊕ (L.Flag ⊕ R.Flag)

open Classical in
noncomputable def nodeEdge (L R : OpenHair) : NodeFlag L R → NodeFlag L R
  | .inl i => if i = 0 then .inl 0 else if i = 1 then .inr (.inl L.root)
      else .inr (.inr R.root)
  | .inr (.inl f) => if f = L.root then .inl 1 else .inr (.inl (L.edge f))
  | .inr (.inr f) => if f = R.root then .inl 2 else .inr (.inr (R.edge f))

noncomputable def node (L R : OpenHair) : OpenHair where
  Flag := NodeFlag L R
  finiteFlag := inferInstance
  root := .inl 0
  edge := nodeEdge L R
  edge_involutive f := by
    rcases f with i | f
    · fin_cases i <;> simp [nodeEdge]
    · rcases f with f | f
      · by_cases h : f = L.root
        · subst f; simp [nodeEdge]
        · simp [nodeEdge, h, edge_ne_root L h, L.edge_involutive f]
      · by_cases h : f = R.root
        · subst f; simp [nodeEdge]
        · simp [nodeEdge, h, edge_ne_root R h, R.edge_involutive f]
  edge_fixed_iff f := by
    rcases f with i | f
    · fin_cases i <;> simp [nodeEdge]
    · rcases f with f | f
      · by_cases h : f = L.root
        · subst f; simp [nodeEdge]
        · simp [nodeEdge, h, L.edge_fixed_iff]
      · by_cases h : f = R.root
        · subst f; simp [nodeEdge]
        · simp [nodeEdge, h, R.edge_fixed_iff]
  next
    | .inl i => .inl (finRotate 3 i)
    | .inr (.inl f) => .inr (.inl (L.next f))
    | .inr (.inr f) => .inr (.inr (R.next f))
  next_cube f := by
    rcases f with i | f
    · fin_cases i <;> rfl
    · rcases f with f | f
      · simp [L.next_cube]
      · simp [R.next_cube]
  color
    | .inl _ => none
    | .inr (.inl f) => L.color f
    | .inr (.inr f) => R.color f
  color_none_iff f := by
    rcases f with i | f
    · change (none : Option LeafLabel) = none ↔
        (Sum.inl (finRotate 3 i) : NodeFlag L R) ≠ Sum.inl i
      have hn : finRotate 3 i ≠ i := by fin_cases i <;> decide
      exact ⟨fun _ h => hn (Sum.inl.inj h), fun _ => rfl⟩
    · rcases f with f | f
      · simpa using L.color_none_iff f
      · simpa using R.color_none_iff f

end OpenHair

noncomputable def HairTree.model : HairTree Color → OpenHair
  | .leaf c => OpenHair.leaf c
  | .node l r => OpenHair.node l.model r.model

namespace FlagGraph

private theorem edge_outside {F : Type} (G : FlagGraph F) (a : F) {f : F}
    (ha : f ≠ a) (hb : f ≠ G.edge a) :
    G.edge f ≠ a ∧ G.edge f ≠ G.edge a := by
  constructor
  · intro h
    have := congrArg G.edge h
    exact hb (by simpa only [G.edge_involutive f] using this)
  · intro h
    exact ha (G.edge_involutive.injective h)

abbrev GraftFlag {F : Type} (T : OpenHair) := F ⊕ (Fin 3 ⊕ T.Flag)

open Classical in
noncomputable def graftEdge {F : Type} (G : FlagGraph F) (a : F) (T : OpenHair) :
    GraftFlag (F := F) T → GraftFlag (F := F) T
  | .inl f => if f = a then .inr (.inl 1) else
      if f = G.edge a then .inr (.inl 2) else .inl (G.edge f)
  | .inr (.inl i) => if i = 0 then .inr (.inr T.root) else
      if i = 1 then .inl a else .inl (G.edge a)
  | .inr (.inr f) => if f = T.root then .inr (.inl 0) else .inr (.inr (T.edge f))

/-- Actual subdivision of the selected edge, followed by stem attachment of
all finite tree flags. Every pre-existing cycle and color is retained. -/
noncomputable def graft {F : Type} (G : FlagGraph F) (a : F) (T : OpenHair) :
    FlagGraph (GraftFlag (F := F) T) where
  edge := graftEdge G a T
  edge_involutive f := by
    rcases f with f | f
    · by_cases ha : f = a
      · subst f; simp [graftEdge]
      · by_cases hb : f = G.edge a
        · subst f; simp [graftEdge, G.edge_ne]
        · obtain ⟨hea, heb⟩ := edge_outside G a ha hb
          simp [graftEdge, ha, hb, hea, heb, G.edge_involutive f]
    · rcases f with i | f
      · fin_cases i <;> simp [graftEdge, G.edge_ne]
      · by_cases hf : f = T.root
        · subst f; simp [graftEdge]
        · simp [graftEdge, hf, OpenHair.edge_ne_root T hf, T.edge_involutive f]
  edge_ne f := by
    rcases f with f | f
    · by_cases ha : f = a
      · simp [graftEdge, ha]
      · by_cases hb : f = G.edge a
        · subst f; simp [graftEdge, G.edge_ne a]
        · simpa [graftEdge, ha, hb] using G.edge_ne f
    · rcases f with i | f
      · fin_cases i <;> simp [graftEdge]
      · by_cases hf : f = T.root
        · simp [graftEdge, hf]
        · simp [graftEdge, hf, T.edge_fixed_iff]
  next
    | .inl f => .inl (G.next f)
    | .inr (.inl i) => .inr (.inl (finRotate 3 i))
    | .inr (.inr f) => .inr (.inr (T.next f))
  next_cube f := by
    rcases f with f | f
    · simp [G.next_cube]
    · rcases f with i | f
      · fin_cases i <;> rfl
      · simp [T.next_cube]
  color
    | .inl f => G.color f
    | .inr (.inl _) => none
    | .inr (.inr f) => T.color f
  color_none_iff f := by
    rcases f with f | f
    · simpa using G.color_none_iff f
    · rcases f with i | f
      · change (none : Option LeafLabel) = none ↔
          (Sum.inr (Sum.inl (finRotate 3 i)) : GraftFlag (F := F) T) ≠
            Sum.inr (Sum.inl i)
        have hn : finRotate 3 i ≠ i := by fin_cases i <;> decide
        exact ⟨fun _ h => hn (Sum.inl.inj (Sum.inr.inj h)), fun _ => rfl⟩
      · simpa using T.color_none_iff f

end FlagGraph

end D5.S3.Combinatorics.Graph.Jacobi
