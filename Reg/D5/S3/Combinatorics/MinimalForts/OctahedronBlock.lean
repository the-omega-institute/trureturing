import Reg.Support.DependentFamily
import D5.S3.Combinatorics.MinimalForts.OctahedronBlock

/-! Source models for unbounded whole-part and transversal classifications. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Combinatorics.MinimalForts.OctahedronBlock

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.MinimalForts.UniversalRoot
open _root_.D5.S3.Combinatorics.MinimalForts.OctahedronBlock

private abbrev propSignature (X : Type) : Signature where
  Params := Unit
  State _ := X
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

private abbrev propActual {X : Type} (L R : X → Prop) : Realization (propSignature X) :=
  realize (propSignature X) (fun i _ s => if i then R s else L s) (fun e => nomatch e)

private abbrev propArena (X : Type) : Arena where
  signature := propSignature X
  Law A := ∀ s, A.readout false () s ↔ A.readout true () s

private def propFamily {X : Type} (L R : X → Prop) (h : ∀ s, L s ↔ R s)
    (s0 s1 : X) (h0 : ¬ L s0) (h1 : L s1) :
    Registration (propArena X) (∀ s, L s ↔ R s) := by
  let bad : Realization (propSignature X) :=
    realize _ (fun i _ _ => if i then True else False) (fun e => nomatch e)
  have hbad : ¬ (propArena X).Law bad := by
    intro hb
    exact (hb s0).mpr trivial
  let altered (i : Bool) : Realization (propSignature X) :=
    realize _ (fun j p s => if j = i then True else (propActual L R).readout j p s)
      (fun e => nomatch e)
  have hR0 : ¬ R s0 := fun hr => h0 ((h s0).mpr hr)
  have hR1 : R s1 := (h s1).mp h1
  have halt (i : Bool) : ¬ (propArena X).Law (altered i) := by
    intro hb
    have hb0 := hb s0
    cases i with
    | false => exact hR0 (hb0.mp trivial)
    | true => exact h0 (hb0.mpr trivial)
  refine {
    actual := propActual L R
    bridge := Iff.rfl
    variation := ⟨h,bad,hbad⟩
    sensitivity := ?_
    dependence := ?_ }
  · constructor
    · intro i
      refine ⟨altered i, ?_, rfl, halt i⟩
      intro j hj
      simp only [altered, realize, if_neg hj]
    · intro e
      exact nomatch e
  · intro i
    refine ⟨(),s0,s1,?_⟩
    have hn : ¬ (propActual L R).readout i () s0 := by
      cases i
      · exact h0
      · exact hR0
    have hp : (propActual L R).readout i () s1 := by
      cases i
      · exact h1
      · exact hR1
    intro he
    rw [he] at hn
    exact hn hp

abbrev SubsetState := Σ m : {m : ℕ // 2 ≤ m}, Finset (Fin m.val × Fin 2)

private abbrev minimalLeft (s : SubsetState) : Prop :=
  MinimalFort (SimpleGraph.completeEquipartiteGraph s.1.val 2) s.2

private abbrev minimalRight (s : SubsetState) : Prop :=
  (∃ i, s.2 = part i) ∨ (s.2.card = 3 ∧ Transversal s.2)

private abbrev emptyState : SubsetState := ⟨⟨2,by omega⟩,∅⟩
private abbrev partState : SubsetState := ⟨⟨2,by omega⟩,part 0⟩

/-- This source model retains every m, every vertex subset and both classification predicates. -/
def minimalFamily : Registration (propArena SubsetState)
    (type_of% (@equipartite_minimal_iff)) := by
  have h : ∀ s : SubsetState, minimalLeft s ↔ minimalRight s :=
    fun s => equipartite_minimal_iff s.1.val s.1.property s.2
  have h0 : ¬ minimalLeft emptyState := by
    intro he
    exact Finset.not_nonempty_empty he.1.1
  have h1 : minimalLeft partState :=
    (h partState).mpr (Or.inl ⟨0,rfl⟩)
  let e := propFamily minimalLeft minimalRight h emptyState partState h0 h1
  refine {
    actual := e.actual
    bridge := ?_
    variation := e.variation
    sensitivity := e.sensitivity
    dependence := e.dependence }
  change (∀ m (hm : 2 ≤ m) S, MinimalFort (SimpleGraph.completeEquipartiteGraph m 2) S ↔
    (∃ i, S = part i) ∨ (S.card = 3 ∧ Transversal S)) ↔
      ∀ s : SubsetState, minimalLeft s ↔ minimalRight s
  constructor
  · intro hp s
    exact hp s.1.val s.1.property s.2
  · intro hp m hm S
    exact hp ⟨⟨m,hm⟩,S⟩

private abbrev rootedLeft (s : SubsetState) : Prop :=
  MinimalFort (cone (SimpleGraph.completeEquipartiteGraph s.1.val 2)) (rootSet s.2)

private abbrev rootedRight (s : SubsetState) : Prop := s.2.card = 2 ∧ Transversal s.2

private abbrev pairState : SubsetState := ⟨⟨2,by omega⟩,{(0,0),(1,0)}⟩

/-- The root model keeps actual cone forthood and the full two-part-transversal condition. -/
def rootedFamily : Registration (propArena SubsetState)
    (type_of% (@equipartite_rooted_iff)) := by
  have h : ∀ s : SubsetState, rootedLeft s ↔ rootedRight s :=
    fun s => equipartite_rooted_iff s.1.val s.1.property s.2
  have h0 : ¬ rootedLeft emptyState := by
    rw [h emptyState]
    simp [rootedRight, emptyState]
  have h1 : rootedLeft pairState := by
    apply (h pairState).mpr
    refine ⟨by simp [pairState], ?_⟩
    change Transversal ({(0,0),(1,0)} : Finset (Fin 2 × Fin 2))
    have hs : ∀ v : Fin 2 × Fin 2, v ∈ ({(0,0),(1,0)} : Finset _) → v.2 = 0 := by
      intro v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with hv | hv <;> simp [hv]
    intro a ha b hb he
    exact Prod.ext he ((hs a ha).trans (hs b hb).symm)
  let e := propFamily rootedLeft rootedRight h emptyState pairState h0 h1
  refine {
    actual := e.actual
    bridge := ?_
    variation := e.variation
    sensitivity := e.sensitivity
    dependence := e.dependence }
  change (∀ m (hm : 2 ≤ m) S,
    MinimalFort (cone (SimpleGraph.completeEquipartiteGraph m 2)) (rootSet S) ↔
    S.card = 2 ∧ Transversal S) ↔ ∀ s : SubsetState, rootedLeft s ↔ rootedRight s
  constructor
  · intro hp s
    exact hp s.1.val s.1.property s.2
  · intro hp m hm S
    exact hp ⟨⟨m,hm⟩,S⟩

abbrev countSignature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Fin 3
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev countActual : Realization countSignature :=
  realize countSignature (fun i _ m => if i = 0 then Fintype.card (Fin m × Fin 2)
    else if i = 1 then (minimalForts (SimpleGraph.completeEquipartiteGraph m 2)).card
    else (rootedChoices (SimpleGraph.completeEquipartiteGraph m 2)).card)
    (fun e => nomatch e)

abbrev countArena : Arena where
  signature := countSignature
  Law R := ∀ m : ℕ, 2 ≤ m →
    R.readout 0 () m = 2*m ∧ R.readout 1 () m = m + 8*m.choose 3 ∧
    R.readout 2 () m = 4*m.choose 2 ∧
    ∀ v, ∃ w, (SimpleGraph.completeEquipartiteGraph m 2).Adj v w

private abbrev countRejected : Realization countSignature :=
  realize countSignature (fun _ _ _ => 0) (fun e => nomatch e)

private theorem count_rejected_law : ¬ countArena.Law countRejected := by
  intro h
  have he := (h 2 (by omega)).1
  norm_num [countRejected,realize] at he

private abbrev countAltered (i : Fin 3) : Realization countSignature :=
  realize countSignature (fun j p m => if j = i then 0 else countActual.readout j p m)
    (fun e => nomatch e)

private theorem count_altered_law (i : Fin 3) : ¬ countArena.Law (countAltered i) := by
  intro h
  have he := h 2 (by omega)
  fin_cases i
  · have he0 := he.1
    norm_num [countAltered,realize] at he0
  · have he1 := he.2.1
    norm_num [countAltered,realize] at he1
  · have he2 := he.2.2.1
    norm_num [countAltered,realize,show Nat.choose 2 2 = 1 by decide] at he2

/-- Three actual cardinalities vary over all natural part counts, with the original graph law. -/
def countFamily : Registration countArena (type_of% (@equipartite_block)) where
  actual := countActual
  bridge := Iff.rfl
  variation := ⟨equipartite_block,countRejected,count_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨countAltered i, ?_,rfl,count_altered_law i⟩
      intro j hj
      simp only [countAltered,realize,if_neg hj]
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(),2,3,?_⟩
    have h2 := equipartite_block 2 (by omega)
    have h3 := equipartite_block 3 (by omega)
    fin_cases i
    · change Fintype.card (Fin 2 × Fin 2) ≠ Fintype.card (Fin 3 × Fin 2)
      rw [h2.1,h3.1]
      omega
    · change (minimalForts (SimpleGraph.completeEquipartiteGraph 2 2)).card ≠
        (minimalForts (SimpleGraph.completeEquipartiteGraph 3 2)).card
      rw [h2.2.1,h3.2.1]
      norm_num [show Nat.choose 2 3 = 0 by decide,show Nat.choose 3 3 = 1 by decide]
    · change (rootedChoices (SimpleGraph.completeEquipartiteGraph 2 2)).card ≠
        (rootedChoices (SimpleGraph.completeEquipartiteGraph 3 2)).card
      rw [h2.2.2.1,h3.2.2.1]
      norm_num [show Nat.choose 2 2 = 1 by decide,show Nat.choose 3 2 = 3 by decide]

end Reg.D5.S3.Combinatorics.MinimalForts.OctahedronBlock
