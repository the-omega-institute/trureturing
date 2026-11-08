import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Combinatorics.Graph.Walks.CycleDetour

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency.types false

namespace Reg.D5.S3.Combinatorics.Graph.Walks.CycleDetour

open LeanInformationAudit SimpleGraph
open _root_.D5.S3.Combinatorics.Graph.Walks.CycleDetour
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped Classical

universe u
noncomputable section

abbrev Parameters := Σ V : Type u, Σ G : SimpleGraph V, Σ base : V,
  Σ successor : V, Σ _path : G.Walk successor base, ℕ

def signature : Signature where
  Params := Parameters.{u}
  State params := params.2.1.Walk (params.2.2.2.2.1.getVert params.2.2.2.2.2)
    (params.2.2.2.2.1.getVert params.2.2.2.2.2)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def arena : Arena where
  signature := signature.{u}
  Law readout := ∀ {V : Type u} {G : SimpleGraph V} {base successor : V}
    (closing : G.Adj base successor) (path : G.Walk successor base),
    (path.cons closing).IsCycle → ∀ (index : ℕ), index < path.length →
    ∀ (detour : G.Walk base (path.getVert index)), detour.IsPath → 2 ≤ detour.length →
    (∀ vertex ∈ detour.support, vertex ∈ (path.cons closing).support →
      vertex = base ∨ vertex = path.getVert index) →
    G.Adj successor (path.getVert (index + 1)) →
    ∃ extended : G.Walk (path.getVert index) (path.getVert index),
      extended.IsCycle ∧ readout.readout () ⟨V, G, base, successor, path, index⟩ extended =
        (path.cons closing).length + detour.length - 1 ∧
      ∀ vertex, vertex ∈ extended.support ↔
        vertex ∈ (path.cons closing).support ∨ vertex ∈ detour.support

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => (0 : ℕ)) (fun empty _ => Empty.elim empty)

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  classical
  intro law
  let V : Type u := ULift.{u} (Fin 4)
  let G : SimpleGraph V := completeGraph V
  have hadj : ∀ left right : Fin 4, left ≠ right → G.Adj ⟨left⟩ ⟨right⟩ := by
    intro left right hne
    change (⟨left⟩ : V) ≠ ⟨right⟩
    exact fun heq => hne (congrArg ULift.down heq)
  have h01 := hadj 0 1 (by decide)
  have h12 := hadj 1 2 (by decide)
  have h20 := hadj 2 0 (by decide)
  have h03 := hadj 0 3 (by decide)
  have h31 := hadj 3 1 (by decide)
  have h32 := hadj 3 2 (by decide)
  let path : G.Walk ⟨1⟩ ⟨0⟩ := Walk.cons h12 (Walk.cons h20 Walk.nil)
  let detour : G.Walk ⟨0⟩ ⟨1⟩ := Walk.cons h03 (Walk.cons h31 Walk.nil)
  have hcycle : (path.cons h01).IsCycle := by
    simp [path, Walk.cons_isCycle_iff, Walk.cons_isPath_iff, Sym2.eq_iff,
      h01.ne, h01.ne.symm, h12.ne, h12.ne.symm, h20.ne, h20.ne.symm]
  have hdetour : detour.IsPath := by
    simp [detour, Walk.cons_isPath_iff, h03.ne, h01.ne, h31.ne]
  have hclean : ∀ vertex ∈ detour.support, vertex ∈ (path.cons h01).support →
      vertex = (⟨0⟩ : V) ∨ vertex = (⟨1⟩ : V) := by
    intro vertex hmem hcycleMem
    simp only [detour, path, Walk.support_cons, Walk.support_nil,
      List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hmem hcycleMem
    rcases hmem with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact False.elim (by aesop)
    · exact Or.inr rfl
  obtain ⟨extended, _, hlength, _⟩ := law h01 path hcycle 0 (by simp [path])
    detour hdetour (show 2 ≤ 2 from le_rfl) hclean h12
  change 0 = 4 at hlength
  omega

def family : Registration arena.{u} (type_of% (@exists_cycle_through_detour.{u})) where
  actual := realize signature (fun _ _ walk => walk.length) (fun empty _ => Empty.elim empty)
  bridge := Iff.rfl
  variation := ⟨@exists_cycle_through_detour, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other hne
      exact (hne (@Subsingleton.elim Unit _ other role)).elim
    · intro empty
      exact nomatch empty
  dependence := by
    intro role
    let V : Type u := ULift.{u} Bool
    let G : SimpleGraph V := completeGraph V
    let first : V := ⟨false⟩
    let second : V := ⟨true⟩
    have hadj : G.Adj first second := by
      change first ≠ second
      intro heq
      cases congrArg ULift.down heq
    let walk : G.Walk first first := Walk.cons hadj (Walk.cons hadj.symm Walk.nil)
    refine ⟨⟨V, G, first, first, Walk.nil, 0⟩, Walk.nil, walk, ?_⟩
    change (Walk.nil : G.Walk first first).length ≠ walk.length
    simp [walk]

noncomputable def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, _, 0, 0}
      (@exists_cycle_through_detour.{u}) (Realization signature.{u}) Type Unit where
  unitName := `D5.S3.Combinatorics.Graph.Walks.CycleDetour.exists_cycle_through_detour.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Walks.CycleDetour.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ walk => walk.length) (fun empty _ => Empty.elim empty))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Walks.CycleDetour
    definition := none
    coordinates := #[0, 1, 2, 3, 5, 7]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "arg", "body", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms registration
end
end Reg.D5.S3.Combinatorics.Graph.Walks.CycleDetour
