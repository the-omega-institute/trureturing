import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Combinatorics.Graph.Walks.ConnectivityFan

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Combinatorics.Graph.Walks.ConnectivityFan

open LeanInformationAudit SimpleGraph
open _root_.D5.S3.Combinatorics.Graph.Walks.ConnectivityFan
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

universe u
noncomputable section

abbrev Parameters := Σ V : Type u, Σ _G : SimpleGraph V, V × V

def signature : Signature where
  Params := Parameters.{u}
  State params := params.2.1.Walk params.2.2.1 params.2.2.2
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def arena : Arena where
  signature := signature.{u}
  Law readout := ∀ {V : Type u} [Finite V] {G : SimpleGraph V} {k : ℕ},
    (∀ S : Set V, S.ncard < k → (G.induce Sᶜ).Connected) →
    ∀ (B : Finset V) {x : V}, x ∉ B →
    ∃ (endpoint : Fin (min k B.card) → V) (paths : ∀ index, G.Walk x (endpoint index)),
      (∀ index, endpoint index ∈ B ∧
        readout.readout () ⟨V, G, x, endpoint index⟩ (paths index) ∧
        ∀ y ∈ (paths index).support, y ∈ B → y = endpoint index) ∧
      (∀ left right, left ≠ right → ∀ y ∈ (paths left).support,
        y ∈ (paths right).support → y = x) ∧ Function.Injective endpoint

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => False) (fun empty _ => Empty.elim empty)

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  classical
  intro law
  let V : Type u := ULift.{u} Bool
  let G : SimpleGraph V := completeGraph V
  have hconn : ∀ S : Set V, S.ncard < 1 → (G.induce Sᶜ).Connected := by
    intro S hS
    have hzero : S.ncard = 0 := by omega
    have hempty : S = ∅ := (Set.ncard_eq_zero (Set.toFinite S)).mp hzero
    subst S
    haveI : Nonempty (↑((∅ : Set V)ᶜ)) := ⟨⟨⟨false⟩, by simp⟩⟩
    simpa [G] using (SimpleGraph.connected_top (V := ↑((∅ : Set V)ᶜ)))
  obtain ⟨endpoint, paths, hpaths, _⟩ := law hconn {⟨true⟩} (x := ⟨false⟩)
    (by simp only [Finset.mem_singleton]; intro heq; cases congrArg ULift.down heq)
  have hbad := (hpaths ⟨0, by simp⟩).2.1
  exact hbad

def family : Registration arena.{u} (type_of% (@exists_fan.{u})) where
  actual := realize signature (fun _ _ path => path.IsPath) (fun empty _ => Empty.elim empty)
  bridge := Iff.rfl
  variation := ⟨@exists_fan, rejected, rejected_law⟩
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
    let start : V := ⟨false⟩
    let other : V := ⟨true⟩
    have hadj : G.Adj start other := by
      change start ≠ other
      intro heq
      cases congrArg ULift.down heq
    let path : G.Walk start start := Walk.cons hadj (Walk.cons hadj.symm Walk.nil)
    refine ⟨⟨V, G, start, start⟩, Walk.nil, path, ?_⟩
    change (Walk.nil : G.Walk start start).IsPath ≠ path.IsPath
    intro heq
    have hpath : path.IsPath := heq ▸ Walk.IsPath.nil
    simpa [path, Walk.cons_isPath_iff] using hpath

noncomputable def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, _, 0, 0}
      (@exists_fan.{u}) (Realization signature.{u}) Type Unit where
  unitName := `D5.S3.Combinatorics.Graph.Walks.ConnectivityFan.exists_fan.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Walks.ConnectivityFan.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ path => path.IsPath)
    (fun empty _ => Empty.elim empty))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Walks.ConnectivityFan
    definition := none
    coordinates := #[0, 2, 6, 8, 9, 10]
    readouts := #[{
      path := #[]
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
end Reg.D5.S3.Combinatorics.Graph.Walks.ConnectivityFan
