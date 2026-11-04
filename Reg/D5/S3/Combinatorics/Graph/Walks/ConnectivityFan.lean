import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Combinatorics.Graph.Walks.ConnectivityFan

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Combinatorics.Graph.Walks.ConnectivityFan

open LeanInformationAudit SimpleGraph
open _root_.D5.S3.Combinatorics.Graph.Walks.ConnectivityFan
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped Classical

universe u
noncomputable section

abbrev Parameters := Σ V : Type u, Σ _G : SimpleGraph V, Σ k : ℕ,
  Σ B : Finset V, Σ _x : V, Σ _endpoint : Fin (min k B.card) → V, Fin (min k B.card)

def signature : Signature where
  Params := Parameters.{u}
  State params := params.2.1.Walk params.2.2.2.2.1
    (params.2.2.2.2.2.1 params.2.2.2.2.2.2)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def arena : Arena where
  signature := signature.{u}
  Law readout := ∀ {V : Type u} [Finite V] {G : SimpleGraph V} {k : ℕ},
    (∀ S : Set V, S.ncard < k → (G.induce Sᶜ).Connected) →
    ∀ (B : Finset V) {x : V}, x ∉ B →
    ∃ (endpoint : Fin (min k B.card) → V) (paths : ∀ index, G.Walk x (endpoint index)),
      (∀ index, endpoint index ∈ B ∧
        readout.readout () ⟨V, G, k, B, x, endpoint, index⟩ (paths index) = true ∧
        ∀ y ∈ (paths index).support, y ∈ B → y = endpoint index) ∧
      (∀ left right, left ≠ right → ∀ y ∈ (paths left).support,
        y ∈ (paths right).support → y = x) ∧ Function.Injective endpoint

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => false) (fun empty _ => Empty.elim empty)

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
  cases hbad

def family : Registration arena.{u} (type_of% (@exists_fan.{u})) where
  actual := realize signature (fun _ _ path => decide path.IsPath) (fun empty _ => Empty.elim empty)
  bridge := by
    dsimp [arena, signature, realize]
    simp only [decide_eq_true_eq]
  variation := by
    refine ⟨?_, rejected, rejected_law⟩
    intro V hfinite G k hconn B x hx
    obtain ⟨endpoint, paths, hpaths, hdisjoint, hinjective⟩ := exists_fan hconn B hx
    refine ⟨endpoint, paths, fun index => ?_, hdisjoint, hinjective⟩
    exact ⟨(hpaths index).1,
      @decide_eq_true _ (Classical.propDecidable _) (hpaths index).2.1, (hpaths index).2.2⟩
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
    refine ⟨⟨V, G, 1, {start}, start, fun _ => start, ⟨0, by simp⟩⟩, Walk.nil, path, ?_⟩
    intro heq
    have hnil : (realize signature (fun _ _ path => decide path.IsPath)
      (fun empty _ => Empty.elim empty)).readout role
      ⟨V, G, 1, {start}, start, fun _ => start, ⟨0, by simp⟩⟩ Walk.nil = true :=
      @decide_eq_true _ (Classical.propDecidable _) Walk.IsPath.nil
    have hpath : path.IsPath := @of_decide_eq_true _ (Classical.propDecidable _) (heq.symm.trans hnil)
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
  readout := some (realize signature (fun _ _ path => decide path.IsPath)
    (fun empty _ => Empty.elim empty))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Walks.ConnectivityFan
    definition := none
    coordinates := #[0, 2, 3, 5, 6, 8, 10]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "body", "arg", "body", "fn", "arg", "body", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms registration

namespace MaximalCycle

abbrev Parameters := Σ V : Type u, Σ _G : SimpleGraph V, V

def signature : Signature where
  Params := Parameters.{u}
  State params := params.2.1.Walk params.2.2 params.2.2
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def arena : Arena where
  signature := signature.{u}
  Law readout := ∀ {V : Type u} [Finite V] {G : SimpleGraph V} {k : ℕ},
    3 ≤ Nat.card V → 2 ≤ k →
    (∀ S : Set V, S.ncard < k → (G.induce Sᶜ).Connected) →
    ∃ base, ∃ cycle : G.Walk base base, readout.readout () ⟨V, G, base⟩ cycle = true ∧
      (∀ otherBase (other : G.Walk otherBase otherBase),
        other.IsCycle → other.length ≤ cycle.length) ∧
      (cycle.induce {vertex | vertex ∈ cycle.support} (fun _ hmem => hmem)).IsHamiltonianCycle ∧
      ∀ x : V, x ∉ cycle.support →
        ∃ (endpoint : Fin (min k cycle.length) → V)
          (paths : ∀ index, G.Walk x (endpoint index)),
          (∀ index, endpoint index ∈ cycle.support ∧ (paths index).IsPath ∧
            ∀ y ∈ (paths index).support, y ∈ cycle.support → y = endpoint index) ∧
          (∀ left right, left ≠ right → ∀ y ∈ (paths left).support,
            y ∈ (paths right).support → y = x) ∧ Function.Injective endpoint

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => false) (fun empty _ => Empty.elim empty)

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  classical
  intro law
  let V : Type u := ULift.{u} (Fin 3)
  let G : SimpleGraph V := completeGraph V
  have hconn : ∀ S : Set V, S.ncard < 2 → (G.induce Sᶜ).Connected := by
    intro S hS
    have hne : S ≠ Set.univ := by
      intro heq
      subst S
      norm_num [V, Set.ncard_univ, Nat.card_eq_fintype_card] at hS
    have hnonempty : Sᶜ.Nonempty := by
      by_contra hnone
      apply hne
      exact Set.eq_univ_iff_forall.mpr fun vertex => by
        by_contra hmissing
        exact hnone ⟨vertex, hmissing⟩
    haveI : Nonempty (↑Sᶜ) := hnonempty.to_subtype
    simpa [G] using (SimpleGraph.connected_top (V := ↑Sᶜ))
  obtain ⟨base, cycle, hcycle, _⟩ := law (G := G) (k := 2)
    (by simp [V, Nat.card_eq_fintype_card]) (by omega) hconn
  cases hcycle

def family : Registration arena.{u} (type_of% (@exists_maximal_cycle_fans.{u})) where
  actual := realize signature (fun _ _ cycle => decide cycle.IsCycle)
    (fun empty _ => Empty.elim empty)
  bridge := by
    dsimp [arena, signature, realize]
    simp only [decide_eq_true_eq]
  variation := by
    refine ⟨?_, rejected, rejected_law⟩
    intro V hfinite G k hn hk hconn
    obtain ⟨base, cycle, hcycle, hrest⟩ := exists_maximal_cycle_fans hn hk hconn
    exact ⟨base, cycle, @decide_eq_true _ (Classical.propDecidable _) hcycle, hrest⟩
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
    let V : Type u := ULift.{u} (Fin 3)
    let G : SimpleGraph V := completeGraph V
    let first : V := ⟨0⟩
    let second : V := ⟨1⟩
    let third : V := ⟨2⟩
    have hfirst : G.Adj first second := by
      change first ≠ second
      intro heq
      have := congrArg (fun vertex : V => vertex.down.val) heq
      simp [first, second] at this
    have hsecond : G.Adj second third := by
      change second ≠ third
      intro heq
      have := congrArg (fun vertex : V => vertex.down.val) heq
      simp [second, third] at this
    have hthird : G.Adj third first := by
      change third ≠ first
      intro heq
      have := congrArg (fun vertex : V => vertex.down.val) heq
      simp [third, first] at this
    let cycle : G.Walk first first :=
      Walk.cons hfirst (Walk.cons hsecond (Walk.cons hthird Walk.nil))
    have hcycle : cycle.IsCycle := by
      simp only [cycle, Walk.cons_isCycle_iff, Walk.cons_isPath_iff, Walk.support_cons,
        Walk.support_nil, List.mem_cons, List.mem_singleton, Walk.edges_cons,
        Walk.edges_nil, List.not_mem_nil, Sym2.eq_iff]
      simp_all [hfirst.ne, hsecond.ne, hthird.ne, hfirst.ne.symm,
        hsecond.ne.symm, hthird.ne.symm, Walk.IsPath.nil]
    refine ⟨⟨V, G, first⟩, cycle, Walk.nil, ?_⟩
    intro heq
    have htrue : (realize signature (fun _ _ cycle => decide cycle.IsCycle)
      (fun empty _ => Empty.elim empty)).readout role ⟨V, G, first⟩ cycle = true :=
      @decide_eq_true _ (Classical.propDecidable _) hcycle
    have hnil : (Walk.nil : G.Walk first first).IsCycle :=
      @of_decide_eq_true _ (Classical.propDecidable _) (heq.symm.trans htrue)
    exact hnil.not_nil Walk.nil_nil

noncomputable def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, _, 0, 0}
      (@exists_maximal_cycle_fans.{u}) (Realization signature.{u}) Type Unit where
  unitName := `D5.S3.Combinatorics.Graph.Walks.ConnectivityFan.exists_maximal_cycle_fans.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Walks.ConnectivityFan.MaximalCycle.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ cycle => decide cycle.IsCycle)
    (fun empty _ => Empty.elim empty))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Walks.ConnectivityFan
    definition := none
    coordinates := #[0, 2, 7]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "arg", "body", "arg", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms registration
end MaximalCycle
end
end Reg.D5.S3.Combinatorics.Graph.Walks.ConnectivityFan
