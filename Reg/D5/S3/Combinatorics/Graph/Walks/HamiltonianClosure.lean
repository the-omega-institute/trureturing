import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Combinatorics.Graph.Walks.HamiltonianClosure

/-! Source-bound graph and walk operands for Hamiltonian degree-sum theorems. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Combinatorics.Graph.Walks.HamiltonianClosure

open LeanInformationAudit
open SimpleGraph
open _root_.D5.S3.Combinatorics.Graph.Walks.HamiltonianClosure
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

universe u
noncomputable section

abbrev GraphSignature : Signature where
  Params := Type u
  State V := SimpleGraph V
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ V := SimpleGraph V
  Anchor := Empty
  finiteAnchor := inferInstance

def graphActual : Realization GraphSignature.{u} :=
  realize GraphSignature (fun _ _ G => G) (fun e => nomatch e)

def graphRejected : Realization GraphSignature.{u} :=
  realize GraphSignature (fun _ _ _ => ⊥) (fun e => nomatch e)

abbrev oreArena : Arena where
  signature := GraphSignature.{u}
  Law R := ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj], 3 ≤ Fintype.card V →
    (∀ u v, u ≠ v → ¬ G.Adj u v → Fintype.card V ≤ G.degree u + G.degree v) →
    (R.readout () V G).IsHamiltonian

private theorem graphDependence : ObservationalDependence GraphSignature.{u} graphActual := by
  intro i
  refine ⟨ULift.{u} Bool, ⊥, ⊤, ?_⟩
  intro he
  have hbad := congrArg (fun G : SimpleGraph (ULift.{u} Bool) => G.Adj ⟨false⟩ ⟨true⟩) he
  simp [graphActual, realize] at hbad

private theorem oreRejected : ¬ oreArena.{u}.Law graphRejected := by
  classical
  intro h
  let V := ULift.{u} (Fin 3)
  have hh := @h V inferInstance inferInstance (completeGraph V) inferInstance
    (by simp [V]) (by intro a b hab hn; exact (hn hab).elim)
  change (⊥ : SimpleGraph V).IsHamiltonian at hh
  exact not_isHamiltonian_bot_of_card_ne_one (by simp [V]) hh

def oreFamily : Registration oreArena.{u} (type_of% (@ore.{u})) where
  actual := graphActual
  bridge := Iff.rfl
  variation := ⟨@ore, graphRejected, oreRejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨graphRejected, ?_, rfl, oreRejected⟩
      intro j hji
      exact (hji (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := graphDependence

abbrev WalkParameters := Σ V : Type u, Σ _G : SimpleGraph V, V
abbrev WalkSignature : Signature where
  Params := WalkParameters.{u}
  State p := p.2.1.Walk p.2.2 p.2.2
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.2.1.Walk p.2.2 p.2.2
  Anchor := Empty
  finiteAnchor := inferInstance

def walkActual : Realization WalkSignature.{u} :=
  realize WalkSignature (fun _ _ w => w) (fun e => nomatch e)
def walkRejected : Realization WalkSignature.{u} :=
  realize WalkSignature (fun _ _ _ => Walk.nil) (fun e => nomatch e)

abbrev pathArena : Arena where
  signature := WalkSignature.{u}
  Law R := ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {a b : V} (p : G.Walk a b), p.IsHamiltonian →
    3 ≤ Fintype.card V → Fintype.card V ≤ G.degree a + G.degree b →
    ∃ c : G.Walk a a, (R.readout () ⟨V, G, a⟩ c).IsHamiltonianCycle

private theorem walkDependence : ObservationalDependence WalkSignature.{u} walkActual := by
  intro i
  let V := ULift.{u} Bool
  let G : SimpleGraph V := completeGraph V
  let a : V := ⟨false⟩
  let b : V := ⟨true⟩
  have hab : G.Adj a b := by
    change a ≠ b
    intro he
    cases congrArg ULift.down he
  let q : G.Walk a a := Walk.cons hab (Walk.cons hab.symm Walk.nil)
  refine ⟨⟨V, G, a⟩, Walk.nil, q, ?_⟩
  intro he
  have hh := congrArg Walk.length he
  norm_num [walkActual, realize, q] at hh

private theorem pathRejected : ¬ pathArena.{u}.Law walkRejected := by
  classical
  intro h
  let V := ULift.{u} (Fin 3)
  let G : SimpleGraph V := completeGraph V
  let a : V := ⟨0⟩
  let b : V := ⟨1⟩
  let c : V := ⟨2⟩
  have hab : G.Adj a b := by change a ≠ b; decide
  have hbc : G.Adj b c := by change b ≠ c; decide
  let p : G.Walk a c := Walk.cons hab (Walk.cons hbc Walk.nil)
  have hp : p.IsHamiltonian := by
    intro v
    rcases v with ⟨v⟩
    fin_cases v <;> simp [p, a, b, c, List.count_cons] <;> decide
  obtain ⟨q, hq⟩ := @h V inferInstance inferInstance G inferInstance a c p hp
    (by simp [V]) (by simp [G, V])
  change (Walk.nil : G.Walk a a).IsHamiltonianCycle at hq
  exact hq.ne_nil rfl

def pathFamily : Registration pathArena.{u} (type_of% (@exists_hamiltonian_cycle_of_path.{u})) where
  actual := walkActual
  bridge := Iff.rfl
  variation := ⟨@exists_hamiltonian_cycle_of_path, walkRejected, pathRejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨walkRejected, ?_, rfl, pathRejected⟩
      intro j hji
      exact (hji (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := walkDependence

abbrev closureArena : Arena where
  signature := GraphSignature.{u}
  Law R := ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {u v : V}, u ≠ v → ¬ G.Adj u v →
    Fintype.card V ≤ G.degree u + G.degree v →
    ((G ⊔ edge u v).IsHamiltonian ↔ (R.readout () V G).IsHamiltonian)

private theorem closureRejected : ¬ closureArena.{u}.Law graphRejected := by
  classical
  intro h
  let V := ULift.{u} (Fin 4)
  let a : V := ⟨0⟩
  let b : V := ⟨1⟩
  let G : SimpleGraph V := (edge a b)ᶜ
  have hab : a ≠ b := by decide
  have hnon : ¬ G.Adj a b := by simp [G, edge_adj, hab]
  have hda : (edge a b).degree a = 1 := by
    rw [← card_neighborFinset_eq_degree]
    have he : (edge a b).neighborFinset a = {b} := by
      ext w
      simp only [mem_neighborFinset, edge_adj, Finset.mem_singleton]
      aesop
    rw [he]
    simp
  have hdb : (edge a b).degree b = 1 := by
    rw [← card_neighborFinset_eq_degree]
    have he : (edge a b).neighborFinset b = {a} := by
      ext w
      simp only [mem_neighborFinset, edge_adj, Finset.mem_singleton]
      aesop
    rw [he]
    simp
  have hdeg : Fintype.card V ≤ G.degree a + G.degree b := by
    simp only [G, degree_compl, hda, hdb]
    norm_num [V]
  have htop : G ⊔ edge a b = ⊤ := by
    ext x y
    simp only [G, sup_adj, top_adj, compl_adj]
    have he : (edge a b).Adj x y → x ≠ y := fun h => h.ne
    tauto
  have hham : (G ⊔ edge a b).IsHamiltonian := by
    rw [htop]
    exact isHamiltonian_top (by simp [V])
  have hh := (@h V inferInstance inferInstance G inferInstance a b hab hnon hdeg).1 hham
  change (⊥ : SimpleGraph V).IsHamiltonian at hh
  exact not_isHamiltonian_bot_of_card_ne_one (by simp [V]) hh

def closureFamily : Registration closureArena.{u} (type_of% (@isHamiltonian_sup_edge_iff.{u})) where
  actual := graphActual
  bridge := Iff.rfl
  variation := ⟨@isHamiltonian_sup_edge_iff, graphRejected, closureRejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨graphRejected, ?_, rfl, closureRejected⟩
      intro j hji
      exact (hji (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := graphDependence

noncomputable def oreRegistration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, _, 0, 0}
      (@ore.{u}) (Realization GraphSignature.{u}) Type Unit where
  unitName := `D5.S3.Combinatorics.Graph.Walks.HamiltonianClosure.ore.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Walks.HamiltonianClosure.oreFamily
  realizationSource := none
  generated := false
  arena := .source ⟨oreArena.{u}⟩
  objectArena := .source ⟨oreArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source oreArena.{u} ⟨oreFamily.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize GraphSignature (fun _ _ w => w) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Walks.HamiltonianClosure
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

noncomputable def pathRegistration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, _, 0, 0}
      (@exists_hamiltonian_cycle_of_path.{u}) (Realization WalkSignature.{u}) Type Unit where
  unitName := `D5.S3.Combinatorics.Graph.Walks.HamiltonianClosure.exists_hamiltonian_cycle_of_path.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Walks.HamiltonianClosure.pathFamily
  realizationSource := none
  generated := false
  arena := .source ⟨pathArena.{u}⟩
  objectArena := .source ⟨pathArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source pathArena.{u} ⟨pathFamily.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize WalkSignature (fun _ _ w => w) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Walks.HamiltonianClosure
    definition := none
    coordinates := #[0, 3, 5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "arg"]
      stateBinder := 11
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

noncomputable def closureRegistration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, _, 0, 0}
      (@isHamiltonian_sup_edge_iff.{u}) (Realization GraphSignature.{u}) Type Unit where
  unitName := `D5.S3.Combinatorics.Graph.Walks.HamiltonianClosure.isHamiltonian_sup_edge_iff.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Walks.HamiltonianClosure.closureFamily
  realizationSource := none
  generated := false
  arena := .source ⟨closureArena.{u}⟩
  objectArena := .source ⟨closureArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source closureArena.{u} ⟨closureFamily.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize GraphSignature (fun _ _ w => w) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Walks.HamiltonianClosure
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms oreFamily
#print axioms pathFamily
#print axioms closureFamily
#print axioms oreRegistration
#print axioms pathRegistration
#print axioms closureRegistration

end
end Reg.D5.S3.Combinatorics.Graph.Walks.HamiltonianClosure
