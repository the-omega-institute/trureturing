import D5.S3.Combinatorics.Graph.StarForming.WitnessBudget
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

noncomputable section
open Classical LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.Graph.StarForming.WitnessBudget
open _root_.D5.S3.Combinatorics.Graph.StarForming.DegreeCapacity
open _root_.D5.S3.Combinatorics.Graph.StarFormingDissociationRefutation
open scoped BigOperators

namespace Reg.D5.S3.Combinatorics.Graph.StarForming.WitnessBudget

abbrev Parameters := Σ V : Type, Σ _ : SimpleGraph V, ℕ

abbrev signature : Signature where
  Params := Parameters
  State p := Finset p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def observation : ∀ (_ : Unit) (p : Parameters), Finset p.1 → ℕ := fun _ _ S => S.card

def noAnchor : ∀ (_ : Empty) (p : Parameters), Finset p.1 := fun e => nomatch e

def bad : Realization signature := realize signature (fun _ _ S => S.card+1) noAnchor

abbrev arena : Arena where
  signature := signature
  Law r := ∀ {V : Type} [f : Fintype V] [e : DecidableEq V]
    (G : SimpleGraph V) [a : DecidableRel G.Adj] (S : Finset V)
    (hS : IsMinimalStarForming G 2 S) (d : ℕ) (_hd : 1 ≤ d)
    (_hdegree : ∀ v, degree G v=d),
    (2*d-1)*r.readout () ⟨V,G,d⟩ S+(isolates G S).card+
      (∑ x ∈ Finset.univ \ S, unused G S hS d x)=d*Fintype.card V

abbrev SourceClaim : Prop := ∀ {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V)
    (hS : IsMinimalStarForming G 2 S) (d : ℕ) (_hd : 1 ≤ d)
    (_hdegree : ∀ v, degree G v=d),
    (2*d-1)*S.card+(isolates G S).card+
      (∑ x ∈ Finset.univ \ S, unused G S hS d x)=d*Fintype.card V

private theorem bad_law : ¬ arena.Law bad := by
  intro h
  have hS : IsMinimalStarForming (⊥ : SimpleGraph (Fin 0)) 2 ∅ := by
    constructor
    · intro x _; exact Fin.elim0 x
    · intro T hT; exact (Finset.not_ssubset_empty T hT).elim
  have hh := h (⊥ : SimpleGraph (Fin 0)) ∅ hS 1 (by omega) (fun v => Fin.elim0 v)
  change (2*1-1)*(0+1)+0+0=1*0 at hh
  omega

def family : Registration arena SourceClaim where
  actual := realize signature observation noAnchor
  bridge := Iff.rfl
  variation := ⟨by
    intro V f e G a S hS d hd hr
    exact regular_budget G S hS d hd hr,bad,bad_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨bad,?_,rfl,bad_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    let p : Parameters := ⟨Fin 1,⊥,1⟩
    refine ⟨p,∅,{(0 : Fin 1)},?_⟩
    change (∅ : Finset (Fin 1)).card ≠ ({(0 : Fin 1)} : Finset (Fin 1)).card
    simp

noncomputable def regularBudgetRegistration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.Combinatorics.Graph.StarForming.WitnessBudget.regular_budget)
      (Realization signature) Unit Unit where
  unitName := `D5.S3.Combinatorics.Graph.StarForming.WitnessBudget.regular_budget.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.StarForming.WitnessBudget.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature observation noAnchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.StarForming.WitnessBudget
    definition := none
    coordinates := #[0,3,7]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","body","body","fn","arg","fn","arg","fn","arg","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Combinatorics.Graph.StarForming.WitnessBudget
