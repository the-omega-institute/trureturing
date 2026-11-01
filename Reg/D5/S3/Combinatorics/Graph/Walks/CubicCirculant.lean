import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Graph.Walks.CubicCirculant
import Reg.Support.DependentFamily

set_option autoImplicit false
namespace Reg.D5.S3.Combinatorics.Graph.Walks.CubicCirculant
open _root_.CubicCirculant
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open SimpleGraph
noncomputable section
namespace Components
abbrev signature : Signature.{0,0,0,0,0} where
  Params := ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ n a => Nat.card (cubic n a).ConnectedComponent) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena.{0,0,0,0,0} where
  signature := signature
  Law R := ∀ (n a : ℕ) (hn : 4 ≤ n) (hne : Even n)
      (ha : 1 ≤ a) (halt : a < n/2),
    let h := Nat.gcd n a
    let ell := n/h
    let g := Nat.gcd a (n/2)
    R.readout () n a = g ∧
      (Even ell → h=g ∧ ∃ m : ℕ, ell=2*(m+2) ∧
        ∀ C : (cubic n a).ConnectedComponent, Nonempty (mobius m ≃g C.toSimpleGraph)) ∧
      (Odd ell → Even h ∧ g=h/2 ∧ ∃ r : ℕ, ell=r+3 ∧
        ∀ C : (cubic n a).ConnectedComponent,
          Nonempty (((SimpleGraph.cycleGraph (r+3)) □ (⊤ : SimpleGraph (ZMod 2))) ≃g C.toSimpleGraph))

private lemma source_law : arena.Law actual := by
  intro n a hn hne ha halt
  exact component_decomposition n a hn hne ha halt
private lemma rejected_fails : ¬ arena.Law rejected := by
  intro h
  have hh := (h 4 1 (by omega) (by decide) (by omega) (by omega)).1
  change (0 : ℕ) = Nat.gcd 1 (4/2) at hh
  norm_num at hh

def registration : Registration arena (type_of% (@_root_.CubicCirculant.component_decomposition)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨source_law,rejected,rejected_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,rejected_fails⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e; exact nomatch e
  dependence := by
    intro i
    cases i
    refine ⟨12,1,2,?_⟩
    change Nat.card (cubic 12 1).ConnectedComponent ≠ Nat.card (cubic 12 2).ConnectedComponent
    have h1 := (component_decomposition 12 1 (by omega) (by decide) (by omega) (by omega)).1
    have h2 := (component_decomposition 12 2 (by omega) (by decide) (by omega) (by omega)).1
    rw [h1,h2]
    norm_num

def contract : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.CubicCirculant.component_decomposition)
    (type_of% (realize signature (fun _ n a => Nat.card (cubic n a).ConnectedComponent) (fun e => nomatch e)))
    Type Unit := {
  unitName := Lean.Name.str (Lean.Name.str `CubicCirculant.component_decomposition
    "Reg.D5.S3.Combinatorics.Graph.Walks.CubicCirculant/Reg.D5.S3.Combinatorics.Graph.Walks.CubicCirculant.Components.arena/[anonymous]") "__information_unit"
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Walks.CubicCirculant.Components.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ n a => Nat.card (cubic n a).ConnectedComponent) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Walks.CubicCirculant
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","body","fn","arg","fn","arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit,value := .bool false }] }
#print axioms registration
#print axioms contract
end Components
end
end Reg.D5.S3.Combinatorics.Graph.Walks.CubicCirculant
