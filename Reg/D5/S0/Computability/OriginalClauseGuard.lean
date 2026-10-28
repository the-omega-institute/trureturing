import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import Reg.Support.BinaryLanguageAudit
import D5.S0.Computability.OriginalClauseGuard

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Reg.D5.S0.Computability.OriginalClauseGuard
open _root_.Complexity _root_.Complexity.StackProgram
open _root_.PredictiveThermodynamic.OriginalGuard
open _root_.PredictiveThermodynamic.Conventional (ParsePhase)
open _root_.Reg.Support.BinaryLanguageAudit
open _root_.Reg.Support.BinaryMachineAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape

namespace ScannerTime

def signature : DependentFamily.Signature where
  Params := Unit
  State := fun _ => Word
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => Nat
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : DependentFamily.Realization signature :=
  DependentFamily.realize signature (fun _ _ w => w.length) (fun e => nomatch e)

def arena : DependentFamily.Arena where
  signature := signature
  Law := fun R => ∀ (p : ParsePhase) (w : Word) (r : StackMachine.Registers 6),
    r 0 = w → Exec scan (.inl p) r ((show Nat from R.readout () () w) + 2)
      (decide (_root_.PredictiveThermodynamic.Unrestricted.scanPhase p w = .ending),
        StackMachine.set r 0 [])

abbrev sourceScope := type_of% (@exec_scan)
theorem source_bridge : sourceScope ↔ arena.Law actual := Iff.rfl

def erased : DependentFamily.Realization signature :=
  DependentFamily.realize signature (fun _ _ _ => (0 : Nat)) (fun e => nomatch e)

theorem erased_fails : ¬ arena.Law erased := by
  intro h
  have impossible := (h .bodyFirst [false] (fun j => if j = 0 then [false] else []) rfl).run
  change (none : Option (Bool × StackMachine.Registers 6)) = some _ at impossible
  cases impossible

def family : DependentFamily.Registration arena sourceScope where
  actual := actual
  bridge := source_bridge
  variation := ⟨exec_scan,erased,erased_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨erased,?_,rfl,erased_fails⟩
      intro j hj
      exact (hj (@Subsingleton.elim Unit _ j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    cases i
    refine ⟨(),[],[false],?_⟩
    change (0 : Nat) ≠ 1
    decide

/-- The full source telescope observes raw input length inside the executed count.
Erasing that length destroys the actual halting execution on a one-bit word. -/
noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,0,0,0,0}
      (@exec_scan) (DependentFamily.Realization signature) Unit Unit where
  unitName := `PredictiveThermodynamic.OriginalGuard.exec_scan.__information_unit
  realizationName := `Reg.D5.S0.Computability.OriginalClauseGuard.ScannerTime.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (DependentFamily.realize signature
    (fun _ _ w => w.length) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S0.Computability.OriginalClauseGuard
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","body","body","body","fn","arg","fn","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end ScannerTime
namespace PolynomialRepair

abbrev signature : DependentFamily.Signature where
  Params := Unit
  State := fun _ => Word → Word
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : DependentFamily.Realization signature :=
  DependentFamily.realize signature (fun _ _ (n : Word → Word) => Complexity.PolyTime n) (fun e => nomatch e)

def arena : DependentFamily.Arena where
  signature := signature
  Law := fun R => ∀ (fallback : Word),
    R.readout () () (repair fallback)

abbrev sourceScope := type_of% (@PredictiveThermodynamic.OriginalGuard.polyTime_repair)
theorem source_bridge : sourceScope ↔ arena.Law actual := Iff.rfl

def erased : DependentFamily.Realization signature :=
  DependentFamily.realize signature (fun _ _ _ => (False : Prop)) (fun e => nomatch e)

theorem erased_fails : ¬ arena.Law erased := by
  intro h
  exact h []

def family : DependentFamily.Registration arena sourceScope where
  actual := actual
  bridge := source_bridge
  variation := ⟨PredictiveThermodynamic.OriginalGuard.polyTime_repair,erased,erased_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨erased,?_,rfl,erased_fails⟩
      intro j hj
      exact (hj (@Subsingleton.elim Unit _ j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    cases i
    refine ⟨(),(fun x : Word => x),diagonalOutput,?_⟩
    change PolyTime (fun x => x) ≠ PolyTime diagonalOutput
    intro heq
    exact diagonal_not_polyTime (heq ▸ polyTime_id)

noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,0,0,0,0}
      (@PredictiveThermodynamic.OriginalGuard.polyTime_repair) (DependentFamily.Realization signature) Unit Unit where
  unitName := `PredictiveThermodynamic.OriginalGuard.polyTime_repair.__information_unit
  realizationName := `Reg.D5.S0.Computability.OriginalClauseGuard.PolynomialRepair.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (DependentFamily.realize signature
    (fun _ _ (n : Word → Word) => Complexity.PolyTime n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S0.Computability.OriginalClauseGuard
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end PolynomialRepair

end Reg.D5.S0.Computability.OriginalClauseGuard
