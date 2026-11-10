import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Quantum.Fermionic.CountableOccupationFock

/-! A source-family audit candidate for the unrestricted countable CAR. -/

noncomputable section
namespace Reg.D5.S3.Quantum.Fermionic.CountableOccupationFock

open _root_.D5.S3.Quantum.Fermionic.CountableOccupationFock
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := ℕ × Bool × Bool
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Module.End ℂ Fock
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ p i => mode i p.2.1 * mode p.1 p.2.2 + mode p.1 p.2.2 * mode i p.2.1)
  (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (i j : ℕ) (a b : Bool), R.readout () (j, a, b) i =
    if i = j ∧ a ≠ b then (1 : Module.End ℂ Fock) else 0

def rejected : Realization signature := realize signature (fun _ _ _ => 0)
  (fun e => nomatch e)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hz := h 0 0 false true
  change (0 : Module.End ℂ Fock) = if 0 = 0 ∧ false ≠ true then 1 else 0 at hz
  simpa using hz

def family : Registration arena (type_of% @car) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨car, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other hne
      exact (hne (Subsingleton.elim other role)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro role
    refine ⟨(0, false, true), 0, 1, ?_⟩
    change mode 0 false * mode 0 true + mode 0 true * mode 0 false ≠
      mode 1 false * mode 0 true + mode 0 true * mode 1 false
    rw [car, car]
    simp

/-- The original operator-valued readout is retained without changing its telescope. -/
def car_audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@car) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Quantum.Fermionic.CountableOccupationFock.carUnit
  realizationName := `Reg.D5.S3.Quantum.Fermionic.CountableOccupationFock.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p i => mode i p.2.1 * mode p.1 p.2.2 + mode p.1 p.2.2 * mode i p.2.1)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℕ
  sourceSelection := some {
    owner := `D5.S3.Quantum.Fermionic.CountableOccupationFock
    definition := none
    coordinates := #[1, 2, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Quantum.Fermionic.CountableOccupationFock
