import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.Semigroups.WuRankOneEndpointClifford

/-! Source-bound readouts for the endpoint action on Pauli words. -/

noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence (Pauli)
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.WuRankOneEndpointFloor

namespace Reg.D5.S3.Quantum.Semigroups.WuRankOneEndpointClifford

private abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => TwoMode)
    (fun _ => TwoMode → Prop)

private def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), 0, 1, ?_⟩
  intro h
  exact (one_ne_zero : (1 : TwoMode) ≠ 0) (Eq.mp (congrFun h 0) rfl)

namespace PauliEigenvalue

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ (p q : Pauli),
    R.readout () () (A₁ (pauliWord p q)) (((lambda : ℂ) ^ cliffordDegree p q) • pauliWord p q)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h .I .I

def family : Registration arena (type_of% @A₁_pauliWord) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@A₁_pauliWord, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@A₁_pauliWord) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Semigroups.WuRankOneEndpointClifford.A₁_pauliWord.audit
  realizationName := `Reg.D5.S3.Quantum.Semigroups.WuRankOneEndpointClifford.PauliEigenvalue.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Semigroups.WuRankOneEndpointClifford
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end PauliEigenvalue

end Reg.D5.S3.Quantum.Semigroups.WuRankOneEndpointClifford
