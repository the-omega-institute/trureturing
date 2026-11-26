import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.UniverseSingleReadout
import D5.S3.Quantum.Recovery.BKMActualMetricCoordinates

/-! Positive definiteness as a readout of the actual BKM coefficient. -/

open scoped Matrix.Norms.L2Operator ComplexOrder
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Recovery.BKMActualMetricCoordinates
open _root_.D5.S3.Quantum.Recovery.BKMRelativeDensity

noncomputable section

namespace Reg.D5.S3.Quantum.Recovery.BKMActualMetricCoordinates

universe u

abbrev signature : Signature :=
  Reg.Support.UniverseSingleReadout.signature (Type u)
    (fun n => Matrix (n × n) (n × n) ℂ) (fun _ => Prop)

def actual : Realization signature.{u} :=
  realize signature (fun _ _ coefficient => coefficient.PosDef) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {n : Type u} [Fintype n] [DecidableEq n]
    (c : Matrix n n ℂ) (_hc : c.PosDef), R.readout () n (omegaCoefficient c)

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  exact h (1 : Matrix (ULift.{u} Unit) (ULift.{u} Unit) ℂ) Matrix.PosDef.one

def registration : Registration arena.{u}
    (∀ {n : Type u} [Fintype n] [DecidableEq n]
      (c : Matrix n n ℂ) (_hc : c.PosDef), (omegaCoefficient c).PosDef) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@omegaCoefficient_posDef, rejected, rejected_law⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro role
    let n := ULift.{u} Unit
    refine ⟨n, 1, 0, ?_⟩
    intro h
    change ((1 : Matrix (n × n) (n × n) ℂ).PosDef) =
      ((0 : Matrix (n × n) (n × n) ℂ).PosDef) at h
    have hz := h.mp Matrix.PosDef.one
    have hv0 : (fun _ : n × n => (1 : ℂ)) ≠ 0 := by
      intro he
      have hentry := congrFun he (ULift.up (), ULift.up ())
      norm_num at hentry
    have hv := hz.dotProduct_mulVec_pos hv0
    simp at hv

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@omegaCoefficient_posDef.{u})
    (type_of% (realize signature.{u} (fun _ _ coefficient => coefficient.PosDef)
      (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Quantum.Recovery.BKMActualMetricCoordinates.omegaCoefficient_posDef.__information_unit,
  realizationName := `Reg.D5.S3.Quantum.Recovery.BKMActualMetricCoordinates.registration,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature.{u} (fun _ _ coefficient => coefficient.PosDef)
    (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Quantum.Recovery.BKMActualMetricCoordinates,
    definition := none, coordinates := #[0],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn"], stateBinder := 0,
      functionOperand := true, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[] }

end Reg.D5.S3.Quantum.Recovery.BKMActualMetricCoordinates
