import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233123SquareStrip
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233251TriangleStrip
import D5.S3.ConceptDynamics.InformationEscape.DependentFamily
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

/-! Readout registrations for the generating-function identity and its finite certificate. -/

namespace Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233123SquareStrip

open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233123SquareStrip
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233251TriangleStrip (Valid)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit PowerSeries

noncomputable section

attribute [local irreducible] a classCount firstCount

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ _ n => a n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ n => a n + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R :=
    (1 - 4 * X) * (1 - 12 * X) *
      (PowerSeries.mk fun n => (R.readout () () n : ℤ)) = X * (1 - 8 * X)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  change (1 - 4 * X) * (1 - 12 * X) *
      (PowerSeries.mk fun n => ((a n + 1 : ℕ) : ℤ)) = X * (1 - 8 * X) at h
  have h0 : a 0 = 0 := by unfold a; decide +kernel
  have hb := congrArg (PowerSeries.coeff 0) h
  simpa [PowerSeries.coeff_mul, h0] using hb

def family : Registration arena (type_of% @result) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    change a 0 ≠ a 1
    unfold a
    decide +kernel

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@result) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233123SquareStrip.auditUnit
  realizationName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233123SquareStrip.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => a n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233123SquareStrip
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg", "arg", "arg", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit

namespace FiniteCertificate

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => Bool) (fun _ => ℤ)

def actual : Realization signature :=
  realize signature (fun _ _ n => firstCount n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ n => firstCount n + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R :=
    (∀ s p, Valid s p →
      classCount s p true = (if s.2 then 12 else 4) ∧
      classCount s p false = (if s.2 then 0 else 4)) ∧
    R.readout () () true = 0 ∧ R.readout () () false = 1

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h.2.1
  have ha := finite_certificate.2.1
  change firstCount true + 1 = 0 at hb
  linarith

def family : Registration arena (type_of% @finite_certificate) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨finite_certificate, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), true, false, ?_⟩
    change firstCount true ≠ firstCount false
    rw [finite_certificate.2.1, finite_certificate.2.2]
    decide

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@finite_certificate) (Realization signature) Type Unit where
  unitName :=
    `Reg.A233123FiniteCertificate.auditUnit
  realizationName :=
    ``family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => firstCount n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233123SquareStrip
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit

end FiniteCertificate
end
end Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233123SquareStrip
