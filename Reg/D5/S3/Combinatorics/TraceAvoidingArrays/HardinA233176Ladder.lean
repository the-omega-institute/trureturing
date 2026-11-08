import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233176Ladder
import D5.S3.ConceptDynamics.InformationEscape.DependentFamily
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

/-! Readout registrations for the ladder generating function and its initial coefficients. -/

namespace Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233176Ladder

open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233176Ladder
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit PowerSeries

noncomputable section

attribute [local irreducible] a

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ _ n => a n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ n => a n + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R :=
    (1 - 8 * X) * (1 - 24 * X - 256 * X ^ 2 + 1024 * X ^ 3) *
      (PowerSeries.mk fun n => (R.readout () () n : ℤ)) =
        X * (11 - 272 * X - 576 * X ^ 2 + 20992 * X ^ 3 - 53248 * X ^ 4)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  change (1 - 8 * X) * (1 - 24 * X - 256 * X ^ 2 + 1024 * X ^ 3) *
    (PowerSeries.mk fun n => ((a n + 1 : ℕ) : ℤ)) =
      X * (11 - 272 * X - 576 * X ^ 2 + 20992 * X ^ 3 - 53248 * X ^ 4) at h
  have h0 := finite_certificate.1
  have hb := congrArg (PowerSeries.coeff 0) h
  simpa [PowerSeries.coeff_mul, Nat.cast_add, h0] using hb

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
    intro h
    have hh := congrArg (fun n : ℕ => (n : ℤ)) h
    linarith [finite_certificate.1, finite_certificate.2.1]

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@result) (Realization signature) Type Unit where
  unitName :=
    `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233176Ladder.auditUnit
  realizationName :=
    `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233176Ladder.family
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
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233176Ladder
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

namespace InitialCoefficients

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ _ n => a n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ n => a n + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R :=
    (R.readout () () 0 : ℤ) = 0 ∧
    (R.readout () () 1 : ℤ) = 11 ∧
    (R.readout () () 2 : ℤ) = 80 ∧
    (R.readout () () 3 : ℤ) = 2688 ∧
    (R.readout () () 4 : ℤ) = 78336 ∧
    (R.readout () () 5 : ℤ) = 2469888 ∧
    (R.readout () () 6 : ℤ) = 76447744 ∧
    (R.readout () () 7 : ℤ) = 2385772544 ∧
    (R.readout () () 8 : ℤ) = 74291609600 ∧
    (R.readout () () 9 : ℤ) = 2315406802944 ∧
    (R.readout () () 10 : ℤ) = 72144847372288 ∧
    (R.readout () () 11 : ℤ) = 2248141575290880

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h.1
  change ((a 0 + 1 : ℕ) : ℤ) = 0 at hb
  have ha := finite_certificate.1
  simp only [Nat.cast_add, Nat.cast_one] at hb
  linarith

def family : Registration arena (type_of% @finite_certificate) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨finite_certificate, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    change a 0 ≠ a 1
    intro h
    have hh := congrArg (fun n : ℕ => (n : ℤ)) h
    linarith [finite_certificate.1, finite_certificate.2.1]

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@finite_certificate) (Realization signature) Type Unit where
  unitName :=
    `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233176Ladder.InitialCoefficients.auditUnit
  realizationName :=
    `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233176Ladder.InitialCoefficients.family
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
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233176Ladder
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit

end InitialCoefficients

end
end Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233176Ladder
