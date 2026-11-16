import Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233175PairStripReadouts
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233175PairStrip
import D5.S3.ConceptDynamics.InformationEscape.DependentFamily
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

/-! Readout registrations for the generating-function identity and its finite certificate. -/

namespace Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233175PairStrip

open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233175PairStrip
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit PowerSeries

noncomputable section

attribute [local irreducible] a v total

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ _ n => a n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ n => a n + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R :=
    (1 - 4 * X) * (1 - 8 * X - 32 * X ^ 2) *
      (PowerSeries.mk fun n => (R.readout () () n : ℤ)) =
        X * (3 - 28 * X - 16 * X ^ 2 + 224 * X ^ 3)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  change (1 - 4 * X) * (1 - 8 * X - 32 * X ^ 2) *
      (PowerSeries.mk fun n => ((a n + 1 : ℕ) : ℤ)) =
        X * (3 - 28 * X - 16 * X ^ 2 + 224 * X ^ 3) at h
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
  unitName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233175PairStrip.auditUnit
  realizationName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233175PairStrip.family
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
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233175PairStrip
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
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℤ)

def actual : Realization signature :=
  realize signature (fun _ _ n => total (v n)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ n => total (v n) + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R :=
    (∀ q t b p, v 7 q t b p = 16 * v 6 q t b p - 32 * v 5 q t b p -
      320 * v 4 q t b p + 512 * v 3 q t b p + 2048 * v 2 q t b p) ∧
    R.readout () () 0 = 3 ∧ total (v 1) = 8 ∧ total (v 2) = 80 ∧
      total (v 3) = 800 ∧ total (v 4) = 8576 ∧
      total (v 5) = 92672 ∧ total (v 6) = 1009664

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h.2.1
  have ha := finite_certificate.2.1
  change total (v 0) + 1 = 3 at hb
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
    change total (v 0) ≠ total (v 1)
    rw [finite_certificate.2.1, finite_certificate.2.2.1]
    decide

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@finite_certificate) (Realization signature) Type Unit where
  unitName :=
    `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233175PairStrip.FiniteCertificate.auditUnit
  realizationName :=
    `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233175PairStrip.FiniteCertificate.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => total (v n)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233175PairStrip
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit

end FiniteCertificate
end
end Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233175PairStrip
