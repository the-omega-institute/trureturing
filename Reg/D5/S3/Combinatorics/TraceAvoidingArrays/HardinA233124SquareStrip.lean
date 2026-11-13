import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233124SquareStrip
import D5.S3.ConceptDynamics.InformationEscape.DependentFamily
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

/-! Readout registrations for the generating-function identity and its finite certificate. -/

namespace Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233124SquareStrip

open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233124SquareStrip
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
    (1 - 8 * X) * (1 - 40 * X + 128 * X ^ 2) *
      (PowerSeries.mk fun n => (R.readout () () n : ℤ)) = X * (3 - 64 * X + 192 * X ^ 2)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  change (1 - 8 * X) * (1 - 40 * X + 128 * X ^ 2) *
      (PowerSeries.mk fun n => ((a n + 1 : ℕ) : ℤ)) = X * (3 - 64 * X + 192 * X ^ 2) at h
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
    intro h
    have h0 := congrArg (PowerSeries.coeff 0) result
    have h1 := congrArg (PowerSeries.coeff 1) result
    have hz : (a 0 : ℤ) = 0 := by
      simpa [PowerSeries.coeff_mul] using h0
    have hn : a 0 = 0 := by exact_mod_cast hz
    have ho : (a 1 : ℤ) = 3 := by
      simpa [PowerSeries.coeff_mul, Finset.Nat.antidiagonal_succ, hn, map_ofNat] using h1
    rw [hn] at h
    exact (by norm_num : (0 : ℤ) ≠ 3) ((congrArg (fun n : ℕ => (n : ℤ)) h).trans ho)

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@result) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233124SquareStrip.auditUnit
  realizationName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233124SquareStrip.family
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
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233124SquareStrip
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


namespace FiniteCertificate

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => Fin 3) (fun _ => ℤ)

def actual : Realization signature :=
  realize signature (fun _ _ n => firstCount n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ n => firstCount n + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R :=
    (∀ s p, Valid s p → ∀ k, classCount s p k = transfer (boundaryClass s p) k) ∧
    (∀ k, R.readout () () k = ![2, 0, 1] k)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h.2 0
  have ha := finite_certificate.2 0
  change firstCount 0 + 1 = 2 at hb
  change firstCount 0 = 2 at ha
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
    change firstCount 0 ≠ firstCount 1
    rw [finite_certificate.2 0, finite_certificate.2 1]
    decide

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@finite_certificate) (Realization signature) Type Unit where
  unitName :=
    Lean.Name.str
      `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233124SquareStrip.FiniteCertificate
      "auditUnit"
  realizationName :=
    `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233124SquareStrip.FiniteCertificate.family
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
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233124SquareStrip
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]


end FiniteCertificate
end
end Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233124SquareStrip
