import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233253TriangleStrip
import D5.S3.ConceptDynamics.InformationEscape.DependentFamily
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

/-! Readout registrations for the generating-function identity and its finite certificate. -/

namespace Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233253TriangleStrip

open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233253TriangleStrip
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit PowerSeries

noncomputable section

attribute [local irreducible] a classCount rankCount firstCount firstRank

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ _ n => a n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ n => a n + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R :=
    (1 - 32 * X) * (1 - 480 * X + 18432 * X ^ 2) *
      (PowerSeries.mk fun n => (R.readout () () n : ℤ)) = 4 * X * (9 - 1120 * X + 30720 * X ^ 2)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  change (1 - 32 * X) * (1 - 480 * X + 18432 * X ^ 2) *
      (PowerSeries.mk fun n => ((a n + 1 : ℕ) : ℤ)) = 4 * X * (9 - 1120 * X + 30720 * X ^ 2) at h
  have h0 : a 0 = 0 := by unfold a; decide +kernel
  have hb := congrArg (PowerSeries.coeff 0) h
  simpa [PowerSeries.coeff_mul, h0] using hb

set_option maxRecDepth 100000 in
def family : Registration arena (type_of% @result) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro ⟨⟩
    refine ⟨(), 0, 1, ?_⟩
    change a 0 ≠ a 1
    have h0 : a 0 = 0 := by unfold a; decide +kernel
    intro he
    have h1 : a 1 = 0 := he ▸ h0
    have hh := congrArg (PowerSeries.coeff 1) result
    norm_num [PowerSeries.coeff_mul, Finset.Nat.antidiagonal_succ, h0, h1] at hh
    norm_num [map_ofNat] at hh

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@result) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233253TriangleStrip.auditUnit
  realizationName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233253TriangleStrip.family
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
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233253TriangleStrip
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
      classCount s p true = (if s.2 then 320 + 64 * rank p else 240) ∧
      classCount s p false = (if s.2 then 0 else 32) ∧
      rankCount s p = (if s.2 then 512 + 160 * rank p else 448)) ∧
    R.readout () () true = 28 ∧ R.readout () () false = 8 ∧ firstRank = 44

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h.2.1
  have ha := finite_certificate.2.1
  change firstCount true + 1 = 28 at hb
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
    rw [finite_certificate.2.1, finite_certificate.2.2.1]
    decide

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@finite_certificate) (Realization signature) Type Unit where
  unitName :=
    `Reg.A233253FiniteCertificate.auditUnit
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
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233253TriangleStrip
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
end Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233253TriangleStrip
