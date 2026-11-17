import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233254TriangleStrip
import D5.S3.ConceptDynamics.InformationEscape.DependentFamily
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

/-! Readout registrations for the generating-function identity and its finite certificate. -/

namespace Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233254TriangleStrip

open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233254TriangleStrip
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit PowerSeries

noncomputable section

attribute [local irreducible] a classCount momentCount firstCount firstMoment

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ _ n => a n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ n => a n + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R :=
    (1 - 64 * X) * (1 - 1600 * X + 368640 * X ^ 2 - 21233664 * X ^ 3) *
      (PowerSeries.mk fun n => (R.readout () () n : ℤ)) =
        8 * X * (17 - 7488 * X + 974848 * X ^ 2 - 40108032 * X ^ 3)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  change (1 - 64 * X) * (1 - 1600 * X + 368640 * X ^ 2 - 21233664 * X ^ 3) *
      (PowerSeries.mk fun n => ((a n + 1 : ℕ) : ℤ)) =
        8 * X * (17 - 7488 * X + 974848 * X ^ 2 - 40108032 * X ^ 3) at h
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
  unitName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233254TriangleStrip.auditUnit
  realizationName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233254TriangleStrip.family
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
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233254TriangleStrip
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
      classCount s p true = (if s.2 then 64 * moment p 1 else 800) ∧
      classCount s p false = (if s.2 then 0 else 64) ∧
      ∀ i : Fin 3, momentCount s p i.succ =
        (if s.2 then 64 * ![moment p 2, moment p 3,
          81 * moment p 1 - 90 * moment p 2 + 25 * moment p 3] i
        else ![17216, 360576, 7530048] i)) ∧
    R.readout () () true = 120 ∧ R.readout () () false = 16 ∧
      ∀ i : Fin 3, firstMoment i.succ = ![2384, 49344, 1028832] i

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h.2.1
  have ha := finite_certificate.2.1
  change firstCount true + 1 = 120 at hb
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
    `Reg.A233254FiniteCertificate.auditUnit
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
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233254TriangleStrip
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
namespace SumRows

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℕ
    (fun m => (Fin 6 → Fin m) → ℤ) (fun _ => ℤ)

def actual : Realization signature :=
  realize signature (fun _ _ f => ∑ c, f c) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ f => (∑ c, f c) + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {m : ℕ} (f : (Fin 6 → Fin m) → ℤ), R.readout () m f =
    ∑ a : Fin m, ∑ b : Fin m, ∑ c : Fin m, ∑ d : Fin m, ∑ e : Fin m,
      ∑ g : Fin m, f ![a, b, c, d, e, g]

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h (m := 0) (fun _ => 0)
  change (∑ _ : Fin 6 → Fin 0, (0 : ℤ)) + 1 = _ at hb
  simp at hb

def family : Registration arena (type_of% @sum_rows) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@sum_rows, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨1, (fun _ => 0), (fun _ => 1), ?_⟩
    change (∑ _ : Fin 6 → Fin 1, (0 : ℤ)) ≠ ∑ _ : Fin 6 → Fin 1, (1 : ℤ)
    decide +kernel

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@sum_rows) (Realization signature) Type Unit where
  unitName := `Reg.A233254SumRows.auditUnit
  realizationName := ``family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ f => ∑ c, f c) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233254TriangleStrip
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end SumRows

end
end Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233254TriangleStrip
