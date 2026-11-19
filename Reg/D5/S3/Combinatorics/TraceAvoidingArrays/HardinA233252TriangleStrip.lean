import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233252TriangleStrip
import D5.S3.ConceptDynamics.InformationEscape.DependentFamily
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

/-! Readout registrations for the three identities and the finite certificate. -/

namespace Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233252TriangleStrip

open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233252TriangleStrip
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233124SquareStrip
  (Valid boundaryClass)
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
    (∀ n : ℕ, 1 ≤ n →
      (R.readout () () (n + 2) : ℤ) = 160 * R.readout () () (n + 1) -
        2304 * R.readout () () n) ∧
    ((1 - 16 * X) * (1 - 144 * X) *
      (PowerSeries.mk fun n => (R.readout () () n : ℤ)) = 2 * X * (5 - 208 * X)) ∧
    (∀ n : ℕ, 9 * (R.readout () () (n + 1) : ℤ) =
      2 ^ (4 * n + 1) * (4 * 9 ^ (n + 1) + 9))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h.2.2 0
  change 9 * ((a 1 + 1 : ℕ) : ℤ) = 2 ^ (1 : ℕ) * (4 * 9 ^ (1 : ℕ) + 9) at hh
  have ha : a 1 = 10 := by
    have h' := _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233252TriangleStrip.result.2.2 0
    norm_num at h'
    omega
  rw [ha] at hh
  norm_num at hh

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
    have h0 : a 0 = 0 := by
      simp [a, _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233251TriangleStrip.widthLegal]
    have h1 := _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233252TriangleStrip.result.2.2 0
    norm_num at h1
    omega

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@result) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233252TriangleStrip.auditUnit
  realizationName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233252TriangleStrip.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some actual
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233252TriangleStrip
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

abbrev certificateSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => Fin 3) (fun _ => ℤ)

def certificateActual : Realization certificateSignature :=
  realize certificateSignature (fun _ _ k => firstCount k) (fun e => nomatch e)

def certificateRejected : Realization certificateSignature :=
  realize certificateSignature (fun _ _ k => firstCount k + 1) (fun e => nomatch e)

abbrev certificateArena : Arena where
  signature := certificateSignature
  Law R :=
    (∀ s p, Valid s p → ∀ k,
      classCount s p k = transfer (boundaryClass s p) k) ∧
    (∀ k, R.readout () () k = ![4, 2, 4] k)

private theorem certificateRejectedLaw : ¬ certificateArena.Law certificateRejected := by
  intro h
  have hb := h.2 0
  have ha := _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233252TriangleStrip.result
  change firstCount 0 + 1 = ![4, 2, 4] 0 at hb
  have hf := _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233252TriangleStrip.finite_certificate.2 0
  rw [hf] at hb
  norm_num at hb

def certificateFamily : Registration certificateArena (type_of% @finite_certificate) where
  actual := certificateActual
  bridge := Iff.rfl
  variation := ⟨finite_certificate, certificateRejected, certificateRejectedLaw⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    certificateArena.Law certificateActual certificateRejected certificateRejectedLaw
  dependence := by
    intro k
    refine ⟨(), 0, 1, ?_⟩
    change firstCount 0 ≠ firstCount 1
    rw [finite_certificate.2 0, finite_certificate.2 1]
    decide

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@finite_certificate) (Realization certificateSignature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233252TriangleStrip.certificateAuditUnit
  realizationName := ``certificateFamily
  realizationSource := none
  generated := false
  arena := .source ⟨certificateArena⟩
  objectArena := .source ⟨certificateArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source certificateArena ⟨certificateFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some certificateActual
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233252TriangleStrip
    definition := none
    coordinates := #[]
    readouts := #[] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit

end FiniteCertificate
end
end Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233252TriangleStrip
