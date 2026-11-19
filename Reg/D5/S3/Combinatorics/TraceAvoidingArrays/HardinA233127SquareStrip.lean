import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233127SquareStrip
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233127Rows
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233251TriangleStrip
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233254TriangleStrip
import D5.S3.ConceptDynamics.InformationEscape.DependentFamily
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration
import Lean.Elab.Tactic.Omega

/-! Four-slot registration of the literal six-column recurrence. -/

namespace Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233127SquareStrip

open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233127SquareStrip
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

attribute [local instance 2000] Pi.instFintype
attribute [local instance 2000]
  _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233251TriangleStrip.widthInstDecidableGood
attribute [local irreducible] a classCount firstCount

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ _ n => a n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ n : ℕ,
    (R.readout () () (n + 9) : ℤ) =
      1984 * (R.readout () () (n + 8) : ℤ) -
      1314816 * (R.readout () () (n + 7) : ℤ) +
      411303936 * (R.readout () () (n + 6) : ℤ) -
      70111985664 * (R.readout () () (n + 5) : ℤ) +
      6893422510080 * (R.readout () () (n + 4) : ℤ) -
      389708152569856 * (R.readout () () (n + 3) : ℤ) +
      11733988091625472 * (R.readout () () (n + 2) : ℤ) -
      145241087982698496 * (R.readout () () (n + 1) : ℤ)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h 0
  change (1 : ℤ) = 1984 * 1 - 1314816 * 1 + 411303936 * 1 - 70111985664 * 1 +
    6893422510080 * 1 - 389708152569856 * 1 + 11733988091625472 * 1 -
    145241087982698496 * 1 at hb
  omega

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
    have hz : a 0 = 0 := by
      unfold a
      decide +kernel
    have hp : 0 < a 1 := by
      unfold a
      apply Finset.card_pos.mpr
      refine ⟨fun ij => ![0, 1, 0, 1, 0, 1] ij.2, ?_⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by decide +kernel⟩
    omega

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@result) (Realization signature) Type Unit where
  unitName := `Reg.A233127.auditUnit
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
  readout := some (realize signature (fun _ _ n => a n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233127SquareStrip
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg", "arg"]
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
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => Fin 11) (fun _ => ℤ)

def actual : Realization signature :=
  realize signature (fun _ _ k => firstCount k) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ k => firstCount k + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R :=
    (∀ s p, Valid s p → ∀ k, classCount s p k = transfer (boundaryClass s p) k) ∧
    (∀ k, R.readout () () k = ![16, 0, 16, 16, 16, 16, 16, 8, 8, 16, 8] k)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h.2 0
  have ha := finite_certificate.2 0
  change firstCount 0 + 1 = 16 at hb
  change firstCount 0 = 16 at ha
  omega

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
  unitName := `Reg.A233127FiniteCertificate.auditUnit
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
  readout := some (realize signature (fun _ _ k => firstCount k) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233127SquareStrip
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

#print axioms audit

end FiniteCertificate

end

end Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233127SquareStrip
