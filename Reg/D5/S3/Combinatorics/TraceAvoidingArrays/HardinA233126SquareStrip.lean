import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233126SquareStrip
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233251TriangleStrip
import D5.S3.ConceptDynamics.InformationEscape.DependentFamily
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration
import Mathlib.Tactic.Linarith

/-! Four-slot registration of the literal five-column recurrence. -/

namespace Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233126SquareStrip

open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233126SquareStrip
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

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
  Law R := ∀ n : ℕ,
    (R.readout () () (n + 7) : ℤ) =
      544 * R.readout () () (n + 6) - 82944 * R.readout () () (n + 5) +
        5144576 * R.readout () () (n + 4) - 146800640 * R.readout () () (n + 3) +
        1879048192 * R.readout () () (n + 2) - 8589934592 * R.readout () () (n + 1)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h 0
  have ha := result 0
  change ((a (0 + 7) + 1 : ℕ) : ℤ) =
    544 * ((a (0 + 6) + 1 : ℕ) : ℤ) - 82944 * ((a (0 + 5) + 1 : ℕ) : ℤ) +
      5144576 * ((a (0 + 4) + 1 : ℕ) : ℤ) - 146800640 * ((a (0 + 3) + 1 : ℕ) : ℤ) +
      1879048192 * ((a (0 + 2) + 1 : ℕ) : ℤ) -
        8589934592 * ((a (0 + 1) + 1 : ℕ) : ℤ) at hb
  simp only [Nat.cast_add, Nat.cast_one] at hb
  linarith

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
      simp [a,
        _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233251TriangleStrip.widthLegal]
    have hp : 0 < a 1 := by
      unfold a
      apply Finset.card_pos.mpr
      refine ⟨fun ij => ![0, 1, 0, 1, 0] ij.2, ?_⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by decide +kernel⟩
    omega

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@result) (Realization signature) Type Unit where
  unitName := `Reg.A233126.auditUnit
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
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233126SquareStrip
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
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => Fin 7) (fun _ => ℤ)

def actual : Realization signature :=
  realize signature (fun _ _ k => firstCount k) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ k => firstCount k + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R :=
    (∀ s p, Valid s p → ∀ k, classCount s p k = transfer (boundaryClass s p) k) ∧
    (∀ k, R.readout () () k = ![8, 0, 8, 4, 8, 4, 4] k)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h.2 0
  have ha := finite_certificate.2 0
  change firstCount 0 + 1 = 8 at hb
  change firstCount 0 = 8 at ha
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
  unitName := `Reg.A233126FiniteCertificate.auditUnit
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
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233126SquareStrip
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

end Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233126SquareStrip
