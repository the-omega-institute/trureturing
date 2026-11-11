import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233126SquareStrip
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233251TriangleStrip
import D5.S3.ConceptDynamics.InformationEscape.DependentFamily
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration
import Lean.Elab.Tactic.Omega

/-! Four-slot registration of the literal five-column recurrence. -/

namespace Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233126SquareStrip

open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233126SquareStrip
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233254TriangleStrip (Valid)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

open scoped BigOperators

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
    (R.readout () () (n + 7) : ℤ) =
      544 * (R.readout () () (n + 6) : ℤ) - 82944 * (R.readout () () (n + 5) : ℤ) +
        5144576 * (R.readout () () (n + 4) : ℤ) -
        146800640 * (R.readout () () (n + 3) : ℤ) +
        1879048192 * (R.readout () () (n + 2) : ℤ) -
        8589934592 * (R.readout () () (n + 1) : ℤ)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h 0
  change (1 : ℤ) = 544 * 1 - 82944 * 1 + 5144576 * 1 - 146800640 * 1 +
    1879048192 * 1 - 8589934592 * 1 at hb
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

namespace LabelSum

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ((Fin 5 → Fin 3) → ℤ)
    (fun _ => Fin 5 → Fin 3) (fun _ => ℤ)

def actual : Realization signature :=
  realize signature (fun _ g q => g q) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ g q => g q + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ g : (Fin 5 → Fin 3) → ℤ,
    (∑ q, R.readout () g q) = ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, ∑ d : Fin 3, ∑ e : Fin 3,
      g ![a, b, c, d, e]

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h (fun _ => 0)
  simpa [rejected, realize] using hb

def family : Registration arena (type_of% @label_sum) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨label_sum, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(fun q => ((q 0).val : ℤ)), (fun _ => 0), (fun _ => 1), ?_⟩
    change (0 : ℤ) ≠ 1
    decide

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@label_sum) (Realization signature) Type Unit where
  unitName := `Reg.A233126LabelSum.auditUnit
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
  readout := some (realize signature (fun _ g q => g q) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233126SquareStrip
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "fn", "arg", "arg", "body", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit

end LabelSum

namespace InitialValid

open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233253TriangleStrip (Row rowLegal)
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233175PairStrip (good finish)

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Row (fun _ => Fin 5 → Fin 3) (fun _ => Bool)

def actual : Realization signature :=
  realize signature (fun _ c p =>
    @decide (Valid (finish (false, false) c) p) (by unfold Valid; infer_instance))
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => false) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ c : Row, c 0 = 0 ∧ rowLegal c ∧ good (false, false) c →
    R.readout () c (labels c) = true

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h ![0, 1, 0, 1, 0] (by decide +kernel)
  change false = true at hb
  cases hb

def family : Registration arena (type_of% @initial_valid) where
  actual := actual
  bridge := by simp [arena, actual, realize]
  variation := ⟨by simpa [arena, actual, realize] using initial_valid,
    rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨![0, 1, 0, 1, 0], (fun _ => 0), ![0, 1, 0, 1, 0], ?_⟩
    have ht : Valid (finish (false, false) ![0, 1, 0, 1, 0]) ![0, 1, 0, 1, 0] := by
      unfold Valid
      decide +kernel
    have hf : ¬ Valid (finish (false, false) ![0, 1, 0, 1, 0])
        (fun _ : Fin 5 => (0 : Fin 3)) := by
      unfold Valid
      decide +kernel
    simp [actual, realize, ht, hf]

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@initial_valid) (Realization signature) Type Unit where
  unitName := `Reg.A233126InitialValid.auditUnit
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
  readout := some (realize signature (fun _ c p =>
    @decide (Valid (finish (false, false) c) p) (by unfold Valid; infer_instance))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233126SquareStrip
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end InitialValid

namespace RowValid

open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233253TriangleStrip (Row rowLegal)
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233175PairStrip (Seen good finish)

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (Σ _ : Seen, Row) (fun _ => Fin 5 → Fin 3) (fun _ => Bool)

def actual : Realization signature :=
  realize signature (fun _ sc p =>
    @decide (Valid (finish sc.1 sc.2) p) (by unfold Valid; infer_instance))
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => false) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ s : Seen, ∀ c : Row, s.1 = true → rowLegal c → good s c →
    R.readout () ⟨s, c⟩ (labels c) = true

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h (true, false) ![0, 1, 0, 1, 0]
    (by rfl) (by decide +kernel) (by decide +kernel)
  change false = true at hb
  cases hb

def family : Registration arena (type_of% @row_valid) where
  actual := actual
  bridge := by simp [arena, actual, realize]
  variation := ⟨by simpa [arena, actual, realize] using row_valid,
    rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨⟨(true, false), ![0, 1, 0, 1, 0]⟩, (fun _ => 0), ![0, 1, 0, 1, 0], ?_⟩
    have ht : Valid (finish (true, false) ![0, 1, 0, 1, 0]) ![0, 1, 0, 1, 0] := by
      unfold Valid
      decide +kernel
    have hf : ¬ Valid (finish (true, false) ![0, 1, 0, 1, 0])
        (fun _ : Fin 5 => (0 : Fin 3)) := by
      unfold Valid
      decide +kernel
    simp [actual, realize, ht, hf]

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@row_valid) (Realization signature) Type Unit where
  unitName := `Reg.A233126RowValid.auditUnit
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
  readout := some (realize signature (fun _ sc p =>
    @decide (Valid (finish sc.1 sc.2) p) (by unfold Valid; infer_instance))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233126SquareStrip
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end RowValid


end

end Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233126SquareStrip
