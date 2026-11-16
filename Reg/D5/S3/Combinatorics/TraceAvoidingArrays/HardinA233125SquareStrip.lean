import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233125SquareStrip
import D5.S3.ConceptDynamics.InformationEscape.DependentFamily
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

/-! Four-slot registrations of the four-column identity, certificate and label sum. -/

open scoped BigOperators

namespace Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233125SquareStrip

open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233125SquareStrip
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
    (1 - 16 * X) * (1 - 144 * X + 3840 * X ^ 2 - 24576 * X ^ 3) *
      (PowerSeries.mk fun n => (R.readout () () n : ℤ)) =
        X * (10 - 704 * X + 14336 * X ^ 2 - 81920 * X ^ 3)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  change (1 - 16 * X) * (1 - 144 * X + 3840 * X ^ 2 - 24576 * X ^ 3) *
      (PowerSeries.mk fun n => ((a n + 1 : ℕ) : ℤ)) =
        X * (10 - 704 * X + 14336 * X ^ 2 - 81920 * X ^ 3) at h
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
  unitName := `Reg.A233125.auditUnit
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
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233125SquareStrip
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
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => Fin 4) (fun _ => ℤ)

def actual : Realization signature :=
  realize signature (fun _ _ k => firstCount k) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ k => firstCount k + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R :=
    (∀ s p, Valid s p → ∀ k, classCount s p k = transfer (boundaryClass s p) k) ∧
    (∀ k, R.readout () () k = ![4, 0, 4, 2] k)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h.2 0
  have ha := finite_certificate.2 0
  change firstCount 0 + 1 = 4 at hb
  change firstCount 0 = 4 at ha
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
  unitName := `Reg.A233125FiniteCertificate.auditUnit
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
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233125SquareStrip
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
  _root_.Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => (Fin 4 → Fin 3) → ℤ) (fun _ => ℤ)

def actual : Realization signature :=
  realize signature (fun _ _ g => ∑ q, g q) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ g => (∑ q, g q) + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ g : (Fin 4 → Fin 3) → ℤ,
    R.readout () () g = ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, ∑ d : Fin 3,
      g ![a, b, c, d]

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h (fun _ => 0)
  change (∑ _q : Fin 4 → Fin 3, (0 : ℤ)) + 1 =
    ∑ _a : Fin 3, ∑ _b : Fin 3, ∑ _c : Fin 3, ∑ _d : Fin 3, (0 : ℤ) at hb
  simpa using hb

def family : Registration arena (type_of% @label_sum) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨label_sum, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), (fun _ => 0), (fun _ => 1), ?_⟩
    change (∑ _q : Fin 4 → Fin 3, (0 : ℤ)) ≠ ∑ _q : Fin 4 → Fin 3, (1 : ℤ)
    norm_num [Fintype.card_fun]

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@label_sum) (Realization signature) Type Unit where
  unitName := `Reg.A233125LabelSum.auditUnit
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
  readout := some (realize signature (fun _ _ g => ∑ q, g q) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233125SquareStrip
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit

end LabelSum

end

end Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233125SquareStrip
