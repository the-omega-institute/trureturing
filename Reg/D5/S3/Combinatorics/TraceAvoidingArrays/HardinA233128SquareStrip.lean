import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233128SquareStrip
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233128Rows
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233175PairStrip
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255PairTransfer
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233251TriangleStrip
import D5.S3.ConceptDynamics.InformationEscape.DependentFamily
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration
import Lean.Elab.Tactic.Omega

/-! Four-slot registration of the literal seven-column recurrence. -/

namespace Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233128SquareStrip

open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233128SquareStrip
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
    (R.readout () () (n + 15) : ℤ) =
      7168 * (R.readout () () (n + 14) : ℤ)
      - 19070976 * (R.readout () () (n + 13) : ℤ)
      + 26086473728 * (R.readout () () (n + 12) : ℤ)
      - 21081846972416 * (R.readout () () (n + 11) : ℤ)
      + 10809917287956480 * (R.readout () () (n + 10) : ℤ)
      - 3649692508960587776 * (R.readout () () (n + 9) : ℤ)
      + 824336623994081902592 * (R.readout () () (n + 8) : ℤ)
      - 124561639357723747287040 * (R.readout () () (n + 7) : ℤ)
      + 12414326720213201465638912 * (R.readout () () (n + 6) : ℤ)
      - 792885332473813431379558400 * (R.readout () () (n + 5) : ℤ)
      + 31062140009178282014900486144 * (R.readout () () (n + 4) : ℤ)
      - 704387882353381376417601683456 * (R.readout () () (n + 3) : ℤ)
      + 8398185226512019784915658735616 * (R.readout () () (n + 2) : ℤ)
      - 40564819207303340847894502572032 * (R.readout () () (n + 1) : ℤ)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h 0
  change (1 : ℤ) =
    7168 * 1
    - 19070976 * 1
    + 26086473728 * 1
    - 21081846972416 * 1
    + 10809917287956480 * 1
    - 3649692508960587776 * 1
    + 824336623994081902592 * 1
    - 124561639357723747287040 * 1
    + 12414326720213201465638912 * 1
    - 792885332473813431379558400 * 1
    + 31062140009178282014900486144 * 1
    - 704387882353381376417601683456 * 1
    + 8398185226512019784915658735616 * 1
    - 40564819207303340847894502572032 * 1 at hb
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
      refine ⟨fun ij => ![0, 1, 0, 1, 0, 1, 0] ij.2, ?_⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by decide +kernel⟩
    omega

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@result) (Realization signature) Type Unit where
  unitName := `Reg.A233128.auditUnit
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
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233128SquareStrip
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
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => Fin 21) (fun _ => ℤ)

def actual : Realization signature :=
  realize signature (fun _ _ k => firstCount k) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ k => firstCount k + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R :=
    (∀ s p, Valid s p → ∀ k, classCount s p k = transfer (boundaryClass s p) k) ∧
    (∀ k, R.readout () () k = ![32, 0, 32, 32, 32, 16, 32, 32, 32, 32, 16, 32, 32, 16,
        32, 16, 32, 16, 32, 16, 16] k)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h.2 0
  have ha := finite_certificate.2 0
  change firstCount 0 + 1 = 32 at hb
  change firstCount 0 = 32 at ha
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
  unitName := `Reg.A233128FiniteCertificate.auditUnit
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
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233128SquareStrip
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

end Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233128SquareStrip
