import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Abundancy.ZelinskyDeficientCore
import Reg.Support.SingleDependentReadout

/-! The upper threshold observation in the construction of deficient cores. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open LeanInformationAudit Real Finset
open scoped BigOperators
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Arith.Abundancy.ZelinskyDeficientCore

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ t => exp t) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ B : ℕ,
    ∃ K : ℝ, 0 < K ∧ ∃ T : ℝ, ∀ t : ℝ, T ≤ t →
      ∃ s : Finset ℕ,
        let h := ∏ p ∈ s, (1 + 1 / (p : ℝ))
        let a := h / (2 - h)
        (∀ p ∈ s, p.Prime ∧ B < p) ∧ h < 2 ∧
          exp t ≤ a ∧ a ≤ 3 * R.readout () () t ∧
          (∀ p ∈ s, (p : ℝ) < 2 * a) ∧
          (∑ p ∈ s, log (p : ℝ)) ≤ K * t ^ 2

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨K, hK, T, hT⟩ := h 0
  obtain ⟨s, hs⟩ := hT T le_rfl
  have hlo := hs.2.2.1
  have hhi := hs.2.2.2.1
  change _ ≤ 3 * (0 : ℝ) at hhi
  linarith [exp_pos T]

def family : Registration arena
    (type_of% @_root_.D5.S3.Arith.Abundancy.ZelinskyDeficientCore.result) where
  actual := actual
  bridge := Iff.rfl
  variation :=
    ⟨@_root_.D5.S3.Arith.Abundancy.ZelinskyDeficientCore.result,
      rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro role
    refine ⟨(), 0, 1, ?_⟩
    change exp (0 : ℝ) ≠ exp 1
    exact Real.exp_injective.ne zero_ne_one

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.Arith.Abundancy.ZelinskyDeficientCore.result)
    (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Abundancy.ZelinskyDeficientCore.result.audit
  realizationName := `Reg.D5.S3.Arith.Abundancy.ZelinskyDeficientCore.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℝ
  sourceSelection := some {
    owner := `D5.S3.Arith.Abundancy.ZelinskyDeficientCore
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "arg", "body", "arg", "arg", "body", "body", "body",
        "arg", "body", "body", "body", "arg", "arg", "arg", "fn", "arg",
        "arg", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Arith.Abundancy.ZelinskyDeficientCore
