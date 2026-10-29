import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.Mertens.ThetaTailZeroExclusion
import Reg.Support.SingleDependentReadout

/-! The actual theta-tail observation and the full conditional zero-exclusion law. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Weil.Mertens.ThetaTailZeroExclusion

open Set MeasureTheory Filter
open scoped Topology
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Weil.Mertens.ActualThetaTailLaplace
open _root_.D5.S3.Weil.Mertens.ThetaTailZeroExclusion
open LeanInformationAudit

noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ × ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ u => (f u, u)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ u => (f u + 1, u)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R :=
    (∀ u : ℝ, (R.readout () () u).1 = f u) ∧
    (∀ {b C : ℝ}, 0 < b → b < 1 / 2 → 0 ≤ C →
      (∀ᶠ u : ℝ in atTop,
        (R.readout () () u).1 ≤ C * Real.exp (-b * u)) →
      ∀ ρ : ℂ, 1 - b < ρ.re → riemannZeta ρ ≠ 0)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have h0 := h.1 0
  norm_num [rejected, realize] at h0

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have hsnd := congrArg Prod.snd h
  norm_num [actual, realize] at hsnd

private theorem actual_law : arena.Law actual := by
  constructor
  · intro u
    rfl
  · intro b C hb hb2 hC hbound
    apply actual_theta_tail_exponential_zero_exclusion hb hb2 hC
    simpa [actual, realize] using hbound

def family : Registration arena
    (type_of% (@actual_theta_tail_exponential_zero_exclusion)) where
  actual := actual
  bridge := by
    constructor
    · intro h
      refine ⟨?_, ?_⟩
      · intro u
        rfl
      · intro b C hb hb2 hC hbound
        apply h hb hb2 hC
        simpa [actual, realize] using hbound
    · intro h b C hb hb2 hC hbound
      apply h.2 hb hb2 hC
      simpa [actual, realize] using hbound
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@actual_theta_tail_exponential_zero_exclusion)
    (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Weil.Mertens.ThetaTailZeroExclusion.actual_theta_tail_exponential_zero_exclusion.__information_unit
  realizationName := `Reg.D5.S3.Weil.Mertens.ThetaTailZeroExclusion.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ u => (f u, u)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Mertens.ThetaTailZeroExclusion
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "domain",
        "fn", "arg", "body", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms registration

end
end Reg.D5.S3.Weil.Mertens.ThetaTailZeroExclusion
