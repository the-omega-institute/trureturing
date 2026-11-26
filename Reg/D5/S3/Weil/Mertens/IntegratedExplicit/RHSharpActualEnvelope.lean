import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.Mertens.IntegratedExplicit.RHSharpActualEnvelope
import Reg.Support.DependentFamily
import Reg.Support.SingleDependentReadout

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Filter Set
open Real
open scoped Topology
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open _root_.D5.S3.Weil.Mertens.IntegratedExplicit.RHSharpActualEnvelope
open _root_.D5.S3.Weil.Mertens.IntegratedExplicit (actualH)
open _root_.D5.S3.Arith.Robin.CompleteMertensPeak (U)
open _root_.D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds

namespace Reg.D5.S3.Weil.Mertens.IntegratedExplicit.RHSharpActualEnvelope

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ x => G x) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ hRH : RiemannHypothesis,
    (∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ y : ℝ in atTop, |V.readout () () y| < firstLiMass + epsilon) ∧
    (∀ epsilon : ℝ, 0 < epsilon → ∀ Y : ℝ,
      ∃ n : ℕ, Y ≤ (n : ℝ) ∧ |V.readout () () (n : ℝ) - firstLiMass| < epsilon)

private theorem actual_law : arena.Law actual := by
  exact @actual_G_control

private theorem source_bridge :
    (type_of% (@actual_G_control)) ↔ arena.Law actual := Iff.rfl

/- A Contract.Registration requires a lawful enrolled-template readout,
   whole-family variation, sensitivity, observational dependence, sourceSelection,
   and current binding evidence. In particular, refuting the entire conditional
   law for a rejected family entails RH: without RH this universal implication
   holds for every family. No extra anchor equality is added to the source law. -/

private def residualScale (y : ℝ) : ℝ := exp (-y / 2)
private def residualSize : ℝ := log (2 * π)
private def zeroReadout (y : ℝ) : ℝ := residualScale y * (actualH y).re

def residualArena : Arena where
  signature := signature
  Law V := ∀ {y : ℝ}, 0 ≤ y →
    |V.readout () () y - zeroReadout y| < residualScale y * residualSize

private def residualChanged : Realization signature :=
  realize signature (fun _ _ y => zeroReadout y + residualScale y * residualSize)
    (fun e => nomatch e)

private theorem residualChanged_fails : ¬ residualArena.Law residualChanged := by
  intro h
  have h0 := h (y := 0) le_rfl
  change |zeroReadout 0 + residualScale 0 * residualSize - zeroReadout 0| <
    residualScale 0 * residualSize at h0
  rw [add_sub_cancel_left] at h0
  exact (not_lt_of_ge (le_abs_self _)) h0

private theorem G_nonpositive {y : ℝ} (hy : y ≤ 0) :
    G y = exp (y / 2) * (1 + eulerMascheroniConstant - y) := by
  have h : exp y ≤ 1 := exp_le_one_iff.mpr hy
  have hfloor : ⌊exp y⌋₊ ≤ 1 := by simpa using Nat.floor_mono h
  have hs : ∑ n ∈ Finset.Ioc 0 ⌊exp y⌋₊,
      ArithmeticFunction.vonMangoldt n / (n : ℝ) = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    obtain ⟨hn, hn'⟩ := Finset.mem_Ioc.mp hn
    have : n = 1 := by omega
    simp [this]
  rw [G, U, hs, Chebyshev.psi_eq_zero_of_le_one h, log_exp, mul_zero, sub_zero]
  calc
    _ = (exp (-y / 2) * exp y) * (1 + eulerMascheroniConstant - y) := by ring
    _ = _ := by rw [← exp_add, show -y / 2 + y = y / 2 by ring]

private theorem residual_dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨(), 0, -2 * log 4, ?_⟩
  change G 0 ≠ G (-2 * log 4)
  have hl : 0 ≤ log (4 : ℝ) := log_nonneg (by norm_num)
  have hlog : log (4 : ℝ) < 2 := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num, log_mul (by norm_num) (by norm_num)]
    linarith [log_two_lt_d9]
  rw [G_nonpositive le_rfl, G_nonpositive (by linarith),
    show (-2 * log (4 : ℝ)) / 2 = -log 4 by ring, exp_neg,
    exp_log (by norm_num : (0 : ℝ) < 4)]
  norm_num
  linarith [one_half_lt_eulerMascheroniConstant]

def residualEvidence : Registration residualArena (type_of% @abs_G_sub_normalized_actualH_le) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@abs_G_sub_normalized_actualH_le, residualChanged, residualChanged_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    residualArena.Law actual residualChanged residualChanged_fails
  dependence := residual_dependence

def residualRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@abs_G_sub_normalized_actualH_le) (Realization signature) Unit Unit where
  unitName := .str
    `D5.S3.Weil.Mertens.IntegratedExplicit.RHSharpActualEnvelope.abs_G_sub_normalized_actualH_le
    "__information_unit"
  realizationName :=
    `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.RHSharpActualEnvelope.residualEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨residualArena⟩
  objectArena := .source ⟨residualArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source residualArena ⟨residualEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ y => G y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Mertens.IntegratedExplicit.RHSharpActualEnvelope
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Weil.Mertens.IntegratedExplicit.RHSharpActualEnvelope
