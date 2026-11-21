import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.Mertens.IntegratedExplicit.QuarticSampling
import Reg.Support.SingleDependentReadout

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open Filter LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Arith.Robin.CompleteMertensPeak (U)
open _root_.D5.S3.Weil.Mertens.IntegratedExplicit.QuarticSampling

namespace Reg.D5.S3.Weil.Mertens.IntegratedExplicit.QuarticSampling

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ x => U x) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law V := RiemannHypothesis ↔ ∀ᶠ n : ℕ in atTop, V.readout () () ((n : ℝ)^4) < (n : ℝ)^2

/-- The two possible readouts make the sample test uniformly false or true.
Classical case distinction selects the readout contradicting the fixed RH proposition. -/
private def rejected : Realization signature := by
  classical
  exact realize signature (fun _ _ x => if RiemannHypothesis then x+1 else -1) (fun e => nomatch e)

private theorem rejected_law : ¬ arena.Law rejected := by
  classical
  change ¬(RiemannHypothesis ↔ ∀ᶠ n : ℕ in atTop,
    (if RiemannHypothesis then (n : ℝ)^4+1 else -1) < (n : ℝ)^2)
  intro h
  by_cases hr : RiemannHypothesis
  · obtain ⟨n, hn⟩ := (h.mp hr).exists
    simp [hr] at hn
    nlinarith [sq_nonneg ((n : ℝ)^2-1/2)]
  · apply hr
    apply h.mpr
    filter_upwards with n
    simp only [show ¬ RiemannHypothesis from hr, ↓reduceIte]
    linarith [sq_nonneg (n : ℝ)]

def evidence : Registration arena (type_of% @rh_iff_eventually_quartic_samples) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨rh_iff_eventually_quartic_samples, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro role
    refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
    change U 0 ≠ U 1
    have h0 : U 0 = 0 := by simp [U, Chebyshev.psi]
    have h1 : U 1 = 1+Real.eulerMascheroniConstant := by simp [U, Chebyshev.psi]
    rw [h0, h1]
    linarith [Real.one_half_lt_eulerMascheroniConstant]

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@rh_iff_eventually_quartic_samples) (Realization signature) Unit Unit where
  unitName := `D5.S3.Weil.Mertens.IntegratedExplicit.QuarticSampling.rh_iff_eventually_quartic_samples.__information_unit
  realizationName := `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.QuarticSampling.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => U x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Mertens.IntegratedExplicit.QuarticSampling
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg", "fn", "arg", "body", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms registration


namespace Window

def arena : Arena where
  signature := signature
  Law V := ∀ {b : ℝ}, 1 < b → (RiemannHypothesis ↔ ∀ κ : ℝ, 0 < κ →
    ∃ᶠ Y : ℝ in atTop, ∀ t, WindowSample Y (Y ^ b) t →
      V.readout () () t ≤ t ^ ((1 : ℝ) / 2 + κ))

private theorem rejected_law : ¬ arena.Law rejected := by
  classical
  intro h
  have h2 := h (b := 2) (by norm_num)
  by_cases rh : RiemannHypothesis
  · obtain ⟨Y, hw, hY⟩ := ((h2.mp rh (1/2) (by norm_num)).and_eventually
      (eventually_ge_atTop (2 : ℝ))).exists
    have hsample : WindowSample Y (Y ^ (2 : ℝ)) Y := by
      exact ⟨⟨le_rfl, Real.self_le_rpow_of_one_le (by linarith) (by norm_num)⟩, Or.inl rfl⟩
    have hbad := hw Y hsample
    change (if RiemannHypothesis then Y+1 else -1) ≤ Y ^ ((1 : ℝ)/2+1/2) at hbad
    simp only [rh, ↓reduceIte, show (1 : ℝ)/2+1/2 = 1 by norm_num, Real.rpow_one] at hbad
    linarith
  · apply rh
    apply h2.mpr
    intro κ _
    apply Filter.Eventually.frequently
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with Y hY
    intro t ht
    change (if RiemannHypothesis then t+1 else -1) ≤ _
    simp only [rh, ↓reduceIte]
    exact (by norm_num : (-1 : ℝ) ≤ 0).trans
      (Real.rpow_nonneg ((by norm_num : (0 : ℝ) ≤ 2).trans (hY.trans ht.1.1)) _)

def evidence : Registration arena (type_of% @rh_iff_quartic_power_windows) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@rh_iff_quartic_power_windows, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := Reg.D5.S3.Weil.Mertens.IntegratedExplicit.QuarticSampling.evidence.dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@rh_iff_quartic_power_windows) (Realization signature) Unit Unit where
  unitName := `D5.S3.Weil.Mertens.IntegratedExplicit.QuarticSampling.rh_iff_quartic_power_windows.__information_unit
  realizationName := `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.QuarticSampling.Window.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => U x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Mertens.IntegratedExplicit.QuarticSampling
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "body", "body", "fn", "arg",
        "body", "body", "body", "fn", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Window

end Reg.D5.S3.Weil.Mertens.IntegratedExplicit.QuarticSampling
