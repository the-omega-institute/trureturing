import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.Laplace.EulerPoleObstruction
import Reg.Support.SingleDependentReadout

noncomputable section
open MeasureTheory Set Complex
open _root_.D5.S3.Analytic.Laplace.EulerPoleObstruction
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Analytic.Laplace.EulerPoleObstruction

namespace FiniteHead
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ → ℂ) (fun _ => Prop)
def actual : Realization signature :=
  realize signature (fun _ _ F => Differentiable ℂ F) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law Q := ∀ {g : ℝ → ℝ} {U V : ℝ}, IntegrableOn g (Ioc U V) →
    Q.readout () () (finiteHead g U V)
private theorem rejected_fails : ¬ arena.Law rejected := by
  intro h
  exact h (g := fun _ => 0) (U := 0) (V := 0) (by simp)
private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (fun _ : ℂ => (0 : ℂ)), (fun z : ℂ => z⁻¹), ?_⟩
  intro he
  have hzero : Differentiable ℂ (fun _ : ℂ => (0 : ℂ)) := differentiable_const _
  have hinv : Differentiable ℂ (fun z : ℂ => z⁻¹) := by
    change Differentiable ℂ (fun _ : ℂ => (0 : ℂ)) =
      Differentiable ℂ (fun z : ℂ => z⁻¹) at he
    rw [← he]
    exact hzero
  exact (differentiableAt_inv_iff.mp (hinv 0)) rfl
def evidence : Registration arena (type_of% @finiteHead_entire) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@finiteHead_entire, rejected, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_fails
  dependence := actual_dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@finiteHead_entire) (Realization signature) Unit Unit where
  unitName := `D5.S3.Analytic.Laplace.EulerPoleObstruction.finiteHead_entire.audit
  realizationName := `Reg.D5.S3.Analytic.Laplace.EulerPoleObstruction.FiniteHead.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ F => Differentiable ℂ F) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Laplace.EulerPoleObstruction
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end FiniteHead

namespace TailAnalytic
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ → ℂ)
    (fun _ => Set ℂ → Prop)
def actual : Realization signature :=
  realize signature (fun _ _ F s => AnalyticOnNhd ℂ F s) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law Q := ∀ {g : ℝ → ℝ} {U : ℝ}, IntegrableOn g (Ioi U) → 0 ≤ U →
    Q.readout () () (fun z : ℂ => ∫ u in Ioi U, kernel g z u) {z | 0 < z.re}
private theorem rejected_fails : ¬ arena.Law rejected := by
  intro h
  exact h (g := fun _ => 0) (U := 0) (by simp) le_rfl
private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (fun _ : ℂ => (0 : ℂ)), (fun z : ℂ => z⁻¹), ?_⟩
  intro he
  have he' : AnalyticOnNhd ℂ (fun _ : ℂ => (0 : ℂ)) univ =
      AnalyticOnNhd ℂ (fun z : ℂ => z⁻¹) univ := congrFun he univ
  have hi : AnalyticOnNhd ℂ (fun z : ℂ => z⁻¹) univ := by
    rw [← he']
    exact analyticOnNhd_const
  exact (differentiableAt_inv_iff.mp (hi 0 (mem_univ 0)).differentiableAt) rfl
def evidence : Registration arena (type_of% @tail_analytic) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@tail_analytic, rejected, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_fails
  dependence := actual_dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@tail_analytic) (Realization signature) Unit Unit where
  unitName := `D5.S3.Analytic.Laplace.EulerPoleObstruction.tail_analytic.audit
  realizationName := `Reg.D5.S3.Analytic.Laplace.EulerPoleObstruction.TailAnalytic.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ F s => AnalyticOnNhd ℂ F s) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Laplace.EulerPoleObstruction
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end TailAnalytic

namespace Cutoff
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ) (fun _ => ℂ)
def actual : Realization signature :=
  realize signature (fun _ _ z => z) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law Q := ∀ {g : ℝ → ℝ} {U V : ℝ}, IntegrableOn g (Ioi U) → 0 ≤ U → U ≤ V →
    ∀ {z : ℂ}, 0 < z.re →
      Q.readout () () (∫ u in Ioi V, kernel g z u) =
        (∫ u in Ioi U, kernel g z u) - finiteHead g U V z
private theorem rejected_fails : ¬ arena.Law rejected := by
  intro h
  have hh := h (g := fun _ => 0) (U := 0) (V := 0) (by simp) le_rfl le_rfl
    (z := 1) (by norm_num)
  simpa [rejected, realize, kernel, finiteHead] using hh
private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 1, zero_ne_one⟩
def evidence : Registration arena (type_of% @tail_cutoff) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@tail_cutoff, rejected, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_fails
  dependence := actual_dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@tail_cutoff) (Realization signature) Unit Unit where
  unitName := `D5.S3.Analytic.Laplace.EulerPoleObstruction.tail_cutoff.audit
  realizationName := `Reg.D5.S3.Analytic.Laplace.EulerPoleObstruction.Cutoff.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z => z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Laplace.EulerPoleObstruction
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Cutoff

end Reg.D5.S3.Analytic.Laplace.EulerPoleObstruction

/-! Full source laws for the original infinite source domains. The actual
bridges and observation dependence are proved. A rejected lawful source family
requires genuine pole data; no such instance is supplied as audit evidence. -/

noncomputable section
open MeasureTheory Filter Set Complex
open scoped Topology
open _root_.D5.S3.Analytic.Laplace.EulerPoleObstruction
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Analytic.Laplace.EulerPoleObstruction

def PoleSourceExists : Prop := ∃ (g : ℝ → ℝ) (U d σ : ℝ) (Φ : ℂ → ℂ) (a Λ : ℂ),
  IntegrableOn g (Ioi U) ∧ 0 < U ∧ d < σ ∧ σ < 0 ∧
  MeromorphicOn Φ {z | d < z.re} ∧
  (∀ x : ℝ, σ ≤ x → x ≤ 0 → AnalyticAt ℂ Φ (x : ℂ)) ∧
  (∀ z : ℂ, 0 < z.re → euler (tailLaplace g U) z = Φ z) ∧
  a.re = σ ∧ a.im ≠ 0 ∧ DoublePole Φ a Λ

namespace Pointwise
abbrev signature : Signature := _root_.Reg.Support.SingleDependentReadout.signature (ℂ × ℝ) (fun _ => ℂ) (fun _ => ℝ)
def actual : Realization signature := realize signature (fun _ _ z => ‖z‖) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law Q := ∀ {g : ℝ → ℝ} {U d σ c s : ℝ} {Φ : ℂ → ℂ}
    (hg : IntegrableOn g (Ioi U)) (hU : 0 < U) (hdσ : d < σ) (hσ : σ < 0)
    (hΦm : MeromorphicOn Φ {z | d < z.re})
    (hΦr : ∀ x : ℝ, σ ≤ x → x ≤ 0 → AnalyticAt ℂ Φ (x : ℂ))
    (hode : ∀ z : ℂ, 0 < z.re → euler (tailLaplace g U) z = Φ z)
    {a Λ : ℂ} (ha : a.re = σ) (him : a.im ≠ 0) (hpole : DoublePole Φ a Λ)
    (hs : s ^ 2 = 1) (hc : 0 ≤ c)
    (hbound : ∀ u : ℝ, U < u → s * g u ≤ envelope σ c u),
    Q.readout () (a, c) Λ ≤ ‖a‖ * c
private theorem actual_law : arena.Law actual := @coefficient_le_of_pointwise_envelope
private theorem exact_bridge : (type_of% @coefficient_le_of_pointwise_envelope) ↔ arena.Law actual := Iff.rfl
private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(0, 0), 0, 1, ?_⟩
  norm_num [actual, realize]
private theorem variation_requires_pole_source {Q : Realization signature}
    (hQ : ¬ arena.Law Q) : PoleSourceExists := by
  by_contra hn
  apply hQ
  intro g U d σ c s Φ hg hU hdσ hσ hΦm hΦr hode a Λ ha him hpole hs hc hbound
  exact (hn ⟨g, U, d, σ, Φ, a, Λ, hg, hU, hdσ, hσ, hΦm, hΦr, hode,
    ha, him, hpole⟩).elim

example (variation : Variation arena actual) (sensitivity : Sensitivity arena actual) :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@coefficient_le_of_pointwise_envelope) (Realization signature) Unit Unit where
  unitName := `D5.S3.Analytic.Laplace.EulerPoleObstruction.coefficient_le_of_pointwise_envelope.audit
  realizationName := `Reg.D5.S3.Analytic.Laplace.EulerPoleObstruction.Pointwise.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨{
    actual := actual
    bridge := exact_bridge
    variation := variation
    sensitivity := sensitivity
    dependence := actual_dependence }⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some actual
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end Pointwise

namespace Eventual
abbrev signature : Signature := _root_.Reg.Support.SingleDependentReadout.signature (ℂ × ℝ) (fun _ => ℂ) (fun _ => ℝ)
def actual : Realization signature := realize signature (fun _ _ z => ‖z‖) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law Q := ∀ {g : ℝ → ℝ} {U d σ c s : ℝ} {Φ : ℂ → ℂ}
    (hg : IntegrableOn g (Ioi U)) (hU : 0 < U) (hdσ : d < σ) (hσ : σ < 0)
    (hΦm : MeromorphicOn Φ {z | d < z.re})
    (hΦr : ∀ x : ℝ, σ ≤ x → x ≤ 0 → AnalyticAt ℂ Φ (x : ℂ))
    (hode : ∀ z : ℂ, 0 < z.re → euler (tailLaplace g U) z = Φ z)
    {a Λ : ℂ} (ha : a.re = σ) (him : a.im ≠ 0) (hpole : DoublePole Φ a Λ)
    (hs : s ^ 2 = 1) (hc : 0 ≤ c)
    (hbound : ∀ᶠ u : ℝ in atTop, s * g u ≤ envelope σ c u),
    Q.readout () (a, c) Λ ≤ ‖a‖ * c
private theorem actual_law : arena.Law actual := @coefficient_le_of_envelope
private theorem exact_bridge : (type_of% @coefficient_le_of_envelope) ↔ arena.Law actual := Iff.rfl
private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(0, 0), 0, 1, ?_⟩
  norm_num [actual, realize]
private theorem variation_requires_pole_source {Q : Realization signature}
    (hQ : ¬ arena.Law Q) : PoleSourceExists := by
  by_contra hn
  apply hQ
  intro g U d σ c s Φ hg hU hdσ hσ hΦm hΦr hode a Λ ha him hpole hs hc hbound
  exact (hn ⟨g, U, d, σ, Φ, a, Λ, hg, hU, hdσ, hσ, hΦm, hΦr, hode,
    ha, him, hpole⟩).elim

example (variation : Variation arena actual) (sensitivity : Sensitivity arena actual) :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@coefficient_le_of_envelope) (Realization signature) Unit Unit where
  unitName := `D5.S3.Analytic.Laplace.EulerPoleObstruction.coefficient_le_of_envelope.audit
  realizationName := `Reg.D5.S3.Analytic.Laplace.EulerPoleObstruction.Eventual.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨{
    actual := actual
    bridge := exact_bridge
    variation := variation
    sensitivity := sensitivity
    dependence := actual_dependence }⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some actual
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end Eventual

namespace Peaks
abbrev signature : Signature := _root_.Reg.Support.SingleDependentReadout.signature (ℝ → ℝ) (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature := realize signature (fun _ g u => g u) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law Q := ∀ {g : ℝ → ℝ} {U₀ d σ : ℝ} {Φ : ℂ → ℂ}
    (hg : IntegrableOn g (Ioi U₀)) (hU₀ : 0 < U₀) (hdσ : d < σ) (hσ : σ < 0)
    (hΦm : MeromorphicOn Φ {z | d < z.re})
    (hreal : ∀ x : ℝ, σ ≤ x → x ≤ 0 → AnalyticAt ℂ Φ (x : ℂ))
    (hode : ∀ z : ℂ, 0 < z.re → euler (tailLaplace g U₀) z = Φ z)
    {a Λ : ℂ} (ha : a.re = σ) (him : a.im ≠ 0) (hpole : DoublePole Φ a Λ),
    ∀ s : ℝ, s ^ 2 = 1 → ∀ c : ℝ, 0 ≤ c → c < ‖Λ‖ / ‖a‖ →
      ∀ T : ℝ, ∃ u : ℝ, max T U₀ < u ∧
        c < u * Real.exp (-σ * u) * (s * Q.readout () g u)
private theorem actual_law : arena.Law actual := @signed_peaks
private theorem exact_bridge : (type_of% @signed_peaks) ↔ arena.Law actual := Iff.rfl
private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨id, 0, 1, zero_ne_one⟩
private theorem variation_requires_pole_source {Q : Realization signature}
    (hQ : ¬ arena.Law Q) : PoleSourceExists := by
  by_contra hn
  apply hQ
  intro g U d σ Φ hg hU hdσ hσ hΦm hΦr hode a Λ ha him hpole
  exact (hn ⟨g, U, d, σ, Φ, a, Λ, hg, hU, hdσ, hσ, hΦm, hΦr, hode,
    ha, him, hpole⟩).elim

example (variation : Variation arena actual) (sensitivity : Sensitivity arena actual) :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@signed_peaks) (Realization signature) Unit Unit where
  unitName := `D5.S3.Analytic.Laplace.EulerPoleObstruction.signed_peaks.audit
  realizationName := `Reg.D5.S3.Analytic.Laplace.EulerPoleObstruction.Peaks.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨{
    actual := actual
    bridge := exact_bridge
    variation := variation
    sensitivity := sensitivity
    dependence := actual_dependence }⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some actual
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end Peaks

end Reg.D5.S3.Analytic.Laplace.EulerPoleObstruction
