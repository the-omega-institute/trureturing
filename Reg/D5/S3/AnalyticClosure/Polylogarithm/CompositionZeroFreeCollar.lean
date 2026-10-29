import D5.S3.AnalyticClosure.Polylogarithm.CompositionReciprocalSeries
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.AnalyticClosure.Polylogarithm.CompositionZeroFreeCollar

open _root_.D5.S3.AnalyticClosure.Polylogarithm
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Complex Filter Set Topology LeanInformationAudit
noncomputable section

abbrev signature : Signature where
  Params := ℕ+ × List ℕ+
  State _ := ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ p z ↦ CompositionZeroFreeCollar.normalizedContinuation p.1 p.2 z)
  (fun e ↦ nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ ↦ 0) (fun e ↦ nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (head : ℕ+) (tail : List ℕ+),
    (∀ z, ‖z‖ < 1 → R.readout () (head, tail) z = CompositionDisk.normalized head tail z) ∧
    AnalyticOnNhd ℂ (R.readout () (head, tail)) CompositionContinuation.omega ∧
    ∃ R0 : ℝ, 1 < R0 ∧ ∀ z ∈ CompositionContinuation.omega,
      ‖z‖ < R0 → R.readout () (head, tail) z ≠ 0

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨_, _, R0, hR0, hn⟩ := h 1 []
  have ho : (0 : ℂ) ∈ CompositionContinuation.omega := by
    simp [CompositionContinuation.omega, Complex.mem_slitPlane_iff]
  exact (hn 0 ho (by simpa using zero_lt_one.trans hR0)) rfl

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  suffices hh : ∃ x y : ℂ,
      CompositionZeroFreeCollar.normalizedContinuation 1 [] x ≠
        CompositionZeroFreeCollar.normalizedContinuation 1 [] y by
    obtain ⟨x, y, hxy⟩ := hh
    exact ⟨(1, []), x, y, hxy⟩
  classical
  by_contra hn
  push Not at hn
  have hp : HasFPowerSeriesAt (CompositionZeroFreeCollar.normalizedContinuation 1 [])
      (FormalMultilinearSeries.ofScalars ℂ
        (fun n ↦ (CompositionDisk.coefficient 1 [] n : ℂ))) 0 := by
    apply hasFPowerSeriesAt_iff.mpr
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) zero_lt_one] with z hz
    have hz' : ‖z‖ < 1 := by simpa using hz
    simp only [zero_add]
    rw [(CompositionZeroFreeCollar.result 1 []).1 z hz']
    have hs := ((CompositionDisk.source_series 1 []).2.2.1 z hz').of_norm.hasSum
    simpa [CompositionDisk.normalized, mul_comm] using hs
  have heq : CompositionZeroFreeCollar.normalizedContinuation 1 [] =
      (fun _ : ℂ ↦ CompositionZeroFreeCollar.normalizedContinuation 1 [] 0) :=
    funext (fun z ↦ hn z 0)
  rw [heq] at hp
  have hh := congrArg (fun s : FormalMultilinearSeries ℂ ℂ ℂ ↦ s 1 (fun _ ↦ 1))
    (hp.eq_formalMultilinearSeries hasFPowerSeriesAt_const)
  have hc : (CompositionDisk.coefficient 1 [] 1 : ℂ) = 0 := by
    simpa [FormalMultilinearSeries.ofScalars_apply_eq,
      constFormalMultilinearSeries_apply_of_nonzero] using hh
  exact (Complex.ofReal_ne_zero.mpr ((CompositionDisk.source_series 1 []).1 1).ne') hc

def sourceEvidence : Registration arena (type_of% (@CompositionZeroFreeCollar.result)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨CompositionZeroFreeCollar.result, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

def result_registration : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@CompositionZeroFreeCollar.result) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.AnalyticClosure.Polylogarithm.CompositionZeroFreeCollar.resultUnit
  realizationName :=
    `Reg.D5.S3.AnalyticClosure.Polylogarithm.CompositionZeroFreeCollar.sourceEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨sourceEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p z ↦ CompositionZeroFreeCollar.normalizedContinuation p.1 p.2 z)
    (fun e ↦ nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.AnalyticClosure.Polylogarithm.CompositionZeroFreeCollar
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "body", "body", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }, {
      path := #["body", "body", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }, {
      path := #["body", "body", "arg", "arg", "arg", "body", "arg", "body", "body",
        "body", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.AnalyticClosure.Polylogarithm.CompositionZeroFreeCollar
