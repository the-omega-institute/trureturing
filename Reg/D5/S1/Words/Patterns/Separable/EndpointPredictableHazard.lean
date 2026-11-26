import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Words.Patterns.Separable.EndpointPredictableHazard
import Reg.Support.DependentFamily

/-! Audit the actual upcoming-cycle hit predicate selected in the strict-past identity. -/

namespace Reg.D5.S1.Words.Patterns.Separable.EndpointPredictableHazard

open _root_.D5.S1.Words.Patterns.Separable.ActualCycles
open _root_.D5.S1.Words.Patterns.Separable.ActualCycleLaw
open _root_.D5.S1.Words.Patterns.Separable.EndpointPredictableHazard
open _root_.D5.S1.Words.Patterns.Separable.EndpointFirstCycleHitLimit
open _root_.D5.S1.Words.Patterns.Separable.EndpointCycleHazard (hit nextHazard)
open _root_.D5.S1.Words.Patterns.Separable.EndpointHistoryKernel (indecomposableWitness)
open _root_.D5.S1.Words.Patterns.Separable.OccupiedComparison (b rho hitsDiagonal)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Filter Topology MeasureTheory
open scoped ENNReal

noncomputable section

abbrev signature : Signature where
  Params := Unit
  State _ := ℤ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ → Set Stream
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ e => hitAt e) (fun a => nomatch a)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => ∅) (fun a => nomatch a)

def arena : Arena where
  signature := signature
  Law R := ∀ e : ℤ,
    (∀ (k : ℕ) (s : Set Stream), MeasurableSet[pastSigma k] s →
      streamMeasure (s ∩ R.readout () () e k) =
        ∫⁻ ω in s, nextHazard (e + streamDiscrepancy k ω) ∂streamMeasure) ∧
    ((∀ᵐ ω ∂streamMeasure, ∑' k, nextHazard (e + streamDiscrepancy k ω) = ∞) →
      ∀ᵐ ω ∂streamMeasure, ∀ N : ℕ, ∃ k ≥ N, ω ∈ R.readout () () e k)

private def directSingleton : MarkedCycle :=
  ⟨false, .terminal 0 (indecomposableWitness false 1)⟩

private theorem directSingleton_hits : hit directSingleton.2 0 := by
  change false = false ∧ hitsDiagonal (indecomposableWitness false 1).val.val 0
  refine ⟨rfl, ⟨0, ?_⟩⟩
  have hp : (indecomposableWitness false 1).val.val (0 : Fin 1) = 0 := Subsingleton.elim _ _
  rw [hp, sub_self]

private theorem directSingleton_misses : ¬ hit directSingleton.2 1 := by
  change ¬ (false = false ∧ hitsDiagonal (indecomposableWitness false 1).val.val 1)
  rintro ⟨_, j, hj⟩
  have h1 : j = 0 := Subsingleton.elim _ _
  have h2 : (indecomposableWitness false 1).val.val j = 0 := Subsingleton.elim _ _
  rw [h1] at h2 hj
  rw [h2, sub_self] at hj
  exact zero_ne_one hj

private theorem rho_pos : 0 < rho := by
  have hb : 0 < b := by
    unfold b
    have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    have hs := Real.sqrt_nonneg (2 : ℝ)
    nlinarith
  unfold rho
  exact pow_pos hb 2

private theorem positive_hazard_zero : 0 < nextHazard 0 := by
  unfold nextHazard
  have hm := measure_mono (μ := cyclePMF.toMeasure)
    (show {directSingleton} ⊆ {c : MarkedCycle | hit c.2 0} by
      intro c hc
      rw [Set.mem_singleton_iff] at hc
      subst c
      exact directSingleton_hits)
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)] at hm
  have hp : cyclePMF directSingleton = ENNReal.ofReal rho := by
    change ENNReal.ofReal (rho ^ (0 + 1 : ℕ)) = _
    rw [zero_add, pow_one]
  rw [hp] at hm
  exact (ENNReal.ofReal_pos.mpr rho_pos).trans_le hm

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hs : MeasurableSet[pastSigma 0] (Set.univ : Set Stream) := by
    let _ : MeasurableSpace Stream := pastSigma 0
    exact MeasurableSet.univ
  have hz := (h 0).1 0 Set.univ hs
  change streamMeasure ((Set.univ : Set Stream) ∩ ∅) =
    (∫⁻ ω in (Set.univ : Set Stream),
      nextHazard (0 + streamDiscrepancy 0 ω) ∂streamMeasure) at hz
  have hzero (ω : Stream) : streamDiscrepancy 0 ω = 0 := by simp [streamDiscrepancy]
  simp only [Set.inter_empty, measure_empty, Measure.restrict_univ, hzero, add_zero,
    lintegral_const, measure_univ, mul_one] at hz
  exact (ne_of_gt positive_hazard_zero) hz.symm

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have he := congrFun h 0
  change hitAt 0 0 = hitAt 1 0 at he
  let ω : Stream := fun _ => directSingleton
  have hzero : streamDiscrepancy 0 ω = 0 := by simp [streamDiscrepancy]
  have ha : ω ∈ hitAt 0 0 := by
    change hit directSingleton.2 (0 + streamDiscrepancy 0 ω)
    rw [hzero, add_zero]
    exact directSingleton_hits
  have hb : ω ∉ hitAt 1 0 := by
    change ¬ hit directSingleton.2 (1 + streamDiscrepancy 0 ω)
    rw [hzero, add_zero]
    exact directSingleton_misses
  exact hb (he ▸ ha)

def family : Registration arena (type_of% @actual_predictable_hazard_and_recurrence) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_predictable_hazard_and_recurrence, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j hj => (hj (@Subsingleton.elim Unit _ j i)).elim,
    rfl, rejected_law⟩, fun a => nomatch a⟩
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actual_predictable_hazard_and_recurrence) (Realization signature) (Type) Unit where
  unitName := `Reg.D5.S1.Words.Patterns.Separable.EndpointPredictableHazard.unit
  realizationName := `Reg.D5.S1.Words.Patterns.Separable.EndpointPredictableHazard.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ e => hitAt e) (fun a => nomatch a))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.Patterns.Separable.EndpointPredictableHazard
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg", "body", "body", "body", "fn", "arg", "arg", "arg", "fn"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit

end
end Reg.D5.S1.Words.Patterns.Separable.EndpointPredictableHazard
