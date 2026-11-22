import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Words.Patterns.Separable.EndpointCycleHazardSeries
import Reg.Support.DependentFamily
import Mathlib.MeasureTheory.Measure.Continuity

/-! Read the actual one-cycle hit mass as a function of the incoming discrepancy. -/

namespace Reg.D5.S1.Words.Patterns.Separable.EndpointCycleHazardSeries

open _root_.D5.S1.Words.Patterns.Separable.ActualCycles
open _root_.D5.S1.Words.Patterns.Separable.ActualCycleLaw
open _root_.D5.S1.Words.Patterns.Separable.EndpointCycleHazard
open _root_.D5.S1.Words.Patterns.Separable.MinimumCutKernel
open _root_.D5.S1.Words.Patterns.Separable.OccupiedComparison
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit MeasureTheory
open scoped ENNReal
noncomputable section

abbrev signature : Signature where
  Params := Unit
  State _ := ℤ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ≥0∞
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ e => nextHazard e) (fun a => nomatch a)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => ⊤) (fun a => nomatch a)

def arena : Arena where
  signature := signature
  Law R := ∀ e : ℤ,
    R.readout () () e = ENNReal.ofReal (rawOccupation e) +
      ∑' r : ℕ, ENNReal.ofReal b ^ (2*r+1) * (1 + ENNReal.ofReal b) *
        normalizedSkewIterate (r+1) e

private theorem hazard_le_one (e : ℤ) : nextHazard e ≤ 1 := by
  unfold nextHazard
  calc
    _ ≤ cyclePMF.toMeasure Set.univ := measure_mono (Set.subset_univ _)
    _ = 1 := measure_univ

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have h0 := h 0
  change (⊤ : ℝ≥0∞) = ENNReal.ofReal (rawOccupation 0) +
    ∑' r : ℕ, ENNReal.ofReal b ^ (2*r+1) * (1 + ENNReal.ofReal b) *
      normalizedSkewIterate (r+1) 0 at h0
  have heq := h0.trans (nextHazard_eq_normalized_series 0).symm
  exact (not_le_of_gt ENNReal.one_lt_top) (heq.le.trans (hazard_le_one 0))

private def singletonDirect : Indecomposable false 1 :=
  ⟨identityAvoider 1, by
    rintro ⟨cut, hc, ht, _⟩
    omega⟩

private def singletonMark : MarkedCycle :=
  ⟨false, .terminal 0 singletonDirect⟩

private theorem singletonMark_hits : hit singletonMark.2 0 := by
  change false = false ∧ hitsDiagonal singletonDirect.val.val 0
  refine ⟨rfl, ⟨0, ?_⟩⟩
  have hp : singletonDirect.val.val (0 : Fin 1) = 0 := Subsingleton.elim _ _
  rw [hp, sub_self]

private theorem hazard_zero_pos : 0 < nextHazard 0 := by
  have hr := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hs := Real.sqrt_nonneg (2 : ℝ)
  have hb : 0 < b := by unfold b; nlinarith
  have hρ : 0 < rho := by unfold rho; positivity
  have hw : 0 < cyclePMF singletonMark := by
    change 0 < ENNReal.ofReal (rho ^ 1)
    exact ENNReal.ofReal_pos.mpr (pow_pos hρ 1)
  have hsubset : ({singletonMark} : Set MarkedCycle) ⊆
      {c : MarkedCycle | hit c.2 0} := by
    intro c hc
    rw [Set.mem_singleton_iff.mp hc]
    exact singletonMark_hits
  apply lt_of_lt_of_le hw
  change cyclePMF singletonMark ≤ cyclePMF.toMeasure {c : MarkedCycle | hit c.2 0}
  rw [← PMF.toMeasure_apply_singleton cyclePMF singletonMark (measurableSet_singleton _)]
  exact measure_mono hsubset

private theorem hit_lt_size {sign : Bool} (c : UnboundedCycle sign) (e : ℤ)
    (h : hit c e) : e < (c.size : ℤ) := by
  induction c generalizing e with
  | terminal n shape =>
      simp only [hit] at h
      obtain ⟨j, hj⟩ := h.2
      change (j.val : ℤ) - ((shape.val.val j).val : ℤ) = e at hj
      have hbound : j.val < n + 1 := j.isLt
      simp only [UnboundedCycle.size]
      omega
  | @discard sign n shape tail ih =>
      simp only [hit] at h
      have hnext := ih _ h
      simp only [UnboundedCycle.size]
      cases sign <;> simp only [Bool.false_eq_true, if_false, if_true] at hnext <;> omega

private def cycleSizeTail (n : ℕ) : Set MarkedCycle :=
  {c | n < c.2.size}

private theorem hazard_le_cycleSizeTail (n : ℕ) :
    nextHazard (n : ℤ) ≤ cyclePMF.toMeasure (cycleSizeTail n) := by
  apply measure_mono
  intro c hc
  change n < c.2.size
  exact_mod_cast hit_lt_size c.2 (n : ℤ) hc

private theorem cycleSizeTail_empty : (⋂ n : ℕ, cycleSizeTail n) = ∅ := by
  ext c
  constructor
  · intro hc
    have hall := Set.mem_iInter.mp hc c.2.size
    exact (Nat.lt_irrefl _ hall).elim
  · simp

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro role
  have hmeas (n : ℕ) : MeasurableSet (cycleSizeTail n) := trivial
  have hfin : ∃ n, cyclePMF.toMeasure (cycleSizeTail n) ≠ ⊤ :=
    ⟨0, measure_ne_top _ _⟩
  obtain ⟨m, hm⟩ := exists_measure_iInter_lt
    (μ := cyclePMF.toMeasure) (s := cycleSizeTail) (fun n => (hmeas n).nullMeasurableSet)
    hazard_zero_pos hfin cycleSizeTail_empty
  have hsubset : cycleSizeTail m ⊆ ⋂ n ≤ m, cycleSizeTail n := by
    intro c hc
    refine Set.mem_iInter.mpr (fun n => Set.mem_iInter.mpr (fun hn => ?_))
    exact lt_of_le_of_lt hn hc
  refine ⟨(), 0, (m : ℤ), ?_⟩
  change nextHazard 0 ≠ nextHazard (m : ℤ)
  exact Ne.symm (ne_of_lt (lt_of_le_of_lt
    ((hazard_le_cycleSizeTail m).trans (measure_mono hsubset)) hm))

def family : Registration arena (type_of% @nextHazard_eq_normalized_series) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨nextHazard_eq_normalized_series, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other hother
      exact (hother (@Subsingleton.elim Unit _ other role)).elim
    · intro anchor
      exact nomatch anchor
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@nextHazard_eq_normalized_series) (Realization signature) (Type) Unit where
  unitName := `Reg.D5.S1.Words.Patterns.Separable.EndpointCycleHazardSeries.unit
  realizationName := `Reg.D5.S1.Words.Patterns.Separable.EndpointCycleHazardSeries.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ e => nextHazard e) (fun a => nomatch a))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.Patterns.Separable.EndpointCycleHazardSeries
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
end
end Reg.D5.S1.Words.Patterns.Separable.EndpointCycleHazardSeries
