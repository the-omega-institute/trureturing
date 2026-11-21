import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Words.Patterns.Separable.EndpointFirstCycleHitLimit
import Reg.Support.DependentFamily

/-! Audit the actual neighborhood filter in the literal fixed-cycle convergence law. -/

namespace Reg.D5.S1.Words.Patterns.Separable.EndpointFirstCycleHitLimit

open _root_.D5.S1.Words.Patterns.Separable.ActualCycles
open _root_.D5.S1.Words.Patterns.Separable.ActualCycleLaw
open _root_.D5.S1.Words.Patterns.Separable.EndpointCanonicalCycle
open _root_.D5.S1.Words.Patterns.Separable.EndpointFirstCycleHitLimit
open _root_.D5.S1.Words.Patterns.Separable.EndpointCycleHazard (hit)
open _root_.D5.S1.Words.Patterns.Separable.EndpointHistoryKernel (indecomposableWitness)
open _root_.D5.S1.Words.Patterns.Separable.MinimumCutKernel (actualMass)
open _root_.D5.S1.Words.Patterns.Separable.OccupiedComparison (b rho hitsDiagonal)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Filter Topology MeasureTheory
open scoped ENNReal

noncomputable section

abbrev signature : Signature where
  Params := ℤ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Filter ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ e k => 𝓝 (firstKHitProbability k e)) (fun a => nomatch a)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => ⊥) (fun a => nomatch a)

def arena : Arena where
  signature := signature
  Law R := ∀ (k : ℕ) (e : ℤ),
    Tendsto (fun n => actualMass n (actualCanonicalFirstKLiteralHit k e n)) atTop
      (R.readout () e k)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact atTop_neBot.ne (tendsto_bot_right_iff.mp (h 0 0))

private theorem firstKHitProbability_zero (e : ℤ) :
    firstKHitProbability 0 e = 0 := by
  have heq : firstKHit 0 e = ∅ := by ext ω; simp [firstKHit]
  simp [firstKHitProbability, heq]

private def directSingleton : MarkedCycle :=
  ⟨false, .terminal 0 (indecomposableWitness false 1)⟩

private def singletonTuple : UnboundedTuple 1 :=
  (directSingleton, ())

private theorem directSingleton_hits : hit directSingleton.2 0 := by
  change false = false ∧ hitsDiagonal (indecomposableWitness false 1).val.val 0
  refine ⟨rfl, ⟨0, ?_⟩⟩
  have hp : (indecomposableWitness false 1).val.val (0 : Fin 1) = 0 := Subsingleton.elim _ _
  rw [hp, sub_self]

private theorem singletonCylinder_subset : Prefix.cylinder singletonTuple ⊆ firstKHit 1 0 := by
  intro ω hω
  have h0 : ω 0 = directSingleton := hω (0 : Fin 1)
  refine ⟨0, by decide, ?_⟩
  rw [h0]
  simpa [streamDiscrepancy] using directSingleton_hits

private theorem rho_pos : 0 < rho := by
  have hb : 0 < b := by
    unfold b
    have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    have hs := Real.sqrt_nonneg (2 : ℝ)
    nlinarith
  unfold rho
  exact pow_pos hb 2

private theorem rho_le_firstKHitProbability_one_zero : rho ≤ firstKHitProbability 1 0 := by
  have hp := (actual_countable_cycle_law.2.2.2.2.2.1 1 singletonTuple).2
  change streamMeasure (Prefix.cylinder singletonTuple) = ENNReal.ofReal (rho ^ 1) at hp
  have h := measureReal_mono (μ := streamMeasure) singletonCylinder_subset
  rw [Measure.real, hp, pow_one, ENNReal.toReal_ofReal rho_pos.le] at h
  exact h

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨0, 0, 1, nhds_injective.ne ?_⟩
  rw [firstKHitProbability_zero]
  exact ne_of_lt (rho_pos.trans_le rho_le_firstKHitProbability_one_zero)

def family : Registration arena (type_of% @actualCanonicalFirstKLiteralHit_limit) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actualCanonicalFirstKLiteralHit_limit, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j hj => (hj (@Subsingleton.elim Unit _ j i)).elim,
    rfl, rejected_law⟩, fun a => nomatch a⟩
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actualCanonicalFirstKLiteralHit_limit) (Realization signature) (Type) Unit where
  unitName := `Reg.D5.S1.Words.Patterns.Separable.EndpointFirstCycleHitLimit.unit
  realizationName := `Reg.D5.S1.Words.Patterns.Separable.EndpointFirstCycleHitLimit.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ e k => 𝓝 (firstKHitProbability k e))
    (fun a => nomatch a))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.Patterns.Separable.EndpointFirstCycleHitLimit
    definition := none
    coordinates := #[1]
    readouts := #[{
      path := #["body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg", "fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit

end
end Reg.D5.S1.Words.Patterns.Separable.EndpointFirstCycleHitLimit
