import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Words.Patterns.Separable.EndpointFiniteLiteralHit
import Reg.Support.DependentFamily

/-! The actual readout is the whole finite-permutation probability at the offset. -/

namespace Reg.D5.S1.Words.Patterns.Separable.EndpointFiniteLiteralHit


open _root_.D5.S1.Words.Patterns.Separable.EndpointFiniteLiteralHit
open _root_.D5.S1.Words.Patterns.Separable.ActualCycles
open _root_.D5.S1.Words.Patterns.Separable.ActualCycleLaw
open _root_.D5.S1.Words.Patterns.Separable.CutFactorization
open _root_.D5.S1.Words.Patterns.Separable.MinimumCutKernel
open _root_.D5.S1.Words.Patterns.Separable.EndpointCanonicalCycle
open _root_.D5.S1.Words.Patterns.Separable.EndpointFirstCycleHitLimit
open _root_.D5.S1.Words.Patterns.Separable.EndpointCycleHazard
open _root_.D5.S1.Words.Patterns.Separable.EndpointHistoryKernel (indecomposableWitness)
open _root_.D5.S0.Diagonal.Probability.EquivariantEscape (uniformPmf)
open _root_.D5.S1.Words.Patterns.Separable.OccupiedComparison
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Filter MeasureTheory Topology
open scoped ENNReal

noncomputable section

abbrev signature : Signature where
  Params := Unit
  State _ := ℤ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ → ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ e => literalHitProbability e) (fun a => nomatch a)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => 0) (fun a => nomatch a)

def arena : Arena where
  signature := signature
  Law R := ∀ e : ℤ,
    (∀ k : ℕ, ∀ a : ℝ, a < firstKHitProbability k e →
      ∀ᶠ n in atTop, a < R.readout () () e n) ∧
    ((∀ᵐ ω ∂streamMeasure, ∃ k : ℕ, hit (ω k).2 (e + streamDiscrepancy k ω)) →
      Tendsto (R.readout () () e) atTop (𝓝 1))

private def directSingleton : MarkedCycle :=
  ⟨false, .terminal 0 (indecomposableWitness false 1)⟩

private theorem directSingleton_hits : hit directSingleton.2 0 := by
  change false = false ∧ hitsDiagonal (indecomposableWitness false 1).val.val 0
  refine ⟨rfl, ⟨0, ?_⟩⟩
  have hi : (indecomposableWitness false 1).val.val (0 : Fin 1) = 0 := Subsingleton.elim _ _
  rw [hi, sub_self]

private theorem immediate_hit_positive : 0 < firstKHitProbability 1 0 := by
  let U : Set MarkedCycle := {directSingleton}
  let ev : Stream → MarkedCycle := fun ω => ω 0
  have hev : MeasurePreserving ev streamMeasure cyclePMF.toMeasure :=
    measurePreserving_eval_infinitePi (fun _ : ℕ => cyclePMF.toMeasure) 0
  have hsub : ev ⁻¹' U ⊆ firstKHit 1 0 := by
    intro ω hω
    change ω 0 = directSingleton at hω
    refine ⟨0, by omega, ?_⟩
    simp only [streamDiscrepancy, Fin.sum_univ_zero, add_zero]
    rw [hω]
    exact directSingleton_hits
  have hM : 0 < streamMeasure (ev ⁻¹' U) := by
    rw [hev.measure_preimage (measurableSet_singleton directSingleton).nullMeasurableSet,
      PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
    have hr : 0 < rho := by
      have hb : 0 < b := by
        unfold b
        nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg (2 : ℝ)]
      unfold rho
      positivity
    change 0 < ENNReal.ofReal (rho ^ (0 + 1 : ℕ))
    simpa only [zero_add, pow_one] using ENNReal.ofReal_pos.2 hr
  exact ENNReal.toReal_pos (hM.trans_le (measure_mono hsub)).ne' (measure_ne_top _ _)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨n, hn⟩ := ((h 0).1 1 0 immediate_hit_positive).exists
  change (0 : ℝ) < 0 at hn
  exact lt_irrefl _ hn

private theorem singleton_all_hits (π : Avoider 1) : hitsDiagonal π.val 0 := by
  refine ⟨0, ?_⟩
  rw [show π.val (0 : Fin 1) = 0 from Subsingleton.elim _ _, sub_self]

private theorem singleton_no_shift (π : Avoider 1) : ¬ hitsDiagonal π.val 1 := by
  rintro ⟨j, hj⟩
  rw [show π.val j = j from Subsingleton.elim _ _, sub_self] at hj
  exact zero_ne_one hj

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have he := congrFun h 1
  change literalHitProbability 0 1 = literalHitProbability 1 1 at he
  classical
  let : Nonempty (Avoider 1) := ⟨identityAvoider 1⟩
  have ha : (uniformPmf (Avoider 1)).toOuterMeasure {π | hitsDiagonal π.val 0} = 1 :=
    (PMF.toOuterMeasure_apply_eq_one_iff _ _).2 fun π _ => singleton_all_hits π
  have hb : (uniformPmf (Avoider 1)).toOuterMeasure {π | hitsDiagonal π.val 1} = 0 :=
    (PMF.toOuterMeasure_apply_eq_zero_iff _ _).2
      (Set.disjoint_left.2 fun π _ hp => singleton_no_shift π hp)
  change ((uniformPmf (Avoider 1)).toOuterMeasure {π | hitsDiagonal π.val 0}).toReal =
    ((uniformPmf (Avoider 1)).toOuterMeasure {π | hitsDiagonal π.val 1}).toReal at he
  rw [ha, hb, ENNReal.toReal_one, ENNReal.toReal_zero] at he
  exact one_ne_zero he

def family : Registration arena (type_of% @finite_avoider_literal_hit_limit_of_stream_hit) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨finite_avoider_literal_hit_limit_of_stream_hit, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j hj => (hj (@Subsingleton.elim Unit _ j i)).elim,
    rfl, rejected_law⟩, fun a => nomatch a⟩
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@finite_avoider_literal_hit_limit_of_stream_hit) (Realization signature) (Type) Unit where
  unitName := `Reg.D5.S1.Words.Patterns.Separable.EndpointFiniteLiteralHit.unit
  realizationName := `Reg.D5.S1.Words.Patterns.Separable.EndpointFiniteLiteralHit.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ e => literalHitProbability e) (fun a => nomatch a))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.Patterns.Separable.EndpointFiniteLiteralHit
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg", "body", "body", "body", "fn", "arg", "body", "arg", "fn"]
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
end Reg.D5.S1.Words.Patterns.Separable.EndpointFiniteLiteralHit
