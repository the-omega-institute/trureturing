/- GID: D5/S3/Weil/Budget/ProjectivePrimalConvergence
   generality: G
   mirror-B: D5/B/S3/Weil/Budget/ProjectivePrimalConvergence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite circle-moment primal optima converge projectively by weak-* compactness. -/

import D5.S3.Weil.Budget.FullCirclePrimalAttainment
import Mathlib.Topology.Order.MonotoneConvergence

/- Library-search audit trail (2026-09-01):
   * `FullCirclePrimalAttainment` supplies the concrete compact budget set, closed
     moment constraints, and compact extreme-value pattern on `FiniteMeasure Circle`.
   * Pinned Mathlib supplies `isCompact_setOf_finiteMeasure_le_of_compactSpace`,
     `FiniteMeasure.continuous_integral_continuousMap`, and continuous mass evaluation.
   * There is no packaged first-countability or sequential-compactness instance for
     `FiniteMeasure Circle`.  The proof below derives the required subsequence by
     splitting a finite measure into its mass and normalized probability measure;
     `ProbabilityMeasure Circle` is compact and metrizable in pinned Mathlib.
   * `IsCompact.tendsto_subseq`, continuous scalar multiplication of finite measures,
     and `FiniteMeasure.self_eq_mass_smul_normalize` then reconstruct weak-* convergence. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped ENNReal NNReal
open Filter MeasureTheory Set Topology

namespace D5.S3.Weil.Budget.ProjectivePrimalConvergence

noncomputable local instance circleMeasurableSpace : MeasurableSpace Circle := borel Circle
local instance circleBorelSpace : BorelSpace Circle := ⟨rfl⟩

open FullCirclePrimalAttainment

/-- A Haar-floor primal point records the proposed floor and the residual positive measure. -/
abbrev PrimalPoint := ℝ≥0 × FiniteMeasure Circle

/-- Reconstruct the completed circle measure from its Haar floor and residual measure. -/
noncomputable def reconstruction (p : PrimalPoint) : FiniteMeasure Circle :=
  p.1 • normalizedCircleHaar + p.2

/-- The common weak-* compact box containing every finite-level feasible set. -/
def commonFeasible (budget : ℝ≥0) : Set PrimalPoint :=
  Icc 0 budget ×ˢ {sigma : FiniteMeasure Circle | sigma.mass ≤ budget}

/-- Feasibility for the first `N` determining circle moments. -/
def levelFeasible (budget : ℝ≥0) (moment : ℕ → C(Circle, ℝ))
    (target : ℕ → ℝ) (N : ℕ) : Set PrimalPoint :=
  commonFeasible budget ∩
    ({p | (reconstruction p).mass ≤ budget} ∩
      {p | ∀ k, k < N →
        ∫ z, moment k z ∂((reconstruction p : FiniteMeasure Circle) : Measure Circle) =
          target k})

/-- Feasibility for the full determining family of circle moments. -/
def fullFeasible (budget : ℝ≥0) (moment : ℕ → C(Circle, ℝ))
    (target : ℕ → ℝ) : Set PrimalPoint :=
  commonFeasible budget ∩
    ({p | (reconstruction p).mass ≤ budget} ∩
      {p | ∀ k,
        ∫ z, moment k z ∂((reconstruction p : FiniteMeasure Circle) : Measure Circle) =
          target k})

/-- The objective is the coefficient of normalized circle Haar measure. -/
def objective (p : PrimalPoint) : ℝ := p.1

/-- The optimal value of the `N`-moment primal problem. -/
noncomputable def levelFrontier (budget : ℝ≥0) (moment : ℕ → C(Circle, ℝ))
    (target : ℕ → ℝ) (N : ℕ) : ℝ :=
  sSup (objective '' levelFeasible budget moment target N)

/-- The optimal value of the full determining-family primal problem. -/
noncomputable def fullFrontier (budget : ℝ≥0) (moment : ℕ → C(Circle, ℝ))
    (target : ℕ → ℝ) : ℝ :=
  sSup (objective '' fullFeasible budget moment target)

private theorem reconstruction_continuous : Continuous reconstruction := by
  change Continuous (fun p : PrimalPoint => p.1 • normalizedCircleHaar + p.2)
  fun_prop

private theorem objective_continuous : Continuous objective := by
  exact NNReal.continuous_coe.comp continuous_fst

private theorem moment_evaluation_continuous
    (moment : ℕ → C(Circle, ℝ)) (k : ℕ) :
    Continuous fun p : PrimalPoint =>
      ∫ z, moment k z ∂((reconstruction p : FiniteMeasure Circle) : Measure Circle) := by
  exact (FiniteMeasure.continuous_integral_continuousMap (moment k)).comp
    reconstruction_continuous

/-- Measures on the circle with a common mass cap admit a weak-* convergent subsequence.

Pinned Mathlib does not expose this as sequential compactness of `FiniteMeasure Circle`.
We extract the mass subsequence and the normalized-probability subsequence separately and
then reconstruct the finite-measure limit. -/
theorem mass_bounded_weakStar_subsequence
    (budget : ℝ≥0) (sequence : ℕ → FiniteMeasure Circle)
    (massBound : ∀ n, (sequence n).mass ≤ budget) :
    ∃ limit : FiniteMeasure Circle, limit.mass ≤ budget ∧
      ∃ selection : ℕ → ℕ, StrictMono selection ∧
        Tendsto (sequence ∘ selection) atTop (nhds limit) := by
  obtain ⟨limitMass, limitMassMem, massSelection, massSelectionStrict, massTendsto⟩ :=
    isCompact_Icc.tendsto_subseq
      (x := fun n => (sequence n).mass)
      (fun n => ⟨zero_le, massBound n⟩)
  obtain ⟨limitProbability, -, probabilitySelection, probabilitySelectionStrict,
      probabilityTendsto⟩ :=
    isCompact_univ.tendsto_subseq
      (x := fun n => (sequence (massSelection n)).normalize)
      (fun _ => mem_univ _)
  let selection := massSelection ∘ probabilitySelection
  let limit : FiniteMeasure Circle :=
    limitMass • limitProbability.toFiniteMeasure
  have selectionStrict : StrictMono selection :=
    massSelectionStrict.comp probabilitySelectionStrict
  have selectedMassTendsto :
      Tendsto (fun n => (sequence (selection n)).mass) atTop (nhds limitMass) := by
    simpa only [selection, Function.comp_def] using
      massTendsto.comp probabilitySelectionStrict.tendsto_atTop
  have selectedProbabilityTendsto :
      Tendsto (fun n => (sequence (selection n)).normalize) atTop
        (nhds limitProbability) := by
    simpa only [selection, Function.comp_def] using probabilityTendsto
  have selectedNormalizedFiniteTendsto :
      Tendsto (fun n => (sequence (selection n)).normalize.toFiniteMeasure) atTop
        (nhds limitProbability.toFiniteMeasure) :=
    ProbabilityMeasure.toFiniteMeasure_continuous.continuousAt.tendsto.comp
      selectedProbabilityTendsto
  have reconstructedTendsto :
      Tendsto
        (fun n => (sequence (selection n)).mass •
          (sequence (selection n)).normalize.toFiniteMeasure)
        atTop (nhds limit) := by
    simpa only [limit] using selectedMassTendsto.smul selectedNormalizedFiniteTendsto
  have selectedTendsto :
      Tendsto (sequence ∘ selection) atTop (nhds limit) := by
    rw [show sequence ∘ selection =
      (fun n => (sequence (selection n)).mass •
        (sequence (selection n)).normalize.toFiniteMeasure) by
      funext n
      exact (sequence (selection n)).self_eq_mass_smul_normalize]
    exact reconstructedTendsto
  refine ⟨limit, ?_, selection, selectionStrict, selectedTendsto⟩
  change (limitMass • limitProbability.toFiniteMeasure).mass ≤ budget
  rw [FiniteMeasure.mass, FiniteMeasure.smul_apply]
  change limitMass * limitProbability.toFiniteMeasure.mass ≤ budget
  rw [ProbabilityMeasure.mass_toFiniteMeasure, mul_one]
  exact limitMassMem.2

/-- The shared budget box is weak-* compact. -/
theorem commonFeasible_isCompact (budget : ℝ≥0) :
    IsCompact (commonFeasible budget) := by
  exact isCompact_Icc.prod
    (isCompact_setOf_finiteMeasure_le_of_compactSpace Circle budget)

/-- Every finite-level feasible set is weak-* closed. -/
theorem levelFeasible_isClosed (budget : ℝ≥0) (moment : ℕ → C(Circle, ℝ))
    (target : ℕ → ℝ) (N : ℕ) :
    IsClosed (levelFeasible budget moment target N) := by
  apply (commonFeasible_isCompact budget).isClosed.inter
  apply IsClosed.inter
  · exact isClosed_Iic.preimage
      (FiniteMeasure.continuous_mass.comp reconstruction_continuous)
  · simp only [setOf_forall]
    exact isClosed_iInter fun k => isClosed_iInter fun _ =>
      isClosed_singleton.preimage (moment_evaluation_continuous moment k)

/-- The full determining-family feasible set is weak-* closed. -/
theorem fullFeasible_isClosed (budget : ℝ≥0) (moment : ℕ → C(Circle, ℝ))
    (target : ℕ → ℝ) :
    IsClosed (fullFeasible budget moment target) := by
  apply (commonFeasible_isCompact budget).isClosed.inter
  apply IsClosed.inter
  · exact isClosed_Iic.preimage
      (FiniteMeasure.continuous_mass.comp reconstruction_continuous)
  · simp only [setOf_forall]
    exact isClosed_iInter fun k =>
      isClosed_singleton.preimage (moment_evaluation_continuous moment k)

private theorem levelFeasible_isCompact
    (budget : ℝ≥0) (moment : ℕ → C(Circle, ℝ)) (target : ℕ → ℝ) (N : ℕ) :
    IsCompact (levelFeasible budget moment target N) := by
  exact (commonFeasible_isCompact budget).inter_right <| by
    apply IsClosed.inter
    · exact isClosed_Iic.preimage
        (FiniteMeasure.continuous_mass.comp reconstruction_continuous)
    · simp only [setOf_forall]
      exact isClosed_iInter fun k => isClosed_iInter fun _ =>
        isClosed_singleton.preimage (moment_evaluation_continuous moment k)

private theorem fullFeasible_isCompact
    (budget : ℝ≥0) (moment : ℕ → C(Circle, ℝ)) (target : ℕ → ℝ) :
    IsCompact (fullFeasible budget moment target) := by
  exact (commonFeasible_isCompact budget).inter_right <| by
    apply IsClosed.inter
    · exact isClosed_Iic.preimage
        (FiniteMeasure.continuous_mass.comp reconstruction_continuous)
    · simp only [setOf_forall]
      exact isClosed_iInter fun k =>
        isClosed_singleton.preimage (moment_evaluation_continuous moment k)

private theorem fullFeasible_subset_levelFeasible
    (budget : ℝ≥0) (moment : ℕ → C(Circle, ℝ)) (target : ℕ → ℝ) (N : ℕ) :
    fullFeasible budget moment target ⊆ levelFeasible budget moment target N := by
  rintro p ⟨hpCommon, hpBudget, hpMoments⟩
  exact ⟨hpCommon, hpBudget, fun k _ => hpMoments k⟩

private theorem levelFeasible_antitone
    (budget : ℝ≥0) (moment : ℕ → C(Circle, ℝ)) (target : ℕ → ℝ) :
    Antitone (levelFeasible budget moment target) := by
  intro N M hNM p hp
  exact ⟨hp.1, hp.2.1, fun k hk => hp.2.2 k (lt_of_lt_of_le hk hNM)⟩

/-- Every finite-level problem has an optimizer once the full problem is feasible. -/
theorem level_optimizer_exists
    (budget : ℝ≥0) (moment : ℕ → C(Circle, ℝ)) (target : ℕ → ℝ)
    (fullNonempty : (fullFeasible budget moment target).Nonempty) (N : ℕ) :
    ∃ optimizer ∈ levelFeasible budget moment target N,
      ∀ p ∈ levelFeasible budget moment target N,
        objective p ≤ objective optimizer := by
  have levelNonempty : (levelFeasible budget moment target N).Nonempty :=
    fullNonempty.mono (fullFeasible_subset_levelFeasible budget moment target N)
  exact (levelFeasible_isCompact budget moment target N).exists_isMaxOn
    levelNonempty objective_continuous.continuousOn

private theorem commonFeasible_subsequence
    (budget : ℝ≥0) (sequence : ℕ → PrimalPoint)
    (inCommon : ∀ n, sequence n ∈ commonFeasible budget) :
    ∃ limit ∈ commonFeasible budget,
      ∃ selection : ℕ → ℕ, StrictMono selection ∧
        Tendsto (sequence ∘ selection) atTop (nhds limit) := by
  obtain ⟨limitMeasure, limitMeasureBound, measureSelection, measureSelectionStrict,
      measureTendsto⟩ :=
    mass_bounded_weakStar_subsequence budget (fun n => (sequence n).2)
      (fun n => (inCommon n).2)
  obtain ⟨limitFloor, limitFloorMem, floorSelection, floorSelectionStrict,
      floorTendsto⟩ :=
    isCompact_Icc.tendsto_subseq
      (x := fun n => (sequence (measureSelection n)).1)
      (fun n => (inCommon (measureSelection n)).1)
  let selection := measureSelection ∘ floorSelection
  have selectionStrict : StrictMono selection :=
    measureSelectionStrict.comp floorSelectionStrict
  have selectedMeasureTendsto :
      Tendsto (fun n => (sequence (selection n)).2) atTop (nhds limitMeasure) := by
    simpa only [selection, Function.comp_def] using
      measureTendsto.comp floorSelectionStrict.tendsto_atTop
  have selectedFloorTendsto :
      Tendsto (fun n => (sequence (selection n)).1) atTop (nhds limitFloor) := by
    simpa only [selection, Function.comp_def] using floorTendsto
  refine ⟨(limitFloor, limitMeasure), ⟨limitFloorMem, limitMeasureBound⟩,
    selection, selectionStrict, ?_⟩
  rw [Prod.tendsto_iff]
  exact ⟨selectedFloorTendsto, selectedMeasureTendsto⟩

/-- Projective primal convergence for the circle moment hierarchy.

The theorem constructs optimizers at every finite level, extracts a weak-* convergent
optimizer subsequence from the common compact budget box, proves its limit satisfies every
determining moment, and identifies the antitone value limit with the full primal value. -/
theorem projective_primal_convergence
    (budget : ℝ≥0) (moment : ℕ → C(Circle, ℝ)) (target : ℕ → ℝ)
    (fullNonempty : (fullFeasible budget moment target).Nonempty) :
    Antitone (levelFrontier budget moment target) ∧
      Tendsto (levelFrontier budget moment target) atTop
        (nhds (fullFrontier budget moment target)) ∧
      ∃ optimizer : ℕ → PrimalPoint,
        ∃ cluster : PrimalPoint,
          ∃ selection : ℕ → ℕ,
            (∀ N, optimizer N ∈ levelFeasible budget moment target N) ∧
            (∀ N p, p ∈ levelFeasible budget moment target N →
              objective p ≤ objective (optimizer N)) ∧
            StrictMono selection ∧
            Tendsto (optimizer ∘ selection) atTop (nhds cluster) ∧
            cluster ∈ fullFeasible budget moment target ∧
            Tendsto (fun k => objective (optimizer (selection k))) atTop
              (nhds (objective cluster)) ∧
            objective cluster = fullFrontier budget moment target := by
  classical
  have optimizerExists (N : ℕ) :=
    level_optimizer_exists budget moment target fullNonempty N
  let optimizer : ℕ → PrimalPoint := fun N => Classical.choose (optimizerExists N)
  have optimizerMem (N : ℕ) : optimizer N ∈ levelFeasible budget moment target N :=
    (Classical.choose_spec (optimizerExists N)).1
  have optimizerMax (N : ℕ) (p : PrimalPoint)
      (hp : p ∈ levelFeasible budget moment target N) :
      objective p ≤ objective (optimizer N) :=
    (Classical.choose_spec (optimizerExists N)).2 p hp
  have levelGreatest (N : ℕ) :
      IsGreatest (objective '' levelFeasible budget moment target N)
        (objective (optimizer N)) := by
    refine ⟨⟨optimizer N, optimizerMem N, rfl⟩, ?_⟩
    rintro _ ⟨p, hp, rfl⟩
    exact optimizerMax N p hp
  have levelFrontierEq (N : ℕ) :
      levelFrontier budget moment target N = objective (optimizer N) := by
    exact (levelGreatest N).csSup_eq
  have hierarchyAntitone : Antitone (levelFrontier budget moment target) := by
    intro N M hNM
    rw [levelFrontierEq M, levelFrontierEq N]
    exact optimizerMax N (optimizer M)
      (levelFeasible_antitone budget moment target hNM (optimizerMem M))
  have optimizerCommon (N : ℕ) : optimizer N ∈ commonFeasible budget :=
    (optimizerMem N).1
  obtain ⟨cluster, clusterCommon, selection, selectionStrict, optimizerTendsto⟩ :=
    commonFeasible_subsequence budget optimizer optimizerCommon
  have clusterBudget : (reconstruction cluster).mass ≤ budget := by
    exact isClosed_Iic.preimage
      (FiniteMeasure.continuous_mass.comp reconstruction_continuous) |>.mem_of_tendsto
        optimizerTendsto (Eventually.of_forall fun k => (optimizerMem (selection k)).2.1)
  have clusterMoments (k : ℕ) :
      ∫ z, moment k z ∂((reconstruction cluster : FiniteMeasure Circle) : Measure Circle) =
        target k := by
    let constraint : Set PrimalPoint :=
      {p | ∫ z, moment k z ∂((reconstruction p : FiniteMeasure Circle) : Measure Circle) =
        target k}
    have constraintClosed : IsClosed constraint :=
      isClosed_singleton.preimage (moment_evaluation_continuous moment k)
    apply constraintClosed.mem_of_tendsto optimizerTendsto
    have selectedLarge : ∀ᶠ n in atTop, k < selection n := by
      apply selectionStrict.tendsto_atTop.eventually
      filter_upwards [eventually_ge_atTop (k + 1)] with n hn
      omega
    filter_upwards [selectedLarge] with n hn
    exact (optimizerMem (selection n)).2.2 k hn
  have clusterFull : cluster ∈ fullFeasible budget moment target :=
    ⟨clusterCommon, clusterBudget, clusterMoments⟩
  obtain ⟨fullOptimizer, fullOptimizerMem, fullOptimizerMax⟩ :=
    (fullFeasible_isCompact budget moment target).exists_isMaxOn
      fullNonempty objective_continuous.continuousOn
  have fullGreatest :
      IsGreatest (objective '' fullFeasible budget moment target)
        (objective fullOptimizer) := by
    refine ⟨⟨fullOptimizer, fullOptimizerMem, rfl⟩, ?_⟩
    rintro _ ⟨p, hp, rfl⟩
    exact fullOptimizerMax hp
  have fullFrontierEq :
      fullFrontier budget moment target = objective fullOptimizer :=
    fullGreatest.csSup_eq
  have selectedObjectiveTendsto :
      Tendsto (fun k => objective (optimizer (selection k))) atTop
        (nhds (objective cluster)) := by
    exact objective_continuous.continuousAt.tendsto.comp optimizerTendsto
  have selectedFrontierTendsto :
      Tendsto (fun k => levelFrontier budget moment target (selection k)) atTop
        (nhds (objective cluster)) := by
    simpa only [levelFrontierEq] using selectedObjectiveTendsto
  have fullLeSelected (k : ℕ) :
      fullFrontier budget moment target ≤
        levelFrontier budget moment target (selection k) := by
    rw [fullFrontierEq, levelFrontierEq]
    exact optimizerMax (selection k) fullOptimizer
      (fullFeasible_subset_levelFeasible budget moment target (selection k) fullOptimizerMem)
  have fullLeCluster :
      fullFrontier budget moment target ≤ objective cluster :=
    ge_of_tendsto' selectedFrontierTendsto fullLeSelected
  have clusterLeFull : objective cluster ≤ fullFrontier budget moment target := by
    rw [fullFrontierEq]
    exact fullOptimizerMax clusterFull
  have clusterObjectiveEq :
      objective cluster = fullFrontier budget moment target :=
    le_antisymm clusterLeFull fullLeCluster
  have hierarchyTendsto :
      Tendsto (levelFrontier budget moment target) atTop
        (nhds (fullFrontier budget moment target)) := by
    apply (tendsto_iff_tendsto_subseq_of_antitone hierarchyAntitone
      selectionStrict.tendsto_atTop).2
    simpa only [clusterObjectiveEq, Function.comp_def] using selectedFrontierTendsto
  exact ⟨hierarchyAntitone, hierarchyTendsto, optimizer, cluster, selection,
    optimizerMem, optimizerMax, selectionStrict, optimizerTendsto, clusterFull,
    selectedObjectiveTendsto, clusterObjectiveEq⟩

#print axioms mass_bounded_weakStar_subsequence
#print axioms commonFeasible_isCompact
#print axioms levelFeasible_isClosed
#print axioms level_optimizer_exists
#print axioms projective_primal_convergence

end D5.S3.Weil.Budget.ProjectivePrimalConvergence
