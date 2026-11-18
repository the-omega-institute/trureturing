/- GID: D5/S3/Combinatorics/Graph/Pressure/MarkovAdditiveTrajectory
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Pressure/MarkovAdditiveTrajectory
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual trajectory prefix adapter and fixed-initial global Doob path Fisher. -/
import D5.S3.Combinatorics.Graph.Pressure.MarkovAdditiveGlobal
import D5.S3.Combinatorics.Graph.Pressure.MarkovAdditivePaths
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.MarkovPrefixMass
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Moments.Variance
import D5.S3.Quantum.Entanglement.PhaseHistoryBound
import D5.S3.Combinatorics.Graph.LegalWords.MarkovBlockWeight

/-! # Actual finite trajectory laws and global Doob path scores -/
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators Matrix Topology
open Matrix MeasureTheory ProbabilityTheory Preorder

namespace D5.S3.Combinatorics.Graph.Pressure.MarkovAdditive
universe u
variable {V : Type u} [Fintype V] [DecidableEq V] [Nonempty V]

private theorem pathWeight_prod (P : Matrix V V ℝ) (n : ℕ) (w : Fin (n+1) → V) :
    pathWeight P n (w 0) (Fin.tail w) = ∏ i : Fin n, P (w i.castSucc) (w i.succ) := by
  induction n with
  | zero => simp [pathWeight]
  | succ n ih =>
    rw [Fin.prod_univ_succ]
    change P (w 0) (w 1) * pathWeight P n (w 1) (Fin.tail (Fin.tail w)) = _
    have ht := congrArg (fun z : ℝ => P (w 0) (w 1) * z) (ih (Fin.tail w))
    exact ht

def rowPMF (P : Matrix V V ℝ) (hP : P ∈ Matrix.rowStochastic ℝ V) (i : V) : PMF V :=
  PMF.ofFintype (fun j => ENNReal.ofReal (P i j)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => hP.1 i j),
      Matrix.sum_row_of_mem_rowStochastic hP, ENNReal.ofReal_one])

/-- The additive process on actual infinite trajectories, with n transitions. -/
def trajectorySum (g : V → V → ℝ) (n : ℕ) (x : ℕ → V) : ℝ :=
  additiveSum g n (x 0) (fun i => x (i.1+1))

private theorem trajectorySum_succ (g : V → V → ℝ) (n : ℕ) (x : ℕ → V) :
    trajectorySum g (n+1) x = trajectorySum g n x + g (x n) (x (n+1)) := by
  induction n generalizing x with
  | zero => simp [trajectorySum, additiveSum]
  | succ n ih =>
    have hh := congrArg (fun z : ℝ => g (x 0) (x 1) + z) (ih (fun k => x (k+1)))
    simp only [trajectorySum, additiveSum, Fin.tail_def, Fin.val_succ] at hh ⊢
    simpa only [Nat.add_assoc, add_assoc, Fin.val_zero, zero_add] using hh

section Measurable
variable [MeasurableSpace V] [MeasurableSingletonClass V]

def transitionKernel (P : Matrix V V ℝ) (hP : P ∈ Matrix.rowStochastic ℝ V) : Kernel V V :=
  Kernel.ofFunOfCountable (fun i => (rowPMF P hP i).toMeasure)

instance transitionKernel_markov (P : Matrix V V ℝ) (hP : P ∈ Matrix.rowStochastic ℝ V) :
    IsMarkovKernel (transitionKernel P hP) :=
  ⟨fun i => inferInstanceAs (IsProbabilityMeasure (rowPMF P hP i).toMeasure)⟩

namespace Stationary
variable {P : Matrix V V ℝ} (π : Stationary P)

def initialPMF : PMF V := PMF.ofFintype (fun i => ENNReal.ofReal (π.prob i)) (by
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => (π.positive i).le),
    π.total, ENNReal.ofReal_one])

/-- The actual infinite homogeneous trajectory law, with initial row held fixed. -/
def trajectoryLaw (K : Matrix V V ℝ) (hK : K ∈ Matrix.rowStochastic ℝ V) : Measure (ℕ → V) :=
  Kernel.trajMeasure (X := fun _ => V) π.initialPMF.toMeasure
    (fun n => (transitionKernel K hK).comap
      (fun x : ↥(Finset.Iic n) → V => x ⟨n, Finset.mem_Iic.mpr le_rfl⟩)
      (measurable_pi_apply _))

/-- Equality with the actual prefix measure, not merely equality of unnormalized masses. -/
theorem trajectory_prefix_eq (K : Matrix V V ℝ) (hK : K ∈ Matrix.rowStochastic ℝ V)
    (n : ℕ) :
    (π.trajectoryLaw K hK).map (fun x (i : Fin (n+1)) => x i.1) =
      (π.initialPathPMF K hK n).toMeasure.map
        (fun x : V × (Fin n → V) => (Fin.cons x.1 x.2 : Fin (n+1) → V)) := by
  apply Measure.ext_of_singleton
  intro w
  unfold trajectoryLaw
  rw [D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.MarkovPrefixMass.markov_chain_law_map_prefix_apply_singleton]
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton w)]
  have hp : (fun x : V × (Fin n → V) => (Fin.cons x.1 x.2 : Fin (n+1) → V)) ⁻¹' {w} =
      {(w 0, Fin.tail w)} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro h
      apply Prod.ext
      · exact congrFun h 0
      · simpa using congrArg Fin.tail h
    · rintro rfl
      exact Fin.cons_self_tail w
  rw [hp, PMF.toMeasure_apply_singleton (π.initialPathPMF K hK n) _
    (measurableSet_singleton _)]
  have hk (i j : V) : transitionKernel K hK i {j} = ENNReal.ofReal (K i j) :=
    PMF.toMeasure_apply_singleton (rowPMF K hK i) j (measurableSet_singleton j)
  rw [PMF.toMeasure_apply_singleton π.initialPMF _ (measurableSet_singleton _)]
  change ENNReal.ofReal (π.prob (w 0)) *
    (∏ i : Fin n, transitionKernel K hK (w i.castSucc) {w i.succ}) =
      ENNReal.ofReal (π.prob (w 0) * pathWeight K n (w 0) (Fin.tail w))
  rw [ENNReal.ofReal_mul (π.positive _).le, pathWeight_prod]
  congr 1
  rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => hK.1 (w i.castSucc) (w i.succ))]
  exact Finset.prod_congr rfl (fun i _ => hk _ _)


instance trajectoryLaw_probability (K : Matrix V V ℝ) (hK : K ∈ Matrix.rowStochastic ℝ V) :
    IsProbabilityMeasure (π.trajectoryLaw K hK) := by
  unfold trajectoryLaw
  infer_instance

/-- Every finite prefix observable is integrable under the actual infinite law. -/
theorem trajectory_integrable (K : Matrix V V ℝ) (hK : K ∈ Matrix.rowStochastic ℝ V)
    (n : ℕ) (f : (Fin (n+1) → V) → ℝ) :
    Integrable (fun x : ℕ → V => f (fun i => x i.1)) (π.trajectoryLaw K hK) := by
  exact (SimpleFunc.ofFinite f).integrable_of_isFiniteMeasure.comp_measurable
    (by fun_prop)

/-- Finite expectations transported to the actual infinite trajectory measure. -/
theorem trajectory_integral (hP : P ∈ Matrix.rowStochastic ℝ V) (n : ℕ)
    (f : V → (Fin n → V) → ℝ) :
    ∫ x, f (x 0) (fun i => x (i.1+1)) ∂π.trajectoryLaw P hP =
      π.stationaryExpectation n f := by
  let F : (Fin (n+1) → V) → ℝ := fun w => f (w 0) (Fin.tail w)
  have hm : Measurable (fun x : ℕ → V => fun i : Fin (n+1) => x i.1) := by fun_prop
  have hF : StronglyMeasurable F := (measurable_of_countable F).stronglyMeasurable
  change ∫ x, F (fun i => x i.1) ∂π.trajectoryLaw P hP = _
  rw [← integral_map hm.aemeasurable hF.aestronglyMeasurable,
    π.trajectory_prefix_eq P hP n,
    integral_map (measurable_of_countable _).aemeasurable hF.aestronglyMeasurable,
    PMF.integral_eq_sum, Fintype.sum_prod_type]
  unfold stationaryExpectation pathExpectation
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w _
  change (ENNReal.ofReal (π.prob i * pathWeight P n i w)).toReal *
    F (Fin.cons i w) = _
  rw [ENNReal.toReal_ofReal (mul_nonneg (π.positive i).le (pathWeight_nonneg P hP n i w))]
  simp [F, mul_assoc]


private theorem trajectorySum_adapted (g : V → V → ℝ) :
    StronglyAdapted (Filtration.piLE (X := fun _ : ℕ => V)) (trajectorySum g) := by
  intro n
  rw [Filtration.piLE_eq_comap_frestrictLe]
  let F : (↥(Finset.Iic n) → V) → ℝ := fun w =>
    additiveSum g n (w ⟨0, by simp⟩)
      (fun i => w ⟨i.1+1, Finset.mem_Iic.mpr (by omega)⟩)
  have hh : StronglyMeasurable[MeasurableSpace.comap (Preorder.frestrictLe (π := fun _ : ℕ => V) n) inferInstance]
      (F ∘ Preorder.frestrictLe n) :=
    (measurable_of_countable F).stronglyMeasurable.comp_measurable
      (comap_measurable (Preorder.frestrictLe (π := fun _ : ℕ => V) n))
  exact hh

set_option maxHeartbeats 800000 in
-- Conditional-law elaboration keeps the dependent prefix indices explicit.
/-- The corrected process is a martingale for the actual coordinate-history filtration. -/
theorem trajectory_martingale (hP : P ∈ Matrix.rowStochastic ℝ V) (hI : P.IsIrreducible)
    (g : V → V → ℝ) :
    Martingale (trajectorySum (π.score hP hI g))
      (Filtration.piLE (X := fun _ : ℕ => V)) (π.trajectoryLaw P hP) := by
  let μ := π.trajectoryLaw P hP
  let a := π.score hP hI g
  refine martingale_of_condExp_sub_eq_zero_nat (f := trajectorySum a)
    (trajectorySum_adapted a) (fun n => π.trajectory_integrable P hP n
      (fun w => additiveSum a n (w 0) (Fin.tail w))) ?_
  intro n
  have he : (trajectorySum a (n+1) - trajectorySum a n) =
      (fun x : ℕ → V => a (x n) (x (n+1))) := by
    funext x
    simp only [Pi.sub_apply, trajectorySum_succ, add_sub_cancel_left]
  change μ[trajectorySum a (n+1) - trajectorySum a n |
    Filtration.piLE (X := fun _ : ℕ => V) n] =ᵐ[μ] 0
  rw [he, Filtration.piLE_eq_comap_frestrictLe]
  let F : ((↥(Finset.Iic n) → V) × V) → ℝ := fun z =>
    a (z.1 ⟨n, Finset.mem_Iic.mpr le_rfl⟩) z.2
  have hi : Integrable (fun x : ℕ → V => a (x n) (x (n+1))) μ := by
    have hh : Integrable (F ∘ (fun x : ℕ → V => (frestrictLe n x, x (n+1)))) μ :=
      (SimpleFunc.ofFinite F).integrable_of_isFiniteMeasure.comp_measurable
        ((measurable_frestrictLe n).prodMk (measurable_pi_apply (n+1)))
    exact hh
  have hc := condExp_prod_ae_eq_integral_condDistrib
    (μ := μ) (measurable_frestrictLe n) (measurable_pi_apply (n+1)).aemeasurable
    (measurable_of_countable F).stronglyMeasurable hi
  have hk : condDistrib (fun x : ℕ → V => x (n+1)) (Preorder.frestrictLe n) μ =ᵐ[
      μ.map (Preorder.frestrictLe n)]
      (transitionKernel P hP).comap
        (fun w : ↥(Finset.Iic n) → V => w ⟨n, Finset.mem_Iic.mpr le_rfl⟩)
        (measurable_pi_apply _) := Kernel.condDistrib_trajMeasure
  have hk' := ae_of_ae_map (measurable_frestrictLe n).aemeasurable hk
  filter_upwards [hc, hk'] with x hx hkernel
  change μ[(fun x : ℕ → V => F (frestrictLe n x, x (n+1))) |
    MeasurableSpace.comap (frestrictLe n) inferInstance] x = (0 : ℝ)
  rw [hx, hkernel]
  change ∫ j, a (x n) j ∂(rowPMF P hP (x n)).toMeasure = 0
  rw [PMF.integral_eq_sum]
  simpa [rowPMF, ENNReal.toReal_ofReal (hP.1 _ _), smul_eq_mul, a] using
    π.score_centered hP hI g (x n)

/-- The infinite-trajectory integral has the exact finite corrected second moment. -/
theorem trajectory_second_moment (hP : P ∈ Matrix.rowStochastic ℝ V)
    (hI : P.IsIrreducible) (g : V → V → ℝ) (n : ℕ) :
    ∫ x, trajectorySum (π.score hP hI g) n x ^ 2 ∂π.trajectoryLaw P hP =
      (n : ℝ) * π.varianceRate hP hI g := by
  exact (π.trajectory_integral hP n
    (fun i w => additiveSum (π.score hP hI g) n i w ^ 2)).trans
      (π.corrected_second_moment hP hI g n)

private theorem trajectory_variance_eq (hP : P ∈ Matrix.rowStochastic ℝ V)
    (g : V → V → ℝ) (n : ℕ) :
    variance (trajectorySum g n) (π.trajectoryLaw P hP) = π.pathVariance g n := by
  have hm : AEMeasurable (trajectorySum g n) (π.trajectoryLaw P hP) :=
    (show Integrable (trajectorySum g n) (π.trajectoryLaw P hP) from
      π.trajectory_integrable P hP n
        (fun w => additiveSum g n (w 0) (Fin.tail w))).aestronglyMeasurable.aemeasurable
  rw [variance_eq_integral hm,
    show (∫ x, trajectorySum g n x ∂π.trajectoryLaw P hP) =
      π.stationaryExpectation n (additiveSum g n) from π.trajectory_integral hP n _]
  exact π.trajectory_integral hP n (fun i w =>
    (additiveSum g n i w - π.stationaryExpectation n (additiveSum g n)) ^ 2)

/-- The periodic-safe finite variance estimate holds for the actual trajectory integral. -/
theorem trajectory_variance_bound (hP : P ∈ Matrix.rowStochastic ℝ V)
    (hI : P.IsIrreducible) (g : V → V → ℝ) (n : ℕ) :
    |variance (trajectorySum g n) (π.trajectoryLaw P hP) -
      (n : ℝ) * π.varianceRate hP hI g| ≤
      oscillation (π.corrector hP hI g)^2 +
        2 * oscillation (π.secondCorrector hP hI g) * Real.sqrt (π.varianceRate hP hI g) := by
  rw [π.trajectory_variance_eq hP g n]
  exact π.variance_uniform_bound hP hI g n

/-- Actual infinite-law variances converge to the pressure curvature rate. -/
theorem trajectory_variance_tendsto (hP : P ∈ Matrix.rowStochastic ℝ V)
    (hI : P.IsIrreducible) (g : V → V → ℝ) :
    Filter.Tendsto (fun n : ℕ => variance (trajectorySum g n) (π.trajectoryLaw P hP) / n)
      Filter.atTop (nhds (π.varianceRate hP hI g)) := by
  simp_rw [π.trajectory_variance_eq hP g]
  exact π.normalized_variance_tendsto hP hI g

end Stationary
end Measurable

namespace Stationary
variable {P : Matrix V V ℝ} (π : Stationary P)

/-- The probability mass of the global family has exactly the already constructed
local score; initial pi is independent of the tilt parameter. -/
theorem globalDoob_path_score (hP : P ∈ Matrix.rowStochastic ℝ V)
    (hI : P.IsIrreducible) (g : V → V → ℝ) (n : ℕ) (i : V) (w : Fin n → V)
    (hw : 0 < π.prob i * pathWeight P n i w) :
    HasDerivAt (fun t => Real.log ((π.initialPathPMF (π.globalDoob hI g t)
      (π.globalDoob_stochastic hI g t).1 n (i,w)).toReal))
      (additiveSum (π.score hP hI g) n i w) 0 := by
  apply (π.doob_path_score hP hI g n i w hw).congr_of_eventuallyEq
  filter_upwards [π.globalDoob_eq_doob_eventually hP hI g] with t ht
  simp only [initialPathPMF, PMF.ofFintype_apply]
  rw [ENNReal.toReal_ofReal (mul_nonneg (π.positive i).le
    (pathWeight_nonneg _ (π.globalDoob_stochastic hI g t).1 n i w)), ht]


/-- Complete-path classical Fisher for the actual global Doob PMF, with fixed initial pi. -/
def completePathFisher (hI : P.IsIrreducible) (g : V → V → ℝ) (n : ℕ) : ℝ :=
  ∑ x : V × (Fin n → V),
    (π.initialPathPMF (π.globalDoob hI g 0) (π.globalDoob_stochastic hI g 0).1 n x).toReal *
    (deriv (fun t => Real.log ((π.initialPathPMF (π.globalDoob hI g t)
      (π.globalDoob_stochastic hI g t).1 n x).toReal)) 0)^2

/-- Zero-mass paths contribute zero, without differentiating log at zero. -/
theorem completePathFisher_eq (hP : P ∈ Matrix.rowStochastic ℝ V) (hI : P.IsIrreducible)
    (g : V → V → ℝ) (n : ℕ) :
    π.completePathFisher hI g n = (n : ℝ) * π.varianceRate hP hI g := by
  rw [← π.pathFisher_eq hP hI g n]
  have hb : π.globalDoob hI g 0 = P :=
    (π.globalDoob_eq_doob_eventually hP hI g).eq_of_nhds.trans (π.doob_base hP hI g)
  unfold completePathFisher pathFisher
  apply Finset.sum_congr rfl
  intro x _
  have hn := mul_nonneg (π.positive x.1).le (pathWeight_nonneg P hP n x.1 x.2)
  simp only [initialPathPMF, pathPMF, PMF.ofFintype_apply, hb,
    ENNReal.toReal_ofReal hn]
  by_cases hw : 0 < π.prob x.1 * pathWeight P n x.1 x.2
  · have hd := (π.globalDoob_path_score hP hI g n x.1 x.2 hw).deriv
    simp only [initialPathPMF, PMF.ofFintype_apply] at hd
    rw [hd, (π.doob_path_score hP hI g n x.1 x.2 hw).deriv]
  · have hz := le_antisymm (le_of_not_gt hw) hn
    rw [hz, zero_mul, zero_mul]


section MeasurableFisher
variable [MeasurableSpace V] [MeasurableSingletonClass V]

/-- The discrepancy between raw trajectory variance and actual complete-path information
is bounded uniformly in time. -/
theorem trajectory_variance_fisher_bound (hP : P ∈ Matrix.rowStochastic ℝ V)
    (hI : P.IsIrreducible) (g : V → V → ℝ) (n : ℕ) :
    |variance (trajectorySum g n) (π.trajectoryLaw P hP) -
      π.completePathFisher hI g n| ≤ oscillation (π.corrector hP hI g)^2 +
        2 * oscillation (π.secondCorrector hP hI g) * Real.sqrt (π.varianceRate hP hI g) := by
  rw [π.completePathFisher_eq hP hI g n]
  exact π.trajectory_variance_bound hP hI g n

end MeasurableFisher

end Stationary

namespace Born
open D5.S3.Quantum.Entanglement

/-- The source's archive-and-memory path corresponding to an initial bit and future states. -/
def sourcePath : (n : ℕ) → Bool → (Fin n → Bool) → PhaseHistoryBound.Path n
  | 0, i, _ => i
  | n+1, i, w => (i, sourcePath n (w 0) (Fin.tail w))

private theorem sourcePath_head (n : ℕ) (i : Bool) (w : Fin n → Bool) :
    PhaseHistoryBound.head n (sourcePath n i w) = i := by
  cases n <;> rfl

private theorem sourcePath_mass (q : ℝ) (n : ℕ) (i : Bool) (w : Fin n → Bool) :
    PhaseHistoryBound.pathMass q n (sourcePath n i w) =
      pathWeight (PhaseHistoryBound.transition q) n i w := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih =>
    simp only [sourcePath, PhaseHistoryBound.pathMass, sourcePath_head, pathWeight, ih]

private theorem sourcePath_block (q : ℝ) (m : ℕ) (l r : Bool) (w : Fin m → Bool) :
    PhaseHistoryBound.pathMass q (m+1) (sourcePath (m+1) l (Fin.snoc w r)) =
      D5.S3.Combinatorics.Graph.LegalWords.MarkovBlockWeight.pathMass q m l w r := by
  induction m generalizing l with
  | zero => simp [sourcePath, PhaseHistoryBound.pathMass, PhaseHistoryBound.head,
      D5.S3.Combinatorics.Graph.LegalWords.MarkovBlockWeight.pathMass, Fin.snoc_zero]
  | succ m ih =>
    have hw : Fin.snoc w r = Fin.cons (α := fun _ : Fin (m+2) => Bool) (w 0)
        (Fin.snoc (α := fun _ : Fin (m+1) => Bool) (Fin.tail w) r) := by
      rw [Fin.cons_snoc_eq_snoc_cons, Fin.cons_self_tail]
    rw [hw]
    change PhaseHistoryBound.transition q l (w 0) *
      PhaseHistoryBound.pathMass q (m+1)
        (sourcePath (m+1) (w 0) (Fin.snoc (Fin.tail w) r)) =
      PhaseHistoryBound.transition q l (w 0) *
        D5.S3.Combinatorics.Graph.LegalWords.MarkovBlockWeight.pathMass q m
          (w 0) (Fin.tail w) r
    exact congrArg (fun z : ℝ => PhaseHistoryBound.transition q l (w 0) * z)
      (ih (w 0) (Fin.tail w))

/-- The actual source circuit realizes the stationary full-path PMF and the unnormalized
fixed-exterior block weights. The latter use m+1 transitions. -/
theorem actual_circuit_path_laws (q : ℝ) (hq : 0 < q) (hq1 : q < 1) (φ : ℕ → ℝ)
    (π : Stationary (PhaseHistoryBound.transition q))
    (hP : PhaseHistoryBound.transition q ∈ Matrix.rowStochastic ℝ Bool) :
    ∃ U : ℕ → SequentialRegisterCircuit.Unitary (Bool × Bool),
      (∀ t i j k, U t (SequentialRegisterCircuit.basis (false, i)) (j,k) =
        PhaseHistoryBound.step q (φ t) (j,k) i) ∧
      (∀ n i (w : Fin n → Bool),
        ∑ j, π.prob j * ‖SequentialRegisterCircuit.circuit U n 0
          (SequentialRegisterCircuit.blankState false n j)
          (PhaseHistoryBound.register n (sourcePath n i w))‖^2 =
            (π.pathPMF hP n (i,w)).toReal) ∧
      (∀ m l r (w : Fin m → Bool),
        ‖SequentialRegisterCircuit.circuit U (m+1) 0
          (SequentialRegisterCircuit.blankState false (m+1) l)
          (PhaseHistoryBound.register (m+1) (sourcePath (m+1) l (Fin.snoc w r)))‖^2 =
            D5.S3.Combinatorics.Graph.LegalWords.MarkovBlockWeight.pathMass q m l w r) := by
  obtain ⟨U, hU, hc, hm, _⟩ := PhaseHistoryBound.actual_source_moments q hq hq1 φ
  refine ⟨U, hU, ?_, ?_⟩
  · intro n i w
    simp_rw [hc, hm, sourcePath_head]
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    change π.prob i * PhaseHistoryBound.pathMass q n (sourcePath n i w) =
      (ENNReal.ofReal (π.prob i * pathWeight (PhaseHistoryBound.transition q) n i w)).toReal
    rw [sourcePath_mass, ENNReal.toReal_ofReal
      (mul_nonneg (π.positive i).le (pathWeight_nonneg _ hP n i w))]
  · intro m l r w
    rw [hc, hm, sourcePath_head, if_pos rfl, sourcePath_block]

private theorem sourcePath_register_snoc : ∀ (n : ℕ) (i j : Bool) (w : Fin n → Bool),
    PhaseHistoryBound.register (n+1) (sourcePath (n+1) i (Fin.snoc w j)) =
      (Fin.cons i w, j) := by
  intro n
  induction n with
  | zero =>
    intro i j w
    have hw : w = Fin.elim0 := Subsingleton.elim _ _
    subst w
    rfl
  | succ n ih =>
    intro i j w
    have he : Fin.snoc w j = Fin.cons (α := fun _ : Fin (n+2) => Bool) (w 0)
        (Fin.snoc (α := fun _ : Fin (n+1) => Bool) (Fin.tail w) j) := by
      rw [Fin.cons_snoc_eq_snoc_cons, Fin.cons_self_tail]
    rw [he]
    change (SequentialRegisterCircuit.headRest (n+1)).symm
      (i, PhaseHistoryBound.register (n+1)
        (sourcePath (n+1) (w 0) (Fin.snoc (Fin.tail w) j))) = _
    rw [ih]
    simp [SequentialRegisterCircuit.headRest, Fin.cons_self_tail, Fin.consEquiv]

end Born

private theorem pathWeight_snoc (K : Matrix V V ℝ) (n : ℕ) (i j : V)
    (w : Fin n → V) :
    pathWeight K (n+1) i (Fin.snoc w j) = pathWeight K n i w * K (endpoint n i w) j := by
  induction n generalizing i with
  | zero => simp [pathWeight, endpoint, Fin.snoc_zero]
  | succ n ih =>
    have he : Fin.snoc w j = Fin.cons (α := fun _ : Fin (n+2) => V) (w 0)
        (Fin.snoc (α := fun _ : Fin (n+1) => V) (Fin.tail w) j) := by
      rw [Fin.cons_snoc_eq_snoc_cons, Fin.cons_self_tail]
    rw [he]
    change K i (w 0) * pathWeight K (n+1) (w 0) (Fin.snoc (Fin.tail w) j) =
      K i (w 0) * pathWeight K n (w 0) (Fin.tail w) * K (endpoint n (w 0) (Fin.tail w)) j
    rw [ih]
    ring

namespace Stationary
variable {P : Matrix V V ℝ} (π : Stationary P)

/-- The actual archive masses after the last state of an (n+1)-transition path is discarded. -/
def archiveMass (K : Matrix V V ℝ) (n : ℕ) (i : V) (w : Fin n → V) : ℝ :=
  ∑ j, π.prob i * pathWeight K (n+1) i (Fin.snoc w j)

private theorem archive_marginal (K : Matrix V V ℝ)
    (hK : K ∈ Matrix.rowStochastic ℝ V) (n : ℕ) (i : V) (w : Fin n → V) :
    π.archiveMass K n i w = π.prob i * pathWeight K n i w := by
  simp only [archiveMass, pathWeight_snoc, ← mul_assoc, ← Finset.mul_sum]
  rw [Matrix.sum_row_of_mem_rowStochastic hK, mul_one]

/-- Classical Fisher of the observed archive, with the reference initial law fixed. -/
def archiveFisher (hI : P.IsIrreducible) (g : V → V → ℝ) (n : ℕ) : ℝ :=
  ∑ x : V × (Fin n → V), π.archiveMass (π.globalDoob hI g 0) n x.1 x.2 *
    (deriv (fun t => Real.log (π.archiveMass (π.globalDoob hI g t) n x.1 x.2)) 0)^2

/-- Discarding the final memory removes exactly one transition's information.
Here n+1 gates leave an archive of n+1 states, hence n observed transitions. -/
theorem archive_information_loss (hP : P ∈ Matrix.rowStochastic ℝ V)
    (hI : P.IsIrreducible) (g : V → V → ℝ) (n : ℕ) :
    π.archiveFisher hI g n = n * π.varianceRate hP hI g ∧
    π.completePathFisher hI g (n+1) - π.archiveFisher hI g n = π.varianceRate hP hI g := by
  have he : π.archiveFisher hI g n = π.completePathFisher hI g n := by
    unfold archiveFisher completePathFisher
    apply Finset.sum_congr rfl
    intro x _
    simp_rw [π.archive_marginal _ (π.globalDoob_stochastic hI g _).1]
    have hm (t : ℝ) :
        ((π.initialPathPMF (π.globalDoob hI g t)
          (π.globalDoob_stochastic hI g t).1 n) x).toReal =
        π.prob x.1 * pathWeight (π.globalDoob hI g t) n x.1 x.2 := by
      simp only [initialPathPMF, PMF.ofFintype_apply,
        ENNReal.toReal_ofReal (mul_nonneg (π.positive x.1).le
          (pathWeight_nonneg _ (π.globalDoob_stochastic hI g t).1 n x.1 x.2))]
    simp_rw [hm]
  rw [he, π.completePathFisher_eq hP hI g n,
    π.completePathFisher_eq hP hI g (n+1)]
  constructor
  · rfl
  · push_cast
    ring

end Stationary

namespace Born
open D5.S3.Quantum.Entanglement

/-- Computational-basis archive and final-memory coordinates realize the full and marginal laws. -/
theorem actual_circuit_archive_law (q : ℝ) (hq : 0 < q) (hq1 : q < 1) (φ : ℕ → ℝ)
    {R : Matrix Bool Bool ℝ} (π : Stationary R)
    (hP : Matrix.of (PhaseHistoryBound.transition q) ∈ Matrix.rowStochastic ℝ Bool) :
    ∃ U : ℕ → SequentialRegisterCircuit.Unitary (Bool × Bool),
      (∀ n i (w : Fin n → Bool) j,
        ∑ k, π.prob k * ‖SequentialRegisterCircuit.circuit U (n+1) 0
          (SequentialRegisterCircuit.blankState false (n+1) k) (Fin.cons i w,j)‖^2 =
        π.prob i * pathWeight (Matrix.of (PhaseHistoryBound.transition q))
          (n+1) i (Fin.snoc w j)) ∧
      (∀ n i (w : Fin n → Bool),
        ∑ j, ∑ k, π.prob k * ‖SequentialRegisterCircuit.circuit U (n+1) 0
          (SequentialRegisterCircuit.blankState false (n+1) k) (Fin.cons i w,j)‖^2 =
        π.prob i * pathWeight (Matrix.of (PhaseHistoryBound.transition q)) n i w) := by
  obtain ⟨U, _, hc, hm, _⟩ := PhaseHistoryBound.actual_source_moments q hq hq1 φ
  have hf (n : ℕ) (i : Bool) (w : Fin n → Bool) (j : Bool) :
      (∑ k, π.prob k * ‖SequentialRegisterCircuit.circuit U (n+1) 0
        (SequentialRegisterCircuit.blankState false (n+1) k) (Fin.cons i w,j)‖^2) =
      π.prob i * pathWeight (Matrix.of (PhaseHistoryBound.transition q))
        (n+1) i (Fin.snoc w j) := by
    rw [← sourcePath_register_snoc n i j w]
    simp_rw [hc, hm, sourcePath_head]
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    rw [sourcePath_mass]
    rfl
  refine ⟨U, hf, ?_⟩
  intro n i w
  simp_rw [hf]
  exact π.archive_marginal _ hP n i w

end Born

end D5.S3.Combinatorics.Graph.Pressure.MarkovAdditive
