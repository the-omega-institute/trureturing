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

/-! # Actual finite trajectory laws and global Doob path scores -/
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators Matrix Topology
open Matrix MeasureTheory ProbabilityTheory

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

end Stationary
end D5.S3.Combinatorics.Graph.Pressure.MarkovAdditive
