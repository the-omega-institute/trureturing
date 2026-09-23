/- GID: D5/S3/Observer/MetricGeometry/ZeroSumBoxRecovery
   generality: G
   mirror-B: D5/B/S3/Observer/MetricGeometry/ZeroSumBoxRecovery
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Zero-sum box recovery has joint constant four thirds and scalar cost one. -/

import D5.S3.Observer.MeasureSeparation.RobustMinimaxKernelBound
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped BigOperators ENNReal

namespace D5.S3.Observer.MetricGeometry.ZeroSumBoxRecovery

open D5.S3.Observer.MeasureSeparation.RobustMinimaxKernelBound

/-- Three real observations, with the usual function-space supremum norm. -/
abbrev Data := Fin 3 → ℝ

/-- The legal states form the zero-sum plane in the observation space. -/
def State := {x : Data // ∑ i, x i = 0}

/-- All signed coefficient costs representing one coordinate on every legal state. -/
def coefficientCosts (i : Fin 3) : Set ℝ :=
  {c | ∃ a : Data, (∀ x : State, ∑ j, a j * x.val j = x.val i) ∧
    c = ∑ j, |a j|}

/-- Worst-case error over actual state/noise pairs, allowing infinite risk. -/
def recoveryRisk (ε : ℝ) (R : Data → State) : ℝ≥0∞ :=
  worstCaseCost {m : State × Data | ‖m.2‖ ≤ ε}
    (fun m R => ENNReal.ofReal ‖(R (m.1.val + m.2)).val - m.1.val‖) R

/-- Subtracting the coordinate mean always returns a legal state. -/
def meanProjection (z : Data) : State :=
  ⟨fun i => z i - (∑ j, z j) / 3, by
    simp only [Fin.sum_univ_three]
    ring⟩

/-- Each scalar task has cost one, but one jointly legal reconstruction has sharp
worst-case error `4ε/3`, even when arbitrary nonlinear estimators are allowed. -/
theorem zero_sum_box_recovery_sharp (ε : ℝ) (hε : 0 ≤ ε) :
    (∀ i : Fin 3, IsLeast (coefficientCosts i) 1) ∧
    (⨆ i : Fin 3, sInf (coefficientCosts i)) = 1 ∧
    (∀ x : State, (meanProjection x.val).val = x.val) ∧
    (∀ e : Data, ‖(meanProjection e).val‖ ≤ (4 / 3 : ℝ) * ‖e‖) ∧
    (⨅ R : Data → State, recoveryRisk ε R) = ENNReal.ofReal ((4 / 3 : ℝ) * ε) ∧
    recoveryRisk ε meanProjection = ENNReal.ofReal ((4 / 3 : ℝ) * ε) := by
  classical
  have scalar : ∀ i : Fin 3, IsLeast (coefficientCosts i) 1 := by
    intro i
    constructor
    · refine ⟨fun j => if j = i then 1 else 0, ?_, ?_⟩
      · intro x
        simp
      · simp only [apply_ite abs, abs_one, abs_zero]
        simp
    · rintro c ⟨a, ha, rfl⟩
      fin_cases i
      · have hv := ha ⟨![1, -1, 0], by
          norm_num [Fin.sum_univ_three, Matrix.cons_val_two, Fin.ext_iff]⟩
        norm_num [Fin.sum_univ_three, Matrix.cons_val_two, Fin.ext_iff] at hv ⊢
        linarith [le_abs_self (a 0), neg_le_abs (a 1), abs_nonneg (a 2)]
      · have hv := ha ⟨![-1, 1, 0], by
          norm_num [Fin.sum_univ_three, Matrix.cons_val_two, Fin.ext_iff]⟩
        norm_num [Fin.sum_univ_three, Matrix.cons_val_two, Fin.ext_iff] at hv ⊢
        linarith [neg_le_abs (a 0), le_abs_self (a 1), abs_nonneg (a 2)]
      · have hv := ha ⟨![-1, 0, 1], by
          norm_num [Fin.sum_univ_three, Matrix.cons_val_two, Fin.ext_iff]⟩
        norm_num [Fin.sum_univ_three, Matrix.cons_val_two, Fin.ext_iff] at hv ⊢
        linarith [neg_le_abs (a 0), abs_nonneg (a 1), le_abs_self (a 2)]
  have scalarSup : (⨆ i : Fin 3, sInf (coefficientCosts i)) = 1 := by
    simp only [fun i => (scalar i).csInf_eq, ciSup_const]
  have exactOnStates : ∀ x : State, (meanProjection x.val).val = x.val := by
    intro x
    funext i
    simp [meanProjection, x.property]
  have projectionBound : ∀ e : Data,
      ‖(meanProjection e).val‖ ≤ (4 / 3 : ℝ) * ‖e‖ := by
    intro e
    have hb (i : Fin 3) : -‖e‖ ≤ e i ∧ e i ≤ ‖e‖ :=
      abs_le.mp (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm e i)
    apply (pi_norm_le_iff_of_nonneg (by positivity)).2
    intro i
    simp only [meanProjection, Real.norm_eq_abs, Fin.sum_univ_three]
    fin_cases i <;> dsimp only <;> apply abs_le.mpr <;>
      constructor <;> linarith! [(hb 0).1, (hb 0).2, (hb 1).1, (hb 1).2,
        (hb 2).1, (hb 2).2]
  have lower : ∀ R : Data → State,
      ENNReal.ofReal ((4 / 3 : ℝ) * ε) ≤ recoveryRisk ε R := by
    intro R
    let z : Data := fun _ => -ε / 3
    let candidates : Fin 3 → State := fun i =>
      ⟨fun j => if j = i then -4 * ε / 3 else 2 * ε / 3, by
        have split (j : Fin 3) :
            (if j = i then -4 * ε / 3 else 2 * ε / 3) =
              2 * ε / 3 + (if j = i then -2 * ε else 0) := by
          split_ifs <;> ring
        simp_rw [split]
        simp [Finset.sum_add_distrib]
        ring⟩
    have sameDatum (i : Fin 3) :
        ‖z - (candidates i).val‖ = ε ∧
        (candidates i).val + (z - (candidates i).val) = z := by
      constructor
      · apply le_antisymm
        · apply (pi_norm_le_iff_of_nonneg hε).2
          intro j
          change |(-ε / 3) - (if j = i then -4 * ε / 3 else 2 * ε / 3)| ≤ ε
          split_ifs <;> apply abs_le.mpr <;> constructor <;> linarith
        · have hi := norm_le_pi_norm (z - (candidates i).val) i
          have diag : (z - (candidates i).val) i = ε := by
            simp [z, candidates]
            ring
          simpa only [diag, Real.norm_eq_abs, abs_of_nonneg hε] using hi
      · exact add_sub_cancel _ _
    have nonnegative : ∃ i : Fin 3, 0 ≤ (R z).val i := by
      by_contra hn
      push Not at hn
      have hz := (R z).property
      simp only [Fin.sum_univ_three] at hz
      linarith [hn 0, hn 1, hn 2]
    obtain ⟨i, hi⟩ := nonnegative
    have errorLower : (4 / 3 : ℝ) * ε ≤ ‖(R z).val - (candidates i).val‖ := by
      have hcoord := norm_le_pi_norm ((R z).val - (candidates i).val) i
      have hdiag : ((R z).val - (candidates i).val) i = (R z).val i + 4 * ε / 3 := by
        simp [candidates]
        ring
      rw [hdiag, Real.norm_eq_abs] at hcoord
      linarith [le_abs_self ((R z).val i + 4 * ε / 3)]
    calc
      ENNReal.ofReal ((4 / 3 : ℝ) * ε) ≤
          ENNReal.ofReal ‖(R z).val - (candidates i).val‖ :=
        ENNReal.ofReal_le_ofReal errorLower
      _ ≤ recoveryRisk ε R := by
        unfold recoveryRisk worstCaseCost
        apply le_iSup_of_le
          (⟨(candidates i, z - (candidates i).val), (sameDatum i).1.le⟩ :
            {m : State × Data | ‖m.2‖ ≤ ε})
        simp only [(sameDatum i).2, le_refl]
  have upper : recoveryRisk ε meanProjection ≤ ENNReal.ofReal ((4 / 3 : ℝ) * ε) := by
    unfold recoveryRisk worstCaseCost
    apply iSup_le
    rintro ⟨⟨x, e⟩, he⟩
    apply ENNReal.ofReal_le_ofReal
    have errorEq : (meanProjection (x.val + e)).val - x.val =
        (meanProjection e).val := by
      funext i
      simp [meanProjection, Finset.sum_add_distrib, x.property]
      ring
    rw [errorEq]
    exact (projectionBound e).trans (mul_le_mul_of_nonneg_left he (by norm_num))
  refine ⟨scalar, scalarSup, exactOnStates, projectionBound, ?_, le_antisymm upper (lower _)⟩
  exact le_antisymm ((iInf_le _ meanProjection).trans upper) (le_iInf lower)

#print axioms zero_sum_box_recovery_sharp

end D5.S3.Observer.MetricGeometry.ZeroSumBoxRecovery
