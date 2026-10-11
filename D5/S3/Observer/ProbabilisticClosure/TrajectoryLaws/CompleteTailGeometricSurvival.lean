/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/CompleteTailGeometricSurvival
   generality: I
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/CompleteTailGeometricSurvival
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: All-event regular generation bounds two-read survival and noncompletion. -/
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.CompleteTailWeightedDistortion

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Classical
namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.CompleteTailGeometricSurvival
open MeasureTheory ProbabilityTheory Finset Filter Topology
open scoped BigOperators
open FourthSegmentStoppedLaw ConstantSuspensionSeparator

/-- Includes never-completing streams as well as words longer than the cut. -/
def survivalEvent (n : ℕ) : Set RawTail := {t | match t with
  | none => True
  | some w => n < w.length}

private theorem prefix_survival (b : Letter) (n : ℕ) :
    prefixRaw b ⁻¹' survivalEvent (n+1) = survivalEvent n := by
  ext t
  cases t <;> simp [prefixRaw, survivalEvent]

private theorem recursion {X Y : Type*} [Fintype X] [Fintype Y]
    (R : RegularTable X Y) (n : ℕ) :
    (∀ x, (R.Q x).real (survivalEvent (n+1)) =
      (1-R.u x)*∑ y, R.B x y*(R.W y).real (survivalEvent n)) ∧
    (∀ y, (R.W y).real (survivalEvent (n+1)) =
      R.v y*∑ x, R.A y x*(R.Q x).real (survivalEvent n)) := by
  constructor
  · intro x
    rw [R.q_generate, prefix_survival]
    simp [survivalEvent]
  · intro y
    rw [R.w_generate, prefix_survival]
    simp [survivalEvent]

private theorem two_step {X Y : Type*} [Fintype X] [Fintype Y]
    (R : RegularTable X Y) (n : ℕ) (d : ℝ) (hd : 0 ≤ d)
    (hq : ∀ x, (R.Q x).real (survivalEvent n) ≤ d)
    (hw : ∀ y, (R.W y).real (survivalEvent n) ≤ d) :
    (∀ x, (R.Q x).real (survivalEvent (n+2)) ≤ (4/15)*d) ∧
    (∀ y, (R.W y).real (survivalEvent (n+2)) ≤ (4/15)*d) := by
  have w1 (y : Y) : (R.W y).real (survivalEvent (n+1)) ≤ (2/5)*d := by
    rw [(recursion R n).2]
    calc
      _ ≤ R.v y*∑ x, R.A y x*d := mul_le_mul_of_nonneg_left
        (sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hq x) (R.A_nonneg y x))
        (by have h := (R.v_box y).1; linarith)
      _ = R.v y*d := by rw [← sum_mul,R.A_sum,one_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right (R.v_box y).2 hd
  have q1 (x : X) : (R.Q x).real (survivalEvent (n+1)) ≤ (2/3)*d := by
    rw [(recursion R n).1]
    calc
      _ ≤ (1-R.u x)*∑ y, R.B x y*d := mul_le_mul_of_nonneg_left
        (sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (hw y) (R.B_nonneg x y))
        (by have h := (R.u_box x).2; linarith)
      _ = (1-R.u x)*d := by rw [← sum_mul,R.B_sum,one_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right (by have h := (R.u_box x).1; linarith) hd
  constructor
  · intro x
    rw [show n+2 = (n+1)+1 by omega,(recursion R (n+1)).1]
    calc
      _ ≤ (1-R.u x)*∑ y, R.B x y*((2/5)*d) := mul_le_mul_of_nonneg_left
        (sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (w1 y) (R.B_nonneg x y))
        (by have h := (R.u_box x).2; linarith)
      _ = (1-R.u x)*((2/5)*d) := by rw [← sum_mul,R.B_sum,one_mul]
      _ ≤ (2/3)*((2/5)*d) := mul_le_mul_of_nonneg_right
        (by have h := (R.u_box x).1; linarith) (by positivity)
      _ = _ := by ring
  · intro y
    rw [show n+2 = (n+1)+1 by omega,(recursion R (n+1)).2]
    calc
      _ ≤ R.v y*∑ x, R.A y x*((2/3)*d) := mul_le_mul_of_nonneg_left
        (sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (q1 x) (R.A_nonneg y x))
        (by have h := (R.v_box y).1; linarith)
      _ = R.v y*((2/3)*d) := by rw [← sum_mul,R.A_sum,one_mul]
      _ ≤ (2/5)*((2/3)*d) := mul_le_mul_of_nonneg_right (R.v_box y).2 (by positivity)
      _ = _ := by ring

/-- Geometric survival and zero noncompletion follow from the actual complete-event equations. -/
theorem regular_complete_survival {X Y : Type*} [Fintype X] [Fintype Y]
    (R : RegularTable X Y) :
    (∀ n : ℕ, (∀ x, (R.Q x).real (survivalEvent (2*n)) ≤ (4/15 : ℝ)^n) ∧
      (∀ y, (R.W y).real (survivalEvent (2*n)) ≤ (4/15 : ℝ)^n)) ∧
    (∀ x, R.Q x {none} = 0) ∧ (∀ y, R.W y {none} = 0) := by
  haveI (x : X) : IsProbabilityMeasure (R.Q x) := R.Qprob x
  haveI (y : Y) : IsProbabilityMeasure (R.W y) := R.Wprob y
  have hg (n : ℕ) :
      (∀ x, (R.Q x).real (survivalEvent (2*n)) ≤ (4/15 : ℝ)^n) ∧
      (∀ y, (R.W y).real (survivalEvent (2*n)) ≤ (4/15 : ℝ)^n) := by
    induction n with
    | zero =>
      constructor
      · intro z
        simpa only [pow_zero,probReal_univ] using
          (measureReal_mono (μ := R.Q z) (Set.subset_univ (survivalEvent (2*0))))
      · intro z
        simpa only [pow_zero,probReal_univ] using
          (measureReal_mono (μ := R.W z) (Set.subset_univ (survivalEvent (2*0))))
    | succ n ih =>
      have h := two_step R (2*n) ((4/15 : ℝ)^n) (by positivity) ih.1 ih.2
      rw [show 2*(n+1) = 2*n+2 by omega,pow_succ]
      simpa only [mul_comm] using h
  have hn (P : Measure RawTail) [IsProbabilityMeasure P]
      (h : ∀ n, P.real (survivalEvent (2*n)) ≤ (4/15 : ℝ)^n) : P {none} = 0 := by
    have ht : Tendsto (fun n : ℕ => (4/15 : ℝ)^n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    have he (n : ℕ) : P.real {none} ≤ (4/15 : ℝ)^n :=
      (measureReal_mono (by intro t ht; simpa [survivalEvent,Set.mem_singleton_iff.mp ht])).trans (h n)
    have hz : P.real {none} = 0 := le_antisymm (le_of_tendsto_of_tendsto tendsto_const_nhds ht (Eventually.of_forall he)) measureReal_nonneg
    exact ((ENNReal.toReal_eq_zero_iff (P {none})).mp hz).resolve_right (measure_ne_top _ _)
  exact ⟨hg,(fun x => hn (R.Q x) (fun n => (hg n).1 x)),
    (fun y => hn (R.W y) (fun n => (hg n).2 y))⟩
end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.CompleteTailGeometricSurvival
