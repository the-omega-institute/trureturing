/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/StoppingMass
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/StoppingMass
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Biased Bernoulli stopping masses decrease strictly and separate disconnected edges. -/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped BigOperators

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw

/-- A fixed interior bias; competitors may depend on this same parameter. -/
structure Bias where
  p : ℝ
  pos : 0 < p
  lt_one : p < 1
  biased : p ≠ 1 / 2

namespace Bias

def π (β : Bias) (s : Bool) : ℝ := if s then β.p else 1 - β.p

def T (β : Bias) (n : ℕ) : ℝ := (1 - β.p)^n + β.p^n

def d (β : Bias) (n : ℕ) : ℝ := β.T n - β.T (n + 1)

theorem π_pos (β : Bias) (s : Bool) : 0 < β.π s := by
  cases s <;> simp only [π, Bool.false_eq_true, ↓reduceIte]
  · linarith [β.lt_one]
  · exact β.pos

theorem π_sum (β : Bias) : β.π false + β.π true = 1 := by simp [π]

theorem T_one (β : Bias) : β.T 1 = 1 := by simp [T]

theorem T_pos (β : Bias) (n : ℕ) : 0 < β.T n := by
  unfold T
  have := β.pos
  have : 0 < 1 - β.p := by linarith [β.lt_one]
  positivity

theorem d_formula (β : Bias) (n : ℕ) :
    β.d n = (1 - β.p)^n * β.p + β.p^n * (1 - β.p) := by
  simp only [d, T, pow_succ]
  ring

theorem d_pos (β : Bias) (n : ℕ) : 0 < β.d n := by
  rw [d_formula]
  have := β.pos
  have : 0 < 1 - β.p := by linarith [β.lt_one]
  positivity

theorem T_succ_lt (β : Bias) (n : ℕ) : β.T (n + 1) < β.T n := by
  have := β.d_pos n
  unfold d at this
  linarith

theorem T_antitone (β : Bias) : Antitone β.T := by
  exact (strictAnti_nat_of_succ_lt β.T_succ_lt).antitone

theorem tail_telescope (β : Bias) (r n : ℕ) :
    (∑ i ∈ Finset.range n, β.d (r + i + 1)) + β.T (r + n + 1) = β.T (r + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have he : r + (n + 1) + 1 = (r + n + 1) + 1 := by omega
    rw [he]
    simp only [d] at ih ⊢
    linarith

theorem unequal_powers (β : Bias) {n : ℕ} (hn : 0 < n) :
    (1 - β.p)^n ≠ β.p^n := by
  have hn0 : n ≠ 0 := by omega
  have h0 : 0 < 1 - β.p := by linarith [β.lt_one]
  have hne : 1 - β.p ≠ β.p := by intro h; apply β.biased; linarith
  rcases lt_or_gt_of_ne hne with h | h
  · exact ne_of_lt (pow_lt_pow_left₀ h h0.le hn0)
  · exact ne_of_gt (pow_lt_pow_left₀ h β.pos.le hn0)

/-- The strict difference for a detached edge, with a successor exponent to avoid subtraction. -/
theorem detached_gap_factorization (β : Bias) (n : ℕ) :
    β.T (n + 3) - β.T 2 * β.T (n + 2) =
      (1 - β.p) * β.p * ((1 - β.p) - β.p) *
        ((1 - β.p)^(n + 1) - β.p^(n + 1)) := by
  simp only [T, pow_succ]
  ring

theorem detached_gap_pos (β : Bias) (n : ℕ) :
    β.T 2 * β.T (n + 2) < β.T (n + 3) := by
  rw [← sub_pos, detached_gap_factorization]
  have h0 : 0 < 1 - β.p := by linarith [β.lt_one]
  have hne : 1 - β.p ≠ β.p := by intro h; apply β.biased; linarith
  have hprod : 0 < ((1 - β.p) - β.p) *
      ((1 - β.p)^(n + 1) - β.p^(n + 1)) := by
    rcases lt_or_gt_of_ne hne with h | h
    · exact mul_pos_of_neg_of_neg (sub_neg.mpr h)
        (sub_neg.mpr (pow_lt_pow_left₀ h h0.le (by omega)))
    · exact mul_pos (sub_pos.mpr h)
        (sub_pos.mpr (pow_lt_pow_left₀ h β.pos.le (by omega)))
  simpa only [mul_assoc] using mul_pos (mul_pos h0 β.pos) hprod

end Bias
end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw
