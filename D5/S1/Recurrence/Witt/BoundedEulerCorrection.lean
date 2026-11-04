/- GID: D5/S1/Recurrence/Witt/BoundedEulerCorrection
   generality: G
   mirror-B: D5/B/S1/Recurrence/Witt/BoundedEulerCorrection
   mirror-E: none(waiver:formal-series-no-numerical-evidence)
   anchors: []
   utility: none
   digest: Every integer ghost weight has a unique bounded positive-index correction to an integral formal exponential. -/

/- admission_basis: escape-witness. Proposed content: the strong proper-divisor recursion simultaneously constructs the bounded residue and integral Euler account; bounded_ledger_unique proves positive-index rigidity by strong induction. The Mobius identity and logarithmic bound consume this account. utility none: symbolic unbounded mathematics, no finite checker or certified instance. Reused frozen owners: PrimitiveEulerLedger and HannaDiagonalGhostPowerIntegrality; no new generic Euler factorization. All novelty claims remain unverified. -/


import D5.S1.Recurrence.Witt.HannaDiagonalGhostPowerIntegrality
import Mathlib.NumberTheory.Harmonic.Bounds

noncomputable section

namespace D5.S1.Recurrence.Witt.BoundedEulerCorrection

open Finset PowerSeries
open D5.S1.Recurrence.Witt.HannaDiagonalGhostPowerIntegrality
open D5.S1.Recurrence.Algebraic.HannaLogarithmicPowerClosure (IntegralSeries)

/-- The proper-divisor recursion selects an integer Euler exponent at every degree.
The entry at zero is irrelevant to the represented product. -/
def ledger (w : ℕ → ℤ) (n : ℕ) : ℤ :=
  Nat.strongRecOn n fun n rec =>
    (w n - ∑ d : n.properDivisors,
      (d.1 : ℤ) * rec d.1 ((Nat.mem_properDivisors.mp d.2).2)) / (n : ℤ)

def properGhost (c : ℕ → ℤ) (n : ℕ) : ℤ :=
  ∑ d ∈ n.properDivisors, (d : ℤ) * c d

def correction (w : ℕ → ℤ) (n : ℕ) : ℤ :=
  (w n - properGhost (ledger w) n) % (n : ℤ)

/-- No condition is imposed on the unused entry at zero. -/
def IsCorrection (w a : ℕ → ℤ) : Prop :=
  (∀ n, 0 < n → 0 ≤ a n ∧ a n < (n : ℤ)) ∧
    IntegralSeries (exponentialSum (fun n => ((w n - a n : ℤ) : ℚ)))

private theorem ledger_eq (w : ℕ → ℤ) (n : ℕ) :
    ledger w n = (w n - properGhost (ledger w) n) / (n : ℤ) := by
  unfold ledger
  rw [Nat.strongRecOn_eq]
  change (w n - ∑ d : ↥n.properDivisors, (d.1 : ℤ) * ledger w d.1) / (n : ℤ) = _
  rw [show (∑ d : ↥n.properDivisors, (d.1 : ℤ) * ledger w d.1) =
    ∑ d ∈ n.properDivisors, (d : ℤ) * ledger w d from
    Finset.sum_coe_sort n.properDivisors (fun d => (d : ℤ) * ledger w d)]
  rfl

private theorem divisorGhost_eq (c : ℕ → ℤ) (n : ℕ) (hn : 0 < n) :
    divisorGhost c n = properGhost c n + (n : ℤ) * c n := by
  rw [divisorGhost, ← Nat.cons_self_properDivisors hn.ne', Finset.sum_cons]
  simp only [properGhost]
  ring

/-- The residue construction solves the divisor-sum equation over the integers. -/
theorem correction_equation (w : ℕ → ℤ) (n : ℕ) (hn : 0 < n) :
    w n - correction w n = divisorGhost (ledger w) n := by
  rw [divisorGhost_eq _ _ hn, ledger_eq]
  have h := Int.emod_add_mul_ediv (w n - properGhost (ledger w) n) (n : ℤ)
  dsimp only [correction]
  nlinarith

private theorem correction_bounds (w : ℕ → ℤ) (n : ℕ) (hn : 0 < n) :
    0 ≤ correction w n ∧ correction w n < (n : ℤ) := by
  have hnZ : (0 : ℤ) < n := by exact_mod_cast hn
  exact ⟨Int.emod_nonneg _ hnZ.ne', Int.emod_lt_of_pos _ hnZ⟩

/-- An actual formal exponential, with the constructed correction, has integer
coefficients. The reverse integrality bridge is reused from its canonical owner. -/
theorem correction_integral (w : ℕ → ℤ) : IsCorrection w (correction w) := by
  refine ⟨correction_bounds w, ?_⟩
  apply gauss_exponential_integral
  have hg := divisor_ghost_gauss (ledger w)
  intro p hp k m hm
  have hleft := correction_equation w (m * p ^ (k + 1))
    (Nat.mul_pos hm (pow_pos hp.pos _))
  have hright := correction_equation w (m * p ^ k)
    (Nat.mul_pos hm (pow_pos hp.pos _))
  dsimp only
  rw [hleft, hright]
  exact hg p hp k m hm

private theorem bounded_ledger_unique (w a c : ℕ → ℤ)
    (ha : ∀ n, 0 < n → 0 ≤ a n ∧ a n < (n : ℤ))
    (hc : ∀ n, 0 < n → w n - a n = divisorGhost c n) :
    ∀ n, 0 < n → a n = correction w n ∧ c n = ledger w n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    have hp : properGhost c n = properGhost (ledger w) n := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [(ih d ((Nat.mem_properDivisors.mp hd).2)
        (Nat.pos_of_mem_properDivisors hd)).2]
    have he := hc n hn
    rw [divisorGhost_eq c n hn, hp] at he
    have hres : a n = correction w n := by
      have h : w n - properGhost (ledger w) n = a n + (n : ℤ) * c n := by
        linarith
      rw [correction, h, Int.add_emod, Int.mul_emod_right, add_zero, Int.emod_emod,
        Int.emod_eq_of_lt (ha n hn).1 (ha n hn).2]
    refine ⟨hres, ?_⟩
    have he' := correction_equation w n hn
    rw [divisorGhost_eq _ _ hn] at he'
    rw [hres] at he
    have hm : (n : ℤ) * c n = (n : ℤ) * ledger w n := by linarith
    exact mul_left_cancel₀ (by exact_mod_cast hn.ne' : (n : ℤ) ≠ 0) hm

/-- Uniqueness holds exactly on positive indices, without fixing `a 0`. -/
theorem correction_unique (w a : ℕ → ℤ) (ha : IsCorrection w a) :
    ∀ n, 0 < n → a n = correction w n := by
  obtain ⟨c, hc⟩ := integral_input_ledger _ ha.2
  have hcZ : ∀ n, 0 < n → w n - a n = divisorGhost c n := by
    intro n hn
    exact_mod_cast hc n hn
  intro n hn
  exact (bounded_ledger_unique w a c ha.1 hcZ n hn).1

/-- The uncorrected Möbius transform; at power weights this is the Jordan sum. -/
def moebiusTransform (w : ℕ → ℤ) (n : ℕ) : ℤ :=
  ∑ d ∈ n.divisors, ArithmeticFunction.moebius (n / d) * w d

/-- Exact inversion of the constructed, rather than postulated, divisor account. -/
theorem moebius_identity (w : ℕ → ℤ) (n : ℕ) (hn : 0 < n) :
    (n : ℤ) * ledger w n = moebiusTransform w n -
      ∑ d ∈ n.divisors, ArithmeticFunction.moebius (n / d) * correction w d := by
  have hsum : ∀ (m : ℕ), 0 < m →
      ∑ d ∈ m.divisors, (d : ℤ) * ledger w d = w m - correction w m := by
    intro m hm
    exact (correction_equation w m hm).symm
  have h := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq.mp hsum) n hn
  simp only [Int.cast_id] at h
  rw [Nat.sum_divisorsAntidiagonal' (fun i j => (ArithmeticFunction.moebius i : ℤ) *
    (w j - correction w j))] at h
  simpa only [moebiusTransform, mul_sub, sum_sub_distrib] using h.symm

private theorem divisor_harmonic_budget (n : ℕ) (hn : 0 < n) :
    (∑ d ∈ n.divisors, (d : ℝ)) / n ≤ 1 + Real.log n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have he : (∑ d ∈ n.divisors, (d : ℝ)) / n =
      ∑ d ∈ n.divisors, (d : ℝ)⁻¹ := by
    rw [← Nat.sum_div_divisors n (fun d => (d : ℝ)), sum_div]
    apply sum_congr rfl
    intro d hd
    have hdn := Nat.dvd_of_mem_divisors hd
    have hdR : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_mem_divisors hd
    have hm : ((n / d : ℕ) : ℝ) * d = n := by
      exact_mod_cast Nat.div_mul_cancel hdn
    apply (div_eq_iff hnR.ne').mpr
    field_simp
    nlinarith
  rw [he]
  calc
    _ ≤ ∑ d ∈ Icc 1 n, (d : ℝ)⁻¹ := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro d hd
        exact mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hd,
          Nat.le_of_dvd hn (Nat.dvd_of_mem_divisors hd)⟩
      · intro d _ _
        exact inv_nonneg.mpr (Nat.cast_nonneg d)
    _ ≤ _ := by
      simpa only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
        using harmonic_le_one_add_log n

/-- Uniform logarithmic error for every integer ghost weight. -/
theorem logarithmic_error (w : ℕ → ℤ) (n : ℕ) (hn : 0 < n) :
    |(ledger w n : ℝ) - (moebiusTransform w n : ℝ) / n| ≤ 1 + Real.log n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  let E : ℤ := ∑ d ∈ n.divisors,
    ArithmeticFunction.moebius (n / d) * correction w d
  have hE : |(E : ℝ)| ≤ ∑ d ∈ n.divisors, (d : ℝ) := by
    calc
      _ ≤ ∑ d ∈ n.divisors,
          |((ArithmeticFunction.moebius (n / d) * correction w d : ℤ) : ℝ)| := by
        simpa only [E, Int.cast_sum] using
          (Finset.abs_sum_le_sum_abs
            (fun d => ((ArithmeticFunction.moebius (n / d) * correction w d : ℤ) : ℝ))
            n.divisors)
      _ ≤ _ := by
        apply sum_le_sum
        intro d hd
        have hb := correction_bounds w d (Nat.pos_of_mem_divisors hd)
        have hb0 : (0 : ℝ) ≤ correction w d := by exact_mod_cast hb.1
        have hble : (correction w d : ℝ) ≤ d := by exact_mod_cast hb.2.le
        have hmu : |(ArithmeticFunction.moebius (n / d) : ℝ)| ≤ 1 := by
          exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n / d)
        rw [Int.cast_mul, abs_mul, abs_of_nonneg hb0]
        nlinarith
  have hi := moebius_identity w n hn
  have hiR : (n : ℝ) * ledger w n = (moebiusTransform w n : ℝ) - E := by
    exact_mod_cast hi
  have he : (ledger w n : ℝ) - (moebiusTransform w n : ℝ) / n = -(E : ℝ) / n := by
    apply (eq_div_iff hnR.ne').mpr
    field_simp
    nlinarith
  rw [he, abs_div, abs_neg, abs_of_pos hnR]
  exact (div_le_div_of_nonneg_right hE hnR.le).trans (divisor_harmonic_budget n hn)

end D5.S1.Recurrence.Witt.BoundedEulerCorrection
