/- GID: D5/S1/Digit/Infinite/CriticalPrefixSeparation
   generality: I
   mirror-B: D5/B/S1/Digit/Infinite/CriticalPrefixSeparation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Sharp prefix separation and critical closed-error recovery for actual finite-tail addresses. -/

import D5.S1.Digit.Infinite.ClosedObservationGraphRealization
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Topology.Instances.Discrete
import Mathlib.Tactic.FinCases

set_option autoImplicit false

namespace D5.S1.Digit.Infinite.CriticalPrefixSeparation

open D5.S1.Digit.Infinite.SuccessorContinuity (LegalDigits)
open D5.S1.Digit.Infinite.ClosedObservationCommonTailWidthModel
open D5.S1.Digit.Infinite.ClosedObservationGraphRealization
open D5.S0.Carrier (GoldenInt)
open D5.S1.Scale (embedding)
open Filter Set
open scoped Topology

/-- The first h actual three-bit windows. -/
def prefix (h : ℕ) (x : LegalDigits) : Fin h → Label := fun j => window x j

/-- The h+1 real samples obtained by deleting three actual bits per step. -/
noncomputable def response (h : ℕ) (x : LegalDigits) : Fin (h + 1) → ℝ :=
  fun j => kappa (bitShift x (3 * j.val))

/-- The legal infinite repetition of the window five. -/
def fiveStream : LegalDigits := ⟨fun j => decide (j % 3 = 2), by
  intro j
  simp only [decide_eq_true_eq]
  omega⟩

/-- N windows five followed by an infinite empty tail. -/
def fiveRun (N : ℕ) : LegalDigits :=
  ⟨fun j => decide (j < 3 * N ∧ j % 3 = 2), by
    intro j
    simp only [decide_eq_true_eq]
    omega⟩

/-- The actual observation domain for the finite-tail closed-error contract. -/
def observations (h : ℕ) (ε : ℝ) : Set (Fin (h + 1) → ℝ) :=
  {r | ∃ x : LegalDigits, finiteTail x ∧ dist r (response h x) ≤ ε}

/-- Correctness requires every compatible source to have the returned prefix. -/
def correct (h : ℕ) (ε : ℝ)
    (decode : observations h ε → (Fin h → Label)) : Prop :=
  ∀ (r : observations h ε) (x : LegalDigits), finiteTail x →
    dist r.val (response h x) ≤ ε → decode r = prefix h x

private theorem golden_facts : 0 < t ∧ t < 1 ∧ t ^ 2 + t = 1 ∧ 1 + g = 2 * t := by
  have hp : 0 < t := inv_pos.mpr Real.goldenRatio_pos
  have hl : t < 1 := inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio
  have hs : t ^ 2 + t = 1 := by
    dsimp [t, D5.S1.Digit.Infinite.SignedSeriesRange.alpha]
    rw [Real.inv_goldenRatio]
    nlinarith [Real.goldenConj_sq]
  refine ⟨hp, hl, hs, ?_⟩
  dsimp [g]
  nlinarith [congrArg (fun z : ℝ => t * z) hs]

private theorem shift_shift (x : LegalDigits) (m n : ℕ) :
    bitShift (bitShift x m) n = bitShift x (m + n) := by
  apply Subtype.ext
  funext j
  simp only [bitShift, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

private theorem residual (x : LegalDigits) (j : ℕ) :
    kappa (bitShift x (3 * j)) + g * kappa (bitShift x (3 * (j + 1))) =
      offset (window x j) := by
  have hr := (closed_observation_graph_realization.2.2.1 (bitShift x (3 * j))).1
  have hw : window (bitShift x (3 * j)) 0 = window x j := by
    simp only [window, Nat.mul_zero, shift_shift, Nat.add_zero]
  rw [hw] at hr
  simp only [originalT, shift_shift, Nat.mul_add, Nat.mul_one] at hr
  dsimp only [branch] at hr
  linarith

private theorem label_gap (l m : Label) (hne : l ≠ m) :
    t ^ 2 ≤ |offset l - offset m| := by
  have ht := golden_facts
  have hhalf : (1 : ℝ) / 2 < t := by nlinarith [ht.2.2.1]
  have hln0 := l.property 0 (by decide)
  have hln1 := l.property 1 (by decide)
  have hmn0 := m.property 0 (by decide)
  have hmn1 := m.property 1 (by decide)
  have hext : (l.val 0 = m.val 0 ∧ l.val 1 = m.val 1 ∧ l.val 2 = m.val 2) → l = m := by
    rintro ⟨h0,h1,h2⟩
    apply Subtype.ext
    funext i
    fin_cases i <;> assumption
  cases hl0 : l.val 0 <;> cases hl1 : l.val 1 <;> cases hl2 : l.val 2 <;>
    cases hm0 : m.val 0 <;> cases hm1 : m.val 1 <;> cases hm2 : m.val 2 <;>
    simp only [hl0, hl1, hl2, hm0, hm1, hm2, Bool.false_eq_true,
      not_false_eq_true, and_self, not_true_eq_false, and_false, false_and] at hln0 hln1 hmn0 hmn1
  all_goals try contradiction
  all_goals try exact False.elim (hne (hext (by simp [hl0,hl1,hl2,hm0,hm1,hm2])))
  all_goals dsimp only [offset]
  all_goals simp only [hl0,hl1,hl2,hm0,hm1,hm2, Bool.false_eq_true, ↓reduceIte]
  all_goals rw [abs_sub_le_iff] at *
  all_goals first | exact (le_abs_self _).trans' (by nlinarith [ht.2.2.1])
                 | exact (neg_le_abs _).trans' (by nlinarith [ht.2.2.1])

private theorem separation (h : ℕ) (x y : LegalDigits) (hne : prefix h x ≠ prefix h y) :
    t / 2 ≤ dist (response h x) (response h y) := by
  classical
  obtain ⟨j, hj⟩ : ∃ j : Fin h, window x j ≠ window y j := by
    by_contra hh
    push_neg at hh
    exact hne (funext hh)
  let M := dist (response h x) (response h y)
  have h0 : |kappa (bitShift x (3 * j.val)) - kappa (bitShift y (3 * j.val))| ≤ M := by
    exact dist_le_pi_dist (response h x) (response h y) ⟨j.val, by omega⟩
  have h1 : |kappa (bitShift x (3 * (j.val + 1))) -
      kappa (bitShift y (3 * (j.val + 1)))| ≤ M := by
    exact dist_le_pi_dist (response h x) (response h y) ⟨j.val + 1, by omega⟩
  have hg : 0 ≤ g := (pow_pos golden_facts.1 3).le
  have hres : offset (window x j) - offset (window y j) =
      (kappa (bitShift x (3 * j.val)) - kappa (bitShift y (3 * j.val))) +
      g * (kappa (bitShift x (3 * (j.val + 1))) -
        kappa (bitShift y (3 * (j.val + 1)))) := by
    linarith [residual x j, residual y j]
  have hu : |offset (window x j) - offset (window y j)| ≤ (1 + g) * M := by
    rw [hres]
    calc
      _ ≤ |kappa (bitShift x (3 * j.val)) - kappa (bitShift y (3 * j.val))| +
          |g * (kappa (bitShift x (3 * (j.val + 1))) -
            kappa (bitShift y (3 * (j.val + 1))))| := abs_add_le _ _
      _ ≤ M + g * M := by rw [abs_mul, abs_of_nonneg hg]; gcongr
      _ = (1 + g) * M := by ring
  have hl := label_gap _ _ hj
  rw [golden_facts.2.2.2] at hu
  have hp := golden_facts.1
  nlinarith

end D5.S1.Digit.Infinite.CriticalPrefixSeparation
