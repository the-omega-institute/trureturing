/- GID: D5/S3/Quantum/Completion/ThreePhaseHistoryRigidity
   generality: G
   mirror-B: D5/B/S3/Quantum/Completion/ThreePhaseHistoryRigidity
   mirror-E: none(waiver:all-depth-ordered-histories)
   anchors: []
   utility: none
   digest: Ordered history energy growth and raw balance supply the original Fourier descent. -/

import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import D5.S3.QuadraticForms.ThreeWayBalance

/-! The all-depth finite-history mechanism of C133 Continuation V, Section 3.
The ordered energy-growth estimate is combined with the original raw law and
derived marker readings. Its bounded-increment consumer uses the Archimedean
property in RawAnchoredFourierQuotient.
The phase index is a group; the original label type is only a magma. -/

noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace D5.S3.Quantum.Completion.ThreePhaseHistoryRigidity

/-- All phase words, retaining order and multiplicity even at coincident labels. -/
def PhaseWords : ℕ → Type
  | 0 => Unit
  | n + 1 => PhaseWords n × ZMod 3

instance phaseWordsFintype (n : ℕ) : Fintype (PhaseWords n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype Unit)
  | succ n ih =>
      letI := ih
      exact inferInstanceAs (Fintype (PhaseWords n × ZMod 3))

lemma phaseWords_card (n : ℕ) : Fintype.card (PhaseWords n) = 3 ^ n := by
  induction n with
  | zero =>
      change Fintype.card Unit = 1
      exact Fintype.card_unique
  | succ n ih =>
      calc
        Fintype.card (PhaseWords (n + 1)) = Fintype.card (PhaseWords n × ZMod 3) :=
          Fintype.card_congr (Equiv.refl _)
        _ = Fintype.card (PhaseWords n) * 3 := by rw [Fintype.card_prod, ZMod.card]
        _ = 3 ^ (n + 1) := by rw [ih, pow_succ]

/-- The original binary operation is applied once at each step, with left bracketing. -/
def orderedHistory {M : Type*} [MulOneClass M] (U : M → M) (u : M) :
    (n : ℕ) → PhaseWords n → M
  | 0, _ => 1
  | n + 1, w => orderedHistory U u n w.1 * U^[w.2.val] u

lemma history_mem {M : Type*} [MulOneClass M]
    (U : M → M) (u : M) (N : Set M) (h₁ : (1 : M) ∈ N)
    (hs : ∀ x ∈ N, ∀ k : ZMod 3, x * U^[k.val] u ∈ N)
    (n : ℕ) (w : PhaseWords n) : orderedHistory U u n w ∈ N := by
  induction n with
  | zero => exact h₁
  | succ n ih => exact hs _ (ih w.1) w.2

lemma history_energy_growth {M : Type*} [MulOneClass M]
    (U : M → M) (u : M) (N : Set M) (h₁ : (1 : M) ∈ N)
    (hs : ∀ x ∈ N, ∀ k : ZMod 3, x * U^[k.val] u ∈ N)
    (E : M → ℝ) (d : ℝ)
    (he : ∀ x ∈ N, 3 * (E x + d) ≤ ∑ k : ZMod 3, E (x * U^[k.val] u))
    (n : ℕ) :
    (3 : ℝ) ^ n * (E 1 + (n : ℝ) * d) ≤
      ∑ w : PhaseWords n, E (orderedHistory U u n w) := by
  induction n with
  | zero =>
      simp only [pow_zero, Nat.cast_zero, zero_mul, add_zero, one_mul, orderedHistory]
      simp only [Finset.sum_const, Finset.card_univ, phaseWords_card, pow_zero, one_nsmul]
      exact le_rfl
  | succ n ih =>
      change _ ≤ ∑ w : PhaseWords n × ZMod 3,
        E (orderedHistory U u n w.1 * U^[w.2.val] u)
      rw [Fintype.sum_prod_type]
      have hsum := Finset.sum_le_sum (s := Finset.univ) (fun w _ =>
        he (orderedHistory U u n w) (history_mem U u N h₁ hs n w))
      have hc : (Fintype.card (PhaseWords n) : ℝ) = (3 : ℝ) ^ n := by
        rw [phaseWords_card]; norm_cast
      change (∑ w : PhaseWords n, 3 * (E (orderedHistory U u n w) + d)) ≤
        ∑ w : PhaseWords n, ∑ k : ZMod 3, E (orderedHistory U u n w * U^[k.val] u) at hsum
      simp only [mul_add, Finset.sum_add_distrib, Finset.sum_const,
        Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum] at hsum
      rw [hc] at hsum
      push_cast
      rw [pow_succ]
      nlinarith

end D5.S3.Quantum.Completion.ThreePhaseHistoryRigidity

namespace D5.S3.Quantum.Completion.RawAnchoredRadicalDescent

/-- The original finite real comparison and its full two-ended balance law. -/
structure RawBalance {M : Type*} [MulOneClass M] (U : M → M) (c : M → M → ℝ) : Prop where
  marker_one : U 1 = 1
  nonneg : ∀ a b, 0 ≤ c a b
  diagonal : ∀ a, c a a = 0
  balance : ∀ a b u v,
    c (a * u) (b * v) + c (a * U u) (b * U v) +
      c (a * U (U u)) (b * U (U v)) = 3 * c a b + 3 * c u v

private lemma marker_invariant {M : Type*} [MulOneClass M]
    (U : M → M) (c : M → M → ℝ) (h : RawBalance U c) (u v : M) :
    c (U u) (U v) = c u v := by
  let s : ℕ → ℝ := fun n => c (U^[n] u) (U^[n] v)
  have hr (n : ℕ) : s (n + 1) + s (n + 2) = 2 * s n := by
    have hh := h.balance 1 1 (U^[n] u) (U^[n] v)
    simp only [one_mul, h.diagonal, mul_zero, zero_add] at hh
    change c (U^[n + 1] u) (U^[n + 1] v) +
      c (U^[n + 2] u) (U^[n + 2] v) = 2 * c (U^[n] u) (U^[n] v)
    simp only [Function.iterate_succ_apply']
    linarith
  exact D5.S3.QuadraticForms.ThreeWayBalance.nonneg_recurrence_constant s
    (fun n => h.nonneg _ _) (fun n => by simpa only [add_comm] using hr n)

/-- Both contextual readings and complete rows/columns have marker period three.
The underlying marker itself need not be periodic, surjective or multiplicative. -/
theorem raw_marker_readouts {M : Type*} [MulOneClass M]
    (U : M → M) (c : M → M → ℝ) (h : RawBalance U c) :
    (∀ u v, c (U u) (U v) = c u v) ∧
    (∀ a b u v, c (a * U (U (U u))) (b * U (U (U v))) = c (a * u) (b * v)) ∧
    (∀ u z, c (U (U (U u))) z = c u z ∧ c z (U (U (U u))) = c z u) := by
  have hm := marker_invariant U c h
  have hc (a b u v : M) :
      c (a * U (U (U u))) (b * U (U (U v))) = c (a * u) (b * v) := by
    have h₀ := h.balance a b u v
    have h₁ := h.balance a b (U u) (U v)
    rw [hm] at h₁
    linarith
  refine ⟨hm, hc, ?_⟩
  intro u z
  constructor
  · simpa [h.marker_one] using hc 1 z u 1
  · simpa [h.marker_one] using hc z 1 1 u

end D5.S3.Quantum.Completion.RawAnchoredRadicalDescent
