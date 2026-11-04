/- GID: D5/S3/Quantum/Completion/RawThreePhaseDescent
   generality: G
   mirror-B: D5/B/S3/Quantum/Completion/RawThreePhaseDescent
   mirror-E: none(waiver:unbounded-original-domain-descent)
   anchors: []
   utility: none
   digest: Nonnegative raw three-phase balance forces marker invariance without magma laws. -/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! Original-domain prerequisites for C133 Continuation V, Theorem 1.3.
No associativity, commutativity, cancellation, marker homomorphism or positivity
of an auxiliary bilinear form is assumed. The complete Hilbert criterion and
radical-fibre collapse are not asserted by this module. -/

noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Completion.RawThreePhaseDescent

/-- The original finite real comparison and its full two-ended balance law. -/
structure RawBalance {M : Type*} [MulOneClass M] (U : M → M) (c : M → M → ℝ) : Prop where
  marker_one : U 1 = 1
  nonneg : ∀ a b, 0 ≤ c a b
  diagonal : ∀ a, c a a = 0
  balance : ∀ a b u v,
    c (a * u) (b * v) + c (a * U u) (b * U v) +
      c (a * U (U u)) (b * U (U v)) = 3 * c a b + 3 * c u v

private lemma recurrence_first_le (s : ℕ → ℝ) (hn : ∀ n, 0 ≤ s n)
    (hr : ∀ n, s (n + 1) + s (n + 2) = 2 * s n) : s 1 ≤ s 0 := by
  by_contra h
  have hd : 0 < s 1 - s 0 := sub_pos.mpr (lt_of_not_ge h)
  have hi : ∀ n : ℕ,
      s (2 * n) ≤ s 0 - (n : ℝ) * (s 1 - s 0) ∧
      s 1 + (n : ℝ) * (s 1 - s 0) ≤ s (2 * n + 1) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        have he := hr (2 * n)
        have ho := hr (2 * n + 1)
        have hn' : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        constructor
        · have hidx : 2 * (n + 1) = 2 * n + 2 := by omega
          rw [hidx]
          push_cast
          nlinarith [ih.1, ih.2]
        · have hidx : 2 * (n + 1) + 1 = (2 * n + 1) + 2 := by omega
          rw [hidx]
          have ho' : s (2 * n + 2) + s (2 * n + 3) = 2 * s (2 * n + 1) := by
            convert ho using 1
          push_cast
          nlinarith [ih.1, ih.2]
  obtain ⟨n, hn'⟩ := exists_nat_gt (s 0 / (s 1 - s 0))
  have hm : s 0 < (n : ℝ) * (s 1 - s 0) := (div_lt_iff₀ hd).mp hn'
  linarith [(hi n).1, hn (2 * n)]

lemma nonnegative_recurrence_constant (s : ℕ → ℝ) (hn : ∀ n, 0 ≤ s n)
    (hr : ∀ n, s (n + 1) + s (n + 2) = 2 * s n) : s 1 = s 0 := by
  have h₁ := recurrence_first_le s hn hr
  have h₂ := recurrence_first_le (fun n => s (n + 1)) (fun n => hn (n + 1))
    (fun n => hr (n + 1))
  have h₀ := hr 0
  norm_num only at h₀ h₂
  linarith

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
  exact nonnegative_recurrence_constant s (fun n => h.nonneg _ _) hr

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

end D5.S3.Quantum.Completion.RawThreePhaseDescent
