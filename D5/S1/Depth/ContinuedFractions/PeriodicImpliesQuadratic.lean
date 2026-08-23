/- GID: D5/S1/Depth/ContinuedFractions/PeriodicImpliesQuadratic
   generality: I
   mirror-B: D5/B/S1/Depth/ContinuedFractions/PeriodicImpliesQuadratic
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Lagrange A holds; B and discriminant/class-number/mod-5 work are not covered. -/

import D5.S1.Depth.GoldenContinuedFraction
import Mathlib.Algebra.ContinuedFractions.Computation.TerminatesIffRat
import Mathlib.Tactic

/- Library-search audit trail (2026-08-22):
   * `rg -n -F 'PeriodicImpliesQuadratic' D5 Golden/Frozen/accepted` and the search for
     `eventually_periodic_implies_quadratic` had no public or private theorem hit.
   * Repository searches for `periodic|quadratic|ContFract|完全商` found only concrete periodic
     examples and Gauss-step facts in this directory; none proves Lagrange direction A.
   * Pinned Mathlib searches for `periodic.*quadratic`, `quadratic.*periodic`, and `Lagrange`
     found no continued-fraction classification theorem. Loogle returned 54 declarations for
     `GenContFract.of`, none periodic/quadratic. LeanSearch returned 20 results for the natural
     language query; the closest hit was `GenContFract.terminates_iff_rat`, not Lagrange.
   * Mathlib's `GenContFract.terminates_iff_rat` is reused for irrationality. The integer
     Mobius transfer matrix and its quadratic fixed-point calculation are proved locally. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Depth.ContinuedFractions.PeriodicImpliesQuadratic

/-- An integer linear-fractional transfer, written as four matrix entries. -/
structure MobiusInt where
  a : ℤ
  b : ℤ
  c : ℤ
  d : ℤ

/-- The determinant of an integer linear-fractional transfer. -/
def MobiusInt.det (M : MobiusInt) : ℤ := M.a * M.d - M.b * M.c

/-- Composition of two integer linear-fractional transfers. -/
def MobiusInt.comp (M N : MobiusInt) : MobiusInt where
  a := M.a * N.a + M.b * N.c
  b := M.a * N.b + M.b * N.d
  c := M.c * N.a + M.d * N.c
  d := M.c * N.b + M.d * N.d

/-- The inverse continued-fraction step `y ↦ q + 1 / y`. -/
def MobiusInt.step (q : ℤ) : MobiusInt := ⟨q, 1, 1, 0⟩

/-- The transfer matrix of `length` consecutive continued-fraction steps. -/
def MobiusInt.segment (coefficient : ℕ → ℤ) (start : ℕ) : ℕ → MobiusInt
  | 0 => ⟨1, 0, 0, 1⟩
  | length + 1 =>
      (MobiusInt.step (coefficient start)).comp
        (MobiusInt.segment coefficient (start + 1) length)

/-- Cross-multiplied action of a transfer, avoiding any hidden denominator assumption. -/
def MobiusInt.Rel (M : MobiusInt) (x y : ℝ) : Prop :=
  x * ((M.c : ℝ) * y + M.d) = (M.a : ℝ) * y + M.b

/-- A certified eventually periodic regular continued fraction.

The `GenContFract` field records that the computed coefficient stream is infinite. The complete
quotients separately record the inverse-Gauss recurrence and repeat after a positive period. -/
structure EventuallyPeriodicCF (x : ℝ) where
  coefficient : ℕ → ℤ
  completeQuotient : ℕ → ℝ
  start : ℕ
  period : ℕ
  period_pos : 0 < period
  value_eq : completeQuotient 0 = x
  quotient_ne_zero : ∀ n, completeQuotient n ≠ 0
  inverse_step : ∀ n,
    completeQuotient n =
      (coefficient n : ℝ) + 1 / completeQuotient (n + 1)
  computed_coefficients : ∀ n,
    (GenContFract.of x).s.get? n = some ⟨1, (coefficient (n + 1) : ℝ)⟩
  tail_coefficients_pos : ∀ n, start ≤ n → 0 < coefficient n
  coefficient_periodic : ∀ n,
    coefficient (start + n + period) = coefficient (start + n)
  complete_quotient_periodic : ∀ n,
    completeQuotient (start + n + period) = completeQuotient (start + n)

/-- A real number is quadratic irrational when it is irrational and is annihilated by a
nonzero integer polynomial of degree at most two. -/
def IsQuadraticIrrational (x : ℝ) : Prop :=
  Irrational x ∧
    ∃ a b c : ℤ,
      (a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) ∧
        (a : ℝ) * x ^ 2 + (b : ℝ) * x + c = 0

private theorem rel_comp {M N : MobiusInt} {x y z : ℝ}
    (hM : M.Rel x z) (hN : N.Rel z y) : (M.comp N).Rel x y := by
  simp only [MobiusInt.Rel, MobiusInt.comp, Int.cast_add, Int.cast_mul] at hM hN ⊢
  linear_combination
    ((N.c : ℝ) * y + N.d) * hM + ((M.a : ℝ) - x * M.c) * hN

private theorem segment_rel {x : ℝ} (h : EventuallyPeriodicCF x) (first length : ℕ) :
    (MobiusInt.segment h.coefficient first length).Rel
      (h.completeQuotient first) (h.completeQuotient (first + length)) := by
  induction length generalizing first with
  | zero => simp [MobiusInt.segment, MobiusInt.Rel]
  | succ length ih =>
      rw [MobiusInt.segment]
      apply rel_comp (z := h.completeQuotient (first + 1))
      · simp only [MobiusInt.Rel, MobiusInt.step, Int.cast_one, Int.cast_zero,
          one_mul, add_zero]
        rw [h.inverse_step first]
        field_simp [h.quotient_ne_zero (first + 1)]
      · simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          ih (first + 1)

private theorem det_comp (M N : MobiusInt) : (M.comp N).det = M.det * N.det := by
  simp only [MobiusInt.det, MobiusInt.comp]
  ring

private theorem segment_det (coefficient : ℕ → ℤ) (first length : ℕ) :
    (MobiusInt.segment coefficient first length).det = (-1 : ℤ) ^ length := by
  induction length generalizing first with
  | zero => simp [MobiusInt.segment, MobiusInt.det]
  | succ length ih =>
      rw [MobiusInt.segment, det_comp, ih (first + 1)]
      simp [MobiusInt.det, MobiusInt.step, pow_succ, mul_comm]

private theorem segment_entries_nonneg (coefficient : ℕ → ℤ) (first length : ℕ)
    (hcoeff : ∀ k, k < length → 0 ≤ coefficient (first + k)) :
    let M := MobiusInt.segment coefficient first length
    0 ≤ M.a ∧ 0 ≤ M.b ∧ 0 ≤ M.c ∧ 0 ≤ M.d := by
  induction length generalizing first with
  | zero => simp [MobiusInt.segment]
  | succ length ih =>
      have hq : 0 ≤ coefficient first := by
        simpa using hcoeff 0 (Nat.zero_lt_succ length)
      have htail : ∀ k, k < length → 0 ≤ coefficient (first + 1 + k) := by
        intro k hk
        simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          hcoeff (k + 1) (by omega)
      obtain ⟨ha, hb, hc, hd⟩ := ih (first + 1) htail
      simp only [MobiusInt.segment, MobiusInt.comp, MobiusInt.step, one_mul, zero_mul,
        add_zero]
      exact ⟨add_nonneg (mul_nonneg hq ha) hc, add_nonneg (mul_nonneg hq hb) hd,
        ha, hb⟩

private theorem segment_b_pos (coefficient : ℕ → ℤ) (first length : ℕ)
    (hlength : 0 < length)
    (hcoeff : ∀ k, k < length → 0 < coefficient (first + k)) :
    0 < (MobiusInt.segment coefficient first length).b := by
  induction length generalizing first with
  | zero => omega
  | succ length ih =>
      cases length with
      | zero => simp [MobiusInt.segment, MobiusInt.comp, MobiusInt.step]
      | succ length =>
          have hq : 0 < coefficient first := by
            simpa using hcoeff 0 (by omega)
          have htail : ∀ k, k < length + 1 →
              0 < coefficient (first + 1 + k) := by
            intro k hk
            simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
              hcoeff (k + 1) (by omega)
          have hb := ih (first + 1) (by omega) htail
          have hnonneg := segment_entries_nonneg coefficient (first + 1) (length + 1)
            (fun k hk => (htail k hk).le)
          rw [MobiusInt.segment]
          simp only [MobiusInt.comp, MobiusInt.step, one_mul, zero_mul, add_zero]
          exact add_pos_of_pos_of_nonneg (mul_pos hq hb) hnonneg.2.2.2

private theorem period_segment_b_pos {x : ℝ} (h : EventuallyPeriodicCF x) :
    0 < (MobiusInt.segment h.coefficient h.start h.period).b := by
  apply segment_b_pos h.coefficient h.start h.period h.period_pos
  intro k hk
  exact h.tail_coefficients_pos (h.start + k) (Nat.le_add_right h.start k)

private theorem computed_cf_irrational {x : ℝ} (h : EventuallyPeriodicCF x) :
    Irrational x := by
  rintro ⟨q, rfl⟩
  have hterminates : (GenContFract.of (q : ℝ)).Terminates :=
    (GenContFract.terminates_iff_rat (q : ℝ)).2 ⟨q, rfl⟩
  rcases hterminates with ⟨n, hn⟩
  change (GenContFract.of (q : ℝ)).s.get? n = none at hn
  rw [h.computed_coefficients n] at hn
  simp at hn

private theorem quadratic_transfers_across_segment {x y : ℝ} (M : MobiusInt)
    (hdet : M.det ≠ 0) (hrel : M.Rel x y) (u v w : ℤ)
    (hnonzero : u ≠ 0 ∨ v ≠ 0 ∨ w ≠ 0)
    (hy : (u : ℝ) * y ^ 2 + (v : ℝ) * y + w = 0) :
    ∃ a b c : ℤ,
      (a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) ∧
        (a : ℝ) * x ^ 2 + (b : ℝ) * x + c = 0 := by
  let qa : ℤ := u * M.d ^ 2 - v * M.d * M.c + w * M.c ^ 2
  let qb : ℤ :=
    -2 * u * M.b * M.d + v * (M.b * M.c + M.a * M.d) -
      2 * w * M.a * M.c
  let qc : ℤ := u * M.b ^ 2 - v * M.a * M.b + w * M.a ^ 2
  let U : ℝ := (M.c : ℝ) * x - M.a
  let V : ℝ := (M.b : ℝ) - M.d * x
  have hUV : U * y = V := by
    dsimp [U, V]
    simp only [MobiusInt.Rel] at hrel
    nlinarith [hrel]
  have hsq : U ^ 2 * y ^ 2 = V ^ 2 := by
    calc
      U ^ 2 * y ^ 2 = (U * y) ^ 2 := by ring
      _ = V ^ 2 := by rw [hUV]
  have hlinear : U ^ 2 * y = U * V := by
    calc
      U ^ 2 * y = U * (U * y) := by ring
      _ = U * V := by rw [hUV]
  have hmixed : (v : ℝ) * V * U = (v : ℝ) * (U ^ 2 * y) := by
    rw [hlinear]
    ring
  have htransformed :
      (u : ℝ) * V ^ 2 + (v : ℝ) * V * U + (w : ℝ) * U ^ 2 = 0 := by
    rw [← hsq, hmixed]
    linear_combination U ^ 2 * hy
  refine ⟨qa, qb, qc, ?_, ?_⟩
  · by_contra hzero
    simp only [not_or, not_ne_iff] at hzero
    have hid (t : ℤ) :
        qa * (M.a * t + M.b) ^ 2 +
            qb * (M.a * t + M.b) * (M.c * t + M.d) +
            qc * (M.c * t + M.d) ^ 2 =
          M.det ^ 2 * (u * t ^ 2 + v * t + w) := by
      dsimp [qa, qb, qc, MobiusInt.det]
      ring
    have hdet_sq : M.det ^ 2 ≠ 0 := pow_ne_zero 2 hdet
    have hw_product : M.det ^ 2 * w = 0 := by
      simpa [hzero.1, hzero.2.1, hzero.2.2] using (hid 0).symm
    have hplus_product : M.det ^ 2 * (u + v + w) = 0 := by
      simpa [hzero.1, hzero.2.1, hzero.2.2] using (hid 1).symm
    have hminus_product : M.det ^ 2 * (u + -v + w) = 0 := by
      simpa [hzero.1, hzero.2.1, hzero.2.2] using (hid (-1)).symm
    have hw : w = 0 := (mul_eq_zero.mp hw_product).resolve_left hdet_sq
    have hplus : u + v + w = 0 :=
      (mul_eq_zero.mp hplus_product).resolve_left hdet_sq
    have hminus : u + -v + w = 0 :=
      (mul_eq_zero.mp hminus_product).resolve_left hdet_sq
    have hu : u = 0 := by omega
    have hv : v = 0 := by omega
    rcases hnonzero with hu' | hv' | hw'
    · exact hu' hu
    · exact hv' hv
    · exact hw' hw
  · calc
      (qa : ℝ) * x ^ 2 + (qb : ℝ) * x + qc =
          (u : ℝ) * V ^ 2 + (v : ℝ) * V * U + (w : ℝ) * U ^ 2 := by
            dsimp [qa, qb, qc, U, V]
            push_cast
            ring
      _ = 0 := htransformed

/-- Lagrange direction A: a certified eventually periodic regular continued fraction is a
quadratic irrational. -/
theorem eventually_periodic_cf_implies_quadratic_irrational {x : ℝ}
    (h : EventuallyPeriodicCF x) : IsQuadraticIrrational x := by
  refine ⟨computed_cf_irrational h, ?_⟩
  let periodMatrix := MobiusInt.segment h.coefficient h.start h.period
  let prefixMatrix := MobiusInt.segment h.coefficient 0 h.start
  let y := h.completeQuotient h.start
  have hrepeat := h.complete_quotient_periodic 0
  simp only [Nat.add_zero] at hrepeat
  have hfixed : periodMatrix.Rel y y := by
    have hperiod := segment_rel h h.start h.period
    rw [hrepeat] at hperiod
    exact hperiod
  have htail :
      (periodMatrix.c : ℝ) * y ^ 2 +
          ((periodMatrix.d - periodMatrix.a : ℤ) : ℝ) * y +
          (-periodMatrix.b : ℤ) = 0 := by
    simp only [MobiusInt.Rel] at hfixed
    push_cast
    linear_combination hfixed
  have hperiod_b : 0 < periodMatrix.b := period_segment_b_pos h
  have htail_nonzero :
      periodMatrix.c ≠ 0 ∨ periodMatrix.d - periodMatrix.a ≠ 0 ∨ -periodMatrix.b ≠ 0 :=
    Or.inr (Or.inr (neg_ne_zero.mpr (ne_of_gt hperiod_b)))
  have hprefix : prefixMatrix.Rel x y := by
    have hp := segment_rel h 0 h.start
    rw [h.value_eq] at hp
    simpa only [Nat.zero_add] using hp
  have hprefix_det : prefixMatrix.det ≠ 0 := by
    rw [segment_det]
    exact pow_ne_zero h.start (by norm_num)
  exact quadratic_transfers_across_segment prefixMatrix hprefix_det hprefix
    periodMatrix.c (periodMatrix.d - periodMatrix.a) (-periodMatrix.b)
    htail_nonzero htail

example : IsQuadraticIrrational Real.goldenRatio := by
  apply eventually_periodic_cf_implies_quadratic_irrational
  refine
    { coefficient := fun _ => (1 : ℤ)
      completeQuotient := fun _ => Real.goldenRatio
      start := 0
      period := 1
      period_pos := by omega
      value_eq := rfl
      quotient_ne_zero := fun _ => ne_of_gt (zero_lt_one.trans Real.one_lt_goldenRatio)
      inverse_step := ?_
      computed_coefficients := ?_
      tail_coefficients_pos := ?_
      coefficient_periodic := ?_
      complete_quotient_periodic := ?_ }
  · intro n
    rw [one_div, Real.inv_goldenRatio]
    ring
  · intro n
    simpa using
      D5.S1.Depth.GoldenContinuedFraction.golden_ratio_continued_fraction.2 n
  · intro n hn
    norm_num
  · intro n
    rfl
  · intro n
    rfl

#print axioms eventually_periodic_cf_implies_quadratic_irrational

end D5.S1.Depth.ContinuedFractions.PeriodicImpliesQuadratic
