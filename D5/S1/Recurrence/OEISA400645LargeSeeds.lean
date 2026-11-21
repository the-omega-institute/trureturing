/- GID: D5/S1/Recurrence/OEISA400645LargeSeeds
   generality: G
   mirror-B: D5/B/S1/Recurrence/OEISA400645LargeSeeds
   mirror-E: none(waiver:symbolic-proof-no-numeric-artifact)
   anchors: []
   utility: none
   digest: For every seed with a_1 <= a_2 <= a_3 the signed A400645 rule has nonnegative radicands, and a_n = c λ^n + O(1) with c > 0 unless the seed is (0,0,0,0) or (1,1,1,1). -/

/-
admission_basis: escape-witness (the-omega-institute/trureturing-requests#351)
escape_witness: mono_rad (from index four the sequence is nondecreasing and every radicand is
  at least a_n^2, without assuming a_3 <= a_4: the first radicand gives a_5 >= max(a_3, a_4) and
  the cancelling term is then dominated by a_(n-1) or a_(n-2)), growth (once a term reaches
  three, the next increments are positive: the radicand at k + 3 is at most (7/4 a_(k+3))^2 and
  the next radicand exceeds (a_(k+4) + 1/2)^2), escape (every other seed reaches three: a run of
  twos gives the radicand 8 and the next term 3, and a zero followed by three ones gives the
  radicand 3 and the next term 2), stall (the two constant seeds have radicand 2 c^2 and stay
  constant), and asymptotic (the squares satisfy the characteristic recurrence with forcing
  √s + 1/4, the window comparisons 8/7 over three terms and 9/10 over two terms hold
  eventually, and the reusable analytic core gives a_n^2 = L r^n + O(r^(n/2))).
proof_shape:
  rad3, round_err3: bind-only helpers; consumers: every lemma below.
  round_sqrt_eq: bind-only helper; consumer: round_val3.
  round_val3: bind-only helper; consumers: stall, escape.
  ge_of_sq_le: bind-only helper; consumers: a3_le_a5, mono_rad.
  a3_le_a5: bind-only helper; consumers: mono_rad, escape.
  mono_le, monoR: bind-only helpers (induction over mono_rad); consumers: growth, escape,
    unbounded, asymptotic.
  mono_rad: content (monotonicity from index four and the radicand lower bound by strong
    induction); consumers: mono_le, escape, asymptotic, result.
  growth, escape, stall, unbounded, asymptotic: content; consumers: unbounded, asymptotic,
    result.
  result: content.
Direct frozen dependencies (module statement_id):
  D5/S1/Recurrence/OEISA400645 (radicand, squaredLimit, limitingRatio, r_bounds),
    sha256:6b9935aa3f2f34c16302ab77311ac7fb8824542a3447a5f9a6013494c199e7aa;
  D5/S1/Recurrence/OEISA400645BoundedError (charPoly, charPoly_sum, rootMultiplicity_charPoly,
    other_roots; made public here for reuse, pin rewritten by the canonical writer);
  D5/S1/Recurrence/RoundedNormBoundedError (analytic, finish, not_bounded_geom; made public
    here for reuse, pin rewritten by the canonical writer).
Search record (§3.1): D5/S1/Recurrence/OEISA400645 and OEISA400645BoundedError treat only the
  seed (0, 0, 0, 1); OEISA400645FixedLagGrowth gives fixed-lag limits for that seed; no D5
  declaration quantifies over seeds of the signed rule; pinned Mathlib has no rounded-norm
  recurrences.
-/

import D5.S1.Recurrence.OEISA400645BoundedError
import D5.S1.Recurrence.RoundedNormBoundedError

set_option autoImplicit false

noncomputable section

/-! # The signed A400645 rule for every seed with `a 1 ≤ a 2 ≤ a 3`

Let `a 1 ≤ a 2 ≤ a 3`, let `a 4` be arbitrary, and let
`a (n + 1) = round √(a n ² + a (n-1)² + a (n-2)² - a (n-3)²)` for `n ≥ 4`. Every radicand is
nonnegative. The seeds `(0, 0, 0, 0)` and `(1, 1, 1, 1)` give constant
sequences; every other seed gives `a n = c λ^n + O(1)` with `c > 0` and
`a (n + 1) / a n = λ + O(λ^(-n))`, where `λ = limitingRatio`.
-/

namespace D5.S1.Recurrence.OEISA400645LargeSeeds

open Polynomial Asymptotics Filter
open D5.S1.Recurrence.OEISA400645 (radicand squaredLimit limitingRatio r_bounds)
open D5.S1.Recurrence.OEISA400645BoundedError (charPoly charPoly_sum rootMultiplicity_charPoly
  other_roots)
open D5.S1.Recurrence.RoundedNormBoundedError (analytic finish not_bounded_geom)

section

variable {a : ℕ → ℕ}

private theorem rad3 (k : ℕ) :
    (radicand a (k + 3) : ℝ) = (a (k + 3) : ℝ) ^ 2 + (a (k + 2) : ℝ) ^ 2 + (a (k + 1) : ℝ) ^ 2 -
      (a k : ℝ) ^ 2 := by
  simp only [radicand, show k + 3 - 1 = k + 2 by omega, show k + 3 - 2 = k + 1 by omega,
    show k + 3 - 3 = k by omega]
  push_cast
  ring

private theorem round_sqrt_eq {s : ℝ} {m : ℤ} (hm : (1 : ℝ) / 2 ≤ m)
    (h1 : ((m : ℝ) - 1 / 2) ^ 2 ≤ s) (h2 : s < ((m : ℝ) + 1 / 2) ^ 2) :
    round (Real.sqrt s) = m := by
  rw [round_eq, Int.floor_eq_iff]
  have hs1 : (m : ℝ) - 1 / 2 ≤ Real.sqrt s := Real.le_sqrt_of_sq_le h1
  have hs2 : Real.sqrt s < (m : ℝ) + 1 / 2 := (Real.sqrt_lt' (by linarith)).mpr h2
  constructor <;> linarith

variable (hrec : ∀ n, 4 ≤ n → (a (n + 1) : ℤ) = round (Real.sqrt (radicand a n : ℝ)))
include hrec

private theorem round_err3 (k : ℕ) (hk : 1 ≤ k) :
    |(a (k + 4) : ℝ) - Real.sqrt (radicand a (k + 3) : ℝ)| ≤ 1 / 2 := by
  have h := abs_sub_round (Real.sqrt (radicand a (k + 3) : ℝ))
  have h0 := hrec (k + 3) (by omega)
  rw [show k + 3 + 1 = k + 4 by omega] at h0
  rw [← h0, abs_sub_comm] at h
  exact_mod_cast h

private theorem round_val3 (k : ℕ) (hk : 1 ≤ k) {m : ℕ}
    (h1 : ((m : ℝ) - 1 / 2) ^ 2 ≤ (radicand a (k + 3) : ℝ))
    (h2 : (radicand a (k + 3) : ℝ) < ((m : ℝ) + 1 / 2) ^ 2) (hm : 1 ≤ m) : a (k + 4) = m := by
  have h := hrec (k + 3) (by omega)
  rw [show k + 3 + 1 = k + 4 by omega] at h
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hr := round_sqrt_eq (s := (radicand a (k + 3) : ℝ)) (m := (m : ℤ))
    (by push_cast; linarith) (by push_cast; exact h1) (by push_cast; exact h2)
  rw [hr] at h
  exact_mod_cast h

/-- A term whose square is at most the radicand is at most the next term. -/
private theorem ge_of_sq_le (k : ℕ) (hk : 1 ≤ k) (y : ℕ)
    (hy : (y : ℝ) ^ 2 ≤ radicand a (k + 3)) : y ≤ a (k + 4) := by
  have h := (abs_le.mp (round_err3 hrec k hk)).1
  have hle : (y : ℝ) ≤ Real.sqrt (radicand a (k + 3)) := Real.le_sqrt_of_sq_le hy
  have : (y : ℝ) < a (k + 4) + 1 := by linarith
  have : y < a (k + 4) + 1 := by exact_mod_cast this
  omega

variable (h12 : a 1 ≤ a 2) (h23 : a 2 ≤ a 3)
include h12 h23

omit h23 in
private theorem a3_le_a5 : a 3 ≤ a 5 := by
  have h := ge_of_sq_le hrec 1 le_rfl (a 3) (by
    rw [rad3, show 1 + 3 = 4 from rfl, show 1 + 2 = 3 from rfl, show 1 + 1 = 2 from rfl]
    have : (a 1 : ℝ) ≤ a 2 := by exact_mod_cast h12
    nlinarith [sq_nonneg (a 4 : ℝ), (Nat.cast_nonneg (a 1) : (0 : ℝ) ≤ _)])
  exact h

/-- From index four the sequence is nondecreasing and every radicand is at least `a n ^ 2`. -/
private theorem mono_rad :
    ∀ n, 4 ≤ n → a n ≤ a (n + 1) ∧ (a n : ℝ) ^ 2 ≤ radicand a n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
    have hprev : (a k : ℝ) ≤ a (k + 1) ∨ (a k : ℝ) ≤ a (k + 2) := by
      rcases Nat.lt_or_ge k 4 with hlt | hge
      · have hk1 : 1 ≤ k := by omega
        interval_cases k
        · left; exact_mod_cast h12
        · left; exact_mod_cast h23
        · right; exact_mod_cast a3_le_a5 hrec h12
      · left; exact_mod_cast (ih k (by omega) hge).1
    have hrad : (a (k + 3) : ℝ) ^ 2 ≤ radicand a (k + 3) := by
      rw [rad3]
      have h0 : (0 : ℝ) ≤ a k := Nat.cast_nonneg _
      rcases hprev with h | h <;>
        nlinarith [sq_nonneg (a (k + 1) : ℝ), sq_nonneg (a (k + 2) : ℝ)]
    exact ⟨ge_of_sq_le hrec k (by omega) _ hrad, hrad⟩

private theorem mono_le {m n : ℕ} (hm : 4 ≤ m) (hmn : m ≤ n) : a m ≤ a n := by
  induction n, hmn using Nat.le_induction with
  | base => exact le_rfl
  | succ n hn ih => exact ih.trans (mono_rad hrec h12 h23 n (by omega)).1

private theorem monoR {m n : ℕ} (hm : 4 ≤ m) (hmn : m ≤ n) : (a m : ℝ) ≤ a n := by
  exact_mod_cast mono_le hrec h12 h23 hm hmn

/-- Growth: once `a (k + 3) ≥ 3`, the next two terms increase strictly. -/
private theorem growth (k : ℕ) (hk : 3 ≤ k) (h3 : 3 ≤ a (k + 3)) : a (k + 4) < a (k + 5) := by
  set y : ℝ := (a (k + 3) : ℝ) with hy
  have hy3 : (3 : ℝ) ≤ y := by rw [hy]; exact_mod_cast h3
  have m1 := monoR hrec h12 h23 (m := k + 1) (n := k + 3) (by omega) (by omega)
  have m2 := monoR hrec h12 h23 (m := k + 2) (n := k + 3) (by omega) (by omega)
  have m3 := monoR hrec h12 h23 (m := k + 1) (n := k + 2) (by omega) (by omega)
  have hr3 : (radicand a (k + 3) : ℝ) ≤ (7 / 4 * y) ^ 2 := by
    rw [rad3]
    have h0 : (0 : ℝ) ≤ a (k + 1) := Nat.cast_nonneg _
    nlinarith [sq_nonneg (a k : ℝ)]
  have hs3 : Real.sqrt (radicand a (k + 3) : ℝ) ≤ 7 / 4 * y :=
    Real.sqrt_le_iff.mpr ⟨by linarith, hr3⟩
  have e1 := (abs_le.mp (round_err3 hrec k (by omega))).2
  have hx : (a (k + 4) : ℝ) ≤ 7 / 4 * y + 1 / 2 := by linarith
  have hx0 : (0 : ℝ) ≤ a (k + 4) := Nat.cast_nonneg _
  have hr4 : ((a (k + 4) : ℝ) + 1 / 2) ^ 2 < (radicand a (k + 1 + 3) : ℝ) := by
    rw [rad3, show k + 1 + 3 = k + 4 by omega, show k + 1 + 2 = k + 3 by omega]
    nlinarith
  have hs4 : (a (k + 4) : ℝ) + 1 / 2 < Real.sqrt (radicand a (k + 1 + 3) : ℝ) :=
    (Real.lt_sqrt (by linarith)).mpr hr4
  have e2 := (abs_le.mp (round_err3 hrec (k + 1) (by omega))).1
  rw [show k + 1 + 4 = k + 5 by omega] at e2
  have : (a (k + 4) : ℝ) < a (k + 5) := by linarith
  exact_mod_cast this

/-- The two stationary seeds give constant sequences. -/
private theorem stall (hs : a 1 = a 3 ∧ a 3 = a 4 ∧ a 4 ≤ 1) : ∀ n, 1 ≤ n → a n = a 1 := by
  obtain ⟨h13, h34, h41⟩ := hs
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    rcases Nat.lt_or_ge n 5 with hlt | hge
    · interval_cases n <;> omega
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
      have hk0 := ih k (by omega) (by omega)
      have hk1 := ih (k + 1) (by omega) (by omega)
      have hk2 := ih (k + 2) (by omega) (by omega)
      have hk3 := ih (k + 3) (by omega) (by omega)
      have hrad : (radicand a (k + 3) : ℝ) = 2 * (a 1 : ℝ) ^ 2 := by
        rw [rad3, hk0, hk1, hk2, hk3]; ring
      have ha1 : a 1 = 0 ∨ a 1 = 1 := by omega
      rcases ha1 with h0 | h1
      · have h := hrec (k + 3) (by omega)
        rw [hrad, h0] at h
        simp at h
        rw [show k + 3 + 1 = k + 4 by omega] at h
        omega
      · rw [h1]
        exact round_val3 hrec (k := k) (by omega) (by rw [hrad, h1]; norm_num)
          (by rw [hrad, h1]; norm_num) le_rfl

/-- Any other seed reaches a term of size at least three from index four on. -/
private theorem escape (hs : ¬ (a 1 = a 3 ∧ a 3 = a 4 ∧ a 4 ≤ 1)) : ∃ N, 4 ≤ N ∧ 3 ≤ a N := by
  by_contra hcon
  push Not at hcon
  -- a run of four twos forces a three
  have two : ∀ k, 4 ≤ k → a k = 2 → False := by
    intro k hk h2
    have hw : ∀ i, i ≤ 3 → a (k + i) = 2 := fun i hi => by
      have := mono_le hrec h12 h23 (m := k) (n := k + i) hk (by omega)
      have := hcon (k + i) (by omega)
      omega
    have hrad : (radicand a (k + 3) : ℝ) = 8 := by
      have w0 := hw 0 (by omega); have w1 := hw 1 (by omega); have w2 := hw 2 (by omega)
      have w3 := hw 3 (by omega)
      rw [add_zero] at w0
      rw [rad3, w0, w1, w2, w3]
      norm_num
    have := round_val3 hrec (k := k) (by omega) (m := 3) (by rw [hrad]; norm_num)
      (by rw [hrad]; norm_num) (by norm_num)
    have := hcon (k + 4) (by omega)
    omega
  have hle1 : ∀ n, 4 ≤ n → a n ≤ 1 := fun n hn => by
    have := hcon n hn
    by_contra h
    exact two n hn (by omega)
  -- a zero followed by three ones forces a two
  have win : ∀ k, 1 ≤ k → a k = 0 → a (k + 1) = 1 → a (k + 2) = 1 → a (k + 3) = 1 →
      False := by
    intro k hk h0 h1 h2 h3
    have hrad : (radicand a (k + 3) : ℝ) = 3 := by
      rw [rad3, h1, h2, h3, h0]
      norm_num
    have := round_val3 hrec (k := k) hk (m := 2) (by rw [hrad]; norm_num)
      (by rw [hrad]; norm_num) (by norm_num)
    have := hle1 (k + 4) (by omega)
    omega
  have h35 := a3_le_a5 hrec h12
  have m4 : a 4 ≤ a 5 := (mono_rad hrec h12 h23 4 le_rfl).1
  have m5 : a 5 ≤ a 6 := (mono_rad hrec h12 h23 5 (by omega)).1
  have m6 : a 6 ≤ a 7 := (mono_rad hrec h12 h23 6 (by omega)).1
  have h5 := hle1 5 (by omega)
  have h6 := hle1 6 (by omega)
  have h7 := hle1 7 (by omega)
  have ha5 : a 5 = 1 := by
    by_contra h
    exact hs ⟨by omega, by omega, by omega⟩
  rcases Nat.lt_or_ge (a 4) 1 with ha4 | ha4
  · exact win 4 (by omega) (by omega) (by show a 5 = 1; omega) (by show a 6 = 1; omega)
      (by show a 7 = 1; omega)
  · rcases Nat.lt_or_ge (a 3) 1 with ha3 | ha3
    · exact win 3 (by omega) (by omega) (by show a 4 = 1; omega) (by show a 5 = 1; omega)
        (by show a 6 = 1; omega)
    · have ha1 : a 1 = 0 := by
        by_contra h
        exact hs ⟨by omega, by omega, by omega⟩
      rcases Nat.lt_or_ge (a 2) 1 with ha2 | ha2
      · exact win 2 (by omega) (by omega) (by show a 3 = 1; omega) (by show a 4 = 1; omega)
          (by show a 5 = 1; omega)
      · exact win 1 le_rfl ha1 (by show a 2 = 1; omega) (by show a 3 = 1; omega)
          (by show a 4 = 1; omega)

/-- Once a term from index four on reaches three the sequence tends to infinity. -/
private theorem unbounded (hN : ∃ N, 4 ≤ N ∧ 3 ≤ a N) : ∀ B : ℕ, ∃ M, ∀ n, M ≤ n → B ≤ a n := by
  obtain ⟨N, hN4, hN3⟩ := hN
  set M := N + 3 with hM
  have hge : ∀ n, N ≤ n → 3 ≤ a n := fun n hn =>
    hN3.trans (mono_le hrec h12 h23 hN4 hn)
  have hstep : ∀ i, i ≤ a (M + 1 + i) := by
    intro i
    induction i with
    | zero => exact Nat.zero_le _
    | succ i ih =>
      have := growth hrec h12 h23 (k := N + i) (by omega) (hge _ (by omega))
      rw [show N + i + 4 = M + 1 + i by omega, show N + i + 5 = M + 1 + (i + 1) by omega] at this
      omega
  intro B
  refine ⟨M + 1 + B, fun n hn => ?_⟩
  have := hstep (n - (M + 1))
  rw [show M + 1 + (n - (M + 1)) = n by omega] at this
  omega

/-- The asymptotic conclusion for every sequence that reaches three. -/
private theorem asymptotic (hN : ∃ N, 4 ≤ N ∧ 3 ≤ a N) :
    ∃ c : ℝ, 0 < c ∧
      (fun n => (a n : ℝ) - c * limitingRatio ^ n) =O[atTop] (fun _ => (1 : ℝ)) ∧
      (fun n => (a (n + 1) : ℝ) / a n - limitingRatio) =O[atTop]
        (fun n => (limitingRatio ^ n)⁻¹) := by
  obtain ⟨N₁, hN₁⟩ := unbounded hrec h12 h23 hN 10
  have hbig : ∀ n, N₁ + 1 ≤ n → (10 : ℝ) ≤ a n := fun n hn => by
    exact_mod_cast hN₁ n (by omega)
  have hr := r_bounds
  set R := squaredLimit with hRdef
  have hR : 1 < R := by linarith
  have hsqR : Real.sqrt R < Real.sqrt 2 := Real.sqrt_lt_sqrt (by linarith) (by linarith)
  set b : ℕ → ℝ := fun n => (a n : ℝ) ^ 2 with hbdef
  have hsum : ∀ j, ∑ k ∈ Finset.range (charPoly.natDegree + 1), charPoly.coeff k * b (j + k) =
      ∑ k ∈ Finset.range (charPoly.natDegree + 1), charPoly.coeff k * b (j + k) := fun _ => rfl
  -- the forcing is a rounding error of the radicand
  have he : ∀ᶠ j in atTop,
      |∑ k ∈ Finset.range (charPoly.natDegree + 1), charPoly.coeff k * b (j + k)| ≤
        Real.sqrt (∑ i ∈ Finset.range 4, b (j + i)) + 1 / 4 := by
    refine eventually_atTop.mpr ⟨1, fun j hj => ?_⟩
    rw [charPoly_sum]
    have hs0 := (mono_rad hrec h12 h23 (j + 3) (by omega)).2
    have hsnn : (0 : ℝ) ≤ radicand a (j + 3) := le_trans (sq_nonneg _) hs0
    have herr := abs_le.mp (round_err3 hrec j hj)
    set u := Real.sqrt (radicand a (j + 3) : ℝ) with hu
    have hu0 : 0 ≤ u := Real.sqrt_nonneg _
    have huu : u ^ 2 = radicand a (j + 3) := Real.sq_sqrt hsnn
    have ht0 : (0 : ℝ) ≤ a (j + 4) := Nat.cast_nonneg _
    have hrad := rad3 (a := a) j
    have hS : (radicand a (j + 3) : ℝ) ≤ ∑ i ∈ Finset.range 4, b (j + i) := by
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, hbdef, add_zero, zero_add]
      rw [hrad]
      nlinarith [sq_nonneg (a j : ℝ)]
    have hus : u ≤ Real.sqrt (∑ i ∈ Finset.range 4, b (j + i)) := Real.sqrt_le_sqrt hS
    have hkey : |(a (j + 4) : ℝ) ^ 2 - radicand a (j + 3)| ≤ u + 1 / 4 := by
      rw [← huu, abs_le]
      constructor
      · nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ (a (j + 4) : ℝ) - u + 1 / 2)
          (add_nonneg ht0 hu0)]
      · nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ u + 1 / 2 - (a (j + 4) : ℝ))
          (add_nonneg ht0 hu0)]
    have hform : b j - b (j + 1) - b (j + 2) - b (j + 3) + b (j + 4) =
        (a (j + 4) : ℝ) ^ 2 - radicand a (j + 3) := by
      rw [hrad]; simp only [hbdef]; ring
    rw [hform]
    linarith
  -- upper comparison with window three
  have hup : ∀ᶠ n in atTop, b (n + 3) ≤ 8 / 7 * ∑ i ∈ Finset.range 3, b (n + i) := by
    refine eventually_atTop.mpr ⟨N₁ + 2, fun n hn => ?_⟩
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, hbdef, zero_add,
      show k + 1 + 3 = k + 4 by omega, show k + 1 + 1 = k + 2 by omega,
      show k + 1 + 2 = k + 3 by omega]
    set S := (a (k + 1) : ℝ) ^ 2 + (a (k + 2) : ℝ) ^ 2 + (a (k + 3) : ℝ) ^ 2 with hSdef
    have h10 := hbig (k + 3) (by omega)
    have hS100 : (100 : ℝ) ≤ S := by nlinarith [sq_nonneg (a (k + 1) : ℝ), sq_nonneg (a (k + 2) : ℝ)]
    have hrS : (radicand a (k + 3) : ℝ) ≤ S := by
      rw [rad3, hSdef]; nlinarith [sq_nonneg (a k : ℝ)]
    have hv : Real.sqrt (radicand a (k + 3) : ℝ) ≤ Real.sqrt S := Real.sqrt_le_sqrt hrS
    have hv10 : (10 : ℝ) ≤ Real.sqrt S := by
      rw [show (10 : ℝ) = Real.sqrt 100 by
        rw [show (100 : ℝ) = 10 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt hS100
    have hvv : Real.sqrt S ^ 2 = S := Real.sq_sqrt (by linarith)
    have herr := (abs_le.mp (round_err3 hrec k (by omega))).2
    have ht0 : (0 : ℝ) ≤ a (k + 4) := Nat.cast_nonneg _
    have hle : (a (k + 4) : ℝ) ≤ Real.sqrt S + 1 / 2 := by linarith
    have hsq : (a (k + 4) : ℝ) ^ 2 ≤ (Real.sqrt S + 1 / 2) ^ 2 := pow_le_pow_left₀ ht0 hle 2
    nlinarith
  -- lower comparison with window two
  have hdown : ∀ᶠ n in atTop, 9 / 10 * ∑ i ∈ Finset.range 2, b (n + i) ≤ b (n + 2) := by
    refine eventually_atTop.mpr ⟨N₁ + 6, fun n hn => ?_⟩
    obtain ⟨j, rfl⟩ : ∃ j, n = j + 2 := ⟨n - 2, by omega⟩
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, hbdef, zero_add,
      show j + 2 + 2 = j + 4 by omega, show j + 2 + 1 = j + 3 by omega]
    set T := (a (j + 2) : ℝ) ^ 2 + (a (j + 3) : ℝ) ^ 2 with hTdef
    have h10 := hbig (j + 3) (by omega)
    have hT100 : (100 : ℝ) ≤ T := by nlinarith [sq_nonneg (a (j + 2) : ℝ)]
    have hm := monoR hrec h12 h23 (m := j) (n := j + 1) (by omega) (by omega)
    have hj0 : (0 : ℝ) ≤ a j := Nat.cast_nonneg _
    have hrT : T ≤ (radicand a (j + 3) : ℝ) := by
      rw [rad3, hTdef]; nlinarith
    have hv : Real.sqrt T ≤ Real.sqrt (radicand a (j + 3) : ℝ) := Real.sqrt_le_sqrt hrT
    have hv10 : (10 : ℝ) ≤ Real.sqrt T := by
      rw [show (10 : ℝ) = Real.sqrt 100 by
        rw [show (100 : ℝ) = 10 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt hT100
    have hvv : Real.sqrt T ^ 2 = T := Real.sq_sqrt (by linarith)
    have herr := (abs_le.mp (round_err3 hrec j (by omega))).1
    have hle : Real.sqrt T - 1 / 2 ≤ (a (j + 4) : ℝ) := by linarith
    have hsq : (Real.sqrt T - 1 / 2) ^ 2 ≤ (a (j + 4) : ℝ) ^ 2 :=
      pow_le_pow_left₀ (by linarith) hle 2
    nlinarith
  have hpos : ∀ᶠ n in atTop, 0 < b n := eventually_atTop.mpr ⟨N₁ + 1, fun n hn => by
    have := hbig n hn
    simp only [hbdef]
    positivity⟩
  obtain ⟨L, hL, hO⟩ := analytic charPoly R hR rootMultiplicity_charPoly (m₁ := 3) (m₂ := 2)
    (w := 4) (by norm_num) (K := 8 / 7) (K' := 9 / 10) (c := 2) (c' := 3 / 2) (by norm_num)
    (by norm_num) (by norm_num) (by nlinarith) (by norm_num) (by norm_num)
    (fun z hz hne => ⟨(other_roots z hz hne).trans hsqR, other_roots z hz hne⟩)
    (by simp [Finset.sum_range_succ]; norm_num) (by simp [Finset.sum_range_succ]; norm_num)
    b hup hdown hpos _ hsum he
  obtain ⟨h1, h2⟩ := finish a R hR L hL hO
  exact ⟨Real.sqrt L, Real.sqrt_pos.mpr hL, h1, h2⟩

end

/-- Signed nearest-rounded rule for every seed with `a 1 ≤ a 2 ≤ a 3`. Let
`a (n + 1) = round √(a n ^ 2 + a (n - 1) ^ 2 + a (n - 2) ^ 2 - a (n - 3) ^ 2)` for `n ≥ 4`, with
`a 4` arbitrary. Then every radicand is nonnegative; the seeds `(0, 0, 0, 0)` and `(1, 1, 1, 1)`
give constant sequences; and for every other seed there is `c > 0` with `a n = c λ^n + O(1)` and
`a (n + 1) / a n = λ + O(λ^(-n))`, where `λ = limitingRatio`. The two constant seeds are exactly
the seeds for which the asymptotics fail. -/
theorem result (a : ℕ → ℕ) (h12 : a 1 ≤ a 2) (h23 : a 2 ≤ a 3)
    (hrec : ∀ n, 4 ≤ n → (a (n + 1) : ℤ) = round (Real.sqrt (radicand a n : ℝ))) :
    (∀ n, 4 ≤ n → 0 ≤ radicand a n) ∧
      (a 1 = a 3 ∧ a 3 = a 4 ∧ a 4 ≤ 1 → ∀ n, 1 ≤ n → a n = a 1) ∧
      ((∃ c : ℝ, 0 < c ∧
          (fun n => (a n : ℝ) - c * limitingRatio ^ n) =O[atTop] (fun _ => (1 : ℝ)) ∧
          (fun n => (a (n + 1) : ℝ) / a n - limitingRatio) =O[atTop]
            (fun n => (limitingRatio ^ n)⁻¹)) ↔
        ¬ (a 1 = a 3 ∧ a 3 = a 4 ∧ a 4 ≤ 1)) := by
  refine ⟨fun n hn => ?_, stall hrec h12 h23, ⟨fun hc hs => ?_, fun hs =>
    asymptotic hrec h12 h23 (escape hrec h12 h23 hs)⟩⟩
  · have h := (mono_rad hrec h12 h23 n hn).2
    have : (0 : ℝ) ≤ radicand a n := le_trans (sq_nonneg _) h
    exact_mod_cast this
  · obtain ⟨c, hc0, hO, -⟩ := hc
    have hconst := stall hrec h12 h23 hs
    have hr := r_bounds
    have hlam : 1 < limitingRatio := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_lt_sqrt zero_le_one (by unfold limitingRatio at *; linarith)
    refine not_bounded_geom a (max (a 0) 1) (fun n => ?_) hc0 hlam hO
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact le_max_left _ _
    · rw [hconst n hn]; exact le_max_of_le_right (by omega)

end D5.S1.Recurrence.OEISA400645LargeSeeds
