/- GID: D5/S1/Words/FibonacciMapFirstStart
   generality: I
   mirror-B: D5/B/S1/Words/FibonacciMapFirstStart
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Least starts of longest Fibonacci-word monochromatic progressions. -/

import D5.S1.Words.FibonacciMapBound
import D5.S1.Scale.Fibonacci
import D5.S1.Deficit.Displacement.GoldenSubstStartSharpness

namespace D5.S1.Words.FibonacciMapFirstStart

/-- The least zero-indexed start attaining the global maximum, allowing either letter. -/
noncomputable def goldenMAPFirstStart (d : ℕ) : ℕ :=
  sInf {j : ℕ | ∃ symbol : Bool,
    ∀ k < goldenMAPMaximum d, goldenWord (j + k * d) = symbol}

/-- The forward and backward Fibonacci displacements exclude every smaller denominator. -/
private theorem fibonacci_one_sided_records (m : ℕ) (hm : 2 ≤ m) :
    (Odd m → ∀ k : ℕ, 0 < k → k < Nat.fib (m + 2) →
      Real.goldenRatio⁻¹ ^ m ≤ Int.fract ((k : ℝ) * Real.goldenRatio)) ∧
    (Even m → ∀ k : ℕ, 0 < k → k < Nat.fib (m + 2) →
      Real.goldenRatio⁻¹ ^ m ≤ 1 - Int.fract ((k : ℝ) * Real.goldenRatio)) := by
  let u : ℤ := Nat.fib m
  let v : ℤ := Nat.fib (m + 1)
  let w : ℤ := Nat.fib (m + 2)
  let eps : ℝ := Real.goldenRatio⁻¹ ^ m
  let delta : ℝ := Real.goldenRatio⁻¹ ^ (m + 1)
  have hu : 0 < u := by
    dsimp [u]
    exact_mod_cast Nat.fib_pos.mpr (by omega : 0 < m)
  have hv : 0 < v := by
    dsimp [v]
    exact_mod_cast Nat.fib_pos.mpr (by omega : 0 < m + 1)
  have huv : u + v = w := by simp [u, v, w, Nat.fib_add_two]
  have heps : 0 < eps := pow_pos (inv_pos.mpr Real.goldenRatio_pos) _
  have hdelta : 0 < delta := pow_pos (inv_pos.mpr Real.goldenRatio_pos) _
  have huR : (0 : ℝ) < u := by exact_mod_cast hu
  have hvR : (0 : ℝ) < v := by exact_mod_cast hv
  have hueps : (u : ℝ) * eps < 1 := by
    have hp := Real.goldenRatio_mul_fib_succ_add_fib (m - 1)
    have hindex : m - 1 + 1 = m := by omega
    rw [hindex] at hp
    have hf : (0 : ℝ) ≤ Nat.fib (m - 1) := Nat.cast_nonneg _
    have huPow : (u : ℝ) < Real.goldenRatio ^ m := by
      dsimp [u]
      push_cast
      have huf : (0 : ℝ) < Nat.fib m := by simpa [u] using huR
      nlinarith [Real.one_lt_goldenRatio]
    have hcancel : Real.goldenRatio ^ m * eps = 1 := by
      dsimp [eps]
      rw [← mul_pow, mul_inv_cancel₀ Real.goldenRatio_pos.ne', one_pow]
    nlinarith [mul_lt_mul_of_pos_right huPow heps]
  -- The integral coordinates force either the same convergent or a denominator at least u+v.
  have exclude (k : ℕ) (hk : 0 < k) (hkw : (k : ℤ) < w)
      (e : ℝ) (he : 0 < e) (a b : ℤ)
      (ha : (a : ℝ) = (k : ℝ) * delta + e * v)
      (hb : (b : ℝ) = (k : ℝ) * eps - e * u)
      (hcoord : (k : ℤ) = a * u + b * v)
      (herr : e = (a : ℝ) * eps - b * delta) : eps ≤ e := by
    by_contra hbad
    have hesmall : e < eps := lt_of_not_ge hbad
    have hkR : (0 : ℝ) < k := by exact_mod_cast hk
    have haR : (0 : ℝ) < a := by
      rw [ha]
      positivity
    have haI : 1 ≤ a := by
      have : (0 : ℤ) < a := by exact_mod_cast haR
      omega
    have hbR : (-1 : ℝ) < b := by
      have heu := mul_lt_mul_of_pos_right hesmall huR
      have hke := mul_pos hkR heps
      rw [hb]
      nlinarith
    have hbI : 0 ≤ b := by
      have : (-1 : ℤ) < b := by exact_mod_cast hbR
      omega
    by_cases hbzero : b = 0
    · have haone : (1 : ℝ) ≤ a := by exact_mod_cast haI
      rw [hbzero] at herr
      norm_num at herr
      nlinarith
    · have hbpos : 1 ≤ b := by omega
      have hau := mul_le_mul_of_nonneg_right haI hu.le
      have hbv := mul_le_mul_of_nonneg_right hbpos hv.le
      nlinarith [hcoord, huv]
  have hres := Real.fib_succ_sub_goldenRatio_mul_fib m
  have hresNext := Real.fib_succ_sub_goldenRatio_mul_fib (m + 1)
  have hconj : Real.goldenConj = -Real.goldenRatio⁻¹ := by
    rw [Real.inv_goldenRatio]
    ring
  have hcass := D5.S1.Scale.fib_cassini_from_golden_norm m
  constructor
  · intro hodd k hk hkw
    have hdet : u * w - v ^ 2 = 1 := by
      simpa [u, v, w, hodd.add_one.neg_one_pow] using hcass
    have hr1 : (u : ℝ) * Real.goldenRatio - v = eps := by
      rw [hconj, hodd.neg_pow] at hres
      dsimp [u, v, eps]
      push_cast
      linarith
    have hr2 : (v : ℝ) * Real.goldenRatio - w = -delta := by
      rw [hconj, hodd.add_one.neg_pow] at hresNext
      dsimp [v, w, delta]
      push_cast
      linarith
    let p : ℤ := ⌊(k : ℝ) * Real.goldenRatio⌋
    let e : ℝ := Int.fract ((k : ℝ) * Real.goldenRatio)
    have he : 0 < e := by
      have hne : e ≠ 0 := by
        rw [Int.fract_ne_zero_iff]
        rintro ⟨z, hz⟩
        exact (Real.goldenRatio_irrational.natCast_mul (by omega : k ≠ 0)).ne_int
          z hz.symm
      exact lt_of_le_of_ne (Int.fract_nonneg _) hne.symm
    have hp : (p : ℝ) = (k : ℝ) * Real.goldenRatio - e := by
      dsimp [p, e]
      rw [Int.fract]
      ring
    let a : ℤ := (k : ℤ) * w - p * v
    let b : ℤ := p * u - (k : ℤ) * v
    apply exclude k hk (by dsimp [w]; exact_mod_cast hkw) e he a b
    · dsimp [a]
      push_cast
      rw [hp]
      nlinarith [hr2]
    · dsimp [b]
      push_cast
      rw [hp]
      nlinarith [hr1]
    · dsimp [a, b]
      linear_combination -(k : ℤ) * hdet
    · have hdetR : (u : ℝ) * w - (v : ℝ) ^ 2 = 1 := by exact_mod_cast hdet
      dsimp [a, b]
      push_cast
      rw [hp]
      rw [show eps = (u : ℝ) * Real.goldenRatio - v by linarith,
        show delta = (w : ℝ) - v * Real.goldenRatio by linarith]
      linear_combination -e * hdetR
  · intro heven k hk hkw
    have hdet : u * w - v ^ 2 = -1 := by
      simpa [u, v, w, heven.add_one.neg_one_pow] using hcass
    have hr1 : (u : ℝ) * Real.goldenRatio - v = -eps := by
      rw [hconj, heven.neg_pow] at hres
      dsimp [u, v, eps]
      push_cast
      linarith
    have hr2 : (v : ℝ) * Real.goldenRatio - w = delta := by
      rw [hconj, heven.add_one.neg_pow] at hresNext
      dsimp [v, w, delta]
      push_cast
      linarith
    let p : ℤ := ⌊(k : ℝ) * Real.goldenRatio⌋ + 1
    let e : ℝ := 1 - Int.fract ((k : ℝ) * Real.goldenRatio)
    have he : 0 < e := by dsimp [e]; linarith [Int.fract_lt_one ((k : ℝ) * Real.goldenRatio)]
    have hp : (p : ℝ) = (k : ℝ) * Real.goldenRatio + e := by
      dsimp [p, e]
      rw [Int.fract]
      push_cast
      ring
    let a : ℤ := p * v - (k : ℤ) * w
    let b : ℤ := (k : ℤ) * v - p * u
    apply exclude k hk (by dsimp [w]; exact_mod_cast hkw) e he a b
    · dsimp [a]
      push_cast
      rw [hp]
      nlinarith [hr2]
    · dsimp [b]
      push_cast
      rw [hp]
      nlinarith [hr1]
    · dsimp [a, b]
      linear_combination (k : ℤ) * hdet
    · have hdetR : (u : ℝ) * w - (v : ℝ) ^ 2 = -1 := by exact_mod_cast hdet
      dsimp [a, b]
      push_cast
      rw [hp]
      rw [show eps = (v : ℝ) - u * Real.goldenRatio by linarith,
        show delta = (v : ℝ) * Real.goldenRatio - w by linarith]
      linear_combination e * hdetR

/-- Open symbol endpoints permit equality in the gap bound in either direction. -/
private theorem open_rotation_run {lo hi eps : ℝ} {x : ℕ → ℝ} {length : ℕ}
    (forward : Bool) (heps : 0 < eps) (hlo : 0 ≤ lo) (hhi : hi ≤ 1)
    (hgap : eps ≤ 1 - (hi - lo)) (hpos : 0 < length)
    (hmem : ∀ k < length, lo < x k ∧ x k < hi)
    (horbit : ∀ k, k + 1 < length →
      x (k + 1) = Int.fract (x k + if forward then eps else -eps)) :
    x (length - 1) = x 0 +
      (if forward then (1 : ℝ) else -1) * (length - 1 : ℕ) * eps ∧
    (length - 1 : ℕ) * eps < hi - lo := by
  have hnext (k : ℕ) (hk : k + 1 < length) :
      x (k + 1) = x k + if forward then eps else -eps := by
    have hx := hmem k (by omega)
    have hy := hmem (k + 1) hk
    cases forward with
    | true =>
      simp only [if_true] at horbit ⊢
      by_cases hw : x k + eps < 1
      · rw [horbit k hk, Int.fract_eq_self.mpr ⟨by linarith, hw⟩]
      · have hf : ⌊x k + eps⌋ = (1 : ℤ) := Int.floor_eq_iff.mpr
          ⟨by exact_mod_cast (show (1 : ℝ) ≤ x k + eps by linarith),
            by exact_mod_cast (show x k + eps < (1 : ℝ) + 1 by linarith)⟩
        rw [horbit k hk, Int.fract, hf] at hy
        norm_num at hy
        linarith
    | false =>
      simp only [Bool.false_eq_true, if_false] at horbit ⊢
      by_cases hw : 0 ≤ x k - eps
      · rw [horbit k hk, Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩]
      · have hf : ⌊x k + -eps⌋ = (-1 : ℤ) := Int.floor_eq_iff.mpr
          ⟨by exact_mod_cast (show (-1 : ℝ) ≤ x k + -eps by linarith),
            by exact_mod_cast (show x k + -eps < (-1 : ℝ) + 1 by linarith)⟩
        rw [horbit k hk, Int.fract, hf] at hy
        norm_num at hy
        linarith
  have hlinear (k : ℕ) (hk : k < length) :
      x k = x 0 + (if forward then (1 : ℝ) else -1) * k * eps := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [hnext k (by simpa using hk), ih (by omega)]
      cases forward <;> simp <;> ring
  have hl : length - 1 < length := by omega
  refine ⟨hlinear _ hl, ?_⟩
  have hx := hmem 0 hpos
  have hy := hmem (length - 1) hl
  rw [hlinear _ hl] at hy
  cases forward <;> simp at hy <;> linarith

/-- A nonempty exact phase window gives a bounded, attained maximum and excludes false letters. -/
private theorem maximum_of_window (d L : ℕ) (eps : ℝ) (forward : Bool)
    (hL : 0 < L) (heps : 0 < eps) (hgap : eps ≤ 1 - goldenMechanicalSlope)
    (hstep : Int.fract ((d : ℝ) * Real.goldenRatio) =
      if forward then eps else 1 - eps)
    (hupper : goldenMechanicalSlope ≤ (L : ℝ) * eps)
    (hfalse : 1 - goldenMechanicalSlope ≤ (L - 1 : ℕ) * eps)
    (hwitness : ∃ j : ℕ,
      1 - goldenMechanicalSlope < Int.fract (((j + 1 : ℕ) : ℝ) * Real.goldenRatio) ∧
      if forward then
        Int.fract (((j + 1 : ℕ) : ℝ) * Real.goldenRatio) + (L - 1 : ℕ) * eps < 1
      else 1 - goldenMechanicalSlope + (L - 1 : ℕ) * eps <
        Int.fract (((j + 1 : ℕ) : ℝ) * Real.goldenRatio)) :
    goldenMAPMaximum d = L ∧ ∀ j : ℕ,
      (∃ symbol : Bool, ∀ k < L, goldenWord (j + k * d) = symbol) ↔
      (1 - goldenMechanicalSlope <
        Int.fract (((j + 1 : ℕ) : ℝ) * Real.goldenRatio) ∧
      if forward then
        Int.fract (((j + 1 : ℕ) : ℝ) * Real.goldenRatio) + (L - 1 : ℕ) * eps < 1
      else 1 - goldenMechanicalSlope + (L - 1 : ℕ) * eps <
        Int.fract (((j + 1 : ℕ) : ℝ) * Real.goldenRatio)) := by
  open D5.S1.Dynamics D5.S1.Words.Mechanical in
  have phase_true (j : ℕ) : goldenWord j = true ↔
      1 - goldenMechanicalSlope < Int.fract (((j + 1 : ℕ) : ℝ) * Real.goldenRatio) := by
    have hweak : goldenWord j = true ↔
        1 - goldenMechanicalSlope ≤ goldenFractionalPart (j + 1) := by
      rw [← lowerMechanicalWord_golden, lowerMechanicalWord_eq_true_iff,
        lowerMechanicalLetter_golden, golden_mechanical_letter_eq_one_iff]
      exact and_iff_left (Int.fract_lt_one _)
    have hboundary : 1 - goldenMechanicalSlope = 2 - Real.goldenRatio := by
      rw [goldenMechanicalSlope, Real.inv_goldenRatio, Real.goldenConj,
        Real.goldenRatio]
      ring
    have hne : goldenFractionalPart (j + 1) ≠ 1 - goldenMechanicalSlope := by
      intro heq
      rw [goldenFractionalPart, Int.fract, hboundary] at heq
      have hint : ((j + 2 : ℕ) : ℝ) * Real.goldenRatio =
          (((⌊((j + 1 : ℕ) : ℝ) * Real.goldenRatio⌋ + 2 : ℤ) : ℝ)) := by
        push_cast at heq ⊢
        nlinarith
      exact (Real.goldenRatio_irrational.natCast_mul (by omega : j + 2 ≠ 0)).ne_int _ hint
    change goldenWord j = true ↔ 1 - goldenMechanicalSlope < goldenFractionalPart (j + 1)
    constructor
    · intro h
      exact lt_of_le_of_ne (hweak.mp h) hne.symm
    · intro h
      exact hweak.mpr h.le
  let a : ℝ := 1 - goldenMechanicalSlope
  let phase (j : ℕ) : ℝ := Int.fract (((j + 1 : ℕ) : ℝ) * Real.goldenRatio)
  let step : ℝ := if forward then eps else -eps
  have hr : 0 < goldenMechanicalSlope := inv_pos.mpr Real.goldenRatio_pos
  have hrlt : goldenMechanicalSlope < 1 := inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio
  have ha : 0 < a := by dsimp [a]; linarith
  have halfr : a ≤ goldenMechanicalSlope := by
    have hquad : goldenMechanicalSlope ^ 2 + goldenMechanicalSlope = 1 := by
      rw [goldenMechanicalSlope, Real.inv_goldenRatio]
      nlinarith [Real.goldenConj_sq]
    dsimp [a]
    nlinarith [sq_nonneg (goldenMechanicalSlope - 1 / 2)]
  have phase_pos (j : ℕ) : 0 < phase j := by
    have hne : phase j ≠ 0 := by
      dsimp [phase]
      change Int.fract (((j + 1 : ℕ) : ℝ) * Real.goldenRatio) ≠ 0
      rw [Int.fract_ne_zero_iff]
      rintro ⟨z, hz⟩
      exact (Real.goldenRatio_irrational.natCast_mul (by omega : j + 1 ≠ 0)).ne_int z hz.symm
    exact lt_of_le_of_ne (Int.fract_nonneg _) hne.symm
  have phase_step (j k : ℕ) :
      phase (j + (k + 1) * d) = Int.fract (phase (j + k * d) + step) := by
    have hf := ThreeGap.fract_add_fract_eq
      (((j + k * d + 1 : ℕ) : ℝ) * Real.goldenRatio) ((d : ℝ) * Real.goldenRatio)
    rw [hstep] at hf
    have hn : j + (k + 1) * d + 1 = (j + k * d + 1) + d := by ring
    have hf' : phase (j + (k + 1) * d) =
        Int.fract (phase (j + k * d) + if forward then eps else 1 - eps) := by
      dsimp [phase]
      rw [hn]
      push_cast at hf ⊢
      rw [add_mul]
      exact hf.symm
    rw [hf']
    dsimp [step]
    cases forward with
    | true => simp
    | false =>
      simp only [Bool.false_eq_true, if_false]
      rw [show phase (j + k * d) + (1 - eps) = (phase (j + k * d) + -eps) + 1 by ring,
        Int.fract_add_one]
  have run_span (j length : ℕ) (symbol : Bool) (hlen : 0 < length)
      (hmap : ∀ k < length, goldenWord (j + k * d) = symbol) :
      (length - 1 : ℕ) * eps < goldenMechanicalSlope ∧
      (symbol = false → (length - 1 : ℕ) * eps < a) := by
    cases symbol with
    | true =>
      have hm (k : ℕ) (hk : k < length) : a < phase (j + k * d) ∧ phase (j + k * d) < 1 :=
        ⟨(phase_true _).mp (hmap k hk), Int.fract_lt_one _⟩
      have h := open_rotation_run forward heps ha.le (le_refl (1 : ℝ))
        (by dsimp [a]; linarith) hlen hm (fun k _ => phase_step j k)
      exact ⟨by dsimp [a] at h; linarith [h.2], by simp⟩
    | false =>
      have hm (k : ℕ) (hk : k < length) : 0 < phase (j + k * d) ∧ phase (j + k * d) < a := by
        refine ⟨phase_pos _, ?_⟩
        have hnot : ¬ goldenWord (j + k * d) = true := by rw [hmap k hk]; decide
        have hle : phase (j + k * d) ≤ a := not_lt.mp (fun hh => hnot ((phase_true _).mpr hh))
        have hboundary : phase (j + k * d) ≠ a := by
          intro heq
          have hweak : goldenWord (j + k * d) = true := by
            open D5.S1.Dynamics D5.S1.Words.Mechanical in
            rw [← lowerMechanicalWord_golden, lowerMechanicalWord_eq_true_iff,
              lowerMechanicalLetter_golden, golden_mechanical_letter_eq_one_iff]
            exact ⟨by simpa [phase, a, goldenFractionalPart] using heq.ge,
              Int.fract_lt_one _⟩
          exact hnot hweak
        exact lt_of_le_of_ne hle hboundary
      have h := open_rotation_run forward heps (le_refl (0 : ℝ))
        (by dsimp [a]; linarith) (by dsimp [a] at halfr ⊢; linarith)
        hlen hm (fun k _ => phase_step j k)
      exact ⟨h.2.trans_le (by simpa using halfr), fun _ => by simpa using h.2⟩
  have upper (j length : ℕ) (symbol : Bool) (hlen : 0 < length)
      (hmap : ∀ k < length, goldenWord (j + k * d) = symbol) : length ≤ L := by
    have hs := (run_span j length symbol hlen hmap).1
    by_contra hh
    have hnat : L ≤ length - 1 := by omega
    have hreal : (L : ℝ) ≤ (length - 1 : ℕ) := by exact_mod_cast hnat
    nlinarith [mul_le_mul_of_nonneg_right hreal heps.le]
  let window (j : ℕ) : Prop := a < phase j ∧
    if forward then phase j + (L - 1 : ℕ) * eps < 1 else a + (L - 1 : ℕ) * eps < phase j
  have classify (j : ℕ) :
      (∃ symbol : Bool, ∀ k < L, goldenWord (j + k * d) = symbol) ↔ window j := by
    constructor
    · rintro ⟨symbol, hmap⟩
      have htrue : symbol = true := by
        cases symbol with
        | true => rfl
        | false =>
          have hs := (run_span j L false hL hmap).2 rfl
          dsimp [a] at hs
          linarith
      subst symbol
      have hm (k : ℕ) (hk : k < L) : a < phase (j + k * d) ∧ phase (j + k * d) < 1 :=
        ⟨(phase_true _).mp (hmap k hk), Int.fract_lt_one _⟩
      have hs := open_rotation_run forward heps ha.le (le_refl (1 : ℝ))
        (by dsimp [a]; linarith) hL hm (fun k _ => phase_step j k)
      dsimp [window]
      refine ⟨by simpa using (hm 0 hL).1, ?_⟩
      have hend := hm (L - 1) (by omega)
      rw [hs.1] at hend
      cases forward <;> simp at hend ⊢ <;> linarith
    · intro hj
      have hlinear (k : ℕ) (hk : k < L) :
          phase (j + k * d) = phase j + (if forward then (1 : ℝ) else -1) * k * eps := by
        induction k with
        | zero => simp
        | succ k ih =>
          rw [phase_step, ih (by omega)]
          have hkR : (k : ℝ) + 1 ≤ (L - 1 : ℕ) := by
            exact_mod_cast (show k + 1 ≤ L - 1 by omega)
          have hmul := mul_le_mul_of_nonneg_right hkR heps.le
          have hz := Int.fract_lt_one (((j + 1 : ℕ) : ℝ) * Real.goldenRatio)
          change phase j < 1 at hz
          dsimp [window] at hj
          cases forward with
          | true =>
            simp only [step, if_true, one_mul, Nat.cast_add, Nat.cast_one] at hj ⊢
            rw [Int.fract_eq_self.mpr ⟨by nlinarith [phase_pos j], by nlinarith⟩]
            ring
          | false =>
            simp only [step, Bool.false_eq_true, if_false, neg_mul, one_mul,
              Nat.cast_add, Nat.cast_one, neg_add_rev] at hj ⊢
            rw [Int.fract_eq_self.mpr ⟨by nlinarith, by nlinarith⟩]
            ring
      refine ⟨true, fun k hk => (phase_true _).mpr ?_⟩
      change a < phase (j + k * d)
      rw [hlinear k hk]
      have hkR : (k : ℝ) ≤ (L - 1 : ℕ) := by exact_mod_cast (show k ≤ L - 1 by omega)
      have hmul := mul_le_mul_of_nonneg_right hkR heps.le
      have hke : (0 : ℝ) ≤ k * eps := by positivity
      dsimp [window] at hj
      cases forward <;> simp at hj ⊢ <;> linarith
  have hbounded : BddAbove {length : ℕ | ∃ j : ℕ, ∃ symbol : Bool,
      0 < length ∧ ∀ k < length, goldenWord (j + k * d) = symbol} := by
    refine ⟨L, ?_⟩
    rintro length ⟨j, symbol, hlen, hmap⟩
    exact upper j length symbol hlen hmap
  obtain ⟨j, hj⟩ := hwitness
  obtain ⟨symbol, hmap⟩ := (classify j).mpr hj
  have hmem : L ∈ {length : ℕ | ∃ j : ℕ, ∃ symbol : Bool,
      0 < length ∧ ∀ k < length, goldenWord (j + k * d) = symbol} := ⟨j, symbol, hL, hmap⟩
  refine ⟨le_antisymm (csSup_le ⟨L, hmem⟩ ?_) (le_csSup hbounded hmem), classify⟩
  rintro length ⟨j, symbol, hlen, hmap⟩
  exact upper j length symbol hlen hmap

/-- Joshi--Rust Conjecture 3.19, with both symbols and all nonnegative starts. -/
theorem result (n : ℕ) (hn : 1 ≤ n) :
    goldenMAPFirstStart (Nat.fib (2 * n + 1)) = Nat.fib (2 * n + 3) - 2 ∧
    goldenMAPFirstStart (Nat.fib (2 * n)) = Nat.fib (4 * n) - 1 := by
  let r : ℝ := Real.goldenRatio⁻¹
  have hr : 0 < r := inv_pos.mpr Real.goldenRatio_pos
  have hrlt : r < 1 := inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio
  have hconj : Real.goldenConj = -r := by dsimp [r]; rw [Real.inv_goldenRatio]; ring
  have hquad : r ^ 2 + r = 1 := by
    dsimp [r]
    rw [Real.inv_goldenRatio]
    nlinarith [Real.goldenConj_sq]
  have ha : 1 - goldenMechanicalSlope = r ^ 2 := by
    change 1 - r = r ^ 2
    linarith
  have hcubic : r - r ^ 3 = r ^ 2 := by
    linear_combination -r * hquad
  have hphir : Real.goldenRatio - r = 1 := by
    linarith only [Real.goldenRatio_add_goldenConj, hconj]
  have htwo : 2 * r ^ 2 < 1 := by
    have hhalf : 1 / 2 < r := by
      by_contra h
      have hle : r ≤ 1 / 2 := le_of_not_gt h
      have hs := mul_self_le_mul_self hr.le hle
      nlinarith only [hquad, hle, hs]
    linarith only [hquad, hhalf]
  have power_le (a b : ℕ) (hab : a ≤ b) : r ^ b ≤ r ^ a := by
    rcases lt_or_eq_of_le hab with h | h
    · exact (pow_lt_pow_right_of_lt_one₀ hr hrlt h).le
    · simp [h]
  have product (m : ℕ) (hm : 2 ≤ m) :
      ((Nat.fib (m - 2) + Nat.fib m : ℕ) : ℝ) * r ^ m =
        r + (-r) ^ (m - 1) * r ^ m := by
    have hidx : m - 2 + 1 = m - 1 := by omega
    have hidx2 : m - 2 + 2 = m := by omega
    have hp := Real.goldenRatio_mul_fib_succ_add_fib (m - 2)
    have hc := Real.goldenConj_mul_fib_succ_add_fib (m - 2)
    rw [hidx] at hp hc
    rw [hconj] at hc
    have hf := Nat.fib_add_two (n := m - 2)
    rw [hidx, hidx2] at hf
    have hl : ((Nat.fib (m - 2) + Nat.fib m : ℕ) : ℝ) =
        Real.goldenRatio ^ (m - 1) + (-r) ^ (m - 1) := by
      rw [hf]
      push_cast
      nlinarith only [hp, hc, hphir]
    have hpow : r ^ m = r ^ (m - 1) * r := by
      rw [← pow_succ]
      congr 1
      omega
    have hcancel : Real.goldenRatio ^ (m - 1) * r ^ (m - 1) = 1 := by
      rw [← mul_pow]
      change (Real.goldenRatio * Real.goldenRatio⁻¹) ^ (m - 1) = 1
      rw [mul_inv_cancel₀ Real.goldenRatio_pos.ne', one_pow]
    rw [hl, add_mul]
    rw [hpow, ← mul_assoc, hcancel, one_mul]
  have first (d L J : ℕ) (eps : ℝ) (forward : Bool)
      (hL : 0 < L) (heps : 0 < eps) (hgap : eps ≤ 1 - goldenMechanicalSlope)
      (hstep : Int.fract ((d : ℝ) * Real.goldenRatio) = if forward then eps else 1 - eps)
      (hupper : goldenMechanicalSlope ≤ (L : ℝ) * eps)
      (hfalse : 1 - goldenMechanicalSlope ≤ (L - 1 : ℕ) * eps)
      (hJ : 1 - goldenMechanicalSlope < Int.fract (((J + 1 : ℕ) : ℝ) * Real.goldenRatio) ∧
        if forward then Int.fract (((J + 1 : ℕ) : ℝ) * Real.goldenRatio) +
          (L - 1 : ℕ) * eps < 1 else 1 - goldenMechanicalSlope +
          (L - 1 : ℕ) * eps < Int.fract (((J + 1 : ℕ) : ℝ) * Real.goldenRatio))
      (hmin : ∀ j : ℕ, j < J → ¬ (1 - goldenMechanicalSlope <
        Int.fract (((j + 1 : ℕ) : ℝ) * Real.goldenRatio) ∧
        if forward then Int.fract (((j + 1 : ℕ) : ℝ) * Real.goldenRatio) +
          (L - 1 : ℕ) * eps < 1 else 1 - goldenMechanicalSlope +
          (L - 1 : ℕ) * eps < Int.fract (((j + 1 : ℕ) : ℝ) * Real.goldenRatio))) :
      goldenMAPFirstStart d = J := by
    have h := maximum_of_window d L eps forward hL heps hgap hstep hupper hfalse ⟨J, hJ⟩
    unfold goldenMAPFirstStart
    rw [h.1]
    apply IsLeast.csInf_eq
    refine ⟨(h.2 J).mpr hJ, ?_⟩
    intro j hj
    exact le_of_not_gt (fun hlt => hmin j hlt ((h.2 j).mp hj))
  constructor
  · let m := 2 * n + 1
    have hm : 3 ≤ m := by dsimp [m]; omega
    have hodd : Odd m := ⟨n, rfl⟩
    let eps := r ^ m
    let t := r ^ (2 * m - 1)
    let z := r ^ (m + 2)
    let L := Nat.fib (m - 2) + Nat.fib m
    let J := Nat.fib (m + 2) - 2
    have hL : 0 < L := by
      exact Nat.add_pos_right _ (Nat.fib_pos.mpr (by omega : 0 < m))
    have heps : 0 < eps := pow_pos hr _
    have ht : 0 < t := pow_pos hr _
    have hz : 0 < z := pow_pos hr _
    have hep3 : eps ≤ r ^ 3 := power_le 3 m hm
    have hgap : eps ≤ r ^ 2 := power_le 2 m (by omega)
    have htprod : t = r ^ (m - 1) * eps := by
      dsimp [t, eps]
      rw [← pow_add]
      congr 1
      omega
    have hzprod : z = eps * r ^ 2 := by dsimp [z, eps]; rw [pow_add]
    have hteps : t ≤ eps * r ^ 2 := by
      rw [htprod]
      nlinarith only [mul_le_mul_of_nonneg_right
        (power_le 2 (m - 1) (by omega)) heps.le]
    have hzt : z + t < eps := by
      rw [hzprod]
      nlinarith only [hteps, htwo, heps]
    have hprod : (L : ℝ) * eps = r + t := by
      have h := product m (by omega)
      have heven : Even (m - 1) := by obtain ⟨a, ha⟩ := hodd; exact ⟨a, by omega⟩
      rw [heven.neg_pow, ← htprod] at h
      exact h
    have hspan : (L - 1 : ℕ) * eps = r + t - eps := by
      rw [Nat.cast_sub (by omega : 1 ≤ L), Nat.cast_one]
      nlinarith only [hprod]
    have hF : 2 ≤ Nat.fib (m + 2) := by
      have h := Nat.fib_mono (show 3 ≤ m + 2 by omega)
      norm_num at h
      exact h
    have hJidx : J + 1 = Nat.fib (m + 2) - 1 := by dsimp [J]; omega
    have hphase : Int.fract (((J + 1 : ℕ) : ℝ) * Real.goldenRatio) = r ^ 2 + z := by
      have hres := Real.fib_succ_sub_goldenRatio_mul_fib (m + 2)
      have hodd2 : Odd (m + 2) := by obtain ⟨a, ha⟩ := hodd; exact ⟨a + 1, by omega⟩
      rw [hconj, hodd2.neg_pow] at hres
      have hrepr : (((J + 1 : ℕ) : ℝ) * Real.goldenRatio) =
          (((Nat.fib (m + 3) : ℤ) - 2 : ℤ) : ℝ) + (r ^ 2 + z) := by
        rw [hJidx, Nat.cast_sub (by omega : 1 ≤ Nat.fib (m + 2)), Nat.cast_one]
        rw [sub_mul, one_mul]
        push_cast
        change (Nat.fib (m + 3) : ℝ) - Real.goldenRatio * Nat.fib (m + 2) = -z at hres
        nlinarith only [hres, hphir, hquad]
      rw [hrepr, Int.fract_intCast_add]
      exact Int.fract_eq_self.mpr ⟨by positivity,
        by nlinarith only [hgap, hzt, ht, htwo]⟩
    have hfirst : goldenMAPFirstStart (Nat.fib m) = J := by
      apply first (Nat.fib m) L J eps true hL heps
        (by rw [ha]; exact hgap) ?_ ?_ ?_ ?_ ?_
      · have h := GoldenSubstStartSharpness.fract_fib_mul_goldenRatio m hodd
        rw [hconj, hodd.neg_pow] at h
        simpa only [neg_neg, if_true] using h
      · change r ≤ (L : ℝ) * eps
        rw [hprod]
        linarith
      · rw [ha, hspan]
        nlinarith only [hcubic, hep3, ht]
      · simp only [if_true]
        rw [ha, hphase, hspan]
        constructor <;> nlinarith only [hz, hzt, hquad]
      · intro j hj hh
        simp only [if_true] at hh
        rw [ha, hspan] at hh
        let x := Int.fract (((j + 1 : ℕ) : ℝ) * Real.goldenRatio)
        have hx : 0 < x - r ^ 2 ∧ x - r ^ 2 < eps := by
          dsimp [x]
          constructor <;> linarith only [hh.1, hh.2, hquad, ht]
        have hshift : Int.fract (((j + 2 : ℕ) : ℝ) * Real.goldenRatio) = x - r ^ 2 := by
          have hrepr : (((j + 2 : ℕ) : ℝ) * Real.goldenRatio) =
              ((⌊((j + 1 : ℕ) : ℝ) * Real.goldenRatio⌋ + 2 : ℤ) : ℝ) + (x - r ^ 2) := by
            dsimp [x]
            rw [Int.fract]
            push_cast
            nlinarith only [hphir, hquad]
          rw [hrepr, Int.fract_intCast_add]
          exact Int.fract_eq_self.mpr ⟨hx.1.le,
            by linarith only [hx.2, hgap, hquad, hr]⟩
        have hrec := (fibonacci_one_sided_records m (by omega)).1 hodd (j + 2)
          (by omega) (by dsimp [J] at hj; omega)
        rw [hshift] at hrec
        change eps ≤ x - r ^ 2 at hrec
        linarith only [hrec, hx.2]
    simpa [m, J, Nat.add_assoc] using hfirst
  · let m := 2 * n
    have hm : 2 ≤ m := by dsimp [m]; omega
    have heven : Even m := ⟨n, by dsimp [m]; omega⟩
    let eps := r ^ m
    let t := r ^ (2 * m - 1)
    let z := r ^ (2 * m)
    let L := Nat.fib (m - 2) + Nat.fib m + 1
    let J := Nat.fib (2 * m) - 1
    have hL : 0 < L := by dsimp [L]; omega
    have heps : 0 < eps := pow_pos hr _
    have ht : 0 < t := pow_pos hr _
    have hz : 0 < z := pow_pos hr _
    have hgap : eps ≤ r ^ 2 := power_le 2 m hm
    have ht3 : t ≤ r ^ 3 := power_le 3 (2 * m - 1) (by omega)
    have hteps : t ≤ eps := power_le m (2 * m - 1) (by omega)
    have hzt : z < t := pow_lt_pow_right_of_lt_one₀ hr hrlt (by omega : 2 * m - 1 < 2 * m)
    have hspan : (L - 1 : ℕ) * eps = r - t := by
      have h := product m hm
      have hodd : Odd (m - 1) := by obtain ⟨a, ha⟩ := heven; exact ⟨a - 1, by omega⟩
      rw [hodd.neg_pow] at h
      have htprod : t = r ^ (m - 1) * eps := by
        dsimp [t, eps]
        rw [← pow_add]
        congr 1
        omega
      dsimp [L]
      rw [h, neg_mul, ← htprod]
      ring
    have hprod : (L : ℝ) * eps = r - t + eps := by
      have hcast : (L : ℝ) = (L - 1 : ℕ) + 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ L), Nat.cast_one]
        ring
      rw [hcast, add_mul, hspan, one_mul]
    have hF : 0 < Nat.fib (2 * m) := Nat.fib_pos.mpr (by omega)
    have hJidx : J + 1 = Nat.fib (2 * m) := by dsimp [J]; omega
    have hphase : Int.fract (((J + 1 : ℕ) : ℝ) * Real.goldenRatio) = 1 - z := by
      rw [hJidx]
      have heven2 : Even (2 * m) := ⟨m, by omega⟩
      have h := GoldenSubstStartSharpness.fract_fib_mul_goldenRatio_of_even (2 * m) heven2
      rw [hconj, heven2.neg_pow] at h
      exact h
    have hfirst : goldenMAPFirstStart (Nat.fib m) = J := by
      apply first (Nat.fib m) L J eps false hL heps
        (by rw [ha]; exact hgap) ?_ ?_ ?_ ?_ ?_
      · have h := GoldenSubstStartSharpness.fract_fib_mul_goldenRatio_of_even m heven
        rw [hconj, heven.neg_pow] at h
        simpa only [Bool.false_eq_true, if_false] using h
      · change r ≤ (L : ℝ) * eps
        rw [hprod]
        linarith
      · rw [ha, hspan]
        linarith only [hcubic, ht3]
      · simp only [Bool.false_eq_true, if_false]
        rw [ha, hphase, hspan]
        constructor <;> nlinarith only [hzt, hquad, hspan, hL,
          mul_nonneg (Nat.cast_nonneg (L - 1)) heps.le]
      · intro j hj hh
        simp only [Bool.false_eq_true, if_false] at hh
        rw [ha, hspan] at hh
        have hrec := (fibonacci_one_sided_records (2 * m - 2) (by omega)).2
          (show Even (2 * m - 2) from ⟨m - 1, by omega⟩) (j + 1) (by omega)
          (by rw [show 2 * m - 2 + 2 = 2 * m by omega]; dsimp [J] at hj; omega)
        have hrecord : t < r ^ (2 * m - 2) :=
          pow_lt_pow_right_of_lt_one₀ hr hrlt (by omega : 2 * m - 2 < 2 * m - 1)
        change r ^ (2 * m - 2) ≤ 1 - Int.fract (((j + 1 : ℕ) : ℝ) * Real.goldenRatio) at hrec
        nlinarith only [hh.2, hquad, hrec, hrecord]
    simpa [m, J, ← Nat.mul_assoc] using hfirst

example : goldenMAPFirstStart 2 = 3 ∧ goldenMAPFirstStart 1 = 2 := by
  have h := result 1 (Nat.le_refl 1)
  norm_num [Nat.fib_add_two] at h
  exact h

#print axioms fibonacci_one_sided_records
#print axioms open_rotation_run
#print axioms maximum_of_window
#print axioms result

end D5.S1.Words.FibonacciMapFirstStart
