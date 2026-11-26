/- GID: D5/S3/Quantum/QuantumChannels/WernerHolevo/ChirpedReplayArithmetic
   generality: I
   mirror-B: D5/B/S3/Quantum/QuantumChannels/WernerHolevo/ChirpedReplayArithmetic
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Quantum/QuantumChannels/WernerHolevo/ChirpedActualSeedBounds.seedBounds; instance=D5/S3/Quantum/QuantumChannels/WernerHolevo/Chirped73Input.centerRaw
   digest: Signed fixed-point enclosures for roots of unity, Cayley phases and correlation derivatives. -/

import D5.S3.Analytic.Certified.TrigEnvelopePhaseReduction
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic

namespace ChirpedReplay

open scoped BigOperators
open D5.S3.Analytic.Certified.TrigEnvelopePhaseReduction
open scoped ComplexConjugate

def scale : ℤ := 2 ^ 64

theorem scale_pos : 0 < scale := by norm_num [scale]

abbrev IntComplex := ℤ × ℤ

namespace IntComplex

def mul (a b : IntComplex) : IntComplex :=
  (a.1 * b.1 - a.2 * b.2, a.1 * b.2 + a.2 * b.1)

def conjugate (a : IntComplex) : IntComplex := (a.1, -a.2)

def floorPair (a : IntComplex) (d : ℤ) : IntComplex := (a.1 / d, a.2 / d)

def scalePair (k : ℤ) (a : IntComplex) : IntComplex := (k * a.1, k * a.2)

noncomputable def decode (s : ℝ) (a : IntComplex) : ℂ := ⟨(a.1 : ℝ) / s, (a.2 : ℝ) / s⟩

@[simp] theorem decode_add (s : ℝ) (a b : IntComplex) :
    decode s (a + b) = decode s a + decode s b := by
  apply Complex.ext <;> simp [decode, Complex.add_re, Complex.add_im, add_div]

@[simp] theorem decode_sum {ι : Type*} (s : ℝ) (t : Finset ι) (a : ι → IntComplex) :
    decode s (∑ i ∈ t, a i) = ∑ i ∈ t, decode s (a i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [decode, Complex.ext_iff]
  | insert i t hi ih => simp [Finset.sum_insert hi, ih]

@[simp] theorem decode_conjugate (s : ℝ) (a : IntComplex) :
    decode s (conjugate a) = conj (decode s a) := by
  apply Complex.ext <;> simp [decode, conjugate, neg_div]

theorem decode_mul {s t : ℝ} (hs : s ≠ 0) (ht : t ≠ 0) (a b : IntComplex) :
    decode (s * t) (mul a b) = decode s a * decode t b := by
  apply Complex.ext <;>
    simp only [decode, mul, Complex.mul_re, Complex.mul_im, Int.cast_sub, Int.cast_add,
      Int.cast_mul] <;>
    field_simp <;> ring

theorem decode_scalePair (s : ℝ) (a : IntComplex) {k : ℤ} (hk : k ≠ 0) :
    decode ((k : ℝ) * s) (scalePair k a) = decode s a := by
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  apply Complex.ext <;> simp [decode, scalePair, mul_div_mul_left _ _ hkR]

theorem decode_mulScale (s t : ℝ) (a : IntComplex) :
    decode (t * s) a = t⁻¹ • decode s a := by
  apply Complex.ext <;> simp only [decode, Complex.smul_re, Complex.smul_im, smul_eq_mul, div_mul_eq_div_div,
    div_eq_mul_inv] <;> ring

theorem mul_sum_left {ι : Type*} (t : Finset ι) (a : ι → IntComplex) (b : IntComplex) :
    mul (∑ i ∈ t, a i) b = ∑ i ∈ t, mul (a i) b := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [mul]
  | insert i t hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, ← ih]
    apply Prod.ext <;> simp [mul, add_mul] <;> ring

end IntComplex

open IntComplex (decode floorPair scalePair)

/-- The remainder proof applies to signed numerators, including negative exact multiples. -/
theorem signed_floor_error (a d : ℤ) (hd : 0 < d) :
    0 ≤ (a : ℝ) / (d : ℝ) - ((a / d : ℤ) : ℝ) ∧
    (a : ℝ) / (d : ℝ) - ((a / d : ℤ) : ℝ) < 1 := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hdec : ((a % d : ℤ) : ℝ) + ((a / d : ℤ) : ℝ) * (d : ℝ) = (a : ℝ) := by
    exact_mod_cast Int.emod_add_ediv_mul a d
  have hrem0 : (0 : ℝ) ≤ ((a % d : ℤ) : ℝ) := by
    exact_mod_cast Int.emod_nonneg a hd.ne'
  have hremd : ((a % d : ℤ) : ℝ) < d := by exact_mod_cast Int.emod_lt_of_pos a hd
  rw [show (a : ℝ) / (d : ℝ) - ((a / d : ℤ) : ℝ) =
      ((a % d : ℤ) : ℝ) / (d : ℝ) by
    apply (eq_div_iff hdR.ne').2
    field_simp <;> nlinarith]
  exact ⟨div_nonneg hrem0 hdR.le, (div_lt_one hdR).2 hremd⟩

theorem abs_scaled_floor_error (a d : ℤ) (hd : 0 < d) {s : ℝ} (hs : 0 < s) :
    |((a / d : ℤ) : ℝ) / s - (a : ℝ) / ((d : ℝ) * s)| ≤ 1 / s := by
  rw [div_mul_eq_div_div, ← sub_div, abs_div, abs_of_pos hs, abs_sub_comm,
    abs_of_nonneg (signed_floor_error a d hd).1]
  exact div_le_div_of_nonneg_right (signed_floor_error a d hd).2.le hs.le

theorem norm_decode_floor_le (a : IntComplex) {d : ℤ} (hd : 0 < d) {s : ℝ} (hs : 0 < s) :
    ‖decode s (floorPair a d) - decode ((d : ℝ) * s) a‖ ≤ 2 / s := by
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  simp only [decode, floorPair, Complex.sub_re, Complex.sub_im]
  calc
    _ ≤ 1 / s + 1 / s :=
      add_le_add (abs_scaled_floor_error a.1 d hd hs) (abs_scaled_floor_error a.2 d hd hs)
    _ = 2 / s := by rw [← add_div]; norm_num

/-- Exact complex products can be accumulated before the next rounding. -/
theorem mul_error_le (a b z w : ℂ) {e₁ e₂ M₁ M₂ : ℝ}
    (ha : ‖a - z‖ ≤ e₁) (hb : ‖b - w‖ ≤ e₂)
    (hz : ‖z‖ ≤ M₁) (hw : ‖w‖ ≤ M₂) :
    ‖a * b - z * w‖ ≤ M₂ * e₁ + (M₁ + e₁) * e₂ := by
  have ha' : ‖a‖ ≤ M₁ + e₁ := calc
    ‖a‖ = ‖z + (a - z)‖ := by rw [add_comm, sub_add_cancel]
    _ ≤ ‖z‖ + ‖a - z‖ := norm_add_le _ _
    _ ≤ _ := add_le_add hz ha
  rw [show a * b - z * w = (a - z) * w + a * (b - w) by ring]
  calc
    _ ≤ ‖(a - z) * w‖ + ‖a * (b - w)‖ := norm_add_le _ _
    _ = ‖a - z‖ * ‖w‖ + ‖a‖ * ‖b - w‖ := by simp only [norm_mul]
    _ ≤ _ := by
      rw [mul_comm M₂ e₁]
      exact add_le_add
        (mul_le_mul ha hw (norm_nonneg _) ((norm_nonneg (a - z)).trans ha))
        (mul_le_mul ha' hb (norm_nonneg _) ((norm_nonneg a).trans ha'))

theorem norm_sum_error_le {ι E : Type*} [SeminormedAddCommGroup E]
    (t : Finset ι) (a x : ι → E) {e : ℝ}
    (h : ∀ i ∈ t, ‖a i - x i‖ ≤ e) :
    ‖(∑ i ∈ t, a i) - ∑ i ∈ t, x i‖ ≤ (t.card : ℝ) * e := by
  rw [← Finset.sum_sub_distrib]
  exact (norm_sum_le t _).trans (by
    simpa only [Finset.sum_const, nsmul_eq_mul] using Finset.sum_le_sum h)

def roundedSquare (s : ℤ) (a : IntComplex) : IntComplex :=
  floorPair (IntComplex.mul a a) s

theorem roundedSquare_error {s : ℤ} (hs : 0 < s) (a : IntComplex) (z : ℂ) {e : ℝ}
    (ha : ‖decode s a - z‖ ≤ e) (hz : ‖z‖ = 1) :
    ‖decode s (roundedSquare s a) - z ^ 2‖ ≤ 2 / (s : ℝ) + 2 * e + e ^ 2 := by
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hr := norm_decode_floor_le (IntComplex.mul a a) hs hsR
  rw [IntComplex.decode_mul hsR.ne' hsR.ne'] at hr
  have hp := mul_error_le (decode s a) (decode s a) z z ha ha hz.le hz.le
  rw [← pow_two z] at hp
  calc
    _ ≤ ‖decode s (roundedSquare s a) - decode s a * decode s a‖ +
        ‖decode s a * decode s a - z ^ 2‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ 2 / (s : ℝ) + (1 * e + (1 + e) * e) := add_le_add hr hp
    _ = _ := by ring

section Roots

def piLo : ℤ := 314159265358979323846
def piHi : ℤ := 314159265358979323847
def piDen : ℤ := 10 ^ 20

def taylorDen (b : ℤ) (p : ℕ) : ℤ := ((22 + p).factorial : ℤ) * b ^ (22 + p)

def taylorNumerator (a b : ℤ) (p : ℕ) : ℤ :=
  ∑ k ∈ Finset.range 12, (-1 : ℤ) ^ k *
    (((22 + p).factorial / (2 * k + p).factorial : ℕ) : ℤ) *
    a ^ (2 * k + p) * b ^ (22 + p - (2 * k + p))

def taylorFloor (s a b : ℤ) (p : ℕ) : ℤ := (s * taylorNumerator a b p) / taylorDen b p

noncomputable def taylor (x : ℝ) (p : ℕ) : ℝ :=
  ∑ k ∈ Finset.range 12, (-1 : ℝ) ^ k * x ^ (2 * k + p) / ((2 * k + p).factorial : ℝ)

private theorem taylorDen_pos {b : ℤ} (hb : 0 < b) (p : ℕ) : 0 < taylorDen b p := by
  have hp : (0 : ℤ) < ((22 + p).factorial : ℤ) := by exact_mod_cast Nat.factorial_pos (22 + p)
  exact mul_pos hp (pow_pos hb _)

theorem taylor_ratio (a b : ℤ) (hb : 0 < b) (p : ℕ) :
    (taylorNumerator a b p : ℝ) / (taylorDen b p : ℝ) = taylor ((a : ℝ) / (b : ℝ)) p := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  unfold taylorNumerator taylorDen taylor
  simp only [Int.cast_sum, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, Int.cast_natCast]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k hk
  have hklt := Finset.mem_range.mp hk
  have hdeg : 2 * k + p ≤ 22 + p := by omega
  have hpow : (b : ℝ) ^ (22 + p) =
      (b : ℝ) ^ (2 * k + p) * (b : ℝ) ^ (22 + p - (2 * k + p)) := by
    rw [← pow_add, Nat.add_sub_of_le hdeg]
  have hfac : (0 : ℝ) < ((2 * k + p).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos (2 * k + p)
  have hlast : (0 : ℝ) < ((22 + p).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos (22 + p)
  rw [Nat.cast_div (Nat.factorial_dvd_factorial hdeg) hfac.ne', div_pow, hpow]
  field_simp <;> ring

theorem taylorFloor_error {s b : ℤ} (hs : 0 < s) (hb : 0 < b) (a : ℤ) (p : ℕ) :
    |(taylorFloor s a b p : ℝ) / (s : ℝ) - taylor ((a : ℝ) / (b : ℝ)) p| ≤
      1 / (s : ℝ) := by
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have h := abs_scaled_floor_error (s * taylorNumerator a b p) (taylorDen b p)
    (taylorDen_pos hb p) hsR
  rw [Int.cast_mul, mul_comm (taylorDen b p : ℝ),
    mul_div_mul_left _ _ hsR.ne', taylor_ratio a b hb p] at h
  exact h

noncomputable def unitPhase (x : ℝ) : ℂ := Complex.exp (Complex.I * (x : ℂ))

private theorem phase_chord_le (x y : ℝ) : ‖unitPhase x - unitPhase y‖ ≤ |x - y| := by
  unfold unitPhase
  have hfactor : Complex.exp (Complex.I * (x : ℂ)) - Complex.exp (Complex.I * (y : ℂ)) =
      Complex.exp (Complex.I * (y : ℂ)) * (Complex.exp (Complex.I * ((x - y : ℝ) : ℂ)) - 1) := by
    have harg : Complex.I * (y : ℂ) + Complex.I * ((x - y : ℝ) : ℂ) =
        Complex.I * (x : ℂ) := by push_cast; ring
    rw [mul_sub, ← Complex.exp_add, harg, mul_one]
  rw [hfactor, norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul]
  simpa only [Real.norm_eq_abs] using Real.norm_exp_I_mul_ofReal_sub_one_le (x := x - y)

def rootStart {n : ℕ} (j : Fin n) : IntComplex :=
  let a := piLo * (j.val : ℤ)
  let b := 4 * (n : ℤ) * piDen
  (taylorFloor scale a b 0, taylorFloor scale a b 1)

def root {n : ℕ} (j : Fin n) : IntComplex :=
  roundedSquare scale (roundedSquare scale (roundedSquare scale (rootStart j)))

private theorem rootStart_error {n : ℕ} (j : Fin n) :
    ‖decode scale (rootStart j) - unitPhase (Real.pi * (j.val : ℝ) / (4 * n))‖ ≤
      3 / (scale : ℝ) := by
  let a : ℤ := piLo * (j.val : ℤ)
  let b : ℤ := 4 * (n : ℤ) * piDen
  let x : ℝ := (a : ℝ) / (b : ℝ)
  let theta : ℝ := Real.pi * (j.val : ℝ) / (4 * n)
  let u : ℝ := (j.val : ℝ) / (4 * n)
  let pol : ℂ := ⟨taylor x 0, taylor x 1⟩
  have hn : 0 < n := Nat.zero_lt_of_lt j.isLt
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hden : 0 < piDen := by norm_num [piDen]
  have hb : 0 < b := by dsimp [b]; positivity
  have hu0 : 0 ≤ u := by dsimp [u]; positivity
  have hu : u ≤ 1 / 4 := by
    have hj : (j.val : ℝ) ≤ n := by exact_mod_cast j.isLt.le
    calc
      u ≤ (n : ℝ) / (4 * n) := div_le_div_of_nonneg_right hj (by positivity)
      _ = 1 / 4 := by field_simp
  have hx : x = ((piLo : ℝ) / (piDen : ℝ)) * u := by
    have hdenR : (0 : ℝ) < piDen := by exact_mod_cast hden
    dsimp [x, a, b, u]
    push_cast
    field_simp <;> ring
  have ht : theta = Real.pi * u := by dsimp [theta, u]; ring
  have hx0 : 0 ≤ x := by
    rw [hx]
    exact mul_nonneg (by norm_num [piLo, piDen]) hu0
  have hx8 : x ≤ 4 / 5 := by
    calc
      x ≤ ((piLo : ℝ) / (piDen : ℝ)) * (1 / 4) := by
        rw [hx]
        exact mul_le_mul_of_nonneg_left hu (by norm_num [piLo, piDen])
      _ ≤ _ := by norm_num [piLo, piDen]
  have hpi0 : (piLo : ℝ) / (piDen : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d20.le
    norm_num [piLo, piDen] at h ⊢
    exact h
  have hpi1 : Real.pi ≤ (piHi : ℝ) / (piDen : ℝ) := by
    have h := Real.pi_lt_d20.le
    norm_num [piHi, piDen] at h ⊢
    exact h
  have hgap : |theta - x| ≤ 1 / (4 * (piDen : ℝ)) := by
    rw [ht, hx, ← sub_mul, abs_mul, abs_of_nonneg (sub_nonneg.mpr hpi0), abs_of_nonneg hu0]
    calc
      _ ≤ ((piHi : ℝ) / (piDen : ℝ) - (piLo : ℝ) / (piDen : ℝ)) * (1 / 4) := by
        exact mul_le_mul (sub_le_sub_right hpi1 _) hu hu0
          (sub_nonneg.mpr (hpi0.trans hpi1))
      _ = _ := by norm_num [piLo, piHi, piDen]
  have hxabs : |x| ≤ 1 := by
    rw [abs_of_nonneg hx0]
    exact hx8.trans (by norm_num)
  have hcos := abs_cos_sub_partial_le x hxabs 12
  have hsin := abs_sin_sub_partial_le x hxabs 12
  have hpoly : ‖pol - unitPhase x‖ ≤
      (4 / 5 : ℝ) ^ 24 / (Nat.factorial 24 : ℝ) + (4 / 5 : ℝ) ^ 25 / (Nat.factorial 25 : ℝ) := by
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    simp [pol, unitPhase, Complex.exp_re, Complex.exp_im, Complex.mul_re, Complex.mul_im,
      abs_sub_comm (taylor x 0) (Real.cos x), abs_sub_comm (taylor x 1) (Real.sin x)]
    apply add_le_add
    · calc
        |Real.cos x - taylor x 0| ≤ |x| ^ 24 / (Nat.factorial 24 : ℝ) := by
          simpa [taylor] using hcos
        _ ≤ _ := div_le_div_of_nonneg_right
          (pow_le_pow_left₀ (abs_nonneg x) (by rwa [abs_of_nonneg hx0]) _) (by positivity)
    · calc
        |Real.sin x - taylor x 1| ≤ |x| ^ 25 / (Nat.factorial 25 : ℝ) := by
          simpa [taylor] using hsin
        _ ≤ _ := div_le_div_of_nonneg_right
          (pow_le_pow_left₀ (abs_nonneg x) (by rwa [abs_of_nonneg hx0]) _) (by positivity)
  have hround : ‖decode scale (rootStart j) - pol‖ ≤ 2 / (scale : ℝ) := by
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    change |(taylorFloor scale a b 0 : ℝ) / (scale : ℝ) - taylor x 0| +
      |(taylorFloor scale a b 1 : ℝ) / (scale : ℝ) - taylor x 1| ≤ _
    calc
      _ ≤ 1 / (scale : ℝ) + 1 / (scale : ℝ) :=
        add_le_add (taylorFloor_error scale_pos hb a 0) (taylorFloor_error scale_pos hb a 1)
      _ = 2 / (scale : ℝ) := by rw [← add_div]; norm_num
  have hchord : ‖unitPhase x - unitPhase theta‖ ≤ 1 / (4 * (piDen : ℝ)) := by
    rw [norm_sub_rev]
    exact (phase_chord_le theta x).trans hgap
  calc
    _ ≤ ‖decode scale (rootStart j) - pol‖ + ‖pol - unitPhase theta‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ 2 / (scale : ℝ) + (‖pol - unitPhase x‖ + ‖unitPhase x - unitPhase theta‖) :=
      add_le_add hround (norm_sub_le_norm_sub_add_norm_sub _ _ _)
    _ ≤ _ := by
      have hbudget : 2 / (scale : ℝ) +
          ((4 / 5 : ℝ) ^ 24 / (Nat.factorial 24 : ℝ) + (4 / 5 : ℝ) ^ 25 / (Nat.factorial 25 : ℝ) +
            1 / (4 * (piDen : ℝ))) ≤ 3 / (scale : ℝ) := by
        norm_num [scale, piDen, Nat.factorial]
      exact (add_le_add le_rfl (add_le_add hpoly hchord)).trans hbudget

/-- Python's root entry, including each of its three signed divisions. -/
theorem root_error {n : ℕ} (j : Fin n) :
    ‖decode scale (root j) - unitPhase (2 * Real.pi * (j.val : ℝ) / n)‖ ≤
      45 / (scale : ℝ) := by
  let theta : ℝ := Real.pi * (j.val : ℝ) / (4 * n)
  let z := unitPhase theta
  let a := rootStart j
  let b := roundedSquare scale a
  let c := roundedSquare scale b
  have hz : ‖z‖ = 1 := Complex.norm_exp_I_mul_ofReal theta
  have h₁ : ‖decode scale b - z ^ 2‖ ≤ 9 / (scale : ℝ) :=
    (roundedSquare_error scale_pos a z (rootStart_error j) hz).trans (by norm_num [scale])
  have hz₂ : ‖z ^ 2‖ = 1 := by rw [norm_pow, hz, one_pow]
  have h₂ : ‖decode scale c - (z ^ 2) ^ 2‖ ≤ 21 / (scale : ℝ) :=
    (roundedSquare_error scale_pos b (z ^ 2) h₁ hz₂).trans (by norm_num [scale])
  have hz₄ : ‖(z ^ 2) ^ 2‖ = 1 := by rw [norm_pow, hz₂, one_pow]
  have h₃ := (roundedSquare_error scale_pos c ((z ^ 2) ^ 2) h₂ hz₄).trans
    (show 2 / (scale : ℝ) + 2 * (21 / (scale : ℝ)) + (21 / (scale : ℝ)) ^ 2 ≤
      45 / (scale : ℝ) by norm_num [scale])
  have hphase : ((z ^ 2) ^ 2) ^ 2 = unitPhase (2 * Real.pi * (j.val : ℝ) / n) := by
    rw [← pow_mul, ← pow_mul]
    change unitPhase theta ^ (8 : ℕ) = _
    unfold unitPhase
    rw [← Complex.exp_nat_mul]
    congr 1
    have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast (Nat.zero_lt_of_lt j.isLt).ne'
    dsimp [theta]
    push_cast
    field_simp <;> ring
  rw [hphase] at h₃
  exact h₃

end Roots

section Cayley

def cayleyDen (a b : ℤ) : ℤ := a ^ 2 + b ^ 2

def cayleyNumerator (a b s : ℤ) : IntComplex :=
  (s * (b ^ 2 - a ^ 2), s * 2 * a * b)

def slopeNumerator (a b s : ℤ) : IntComplex :=
  (-s * 4 * (a * b) * b ^ 2, s * 2 * b ^ 2 * (b ^ 2 - a ^ 2))

def roundedCayley (a b s : ℤ) : IntComplex :=
  floorPair (scalePair scale (cayleyNumerator a b s)) (cayleyDen a b)

def roundedSlope (a b s : ℤ) : IntComplex :=
  floorPair (scalePair scale (slopeNumerator a b s)) (cayleyDen a b ^ 2)

noncomputable def cayley (t : ℝ) (s : ℤ) : ℂ :=
  (s : ℂ) * (1 + Complex.I * (t : ℂ)) / (1 - Complex.I * (t : ℂ))

noncomputable def cayleySlope (t : ℝ) (s : ℤ) : ℂ :=
  2 * (s : ℂ) * Complex.I / (1 - Complex.I * (t : ℂ)) ^ 2

private theorem cayleyDivisor_ne_zero (t : ℝ) : (1 - Complex.I * (t : ℂ)) ≠ 0 := by
  intro h
  have h' := congrArg Complex.re h
  simp [Complex.sub_re, Complex.mul_re] at h'

theorem cayley_error (a b s : ℤ) (hb : 0 < b) :
    ‖decode scale (roundedCayley a b s) - cayley ((a : ℝ) / (b : ℝ)) s‖ ≤ 2 / (scale : ℝ) ∧
      ‖decode scale (roundedSlope a b s) - cayleySlope ((a : ℝ) / (b : ℝ)) s‖ ≤
        2 / (scale : ℝ) := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hd : 0 < cayleyDen a b := by
    unfold cayleyDen
    exact add_pos_of_nonneg_of_pos (sq_nonneg _) (pow_pos hb _)
  have hdR : (0 : ℝ) < (a : ℝ) ^ 2 + (b : ℝ) ^ 2 :=
    add_pos_of_nonneg_of_pos (sq_nonneg _) (pow_pos hbR _)
  have hsR : (0 : ℝ) < scale := by exact_mod_cast scale_pos
  have hdiv := cayleyDivisor_ne_zero ((a : ℝ) / (b : ℝ))
  have hp : decode (cayleyDen a b : ℝ) (cayleyNumerator a b s) =
      cayley ((a : ℝ) / (b : ℝ)) s := by
    unfold cayley
    apply (eq_div_iff hdiv).2
    apply Complex.ext <;>
      simp [decode, cayleyDen, cayleyNumerator, Complex.mul_re, Complex.mul_im,
        Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im] <;>
      push_cast <;> field_simp <;> ring
  have hq : decode ((cayleyDen a b ^ 2 : ℤ) : ℝ) (slopeNumerator a b s) =
      cayleySlope ((a : ℝ) / (b : ℝ)) s := by
    unfold cayleySlope
    apply (eq_div_iff (pow_ne_zero 2 hdiv)).2
    apply Complex.ext <;>
      simp [decode, cayleyDen, slopeNumerator, pow_two, Complex.mul_re, Complex.mul_im,
        Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im] <;>
      push_cast <;> field_simp <;> ring
  constructor
  · have h := norm_decode_floor_le (scalePair scale (cayleyNumerator a b s)) hd hsR
    rwa [mul_comm (cayleyDen a b : ℝ), IntComplex.decode_scalePair _ _ scale_pos.ne', hp] at h
  · have h := norm_decode_floor_le (scalePair scale (slopeNumerator a b s)) (pow_pos hd 2) hsR
    rwa [mul_comm ((cayleyDen a b ^ 2 : ℤ) : ℝ),
      IntComplex.decode_scalePair _ _ scale_pos.ne', hq] at h

theorem cayley_norm_bounds (t : ℝ) (s : ℤ) (hs : s = 1 ∨ s = -1) :
    ‖cayley t s‖ = 1 ∧ ‖cayleySlope t s‖ ≤ 2 := by
  have hsign : ‖(s : ℂ)‖ = 1 := by rcases hs with rfl | rfl <;> simp
  have hm : ‖1 - Complex.I * (t : ℂ)‖ ^ 2 = 1 + t ^ 2 := by
    rw [Complex.sq_norm]
    simp [Complex.normSq_apply, Complex.mul_re, Complex.mul_im, Complex.sub_re,
      Complex.sub_im, pow_two]
  have hp : ‖1 + Complex.I * (t : ℂ)‖ ^ 2 = 1 + t ^ 2 := by
    rw [Complex.sq_norm]
    simp [Complex.normSq_apply, Complex.mul_re, Complex.mul_im, Complex.add_re,
      Complex.add_im, pow_two]
  have heq : ‖1 + Complex.I * (t : ℂ)‖ = ‖1 - Complex.I * (t : ℂ)‖ := by
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (hp.trans hm.symm)
  constructor
  · rw [cayley, norm_div, norm_mul, hsign, one_mul, heq,
      div_self (norm_ne_zero_iff.mpr (cayleyDivisor_ne_zero t))]
  · rw [cayleySlope, norm_div, norm_mul, norm_mul, hsign, Complex.norm_I, mul_one, mul_one,
      norm_pow, hm]
    have hden : (1 : ℝ) ≤ 1 + t ^ 2 := le_add_of_nonneg_right (sq_nonneg _)
    rw [Complex.norm_two]
    exact div_le_self (by norm_num) hden

end Cayley

section Seeds

private theorem scale_real_pos : (0 : ℝ) < (scale : ℝ) := by exact_mod_cast scale_pos

/-- Round a whole seed sum, maintained at S², once after division by n. -/
theorem roundedAverage_error {n : ℕ} (hn : 0 < n)
    (u : IntComplex) (a x : Fin n → ℂ) {e : ℝ}
    (hu : decode ((scale : ℝ) ^ 2) u = ∑ i, a i)
    (h : ∀ i, ‖a i - x i‖ ≤ e) :
    ‖decode scale (floorPair u ((n : ℤ) * scale)) -
      (n : ℝ)⁻¹ • (∑ i, x i)‖ ≤ 2 / (scale : ℝ) + e := by
  have hnZ : (0 : ℤ) < n := by exact_mod_cast hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hfloor := norm_decode_floor_le u (mul_pos hnZ scale_pos) scale_real_pos
  have hdecode : decode ((((n : ℤ) * scale : ℤ) : ℝ) * (scale : ℝ)) u =
      (n : ℝ)⁻¹ • (∑ i, a i) := by
    rw [show (((n : ℤ) * scale : ℤ) : ℝ) * (scale : ℝ) = (n : ℝ) * (scale : ℝ) ^ 2 by
      push_cast; ring, IntComplex.decode_mulScale, hu]
  rw [hdecode] at hfloor
  have hsum : ‖(∑ i, a i) - ∑ i, x i‖ ≤ (n : ℝ) * e := by
    simpa only [Finset.card_univ, Fintype.card_fin] using
      norm_sum_error_le Finset.univ a x (fun i _ => h i)
  have havg : ‖(n : ℝ)⁻¹ • (∑ i, a i) - (n : ℝ)⁻¹ • (∑ i, x i)‖ ≤ e := by
    rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hnR.le)]
    calc
      _ ≤ (n : ℝ)⁻¹ * ((n : ℝ) * e) := mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hnR.le)
      _ = e := by rw [← mul_assoc, inv_mul_cancel₀ hnR.ne', one_mul]
  exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add hfloor havg)

/-- Each integer orbit coefficient can be multiplied once after its root sum.
The fiber of a distinguished label can carry the fixed zero-frequency term. -/
theorem orbit_products_eq_frequency_sum {ι κ : Type*} [Fintype κ] [DecidableEq κ]
    (t : Finset ι) (orbit : ι → κ) (roots : ι → IntComplex) (factors : κ → IntComplex) :
    (∑ k, IntComplex.mul (∑ i ∈ t with orbit i = k, roots i) (factors k)) =
      ∑ i ∈ t, IntComplex.mul (roots i) (factors (orbit i)) := by
  rw [← Finset.sum_fiberwise t orbit (fun i => IntComplex.mul (roots i) (factors (orbit i)))]
  apply Finset.sum_congr rfl
  intro k _
  rw [IntComplex.mul_sum_left]
  apply Finset.sum_congr rfl
  intro i hi
  rw [(Finset.mem_filter.mp hi).2]

/-- The zero-frequency factor can use exact 1. Inactive slopes can use exact 0. -/
theorem chirpedSeed_error {n : ℕ} (hn : 0 < n) (u : IntComplex)
    (roots factors : Fin n → IntComplex) (z w : Fin n → ℂ)
    (hz : ∀ i, ‖z i‖ ≤ 1) (hr : ∀ i, ‖decode scale (roots i) - z i‖ ≤ 45 / (scale : ℝ))
    (hw : ∀ i, ‖decode scale (factors i) - w i‖ ≤ 2 / (scale : ℝ))
    (hu : u = ∑ i, IntComplex.mul (roots i) (factors i)) :
    (∀ i, ‖w i‖ ≤ 1) →
      ‖decode scale (floorPair u ((n : ℤ) * scale)) -
        (n : ℝ)⁻¹ • (∑ i, z i * w i)‖ ≤ 52 / (scale : ℝ) := by
  intro hwNorm
  have ha : decode ((scale : ℝ) ^ 2) u = ∑ i, decode scale (roots i) * decode scale (factors i) := by
    rw [hu, IntComplex.decode_sum, pow_two]
    simp only [IntComplex.decode_mul scale_real_pos.ne' scale_real_pos.ne']
  refine (roundedAverage_error hn u _ _ ha
    (e := 45 / (scale : ℝ) + (1 + 45 / (scale : ℝ)) * (2 / (scale : ℝ))) ?_).trans
      (by norm_num [scale])
  intro i
  simpa only [one_mul] using
    mul_error_le _ _ _ _ (hr i) (hw i) (hz i) (hwNorm i)

theorem chirpedSlope_error {n : ℕ} (hn : 0 < n) (u : IntComplex)
    (roots slopes : Fin n → IntComplex) (z w : Fin n → ℂ)
    (hz : ∀ i, ‖z i‖ ≤ 1) (hwNorm : ∀ i, ‖w i‖ ≤ 2)
    (hr : ∀ i, ‖decode scale (roots i) - z i‖ ≤ 45 / (scale : ℝ))
    (hw : ∀ i, ‖decode scale (slopes i) - w i‖ ≤ 2 / (scale : ℝ))
    (hu : u = ∑ i, IntComplex.mul (roots i) (slopes i)) :
    ‖decode scale (floorPair u ((n : ℤ) * scale)) -
      (n : ℝ)⁻¹ • (∑ i, z i * w i)‖ ≤ 97 / (scale : ℝ) := by
  have ha : decode ((scale : ℝ) ^ 2) u = ∑ i, decode scale (roots i) * decode scale (slopes i) := by
    rw [hu, IntComplex.decode_sum, pow_two]
    simp only [IntComplex.decode_mul scale_real_pos.ne' scale_real_pos.ne']
  refine (roundedAverage_error hn u _ _ ha
    (e := 2 * (45 / (scale : ℝ)) + (1 + 45 / (scale : ℝ)) * (2 / (scale : ℝ))) ?_).trans
      (by norm_num [scale])
  intro i
  exact mul_error_le _ _ _ _ (hr i) (hw i) (hz i) (hwNorm i)

def unchirpedSeed (d : Fin 73) (phase : IntComplex) : IntComplex :=
  ((if d = 0 then scale else 0), 0) + floorPair (phase - (scale, 0)) 73

def unchirpedSlope (slope : IntComplex) : IntComplex := floorPair slope 73

noncomputable def unchirpedSeedExact (d : Fin 73) (q : ℂ) : ℂ :=
  (if d = 0 then 1 else 0) + (73 : ℝ)⁻¹ • (q - 1)

/-- The uniform offset is rounded once. The exact indicator is added at scale S. -/
theorem unchirpedSeed_error (d : Fin 73) (phase : IntComplex) (q : ℂ)
    (hq : ‖decode scale phase - q‖ ≤ 2 / (scale : ℝ)) :
    ‖decode scale (unchirpedSeed d phase) - unchirpedSeedExact d q‖ ≤
      52 / (scale : ℝ) := by
  have hunit : decode scale (scale, 0) = 1 := by
    apply Complex.ext <;> simp [decode, scale_real_pos.ne']
  have hshift : decode scale (phase - (scale, 0)) = decode scale phase - 1 := by
    rw [← hunit]
    apply Complex.ext <;> simp [decode, Complex.sub_re, Complex.sub_im, sub_div]
  have hind : decode scale ((if d = 0 then scale else 0), 0) =
      (if d = 0 then (1 : ℂ) else 0) := by
    by_cases hd : d = 0
    · simpa only [hd, if_true] using hunit
    · simp [hd, decode, Complex.ext_iff]
  have hfloor := norm_decode_floor_le (phase - (scale, 0)) (by norm_num : (0 : ℤ) < 73)
    scale_real_pos
  rw [Int.cast_ofNat, IntComplex.decode_mulScale, hshift] at hfloor
  have herr : ‖(73 : ℝ)⁻¹ • (decode scale phase - 1) - (73 : ℝ)⁻¹ • (q - 1)‖ ≤
      (73 : ℝ)⁻¹ * (2 / (scale : ℝ)) := by
    rw [← smul_sub, sub_sub_sub_cancel_right, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left hq (by positivity)
  rw [unchirpedSeed, unchirpedSeedExact, IntComplex.decode_add, hind, add_sub_add_left_eq_sub]
  exact ((norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add hfloor herr)).trans
    (by norm_num [scale])

theorem unchirpedSlope_error (slope : IntComplex) (q' : ℂ)
    (hq : ‖decode scale slope - q'‖ ≤ 2 / (scale : ℝ)) :
    ‖decode scale (unchirpedSlope slope) - (73 : ℝ)⁻¹ • q'‖ ≤ 97 / (scale : ℝ) := by
  have hfloor := norm_decode_floor_le slope (by norm_num : (0 : ℤ) < 73) scale_real_pos
  rw [Int.cast_ofNat, IntComplex.decode_mulScale] at hfloor
  have herr : ‖(73 : ℝ)⁻¹ • decode scale slope - (73 : ℝ)⁻¹ • q'‖ ≤
      (73 : ℝ)⁻¹ * (2 / (scale : ℝ)) := by
    rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left hq (by positivity)
  exact ((norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add hfloor herr)).trans
    (by norm_num [scale])

end Seeds

section Correlations

def correlationInt {n : ℕ} (a b : Fin n → IntComplex) : IntComplex :=
  ∑ d, IntComplex.mul (IntComplex.conjugate (a d)) (b d)

noncomputable def correlation {n : ℕ} (a b : Fin n → ℂ) : ℂ :=
  ∑ d, conj (a d) * b d

private theorem decode_correlationInt {n : ℕ} (a b : Fin n → IntComplex) :
    decode ((scale : ℝ) ^ 2) (correlationInt a b) =
      correlation (fun d => decode scale (a d)) (fun d => decode scale (b d)) := by
  simp only [correlationInt, correlation, IntComplex.decode_sum, pow_two,
    IntComplex.decode_mul scale_real_pos.ne' scale_real_pos.ne', IntComplex.decode_conjugate]

private theorem correlation_error {n : ℕ} (a b : Fin n → IntComplex) (x y : Fin n → ℂ)
    {e₁ e₂ M₁ M₂ : ℝ}
    (ha : ∀ d, ‖decode scale (a d) - x d‖ ≤ e₁)
    (hb : ∀ d, ‖decode scale (b d) - y d‖ ≤ e₂)
    (hx : ∀ d, ‖x d‖ ≤ M₁) (hy : ∀ d, ‖y d‖ ≤ M₂) :
    ‖decode ((scale : ℝ) ^ 2) (correlationInt a b) - correlation x y‖ ≤
      (n : ℝ) * (M₂ * e₁ + (M₁ + e₁) * e₂) := by
  rw [decode_correlationInt]
  unfold correlation
  have hsum := norm_sum_error_le Finset.univ (fun d => conj (decode scale (a d)) * decode scale (b d))
    (fun d => conj (x d) * y d) (fun d _ => mul_error_le _ _ _ _
      (by simpa only [← map_sub, Complex.norm_conj] using ha d)
      (hb d) (by simpa only [Complex.norm_conj] using hx d) (hy d))
  simpa only [Finset.card_univ, Fintype.card_fin] using hsum

theorem correlation_value_error {n : ℕ} (a b : Fin n → IntComplex) (x y : Fin n → ℂ)
    (ha : ∀ d, ‖decode scale (a d) - x d‖ ≤ 52 / (scale : ℝ))
    (hb : ∀ d, ‖decode scale (b d) - y d‖ ≤ 52 / (scale : ℝ))
    (hx : ∀ d, ‖x d‖ ≤ 1) (hy : ∀ d, ‖y d‖ ≤ 1) :
    ‖decode ((scale : ℝ) ^ 2) (correlationInt a b) - correlation x y‖ ≤
      120 * (n : ℝ) / (scale : ℝ) := by
  refine (correlation_error a b x y ha hb hx hy).trans ?_
  calc
    _ ≤ (n : ℝ) * (120 / (scale : ℝ)) :=
      mul_le_mul_of_nonneg_left (by norm_num [scale]) (Nat.cast_nonneg n)
    _ = _ := by ring

/-- Both contributions are retained even when the same parameter acts on both sides. -/
theorem correlation_slope_error {n : ℕ} (a b da db : Fin n → IntComplex)
    (x y dx dy : Fin n → ℂ)
    (ha : ∀ d, ‖decode scale (a d) - x d‖ ≤ 52 / (scale : ℝ))
    (hb : ∀ d, ‖decode scale (b d) - y d‖ ≤ 52 / (scale : ℝ))
    (hda : ∀ d, ‖decode scale (da d) - dx d‖ ≤ 97 / (scale : ℝ))
    (hdb : ∀ d, ‖decode scale (db d) - dy d‖ ≤ 97 / (scale : ℝ))
    (hx : ∀ d, ‖x d‖ ≤ 1) (hy : ∀ d, ‖y d‖ ≤ 1)
    (hdx : ∀ d, ‖dx d‖ ≤ 2) (hdy : ∀ d, ‖dy d‖ ≤ 2) :
    ‖decode ((scale : ℝ) ^ 2) (correlationInt da b + correlationInt a db) -
      (correlation dx y + correlation x dy)‖ ≤ 420 * (n : ℝ) / (scale : ℝ) := by
  have hleft := correlation_error da b dx y hda hb hdx hy
  have hright := correlation_error a db x dy ha hdb hx hdy
  rw [IntComplex.decode_add, add_sub_add_comm]
  refine (norm_add_le _ _).trans ((add_le_add hleft hright).trans ?_)
  rw [← mul_add]
  calc
    _ ≤ (n : ℝ) * (420 / (scale : ℝ)) :=
      mul_le_mul_of_nonneg_left (by norm_num [scale]) (Nat.cast_nonneg n)
    _ = _ := by ring

def projectInt (imag : Bool) (z : IntComplex) : ℤ := if imag then z.2 else z.1

noncomputable def project (imag : Bool) (z : ℂ) : ℝ := if imag then z.im else z.re

/-- Convert the projected error directly to the cleared integer units of a row check. -/
theorem projected_error {n : ℕ} (imag : Bool) (u : IntComplex) (z : ℂ) (b : ℝ)
    (h : ‖decode ((scale : ℝ) ^ 2) u - z‖ ≤ b * (n : ℝ) / (scale : ℝ)) :
    |(scale : ℝ) ^ 2 * project imag z - (projectInt imag u : ℝ)| ≤ b * (n : ℝ) * (scale : ℝ) := by
  let S : ℝ := scale
  have hS : 0 < S := scale_real_pos
  have hS0 : S ≠ 0 := hS.ne'
  have hcoord :
      |(projectInt imag u : ℝ) / S ^ 2 - project imag z| ≤ b * (n : ℝ) / S := by
    cases imag
    · exact (Complex.abs_re_le_norm (decode (S ^ 2) u - z)).trans h
    · exact (Complex.abs_im_le_norm (decode (S ^ 2) u - z)).trans h
  calc
    _ = S ^ 2 * |(projectInt imag u : ℝ) / S ^ 2 - project imag z| := by
      have heq : S ^ 2 * ((projectInt imag u : ℝ) / S ^ 2 - project imag z) =
          - (S ^ 2 * project imag z - (projectInt imag u : ℝ)) := by
        field_simp <;> ring
      change |S ^ 2 * project imag z - (projectInt imag u : ℝ)| = _
      calc
        _ = |S ^ 2 * ((projectInt imag u : ℝ) / S ^ 2 - project imag z)| := by
          rw [heq, abs_neg]
        _ = _ := by rw [abs_mul, abs_of_pos (pow_pos hS 2)]
    _ ≤ S ^ 2 * (b * (n : ℝ) / S) := mul_le_mul_of_nonneg_left hcoord (sq_nonneg _)
    _ = _ := by
      change S ^ 2 * (b * (n : ℝ) / S) = b * (n : ℝ) * S
      field_simp <;> ring

end Correlations

end ChirpedReplay
