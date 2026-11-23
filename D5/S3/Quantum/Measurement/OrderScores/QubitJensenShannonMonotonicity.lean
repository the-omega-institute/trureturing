/- GID: D5/S3/Quantum/Measurement/OrderScores/QubitJensenShannonMonotonicity
   generality: I
   mirror-B: D5/B/S3/Quantum/Measurement/OrderScores/QubitJensenShannonMonotonicity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Wu's optimized qubit Jensen-Shannon order score increases strictly across the closed interval. -/

/-
admission_basis: open-problem-resolution
quantitative_increase: proof_shape: content. escape_witness: restricted_transport supplies one circle point at the larger parameter with every coefficient weakly larger.
result: proof_shape: content. escape_witness: circle_score_increment keeps the positive quadratic gain while the higher coefficients are nonnegative.
Direct frozen dependency: FiniteStateChannel.DensityState (in quantitative_increase).
QubitJensenShannon supplies the native score and entropy series.
-/

import D5.S3.Quantum.Measurement.OrderScores.QubitJensenShannon

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Quantum.Measurement.OrderScores.QubitJensenShannonMonotonicity

open Set Finset
open D5.S3.Quantum.Measurement.OrderScores.QubitJensenShannon

private theorem sum_range_even_odd (f : ℕ → ℝ) (n : ℕ) :
    (∑ i ∈ range (2 * n + 1), f i) =
      (∑ j ∈ range (n + 1), f (2 * j)) + ∑ j ∈ range n, f (2 * j + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 1 + 1 by omega,
      sum_range_succ, sum_range_succ, ih]
    rw [sum_range_succ (f := fun j => f (2*j)) (n+1),
      sum_range_succ (f := fun j => f (2*j+1)) n,
      show 2 * (n + 1) = (2 * n + 1) + 1 by omega]
    ring

private theorem avg_even_binomial (n : ℕ) (u v : ℝ) :
    ((u + v) ^ (2 * n) + (u - v) ^ (2 * n)) / 2 =
      ∑ j ∈ range (n + 1), ((2 * n).choose (2 * j) : ℝ) *
        (u ^ 2) ^ (n - j) * (v ^ 2) ^ j := by
  rw [add_comm u v, sub_eq_add_neg, add_comm u (-v), add_pow, add_pow, ← sum_add_distrib]
  rw [sum_range_even_odd]
  simp only [show ∀ k : ℕ, Even (2 * k) from fun k => even_two.mul_right k,
    show ∀ k : ℕ, Odd (2 * k + 1) from fun k => ⟨k, rfl⟩,
    Even.neg_pow, Odd.neg_pow, neg_mul, add_neg_cancel, sum_const_zero, add_zero]
  rw [div_eq_mul_inv, sum_mul]
  apply sum_congr rfl
  intro j _
  rw [show 2 * n - 2 * j = 2 * (n - j) by omega, pow_mul]
  ring

private theorem coeff_expansion (n : ℕ) (s u v : ℝ) :
    coeff n s u v =
      s * (u ^ 2) ^ (n + 1) + (1 - s) * (v ^ 2) ^ (n + 1) +
      ∑ j ∈ range n, ((2 * (n + 1)).choose (2 * (j + 1)) : ℝ) *
        (u ^ 2) ^ (n - j) * (v ^ 2) ^ (j + 1) := by
  unfold coeff
  rw [show 2 * n + 2 = 2 * (n + 1) by omega, avg_even_binomial, sum_range_succ,
    sum_range_succ']
  simp only [Nat.mul_zero, Nat.sub_zero, Nat.choose_zero_right, Nat.choose_self, Nat.cast_one, Nat.sub_self,
    pow_zero, one_mul, mul_one]
  rw [pow_mul u, pow_mul v]
  simp only [show ∀ j : ℕ, n + 1 - (j + 1) = n - j by omega]
  ring

private theorem coeff_le_of_sq_le (n : ℕ) {s u v u' v' : ℝ} (hs : s ∈ Set.Icc 0 1)
    (hu : u ^ 2 ≤ u' ^ 2) (hv : v ^ 2 ≤ v' ^ 2) :
    coeff n s u v ≤ coeff n s u' v' := by
  rw [coeff_expansion, coeff_expansion]
  have hs0 := hs.1
  have hX : 0 ≤ 1 - s := sub_nonneg.mpr hs.2
  gcongr

private theorem coeff_le_of_param_le (n : ℕ) {s t u v : ℝ} (hst : s ≤ t) (hv : v ^ 2 ≤ u ^ 2) :
    coeff n s u v ≤ coeff n t u v := by
  rw [coeff_expansion, coeff_expansion]
  have hp := pow_le_pow_left₀ (sq_nonneg v) hv (n + 1)
  have hh := mul_nonneg (sub_nonneg.mpr hst) (sub_nonneg.mpr hp)
  linarith only [hh]

private theorem circle_point_disk {w : ℝ} (hw : w ∈ Set.Icc 0 1) : circlePoint w ∈ disk := by
  change Real.sqrt w ^ 2 + Real.sqrt (1 - w) ^ 2 ≤ 1
  rw [Real.sq_sqrt hw.1, Real.sq_sqrt (sub_nonneg.mpr hw.2)]
  linarith

private theorem disk_coeff_mono (n : ℕ) {s : ℝ} (hs : s ∈ Set.Icc 0 1) {d e : ℝ × ℝ}
    (hx : d.1 ^ 2 ≤ e.1 ^ 2) (hz : d.2 ^ 2 ≤ e.2 ^ 2) :
    diskCoeff n s d ≤ diskCoeff n s e := by
  apply coeff_le_of_sq_le n hs
  · simpa only [mul_pow] using mul_le_mul_of_nonneg_left hz (sq_nonneg (Real.sqrt (1-s)))
  · simpa only [mul_pow] using mul_le_mul_of_nonneg_left hx (sq_nonneg (Real.sqrt s))

private theorem circle_dominates_disk {s : ℝ} (hs : s ∈ Set.Icc 0 1) {d : ℝ × ℝ} (hd : d ∈ disk) :
    ∃ w ∈ Set.Icc (0 : ℝ) 1, ∀ n, diskCoeff n s d ≤ diskCoeff n s (circlePoint w) := by
  obtain ⟨x,z⟩ := d
  change x ^ 2 + z ^ 2 ≤ 1 at hd
  have hw : x ^ 2 ∈ Set.Icc (0 : ℝ) 1 := ⟨sq_nonneg _, by nlinarith [sq_nonneg z]⟩
  refine ⟨x ^ 2, hw, fun n => disk_coeff_mono n hs ?_ ?_⟩
  · change x ^ 2 ≤ Real.sqrt (x ^ 2) ^ 2
    rw [Real.sq_sqrt hw.1]
  · change z ^ 2 ≤ Real.sqrt (1 - x ^ 2) ^ 2
    rw [Real.sq_sqrt (sub_nonneg.mpr hw.2)]
    linarith

private theorem first_circle_coeff {s w : ℝ} (hs : s ∈ Set.Icc 0 1) (hw : w ∈ Set.Icc 0 1) :
    diskCoeff 0 s (circlePoint w) = s * (1-s) := by
  unfold diskCoeff circlePoint
  simp only [coeff_zero, mul_pow, Real.sq_sqrt hs.1, Real.sq_sqrt hw.1,
    Real.sq_sqrt (sub_nonneg.mpr hs.2), Real.sq_sqrt (sub_nonneg.mpr hw.2)]
  ring

private theorem half_in_unit {s : ℝ} (hs : s ∈ Set.Icc 0 (1 / 2 : ℝ)) : s ∈ Set.Icc 0 1 :=
  ⟨hs.1, hs.2.trans (by norm_num)⟩

private theorem circle_bias_sq {s w : ℝ} (hs : s ∈ Set.Icc 0 1) (hw : w ∈ Set.Icc 0 1) :
    (Real.sqrt (1 - s) * (circlePoint w).2) ^ 2 = (1 - s) * (1 - w) ∧
    (Real.sqrt s * (circlePoint w).1) ^ 2 = s * w := by
  simp [circlePoint, mul_pow, Real.sq_sqrt hs.1, Real.sq_sqrt hw.1,
    Real.sq_sqrt (sub_nonneg.mpr hs.2), Real.sq_sqrt (sub_nonneg.mpr hw.2)]

/-- One sign change gives a lower bound throughout the unit interval. -/
private theorem one_sign_change (n j : ℕ) (q : ℕ → ℝ) (y : ℝ) (hy : 0 ≤ y) (hy' : y ≤ 1)
    (hpos : ∀ k < n, k ≤ j → 0 ≤ q k)
    (hneg : ∀ k < n, j < k → q k ≤ 0) :
    y ^ j * (∑ k ∈ range n, q k) ≤ ∑ k ∈ range n, q k * y ^ k := by
  rw [mul_sum]
  apply sum_le_sum
  intro k hk
  have hkn := mem_range.mp hk
  rw [mul_comm (y ^ j)]
  rcases le_or_gt k j with hkj | hjk
  · exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hy hy' hkj) (hpos k hkn hkj)
  · exact mul_le_mul_of_nonpos_left (pow_le_pow_of_le_one hy hy' hjk.le) (hneg k hkn hjk)

/-- The exact closed-interval gain from the first nonzero series coefficient. -/
private theorem first_coefficient_strict {s t : ℝ} (hst : s < t) (ht : t ≤ 1 / 2) :
    s * (1 - s) < t * (1 - t) := by
  have hp : 0 < (t - s) * (1 - t - s) := mul_pos (by linarith) (by linarith)
  linarith only [show t * (1 - t) - s * (1 - s) = (t - s) * (1 - t - s) by ring, hp]

/-- The weaker bound needed at both derivatives follows from a stronger power bound. -/
private theorem endpoint_power (n : ℕ) (s : ℝ) (hs : 0 ≤ s) (hh : s ≤ 1 / 2) :
    (1 - 2 * s) ^ (2 * n + 1) ≤ (1 - s) ^ (2 * (n + 1)) - s ^ (2 * (n + 1)) := by
  have hd : 0 ≤ 1 - 2 * s := by linarith
  have hdu : 1 - 2 * s ≤ 1 := by linarith
  have hsquare : 1 - 2 * s ≤ (1 - s) ^ 2 := by nlinarith [sq_nonneg s]
  have hrec : ∀ k : ℕ, (1 - 2 * s) ^ k ≤ (1 - s) ^ (2 * k) - s ^ (2 * k) ∨ k = 0 := by
    intro k
    induction k with
    | zero => exact Or.inr rfl
    | succ k ih =>
      left
      rcases ih with ih | rfl
      · have hmul := mul_le_mul ih hsquare hd ((pow_nonneg hd k).trans ih)
        have hn : 0 ≤ s ^ (2 * k) * (1 - 2 * s) := mul_nonneg (pow_nonneg hs _) hd
        rw [pow_succ, Nat.mul_succ, pow_add, pow_add]
        nlinarith only [hmul, hn,
          show (1 - s) ^ 2 - s ^ 2 = 1 - 2 * s by ring,
          show s ^ (2 * k) * ((1 - s) ^ 2 - s ^ 2) = s ^ (2 * k) * (1 - 2 * s) by ring]
      · simp
        ring_nf
        norm_num
  have hstrong := (hrec (n + 1)).resolve_right (by omega)
  exact (pow_le_pow_of_le_one hd hdu (by omega : n + 1 ≤ 2 * n + 1)).trans hstrong

private def chooseR (n k : ℕ) : ℝ := (n.choose k : ℝ)

private theorem adjacent_choose (d k : ℕ) (hk : k ≤ d) :
    chooseR d (k+1) * ((k:ℝ)+1) = chooseR d k * ((d:ℝ)-k) := by
  unfold chooseR
  have hh := congrArg (fun m : ℕ => (m : ℝ)) (Nat.choose_succ_right_eq d k)
  simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_sub hk] using hh

private def gradientCoeff (n : ℕ) (s : ℝ) (j : ℕ) : ℝ :=
  chooseR (2*n+1) (2*j+1) - ((1-s)/s) * chooseR (2*n+1) (2*j) +
    (if j=0 then (1-s)^2/s else 0) - (if j=n then s else 0)

private def gradient (n : ℕ) (s y : ℝ) : ℝ :=
  ∑ j ∈ range (n+1), gradientCoeff n s j * y^j

private theorem gradient_coeff_first {n : ℕ} (hn : 0 < n) {s : ℝ} (hs : 0 < s) :
    gradientCoeff n s 0 = (2*(n:ℝ)+1) - (1-s) := by
  have hn' : (0 : ℕ) ≠ n := by omega
  simp [gradientCoeff, chooseR, hn']
  field_simp
  ring

private theorem gradient_coeff_last {n : ℕ} (hn : 0 < n) {s : ℝ} (hs : 0 < s)
    (hS : s ≤ 1/2) : gradientCoeff n s n ≤ 0 := by
  simp [gradientCoeff, chooseR, hn.ne']
  have hRatio : 1 ≤ (1-s)/s := (le_div_iff₀ hs).2 (by linarith)
  have hCast : (1 : ℝ) ≤ 2*(n:ℝ)+1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
  have hP := mul_le_mul hRatio hCast (by norm_num : (0:ℝ) ≤ 1)
    (show 0 ≤ (1-s)/s from (by norm_num : (0:ℝ) ≤ 1).trans hRatio)
  nlinarith only [hP, hs]

private theorem gradient_coeff_interior {n j : ℕ} (hj : 0 < j) (hjn : j < n) (s : ℝ) :
    gradientCoeff n s j =
      chooseR (2*n+1) (2*j) * (((2*(n:ℝ)+1-2*j)/(2*j+1)) - (1-s)/s) := by
  have hc := adjacent_choose (2*n+1) (2*j) (by omega)
  push_cast at hc
  have hN : (2*(j:ℝ)+1) ≠ 0 := by positivity
  have he := (eq_div_iff hN).mpr hc
  rw [gradientCoeff, he]
  simp only [ite_eq_right hj.ne', ite_eq_right (ne_of_lt hjn)]
  ring

private theorem gradient_coeff_cut {n : ℕ} (hn : 0 < n) {s : ℝ} (hs : 0 < s)
    (hS : s ≤ 1/2) :
    ∃ k, (∀ j < n+1, j ≤ k → 0 ≤ gradientCoeff n s j) ∧
      ∀ j < n+1, k < j → gradientCoeff n s j ≤ 0 := by
  have h0 : 0 ≤ gradientCoeff n s 0 := by
    rw [gradient_coeff_first hn hs]
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hlast := gradient_coeff_last hn hs hS
  have hdown (j k : ℕ) (hjk : j ≤ k) (hkn : k ≤ n)
      (hneg : gradientCoeff n s j < 0) : gradientCoeff n s k ≤ 0 := by
    rcases eq_or_lt_of_le hkn with rfl | hkn
    · exact hlast
    have hj : 0 < j := by
      by_contra! he
      have : j = 0 := by omega
      subst j
      exact (not_lt_of_ge h0) hneg
    have hkn' : 0 < k := hj.trans_le hjk
    rw [gradient_coeff_interior hj (hjk.trans_lt hkn) s] at hneg
    rw [gradient_coeff_interior hkn' hkn s]
    have hjc : (j:ℝ) ≤ k := by exact_mod_cast hjk
    have hnum : 2*(n:ℝ)+1-2*k ≤ 2*(n:ℝ)+1-2*j := by linarith
    have hD : 0 < 2*(j:ℝ)+1 := by positivity
    have hD' : 0 < 2*(k:ℝ)+1 := by positivity
    have hN' : 0 ≤ 2*(n:ℝ)+1-2*k := by
      have : (k:ℝ) ≤ n := by exact_mod_cast hkn.le
      linarith
    have hle : (2*(n:ℝ)+1-2*k)/(2*k+1) ≤ (2*(n:ℝ)+1-2*j)/(2*j+1) :=
      (div_le_div_of_nonneg_left hN' hD (by linarith)).trans
        (div_le_div_of_nonneg_right hnum hD.le)
    have hneg' : (2*(n:ℝ)+1-2*j)/(2*j+1)-(1-s)/s < 0 :=
      neg_of_mul_neg_right hneg (by unfold chooseR; positivity)
    exact mul_nonpos_of_nonneg_of_nonpos (by unfold chooseR; positivity)
      ((sub_le_sub_right hle _).trans hneg'.le)
  by_cases hex : ∃ j, gradientCoeff n s j < 0
  · let j := Nat.find hex
    have hj : gradientCoeff n s j < 0 := Nat.find_spec hex
    have hj0 : 0 < j := by
      by_contra! he
      have h : j = 0 := by omega
      exact (not_lt_of_ge (h ▸ h0)) hj
    refine ⟨j-1, ?_, ?_⟩
    · intro k _ hk
      exact le_of_not_gt (Nat.find_min hex (by omega : k < j))
    · intro k hkn hk
      exact hdown j k (by omega) (by omega) hj
  · exact ⟨n, fun j _ _ => le_of_not_gt (fun h => hex ⟨j,h⟩), fun _ h₁ h₂ => by omega⟩

private theorem gradient_nonneg_below {n : ℕ} (hn : 0 < n) {s y z : ℝ} (hs : 0 < s)
    (hS : s ≤ 1/2) (hy : 0 ≤ y) (hyz : y ≤ z) (hz : 0 < z)
    (hgrad : 0 ≤ gradient n s z) : 0 ≤ gradient n s y := by
  obtain ⟨k,hpos,hneg⟩ := gradient_coeff_cut hn hs hS
  let c (j : ℕ) := gradientCoeff n s j * z^j
  have hh := one_sign_change (n+1) k c (y/z) (div_nonneg hy hz.le) ((div_le_one hz).2 hyz)
    (fun j hj hjk => mul_nonneg (hpos j hj hjk) (pow_nonneg hz.le _))
    (fun j hj hjk => mul_nonpos_of_nonpos_of_nonneg (hneg j hj hjk) (pow_nonneg hz.le _))
  have he : (∑ j ∈ range (n+1), c j * (y/z)^j) = gradient n s y := by
    unfold gradient
    apply sum_congr rfl
    intro j _
    dsimp [c]
    rw [mul_assoc, ← mul_pow, ← mul_div_assoc, mul_div_cancel_left₀ y hz.ne']
  rw [he] at hh
  exact (mul_nonneg (pow_nonneg (div_nonneg hy hz.le) _) hgrad).trans hh

private def evenPart (n : ℕ) (q : ℝ) : ℝ :=
  ∑ j ∈ range (n+1), chooseR (2*n+1) (2*j) * q^(2*j)

private def oddPart (n : ℕ) (q : ℝ) : ℝ :=
  ∑ j ∈ range (n+1), chooseR (2*n+1) (2*j+1) * q^(2*j+1)

private theorem one_add_odd_pow (n : ℕ) (q : ℝ) :
    (1+q)^(2*n+1) = evenPart n q + oddPart n q := by
  rw [add_comm, add_pow]
  simp only [one_pow, mul_one]
  rw [show 2*n+1+1 = (2*n+1)+1 by rfl, sum_range_succ, sum_range_even_odd]
  unfold oddPart evenPart chooseR
  rw [sum_range_succ (f := fun j => ((2*n+1).choose (2*j+1) : ℝ) * q^(2*j+1)) n]
  simp only [mul_comm (q ^ _) (_ : ℝ)]
  ring

private theorem one_sub_odd_pow (n : ℕ) (q : ℝ) :
    (1-q)^(2*n+1) = evenPart n q - oddPart n q := by
  rw [sub_eq_add_neg, one_add_odd_pow]
  unfold evenPart oddPart
  simp only [show ∀ j : ℕ, Even (2*j) from fun j => even_two.mul_right j,
    show ∀ j : ℕ, Odd (2*j+1) from fun j => ⟨j,rfl⟩,
    Even.neg_pow, Odd.neg_pow, mul_neg, sum_neg_distrib, sub_eq_add_neg]

private theorem gradient_identity (n : ℕ) (s q : ℝ) :
    ((1 - ((1-s)/s)*q)*(1+q)^(2*n+1) -
      (1 + ((1-s)/s)*q)*(1-q)^(2*n+1)) / 2 +
    (1-s) * (((1-s)/s)*q) - s*q^(2*n+1) =
    q * gradient n s (q^2) := by
  rw [one_add_odd_pow, one_sub_odd_pow]
  calc
    _ = oddPart n q - ((1-s)/s)*q * evenPart n q + (1-s)^2/s*q - s*q^(2*n+1) := by ring
    _ = _ := by
      let R := range (n+1)
      have he : evenPart n q = ∑ j ∈ R, chooseR (2*n+1) (2*j) * (q^2)^j := by
        unfold evenPart
        simp only [R, pow_mul]
      have ho : oddPart n q = q * ∑ j ∈ R, chooseR (2*n+1) (2*j+1) * (q^2)^j := by
        unfold oddPart
        rw [mul_sum]
        apply sum_congr rfl
        intro j _
        rw [pow_succ, pow_mul]
        ring
      have hf : (∑ j ∈ R, (if j=0 then (1-s)^2/s else 0) * (q^2)^j) = (1-s)^2/s := by
        rw [sum_eq_single 0]
        · simp
        · intro j _ hj
          simp [hj]
        · simp [R]
      have hlast : (∑ j ∈ R, (if j=n then s else 0) * (q^2)^j) = s * (q^2)^n := by
        rw [sum_eq_single n]
        · simp
        · intro j _ hj
          simp [hj]
        · simp [R]
      rw [ho, he]
      unfold gradient
      change _ = q * ∑ j ∈ R, gradientCoeff n s j * (q^2)^j
      simp only [gradientCoeff, sub_mul, add_mul, sum_add_distrib, sum_sub_distrib, hf, hlast]
      simp_rw [mul_assoc]
      rw [← mul_sum, pow_succ q (2*n), pow_mul]
      ring

private def uCircle (s w : ℝ) : ℝ := Real.sqrt (1-s) * Real.sqrt (1-w)
private def vCircle (s w : ℝ) : ℝ := Real.sqrt s * Real.sqrt w

private theorem has_deriv_at_u_circle {s w : ℝ} (hs : s < 1) (hw : w < 1) :
    HasDerivAt (uCircle s) (-(1-s)/(2*uCircle s w)) w := by
  have hS : 0 < 1-s := sub_pos.mpr hs
  have hW : 0 < 1-w := sub_pos.mpr hw
  have hm := (Real.sqrt_pos.2 hS).ne'
  have hn := (Real.sqrt_pos.2 hW).ne'
  have hd := (Real.hasDerivAt_sqrt hW.ne').comp w
    ((hasDerivAt_const w (1 : ℝ)).sub (hasDerivAt_id w))
  apply (hd.const_mul (Real.sqrt (1-s))).congr_deriv
  simp only [zero_sub, uCircle]
  field_simp
  nlinarith [Real.sq_sqrt hS.le]

private theorem has_deriv_at_v_circle {s w : ℝ} (hs : 0 < s) (hw : 0 < w) :
    HasDerivAt (vCircle s) (s/(2*vCircle s w)) w := by
  have hm := (Real.sqrt_pos.2 hs).ne'
  have hn := (Real.sqrt_pos.2 hw).ne'
  apply ((Real.hasDerivAt_sqrt hw.ne').const_mul (Real.sqrt s)).congr_deriv
  unfold vCircle
  field_simp
  nlinarith [Real.sq_sqrt hs.le]

private theorem gradient_nonneg_at_end (n : ℕ) {s : ℝ} (hs : 0 < s) (hS : s ≤ 1/2) :
    0 ≤ gradient n s ((s/(1-s))^2) := by
  let X := 1-s
  let q := s/X
  have hX : 0 < X := by dsimp [X]; linarith
  have hq : 0 < q := div_pos hs hX
  have h : X/s*q = 1 := by dsimp [q]; field_simp
  have hh := gradient_identity n s q
  change ((1-X/s*q)*(1+q)^(2*n+1)-(1+X/s*q)*(1-q)^(2*n+1))/2+X*(X/s*q)-
    s*q^(2*n+1) = q * gradient n s (q^2) at hh
  rw [h] at hh
  have hs' : X*q = s := by
    dsimp [q]
    rw [← mul_div_assoc, mul_div_cancel_left₀ s hX.ne']
  have hp : X*(1-q) = 1-2*s := by
    rw [mul_sub, mul_one, hs']
    dsimp [X]
    ring
  have he : X^(2*n+1) * (q * gradient n s (q^2)) =
      X^(2*(n+1)) - s^(2*(n+1)) - (1-2*s)^(2*n+1) := by
    rw [← hh, show 2*(n+1) = (2*n+1)+1 by omega, pow_succ X, pow_succ s,
      ← hp, ← hs', mul_pow, mul_pow]
    ring
  have hb : 0 ≤ X^(2*(n+1)) - s^(2*(n+1)) - (1-2*s)^(2*n+1) :=
    sub_nonneg.mpr (endpoint_power n s hs.le hS)
  rw [← he] at hb
  exact nonneg_of_mul_nonneg_right (nonneg_of_mul_nonneg_right hb (pow_pos hX _)) hq

private theorem has_deriv_at_circle_coeff (n : ℕ) {s w : ℝ} (hs : s ∈ Set.Ioo (0 : ℝ) 1)
    (hw : w ∈ Set.Ioo (0 : ℝ) 1) :
    let u := uCircle s w
    let v := vCircle s w
    let q := v/u
    HasDerivAt (fun z => diskCoeff n s (circlePoint z))
      (((n:ℝ)+1) * (s/v) * u^(2*n+1) * (q * gradient n s (q^2))) w := by
  dsimp only
  let u := uCircle s w
  let v := vCircle s w
  let q := v/u
  let X := 1-s
  have hX : 0 < X := sub_pos.mpr hs.2
  have hu : 0 < u := mul_pos (Real.sqrt_pos.2 hX) (Real.sqrt_pos.2 (sub_pos.mpr hw.2))
  have hv : 0 < v := mul_pos (Real.sqrt_pos.2 hs.1) (Real.sqrt_pos.2 hw.1)
  have hdU := has_deriv_at_u_circle hs.2 hw.2
  have hdV := has_deriv_at_v_circle hs.1 hw.1
  have hd₁ := ((hdU.add hdV).pow (2*n+2)).add ((hdU.sub hdV).pow (2*n+2))
  have hd₂ := (((hd₁.div_const 2).sub ((hdU.pow (2*n+2)).const_mul X)).sub
    ((hdV.pow (2*n+2)).const_mul s))
  change HasDerivAt (fun z => coeff n s (uCircle s z) (vCircle s z))
    (((n:ℝ)+1) * (s/v) * u^(2*n+1) * (q * gradient n s (q^2))) w
  apply hd₂.congr_deriv
  have hplus : (u+v)^(2*n+1) = u^(2*n+1) * (1+q)^(2*n+1) := by
    rw [← mul_pow]
    congr 1
    dsimp [q]
    field_simp
  have hminus : (u-v)^(2*n+1) = u^(2*n+1) * (1-q)^(2*n+1) := by
    rw [← mul_pow]
    congr 1
    dsimp [q]
    field_simp
  have hq : v^(2*n+1) = u^(2*n+1) * q^(2*n+1) := by
    rw [← mul_pow]
    congr 1
    dsimp [q]
    field_simp
  change (((((2*n+2:ℕ):ℝ)*(u+v)^(2*n+2-1)*(-X/(2*u)+s/(2*v)) +
      ((2*n+2:ℕ):ℝ)*(u-v)^(2*n+2-1)*(-X/(2*u)-s/(2*v)))/2 -
      X*(((2*n+2:ℕ):ℝ)*u^(2*n+2-1)*(-X/(2*u)))) -
      s*(((2*n+2:ℕ):ℝ)*v^(2*n+2-1)*(s/(2*v)))) =
        ((n:ℝ)+1) * (s/v) * u^(2*n+1) * (q * gradient n s (q^2))
  have hf : (s/v) * (X/s*q) = X/u := by
    dsimp [q]
    field_simp [hs.1.ne', hu.ne', hv.ne']
  have hh := gradient_identity n s q
  change ((1-(X/s)*q)*(1+q)^(2*n+1)-(1+(X/s)*q)*(1-q)^(2*n+1))/2+
    X*(X/s*q)-s*q^(2*n+1) = _ at hh
  rw [show 2*n+2-1 = 2*n+1 by omega, hplus, hminus, hq, ← hh]
  push_cast
  have hfU : -X/(2*u) = -(s/v)*(X/s*q)/2 := by
    rw [neg_mul, hf]
    field_simp [hu.ne']
  have hfV : s/(2*v) = (s/v)/2 := by field_simp [hv.ne']
  rw [hfU, hfV]
  ring

private theorem lower_circle_mono (n : ℕ) {s : ℝ} (hs : s ∈ Set.Icc 0 (1 / 2 : ℝ)) :
    MonotoneOn (fun w => diskCoeff n s (circlePoint w)) (Set.Icc 0 s) := by
  by_cases h0 : s = 0
  · subst s
    intro a ha b hb _
    have he : a=b := (le_antisymm ha.2 ha.1).trans (le_antisymm hb.2 hb.1).symm
    rw [he]
  have hs0 := lt_of_le_of_ne hs.1 (Ne.symm h0)
  have hs1 : s < 1 := hs.2.trans_lt (by norm_num)
  have hsI := half_in_unit hs
  by_cases hn : n = 0
  · subst n
    intro a ha b hb _
    change diskCoeff 0 s (circlePoint a) ≤ diskCoeff 0 s (circlePoint b)
    rw [first_circle_coeff hsI ⟨ha.1,ha.2.trans hsI.2⟩,
      first_circle_coeff hsI ⟨hb.1,hb.2.trans hsI.2⟩]
  have hderiv (w : ℝ) (hw : w ∈ Set.Ioo 0 s) :=
    has_deriv_at_circle_coeff n ⟨hs0,hs1⟩ ⟨hw.1,hw.2.trans hs1⟩
  have hc : Continuous (fun w => diskCoeff n s (circlePoint w)) := by
    unfold diskCoeff circlePoint coeff
    fun_prop
  apply monotoneOn_of_deriv_nonneg (convex_Icc _ _) hc.continuousOn
  · rw [interior_Icc]
    intro w hw
    exact (hderiv w hw).differentiableAt.differentiableWithinAt
  rw [interior_Icc]
  intro w hw
  let u := uCircle s w
  let v := vCircle s w
  have hX : 0 < 1-s := sub_pos.mpr hs1
  have hu : 0 < u := mul_pos (Real.sqrt_pos.2 hX)
    (Real.sqrt_pos.2 (sub_pos.mpr (hw.2.trans hs1)))
  have hv : 0 < v := mul_pos (Real.sqrt_pos.2 hs0) (Real.sqrt_pos.2 hw.1)
  have hu' : 1-s ≤ u := by
    unfold u uCircle
    calc
      1-s = Real.sqrt (1-s)*Real.sqrt (1-s) := (Real.mul_self_sqrt hX.le).symm
      _ ≤ _ := by gcongr; linarith [hw.2]
  have hv' : v ≤ s := by
    unfold v vCircle
    calc
      _ ≤ Real.sqrt s*Real.sqrt s := by gcongr; linarith [hw.2]
      _ = s := Real.mul_self_sqrt hs.1
  have hq : v/u ≤ s/(1-s) :=
    (div_le_div_of_nonneg_right hv' hu.le).trans (div_le_div_of_nonneg_left hs.1 hX hu')
  rw [(hderiv w hw).deriv]
  change 0 ≤ ((n:ℝ)+1)*(s/v)*u^(2*n+1)*
    (v/u * gradient n s ((v/u)^2))
  have hgrad := gradient_nonneg_below (Nat.pos_of_ne_zero hn) hs0 hs.2 (sq_nonneg (v/u))
    (pow_le_pow_left₀ (div_nonneg hv.le hu.le) hq 2) (by positivity)
    (gradient_nonneg_at_end n hs0 hs.2)
  positivity

private theorem reflected_pair {X S W V : ℝ} (hS : 0 ≤ S) (hSX : S ≤ X)
    (hV : 0 ≤ V) (hVW : V ≤ W) (p q : ℕ) :
    (X * V)^p * (S * W)^q + (X * V)^q * (S * W)^p ≤
    (X * W)^p * (S * V)^q + (X * W)^q * (S * V)^p := by
  wlog hpq : q ≤ p generalizing p q
  · rw [add_comm, add_comm ((X * W)^p * (S * V)^q)]
    exact this q p (by omega)
  have hp : p = q + (p-q) := by omega
  have hpow (a : ℝ) : a^p = a^q * a^(p-q) := by
    nth_rw 1 [hp]
    rw [pow_add]
  simp only [hpow]
  have he :
      (X * W)^q * (X * W)^(p-q) * (S * V)^q +
          (X * W)^q * ((S * V)^q * (S * V)^(p-q)) -
        ((X * V)^q * (X * V)^(p-q) * (S * W)^q +
          (X * V)^q * ((S * W)^q * (S * W)^(p-q))) =
      (X*S*W*V)^q * ((X^(p-q)-S^(p-q)) * (W^(p-q)-V^(p-q))) := by
    simp only [mul_pow]
    ring
  apply sub_nonneg.mp
  rw [he]
  have hX := hS.trans hSX
  have hW := hV.trans hVW
  exact mul_nonneg (pow_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hX hS) hW) hV) _)
    (mul_nonneg (sub_nonneg.mpr (pow_le_pow_left₀ hS hSX _))
      (sub_nonneg.mpr (pow_le_pow_left₀ hV hVW _)))

private theorem circle_reflection (n : ℕ) {s w : ℝ} (hs : s ∈ Set.Icc 0 (1 / 2 : ℝ))
    (hw : w ∈ Set.Icc (1 / 2 : ℝ) 1) :
    diskCoeff n s (circlePoint w) ≤ diskCoeff n s (circlePoint (1 - w)) := by
  have hX : s ≤ 1-s := by linarith [hs.2]
  have hw0 : w ∈ Set.Icc 0 1 := ⟨by linarith [hw.1], hw.2⟩
  have hv0 : 1-w ∈ Set.Icc 0 1 := ⟨sub_nonneg.mpr hw.2, by linarith [hw.1]⟩
  obtain ⟨hu,hv⟩ := circle_bias_sq (half_in_unit hs) hw0
  obtain ⟨hu',hv'⟩ := circle_bias_sq (half_in_unit hs) hv0
  unfold diskCoeff
  rw [coeff_expansion, coeff_expansion, hu, hv, hu', hv',
    show 1 - (1 - w) = w by ring]
  have hend :
      s * ((1-s)*(1-w))^(n+1) + (1-s) * (s*w)^(n+1) ≤
      s * ((1-s)*w)^(n+1) + (1-s) * (s*(1-w))^(n+1) := by
    apply sub_nonneg.mp
    have he :
        s * ((1-s)*w)^(n+1) + (1-s) * (s*(1-w))^(n+1) -
          (s * ((1-s)*(1-w))^(n+1) + (1-s) * (s*w)^(n+1)) =
        (s*(1-s)) * (((1-s)^n - s^n) * (w^(n+1) - (1-w)^(n+1))) := by
      simp only [mul_pow, pow_succ _ n]
      ring
    rw [he]
    exact mul_nonneg (mul_nonneg hs.1 (hs.1.trans hX))
      (mul_nonneg (sub_nonneg.mpr (pow_le_pow_left₀ hs.1 hX _))
        (sub_nonneg.mpr (pow_le_pow_left₀ hv0.1 (by linarith [hw.1]) _)))
  apply add_le_add hend
  let term (a b : ℝ) (j : ℕ) :=
    ((2 * (n + 1)).choose (2 * (j + 1)) : ℝ) * a^(n-j) * b^(j+1)
  have hpaired (a b : ℝ) :
      (∑ j ∈ range n, (term a b j + term a b (n - 1 - j))) =
        2 * ∑ j ∈ range n, term a b j := by
    rw [sum_add_distrib, sum_range_reflect]
    ring
  change (∑ j ∈ range n, term ((1-s)*(1-w)) (s*w) j) ≤
    ∑ j ∈ range n, term ((1-s)*w) (s*(1-w)) j
  apply le_of_mul_le_mul_left _ (by norm_num : (0:ℝ) < 2)
  rw [← hpaired, ← hpaired]
  apply sum_le_sum
  intro j hj
  have hjn := mem_range.mp hj
  have h₁ : n - (n - 1 - j) = j+1 := by omega
  have h₂ : n - 1 - j + 1 = n-j := by omega
  have hchoose : (2*(n+1)).choose (2*(n-j)) = (2*(n+1)).choose (2*(j+1)) := by
    rw [← Nat.choose_symm (show 2*(j+1) ≤ 2*(n+1) by omega)]
    congr 1
    omega
  simp only [term, h₁, h₂, hchoose]
  have h := reflected_pair (W := w) hs.1 hX hv0.1 (by linarith [hw.1]) (n-j) (j+1)
  convert mul_le_mul_of_nonneg_left h (show 0 ≤ ((2*(n+1)).choose (2*(j+1)) : ℝ) by positivity)
    using 1 <;> ring

private def diagonalCoeff (n : ℕ) (s : ℝ) : ℝ :=
  (1 + (1 - 2 * s) ^ (2 * n + 2)) / 2 -
    (1 - s) ^ (2 * n + 3) - s ^ (2 * n + 3)

private theorem diagonal_coeff_eq (n : ℕ) {s : ℝ} (hs : s ∈ Set.Icc 0 1) :
    diskCoeff n s (circlePoint s) = diagonalCoeff n s := by
  unfold diskCoeff
  simp only [circlePoint, ← sq, Real.sq_sqrt hs.1, Real.sq_sqrt (sub_nonneg.mpr hs.2)]
  unfold coeff diagonalCoeff
  rw [show 1 - s + s = 1 by ring, show 1 - s - s = 1 - 2*s by ring, one_pow]
  rw [show 2 * n + 3 = (2 * n + 2) + 1 by omega, pow_succ, pow_succ]
  ring

private theorem diagonal_coeff_mono (n : ℕ) :
    MonotoneOn (diagonalCoeff n) (Set.Icc 0 (1 / 2 : ℝ)) := by
  refine monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    (by unfold diagonalCoeff; fun_prop) (by unfold diagonalCoeff; fun_prop) ?_
  intro s hs
  have hs' : s ∈ Set.Icc 0 (1 / 2 : ℝ) := interior_subset hs
  have hpow := endpoint_power n s hs'.1 hs'.2
  have hpos : 0 ≤ (1 - 2 * s) ^ (2 * n + 1) :=
    pow_nonneg (by linarith [hs'.2]) _
  have hd := ((hasDerivAt_const s (1 : ℝ)).sub ((hasDerivAt_id s).const_mul 2)).pow (2 * n + 2)
  have hX := ((hasDerivAt_const s (1 : ℝ)).sub (hasDerivAt_id s)).pow (2 * n + 3)
  have hS := (hasDerivAt_id s).pow (2 * n + 3)
  have h := (((hasDerivAt_const s (1 : ℝ)).add hd).div_const 2).sub hX |>.sub hS
  have h' : HasDerivAt (diagonalCoeff n) _ s := h
  rw [h'.deriv]
  simp only [Pi.sub_apply, id_eq, mul_one, zero_sub, zero_add, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
    show 2*n+2-1 = 2*n+1 by omega, show 2*n+3-1 = 2*(n+1) by omega]
  have hmul := mul_nonneg (show 0 ≤ 2 * (n : ℝ) + 3 by positivity) (sub_nonneg.mpr hpow)
  nlinarith only [hmul, hpos]

private theorem fixed_midpoint_transport {s t w U : ℝ} (hs : s ∈ Set.Icc 0 (1 / 2 : ℝ))
    (ht : t ∈ Set.Icc 0 (1 / 2 : ℝ)) (hst : s ≤ t)
    (hw : w ∈ Set.Icc s (1 / 2 : ℝ)) (hU : U ^ 2 = (1 - s) * (1 - w))
    (hU0 : 1 / 2 ≤ U) (htU : t ≤ 1 - U) :
    let w' := 1 - U ^ 2 / (1 - t)
    w' ∈ Set.Icc t (1 / 2 : ℝ) ∧
      ∀ n, diskCoeff n s (circlePoint w) ≤ diskCoeff n t (circlePoint w') := by
  dsimp
  let w' := 1 - U ^ 2 / (1 - t)
  have hX : 0 < 1 - s := by linarith [hs.2]
  have hY : 0 < 1 - t := by linarith [ht.2]
  have hw0 : w ∈ Set.Icc 0 1 := ⟨hs.1.trans hw.1, hw.2.trans (by norm_num)⟩
  have hw'le : w' ≤ w := by
    have h := div_le_div_of_nonneg_left (sq_nonneg U) hY (by linarith : 1-t ≤ 1-s)
    rw [hU, mul_div_cancel_left₀ _ hX.ne', ← hU] at h
    change 1 - U ^ 2 / (1 - t) ≤ w
    linarith
  have hw'ge : t ≤ w' := by
    have hp := pow_le_pow_left₀ (show 0 ≤ U by linarith) (show U ≤ 1 - t by linarith) 2
    have hh : U^2 / (1-t) ≤ 1-t := (div_le_iff₀ hY).mpr (by nlinarith only [hp])
    change t ≤ 1 - U ^ 2 / (1 - t)
    linarith
  have hw' : w' ∈ Set.Icc t (1 / 2 : ℝ) := ⟨hw'ge, hw'le.trans hw.2⟩
  have hw'0 : w' ∈ Set.Icc 0 1 := ⟨ht.1.trans hw'ge, hw'.2.trans (by norm_num)⟩
  refine ⟨hw', fun n => ?_⟩
  obtain ⟨hu,hv⟩ := circle_bias_sq (half_in_unit hs) hw0
  obtain ⟨hu',hv'⟩ := circle_bias_sq (half_in_unit ht) hw'0
  have hU' : (1 - t) * (1 - w') = U ^ 2 := by
    dsimp [w']
    field_simp [hY.ne']
    ring
  have hdiv : U ^ 2 ≤ (1 - s) * (1 - t) := by
    have h₁ := mul_le_mul (show U ≤ 1 - s by linarith)
      (show U ≤ 1 - t by linarith) (show 0 ≤ U by linarith) hX.le
    nlinarith only [h₁]
  have hvmono : s*w ≤ t*w' := by
    have he : t*w' - s*w = (t-s) * (1 - U^2 / ((1-s)*(1-t))) := by
      have he0 : w = 1 - U ^ 2 / (1 - s) := by
        rw [hU, mul_div_cancel_left₀ _ hX.ne']
        ring
      rw [he0]
      dsimp [w']
      field_simp [hX.ne', hY.ne']
      ring
    rw [← sub_nonneg, he]
    exact mul_nonneg (sub_nonneg.mpr hst)
      (sub_nonneg.mpr ((div_le_one (mul_pos hX hY)).mpr hdiv))
  have hvle : s*w ≤ U ^ 2 := by
    rw [hU]
    nlinarith only [hw.2, hs.2]
  unfold diskCoeff
  calc
    _ ≤ coeff n t (Real.sqrt (1 - s) * (circlePoint w).2)
        (Real.sqrt s * (circlePoint w).1) :=
      coeff_le_of_param_le n hst (by rwa [hv, hu, ← hU])
    _ ≤ _ := coeff_le_of_sq_le n (half_in_unit ht)
      (by rw [hu, hu', ← hU, hU'])
      (by rwa [hv, hv'])

private theorem restricted_transport {s t w : ℝ} (hs : s ∈ Set.Icc 0 (1 / 2 : ℝ))
    (ht : t ∈ Set.Icc 0 (1 / 2 : ℝ)) (hst : s ≤ t)
    (hw : w ∈ Set.Icc s (1 / 2 : ℝ)) :
    ∃ w' ∈ Set.Icc t (1 / 2 : ℝ),
      ∀ n, diskCoeff n s (circlePoint w) ≤ diskCoeff n t (circlePoint w') := by
  let U := Real.sqrt ((1 - s) * (1 - w))
  have hs1 : 0 ≤ 1 - s := by linarith [hs.2]
  have hw1 : 0 ≤ 1 - w := by linarith [hw.2]
  have hU : U ^ 2 = (1 - s) * (1 - w) := Real.sq_sqrt (mul_nonneg hs1 hw1)
  have hUn : 0 ≤ U := Real.sqrt_nonneg _
  have hU0 : 1 / 2 ≤ U := by
    have hm := mul_le_mul (show 1 / 2 ≤ 1-s by linarith [hs.2])
      (show 1 / 2 ≤ 1-w by linarith [hw.2]) (by norm_num : 0 ≤ (1:ℝ)/2) hs1
    nlinarith [mul_nonneg hUn (show 0 ≤ (1:ℝ)/2 by norm_num)]
  have hU1 : U ≤ 1-s := by
    have hm := mul_le_mul_of_nonneg_left (show 1-w ≤ 1-s by linarith [hw.1]) hs1
    nlinarith [mul_nonneg hUn hs1]
  by_cases htU : t ≤ 1-U
  · exact ⟨_, fixed_midpoint_transport hs ht hst hw hU hU0 htU⟩
  · let q := 1-U
    have hq : q ∈ Set.Icc 0 (1/2 : ℝ) := ⟨by dsimp [q]; linarith [hs.1], by dsimp [q]; linarith⟩
    have hsq : s ≤ q := by dsimp [q]; linarith
    have hqt : q ≤ t := (lt_of_not_ge htU).le
    obtain ⟨_, hmono⟩ := fixed_midpoint_transport hs hq hsq hw hU hU0 (le_refl q)
    have hqeq : 1 - U ^ 2 / (1 - q) = q := by
      have hUne : U ≠ 0 := by linarith
      dsimp [q]
      rw [show 1 - (1 - U) = U by ring, pow_two, mul_div_cancel_left₀ U hUne]
    rw [hqeq] at hmono
    refine ⟨t, ⟨le_rfl, ht.2⟩, fun n => (hmono n).trans ?_⟩
    rw [diagonal_coeff_eq n (half_in_unit hq), diagonal_coeff_eq n (half_in_unit ht)]
    exact diagonal_coeff_mono n hq ht hqt

private theorem circle_score_increment {s t w z : ℝ} (hs : s ∈ Set.Icc 0 1) (ht : t ∈ Set.Icc 0 1)
    (hw : w ∈ Set.Icc 0 1) (hz : z ∈ Set.Icc 0 1)
    (hc : ∀ n, diskCoeff n s (circlePoint w) ≤ diskCoeff n t (circlePoint z)) :
    (t * (1 - t) - s * (1 - s)) / (2 * Real.log 2) ≤
      diskScore t (circlePoint z) - diskScore s (circlePoint w) := by
  let f (n : ℕ) := seriesWeight n *
    (diskCoeff n t (circlePoint z) - diskCoeff n s (circlePoint w))
  have hsum : HasSum f ((diskScore t (circlePoint z) - diskScore s (circlePoint w)) * Real.log 2) := by
    convert (disk_series ht (circle_point_disk hz)).sub
      (disk_series hs (circle_point_disk hw)) using 1
    · funext n
      unfold f
      ring
    · ring
  have hnonneg (n : ℕ) : 0 ≤ f n :=
    mul_nonneg (series_weight_pos n).le (sub_nonneg.mpr (hc n))
  have hfirst : f 0 ≤ ∑' n, f n := hsum.summable.le_tsum 0 (fun n _ => hnonneg n)
  rw [hsum.tsum_eq] at hfirst
  have heq : f 0 = (t * (1 - t) - s * (1 - s)) / 2 := by
    unfold f
    rw [first_circle_coeff ht hz, first_circle_coeff hs hw]
    norm_num [seriesWeight]
    ring
  rw [heq] at hfirst
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  apply (div_le_iff₀ (show 0 < 2 * Real.log 2 by positivity)).mpr
  linarith only [hfirst]

private theorem circle_clamping {s w : ℝ} (hs : s ∈ Set.Icc 0 (1 / 2 : ℝ)) (hw : w ∈ Set.Icc 0 1) :
    ∃ w' ∈ Set.Icc s (1 / 2 : ℝ),
      ∀ n, diskCoeff n s (circlePoint w) ≤ diskCoeff n s (circlePoint w') := by
  have hmono : ∃ q ∈ Set.Icc (0 : ℝ) (1/2), ∀ n,
      diskCoeff n s (circlePoint w) ≤ diskCoeff n s (circlePoint q) := by
    by_cases hw' : w ≤ 1/2
    · exact ⟨w, ⟨hw.1, hw'⟩, fun _ => le_rfl⟩
    · refine ⟨1-w, ⟨by linarith [hw.2], by linarith⟩, fun n => ?_⟩
      exact circle_reflection n hs ⟨(lt_of_not_ge hw').le, hw.2⟩
  obtain ⟨q, hq, hmono⟩ := hmono
  by_cases hq' : s ≤ q
  · exact ⟨q, ⟨hq', hq.2⟩, hmono⟩
  · refine ⟨s, ⟨le_rfl, hs.2⟩, fun n => (hmono n).trans ?_⟩
    exact lower_circle_mono n hs ⟨hq.1, (lt_of_not_ge hq').le⟩ ⟨hs.1, le_rfl⟩
      (lt_of_not_ge hq').le

private theorem maximizing_circle {t : ℝ}
    (ht : t ∈ Set.Icc 0 (1 / 2 : ℝ)) :
    ∃ w ∈ Set.Icc (sOfT t) (1 / 2 : ℝ), diskScore (sOfT t) (circlePoint w) = psi t := by
  obtain ⟨d, hd, _, _, hmax, hupper, _⟩ := native_maximum ht
  have hs := (parameter_calibration ht).1
  obtain ⟨w, hw, hmono⟩ := circle_dominates_disk (half_in_unit hs) hd
  obtain ⟨w', hw', hmono'⟩ := circle_clamping hs hw
  have hw'0 : w' ∈ Set.Icc 0 1 := ⟨hs.1.trans hw'.1, hw'.2.trans (by norm_num)⟩
  have hd' := circle_point_disk hw'0
  refine ⟨w', hw', le_antisymm (hupper _ hd') ?_⟩
  rw [← hmax]
  exact disk_score_le_of_coeff_le (half_in_unit hs) (half_in_unit hs) hd hd'
    (fun n => (hmono n).trans (hmono' n))

theorem quantitative_increase {t t' : ℝ} (ht : 0 ≤ t) (htt' : t < t') (ht' : t' ≤ 1 / 2) :
    (t' ^ 2 - t ^ 2) / (2 * Real.log 2) ≤ psi t' - psi t := by
  have htI : t ∈ Set.Icc 0 (1 / 2 : ℝ) := ⟨ht, htt'.le.trans ht'⟩
  have htI' : t' ∈ Set.Icc 0 (1 / 2 : ℝ) := ⟨ht.trans htt'.le, ht'⟩
  obtain ⟨hs, he⟩ := parameter_calibration htI
  obtain ⟨hs', he'⟩ := parameter_calibration htI'
  have hst : sOfT t ≤ sOfT t' := by
    by_contra! h
    have hh := first_coefficient_strict h hs.2
    rw [he, he'] at hh
    exact (not_lt_of_ge (pow_le_pow_left₀ ht htt'.le 2)) hh
  obtain ⟨w, hw, hwmax⟩ := maximizing_circle htI
  obtain ⟨w', hw', hmono⟩ := restricted_transport hs hs' hst hw
  have hw0 : w ∈ Set.Icc 0 1 := ⟨hs.1.trans hw.1, hw.2.trans (by norm_num)⟩
  have hw0' : w' ∈ Set.Icc 0 1 := ⟨hs'.1.trans hw'.1, hw'.2.trans (by norm_num)⟩
  have hinc := circle_score_increment (half_in_unit hs) (half_in_unit hs') hw0 hw0' hmono
  rw [he, he', hwmax] at hinc
  obtain ⟨_, _, _, _, _, hupper, _⟩ := native_maximum htI'
  exact hinc.trans (sub_le_sub_right (hupper _ (circle_point_disk hw0')) _)

theorem result : StrictMonoOn psi (Set.Icc (0 : ℝ) (1 / 2)) := by
  intro t ht t' ht' htt'
  have hpos : 0 < (t' ^ 2 - t ^ 2) / (2 * Real.log 2) :=
    div_pos (sub_pos.mpr (pow_lt_pow_left₀ htt' ht.1 (by decide))) (by positivity)
  exact sub_pos.mp (hpos.trans_le (quantitative_increase ht.1 htt' ht'.2))

end D5.S3.Quantum.Measurement.OrderScores.QubitJensenShannonMonotonicity
