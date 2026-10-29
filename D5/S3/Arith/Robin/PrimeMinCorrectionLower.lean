/- GID: D5/S3/Arith/Robin/PrimeMinCorrectionLower
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/PrimeMinCorrectionLower
   mirror-E: none(waiver:analytic-inequality)
   anchors: []
   utility: none
   digest: Finite geometric prime shells give a uniform lower Robin correction. -/

import D5.S3.Arith.Robin.OriginalEndpointPrimeTail
import D5.S3.Arith.Robin.EulerLayerRootCorrection
import Mathlib.Algebra.Field.GeomSum

/-! Uniform lower correction from a head and finitely many geometric prime shells. -/

namespace D5.S3.Arith.Robin.PrimeMinCorrectionLower

open Finset Filter
open scoped Topology Chebyshev
open EulerLayerRootCorrection OriginalEndpointPrimeTail
open D5.S3.Weil.GronwallLowerEnvelope

noncomputable section

private theorem prime_min_nonneg {X : ℝ} (hX : 1 < X) {p : ℕ} (hp : p.Prime) :
    0 ≤ min (Real.log p / (X * Real.log X))
      (-Real.log (1 - (p : ℝ)⁻¹ ^ 2)) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hi : (p : ℝ)⁻¹ < 1 := (inv_lt_one₀ hp0).mpr hp1
  have hi2 : (p : ℝ)⁻¹ ^ 2 < 1 :=
    pow_lt_one₀ (inv_pos.mpr hp0).le hi (by norm_num)
  apply le_min
  · exact div_nonneg (Real.log_natCast_nonneg p)
      (mul_pos (by linarith) (Real.log_pos hX)).le
  · have h := Real.log_le_sub_one_of_pos (sub_pos.mpr hi2)
    nlinarith [sq_nonneg ((p : ℝ)⁻¹)]

private theorem prime_weight_lower {X U D : ℝ} (hX : 1 < X)
    (hD : 0 < D) (hXD : X * Real.log X ≤ D)
    (hUD : U ^ 2 * Real.log U ≤ D) {p : ℕ} (hp : p.Prime)
    (hpU : (p : ℝ) ≤ U) :
    Real.log p / D ≤ min (Real.log p / (X * Real.log X))
      (-Real.log (1 - (p : ℝ)⁻¹ ^ 2)) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hlogp : 0 < Real.log (p : ℝ) := Real.log_pos hp1
  have hU0 : 0 < U := hp0.trans_le hpU
  have hUlog : Real.log (p : ℝ) ≤ Real.log U := Real.log_le_log hp0 hpU
  have hpp : (p : ℝ) ^ 2 * Real.log p ≤ D :=
    (mul_le_mul (sq_le_sq₀ hp0.le hU0.le |>.mpr hpU) hUlog
      hlogp.le (sq_nonneg U)).trans hUD
  have hi : (p : ℝ)⁻¹ < 1 := (inv_lt_one₀ hp0).mpr hp1
  have hi2 : (p : ℝ)⁻¹ ^ 2 < 1 :=
    pow_lt_one₀ (inv_pos.mpr hp0).le hi (by norm_num)
  have htangent : (p : ℝ)⁻¹ ^ 2 ≤ -Real.log (1 - (p : ℝ)⁻¹ ^ 2) := by
    have h := Real.log_le_sub_one_of_pos (sub_pos.mpr hi2)
    linarith
  apply le_min
  · exact div_le_div_of_nonneg_left hlogp.le
      (mul_pos (by linarith) (Real.log_pos hX)) hXD
  · apply le_trans _ htangent
    apply (div_le_iff₀ hD).mpr
    have h := mul_le_mul_of_nonneg_left hpp (sq_nonneg ((p : ℝ)⁻¹))
    have hid : (p : ℝ)⁻¹ ^ 2 * ((p : ℝ) ^ 2 * Real.log p) = Real.log p := by
      field_simp
    rw [hid] at h
    nlinarith only [h]

private theorem shell_scale {d e : ℝ} (hd : 0 < d) (he : 0 < e) :
    Tendsto (fun X : ℝ =>
      ((θ (d * Real.sqrt X) - θ (e * Real.sqrt X)) /
        ((d * Real.sqrt X) ^ 2 * Real.log (d * Real.sqrt X))) *
        (Real.sqrt X * Real.log X)) atTop (𝓝 (2 * (d - e) / d ^ 2)) := by
  have h := ((theta_sqrt_scale hd).sub (theta_sqrt_scale he)).div
    ((log_sqrt_scale hd).const_mul (d ^ 2)) (by positivity : d ^ 2 * (1 / 2 : ℝ) ≠ 0)
  convert h.congr' ?_ using 1
  · congr 1
    field_simp
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with X hX
    have hs : 0 < Real.sqrt X := Real.sqrt_pos.mpr (by linarith)
    have hl : 0 < Real.log X := Real.log_pos hX
    dsimp
    rw [mul_pow, Real.sq_sqrt (by linarith : 0 ≤ X)]
    field_simp
    rw [Real.sq_sqrt (by linarith : 0 ≤ X)]
    ring


private def shellLower (a b r : ℝ) (N : ℕ) (X : ℝ) : ℝ :=
  θ (a * Real.sqrt X) / (X * Real.log X) +
    ∑ k ∈ range N,
      (θ (b * r ^ (k + 1) * Real.sqrt X) - θ (b * r ^ k * Real.sqrt X)) /
        ((b * r ^ (k + 1) * Real.sqrt X) ^ 2 *
          Real.log (b * r ^ (k + 1) * Real.sqrt X))

private theorem finite_shell_lower {a b r X : ℝ} {N P : ℕ}
    (hX : 1 < X) (ha : 0 < a) (hab : a ≤ b) (hr : 1 ≤ r)
    (hhead : (a * Real.sqrt X) ^ 2 * Real.log (a * Real.sqrt X) ≤ X * Real.log X)
    (hshell : ∀ k < N, X * Real.log X ≤
      (b * r ^ (k + 1) * Real.sqrt X) ^ 2 *
        Real.log (b * r ^ (k + 1) * Real.sqrt X))
    (hcut : b * r ^ N * Real.sqrt X ≤ P) :
    shellLower a b r N X ≤ ∑ p ∈ Nat.primesLE P,
      min (Real.log p / (X * Real.log X)) (-Real.log (1 - (p : ℝ)⁻¹ ^ 2)) := by
  classical
  let f : ℕ → ℝ := fun p => min (Real.log p / (X * Real.log X))
    (-Real.log (1 - (p : ℝ)⁻¹ ^ 2))
  let Y : ℕ → ℝ := fun k => b * r ^ k * Real.sqrt X
  let S : ℕ → Finset ℕ := fun k => Nat.primesLE ⌊Y k⌋₊
  have hb : 0 < b := ha.trans_le hab
  have hD : 0 < X * Real.log X := mul_pos (by linarith) (Real.log_pos hX)
  have hYmono : Monotone Y := by
    intro i j hij
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hr hij) hb.le) (Real.sqrt_nonneg X)
  have hSmono : Monotone S := fun i j hij =>
    Nat.primesLE_mono (Nat.floor_mono (hYmono hij))
  have hbase : θ (a * Real.sqrt X) / (X * Real.log X) ≤ ∑ p ∈ S 0, f p := by
    have hterm : θ (a * Real.sqrt X) / (X * Real.log X) ≤
        ∑ p ∈ Nat.primesLE ⌊a * Real.sqrt X⌋₊, f p := by
      rw [Chebyshev.theta_eq_sum_primesLE, Finset.sum_div]
      apply sum_le_sum
      intro p hp
      have hpp := (Nat.mem_primesLE.mp hp).2
      have hpA : (p : ℝ) ≤ a * Real.sqrt X :=
        (Nat.cast_le.mpr (Nat.mem_primesLE.mp hp).1).trans
          (Nat.floor_le (by positivity))
      exact prime_weight_lower hX hD le_rfl hhead hpp hpA
    apply hterm.trans
    apply sum_le_sum_of_subset_of_nonneg
    · apply Nat.primesLE_mono
      apply Nat.floor_mono
      simpa [Y] using mul_le_mul_of_nonneg_right hab (Real.sqrt_nonneg X)
    · intro p hp _
      exact prime_min_nonneg hX (Nat.mem_primesLE.mp hp).2
  have hstep (k : ℕ) (hk : k < N) :
      (θ (Y (k + 1)) - θ (Y k)) /
          (Y (k + 1) ^ 2 * Real.log (Y (k + 1))) ≤
        ∑ p ∈ S (k + 1) \ S k, f p := by
    have hden := hshell k hk
    change X * Real.log X ≤ Y (k + 1) ^ 2 * Real.log (Y (k + 1)) at hden
    have hpos := hD.trans_le hden
    have htheta : θ (Y (k + 1)) - θ (Y k) =
        ∑ p ∈ S (k + 1) \ S k, Real.log p := by
      rw [Chebyshev.theta_eq_sum_primesLE, Chebyshev.theta_eq_sum_primesLE]
      exact (sum_sdiff_eq_sub (f := fun p : ℕ => Real.log p) (hSmono (Nat.le_succ k))).symm
    rw [htheta, Finset.sum_div]
    apply sum_le_sum
    intro p hp
    have hpmem := (mem_sdiff.mp hp).1
    have hpp := (Nat.mem_primesLE.mp hpmem).2
    have hpY : (p : ℝ) ≤ Y (k + 1) :=
      (Nat.cast_le.mpr (Nat.mem_primesLE.mp hpmem).1).trans
        (Nat.floor_le (by dsimp [Y]; positivity))
    exact prime_weight_lower hX hpos hden le_rfl hpp hpY
  have hpartial : ∀ n ≤ N, shellLower a b r n X ≤ ∑ p ∈ S n, f p := by
    intro n
    induction n with
    | zero => simpa [shellLower] using fun _ : 0 ≤ N => hbase
    | succ n ih =>
      intro hn
      have hprev := ih (by omega)
      have hnext := hstep n (by omega)
      have hadd := add_le_add hprev hnext
      have heq : (∑ p ∈ S n, f p) + (∑ p ∈ S (n + 1) \ S n, f p) =
          ∑ p ∈ S (n + 1), f p := by
        rw [add_comm]
        exact sum_sdiff (hSmono (Nat.le_succ n))
      rw [heq] at hadd
      simpa [shellLower, sum_range_succ, Y, add_assoc] using hadd
  apply (hpartial N le_rfl).trans
  apply sum_le_sum_of_subset_of_nonneg
  · exact Nat.primesLE_mono ((Nat.floor_le_floor hcut).trans_eq (Nat.floor_natCast P))
  · intro p hp _
    exact prime_min_nonneg hX (Nat.mem_primesLE.mp hp).2

private theorem shell_lower_scale {a b r : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hr : 0 < r) (N : ℕ) :
    Tendsto (fun X : ℝ => shellLower a b r N X * (Real.sqrt X * Real.log X))
      atTop (𝓝 (a + ∑ k ∈ range N,
        2 * (b * r ^ (k + 1) - b * r ^ k) / (b * r ^ (k + 1)) ^ 2)) := by
  have hhead : Tendsto (fun X : ℝ =>
      θ (a * Real.sqrt X) / (X * Real.log X) * (Real.sqrt X * Real.log X))
      atTop (𝓝 a) := by
    apply (theta_sqrt_scale ha).congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with X hX
    have hs := Real.sq_sqrt (show 0 ≤ X by linarith)
    have hs0 : Real.sqrt X ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by linarith))
    field_simp [ne_of_gt (Real.log_pos hX), ne_of_gt (show 0 < X by linarith), hs0]
    rw [hs]
    ring
  have hsum := tendsto_finsetSum (range N) (fun k _ =>
    shell_scale (mul_pos hb (pow_pos hr (k + 1))) (mul_pos hb (pow_pos hr k)))
  convert hhead.add hsum using 1
  ext X
  simp only [shellLower, add_mul, sum_mul, mul_assoc]


private theorem cutoff_denominator_scale {d : ℝ} (hd : 0 < d) :
    Tendsto (fun X : ℝ =>
      (d * Real.sqrt X) ^ 2 * Real.log (d * Real.sqrt X) / (X * Real.log X))
      atTop (𝓝 (d ^ 2 / 2)) := by
  convert ((log_sqrt_scale hd).const_mul (d ^ 2)).congr' ?_ using 1
  · congr 1
    ring
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with X hX
    rw [mul_pow, Real.sq_sqrt (by linarith : 0 ≤ X)]
    field_simp

private theorem shell_parameters {ε : ℝ} (hε : 0 < ε) :
    ∃ a b r : ℝ, ∃ N : ℕ,
      0 < a ∧ a ^ 2 < 2 ∧ a ≤ b ∧ 0 < b ∧ 2 < b ^ 2 ∧ 1 < r ∧ 1 ≤ N ∧
      2 * Real.sqrt 2 - ε < a + ∑ k ∈ range N,
        2 * (b * r ^ (k + 1) - b * r ^ k) / (b * r ^ (k + 1)) ^ 2 := by
  let e := min ε 1
  let s := Real.sqrt 2
  let a := s - e / 4
  let r := 1 + e / (16 * s)
  let b := s * r
  have he : 0 < e := lt_min hε (by norm_num)
  have he1 : e ≤ 1 := min_le_right _ _
  have heε : e ≤ ε := min_le_left _ _
  have hs : 0 < s := Real.sqrt_pos.mpr (by norm_num)
  have hs2 : s ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs1 : 1 ≤ s := by nlinarith
  have hr : 1 < r := by
    have hpos : 0 < e / (16 * s) := by positivity
    dsimp [r]
    linarith only [hpos]
  have hr0 : 0 < r := by linarith
  have ha : 0 < a := by dsimp [a]; linarith
  have has : a < s := by dsimp [a]; linarith
  have hsb : s < b := by dsimp [b]; nlinarith
  have hb : 0 < b := hs.trans hsb
  have hi0 : 0 ≤ r⁻¹ := (inv_pos.mpr hr0).le
  have hi1 : r⁻¹ < 1 := (inv_lt_one₀ hr0).mpr hr
  have hediv : 0 < e / (8 * s) := by positivity
  obtain ⟨n, hn⟩ := eventually_atTop.mp
    ((tendsto_pow_atTop_nhds_zero_of_lt_one hi0 hi1).eventually_lt_const hediv)
  let N := max n 1
  have hN : 1 ≤ N := le_max_right _ _
  have htail : (r⁻¹) ^ N < e / (8 * s) := hn N (le_max_left _ _)
  have hgeom := geom_sum_mul_neg (r⁻¹) N
  have hsum : (∑ k ∈ range N,
      2 * (b * r ^ (k + 1) - b * r ^ k) / (b * r ^ (k + 1)) ^ 2) =
      2 / (r * b) * (1 - (r⁻¹) ^ N) := by
    have hterm (k : ℕ) :
        2 * (b * r ^ (k + 1) - b * r ^ k) / (b * r ^ (k + 1)) ^ 2 =
        (2 / (r * b) * (1 - r⁻¹)) * (r⁻¹) ^ k := by
      rw [pow_succ, inv_pow]
      field_simp
    simp_rw [hterm]
    rw [← mul_sum]
    calc
      _ = (2 / (r * b)) * ((∑ k ∈ range N, (r⁻¹) ^ k) * (1 - r⁻¹)) := by ring
      _ = _ := by rw [hgeom]
  have hcoeff : 2 / (r * b) = s / r ^ 2 := by
    dsimp [b]
    apply (div_eq_div_iff (by positivity) (by positivity)).mpr
    nlinarith [hs2]
  have hrloss : 2 * s * (r - 1) = e / 8 := by
    dsimp [r]
    field_simp
    ring
  have hcube : 1 ≤ r ^ 2 * (2 * r - 3) + 2 := by
    have hnon : 0 ≤ (r - 1) ^ 2 * (2 * r + 1) := by positivity
    nlinarith only [hnon]
  have hrlower : 3 - 2 * r ≤ 1 / r ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hr0)).mpr
    nlinarith only [hcube]
  have hcoefflower : s - e / 8 ≤ s / r ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hrlower hs.le
    rw [mul_one_div] at h
    nlinarith only [h, hrloss]
  have hcoeffupper : s / r ^ 2 ≤ s := by
    apply (div_le_iff₀ (sq_pos_of_pos hr0)).mpr
    nlinarith [sq_nonneg (r - 1)]
  have htailloss : s / r ^ 2 * (r⁻¹) ^ N < e / 8 := by
    have hsmall : s * (r⁻¹) ^ N < e / 8 := by
      have h := (lt_div_iff₀ (by positivity : 0 < 8 * s)).mp htail
      nlinarith only [h]
    exact (mul_le_mul_of_nonneg_right hcoeffupper (pow_nonneg hi0 N)).trans_lt hsmall
  refine ⟨a, b, r, N, ha, ?_, ?_, hb, ?_, hr, hN, ?_⟩
  · nlinarith
  · exact has.le.trans hsb.le
  · nlinarith
  · rw [hsum, hcoeff]
    dsimp [a, s] at *
    nlinarith only [hcoefflower, htailloss, heε, he]

private theorem uniform_prime_min {ε c : ℝ} (hε : 0 < ε) (hc : 0 < c) :
    ∃ A : ℝ, 1 < A ∧ ∀ X : ℝ, A ≤ X → ∀ P : ℕ, c * X ≤ P →
      (2 * Real.sqrt 2 - ε) / (Real.sqrt X * Real.log X) <
        ∑ p ∈ Nat.primesLE P, min (Real.log p / (X * Real.log X))
          (-Real.log (1 - (p : ℝ)⁻¹ ^ 2)) := by
  obtain ⟨a, b, r, N, ha, ha2, hab, hb, hb2, hr, hN, hF⟩ := shell_parameters hε
  have hhead := (cutoff_denominator_scale ha).eventually_lt_const
    (show a ^ 2 / 2 < 1 by linarith)
  have hshell : ∀ᶠ X : ℝ in atTop, ∀ k ∈ range N,
      X * Real.log X ≤ (b * r ^ (k + 1) * Real.sqrt X) ^ 2 *
        Real.log (b * r ^ (k + 1) * Real.sqrt X) := by
    apply (eventually_all_finset (range N)).mpr
    intro k hk
    have hd : 0 < b * r ^ (k + 1) := mul_pos hb (pow_pos (by linarith) _)
    have hbd : b ≤ b * r ^ (k + 1) := by
      exact le_mul_of_one_le_right hb.le (one_le_pow₀ hr.le)
    have hd2 : 2 < (b * r ^ (k + 1)) ^ 2 :=
      hb2.trans_le (sq_le_sq₀ hb.le hd.le |>.mpr hbd)
    have h := (cutoff_denominator_scale hd).eventually_const_lt
      (show 1 < (b * r ^ (k + 1)) ^ 2 / 2 by linarith)
    filter_upwards [h, eventually_gt_atTop (1 : ℝ)] with X h hX
    simpa only [one_mul] using
      ((lt_div_iff₀ (mul_pos (by linarith) (Real.log_pos hX))).mp h).le
  have hcut : ∀ᶠ X : ℝ in atTop, b * r ^ N * Real.sqrt X ≤ c * X := by
    have h := Real.tendsto_sqrt_atTop.eventually (eventually_ge_atTop (b * r ^ N / c))
    filter_upwards [h, eventually_gt_atTop (0 : ℝ)] with X h hX
    have h' : b * r ^ N ≤ c * Real.sqrt X := by simpa only [mul_comm] using (div_le_iff₀ hc).mp h
    have h'' := mul_le_mul_of_nonneg_right h' (Real.sqrt_nonneg X)
    convert h'' using 1
    rw [mul_assoc, ← pow_two, Real.sq_sqrt hX.le]
  have hlimit := (shell_lower_scale ha hb (by linarith : 0 < r) N).eventually_const_lt hF
  obtain ⟨T, hT⟩ := eventually_atTop.mp
    (hhead.and (hshell.and (hcut.and hlimit)))
  refine ⟨max T 2, lt_of_lt_of_le (by norm_num) (le_max_right _ _), ?_⟩
  intro X hX P hP
  have hX2 : 2 ≤ X := (le_max_right T 2).trans hX
  have hX1 : 1 < X := by linarith
  have h := hT X ((le_max_left T 2).trans hX)
  have hD : 0 < X * Real.log X := mul_pos (by linarith) (Real.log_pos hX1)
  have hhead' := (div_lt_one hD).mp h.1
  have hfinite := finite_shell_lower hX1 ha hab hr.le hhead'.le
    (fun k hk => h.2.1 k (mem_range.mpr hk)) (h.2.2.1.trans hP)
  have hnorm : (2 * Real.sqrt 2 - ε) / (Real.sqrt X * Real.log X) <
      shellLower a b r N X := by
    exact (div_lt_iff₀ (mul_pos (Real.sqrt_pos.mpr (by linarith))
      (Real.log_pos hX1))).mpr h.2.2.2
  exact hnorm.trans_le hfinite

/-- One threshold, chosen before the integer, gives both the full lower
correction and its same-integer original Robin-margin consequence. -/
private theorem conditional_min_tail_robin_lower {ε c : ℝ} (hε : 0 < ε) (hc : 0 < c) :
    ∃ A : ℝ, 1 < A ∧ ∀ m : ℕ, 0 < m →
      m.primeFactors = Nat.primesLE (largestPrime m) →
      1 < θ (largestPrime m) → A ≤ Real.log (m : ℝ) →
      c * Real.log (m : ℝ) ≤ largestPrime m →
      (2 * Real.sqrt 2 - ε) /
          (Real.sqrt (Real.log (m : ℝ)) * Real.log (Real.log (m : ℝ))) <
        tail m + Real.log (Real.log (Real.log (m : ℝ))) -
          Real.log (Real.log (θ (largestPrime m))) ∧
      (2 * Real.sqrt 2 - ε) /
          (Real.sqrt (Real.log (m : ℝ)) * Real.log (Real.log (m : ℝ))) +
          Mertens.E₃ (largestPrime m) + Real.log (Real.log (θ (largestPrime m))) -
          Real.log (Real.log (largestPrime m)) < robinLogMargin m := by
  obtain ⟨A, hA, hbound⟩ := uniform_prime_min hε hc
  refine ⟨A, hA, ?_⟩
  intro m hm hsupport htheta hAm hcP
  have h := hbound (Real.log (m : ℝ)) hAm (largestPrime m) hcP
  rw [← hsupport] at h
  have hfinite := finite_min_tail_robin_bound hm hsupport htheta
  exact ⟨h.trans_le hfinite.1, by linarith [hfinite.2]⟩

/-- One threshold before every original integer gives the full lower correction
and its same-integer Robin consequence, without a prime-ratio premise. -/
theorem uniform_min_tail_robin_lower {ε : ℝ} (hε : 0 < ε) :
    ∃ A : ℝ, 1 < A ∧ ∀ m : ℕ, 0 < m →
      m.primeFactors = Nat.primesLE (largestPrime m) →
      1 < θ (largestPrime m) → A ≤ Real.log (m : ℝ) →
      (2 * Real.sqrt 2 - ε) /
          (Real.sqrt (Real.log (m : ℝ)) * Real.log (Real.log (m : ℝ))) <
        tail m + Real.log (Real.log (Real.log (m : ℝ))) -
          Real.log (Real.log (θ (largestPrime m))) ∧
      (2 * Real.sqrt 2 - ε) /
          (Real.sqrt (Real.log (m : ℝ)) * Real.log (Real.log (m : ℝ))) +
          Mertens.E₃ (largestPrime m) + Real.log (Real.log (θ (largestPrime m))) -
          Real.log (Real.log (largestPrime m)) < robinLogMargin m := by
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  let c : ℝ := 1 / (2 * Real.log 4)
  have hc : 0 < c := by dsimp [c]; positivity
  obtain ⟨A₀, hA₀, hconditional⟩ := conditional_min_tail_robin_lower hε hc
  refine ⟨max A₀ 64, hA₀.trans_le (le_max_left _ _), ?_⟩
  intro m hm hsupport htheta hAm
  let X : ℝ := Real.log (m : ℝ)
  let Y : ℝ := θ (largestPrime m)
  have hX64 : 64 ≤ X := (le_max_right A₀ 64).trans hAm
  have hX : 1 < X := by linarith
  have hX0 : 0 < X := by linarith
  have hlogX : 0 < Real.log X := Real.log_pos hX
  by_cases hhalf : X / 2 ≤ Y
  · have hcheb := Chebyshev.theta_le_log4_mul_x
      (x := (largestPrime m : ℝ)) (Nat.cast_nonneg _)
    have hratio : c * X ≤ (largestPrime m : ℝ) := by
      dsimp [c]
      rw [one_div_mul_eq_div]
      apply (div_le_iff₀ (by positivity : 0 < 2 * Real.log 4)).mpr
      dsimp [Y] at hhalf
      nlinarith only [hhalf, hcheb]
    exact hconditional m hm hsupport htheta ((le_max_left A₀ 64).trans hAm) hratio
  · have hgap : Y < X / 2 := lt_of_not_ge hhalf
    have ht := D5.S3.Arith.Robin.RestrictedDivisorStrictInventory.loglog_tangent
      (x := X) (y := Y) hX htheta (by linarith)
    have ht' : Real.log (Real.log Y) - Real.log (Real.log X) <
        (Y - X) / (X * Real.log X) := by
      simpa [D5.S3.Arith.Robin.ActualRobinClockCovariance.g, div_eq_mul_inv] using ht
    have hclock : 1 / (2 * Real.log X) <
        Real.log (Real.log X) - Real.log (Real.log Y) := by
      have hcharge : 1 / (2 * Real.log X) < (X - Y) / (X * Real.log X) := by
        apply (div_lt_div_iff₀ (by positivity : 0 < 2 * Real.log X)
          (mul_pos hX0 hlogX)).mpr
        nlinarith only [mul_pos (by linarith : 0 < X / 2 - Y) hlogX]
      have hflip : (X - Y) / (X * Real.log X) <
          Real.log (Real.log X) - Real.log (Real.log Y) := by
        rw [sub_div] at ht' ⊢
        linarith only [ht']
      exact hcharge.trans hflip
    have hsX : 8 ≤ Real.sqrt X := by
      have h := Real.sqrt_le_sqrt hX64
      norm_num at h ⊢
      exact h
    have hs2 : Real.sqrt 2 < 2 := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
    have hsmall : (2 * Real.sqrt 2 - ε) / (Real.sqrt X * Real.log X) <
        1 / (2 * Real.log X) := by
      apply (div_lt_div_iff₀ (mul_pos (Real.sqrt_pos.mpr hX0) hlogX)
        (by positivity : 0 < 2 * Real.log X)).mpr
      have hcoeff : 2 * (2 * Real.sqrt 2 - ε) < Real.sqrt X := by linarith
      nlinarith only [mul_pos (sub_pos.mpr hcoeff) hlogX]
    obtain ⟨htail, hmargin⟩ := tail_robin_data hm hsupport
    have hlower : (2 * Real.sqrt 2 - ε) / (Real.sqrt X * Real.log X) <
        tail m + Real.log (Real.log X) - Real.log (Real.log Y) := by
      linarith [hsmall.trans hclock]
    refine ⟨hlower, ?_⟩
    dsimp [X, Y] at hlower
    linarith only [hlower, hmargin]

end

end D5.S3.Arith.Robin.PrimeMinCorrectionLower
