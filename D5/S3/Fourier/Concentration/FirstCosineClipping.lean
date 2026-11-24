/- GID: D5/S3/Fourier/Concentration/FirstCosineClipping
   generality: G
   mirror-B: D5/B/S3/Fourier/Concentration/FirstCosineClipping
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact first clipping threshold for two real cosine moments. -/

import D5.S3.Fourier.Concentration.AggregateCosineBalance
import Mathlib.NumberTheory.Niven
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Algebra.Order.Round

/-! The first support change in minimum squared mass under two real cosine bounds. -/

open Finset AddChar

namespace D5.S3.Fourier.Concentration.FirstCosineClipping

open AggregateCosineBalance

private theorem sum_e {q : ℕ} [NeZero q] (hq : 5 ≤ q) (m : ℤ)
    (hm : m ≠ 0) (hlo : -4 ≤ m) (hhi : m ≤ 4) :
    (∑ k : ZMod q, e k m) = 0 := by
  have hmod : (m : ZMod q) ≠ 0 := by
    intro h
    exact hm (Int.eq_zero_of_dvd_of_natAbs_lt_natAbs
      ((ZMod.intCast_zmod_eq_zero_iff_dvd m q).mp h) (by omega))
  exact sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar q hmod)


private theorem sum_mode_zero {q : ℕ} [NeZero q] (hq : 5 ≤ q) (m : ℤ)
    (hm : 0 < m) (hu : m ≤ 4) : (∑ k : ZMod q, mode k m) = 0 := by
  have h : (∑ k : ZMod q, (e k m + e k (-m))) = 0 := by
    rw [sum_add_distrib, sum_e hq m (by omega) (by omega) hu,
      sum_e hq (-m) (by omega) (by omega) (by omega), add_zero]
  simp only [e_pair, ← mul_sum, ← Complex.ofReal_sum, mul_eq_zero, OfNat.ofNat_ne_zero,
    false_or, Complex.ofReal_eq_zero] at h
  exact h

private theorem mode_prod {q : ℕ} [NeZero q] (k : ZMod q) (m n : ℤ) :
    2 * (mode k m * mode k n) = mode k (m + n) + mode k (m - n) := by
  let θ (j : ℤ) := 2 * Real.pi * (j : ℝ) * (k.val : ℝ) / (q : ℝ)
  have h_add : θ (m + n) = θ m + θ n := by dsimp [θ]; push_cast; ring
  have h_sub : θ (m - n) = θ m - θ n := by dsimp [θ]; push_cast; ring
  change 2 * (Real.cos (θ m) * Real.cos (θ n)) =
    Real.cos (θ (m + n)) + Real.cos (θ (m - n))
  rw [h_add, h_sub, ← mul_assoc, Real.two_mul_cos_mul_cos, add_comm]

private theorem two_modes_orthogonal {q : ℕ} [NeZero q] (hq : 5 ≤ q) :
    (∑ k : ZMod q, mode k 1) = 0 ∧ (∑ k : ZMod q, mode k 2) = 0 ∧
    (∑ k : ZMod q, mode k 1 * mode k 2) = 0 ∧
    (∑ k : ZMod q, mode k 1 ^ 2) = (q : ℝ)/2 ∧
    (∑ k : ZMod q, mode k 2 ^ 2) = (q : ℝ)/2 := by
  have h1 := sum_mode_zero hq (1 : ℤ) (by decide) (by decide)
  have h2 := sum_mode_zero hq (2 : ℤ) (by decide) (by decide)
  have h3 := sum_mode_zero hq (3 : ℤ) (by decide) (by decide)
  have h4 := sum_mode_zero hq (4 : ℤ) (by decide) (by decide)
  have h0 : (∑ k : ZMod q, mode k 0) = (q : ℝ) := by simp [mode]
  have hn (k : ZMod q) : mode k (-1) = mode k 1 := by
    simp [mode, neg_div]
  have hp (m n : ℤ) : 2 * (∑ k : ZMod q, mode k m * mode k n) =
      (∑ k : ZMod q, mode k (m + n)) + ∑ k : ZMod q, mode k (m - n) := by
    rw [mul_sum, ← sum_add_distrib]
    exact sum_congr rfl (fun k _ => mode_prod k m n)
  have h12 := hp 1 2
  have h11 := hp 1 1
  have h22 := hp 2 2
  norm_num [hn, h1, h2, h3, h4, h0] at h12 h11 h22
  refine ⟨h1, h2, by linarith, ?_, ?_⟩
  · simp only [pow_two]
    linarith
  · simp only [pow_two]
    linarith

private theorem exact_preclipping_remainder {ι : Type*} [Fintype ι] (s w : ι → ℝ) (n a : ℝ) (hn : 0 < n)
    (hws : ∑ k, w k = 1)
    (v : ι → ℝ) (hv : ∀ k, n * v k = 1 + 2 * a * s k)
    (hvs : ∑ k, v k = 1) (hva : ∑ k, v k * s k = 2 * a) :
    (∑ k, w k ^ 2) - (1 + 4 * a ^ 2) / n =
      (∑ k, (w k - v k) ^ 2) +
        (4 * a / n) * ((∑ k, w k * s k) - 2 * a) := by
  have hm (f : ι → ℝ) : n * (∑ k, f k * v k) = (∑ k, f k) +
      2 * a * ∑ k, f k * s k := by
    simp only [mul_sum, ← sum_add_distrib]
    apply sum_congr rfl
    intro k _
    calc
      n * (f k * v k) = f k * (n * v k) := by ring
      _ = _ := by rw [hv]; ring
  have hwv := hm w
  rw [hws] at hwv
  have hvv := hm v
  rw [hvs, hva] at hvv
  have hid : (∑ k, (w k - v k) ^ 2) = (∑ k, w k ^ 2) -
      2 * (∑ k, w k * v k) + ∑ k, v k * v k := by
    simp only [mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
    apply sum_congr rfl
    intro k _
    ring
  rw [hid]
  apply (mul_right_inj' hn.ne').mp
  field_simp [hn.ne']
  simp only [pow_two]
  linear_combination 2 * hwv - hvv

private theorem affine_cosine_mass {q : ℕ} [NeZero q] (hq : 5 ≤ q) (a : ℝ) :
    let s (k : ZMod q) := mode k 1 + mode k 2
    let b (k : ZMod q) := (1 + 2 * a * s k) / (q : ℝ)
    (∑ k, b k) = 1 ∧
      (∑ k, b k * mode k 1) = a ∧ (∑ k, b k * mode k 2) = a ∧
      ∀ w : ZMod q → ℝ, (∑ k, w k) = 1 →
        (∑ k, w k ^ 2) - (1 + 4 * a ^ 2) / (q : ℝ) =
          (∑ k, (w k - b k) ^ 2) +
            (4 * a / (q : ℝ)) * ((∑ k, w k * s k) - 2 * a) := by
  dsimp only
  let s (k : ZMod q) := mode k 1 + mode k 2
  let b (k : ZMod q) := (1 + 2 * a * s k) / (q : ℝ)
  have hqR : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  obtain ⟨h1, h2, h12, h11, h22⟩ := two_modes_orthogonal hq
  have hsum : (∑ k, b k) = 1 := by
    dsimp [b, s]
    simp only [← sum_div, sum_add_distrib, ← mul_sum, h1, h2, add_zero, mul_zero, Finset.sum_const,
      Finset.card_univ, ZMod.card, nsmul_eq_mul, mul_one]
    exact div_self hqR.ne'
  have hbmult (f : ZMod q → ℝ) :
      (q : ℝ) * (∑ k, b k * f k) = (∑ k, f k) +
        2*a*((∑ k, mode k 1 * f k) + ∑ k, mode k 2 * f k) := by
    simp only [mul_sum, ← sum_add_distrib]
    apply sum_congr rfl
    intro k _
    dsimp [b, s]
    field_simp [hqR.ne']
  have hcomm : (∑ k : ZMod q, mode k 2 * mode k 1) = 0 := by
    simpa only [mul_comm (mode _ 2)] using h12
  have hM1 : (∑ k, b k * mode k 1) = a := by
    apply (mul_right_inj' hqR.ne').mp
    rw [hbmult]
    simp only [h1, hcomm, add_zero, zero_add, ← pow_two, h11]
    ring
  have hM2 : (∑ k, b k * mode k 2) = a := by
    apply (mul_right_inj' hqR.ne').mp
    rw [hbmult]
    simp only [h2, h12, zero_add, ← pow_two, h22]
    ring
  have hm : (∑ k, b k * s k) = 2*a := by
    simp only [s, mul_add, sum_add_distrib, hM1, hM2]
    ring
  refine ⟨hsum, hM1, hM2, ?_⟩
  intro w hw
  exact exact_preclipping_remainder s w q a hqR hw b (fun k => by
    dsimp [b]
    field_simp [hqR.ne']
    ) hsum hm


private theorem mode_ne_quarter {q : ℕ} [NeZero q] (k : ZMod q) : mode k 1 ≠ -(1 / 4 : ℝ) := by
  intro h
  rw [mode, Int.cast_one, mul_one] at h
  have hθ : ∃ r : ℚ, 2 * Real.pi * (k.val : ℝ) / (q : ℝ) = (r : ℝ) * Real.pi := by
    refine ⟨(2 * (k.val : ℚ)) / (q : ℚ), ?_⟩
    push_cast
    ring
  have hcos : ∃ r : ℚ, Real.cos (2 * Real.pi * (k.val : ℝ) / (q : ℝ)) = (r : ℝ) :=
    ⟨-(1 / 4), by simpa using h⟩
  have hn := niven hθ hcos
  rw [h] at hn
  norm_num at hn

private theorem exists_quarter_nearby {q : ℕ} [NeZero q] (hq : 5 ≤ q) :
    ∃ k : ZMod q, |mode k 1 + 1/4| ≤ Real.pi / (q : ℝ) := by
  let θ := Real.arccos (-(1/4 : ℝ))
  let x := (q : ℝ) * θ / (2 * Real.pi)
  have hqR : (5 : ℝ) ≤ q := by exact_mod_cast hq
  have hθ₀ : 0 ≤ θ := Real.arccos_nonneg _
  have hθπ : θ ≤ Real.pi := Real.arccos_le_pi _
  have hx₀ : 0 ≤ x := by dsimp [x]; positivity
  have hxq : x ≤ (q : ℝ) / 2 := by
    dsimp [x]
    apply (div_le_iff₀ (by positivity : 0 < 2 * Real.pi)).2
    nlinarith [mul_le_mul_of_nonneg_left hθπ (show (0 : ℝ) ≤ q by linarith)]
  obtain ⟨hlo, hhi⟩ := abs_le.mp (abs_sub_round x)
  have h₀ : 0 ≤ round x := by
    have h : (-1 : ℝ) < (round x : ℝ) := by linarith
    have h' : (-1 : ℤ) < round x := by exact_mod_cast h
    omega
  let k : ℕ := (round x).toNat
  have hk : (k : ℤ) = round x := Int.toNat_of_nonneg h₀
  have hkR : (k : ℝ) = (round x : ℝ) := by exact_mod_cast hk
  have hkq : k < q := by
    have h : (k : ℝ) < q := by rw [hkR]; linarith
    exact_mod_cast h
  refine ⟨(k : ZMod q), ?_⟩
  have hval : ((k : ZMod q).val : ℝ) = (k : ℝ) := by
    rw [ZMod.val_natCast_of_lt hkq]
  have ha : mode (k : ZMod q) 1 = Real.cos (2 * Real.pi * (k : ℝ) / q) := by
    simp only [mode, hval, Int.cast_one, mul_one]
  have hcos : Real.cos θ = -(1/4 : ℝ) := Real.cos_arccos (by norm_num) (by norm_num)
  have hangle :
      2 * Real.pi * (k : ℝ) / (q : ℝ) - θ =
        (2 * Real.pi / (q : ℝ)) * ((round x : ℝ) - x) := by
    rw [hkR]
    dsimp [x]
    field_simp [Real.pi_ne_zero, show (q : ℝ) ≠ 0 by positivity]
  rw [ha, ← sub_neg_eq_add, ← hcos]
  calc
    _ ≤ |2 * Real.pi * (k : ℝ) / (q : ℝ) - θ| := Real.abs_cos_sub_cos_le _ _
    _ ≤ Real.pi / (q : ℝ) := by
      rw [hangle, abs_mul, abs_of_nonneg (by positivity), abs_sub_comm]
      calc
        _ ≤ (2 * Real.pi / (q : ℝ)) * (1 / 2) :=
          mul_le_mul_of_nonneg_left (abs_sub_round x) (by positivity)
        _ = _ := by ring

private theorem exact_cosine_clipping_threshold {q : ℕ} [NeZero q] (hq : 5 ≤ q) :
    let s (k : ZMod q) := mode k 1 + mode k 2
    ∃ m : ℝ, (∃ k, m = s k) ∧ (∀ k, m ≤ s k) ∧
      4/9 < -1/(2*m) ∧
      -1/(2*m) ≤ 4/9 + (16 * Real.pi ^ 2) / (9 * (q : ℝ)^2) ∧
      (∀ a : ℝ, 0 ≤ a →
        ((∀ k, 0 ≤ (1 + 2*a*s k)/(q : ℝ)) ↔ a ≤ -1/(2*m))) := by
  dsimp only
  let s (k : ZMod q) := mode k 1 + mode k 2
  let values := univ.image s
  have hne : values.Nonempty := ⟨s 0, mem_image_of_mem s (mem_univ _)⟩
  let m := values.min' hne
  obtain ⟨kmin, _, hkmin⟩ := mem_image.mp (min'_mem values hne)
  change s kmin = m at hkmin
  have hmin k : m ≤ s k := min'_le values _ (mem_image_of_mem s (mem_univ k))
  have hsumpos (k : ZMod q) : s k ≤ 2 := by
    have h₁ : mode k 1 ≤ 1 := Real.cos_le_one _
    have h₂ : mode k 2 ≤ 1 := Real.cos_le_one _
    dsimp [s]
    linarith
  have hfactor (k : ZMod q) : s k = 2 * (mode k 1 + 1/4)^2 - 9/8 := by
    dsimp [s]
    rw [mode_double]
    ring
  have hlow : -(9/8 : ℝ) < m := by
    have hp := sq_pos_of_ne_zero (show mode kmin 1 + 1/4 ≠ 0 by
      intro h
      apply mode_ne_quarter kmin
      linarith)
    rw [← hkmin, hfactor]
    linarith
  have hqR : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  obtain ⟨h1, h2, h12, h11, h22⟩ := two_modes_orthogonal hq
  have hs : (∑ k, s k) = 0 := by simp [s, sum_add_distrib, h1, h2]
  have hs2 : (∑ k, s k ^ 2) = (q : ℝ) := by
    simp only [s, add_sq, sum_add_distrib, mul_assoc, ← mul_sum, h11, h12, h22]
    ring
  have hup : m ≤ -(1/2 : ℝ) := by
    have hnn : 0 ≤ ∑ k, (2 - s k) * (s k - m) :=
      sum_nonneg fun k _ => mul_nonneg (sub_nonneg.mpr (hsumpos k)) (sub_nonneg.mpr (hmin k))
    have hr : (∑ k, (2 - s k) * (s k - m)) = (2+m)*(∑ k, s k) - (∑ k, s k^2) -
        (q : ℝ) * (2*m) := by
      have hmconst : ∑ _ : ZMod q, 2*m = (q : ℝ) * (2*m) := by simp [nsmul_eq_mul]
      rw [← hmconst, mul_sum, ← sum_sub_distrib, ← sum_sub_distrib]
      exact sum_congr rfl fun k _ => by ring
    rw [hr, hs, hs2] at hnn
    have hmul : 0 ≤ (q : ℝ) * (-(2 * m) - 1) := by nlinarith
    have hm := nonneg_of_mul_nonneg_right hmul hqR
    linarith
  have hmden : 0 < -(2*m) := by linarith
  refine ⟨m, ⟨kmin, hkmin.symm⟩, hmin, ?_, ?_, ?_⟩
  · rw [neg_div, ← div_neg]
    exact (lt_div_iff₀ hmden).2 (by linarith)
  · obtain ⟨k, hk⟩ := exists_quarter_nearby hq
    have hd : (mode k 1 + 1/4)^2 ≤ (Real.pi/(q : ℝ))^2 := by
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hk 2
    have hm := hmin k
    rw [hfactor k] at hm
    have hgap : m + 9/8 ≤ 2 * (Real.pi/(q : ℝ))^2 := by linarith
    have hn : 0 ≤ (16*Real.pi^2)/(9*(q : ℝ)^2) := by positivity
    rw [neg_div, ← div_neg]
    apply (div_le_iff₀ hmden).2
    have hs' := mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ -(2*m) by linarith) hn
    have hmatch : (16*Real.pi^2)/(9*(q : ℝ)^2) = (16/9)*(Real.pi/(q : ℝ))^2 := by ring
    linarith [congrArg (fun x : ℝ => (8/9) * x) hmatch]
  · intro a ha
    rw [neg_div, ← div_neg, le_div_iff₀ hmden]
    constructor
    · intro hv
      have hk := hv kmin
      change 0 ≤ (1 + 2*a*s kmin)/(q : ℝ) at hk
      rw [hkmin] at hk
      have hk' := mul_nonneg hk hqR.le
      rw [div_mul_cancel₀ _ hqR.ne'] at hk'
      linarith
    · intro ham k
      apply div_nonneg _ hqR.le
      have hs' := mul_le_mul_of_nonneg_left (hmin k) (show 0 ≤ 2*a by positivity)
      linarith

/-- At two common cosine thresholds, the unconstrained affine law gives the exact optimum
until its first negative entry. Every feasible law pays at least the squared mass of the
negative entries as additional cost after this support change. -/
theorem first_cosine_clipping {q : ℕ} [NeZero q] (hq : 5 ≤ q) :
    let c := fun k : ZMod q => mode k 1
    let d := fun k : ZMod q => mode k 2
    let s := fun k => c k + d k
    let square := fun x : ℝ => x ^ 2
    ∃ m : ℝ, (∃ k, m = s k) ∧ (∀ k, m ≤ s k) ∧
      4 / 9 < -1 / (2 * m) ∧
      -1 / (2 * m) ≤ 4 / 9 + 16 * square Real.pi / (9 * square (q : ℝ)) ∧
      ∀ a : ℝ,
        let v := fun k => (1 + 2 * a * s k) / (q : ℝ)
        let lower := (1 + 4 * square a) / (q : ℝ)
        let feasible := fun w : ZMod q → ℝ =>
          (∀ k, 0 ≤ w k) ∧ (∑ k, w k) = 1 ∧
            a ≤ (∑ k, w k * c k) ∧ a ≤ (∑ k, w k * d k)
        (∑ k, v k) = 1 ∧ (∑ k, v k * c k) = a ∧ (∑ k, v k * d k) = a ∧
          (∀ w : ZMod q → ℝ, (∑ k, w k) = 1 →
            (∑ k, square (w k)) - lower =
              (∑ k, square (w k - v k)) +
                (4 * a / (q : ℝ)) * ((∑ k, w k * s k) - 2 * a)) ∧
          (0 ≤ a →
            ((∀ k, 0 ≤ v k) ↔ a ≤ -1 / (2 * m)) ∧
            (-1 / (2 * m) < a → 0 < ∑ k, square (max 0 (-v k))) ∧
            (∀ w, feasible w →
              lower + (∑ k, square (max 0 (-v k))) ≤ (∑ k, square (w k)) ∧
                ((∑ k, square (w k)) = lower ↔ w = v)) ∧
            ((∃ w, feasible w ∧ (∑ k, square (w k)) = lower) ↔ a ≤ -1 / (2 * m))) := by
  dsimp only
  let s (k : ZMod q) := mode k 1 + mode k 2
  obtain ⟨m, hm, hmin, hlo, hhi, hcut⟩ := exact_cosine_clipping_threshold hq
  refine ⟨m, hm, hmin, hlo, hhi, ?_⟩
  intro a
  let v (k : ZMod q) := (1 + 2 * a * s k) / (q : ℝ)
  obtain ⟨hv, h₁, h₂, hgap⟩ := affine_cosine_mass hq a
  change (∑ k, v k * mode k 1) = a at h₁
  change (∑ k, v k * mode k 2) = a at h₂
  have hvEnergy : (∑ k, v k ^ 2) = (1 + 4 * a ^ 2) / (q : ℝ) := by
    have hs : (∑ k, v k * s k) = 2 * a := by
      simp only [s, mul_add, sum_add_distrib, h₁, h₂]
      ring
    have h := hgap v hv
    change (∑ k, v k ^ 2) - (1 + 4 * a ^ 2) / (q : ℝ) =
      (∑ k, (v k - v k) ^ 2) + (4 * a / (q : ℝ)) * ((∑ k, v k * s k) - 2 * a) at h
    simpa [hs, sub_eq_zero] using h
  refine ⟨hv, h₁, h₂, hgap, ?_⟩
  intro ha
  have hclip (habove : -1 / (2 * m) < a) : 0 < ∑ k, (max 0 (-v k)) ^ 2 := by
    obtain ⟨k, hk⟩ := not_forall.mp
      (fun hn => (not_le.mpr habove) ((hcut a ha).mp hn))
    have hneg : v k < 0 := lt_of_not_ge hk
    exact sum_pos' (fun j _ => sq_nonneg _) ⟨k, mem_univ k,
      pow_pos ((neg_pos.mpr hneg).trans_le (le_max_right _ _)) 2⟩
  have hFor (w : ZMod q → ℝ) (hw : ∀ k, 0 ≤ w k) (hws : ∑ k, w k = 1)
      (hwm1 : a ≤ ∑ k, w k * mode k 1) (hwm2 : a ≤ ∑ k, w k * mode k 2) :
      (1 + 4 * a ^ 2) / (q : ℝ) + (∑ k, (max 0 (-v k)) ^ 2) ≤ (∑ k, w k ^ 2) ∧
        ((∑ k, w k ^ 2) = (1 + 4 * a ^ 2) / (q : ℝ) ↔ w = v) := by
    have hmom : 2 * a ≤ ∑ k, w k * s k := by
      simp only [s, mul_add, sum_add_distrib]
      linarith
    have hmoment : 0 ≤ (4 * a / (q : ℝ)) * ((∑ k, w k * s k) - 2 * a) :=
      mul_nonneg (by positivity) (sub_nonneg.mpr hmom)
    have hdist : (∑ k, (max 0 (-v k)) ^ 2) ≤ ∑ k, (w k - v k) ^ 2 := by
      apply sum_le_sum
      intro k _
      by_cases hi : v k ≤ 0
      · rw [max_eq_right (neg_nonneg.mpr hi)]
        exact pow_le_pow_left₀ (neg_nonneg.mpr hi) (by linarith [hw k]) 2
      · rw [max_eq_left (by linarith), zero_pow (by decide)]
        positivity
    have he := hgap w hws
    change (∑ k, w k ^ 2) - (1 + 4 * a ^ 2) / (q : ℝ) =
      (∑ k, (w k - v k) ^ 2) + (4 * a / (q : ℝ)) * ((∑ k, w k * s k) - 2 * a) at he
    refine ⟨by linarith, ?_⟩
    constructor
    · intro hwE
      have hd : 0 ≤ ∑ k, (w k - v k) ^ 2 := sum_nonneg fun k _ => sq_nonneg _
      have hd0 : (∑ k, (w k - v k) ^ 2) = 0 := by linarith
      ext k
      have hz := (sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (w j - v j))).mp hd0 k (mem_univ k)
      rw [pow_two, mul_eq_zero] at hz
      exact sub_eq_zero.mp (hz.elim id id)
    · rintro rfl
      exact hvEnergy
  refine ⟨hcut a ha, hclip, fun w ⟨hn, hws, hm₁, hm₂⟩ => hFor w hn hws hm₁ hm₂, ?_⟩
  constructor
  · rintro ⟨w, ⟨hw, hws, hwm1, hwm2⟩, he⟩
    have heq := (hFor w hw hws hwm1 hwm2).2.mp he
    apply (hcut a ha).1
    rw [heq] at hw
    exact hw
  · intro hac
    exact ⟨v, ⟨(hcut a ha).2 hac, hv, h₁.ge, h₂.ge⟩, hvEnergy⟩

end D5.S3.Fourier.Concentration.FirstCosineClipping
