/- GID: D5/S3/FiniteGroups/BajnokBeattySquareDisplacementActualMoments
   generality: I
   mirror-B: D5/B/S3/FiniteGroups/BajnokBeattySquareDisplacementActualMoments
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Actual count-threshold moments from finite quotient detectors, odd dilation and GCD polarization. -/

import D5.S3.FiniteGroups.BajnokBeattySquareDisplacementThresholdDistribution
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.NumberTheory.Bernoulli
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.FiniteGroups.BajnokBeattySquareDisplacementActualMoments

open Filter Set
open scoped Topology BigOperators
open _root_.D5.S3.FiniteGroups.BajnokBeattySquareDisplacementThresholdDistribution

/-- Signed integer parameters; positivity is retained as part of the parameter. -/
abbrev Params := {p : ℤ // 5 ≤ p ∧ Odd p}

/-- The actual threshold error in the logarithmic coordinate. -/
def D (T : Params → ℕ → ℕ) (p : Params) (k : ℕ) : ℝ :=
  (T p k : ℝ) - (p.val : ℝ) * (qAt k : ℝ) / (4 * Real.log 2)

/-- Finite Cesaro average, with the usual totalized value at zero. -/
def avg (f : ℕ → ℝ) (N : ℕ) : ℝ := (∑ k ∈ Finset.range N, f k) / (N : ℝ)

theorem param_pos (p : Params) : (0 : ℝ) < (p.val : ℝ) := by
  exact_mod_cast (show (0 : ℤ) < p.val by have := p.property.1; omega)

theorem avg_sub (f g : ℕ → ℝ) (N : ℕ) :
    avg (fun (k : ℕ) => f k - g k) N = avg f N - avg g N := by
  simp only [avg, Finset.sum_sub_distrib, sub_div]

theorem avg_const_mul (c : ℝ) (f : ℕ → ℝ) (N : ℕ) :
    avg (fun (k : ℕ) => c * f k) N = c * avg f N := by
  rw [avg, ← Finset.mul_sum]
  simp only [avg, mul_div_assoc]

private theorem avg_div (f : ℕ → ℝ) (c : ℝ) (N : ℕ) :
    avg (fun (k : ℕ) => f k / c) N = avg f N / c := by
  unfold avg
  rw [← Finset.sum_div]
  ring

/-- The bracket supplies normalization invisible to every pair detector. -/
private theorem bracket_bounds (T : Params → ℕ → ℕ) (p : Params)
    (hT : ∀ k, bracketSC p.val (qAt k) (T p k)) :
    (∃ B : ℝ, ∀ k, |D T p k| ≤ B) ∧ (∀ᶠ k : ℕ in atTop, |D T p k| ≤ 1) := by
  let A : ℝ := (p.val : ℝ) / (4 * Real.log 2) - 1 / 2 + 1 / (2 * (p.val : ℝ))
  have hp := param_pos p
  have hL : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2))
  have hq (k : ℕ) : (1 : ℝ) ≤ (qAt k : ℝ) := by
    simp only [qAt, Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast]
    linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ (k : ℝ))]
  have hlo (k : ℕ) : -A / (qAt k : ℝ) < D T p k := by
    have he : ((qAt k : ℝ)^2 - 1) * (p.val : ℝ) /
          (4 * (qAt k : ℝ) * Real.log 2) + 1 / (2 * (qAt k : ℝ)) -
          1 / (2 * (qAt k : ℝ) * (p.val : ℝ)) =
        (p.val : ℝ) * (qAt k : ℝ) / (4 * Real.log 2) - A / (qAt k : ℝ) := by
      dsimp [A]
      field_simp [hL, hp.ne', (show (qAt k : ℝ) ≠ 0 by linarith [hq k])]
      <;> ring
    have hh := (hT k).2.1
    rw [he] at hh
    dsimp [D]
    rw [neg_div]
    linarith
  have hup (k : ℕ) : D T p k < 1 := by
    have hh : (T p k : ℝ) ≤
        (⌈(p.val : ℝ) * (qAt k : ℝ) / (4 * Real.log 2)⌉ : ℝ) := by
      exact_mod_cast (hT k).2.2
    have hc := Int.ceil_lt_add_one ((p.val : ℝ) * (qAt k : ℝ) / (4 * Real.log 2))
    dsimp [D]
    linarith
  constructor
  · refine ⟨|A| + 1, fun (k : ℕ) => abs_le.mpr ⟨?_, ?_⟩⟩
    · have hA : A / (qAt k : ℝ) ≤ |A| := by
        apply (div_le_iff₀ (show (0 : ℝ) < (qAt k : ℝ) by linarith [hq k])).mpr
        nlinarith [le_abs_self A, abs_nonneg A, hq k]
      have hh := hlo k
      rw [neg_div] at hh
      linarith
    · linarith [hup k, abs_nonneg A]
  · obtain ⟨K, hK⟩ := exists_nat_gt |A|
    filter_upwards [eventually_ge_atTop K] with k hk
    have hAk : A ≤ (qAt k : ℝ) := by
      have hKk : (K : ℝ) ≤ k := by exact_mod_cast hk
      have hkq : (k : ℝ) ≤ (qAt k : ℝ) := by
        simp only [qAt, Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast]
        linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ (k : ℝ))]
      linarith [le_abs_self A]
    have hA : A / (qAt k : ℝ) ≤ 1 :=
      (div_le_iff₀ (show (0 : ℝ) < (qAt k : ℝ) by linarith [hq k])).mpr (by simpa using hAk)
    have hh := hlo k
    rw [neg_div] at hh
    exact abs_le.mpr ⟨by linarith, (hup k).le⟩

/-- A finite prefix contributes only a constant divided by N. No cutoff is
    required to be uniform in the dilation parameter. -/
private theorem avg_eventual_close (f g : ℕ → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (h : ∀ᶠ k : ℕ in atTop, |f k - g k| ≤ c) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, |avg f N - avg g N| < c + ε := by
  classical
  obtain ⟨K, hK⟩ := eventually_atTop.mp h
  let C : ℝ := ∑ k ∈ Finset.range K, |f k - g k|
  have hsum (N : ℕ) : (∑ k ∈ Finset.range N, |f k - g k|) ≤ (N : ℝ) * c + C := by
    have hterm : (∑ k ∈ Finset.range N, |f k - g k|) ≤
        ∑ k ∈ Finset.range N, (c + if k < K then |f k - g k| else 0) := by
      apply Finset.sum_le_sum
      intro k hk
      by_cases hkK : k < K
      · simp only [ite_eq_left hkK]; linarith
      · simp only [ite_eq_right hkK, add_zero]
        exact hK k (Nat.le_of_not_gt hkK)
    have hprefix : (∑ k ∈ (Finset.range N).filter (fun (k : ℕ) => k < K), |f k - g k|) ≤ C := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro k hk
        exact Finset.mem_range.mpr (Finset.mem_filter.mp hk).2
      · intro k _ _
        exact abs_nonneg _
    rw [Finset.sum_add_distrib] at hterm
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hterm
    rw [← Finset.sum_filter] at hterm
    linarith
  have hpref : ∀ᶠ N : ℕ in atTop, C / (N : ℝ) < ε :=
    (tendsto_order.mp (tendsto_const_div_atTop_nhds_zero_nat C)).2 ε hε
  filter_upwards [hpref, eventually_gt_atTop (0 : ℕ)] with N hNε hN
  have hNR : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have ha : |avg f N - avg g N| ≤
      (∑ k ∈ Finset.range N, |f k - g k|) / (N : ℝ) := by
    rw [← avg_sub]
    dsimp [avg]
    rw [abs_div, abs_of_pos hNR]
    exact div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) hNR.le
  have hb := div_le_div_of_nonneg_right (hsum N) hNR.le
  have he : ((N : ℝ) * c + C) / (N : ℝ) = c + C / (N : ℝ) := by
    field_simp [hNR.ne']
  rw [he] at hb
  linarith

private def box (a b : ℕ) : Finset (ℕ × ℕ) := (Finset.range a).product (Finset.range b)
private def digit (d : ℤ) (uv : ℕ × ℕ) : ℤ := d * ((uv.2 : ℤ) - uv.1)

/-- The public closed mass is exactly a finite shared-divisor convolution. -/
private theorem mass_reference (p r : Params) (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hpa : p.val = (Int.gcd p.val r.val : ℤ) * a)
    (hrb : r.val = (Int.gcd p.val r.val : ℤ) * b) (z : ℤ) :
    mass p.val r.val z =
      (((box a b).filter (fun uv => digit (Int.gcd p.val r.val) uv = z)).card : ℝ) /
        ((a : ℝ) * (b : ℝ)) := by
  classical
  let d : ℤ := Int.gcd p.val r.val
  have hd : d ≠ 0 := by
    dsimp only [d]
    have hp : p.val ≠ 0 := by have := p.property.1; omega
    exact_mod_cast (Nat.ne_of_gt (Int.gcd_pos_of_ne_zero_left r.val hp))
  change p.val = d * (a : ℤ) at hpa
  change r.val = d * (b : ℤ) at hrb
  have hadiv : p.val / d = (a : ℤ) := by rw [hpa, Int.mul_ediv_cancel_left _ hd]
  have hbdiv : r.val / d = (b : ℤ) := by rw [hrb, Int.mul_ediv_cancel_left _ hd]
  by_cases hz : d ∣ z
  · have hzd : d * (z / d) = z := by simpa only [mul_comm] using Int.ediv_mul_cancel hz
    have hm : mass p.val r.val z =
        if -(a : ℤ) < z / d ∧ z / d < (b : ℤ) then
          ((min (min (a : ℤ) (b : ℤ))
            (min ((a : ℤ) + z / d) ((b : ℤ) - z / d)) : ℤ) : ℝ) /
            ((a : ℝ) * (b : ℝ)) else 0 := by
      unfold mass
      change (if _ : d ∣ z then _ else 0) = _
      rw [dite_eq_left hz]
      dsimp only
      rw [hadiv, hbdiv]
      simp only [Int.cast_min, Int.cast_add, Int.cast_sub, Int.cast_natCast]
      rfl
    have he (uv : ℕ × ℕ) : digit d uv = z ↔ (uv.2 : ℤ) - uv.1 = z / d := by
      dsimp [digit]
      constructor
      · intro h
        exact mul_left_cancel₀ hd (h.trans hzd.symm)
      · intro h
        rw [h, hzd]
    have hf : (box a b).filter (fun uv => digit d uv = z) =
        (box a b).filter (fun uv => (uv.2 : ℤ) - uv.1 = z / d) := by
      ext uv
      simp only [Finset.mem_filter, he]
    have hcard := fiber_count_formula a b (z / d)
    rw [hf]
    by_cases hj : -(a : ℤ) < z / d ∧ z / d < (b : ℤ)
    · have hc : max 0 (min (a : ℤ) ((b : ℤ) - z / d) - max 0 (-(z / d))) =
          min (min (a : ℤ) (b : ℤ)) (min ((a : ℤ) + z / d) ((b : ℤ) - z / d)) := by omega
      have hcR : (((box a b).filter (fun uv => (uv.2 : ℤ) - uv.1 = z / d)).card : ℝ) =
          ((min (min (a : ℤ) (b : ℤ))
            (min ((a : ℤ) + z / d) ((b : ℤ) - z / d)) : ℤ) : ℝ) := by
        exact_mod_cast hcard.trans hc
      rw [hcR]
      rw [hm, ite_eq_left hj]
    · have hc : max 0 (min (a : ℤ) ((b : ℤ) - z / d) - max 0 (-(z / d))) = 0 := by omega
      have hcR : (((box a b).filter (fun uv => (uv.2 : ℤ) - uv.1 = z / d)).card : ℝ) = 0 := by
        exact_mod_cast hcard.trans hc
      rw [hcR]
      rw [hm, ite_eq_right hj, zero_div]
  · have hf : (box a b).filter (fun uv => digit d uv = z) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro uv _ he
      exact hz ⟨(uv.2 : ℤ) - uv.1, he.symm⟩
    have hm : mass p.val r.val z = 0 := by
      unfold mass
      change (if _ : d ∣ z then _ else 0) = 0
      exact dite_eq_right hz
    rw [hm, hf]
    simp only [Finset.card_empty, Nat.cast_zero, zero_div]

private theorem fiber_sum {α : Type*} (A : Finset α) (X : α → ℤ) (S : Finset ℤ)
    (hX : ∀ k ∈ A, X k ∈ S) (f : ℤ → ℝ) :
    (∑ k ∈ A, f (X k)) =
      ∑ z ∈ S, f z * (((A.filter (fun k => X k = z)).card : ℝ)) := by
  classical
  simpa only [Finset.sum_const, nsmul_eq_mul, mul_comm] using
    (Finset.sum_fiberwise_of_maps_to' hX f).symm

/-- Exact finite GLOBAL range partition. Both the observed detector and the
    reference rectangle lie in S, so no infinite sum of zero masses is involved. -/
private theorem finite_transport (p r : Params) (X : ℕ → ℤ)
    (hB : ∃ B : ℝ, ∀ k, |(X k : ℝ)| ≤ B)
    (hX : ∀ z : ℤ, Tendsto (fun N : ℕ =>
      (((Finset.range N).filter (fun (k : ℕ) => X k = z)).card : ℝ) / (N : ℝ))
      atTop (𝓝 (mass p.val r.val z)))
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hpa : p.val = (Int.gcd p.val r.val : ℤ) * a)
    (hrb : r.val = (Int.gcd p.val r.val : ℤ) * b) (f : ℤ → ℝ) :
    Tendsto (avg (fun (k : ℕ) => f (X k))) atTop
      (𝓝 ((∑ uv ∈ box a b, f (digit (Int.gcd p.val r.val) uv)) /
        ((a : ℝ) * (b : ℝ)))) := by
  classical
  obtain ⟨B, hB⟩ := hB
  obtain ⟨M, hM⟩ := exists_nat_gt B
  let S : Finset ℤ := Finset.Icc (-(M : ℤ)) (M : ℤ) ∪
    (box a b).image (digit (Int.gcd p.val r.val))
  have hXS (k : ℕ) : X k ∈ S := by
    apply Finset.mem_union.mpr
    left
    apply Finset.mem_Icc.mpr
    have hh := abs_le.mp (hB k)
    constructor
    · exact_mod_cast (by linarith : -(M : ℝ) ≤ (X k : ℝ))
    · exact_mod_cast (by linarith : (X k : ℝ) ≤ (M : ℝ))
  have hRS (uv : ℕ × ℕ) (huv : uv ∈ box a b) : digit (Int.gcd p.val r.val) uv ∈ S :=
    Finset.mem_union.mpr (Or.inr (Finset.mem_image_of_mem _ huv))
  have hs := tendsto_finsetSum S (fun z _ =>
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => f z) atTop (𝓝 (f z))).mul (hX z))
  have heN (N : ℕ) : avg (fun (k : ℕ) => f (X k)) N =
      ∑ z ∈ S, f z *
        ((((Finset.range N).filter (fun (k : ℕ) => X k = z)).card : ℝ) / (N : ℝ)) := by
    rw [avg, fiber_sum (Finset.range N) X S (fun k _ => hXS k) f, Finset.sum_div]
    simp only [mul_div_assoc]
  have heL : (∑ z ∈ S, f z * mass p.val r.val z) =
      (∑ uv ∈ box a b, f (digit (Int.gcd p.val r.val) uv)) / ((a : ℝ) * (b : ℝ)) := by
    simp_rw [mass_reference p r a b ha hb hpa hrb, ← mul_div_assoc]
    rw [← Finset.sum_div, ← fiber_sum (box a b) (digit (Int.gcd p.val r.val)) S hRS f]
  rw [heL] at hs
  exact hs.congr' (Eventually.of_forall fun N => (heN N).symm)

private theorem range_moments (n : ℕ) :
    (∑ i ∈ Finset.range n, (i : ℝ)) = (n : ℝ) * ((n : ℝ) - 1) / 2 ∧
    (∑ i ∈ Finset.range n, (i : ℝ)^2) =
      (n : ℝ) * ((n : ℝ) - 1) * (2 * (n : ℝ) - 1) / 6 := by
  have h1 : (∑ i ∈ Finset.range n, (i : ℚ)) = (n : ℚ) * ((n : ℚ) - 1) / 2 := by
    calc
      _ = ∑ i ∈ Finset.range n, (i : ℚ)^1 := by simp only [pow_one]
      _ = _ := sum_range_pow n 1
      _ = (n : ℚ) * ((n : ℚ) - 1) / 2 := by
        norm_num [Finset.sum_range_succ, bernoulli_zero, bernoulli_one]
        <;> ring
  have h2 : (∑ i ∈ Finset.range n, (i : ℚ)^2) =
      (n : ℚ) * ((n : ℚ) - 1) * (2 * (n : ℚ) - 1) / 6 := by
    calc
      _ = _ := sum_range_pow n 2
      _ = (n : ℚ) * ((n : ℚ) - 1) * (2 * (n : ℚ) - 1) / 6 := by
        norm_num [Finset.sum_range_succ, bernoulli_zero, bernoulli_one, bernoulli_two]
        <;> ring
  constructor
  · have h := congrArg (fun x : ℚ => (x : ℝ)) h1
    push_cast at h
    exact h
  · exact_mod_cast h2

/-- Only finite rectangle algebra is used. The two finite digits here are
    reference coordinates, not independence assumptions about actual errors. -/
private theorem rectangle_moments (p r : Params) (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hpa : p.val = (Int.gcd p.val r.val : ℤ) * a)
    (hrb : r.val = (Int.gcd p.val r.val : ℤ) * b) :
    (∑ uv ∈ box a b, (digit (Int.gcd p.val r.val) uv : ℝ)) / ((a : ℝ) * (b : ℝ)) =
        ((r.val : ℝ) - (p.val : ℝ)) / 2 ∧
    (∑ uv ∈ box a b, (digit (Int.gcd p.val r.val) uv : ℝ)^2) / ((a : ℝ) * (b : ℝ)) =
        (2 * (p.val : ℝ)^2 + 2 * (r.val : ℝ)^2 - 3 * (p.val : ℝ) * (r.val : ℝ) -
          (Int.gcd p.val r.val : ℝ)^2) / 6 := by
  let d : ℝ := Int.gcd p.val r.val
  have haR : (a : ℝ) ≠ 0 := by exact_mod_cast ha.ne'
  have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
  have hpR : (p.val : ℝ) = d * (a : ℝ) := by
    dsimp only [d]
    exact_mod_cast hpa
  have hrR : (r.val : ℝ) = d * (b : ℝ) := by
    dsimp only [d]
    exact_mod_cast hrb
  have hbox : box a b = ((Finset.range a) ×ˢ (Finset.range b) : Finset (ℕ × ℕ)) := by
    ext uv
    constructor
    · intro h
      exact Finset.mem_product.mpr (Finset.mem_product.mp h)
    · intro h
      exact Finset.mem_product.mpr (Finset.mem_product.mp h)
  obtain ⟨ha1, ha2⟩ := range_moments a
  obtain ⟨hb1, hb2⟩ := range_moments b
  have hi1 (u : ℕ) : (∑ v ∈ Finset.range b, d * ((v : ℝ) - (u : ℝ))) =
      d * (∑ v ∈ Finset.range b, (v : ℝ)) - ((b : ℝ) * d) * (u : ℝ) := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  have hs1 : (∑ uv ∈ box a b, (digit (Int.gcd p.val r.val) uv : ℝ)) =
      d * (a : ℝ) * (∑ v ∈ Finset.range b, (v : ℝ)) -
        d * (b : ℝ) * (∑ u ∈ Finset.range a, (u : ℝ)) := by
    rw [hbox, Finset.sum_product]
    simp only [digit, Int.cast_mul, Int.cast_sub, Int.cast_natCast]
    change (∑ u ∈ Finset.range a, ∑ v ∈ Finset.range b, d * ((v : ℝ) - (u : ℝ))) = _
    simp_rw [hi1]
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, ← Finset.mul_sum]
    ring
  have hi2 (u : ℕ) : (∑ v ∈ Finset.range b, (d * ((v : ℝ) - (u : ℝ)))^2) =
      d^2 * (∑ v ∈ Finset.range b, (v : ℝ)^2) -
        (2 * d^2 * (∑ v ∈ Finset.range b, (v : ℝ))) * (u : ℝ) +
        ((b : ℝ) * d^2) * (u : ℝ)^2 := by
    calc
      _ = ∑ v ∈ Finset.range b,
          (d^2 * (v : ℝ)^2 - (2 * d^2 * (u : ℝ)) * (v : ℝ) + d^2 * (u : ℝ)^2) := by
        apply Finset.sum_congr rfl
        intro v _
        ring
      _ = _ := by
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
          Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring
  have hs2 : (∑ uv ∈ box a b, (digit (Int.gcd p.val r.val) uv : ℝ)^2) =
      d^2 * (a : ℝ) * (∑ v ∈ Finset.range b, (v : ℝ)^2) -
        2 * d^2 * (∑ u ∈ Finset.range a, (u : ℝ)) * (∑ v ∈ Finset.range b, (v : ℝ)) +
        d^2 * (b : ℝ) * (∑ u ∈ Finset.range a, (u : ℝ)^2) := by
    rw [hbox, Finset.sum_product]
    simp only [digit, Int.cast_mul, Int.cast_sub, Int.cast_natCast]
    change (∑ u ∈ Finset.range a, ∑ v ∈ Finset.range b, (d * ((v : ℝ) - (u : ℝ)))^2) = _
    simp_rw [hi2]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul, ← Finset.mul_sum]
    ring
  constructor
  · rw [hs1, ha1, hb1, hpR, hrR]
    field_simp [haR, hbR]
    <;> ring
  · rw [hs2, ha1, hb1, ha2, hb2, hpR, hrR]
    change _ = (2 * (d * (a : ℝ))^2 + 2 * (d * (b : ℝ))^2 -
      3 * (d * (a : ℝ)) * (d * (b : ℝ)) - d^2) / 6
    field_simp [haR, hbR]
    <;> ring

private def Y (T : Params → ℕ → ℕ) (p r : Params) (k : ℕ) : ℤ :=
  r.val * (T p k : ℤ) - p.val * (T r k : ℤ)

private theorem detector_identity (T : Params → ℕ → ℕ) (p r : Params) (k : ℕ) :
    (Y T p r k : ℝ) = (r.val : ℝ) * D T p k - (p.val : ℝ) * D T r k := by
  simp only [Y, D, Int.cast_sub, Int.cast_mul, Int.cast_natCast]
  ring

private theorem detector_moments (T : Params → ℕ → ℕ)
    (hT : ∀ (p : Params) (k : ℕ), bracketSC p.val (qAt k) (T p k))
    (hfreq : ∀ (p r : Params) (z : ℤ), Tendsto (fun N : ℕ =>
      (((Finset.range N).filter (fun (k : ℕ) => Y T p r k = z)).card : ℝ) / (N : ℝ))
      atTop (𝓝 (mass p.val r.val z))) (p r : Params) :
    Tendsto (avg (fun (k : ℕ) => (Y T p r k : ℝ))) atTop
      (𝓝 (((r.val : ℝ) - (p.val : ℝ)) / 2)) ∧
    Tendsto (avg (fun (k : ℕ) => (Y T p r k : ℝ)^2)) atTop
      (𝓝 ((2 * (p.val : ℝ)^2 + 2 * (r.val : ℝ)^2 -
        3 * (p.val : ℝ) * (r.val : ℝ) - (Int.gcd p.val r.val : ℝ)^2) / 6)) := by
  obtain ⟨Bp, hBp⟩ := (bracket_bounds T p (hT p)).1
  obtain ⟨Br, hBr⟩ := (bracket_bounds T r (hT r)).1
  have hbound : ∃ B : ℝ, ∀ k, |(Y T p r k : ℝ)| ≤ B := by
    refine ⟨(r.val : ℝ) * Bp + (p.val : ℝ) * Br, fun (k : ℕ) => ?_⟩
    rw [detector_identity]
    have hh : |(r.val : ℝ) * D T p k - (p.val : ℝ) * D T r k| ≤
        |(r.val : ℝ) * D T p k| + |(p.val : ℝ) * D T r k| := by
      simpa only [sub_eq_add_neg, abs_neg] using
        abs_add_le ((r.val : ℝ) * D T p k) (-((p.val : ℝ) * D T r k))
    rw [abs_mul, abs_mul, abs_of_pos (param_pos r), abs_of_pos (param_pos p)] at hh
    exact hh.trans (add_le_add (mul_le_mul_of_nonneg_left (hBp k) (param_pos r).le)
      (mul_le_mul_of_nonneg_left (hBr k) (param_pos p).le))
  obtain ⟨a, b, ha, hb, _, hpa, hrb⟩ := positive_gcd_coordinates p.val r.val
    (by have := p.property.1; omega) (by have := r.property.1; omega)
  obtain ⟨hc1, hc2⟩ := rectangle_moments p r a b ha hb hpa hrb
  constructor
  · have h := finite_transport p r (Y T p r) hbound (hfreq p r) a b ha hb hpa hrb
      (fun z => (z : ℝ))
    rw [hc1] at h
    exact h
  · have h := finite_transport p r (Y T p r) hbound (hfreq p r) a b ha hb hpa hrb
      (fun z => (z : ℝ)^2)
    rw [hc2] at h
    exact h

private def dilated (p : Params) (m : ℕ) (hm : 1 ≤ m) (hmo : Odd m) : Params :=
  ⟨(m : ℤ) * p.val, by
    constructor
    · have hp := p.property.1
      have hmZ : (1 : ℤ) ≤ m := by exact_mod_cast hm
      nlinarith
    · have hmO : Odd (m : ℤ) := by
        rcases hmo with ⟨u, hu⟩
        refine ⟨(u : ℤ), ?_⟩
        exact_mod_cast hu
      exact hmO.mul p.property.2⟩

private def X (T : Params → ℕ → ℕ) (p : Params) (m : ℕ) (hm : 1 ≤ m) (hmo : Odd m)
    (k : ℕ) : ℝ := D T p k - D T (dilated p m hm hmo) k / (m : ℝ)

private theorem dilation_moments (T : Params → ℕ → ℕ)
    (hT : ∀ (p : Params) (k : ℕ), bracketSC p.val (qAt k) (T p k))
    (hfreq : ∀ (p r : Params) (z : ℤ), Tendsto (fun N : ℕ =>
      (((Finset.range N).filter (fun (k : ℕ) => Y T p r k = z)).card : ℝ) / (N : ℝ))
      atTop (𝓝 (mass p.val r.val z)))
    (p : Params) (m : ℕ) (hm : 1 ≤ m) (hmo : Odd m) :
    Tendsto (avg (X T p m hm hmo)) atTop (𝓝 (((m : ℝ) - 1) / (2 * (m : ℝ)))) ∧
    Tendsto (avg (fun (k : ℕ) => X T p m hm hmo k ^ 2)) atTop
      (𝓝 ((((m : ℝ) - 1) * (2 * (m : ℝ) - 1)) / (6 * (m : ℝ)^2))) := by
  let r := dilated p m hm hmo
  have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hp := param_pos p
  have hr : (r.val : ℝ) = (m : ℝ) * (p.val : ℝ) := by
    simp only [r, dilated, Int.cast_mul, Int.cast_natCast]
  have hgZ : (Int.gcd p.val r.val : ℤ) = p.val := by
    apply Int.gcd_eq_left (by have := p.property.1; omega)
    exact ⟨(m : ℤ), by dsimp [r, dilated]; ring⟩
  have hg : (Int.gcd p.val r.val : ℝ) = (p.val : ℝ) := by exact_mod_cast hgZ
  have he (k : ℕ) : (Y T p r k : ℝ) / ((p.val : ℝ) * (m : ℝ)) = X T p m hm hmo k := by
    rw [detector_identity, hr]
    dsimp [X, r]
    field_simp [hp.ne', hmR.ne']
    <;> ring
  have he2 (k : ℕ) : (Y T p r k : ℝ)^2 / ((p.val : ℝ) * (m : ℝ))^2 =
      X T p m hm hmo k ^ 2 := by rw [← div_pow, he]
  obtain ⟨h1, h2⟩ := detector_moments T hT hfreq p r
  have h1' := h1.div_const ((p.val : ℝ) * (m : ℝ))
  have h2' := h2.div_const (((p.val : ℝ) * (m : ℝ))^2)
  have hμ : (((r.val : ℝ) - (p.val : ℝ)) / 2) / ((p.val : ℝ) * (m : ℝ)) =
      ((m : ℝ) - 1) / (2 * (m : ℝ)) := by
    rw [hr]
    field_simp [hp.ne', hmR.ne']
    <;> ring
  have hν : ((2 * (p.val : ℝ)^2 + 2 * (r.val : ℝ)^2 -
      3 * (p.val : ℝ) * (r.val : ℝ) - (Int.gcd p.val r.val : ℝ)^2) / 6) /
        ((p.val : ℝ) * (m : ℝ))^2 =
      (((m : ℝ) - 1) * (2 * (m : ℝ) - 1)) / (6 * (m : ℝ)^2) := by
    rw [hr, hg]
    field_simp [hp.ne', hmR.ne']
    <;> ring
  rw [hμ] at h1'
  rw [hν] at h2'
  constructor
  · exact h1'.congr' (Eventually.of_forall fun N => by rw [← avg_div]; simp_rw [he])
  · exact h2'.congr' (Eventually.of_forall fun N => by rw [← avg_div]; simp_rw [he2])

private theorem dilation_close (T : Params → ℕ → ℕ)
    (hT : ∀ (p : Params) (k : ℕ), bracketSC p.val (qAt k) (T p k))
    (p : Params) (m : ℕ) (hm : 1 ≤ m) (hmo : Odd m) :
    (∀ᶠ k : ℕ in atTop, |D T p k - X T p m hm hmo k| ≤ 1 / (m : ℝ)) ∧
    (∀ᶠ k : ℕ in atTop, |D T p k ^ 2 - X T p m hm hmo k ^ 2| ≤ 3 / (m : ℝ)) := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < m := by linarith
  have he : ∀ᶠ k : ℕ in atTop,
      |D T p k| ≤ 1 ∧ |D T (dilated p m hm hmo) k| ≤ 1 :=
    ((bracket_bounds T p (hT p)).2).and
      ((bracket_bounds T (dilated p m hm hmo) (hT _)).2)
  have hsmall : 1 / (m : ℝ) ≤ 1 := (div_le_iff₀ hmpos).mpr (by simpa using hmR)
  have hdiff (k : ℕ) (hk : |D T (dilated p m hm hmo) k| ≤ 1) :
      |D T p k - X T p m hm hmo k| ≤ 1 / (m : ℝ) := by
    have hid : D T p k - X T p m hm hmo k = D T (dilated p m hm hmo) k / (m : ℝ) := by
      dsimp [X]
      ring
    rw [hid, abs_div, abs_of_pos hmpos]
    exact div_le_div_of_nonneg_right hk hmpos.le
  constructor
  · exact he.mono fun k hk => hdiff k hk.2
  · filter_upwards [he] with k hk
    have hd := hdiff k hk.2
    have hx : |X T p m hm hmo k| ≤ 1 + 1 / (m : ℝ) := by
      have hh : |X T p m hm hmo k| ≤ |D T p k| + |D T p k - X T p m hm hmo k| := by
        calc
          _ = |D T p k + (X T p m hm hmo k - D T p k)| := by congr 1; ring
          _ ≤ |D T p k| + |X T p m hm hmo k - D T p k| := abs_add_le _ _
          _ = _ := by rw [abs_sub_comm (X T p m hm hmo k) (D T p k)]
      linarith
    have hs : |D T p k + X T p m hm hmo k| ≤ 3 :=
      (abs_add_le _ _).trans (by linarith)
    calc
      |D T p k ^ 2 - X T p m hm hmo k ^ 2| =
          |(D T p k - X T p m hm hmo k) * (D T p k + X T p m hm hmo k)| := by
        congr 1
        ring
      _ = |D T p k - X T p m hm hmo k| * |D T p k + X T p m hm hmo k| := abs_mul _ _
      _ ≤ (1 / (m : ℝ)) * 3 := mul_le_mul hd hs (abs_nonneg _) (by positivity)
      _ = 3 / (m : ℝ) := by ring

private theorem grid_errors (m : ℕ) (hm : 1 ≤ m) :
    |((m : ℝ) - 1) / (2 * (m : ℝ)) - 1 / 2| ≤ 1 / (2 * (m : ℝ)) ∧
    |(((m : ℝ) - 1) * (2 * (m : ℝ) - 1)) / (6 * (m : ℝ)^2) - 1 / 3| ≤
      1 / (2 * (m : ℝ)) := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hp : (0 : ℝ) < m := by linarith
  have h1 : ((m : ℝ) - 1) / (2 * (m : ℝ)) - 1 / 2 = -(1 / (2 * (m : ℝ))) := by
    field_simp [hp.ne']
    <;> ring
  have h2 : (((m : ℝ) - 1) * (2 * (m : ℝ) - 1)) / (6 * (m : ℝ)^2) - 1 / 3 =
      -(1 / (2 * (m : ℝ))) + 1 / (6 * (m : ℝ)^2) := by
    field_simp [hp.ne']
    <;> ring
  have hterm : 1 / (6 * (m : ℝ)^2) ≤ 1 / (2 * (m : ℝ)) := by
    apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 6 * (m : ℝ)^2)
      (by positivity : (0 : ℝ) < 2 * (m : ℝ))).mpr
    nlinarith
  rw [h1, h2]
  constructor
  · rw [abs_neg, abs_of_nonneg (by positivity)]
  · exact abs_le.mpr ⟨by linarith [show (0 : ℝ) ≤ 1 / (6 * (m : ℝ)^2) by positivity],
      by linarith [show (0 : ℝ) ≤ 1 / (2 * (m : ℝ)) by positivity]⟩

private theorem fine_odd_grid (δ : ℝ) (hδ : 0 < δ) :
    ∃ m : ℕ, 1 ≤ m ∧ Odd m ∧ 1 / (m : ℝ) < δ := by
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / δ)
  let m : ℕ := 2 * n + 1
  have hm : 1 ≤ m := by dsimp [m]; omega
  have hmn : n ≤ m := by dsimp [m]; omega
  have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  refine ⟨m, hm, ⟨n, rfl⟩, ?_⟩
  have hlt : 1 / δ < (m : ℝ) := lt_of_lt_of_le hn (by exact_mod_cast hmn)
  have hh := (div_lt_iff₀ hδ).mp hlt
  apply (div_lt_iff₀ hmR).mpr
  nlinarith

/-- Choose one odd grid first, then let N grow with that grid's own cutoffs.
    This proves existence of both limits; neither is an input hypothesis. -/
private theorem marginal_limits (T : Params → ℕ → ℕ)
    (hT : ∀ (p : Params) (k : ℕ), bracketSC p.val (qAt k) (T p k))
    (hfreq : ∀ (p r : Params) (z : ℤ), Tendsto (fun N : ℕ =>
      (((Finset.range N).filter (fun (k : ℕ) => Y T p r k = z)).card : ℝ) / (N : ℝ))
      atTop (𝓝 (mass p.val r.val z))) (p : Params) :
    Tendsto (avg (D T p)) atTop (𝓝 (1 / 2)) ∧
    Tendsto (avg (fun (k : ℕ) => D T p k ^ 2)) atTop (𝓝 (1 / 3)) := by
  constructor
  · apply Metric.tendsto_nhds.mpr
    intro ε hε
    obtain ⟨m, hm, hmo, hsmall⟩ := fine_odd_grid (ε / 16) (by positivity)
    have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    have hlim := (dilation_moments T hT hfreq p m hm hmo).1
    have hclose := avg_eventual_close (D T p) (X T p m hm hmo)
      (1 / (m : ℝ)) (by positivity) (dilation_close T hT p m hm hmo).1 (ε / 4) (by positivity)
    have hgrid : ∀ᶠ N : ℕ in atTop,
        |avg (X T p m hm hmo) N - ((m : ℝ) - 1) / (2 * (m : ℝ))| < ε / 4 := by
      simpa only [Real.dist_eq] using (Metric.tendsto_nhds.mp hlim) (ε / 4) (by positivity)
    have herr := (grid_errors m hm).1
    have hhalf : 1 / (2 * (m : ℝ)) = (1 / (m : ℝ)) / 2 := by ring
    rw [hhalf] at herr
    filter_upwards [hclose, hgrid] with N hNclose hNgrid
    rw [Real.dist_eq]
    have htri := abs_sub_le (avg (D T p) N) (avg (X T p m hm hmo) N) (1 / 2)
    have htri' := abs_sub_le (avg (X T p m hm hmo) N)
      (((m : ℝ) - 1) / (2 * (m : ℝ))) (1 / 2)
    linarith
  · apply Metric.tendsto_nhds.mpr
    intro ε hε
    obtain ⟨m, hm, hmo, hsmall⟩ := fine_odd_grid (ε / 16) (by positivity)
    have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    have hlim := (dilation_moments T hT hfreq p m hm hmo).2
    have hclose := avg_eventual_close (fun (k : ℕ) => D T p k ^ 2)
      (fun (k : ℕ) => X T p m hm hmo k ^ 2) (3 / (m : ℝ)) (by positivity)
      (dilation_close T hT p m hm hmo).2 (ε / 4) (by positivity)
    have hgrid : ∀ᶠ N : ℕ in atTop,
        |avg (fun (k : ℕ) => X T p m hm hmo k ^ 2) N -
          (((m : ℝ) - 1) * (2 * (m : ℝ) - 1)) / (6 * (m : ℝ)^2)| < ε / 4 := by
      simpa only [Real.dist_eq] using (Metric.tendsto_nhds.mp hlim) (ε / 4) (by positivity)
    have herr := (grid_errors m hm).2
    have hhalf : 1 / (2 * (m : ℝ)) = (1 / (m : ℝ)) / 2 := by ring
    have hthree : 3 / (m : ℝ) = 3 * (1 / (m : ℝ)) := by ring
    rw [hhalf] at herr
    filter_upwards [hclose, hgrid] with N hNclose hNgrid
    rw [Real.dist_eq]
    rw [hthree] at hNclose
    have htri := abs_sub_le (avg (fun (k : ℕ) => D T p k ^ 2) N)
      (avg (fun (k : ℕ) => X T p m hm hmo k ^ 2) N) (1 / 3)
    have htri' := abs_sub_le (avg (fun (k : ℕ) => X T p m hm hmo k ^ 2) N)
      ((((m : ℝ) - 1) * (2 * (m : ℝ) - 1)) / (6 * (m : ℝ)^2)) (1 / 3)
    linarith

private theorem polarization_average (T : Params → ℕ → ℕ) (p r : Params) (N : ℕ) :
    avg (fun (k : ℕ) => D T p k * D T r k) N =
      ((r.val : ℝ)^2 * avg (fun (k : ℕ) => D T p k ^ 2) N +
        (p.val : ℝ)^2 * avg (fun (k : ℕ) => D T r k ^ 2) N -
        avg (fun (k : ℕ) => (Y T p r k : ℝ)^2) N) / (2 * (p.val : ℝ) * (r.val : ℝ)) := by
  have hp := param_pos p
  have hr := param_pos r
  have he (k : ℕ) : D T p k * D T r k =
      ((r.val : ℝ)^2 * D T p k ^ 2 + (p.val : ℝ)^2 * D T r k ^ 2 -
        (Y T p r k : ℝ)^2) / (2 * (p.val : ℝ) * (r.val : ℝ)) := by
    rw [detector_identity]
    field_simp [hp.ne', hr.ne']
    <;> ring
  calc
    _ = avg (fun (k : ℕ) => ((r.val : ℝ)^2 * D T p k ^ 2 +
        (p.val : ℝ)^2 * D T r k ^ 2 - (Y T p r k : ℝ)^2) /
          (2 * (p.val : ℝ) * (r.val : ℝ))) N := by
      unfold avg
      congr 1
      apply Finset.sum_congr rfl
      intro k _
      exact he k
    _ = _ := by
      rw [avg_div, avg_sub]
      have hadd : avg (fun (k : ℕ) => (r.val : ℝ)^2 * D T p k ^ 2 +
          (p.val : ℝ)^2 * D T r k ^ 2) N =
          avg (fun (k : ℕ) => (r.val : ℝ)^2 * D T p k ^ 2) N +
            avg (fun (k : ℕ) => (p.val : ℝ)^2 * D T r k ^ 2) N := by
        simp only [avg, Finset.sum_add_distrib, add_div]
      rw [hadd, avg_const_mul, avg_const_mul]

/-- One actual threshold family for every signed odd p>=5. Every original
    crossing clause, both logarithmic brackets and original-crossing uniqueness
    are retained at every q=2*k+3. The marginal limits are established by fixed
    odd dilation; all mixed moments and empirical covariances, including the
    diagonal, follow from the finite shared-divisor convolution and polarization. -/
theorem actual_square_displacement_actual_moments :
    ∃ T : Params → ℕ → ℕ,
      (∀ (p : Params) (k : ℕ), bracketSC p.val (qAt k) (T p k) ∧
        ∀ t : ℕ, originalSC p.val (qAt k) t → t = T p k) ∧
      (∀ p : Params,
        Tendsto (avg (D T p)) atTop (𝓝 (1 / 2)) ∧
        Tendsto (avg (fun (k : ℕ) => D T p k ^ 2)) atTop (𝓝 (1 / 3))) ∧
      (∀ p r : Params,
        Tendsto (avg (fun (k : ℕ) => D T p k * D T r k)) atTop
          (𝓝 (1 / 4 + (Int.gcd p.val r.val : ℝ)^2 /
            (12 * (p.val : ℝ) * (r.val : ℝ)))) ∧
        Tendsto (fun N : ℕ => avg (fun (k : ℕ) => D T p k * D T r k) N -
          avg (D T p) N * avg (D T r) N) atTop
          (𝓝 ((Int.gcd p.val r.val : ℝ)^2 / (12 * (p.val : ℝ) * (r.val : ℝ))))) := by
  classical
  have hex (p : Params) : ∃ V : ℕ → ℕ,
      ∀ k, bracketSC p.val (qAt k) (V k) ∧
        ∀ t, originalSC p.val (qAt k) t → t = V k := by
    obtain ⟨V, W, hV, _, _⟩ := actual_square_displacement_threshold_distribution
      p.val p.val p.property.1 p.property.2 p.property.1 p.property.2
    exact ⟨V, hV⟩
  choose T hT using hex
  have hfreq (p r : Params) (z : ℤ) : Tendsto (fun N : ℕ =>
      (((Finset.range N).filter (fun (k : ℕ) => Y T p r k = z)).card : ℝ) / (N : ℝ))
      atTop (𝓝 (mass p.val r.val z)) := by
    obtain ⟨V, W, hV, hW, hhist⟩ := actual_square_displacement_threshold_distribution
      p.val r.val p.property.1 p.property.2 r.property.1 r.property.2
    have heV : V = T p := by
      funext k
      exact (hT p k).2 (V k) (hV k).1.1
    have heW : W = T r := by
      funext k
      exact (hT r k).2 (W k) (hW k).1.1
    rw [heV, heW] at hhist
    convert hhist z using 1
    funext N
    apply congrArg (fun s : Finset ℕ => (s.card : ℝ) / (N : ℝ))
    ext k
    constructor
    · intro hk
      exact Finset.mem_filter.mpr (Finset.mem_filter.mp hk)
    · intro hk
      exact Finset.mem_filter.mpr (Finset.mem_filter.mp hk)
  have hbr : ∀ (p : Params) (k : ℕ), bracketSC p.val (qAt k) (T p k) := fun p k => (hT p k).1
  have hmarg := marginal_limits T hbr hfreq
  refine ⟨T, hT, hmarg, ?_⟩
  intro p r
  have hp := param_pos p
  have hr := param_pos r
  have hY := (detector_moments T hbr hfreq p r).2
  have hpconst : Tendsto (fun _ : ℕ => (p.val : ℝ)^2) atTop (𝓝 ((p.val : ℝ)^2)) :=
    tendsto_const_nhds
  have hrconst : Tendsto (fun _ : ℕ => (r.val : ℝ)^2) atTop (𝓝 ((r.val : ℝ)^2)) :=
    tendsto_const_nhds
  have hpol := (((hrconst.mul (hmarg p).2).add
    (hpconst.mul (hmarg r).2)).sub hY).div_const
      (2 * (p.val : ℝ) * (r.val : ℝ))
  have hval : ((r.val : ℝ)^2 * (1 / 3) + (p.val : ℝ)^2 * (1 / 3) -
      (2 * (p.val : ℝ)^2 + 2 * (r.val : ℝ)^2 - 3 * (p.val : ℝ) * (r.val : ℝ) -
        (Int.gcd p.val r.val : ℝ)^2) / 6) / (2 * (p.val : ℝ) * (r.val : ℝ)) =
      1 / 4 + (Int.gcd p.val r.val : ℝ)^2 / (12 * (p.val : ℝ) * (r.val : ℝ)) := by
    field_simp [hp.ne', hr.ne']
    <;> ring
  change Tendsto (fun N => ((r.val : ℝ)^2 * avg (fun (k : ℕ) => D T p k ^ 2) N +
    (p.val : ℝ)^2 * avg (fun (k : ℕ) => D T r k ^ 2) N - avg (fun (k : ℕ) => (Y T p r k : ℝ)^2) N) /
      (2 * (p.val : ℝ) * (r.val : ℝ))) atTop (𝓝 _) at hpol
  rw [hval] at hpol
  have hmix : Tendsto (avg (fun (k : ℕ) => D T p k * D T r k)) atTop
      (𝓝 (1 / 4 + (Int.gcd p.val r.val : ℝ)^2 / (12 * (p.val : ℝ) * (r.val : ℝ)))) :=
    hpol.congr' (Eventually.of_forall fun N => (polarization_average T p r N).symm)
  refine ⟨hmix, ?_⟩
  have hcov := hmix.sub ((hmarg p).1.mul (hmarg r).1)
  have hvalue : (1 / 4 + (Int.gcd p.val r.val : ℝ)^2 /
      (12 * (p.val : ℝ) * (r.val : ℝ))) - (1 / 2) * (1 / 2) =
      (Int.gcd p.val r.val : ℝ)^2 / (12 * (p.val : ℝ) * (r.val : ℝ)) := by ring
  rw [hvalue] at hcov
  exact hcov

end D5.S3.FiniteGroups.BajnokBeattySquareDisplacementActualMoments
