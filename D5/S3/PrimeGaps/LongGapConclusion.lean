/- GID: D5/S3/PrimeGaps/LongGapConclusion
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Port the covering-residue construction closing Theorem 1.1 on long prime gaps. -/

/- Ported from openai/LongGapsBetweenPrimes commit 8f5fa88c88b4750028c05b66b081d56a92418054.
   Modified by trureturing on 2026-09-04: repository routing and module split. -/
/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import D5.S3.PrimeGaps.SmoothCovers

namespace LongGapsBetweenPrimes

noncomputable section

/-- The real scale of the interval covered by the sieve. -/
def coverScale (x : ℝ) : ℝ :=
  x * Real.log x ^ 2 * Real.log (Real.log (Real.log x)) / Real.log (Real.log x) ^ 2

/-- The covering length is the integer part of `η * coverScale x`. -/
lemma coverLength_eq (η x : ℝ) : coverLength η x = ⌊η * coverScale x⌋₊ := by
  simp only [coverLength, coverScale, mul_div_assoc, mul_assoc]

/-- The constant combining the initial sieve and greedy survival bounds. -/
def coveringConstant : ℝ :=
  10 * smoothScaleConstant * Real.exp 6 * (Real.log 4 + 2)

/-- The combined covering constant is positive. -/
lemma coveringConstant_pos : 0 < coveringConstant := by
  have := smoothScaleConstant_pos
  unfold coveringConstant
  positivity

/-- A covering scale small enough to meet the short-translate density threshold. -/
def coverEta : ℝ := sieveDelta / (2 * (1 + coveringConstant))

/-- The chosen covering scale is positive. -/
lemma coverEta_pos : 0 < coverEta := by
  exact div_pos sieveDelta_pos
    (mul_pos (by norm_num) (add_pos zero_lt_one coveringConstant_pos))

/-- The chosen covering scale is at most one. -/
lemma coverEta_le_one : coverEta ≤ 1 := by
  unfold coverEta
  apply (div_le_one (by linarith [coveringConstant_pos])).mpr
  linarith [sieveDelta_lt_half, coveringConstant_pos]

/-- The combined covering bound fits within the sieve density threshold. -/
lemma coveringConstant_mul_eta_le : coveringConstant * coverEta ≤ sieveDelta := by
  have hC := coveringConstant_pos
  have hδ := sieveDelta_pos
  unfold coverEta
  rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
  nlinarith [mul_pos hC hδ]

/-- Eventually, the rounded covering length has the required size and retains half its scale. -/
lemma eventually_coverLength_bounds {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) :
    ∀ᶠ x : ℝ in Filter.atTop, x < (coverLength η x : ℝ) ∧
      (coverLength η x : ℝ) ≤ x * Real.log x ^ 2 ∧
      (η / 2) * coverScale x ≤ (coverLength η x : ℝ) := by
  filter_upwards [eventually_cover_parameters,
    Real.tendsto_log_atTop.eventually_ge_atTop (2 / η)] with x hp hηL
  obtain ⟨hx, hL, hLL, hLLL, hquad, _, _, _, _⟩ := hp
  have hx0 : 0 < x := by linarith
  have hL0 : 0 < Real.log x := by linarith
  have hLL0 : 0 < Real.log (Real.log x) := by linarith
  have hden : Real.log (Real.log x) ^ 2 ≤ Real.log x := by
    nlinarith [smoothScaleConstant_gt_ten, sq_nonneg (Real.log (Real.log x))]
  have hlower : x * Real.log x ≤ coverScale x := by
    unfold coverScale
    apply (le_div_iff₀ (sq_pos_of_pos hLL0)).mpr
    calc
      _ ≤ x * Real.log x * Real.log x :=
        mul_le_mul_of_nonneg_left hden (by positivity)
      _ = x * Real.log x ^ 2 := by ring
      _ ≤ _ := le_mul_of_one_le_right (by positivity) hLLL
  have hbig : 2 * x ≤ η * coverScale x := by
    calc
      _ ≤ (Real.log x * η) * x :=
        mul_le_mul_of_nonneg_right ((div_le_iff₀ hη).mp hηL) hx0.le
      _ = η * (x * Real.log x) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hlower hη.le
  have hscale0 : 0 ≤ coverScale x := (by positivity : 0 ≤ x * Real.log x).trans hlower
  have hupper : η * coverScale x ≤ x * Real.log x ^ 2 := by
    calc
      _ ≤ coverScale x := mul_le_of_le_one_left hscale0 hη1
      _ ≤ _ := by
        unfold coverScale
        apply (div_le_iff₀ (sq_pos_of_pos hLL0)).mpr
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        nlinarith [Real.log_le_sub_one_of_pos hLL0]
  rw [coverLength_eq]
  have hfloor := Nat.lt_floor_add_one (η * coverScale x)
  exact ⟨by linarith, (Nat.floor_le (mul_nonneg hη.le hscale0)).trans hupper,
    by linarith⟩

/-- Every prime in the zero-residue sieve is at most `x`. -/
lemma zeroCoverPrimes_subset {x : ℝ} (hx : 0 ≤ x) (hW : coverW x ≤ ⌊x⌋₊) :
    zeroCoverPrimes x ⊆ ⌊x⌋₊.primesLE := by
  intro p hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact Nat.mem_primesLE.mpr ⟨(Nat.mem_primesLE.mp hp).1.trans hW, (Nat.mem_primesLE.mp hp).2⟩
  · have hm := Nat.mem_primesLE.mp (Finset.mem_sdiff.mp hp).1
    exact Nat.mem_primesLE.mpr ⟨hm.1.trans (Nat.floor_mono (by linarith : x / 2 ≤ x)), hm.2⟩

/-- The zero-residue and greedy prime sets are disjoint. -/
lemma zeroCoverPrimes_disjoint (x : ℝ) :
    Disjoint (zeroCoverPrimes x) (auxiliaryPrimes (coverW x) (coverZ x)) := by
  simp only [zeroCoverPrimes, auxiliaryPrimes, Finset.disjoint_left, Finset.mem_union,
    Finset.mem_sdiff]
  tauto

/-- For large `x`, residue classes leave at most `sieveDelta * x` integers uncovered. -/
lemma eventually_covering_residues : ∀ᶠ x : ℝ in Filter.atTop,
    ∃ a : ℕ → ℕ, (∀ p ∈ ⌊x⌋₊.primesLE, a p < p) ∧
      ((survivors (Finset.Icc 1 (coverLength coverEta x)) ⌊x⌋₊.primesLE a).card : ℝ) ≤
        sieveDelta * x := by
  classical
  filter_upwards [eventually_cover_parameters,
    eventually_coverLength_bounds coverEta_pos coverEta_le_one,
    eventually_zeroSurvivors_bound, eventually_greedy_product_bound]
    with x hparameters hlength hzero hgreedy
  obtain ⟨hx, hL, hLL, hLLL, _, _, _, hZlow, hZhigh⟩ := hparameters
  have hx0 : 0 < x := by linarith
  have hL0 : 0 < Real.log x := by linarith
  have hLL0 : 0 < Real.log (Real.log x) := by linarith
  have hLLL0 : 0 < Real.log (Real.log (Real.log x)) := by linarith
  have hZ := coverZ_le_floor hx0 hZhigh
  have hW := (coverW_le_coverZ (by linarith) hZlow).trans hZ
  obtain ⟨a, ha, hcard⟩ := combine_greedy_residues
    (Finset.Icc 1 (coverLength coverEta x)) (zeroCoverPrimes x)
    (auxiliaryPrimes (coverW x) (coverZ x)) ⌊x⌋₊.primesLE
    (zeroCoverPrimes_subset hx0.le hW)
    (by
      intro p hp
      obtain ⟨hp, _, hpZ⟩ := mem_auxiliaryPrimes.mp hp
      exact Nat.mem_primesLE.mpr ⟨hpZ.trans hZ, hp⟩)
    (zeroCoverPrimes_disjoint x) (fun p hp => (Nat.mem_primesLE.mp hp).2.pos)
  refine ⟨a, ha, ?_⟩
  have hfloor : (coverLength coverEta x : ℝ) ≤ coverEta * coverScale x := by
    rw [coverLength_eq]
    apply Nat.floor_le
    unfold coverScale
    exact mul_nonneg coverEta_pos.le (by positivity)
  have hzero' := hzero (coverLength coverEta x) hlength.1.le hlength.2.1
  have hC := smoothScaleConstant_pos
  calc
    _ ≤ ((zeroSurvivors x (coverLength coverEta x)).card : ℝ) *
        ∏ p ∈ auxiliaryPrimes (coverW x) (coverZ x), (1 - 1 / (p : ℝ)) := hcard
    _ ≤ ((zeroSurvivors x (coverLength coverEta x)).card : ℝ) *
        (10 * smoothScaleConstant * Real.exp 6 * Real.log (Real.log x) ^ 2 /
          (Real.log x * Real.log (Real.log (Real.log x)))) :=
      mul_le_mul_of_nonneg_left hgreedy (Nat.cast_nonneg _)
    _ ≤ ((Real.log 4 + 2) * (coverEta * coverScale x) / Real.log x) *
        (10 * smoothScaleConstant * Real.exp 6 * Real.log (Real.log x) ^ 2 /
          (Real.log x * Real.log (Real.log (Real.log x)))) := by
      gcongr
      exact hzero'.trans (by gcongr)
    _ = (coveringConstant * coverEta) * x := by
      unfold coveringConstant coverScale
      field_simp
    _ ≤ sieveDelta * x := mul_le_mul_of_nonneg_right coveringConstant_mul_eta_le hx0.le

/-- Combining the covering with Proposition 1.2 produces the long prime gaps. -/
theorem eventually_prime_gaps_in_x : ∀ᶠ x : ℝ in Filter.atTop,
    ∃ p q : ℕ, ConsecutivePrimes p q ∧ (q : ℝ) ≤ Real.exp (8 * x) ∧
      (coverEta / 2) * coverScale x ≤ ((q - p : ℕ) : ℝ) := by
  classical
  filter_upwards [eventually_covering_residues,
    eventually_coverLength_bounds coverEta_pos coverEta_le_one,
    short_translates_with_sieveDelta, Filter.eventually_ge_atTop (2 : ℝ)]
    with x hcover hlength htranslate hx
  let H := coverLength coverEta x
  let Q := primorial ⌊x⌋₊
  have hx0 : 0 ≤ x := by linarith
  obtain ⟨a, ha, hcard⟩ := hcover
  have hcop : (↑⌊x⌋₊.primesLE : Set ℕ).Pairwise Nat.Coprime := by
    intro p hp q hq hpq
    exact (Nat.coprime_primes (Nat.mem_primesLE.mp hp).2
      (Nat.mem_primesLE.mp hq).2).mpr hpq
  let b := Nat.chineseRemainderOfFinset (fun p => p - a p) (fun p => p) ⌊x⌋₊.primesLE
    (fun p hp => (Nat.mem_primesLE.mp hp).2.ne_zero) hcop
  have hb : b.val < Q := by
    simpa only [Q, primorial_eq_prod_primesLE] using
      Nat.chineseRemainderOfFinset_lt_prod (fun p => p - a p) (fun p => p)
        (fun p hp => (Nat.mem_primesLE.mp hp).2.ne_zero) hcop
  obtain ⟨t, ht, htbound, htcomposite⟩ := htranslate H hlength.1 hlength.2.1
    (survivors (Finset.Icc 1 H) ⌊x⌋₊.primesLE a) (Finset.filter_subset _ _) hcard b.val hb
  let N := b.val + Q * t
  have hQN : Q ≤ N := (Nat.le_mul_of_pos_right Q ht).trans (Nat.le_add_left _ _)
  have hQ2 : 2 ≤ Q := Nat.le_of_dvd (primorial_pos _)
    (Nat.prime_two.dvd_primorial_iff.mpr (Nat.le_floor hx))
  have hcomposite : ∀ s ∈ Finset.Icc 1 H, ¬Nat.Prime (N + s) := by
    intro s hs
    by_cases hsurvives : s ∈ survivors (Finset.Icc 1 H) ⌊x⌋₊.primesLE a
    · exact htcomposite s hsurvives
    · obtain ⟨p, hp, hsp⟩ : ∃ p ∈ ⌊x⌋₊.primesLE, s % p = a p := by
        simpa [survivors, hs] using hsurvives
      obtain ⟨hpx, hpprime⟩ := Nat.mem_primesLE.mp hp
      have hpQ : p ∣ Q := hpprime.dvd_primorial_iff.mpr hpx
      have hbs : p ∣ b.val + s := by
        apply Nat.dvd_of_mod_eq_zero
        calc
          (b.val + s) % p = ((p - a p) + a p) % p := by
            rw [Nat.add_mod, b.property p hp, hsp, Nat.add_mod (p - a p),
              Nat.mod_eq_of_lt (ha p hp)]
          _ = 0 := by rw [Nat.sub_add_cancel (ha p hp).le, Nat.mod_self]
      have hdiv : p ∣ N + s := by
        change p ∣ b.val + Q * t + s
        rw [Nat.add_right_comm]
        exact dvd_add hbs (dvd_mul_of_dvd_left hpQ t)
      have hlt : p < N + s := by
        have := Nat.le_of_dvd (primorial_pos _) hpQ
        have := (Finset.mem_Icc.mp hs).1
        omega
      intro hprime
      exact (hprime.eq_one_or_self_of_dvd p hdiv).elim hpprime.ne_one (ne_of_lt hlt)
  obtain ⟨p, q, hpq, _, _, hqN, hgap⟩ :=
    consecutivePrimes_of_composite_interval (hQ2.trans hQN) (H := H) (by
      intro n hNn hnH
      have hs : n - N ∈ Finset.Icc 1 H := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      simpa only [Nat.add_sub_of_le hNn.le] using hcomposite (n - N) hs)
  refine ⟨p, q, hpq, ?_, hlength.2.2.trans (by exact_mod_cast hgap.le)⟩
  have hQbound : (Q : ℝ) ≤ Real.exp (3 * x) := by
    calc
      (Q : ℝ) ≤ (4 : ℝ) ^ ⌊x⌋₊ := by exact_mod_cast primorial_le_four_pow ⌊x⌋₊
      _ ≤ Real.exp 3 ^ ⌊x⌋₊ := by
        gcongr
        linarith [Real.add_one_le_exp (3 : ℝ)]
      _ = Real.exp (3 * (⌊x⌋₊ : ℝ)) := by rw [← Real.exp_nat_mul, mul_comm]
      _ ≤ Real.exp (3 * x) := by gcongr; exact Nat.floor_le hx0
  have hNbound : (N : ℝ) ≤ 2 * Real.exp (4 * x) := by
    calc
      (N : ℝ) = (b.val : ℝ) + (Q : ℝ) * t := by simp only [N, Nat.cast_add, Nat.cast_mul]
      _ ≤ (Q : ℝ) * (1 + Real.exp x) := by
        have hb' : (b.val : ℝ) ≤ Q := by exact_mod_cast hb.le
        nlinarith [mul_le_mul_of_nonneg_left htbound (Nat.cast_nonneg Q)]
      _ ≤ Real.exp (3 * x) * (2 * Real.exp x) :=
        mul_le_mul hQbound (by linarith [Real.one_le_exp hx0])
          (by positivity) (Real.exp_nonneg _)
      _ = 2 * Real.exp (4 * x) := by
        rw [show (4 : ℝ) * x = 3 * x + x by ring, Real.exp_add]
        ring
  calc
    (q : ℝ) ≤ 2 * (N : ℝ) := by exact_mod_cast hqN
    _ ≤ 4 * Real.exp (4 * x) := by linarith
    _ ≤ Real.exp (4 * x) * Real.exp (4 * x) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
      linarith [Real.add_one_le_exp (4 * x)]
    _ = Real.exp (8 * x) := by rw [← Real.exp_add]; congr 1; ring

/-- Dividing by `c` preserves at least half of `log u` when `log u ≥ 2 * log c`. -/
lemma half_log_le_log_div {u c : ℝ} (hu : 0 < u) (hc : 0 < c)
    (h : 2 * Real.log c ≤ Real.log u) : Real.log u / 2 ≤ Real.log (u / c) := by
  rw [Real.log_div hu.ne' hc.ne']
  linarith

/-- Rescaling by one eighth reduces `coverScale` by at most a factor of 64 eventually. -/
lemma eventually_coverScale_div_eight : ∀ᶠ y : ℝ in Filter.atTop,
    coverScale y / 64 ≤ coverScale (y / 8) := by
  have hlog := Real.tendsto_log_atTop
  have hloglog := hlog.comp hlog
  have hlogloglog := hlog.comp hloglog
  filter_upwards [eventually_cover_parameters,
    hlog.eventually_ge_atTop (2 * Real.log 8),
    hloglog.eventually_ge_atTop (2 * Real.log 2),
    hlogloglog.eventually_ge_atTop (2 * Real.log 2)] with y hy h₁ h₂ h₃
  obtain ⟨hy, hL, hLL, hLLL, _⟩ := hy
  have hy0 : 0 < y := by linarith
  have hL0 : 0 < Real.log y := by linarith
  have hLL0 : 0 < Real.log (Real.log y) := by linarith
  have h₁' := half_log_le_log_div hy0 (by norm_num : (0 : ℝ) < 8) h₁
  have h₂' : Real.log (Real.log y) / 2 ≤ Real.log (Real.log (y / 8)) :=
    (half_log_le_log_div hL0 (by norm_num : (0 : ℝ) < 2) h₂).trans
      (Real.log_le_log (by positivity) h₁')
  have h₃' : Real.log (Real.log (Real.log y)) / 2 ≤
      Real.log (Real.log (Real.log (y / 8))) :=
    (half_log_le_log_div hLL0 (by norm_num : (0 : ℝ) < 2) h₃).trans
      (Real.log_le_log (by positivity) h₂')
  have hL0' : 0 < Real.log (y / 8) := by linarith
  have hLL0' : 0 < Real.log (Real.log (y / 8)) := by linarith
  have hLLL0' : 0 < Real.log (Real.log (Real.log (y / 8))) := by linarith
  have hden : Real.log (Real.log (y / 8)) ≤ Real.log (Real.log y) :=
    Real.log_le_log hL0' (Real.log_le_log (by positivity) (by linarith))
  unfold coverScale
  calc
    _ = (y / 8) * (Real.log y / 2) ^ 2 *
        (Real.log (Real.log (Real.log y)) / 2) / Real.log (Real.log y) ^ 2 := by ring
    _ ≤ _ := by gcongr

/-- The prime-gap scale is the covering scale evaluated at `log X`. -/
lemma gapScale_eq_coverScale_log (X : ℝ) : gapScale X = coverScale (Real.log X) := by
  rfl

/-- Theorem 1.1: the unconditional long-gap bound in the paper. -/
theorem long_gap_theorem : LongGapTheorem := by
  refine ⟨coverEta / 128, by have h := coverEta_pos; positivity, ?_⟩
  have hx : Filter.Tendsto (fun X : ℝ => Real.log X / 8) Filter.atTop Filter.atTop :=
    Filter.Tendsto.atTop_div_const (by norm_num) Real.tendsto_log_atTop
  filter_upwards [hx.eventually eventually_prime_gaps_in_x,
    Real.tendsto_log_atTop.eventually eventually_coverScale_div_eight,
    Filter.eventually_gt_atTop (0 : ℝ)] with X hgap hscale hX
  obtain ⟨p, q, hpq, hq, hwidth⟩ := hgap
  refine ⟨p, q, hpq, ?_, ?_⟩
  · have he : 8 * (Real.log X / 8) = Real.log X := by ring
    rw [he, Real.exp_log hX] at hq
    exact hq
  · rw [gapScale_eq_coverScale_log]
    have hη : 0 ≤ coverEta / 2 := by have h := coverEta_pos; positivity
    have hm := mul_le_mul_of_nonneg_left hscale hη
    nlinarith

/-- Consecutive primes occur at adjacent indices in the prime enumeration. -/
lemma consecutivePrimes_eq_nth {p q : ℕ} (h : ConsecutivePrimes p q) :
    ∃ n : ℕ, Nat.nth Nat.Prime n = p ∧ Nat.nth Nat.Prime (n + 1) = q := by
  rcases h with ⟨hp, hq, hpq, hgap⟩
  have hmono := Nat.nth_strictMono Nat.infinite_setOfPred_prime
  have hn : Nat.count Nat.Prime p < Nat.count Nat.Prime q := by
    apply hmono.lt_iff_lt.mp
    simpa only [Nat.nth_count hp, Nat.nth_count hq] using hpq
  refine ⟨Nat.count Nat.Prime p, Nat.nth_count hp, ?_⟩
  apply le_antisymm
  · simpa only [Nat.nth_count hq] using hmono.monotone (Nat.succ_le_of_lt hn)
  · by_contra! hlt
    exact hgap _
      (by simpa only [Nat.nth_count hp] using hmono (Nat.lt_succ_self (Nat.count Nat.Prime p)))
      hlt (Nat.nth_mem _ (fun hf => (Nat.infinite_setOfPred_prime hf).elim))

/-- The long-prime-gap statement in the indexed form of `Challenge.lean`. -/
theorem long_prime_gaps :
    ∃ c X₀ : ℝ, 0 < c ∧ ∀ X : ℝ, X₀ ≤ X → ∃ n : ℕ,
      (Nat.nth Nat.Prime (n + 1) : ℝ) < X ∧
        c * (Real.log X * Real.log (Real.log X) ^ 2 *
          Real.log (Real.log (Real.log (Real.log X))) /
            Real.log (Real.log (Real.log X)) ^ 2) <
          (Nat.nth Nat.Prime (n + 1) : ℝ) - Nat.nth Nat.Prime n := by
  obtain ⟨c, hc, hgap⟩ := long_gap_theorem
  have hlog : Filter.Tendsto (fun X : ℝ => Real.log X / 8)
      Filter.atTop Filter.atTop :=
    Filter.Tendsto.atTop_div_const (by norm_num) Real.tendsto_log_atTop
  have heventually : ∀ᶠ X : ℝ in Filter.atTop, ∃ n : ℕ,
      (Nat.nth Nat.Prime (n + 1) : ℝ) < X ∧
        (c / 128) * gapScale X <
          (Nat.nth Nat.Prime (n + 1) : ℝ) - Nat.nth Nat.Prime n := by
    filter_upwards [(Real.tendsto_exp_atTop.comp hlog).eventually hgap,
      Real.tendsto_log_atTop.eventually eventually_coverScale_div_eight,
      Filter.eventually_gt_atTop (1 : ℝ)] with X hgap hscale hX
    obtain ⟨p, q, hpq, hq, hwidth⟩ := hgap
    obtain ⟨n, hn, hn'⟩ := consecutivePrimes_eq_nth hpq
    refine ⟨n, ?_, ?_⟩
    · rw [hn']
      apply hq.trans_lt
      calc
        Real.exp (Real.log X / 8) < Real.exp (Real.log X) := by
          apply Real.exp_lt_exp.mpr
          have := Real.log_pos hX
          linarith
        _ = X := Real.exp_log (by linarith)
    · rw [hn, hn', gapScale_eq_coverScale_log]
      rw [gapScale_eq_coverScale_log, Function.comp_apply, Real.log_exp,
        Nat.cast_sub hpq.2.2.1.le] at hwidth
      have hpositive : (0 : ℝ) < (q : ℝ) - p :=
        sub_pos.mpr (by exact_mod_cast hpq.2.2.1)
      have hbound := mul_le_mul_of_nonneg_left hscale hc.le
      nlinarith
  obtain ⟨X₀, hX₀⟩ := Filter.eventually_atTop.mp heventually
  exact ⟨c / 128, X₀, by positivity, hX₀⟩

#print axioms long_prime_gaps
-- 'LongGapsBetweenPrimes.long_prime_gaps' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end

end LongGapsBetweenPrimes
