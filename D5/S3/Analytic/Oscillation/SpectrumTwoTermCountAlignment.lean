/- GID: D5/S3/Analytic/Oscillation/SpectrumTwoTermCountAlignment
   generality: G
   mirror-B: D5/B/S3/Analytic/Oscillation/SpectrumTwoTermCountAlignment
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Thinning a commensurate spectrum gives bounded two-term count discrepancy. -/

import D5.S3.Analytic.Oscillation.SpectrumCommensurateAlignment
import Mathlib.Analysis.Real.Pi.Bounds

/-! An inclusive zero-count comparison spectrum obtained by floor increments. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter Set
open scoped Topology BigOperators

namespace D5.S3.Analytic.Oscillation.SpectrumTwoTermCountAlignment

open OrdinateCounting (Spectrum)
open SpectrumPhaseCutoff (mass sine mem_cut)
open SpectrumCommensurateAlignment (Index boundary blockSize rate denominator denominator_pos
  blockSize_pos denominator_bounds boundary_succ boundary_strictMono rate_in_block cutoff_block
  lower_blocks blocks mem_blocks sum_blocks log_bounds block_le_of_mem_cut quarter_phase progression_visits)

private abbrev raw := SpectrumCommensurateAlignment.spectrum

private def base (n : ℕ) : ℝ := boundary n / 21

private def meshDenominator (n : ℕ) : ℝ := 21 * (denominator n : ℝ)

private theorem meshDenominator_pos (n : ℕ) : 0 < meshDenominator n := by
  have : (0 : ℝ) < (denominator n : ℝ) := by exact_mod_cast denominator_pos n
  unfold meshDenominator
  positivity

private def gridRate (n k : ℕ) : ℝ := base n + (4 * (k : ℝ) + 1) / meshDenominator n

private theorem gridRate_eq (j : Index) : gridRate j.1 j.2.val = rate j / 21 := by
  unfold gridRate base meshDenominator rate
  ring

private def countMain (t : ℝ) : ℝ :=
  t / (2 * Real.pi) * (Real.log (t / (2 * Real.pi)) - 1)

private theorem countMain_deriv {t : ℝ} (ht : 0 < t) :
    HasDerivAt countMain (Real.log (t / (2 * Real.pi)) / (2 * Real.pi)) t := by
  let a : ℝ := 2 * Real.pi
  have ha : 0 < a := by dsimp [a]; positivity
  have hscale := (hasDerivAt_id t).div_const a
  have hlog := hscale.log (div_pos ht ha).ne'
  have hprod := hscale.mul (hlog.sub_const 1)
  change HasDerivAt countMain (Real.log (t / a) / a) t
  convert hprod using 1
  · rfl
  · simp only [id_eq]
    field_simp
    ring

private theorem base_strictMono : StrictMono base := by
  intro n m h
  exact div_lt_div_of_pos_right (boundary_strictMono h) (by norm_num)

private theorem seed_base : 8 ≤ base 6 := by norm_num [base, boundary]

private theorem grid_in_block (j : Index) :
    base j.1 < gridRate j.1 j.2.val ∧ gridRate j.1 j.2.val < base (j.1 + 1) := by
  rw [gridRate_eq]
  exact ⟨div_lt_div_of_pos_right (rate_in_block j).1 (by norm_num),
    div_lt_div_of_pos_right (rate_in_block j).2 (by norm_num)⟩

private theorem blockSize_cast (n : ℕ) :
    (blockSize n : ℝ) = (denominator n : ℝ) * 2 ^ n := by simp [blockSize]

private theorem grid_last (n : ℕ) :
    gridRate n (blockSize n - 1) = base (n + 1) - 3 / meshDenominator n := by
  have hq : (0 : ℝ) < (denominator n : ℝ) := by exact_mod_cast denominator_pos n
  rw [gridRate, Nat.cast_sub (blockSize_pos n), Nat.cast_one, blockSize_cast]
  unfold base meshDenominator
  rw [boundary_succ]
  unfold boundary
  field_simp
  ring

private theorem mesh_mono : Monotone meshDenominator := by
  intro n m h
  have hq : denominator n ≤ denominator m := by
    change 5 ^ Nat.log 5 (n + 1) ≤ 5 ^ Nat.log 5 (m + 1)
    exact Nat.pow_le_pow_right (by decide) (Nat.log_mono_right (by omega))
  unfold meshDenominator
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast hq) (by norm_num)

private def predecessor (n k : ℕ) : ℝ :=
  if k = 0 then
    if n ≤ 6 then base 6 else gridRate (n - 1) (blockSize (n - 1) - 1)
  else gridRate n (k - 1)

private theorem grid_gap {n k : ℕ} (hn : 6 ≤ n) (hk : k < blockSize n) :
    8 ≤ predecessor n k ∧ predecessor n k < gridRate n k ∧
      gridRate n k ≤ boundary (n + 1) ∧
      gridRate n k - predecessor n k ≤ 4 / meshDenominator (n - 1) := by
  have hq := meshDenominator_pos n
  have hqprev := meshDenominator_pos (n - 1)
  have hmono := mesh_mono (Nat.sub_le n 1)
  have hFourth : (4 : ℝ) / meshDenominator n ≤ 4 / meshDenominator (n - 1) :=
    div_le_div_of_nonneg_left (by norm_num) hqprev hmono
  have htop := (grid_in_block (⟨n, ⟨k, hk⟩⟩ : Index)).2.le
  have hbound : gridRate n k ≤ boundary (n + 1) :=
    htop.trans (div_le_self (by unfold boundary; positivity) (by norm_num))
  refine ⟨?_, ?_, hbound, ?_⟩
  · by_cases h : k = 0
    · rw [predecessor, ite_eq_left h]
      split_ifs with hseed
      · exact seed_base
      · have hn' : 6 ≤ n - 1 := by omega
        exact seed_base.trans ((base_strictMono.monotone hn').trans
          (grid_in_block (⟨n - 1, ⟨blockSize (n - 1) - 1, by
            have := blockSize_pos (n - 1)
            omega⟩⟩ : Index)).1.le)
    · rw [predecessor, ite_eq_right h]
      exact seed_base.trans ((base_strictMono.monotone hn).trans
        (grid_in_block (⟨n, ⟨k - 1, by omega⟩⟩ : Index)).1.le)
  · by_cases h : k = 0
    · subst k
      rw [predecessor, ite_eq_left rfl]
      split_ifs with hseed
      · have hsame : n = 6 := by omega
        subst n
        exact (grid_in_block (⟨6, ⟨0, hk⟩⟩ : Index)).1
      · rw [grid_last, show n - 1 + 1 = n by omega]
        unfold gridRate
        have hm := meshDenominator_pos (n - 1)
        have hx : 0 < 3 / meshDenominator (n - 1) := by positivity
        have hy : 0 < (4 * (0 : ℝ) + 1) / meshDenominator n := by positivity
        linarith
    · rw [predecessor, ite_eq_right h, gridRate, gridRate, Nat.cast_sub (by omega : 1 ≤ k)]
      rw [Nat.cast_one]
      apply add_lt_add_right
      apply div_lt_div_of_pos_right _ hq
      linarith
  · by_cases h : k = 0
    · subst k
      rw [predecessor, ite_eq_left rfl]
      split_ifs with hseed
      · have hsame : n = 6 := by omega
        subst n
        simp only [gridRate, Nat.cast_zero, mul_zero, zero_add, add_sub_cancel_left]
        exact (div_le_div_of_nonneg_right (by norm_num : (1 : ℝ) ≤ 4) hq.le).trans hFourth
      · rw [grid_last, show n - 1 + 1 = n by omega]
        unfold gridRate
        simp only [Nat.cast_zero, mul_zero, zero_add]
        have hfirst : (1 : ℝ) / meshDenominator n ≤ 1 / meshDenominator (n - 1) :=
          div_le_div_of_nonneg_left (by norm_num) hqprev hmono
        calc
          _ = 1 / meshDenominator n + 3 / meshDenominator (n - 1) := by ring
          _ ≤ 1 / meshDenominator (n - 1) + 3 / meshDenominator (n - 1) :=
            add_le_add_left hfirst _
          _ = _ := by ring
    · rw [predecessor, ite_eq_right h, gridRate, gridRate, Nat.cast_sub (by omega : 1 ≤ k)]
      rw [Nat.cast_one]
      calc
        _ = 4 / meshDenominator n := by ring
        _ ≤ _ := hFourth

private theorem countMain_diff {x y : ℝ} (hx : 8 ≤ x) (hxy : x < y) :
    ∃ v ∈ Ioo x y, countMain y - countMain x =
      (Real.log (v / (2 * Real.pi)) / (2 * Real.pi)) * (y - x) := by
  obtain ⟨v, hv, heq⟩ := exists_hasDerivAt_eq_slope countMain
    (fun v => Real.log (v / (2 * Real.pi)) / (2 * Real.pi)) hxy
    (fun t ht => (countMain_deriv (by linarith [ht.1])).continuousAt.continuousWithinAt)
    (fun t ht => countMain_deriv (by linarith [ht.1]))
  exact ⟨v, hv, ((eq_div_iff (sub_ne_zero.mpr hxy.ne')).1 heq).symm⟩

private theorem countMain_strictMonoOn : StrictMonoOn countMain (Ici 8) := by
  intro x hx y _ hxy
  have hx' : (8 : ℝ) ≤ x := hx
  obtain ⟨v, hv, heq⟩ := countMain_diff hx' hxy
  have hπ := Real.pi_pos
  have hlog : 0 < Real.log (v / (2 * Real.pi)) := by
    apply Real.log_pos
    exact (lt_div_iff₀ (by positivity)).2 (by linarith [Real.pi_lt_four, hv.1, hx'])
  have h := mul_pos (div_pos hlog (by positivity : 0 < 2 * Real.pi)) (sub_pos.mpr hxy)
  rw [← heq] at h
  exact sub_pos.mp h

private theorem step_countMain {n k : ℕ} (hn : 6 ≤ n) (hk : k < blockSize n) :
    0 < countMain (gridRate n k) - countMain (predecessor n k) ∧
      countMain (gridRate n k) - countMain (predecessor n k) < 1 := by
  obtain ⟨hprev, hstep, htop, hwidth⟩ := grid_gap hn hk
  obtain ⟨v, hv, heq⟩ := countMain_diff hprev hstep
  have hnR : (6 : ℝ) ≤ n := by exact_mod_cast hn
  have ha : 0 < 2 * Real.pi := by positivity
  have hπ : (6 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  have hvpos : 0 < v := by linarith [hv.1]
  have hlogpos : 0 < Real.log (v / (2 * Real.pi)) := by
    apply Real.log_pos
    exact (lt_div_iff₀ ha).2 (by linarith [Real.pi_lt_four, hv.1])
  have hloga : Real.log (v / (2 * Real.pi)) ≤ Real.log v :=
    Real.log_le_log (div_pos hvpos ha) (div_le_self hvpos.le (by linarith))
  have hlogtop := Real.log_le_log hvpos (hv.2.le.trans htop)
  have hlogB : Real.log (boundary (n + 1)) = ((n : ℝ) + 3) * Real.log 2 := by
    unfold boundary
    rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) (by positivity : (2 : ℝ) ^ (n + 1) ≠ 0),
      Real.log_pow, show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
    push_cast
    ring
  have hlog2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    linarith
  have hlog : Real.log (v / (2 * Real.pi)) ≤ (n : ℝ) + 3 := by
    rw [hlogB] at hlogtop
    exact (hloga.trans hlogtop).trans
      (mul_le_of_le_one_right (by positivity) hlog2)
  have hderiv : Real.log (v / (2 * Real.pi)) / (2 * Real.pi) ≤ ((n : ℝ) + 3) / 6 :=
    (div_le_div_of_nonneg_left hlogpos.le (by norm_num) hπ).trans
      (div_le_div_of_nonneg_right hlog (by norm_num))
  have hnq : (n : ℝ) < 5 * (denominator (n - 1) : ℝ) := by
    have h := (denominator_bounds (n - 1)).2
    rw [show n - 1 + 1 = n by omega] at h
    exact_mod_cast h
  have hden : 4 * (((n : ℝ) + 3) / 6) < meshDenominator (n - 1) := by
    unfold meshDenominator
    linarith
  rw [heq]
  refine ⟨mul_pos (div_pos hlogpos ha) (sub_pos.mpr hstep), ?_⟩
  calc
    _ ≤ (((n : ℝ) + 3) / 6) * (4 / meshDenominator (n - 1)) :=
      mul_le_mul hderiv hwidth (sub_nonneg.mpr hstep.le) (by positivity)
    _ = (4 * (((n : ℝ) + 3) / 6)) / meshDenominator (n - 1) := by ring
    _ < 1 := (div_lt_one₀ (meshDenominator_pos (n - 1))).2 hden

private def increment (n k : ℕ) : ℤ :=
  ⌊countMain (gridRate n k)⌋ - ⌊countMain (predecessor n k)⌋

private theorem increment_in {n k : ℕ} (hn : 6 ≤ n) (hk : k < blockSize n) :
    increment n k = 0 ∨ increment n k = 1 := by
  obtain ⟨hinc, hspan⟩ := step_countMain hn hk
  have hmono := Int.floor_mono (sub_pos.mp hinc).le
  have hhigh : ⌊countMain (gridRate n k)⌋ < ⌊countMain (predecessor n k)⌋ + 2 := by
    apply Int.floor_lt.mpr
    push_cast
    linarith [Int.lt_floor_add_one (countMain (predecessor n k))]
  unfold increment
  omega

private abbrev Retained := {j : Index // 6 ≤ j.1 ∧ increment j.1 j.2.val = 1}

private abbrev spectrum : Spectrum where
  index := Retained
  gamma j := gridRate j.1.1 j.1.2.val
  mult := fun _ => 1
  gamma_pos j := by
    rw [gridRate_eq]
    exact div_pos (raw.gamma_pos j.1) (by norm_num)
  gamma_injective := by
    intro i j h
    apply Subtype.ext
    apply raw.gamma_injective
    change rate i.1 = rate j.1
    change gridRate i.1.1 i.1.2.val = gridRate j.1.1 j.1.2.val at h
    linarith only [h, gridRate_eq i.1, gridRate_eq j.1]
  mult_pos := fun _ => Nat.one_pos
  finite_le T := by
    refine ((raw.finite_le (21 * T)).preimage Subtype.val_injective.injOn).subset ?_
    intro j hj
    change rate j.1 ≤ 21 * T
    change gridRate j.1.1 j.1.2.val ≤ T at hj
    linarith only [hj, gridRate_eq j.1]

private theorem cutoff_block_scaled {T : ℝ} (hT : base 6 ≤ T) :
    ∃ n : ℕ, 6 ≤ n ∧ base n ≤ T ∧ T < base (n + 1) := by
  have hseed : 4 ≤ 21 * T := by linarith [seed_base.trans hT]
  obtain ⟨n, hlo, hhi⟩ := cutoff_block hseed
  have hl : base n ≤ T := (div_le_iff₀ (by norm_num)).2 (by linarith)
  have hu : T < base (n + 1) := (lt_div_iff₀ (by norm_num)).2 (by linarith)
  refine ⟨n, ?_, hl, hu⟩
  by_contra! hn
  exact hu.not_ge ((base_strictMono.monotone (Nat.succ_le_of_lt hn)).trans hT)

private theorem predecessor_succ (n k : ℕ) :
    predecessor n (k + 1) = gridRate n k := by
  simp [predecessor]

private theorem predecessor_seam {n : ℕ} (hn : 6 ≤ n) :
    predecessor n (blockSize n) = predecessor (n + 1) 0 := by
  simp [predecessor, (blockSize_pos n).ne', show ¬ n + 1 ≤ 6 by omega]

private theorem sum_increments (n r : ℕ) :
    ∑ k ∈ Finset.range r, increment n k =
      ⌊countMain (predecessor n r)⌋ - ⌊countMain (predecessor n 0)⌋ := by
  simp_rw [increment, ← predecessor_succ]
  exact Finset.sum_range_sub (fun k => ⌊countMain (predecessor n k)⌋) r

private theorem sum_complete_blocks {n : ℕ} (hn : 6 ≤ n) :
    ∑ j ∈ Finset.Ico 6 n, ∑ k ∈ Finset.range (blockSize j), increment j k =
      ⌊countMain (predecessor n 0)⌋ - ⌊countMain (base 6)⌋ := by
  induction n, hn using Nat.le_induction with
  | base => simp [predecessor]
  | succ n hn ih =>
    rw [Finset.sum_Ico_succ_top hn, ih, sum_increments, predecessor_seam hn]
    ring

private def prefixLength (n : ℕ) (T : ℝ) : ℕ :=
  min (blockSize n) ⌊(meshDenominator n * (T - base n) + 3) / 4⌋₊

private theorem prefix_le (n : ℕ) (T : ℝ) : prefixLength n T ≤ blockSize n :=
  min_le_left _ _

private theorem grid_le_iff {n k : ℕ} {T : ℝ} (hT : base n ≤ T) (hk : k < blockSize n) :
    gridRate n k ≤ T ↔ k < prefixLength n T := by
  have hq := meshDenominator_pos n
  have hnonneg : 0 ≤ (meshDenominator n * (T - base n) + 3) / 4 := by positivity
  rw [prefixLength, lt_min_iff, and_iff_right hk, ← Nat.succ_le_iff,
    Nat.le_floor_iff hnonneg, Nat.cast_succ, gridRate,
    add_comm (base n), ← le_sub_iff_add_le, div_le_iff₀ hq, le_div_iff₀ (by norm_num : (0 : ℝ) < 4)]
  rw [mul_comm (T - base n) (meshDenominator n)]
  constructor <;> intro h <;> linarith

private theorem mem_cut_map {T : ℝ} {n : ℕ} (hT : T < base (n + 1))
    (j : Index) :
    j ∈ (spectrum.cut T).map ⟨Subtype.val, Subtype.val_injective⟩ ↔
      j ∈ (blocks (Finset.Icc 6 n)).filter
        (fun k => increment k.1 k.2.val = 1 ∧ gridRate k.1 k.2.val ≤ T) := by
  classical
  rw [Finset.mem_map, Finset.mem_filter, mem_blocks, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨j, hj⟩, hjT, rfl⟩
    have hjT' : gridRate j.1 j.2.val ≤ T := mem_cut.1 hjT
    have hcut : j ∈ raw.cut (21 * T) := mem_cut.2 (by
      change rate j ≤ 21 * T
      linarith only [gridRate_eq j, hjT'])
    have hbase : 21 * T < boundary (n + 1) := by
      have hh := (lt_div_iff₀ (by norm_num : (0 : ℝ) < 21)).1 hT
      linarith only [hh]
    exact ⟨⟨hj.1, block_le_of_mem_cut hbase hcut⟩, hj.2, hjT'⟩
  · rintro ⟨hj, hi, hjT⟩
    exact ⟨⟨j, hj.1, hi⟩, mem_cut.2 hjT, rfl⟩

private theorem inclusive_count {T : ℝ} {n : ℕ} (hn : 6 ≤ n)
    (hlo : base n ≤ T) (hhi : T < base (n + 1)) :
    (spectrum.N T : ℤ) =
      ⌊countMain (predecessor n (prefixLength n T))⌋ - ⌊countMain (base 6)⌋ := by
  classical
  let A := blocks (Finset.Icc 6 n)
  have hmap : (spectrum.cut T).map ⟨Subtype.val, Subtype.val_injective⟩ =
      A.filter (fun j => increment j.1 j.2.val = 1 ∧ gridRate j.1 j.2.val ≤ T) := by
    ext j
    exact mem_cut_map hhi j
  have hcount : (spectrum.N T : ℤ) =
      ∑ j ∈ A, if gridRate j.1 j.2.val ≤ T then increment j.1 j.2.val else 0 := by
    have hNat : spectrum.N T = ∑ _ ∈ spectrum.cut T, (1 : ℕ) := rfl
    rw [hNat, Nat.cast_sum]
    simp only [Nat.cast_one]
    rw [← Finset.sum_map (spectrum.cut T) ⟨Subtype.val, Subtype.val_injective⟩ (fun _ => (1 : ℤ)),
      hmap, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro j hj
    have hjn : 6 ≤ j.1 := (Finset.mem_Icc.1 (mem_blocks.1 hj)).1
    rcases increment_in hjn j.2.isLt with hi | hi <;> simp [hi]
  rw [hcount]
  change (∑ j ∈ blocks (Finset.Icc 6 n),
    if gridRate j.1 j.2.val ≤ T then increment j.1 j.2.val else 0) = _
  have hIcc : Finset.Icc 6 n = Finset.Ico 6 (n + 1) := by
    ext j
    simp only [Finset.mem_Icc, Finset.mem_Ico, Nat.lt_succ_iff]
  unfold blocks
  rw [Finset.sum_sigma, hIcc, Finset.sum_Ico_succ_top hn]
  have hcomplete : (∑ j ∈ Finset.Ico 6 n,
      ∑ k : Fin (blockSize j), if gridRate j k.val ≤ T then increment j k.val else 0) =
      ∑ j ∈ Finset.Ico 6 n, ∑ k ∈ Finset.range (blockSize j), increment j k := by
    apply Finset.sum_congr rfl
    intro j hj
    have hjn := (Finset.mem_Ico.1 hj).2
    calc
      _ = ∑ k : Fin (blockSize j), increment j k.val := by
        apply Finset.sum_congr rfl
        intro k _
        exact ite_eq_left ((grid_in_block (⟨j, k⟩ : Index)).2.le.trans
          ((base_strictMono.monotone (Nat.succ_le_of_lt hjn)).trans hlo))
      _ = _ := Fin.sum_univ_eq_sum_range (increment j) (blockSize j)
  have hpartial : (∑ k : Fin (blockSize n),
      if gridRate n k.val ≤ T then increment n k.val else 0) =
      ∑ k ∈ Finset.range (prefixLength n T), increment n k := by
    rw [Fin.sum_univ_eq_sum_range (fun k : ℕ =>
      if gridRate n k ≤ T then increment n k else 0), ← Finset.sum_filter]
    congr 1
    ext k
    rw [Finset.mem_filter, Finset.mem_range, Finset.mem_range]
    constructor
    · rintro ⟨hk, hout⟩
      exact (grid_le_iff hlo hk).1 hout
    · intro hk
      have hk' := hk.trans_le (prefix_le n T)
      exact ⟨hk', (grid_le_iff hlo hk').2 hk⟩
  rw [hcomplete, hpartial, sum_complete_blocks hn, sum_increments]
  ring

end D5.S3.Analytic.Oscillation.SpectrumTwoTermCountAlignment
