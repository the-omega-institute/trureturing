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
  blocks mem_blocks log_bounds block_le_of_mem_cut quarter_phase progression_visits)

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

private theorem cutoff_bracket {T : ℝ} {n : ℕ} (hn : 6 ≤ n)
    (hlo : base n ≤ T) (hhi : T < base (n + 1)) :
    let r := prefixLength n T
    8 ≤ predecessor n r ∧ predecessor n r ≤ T ∧
      ∃ y : ℝ, T < y ∧ countMain y - countMain (predecessor n r) < 1 := by
  let r := prefixLength n T
  have hr : r ≤ blockSize n := prefix_le n T
  have hprev_le : predecessor n r ≤ T := by
    cases h : r with
    | zero =>
      rw [predecessor, ite_eq_left rfl]
      split_ifs with hseed
      · exact (base_strictMono.monotone hn).trans hlo
      · rw [grid_last, show n - 1 + 1 = n by omega]
        exact (sub_le_self _ (div_nonneg (by norm_num) (meshDenominator_pos _).le)).trans hlo
    | succ k =>
      rw [predecessor_succ]
      exact (grid_le_iff hlo (by omega)).2 (by omega)
  by_cases hfull : r = blockSize n
  · have hn' : 6 ≤ n + 1 := by omega
    obtain ⟨hprev, _, _, _⟩ := grid_gap hn' (blockSize_pos (n + 1))
    have hp := (step_countMain hn' (blockSize_pos (n + 1))).2
    rw [← predecessor_seam hn, ← hfull] at hprev hp
    exact ⟨hprev, hprev_le, gridRate (n + 1) 0,
      hhi.trans ((grid_in_block (⟨n + 1, ⟨0, blockSize_pos (n + 1)⟩⟩ : Index)).1), hp⟩
  · have hlt := lt_of_le_of_ne hr hfull
    obtain ⟨hprev, _, _, _⟩ := grid_gap hn hlt
    have hnext : T < gridRate n r := by
      by_contra! h
      exact (lt_irrefl r) ((grid_le_iff hlo hlt).1 h)
    exact ⟨hprev, hprev_le, gridRate n r, hnext, (step_countMain hn hlt).2⟩

private theorem count_error {T : ℝ} (hT : base 6 ≤ T) :
    |(spectrum.N T : ℝ) - countMain T| ≤
      |(↑(⌊countMain (base 6)⌋ : ℤ) : ℝ)| + 2 := by
  obtain ⟨n, hn, hlo, hhi⟩ := cutoff_block_scaled hT
  obtain ⟨hp, hpT, y, hy, hgap⟩ := cutoff_bracket hn hlo hhi
  have hT8 := hp.trans hpT
  have hlow := countMain_strictMonoOn.monotoneOn hp hT8 hpT
  have hhigh := countMain_strictMonoOn.monotoneOn hT8 (hT8.trans hy.le) hy.le
  have heq := congrArg (fun k : ℤ => (k : ℝ)) (inclusive_count hn hlo hhi)
  push_cast at heq
  rw [heq]
  have hflo := Int.floor_le (countMain (predecessor n (prefixLength n T)))
  have hfhi := Int.lt_floor_add_one (countMain (predecessor n (prefixLength n T)))
  have htest : |(⌊countMain (predecessor n (prefixLength n T))⌋ : ℤ) -
      countMain T| ≤ 2 := by
    apply abs_le.2
    constructor <;> linarith
  have htri := abs_add_le
    ((⌊countMain (predecessor n (prefixLength n T))⌋ : ℤ) - countMain T)
    (-(↑(⌊countMain (base 6)⌋ : ℤ) : ℝ))
  rw [abs_neg] at htri
  calc
    _ = |((⌊countMain (predecessor n (prefixLength n T))⌋ : ℤ) - countMain T) +
          (-(↑(⌊countMain (base 6)⌋ : ℤ) : ℝ))| := by congr 1; ring
    _ ≤ _ := htri.trans (by linarith)

private abbrev leadingCoefficient : ℝ := 1 / (2 * Real.pi)

private theorem coarse_count :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ T : ℝ, base 6 ≤ T →
      |(spectrum.N T : ℝ) - leadingCoefficient * T * Real.log T| ≤ D * T := by
  let D := |(↑(⌊countMain (base 6)⌋ : ℤ) : ℝ)| + 2
  let C := |leadingCoefficient * (Real.log (2 * Real.pi) + 1)|
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hC : 0 ≤ C := abs_nonneg _
  refine ⟨D + C, add_nonneg hD hC, fun T hT => ?_⟩
  have hT8 := seed_base.trans hT
  have hT0 : 0 < T := by linarith
  have hdiff :
      countMain T - leadingCoefficient * T * Real.log T =
        -(leadingCoefficient * (Real.log (2 * Real.pi) + 1)) * T := by
    unfold countMain
    rw [Real.log_div hT0.ne' (by positivity)]
    ring
  have hterm :
      |countMain T - leadingCoefficient * T * Real.log T| = C * T := by
    rw [hdiff, abs_mul, abs_neg, abs_of_pos hT0]
  calc
    _ ≤ |(spectrum.N T : ℝ) - countMain T| +
        |countMain T - leadingCoefficient * T * Real.log T| := abs_sub_le _ _ _
    _ ≤ D + C * T := by rw [hterm]; exact add_le_add_left (count_error hT) _
    _ ≤ (D + C) * T := by
      rw [add_mul]
      have hT1 : 1 ≤ T := by linarith
      exact add_le_add_left (le_mul_of_one_le_right hD hT1) (C * T)

private theorem count_asymptotic : OrdinateCounting.CountAsymptotic spectrum := by
  obtain ⟨D, hD, hcount⟩ := coarse_count
  have hzero : Tendsto (fun T : ℝ => D / Real.log T) atTop (nhds 0) := by
    simpa [div_eq_mul_inv, Function.comp_def] using
      (tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop).const_mul D
  have herr : Tendsto
      (fun T : ℝ => (spectrum.N T : ℝ) / (T * Real.log T) - leadingCoefficient)
      atTop (nhds 0) := by
    apply squeeze_zero_norm' _ hzero
    filter_upwards [eventually_ge_atTop (base 6)] with T hT
    have hT8 := seed_base.trans hT
    have hTpos : 0 < T := by linarith
    have hlog : 0 < Real.log T := Real.log_pos (by linarith)
    have hquot : (spectrum.N T : ℝ) / (T * Real.log T) - leadingCoefficient =
        ((spectrum.N T : ℝ) - leadingCoefficient * T * Real.log T) / (T * Real.log T) := by
      field_simp
    rw [Real.norm_eq_abs, hquot, abs_div, abs_of_pos (mul_pos hTpos hlog)]
    calc
      _ ≤ D * T / (T * Real.log T) :=
        div_le_div_of_nonneg_right (hcount T hT) (mul_nonneg hTpos.le hlog.le)
      _ = D / Real.log T := by field_simp
  simpa [OrdinateCounting.CountAsymptotic] using herr.add_const leadingCoefficient

private theorem eventually_positive_count : ∀ᶠ T : ℝ in atTop, 0 < spectrum.N T := by
  have hc : 0 < leadingCoefficient := by positivity
  have hc' : leadingCoefficient / 2 < leadingCoefficient := by linarith
  have hr := count_asymptotic.eventually (lt_mem_nhds hc')
  filter_upwards [hr, eventually_gt_atTop (1 : ℝ)] with T hratio hT
  have hratio' : 0 < (spectrum.N T : ℝ) / (T * Real.log T) :=
    (half_pos hc).trans hratio
  have hN : (0 : ℝ) < spectrum.N T :=
    by simpa only [zero_mul] using
      (lt_div_iff₀ (mul_pos (by linarith) (Real.log_pos hT))).1 hratio'
  exact_mod_cast hN

private theorem infinite_index : Infinite spectrum.index := by
  by_contra! hf
  let _ : Fintype spectrum.index := Fintype.ofFinite spectrum.index
  let K := Fintype.card spectrum.index
  have hbound (T : ℝ) : spectrum.N T ≤ K := by
    have hsum : spectrum.N T = ∑ _ ∈ spectrum.cut T, (1 : ℕ) := rfl
    rw [hsum, Finset.sum_const, nsmul_eq_mul, mul_one]
    exact Finset.card_le_univ _
  obtain ⟨D, hD, hcount⟩ := coarse_count
  have hc : 0 < leadingCoefficient := by positivity
  have hbig : ∀ᶠ T : ℝ in atTop, (K : ℝ) < T ∧ base 6 ≤ T ∧
      (D + 1) / leadingCoefficient ≤ Real.log T :=
    (eventually_gt_atTop (K : ℝ)).and ((eventually_ge_atTop (base 6)).and
      (Real.tendsto_log_atTop.eventually_ge_atTop _))
  obtain ⟨T, hTK, hTb, hlog⟩ := hbig.exists
  have hTc : 0 < T := by linarith [seed_base.trans hTb]
  have hprod := mul_le_mul_of_nonneg_right ((div_le_iff₀ hc).1 hlog) hTc.le
  have hcount' := (abs_le.1 (hcount T hTb)).1
  have hcard : (spectrum.N T : ℝ) ≤ K := by exact_mod_cast hbound T
  nlinarith only [hprod, hcount', hcard, hTK]

private def harmonicWeight (j : spectrum.index) : ℝ :=
  spectrum.gamma j / (1 / 4 + spectrum.gamma j ^ 2)

private theorem harmonicWeight_pos (j : spectrum.index) : 0 < harmonicWeight j :=
  div_pos (spectrum.gamma_pos j) (by positivity)

private theorem harmonicWeight_le_inv (j : spectrum.index) :
    harmonicWeight j ≤ 1 / spectrum.gamma j := by
  unfold harmonicWeight
  apply (div_le_div_iff₀ (by positivity) (spectrum.gamma_pos j)).2
  nlinarith

private theorem square_tail :
    SpectrumLogarithmicMissingWindow.HasLogarithmicSquareTail spectrum harmonicWeight := by
  classical
  obtain ⟨C, hC, htail⟩ := OrdinateCounting.inverse_square_tail spectrum count_asymptotic
  refine ⟨C + 1, by linarith, ?_⟩
  filter_upwards [eventually_ge_atTop (4 : ℝ)] with X hX
  intro T _
  letI : DecidableEq spectrum.index := fun a b => Classical.propDecidable (a = b)
  let S := spectrum.cut T \ spectrum.cut X
  have hXγ (j : spectrum.index) (hj : j ∈ S) : X < spectrum.gamma j :=
    lt_of_not_ge (fun h => (Finset.mem_sdiff.1 hj).2 (mem_cut.2 h))
  let embed : {j // j ∈ S} ↪ {j : spectrum.index // X < spectrum.gamma j} :=
    ⟨fun j => ⟨j.1, hXγ j.1 j.2⟩, by
      intro a b h
      exact Subtype.ext (congrArg (fun j : {j : spectrum.index // X < spectrum.gamma j} => j.1) h)⟩
  obtain ⟨hSum, hBound⟩ := htail X hX
  have hnonneg (j : {j : spectrum.index // X < spectrum.gamma j}) :
      0 ≤ (spectrum.mult j.val : ℝ) / spectrum.gamma j.val ^ 2 := by positivity
  have hfinite := hSum.sum_le_tsum (S.attach.map embed) (fun j _ => hnonneg j)
  rw [Finset.sum_map] at hfinite
  simp only [Nat.cast_one] at hfinite hBound
  change (∑ j ∈ S.attach, 1 / spectrum.gamma j.val ^ 2) ≤ _ at hfinite
  have hattach := Finset.sum_attach S (fun j => 1 / spectrum.gamma j ^ 2)
  rw [hattach] at hfinite
  calc
    _ ≤ ∑ j ∈ S, 1 / spectrum.gamma j ^ 2 := by
      change (∑ j ∈ S, harmonicWeight j ^ 2) ≤ _
      apply Finset.sum_le_sum
      intro j _
      rw [← one_pow 2, ← div_pow]
      exact pow_le_pow_left₀ (harmonicWeight_pos j).le (harmonicWeight_le_inv j) 2
    _ ≤ C * Real.log X / X := hfinite.trans hBound
    _ ≤ (C + 1) * Real.log X / X :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by linarith) (Real.log_nonneg (by linarith))) (by linarith)

private theorem retained_alignment {T : ℝ} {n : ℕ} (hi : T < base (n + 1)) (m : ℤ)
    {X : ℝ} (hXT : X ≤ T) :
    let q := 21 * denominator n
    sine spectrum harmonicWeight X
      (Real.pi * (q : ℝ) / 2 + (m : ℝ) * (2 * Real.pi * (q : ℝ))) =
      mass spectrum harmonicWeight X := by
  dsimp
  unfold sine mass
  apply Finset.sum_congr rfl
  intro j hj
  have hjX : gridRate j.1.1 j.1.2.val ≤ X := mem_cut.1 hj
  have hjT : j.1 ∈ raw.cut (21 * T) := mem_cut.2 (by
    change rate j.1 ≤ 21 * T
    linarith only [gridRate_eq j.1, hjX, hXT])
  have hbase : 21 * T < boundary (n + 1) := by
    linarith only [(lt_div_iff₀ (by norm_num : (0 : ℝ) < 21)).1 hi]
  obtain ⟨b, hb⟩ := quarter_phase (j := j.1) (block_le_of_mem_cut hbase hjT)
  have hq :
      spectrum.gamma j * ((21 * denominator n : ℕ) : ℝ) = 4 * (b : ℝ) + 1 := by
    change gridRate j.1.1 j.1.2.val * _ = _
    rw [gridRate_eq j.1]
    push_cast
    linear_combination hb
  let k := (b : ℤ) + m * (4 * (b : ℤ) + 1)
  have harg :
      spectrum.gamma j *
        (Real.pi * ((21 * denominator n : ℕ) : ℝ) / 2 +
          (m : ℝ) * (2 * Real.pi * ((21 * denominator n : ℕ) : ℝ))) =
      Real.pi / 2 + (k : ℝ) * (2 * Real.pi) := by
    calc
      _ = (spectrum.gamma j * ((21 * denominator n : ℕ) : ℝ)) *
          (Real.pi / 2 + (m : ℝ) * (2 * Real.pi)) := by ring
      _ = _ := by rw [hq]; simp [k]; ring
  rw [harg, Real.sin_add_int_mul_two_pi, Real.sin_pi_div_two, mul_one]

private theorem progression_bound {T : ℝ} {n : ℕ}
    (lo : base n ≤ T) (hi : T < base (n + 1)) :
    ((21 * denominator n : ℕ) : ℝ) + 1 ≤
      21 * (Real.log (21 * T) / Real.log 2) := by
  have hlo : boundary n ≤ 21 * T := by
    linarith only [(div_le_iff₀ (by norm_num : (0 : ℝ) < 21)).1 lo]
  have hhi : 21 * T < boundary (n + 1) := by
    linarith only [(lt_div_iff₀ (by norm_num : (0 : ℝ) < 21)).1 hi]
  have hl := (log_bounds hlo hhi).1
  have hsize : ((21 * denominator n : ℕ) : ℝ) ≤ 21 * ((n : ℝ) + 1) := by
    exact_mod_cast Nat.mul_le_mul_left 21 (denominator_bounds n).1
  linarith only [hl, hsize]

private theorem visits {T : ℝ} {n : ℕ}
    (hbound : ((21 * denominator n : ℕ) : ℝ) + 1 ≤
      21 * (Real.log (21 * T) / Real.log 2)) (A : ℝ) :
    let q := 21 * denominator n
    ∃ m : ℤ, Real.pi * (q : ℝ) / 2 + (m : ℝ) * (2 * Real.pi * (q : ℝ)) ∈
      Ioo A (A + (42 * Real.pi / Real.log 2) * Real.log (21 * T)) := by
  let q := 21 * denominator n
  have hq : 0 < q := Nat.mul_pos (by decide) (denominator_pos n)
  have hbound' : (q : ℝ) + 1 ≤ Real.log ((21 * T) ^ (21 : ℕ)) / Real.log 2 := by
    rw [Real.log_pow]
    push_cast
    convert hbound using 1
    ring
  obtain ⟨m, hm⟩ := progression_visits hq hbound' A
  refine ⟨m, ?_⟩
  have hlength : (2 * Real.pi / Real.log 2) * Real.log ((21 * T) ^ (21 : ℕ)) =
      (42 * Real.pi / Real.log 2) * Real.log (21 * T) := by
    rw [Real.log_pow]
    push_cast
    ring
  rw [hlength] at hm
  exact hm

open D5.S3.Analytic.Asymptotics.LogarithmicPhaseStiffness
  (realCutoff strictCount phaseMoment phaseWeight phaseCost momentErrorBound logarithmic_phase_stiffness)

private theorem finite_lt (T : ℝ) : {j : spectrum.index | spectrum.gamma j < T}.Finite :=
  (spectrum.finite_le T).subset (fun j hj =>
    show spectrum.gamma j ≤ T from (show spectrum.gamma j < T from hj).le)

private theorem mem_realCutoff {T : ℝ} {j : spectrum.index} :
    j ∈ realCutoff spectrum.gamma finite_lt T ↔ spectrum.gamma j < T :=
  (finite_lt T).mem_toFinset

private theorem strict_subset (T : ℝ) :
    realCutoff spectrum.gamma finite_lt T ⊆ spectrum.cut T :=
  fun _ hj => mem_cut.2 (mem_realCutoff.1 hj).le

private theorem boundary_card_le_one (T : ℝ) :
    ((spectrum.cut T) \ realCutoff spectrum.gamma finite_lt T).card ≤ 1 := by
  classical
  apply Finset.card_le_one_iff.2
  intro i j hi hj
  apply spectrum.gamma_injective
  have endpoint (k : spectrum.index) (hk : k ∈ spectrum.cut T \
      realCutoff spectrum.gamma finite_lt T) : spectrum.gamma k = T := by
    obtain ⟨hcut, hncut⟩ := Finset.mem_sdiff.1 hk
    exact (mem_cut.1 hcut).antisymm (le_of_not_gt (fun h => hncut (mem_realCutoff.2 h)))
  rw [endpoint i hi, endpoint j hj]

private theorem strict_count_error {T : ℝ} :
    |strictCount spectrum.gamma 1 finite_lt T - (spectrum.N T : ℝ)| ≤ 1 := by
  classical
  let s := realCutoff spectrum.gamma finite_lt T
  let u := spectrum.cut T
  have hN : spectrum.N T = u.card := by
    change (∑ _ ∈ u, (1 : ℕ)) = u.card
    simp
  have hS : strictCount spectrum.gamma 1 finite_lt T = s.card := by
    change (∑ _ ∈ s, (1 : ℝ)) = s.card
    simp
  have hsub := strict_subset T
  have hle : s.card ≤ u.card := Finset.card_le_card hsub
  have hdiff := (Finset.card_sdiff_of_subset hsub)
  have hh := boundary_card_le_one T
  change (u \ s).card ≤ 1 at hh
  rw [hdiff] at hh
  rw [hS, hN, abs_of_nonpos (sub_nonpos.mpr (by exact_mod_cast hle))]
  have hz : (u.card : ℝ) - s.card ≤ 1 := by
    rw [← Nat.cast_sub hle]
    exact_mod_cast hh
  linarith

private theorem harmonicMoment_error {T : ℝ} (hT : base 6 ≤ T) :
    |mass spectrum harmonicWeight T - phaseMoment spectrum.gamma 1 finite_lt T| ≤ 1 := by
  classical
  let s := realCutoff spectrum.gamma finite_lt T
  let u := spectrum.cut T
  have hsub := strict_subset T
  have hident : phaseMoment spectrum.gamma 1 finite_lt T = ∑ j ∈ s, harmonicWeight j := by
    unfold phaseMoment
    apply Finset.sum_congr rfl
    intro j _
    have hγ := (spectrum.gamma_pos j).ne'
    simp only [phaseWeight, Pi.one_apply, harmonicWeight]
    field_simp
  have hsplit : mass spectrum harmonicWeight T - phaseMoment spectrum.gamma 1 finite_lt T =
      ∑ j ∈ u \ s, harmonicWeight j := by
    rw [hident]
    unfold mass
    have h := Finset.sum_sdiff (f := harmonicWeight) hsub
    linarith only [h]
  rw [hsplit, abs_of_nonneg (Finset.sum_nonneg (fun j _ => (harmonicWeight_pos j).le))]
  have hper (j : spectrum.index) (hj : j ∈ u \ s) : harmonicWeight j ≤ 1 := by
    have hjn := (Finset.mem_sdiff.1 hj).2
    have hjT : T ≤ spectrum.gamma j := le_of_not_gt (fun h => hjn (mem_realCutoff.2 h))
    exact (harmonicWeight_le_inv j).trans
      ((div_le_one₀ (spectrum.gamma_pos j)).2 (by linarith [seed_base.trans hT]))
  calc
    _ ≤ ∑ _ ∈ u \ s, (1 : ℝ) := Finset.sum_le_sum hper
    _ ≤ 1 := by
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
      exact_mod_cast boundary_card_le_one T

private theorem log_squared_mass :
    SpectrumCriticalMissingWindow.HasLogSquaredMass spectrum harmonicWeight := by
  obtain ⟨D, hD, hDcount⟩ := coarse_count
  let c := leadingCoefficient
  let C := D + 1
  let L := base 6
  have hc : 0 < c := by dsimp [c]; positivity
  have hC : 0 ≤ C := by dsimp [C]; linarith
  have hL8 : 8 ≤ L := seed_base
  have hL : 1 < L := by linarith
  have hγ (j : spectrum.index) : L ≤ spectrum.gamma j :=
    (base_strictMono.monotone j.2.1).trans
      (grid_in_block j.1).1.le
  have hcount (u : ℝ) (hu : L ≤ u) :
      |strictCount spectrum.gamma 1 finite_lt u - c * u * Real.log u| ≤ C * u := by
    exact (abs_sub_le _ (spectrum.N u : ℝ) _).trans (by
      have h₁ := strict_count_error (T := u)
      have h₂ := hDcount u hu
      dsimp [c, C]
      nlinarith only [h₁, h₂, show 1 ≤ u by linarith [hL8.trans hu]])
  have ha := logarithmic_phase_stiffness spectrum.gamma (fun _ => 1) finite_lt hL hγ
    (fun _ => zero_le_one) hc.le hcount
  let M := ∑' j, phaseWeight spectrum.gamma 1 j
  let E := 16 * c + 19 * C + c / 2 * (Real.log L) ^ 2 - C * Real.log L + M / 4
  let slope := 19 * c + C
  have hslope : 0 ≤ slope := by dsimp [slope]; positivity
  refine ⟨c / 2, 1 + |E| + slope, by positivity, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop L] with T hT
  have hT8 := hL8.trans hT
  have hTpos : 0 < T := by linarith
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  let t := T⁻¹
  have ht : 0 < t := inv_pos.mpr hTpos
  have htL : L * |t| ≤ 1 := by
    rw [abs_of_pos ht]
    change L * T⁻¹ ≤ 1
    rw [← div_eq_mul_inv, div_le_one₀ hTpos]
    exact hT
  have htinv : |t|⁻¹ = T := by rw [abs_of_pos ht]; simp [t]
  have hA := ha.2.2.2.2 t (abs_pos.mpr ht.ne') htL
  have h₁ := hA.1
  have h₂ := hA.2.2.1
  dsimp only at h₁ h₂
  rw [htinv] at h₁ h₂
  let P := phaseMoment spectrum.gamma 1 finite_lt T
  let Q := c / 2 * (Real.log T) ^ 2
  let V := phaseCost spectrum.gamma (phaseWeight spectrum.gamma 1) t
  have hterm : c / 2 * t ^ 2 * (Real.log T) ^ 2 = t ^ 2 * Q := by dsimp [Q]; ring
  have h₂' : |V - t ^ 2 * Q| ≤ t ^ 2 *
      (9 * c * Real.log T + 8 * c + 9 * C + momentErrorBound L T c C M) := by
    rw [← hterm]
    exact h₂
  have h₁' : |t ^ 2 * P - V| ≤ t ^ 2 * (9 * c * Real.log T + 8 * c + 9 * C) := by
    rw [abs_sub_comm]
    exact h₁
  have htri := (abs_sub_le (t ^ 2 * P) V (t ^ 2 * Q)).trans (add_le_add h₁' h₂')
  rw [← mul_sub, abs_mul, abs_of_nonneg (sq_nonneg t), ← mul_add] at htri
  have hmoment := le_of_mul_le_mul_left htri (sq_pos_of_pos ht)
  have hbnd : |P - Q| ≤ slope * Real.log T + E := by
    refine hmoment.trans_eq ?_
    unfold momentErrorBound slope E
    ring
  calc
    _ ≤ |mass spectrum harmonicWeight T - P| + |P - Q| := abs_sub_le _ _ _
    _ ≤ 1 + (slope * Real.log T + E) := add_le_add (harmonicMoment_error hT) hbnd
    _ ≤ _ := by
      have hE := le_abs_self E
      nlinarith [mul_nonneg (add_nonneg (show 0 ≤ (1 : ℝ) by norm_num) (abs_nonneg E)) hlogT]

/-- The two-term count can coexist with harmonic weights and frequent simultaneous alignment. -/
theorem exists_two_term_count_alignment :
    ∃ (S : Spectrum) (w : S.index → ℝ), Infinite S.index ∧
      (∀ j, S.mult j = 1 ∧ w j = S.gamma j / (1 / 4 + S.gamma j ^ 2)) ∧
      (∃ D : ℝ, 0 ≤ D ∧ ∀ᶠ T : ℝ in atTop,
        |(S.N T : ℝ) -
          T / (2 * Real.pi) * (Real.log (T / (2 * Real.pi)) - 1)| ≤ D) ∧
      SpectrumCriticalMissingWindow.HasLogSquaredMass S w ∧
      SpectrumLogarithmicMissingWindow.HasLogarithmicSquareTail S w ∧
      ∀ᶠ T : ℝ in atTop, 0 < mass S w T ∧
        ∃ q : ℕ, 0 < q ∧ (q : ℝ) + 1 ≤ 21 * (Real.log (21 * T) / Real.log 2) ∧
          (∀ (m : ℤ) (X : ℝ), X ≤ T →
            sine S w X (Real.pi * (q : ℝ) / 2 + (m : ℝ) * (2 * Real.pi * (q : ℝ))) =
              mass S w X) ∧
          ∀ A : ℝ, ∃ m : ℤ, Real.pi * (q : ℝ) / 2 + (m : ℝ) * (2 * Real.pi * (q : ℝ)) ∈
            Ioo A (A + (42 * Real.pi / Real.log 2) * Real.log (21 * T)) := by
  refine ⟨spectrum, harmonicWeight, infinite_index, fun _ => ⟨rfl, rfl⟩,
    ?_, log_squared_mass, square_tail, ?_⟩
  · refine ⟨|(↑(⌊countMain (base 6)⌋ : ℤ) : ℝ)| + 2, by positivity, ?_⟩
    filter_upwards [eventually_ge_atTop (base 6)] with T hT
    exact count_error hT
  · filter_upwards [eventually_positive_count, eventually_ge_atTop (base 6)] with T hN hT
    obtain ⟨n, _, hlo, hhi⟩ := cutoff_block_scaled hT
    have hnonempty : (spectrum.cut T).Nonempty := by
      by_contra! h
      simp [Spectrum.N, h] at hN
    have hmass : 0 < mass spectrum harmonicWeight T :=
      Finset.sum_pos (fun j _ => harmonicWeight_pos j) hnonempty
    have hbound := progression_bound hlo hhi
    exact ⟨hmass, 21 * denominator n, Nat.mul_pos (by decide) (denominator_pos n),
      hbound, fun m X hXT => retained_alignment hhi m hXT, visits hbound⟩

#print axioms exists_two_term_count_alignment

end D5.S3.Analytic.Oscillation.SpectrumTwoTermCountAlignment
