/- GID: D5/S3/Observer/MetricGeometry/QuadraticSixPositionRisk
   generality: I
   mirror-B: D5/B/S3/Observer/MetricGeometry/QuadraticSixPositionRisk
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Six quadratic reports have an exact joint-noise risk and finite deletion certificates. -/

import D5.S3.Observer.MetricGeometry.QuadraticRawReportRecovery
import Mathlib.Tactic

/-! Exact joint strip geometry of the original six sampling positions. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set
open scoped ENNReal
open D5.S3.Observer.MetricGeometry.QuadraticRawReportRecovery

namespace D5.S3.Observer.MetricGeometry.QuadraticSixPositionRisk

/-- All six original report positions. -/
def full : Design := positions.attach

/-- The untruncated six-position diameter as a function of normalized noise and width. -/
def envelope (c K : ℝ) : ℝ :=
  max (c / 10) (max (c * (K + 9) / (90 + 2 * c))
    (max (c * (K + 7) / (72 + 2 * c)) (c * K / (16 + 2 * c))))

/-- A slope whose joint strip remains legal when this original position is deleted. -/
def deletionSlope (p : Index) : ℝ :=
  if p.val = 0 then 11 else if p.val = 1 then 2 else
    if p.val = 2 then 9 else if p.val = 8 then 11 else if p.val = 9 then 18 else 9

/-- The range of that slope's quadratic on the remaining original coordinates. -/
def deletionRange (p : Index) : ℝ :=
  if p.val = 1 ∨ p.val = 9 then 80 else if p.val = 2 ∨ p.val = 8 then 18 else 14

private lemma strips_neg (ε : ℝ) (J : Design) (U V : ℝ)
    (h : Strips ε J U V) : Strips ε J (-U) (-V) := by
  intro i hi j hj
  have hh := h j hj i hi
  nlinarith only [hh]

private lemma finite_pair (m ε H s U V d : ℝ) (J : Design)
    (hU : 0 ≤ U) (hd : 0 < d) (hdH : d ≤ H)
    (hstrip : Strips ε J U V)
    (hbound : 2 * (m + U) * d ≤ H * U + |s * U - (10 * U + V)|) :
    ∃ u v : ℝ, u ∈ prior H s ∧ v ∈ prior H s ∧
      PairCompatible m ε J u v ∧ v - u = d := by
  let a := -5 + (s - H) / 2
  let b := -5 + (s + H) / 2
  by_cases hz : 0 ≤ s * U - (10 * U + V)
  · rw [abs_of_nonneg hz] at hbound
    let A' := (2 * U * (b - d) - V) / (2 * d)
    have hA' : m ≤ A' := by
      apply (le_div_iff₀ (by positivity : 0 < 2 * d)).2
      dsimp [b] at *
      nlinarith only [hbound]
    have hA : m ≤ A' + U := by linarith
    refine ⟨b - d, b, ⟨?_, ?_⟩, ⟨?_, le_rfl⟩, ?_, by ring⟩
    · dsimp [b]; linarith
    · dsimp [b]; linarith
    · dsimp [b]; linarith
    · apply (pairCompatible_iff_strips m ε J (b - d) b).2
      refine ⟨A' + U, A', hA, hA', ?_⟩
      have hcoeff : 2 * ((A' + U) * (b - d) - A' * b) = V := by
        dsimp [A']
        field_simp
        ring
      simpa only [show A' + U - A' = U by ring, hcoeff] using hstrip
  · rw [abs_of_nonpos (le_of_not_ge hz)] at hbound
    let A := (-2 * U * (a + d) + V) / (2 * d)
    have hA : m ≤ A := by
      apply (le_div_iff₀ (by positivity : 0 < 2 * d)).2
      dsimp [a] at *
      nlinarith only [hbound]
    have hA' : m ≤ A + U := by linarith
    refine ⟨a, a + d, ⟨le_rfl, ?_⟩, ⟨?_, ?_⟩, ?_, by ring⟩
    · dsimp [a]; linarith
    · dsimp [a]; linarith
    · dsimp [a]; linarith
    · apply (pairCompatible_iff_strips m ε J a (a + d)).2
      refine ⟨A, A + U, hA, hA', ?_⟩
      have hcoeff : 2 * (A * a - (A + U) * (a + d)) = -V := by
        dsimp [A]
        field_simp
        ring
      simpa only [sub_add_cancel_left, hcoeff] using strips_neg ε J U V hstrip

private lemma coefficient_lower (m ε H s U V : ℝ) (J : Design)
    (hm : 0 < m) (hε : 0 ≤ ε) (hU : 0 ≤ U)
    (hstrip : Strips ε J U V) :
    ENNReal.ofReal (min H ((H * U + |s * U - (10 * U + V)|) /
      (2 * (m + U))) / 2) ≤ minimaxRisk m ε H s J := by
  let d := min H ((H * U + |s * U - (10 * U + V)|) / (2 * (m + U)))
  change ENNReal.ofReal (d / 2) ≤ _
  by_cases hd : 0 < d
  · have hb : 2 * (m + U) * d ≤ H * U + |s * U - (10 * U + V)| := by
      have := (le_div_iff₀ (by positivity : 0 < 2 * (m + U))).mp
        (min_le_right H ((H * U + |s * U - (10 * U + V)|) / (2 * (m + U))))
      nlinarith only [this]
    obtain ⟨u, v, hu, hv, hp, hgap⟩ :=
      finite_pair m ε H s U V d J hU hd (min_le_left _ _) hstrip hb
    rw [(raw_minimax m ε H s hε J).1]
    have he : |u - v| = d := by rw [abs_sub_comm, hgap, abs_of_pos hd]
    rw [← he]
    exact le_iSup_of_le u (le_iSup_of_le v (le_iSup_of_le hu
      (le_iSup_of_le hv (le_iSup_of_le hp le_rfl))))
  · rw [ENNReal.ofReal_of_nonpos (by linarith : d / 2 ≤ 0)]
    exact bot_le

private lemma ray_lower (m ε H s l w : ℝ) (J : Design)
    (hm : 0 < m) (hε : 0 ≤ ε) (hw : 0 < w)
    (hrange : ∀ i ∈ J, ∀ j ∈ J,
      ((i.val : ℝ) ^ 2 - l * i.val) - ((j.val : ℝ) ^ 2 - l * j.val) ≤ w) :
    ENNReal.ofReal (min H ((2 * ε / m) * (H + |s + l - 10|) /
      (w + 2 * (2 * ε / m))) / 2) ≤ minimaxRisk m ε H s J := by
  let U := 4 * ε / w
  have hU : 0 ≤ U := by dsimp [U]; positivity
  have hs : Strips ε J U (-l * U) := by
    intro i hi j hj
    have hh := mul_le_mul_of_nonneg_left (hrange i hi j hj) hU
    have he : U * w = 4 * ε := by dsimp [U]; field_simp
    nlinarith only [hh, he]
  have he : (H * U + |s * U - (10 * U + -l * U)|) / (2 * (m + U)) =
      (2 * ε / m) * (H + |s + l - 10|) / (w + 2 * (2 * ε / m)) := by
    rw [show s * U - (10 * U + -l * U) = (s + l - 10) * U by ring,
      abs_mul, abs_of_nonneg hU]
    dsimp [U]
    field_simp
    ring
  simpa only [he] using coefficient_lower m ε H s U (-l * U) J hm hε hU hs

private lemma full_range (l w : ℝ)
    (hl : (l = 1 ∧ w = 90) ∨ (l = 19 ∧ w = 90) ∨
      (l = 3 ∧ w = 72) ∨ (l = 17 ∧ w = 72) ∨ (l = 10 ∧ w = 16)) :
    ∀ i ∈ full, ∀ j ∈ full,
      ((i.val : ℝ) ^ 2 - l * i.val) - ((j.val : ℝ) ^ 2 - l * j.val) ≤ w := by
  intro i _ j _
  have hi := i.property
  have hj := j.property
  simp only [positions, Finset.mem_insert, Finset.mem_singleton] at hi hj
  rcases i with ⟨i, hi'⟩
  rcases j with ⟨j, hj'⟩
  rcases hl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

private lemma deletion_range (p : Index) :
    0 < deletionRange p ∧ ∀ i ∈ full.erase p, ∀ j ∈ full.erase p,
      ((i.val : ℝ) ^ 2 - deletionSlope p * i.val) -
        ((j.val : ℝ) ^ 2 - deletionSlope p * j.val) ≤ deletionRange p := by
  have hp := p.property
  simp only [positions, Finset.mem_insert, Finset.mem_singleton] at hp
  constructor
  · rcases p with ⟨p, hp'⟩
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [deletionRange]
  · intro i hi j hj
    have hip := (Finset.mem_erase.mp hi).1
    have hjp := (Finset.mem_erase.mp hj).1
    have hi' := i.property
    have hj' := j.property
    simp only [positions, Finset.mem_insert, Finset.mem_singleton] at hi' hj'
    rcases p with ⟨p, hp'⟩
    rcases i with ⟨i, hi''⟩
    rcases j with ⟨j, hj''⟩
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hi' with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hj' with rfl | rfl | rfl | rfl | rfl | rfl <;>
      norm_num [deletionRange, deletionSlope] at *

/-- Every single-coordinate deletion has a jointly legal finite-world lower bound. -/
theorem deletion_lower (m ε H s : ℝ) (hm : 0 < m) (hε : 0 < ε) (p : Index) :
    ENNReal.ofReal (min H ((2 * ε / m) * (H + |s + deletionSlope p - 10|) /
      (deletionRange p + 2 * (2 * ε / m))) / 2) ≤
      minimaxRisk m ε H s (full.erase p) :=
  ray_lower m ε H s (deletionSlope p) (deletionRange p) (full.erase p)
    hm hε.le (deletion_range p).1 (deletion_range p).2

private lemma full_strips (ε U V : ℝ) (h : Strips ε full U V) :
    10 * |10 * U + V| ≤ 4 * ε ∧
      9 * |U| + 9 * |10 * U + V| ≤ 4 * ε ∧
      16 * |U| + 8 * |10 * U + V| ≤ 4 * ε := by
  have hh (i j : Index) := h i (by simp [full]) j (by simp [full])
  let z : Index := ⟨0, by norm_num [positions]⟩
  let a : Index := ⟨1, by norm_num [positions]⟩
  let b : Index := ⟨2, by norm_num [positions]⟩
  let c : Index := ⟨8, by norm_num [positions]⟩
  let d : Index := ⟨9, by norm_num [positions]⟩
  let e : Index := ⟨10, by norm_num [positions]⟩
  have hze := hh z e
  have hez := hh e z
  have hea := hh e a
  have hae := hh a e
  have hzd := hh z d
  have hdz := hh d z
  have heb := hh e b
  have hbe := hh b e
  have hzc := hh z c
  have hcz := hh c z
  norm_num [z, a, b, c, d, e] at hze hez hea hae hzd hdz heb hbe hzc hcz
  rcases le_total 0 U with hU | hU <;>
    rcases le_total 0 (10 * U + V) with hV | hV <;>
    simp only [abs_of_nonneg, abs_of_nonpos, hU, hV] <;>
    constructor <;> (try constructor) <;> linarith

private lemma polygon_support (m ε K D U W : ℝ)
    (hU : 0 ≤ U) (hW : 0 ≤ W)
    (h0 : 10 * W ≤ 4 * ε) (h1 : 9 * U + 9 * W ≤ 4 * ε)
    (h2 : 16 * U + 8 * W ≤ 4 * ε)
    (hD0 : 2 * ε ≤ 10 * m * D)
    (hD1 : 2 * ε * (K + 9) ≤ (90 * m + 4 * ε) * D)
    (hD2 : 2 * ε * (K + 7) ≤ (72 * m + 4 * ε) * D)
    (hD3 : 2 * ε * K ≤ (16 * m + 4 * ε) * D) :
    K * U + W ≤ 2 * D * (m + U) := by
  let r := K - 2 * D
  by_cases hr0 : r ≤ 0
  · have hp := mul_nonpos_of_nonpos_of_nonneg hr0 hU
    dsimp [r] at hp
    nlinarith only [hp, h0, hD0]
  have hr0' : 0 ≤ r := (lt_of_not_ge hr0).le
  by_cases hr1 : r ≤ 1
  · have hp := mul_le_mul_of_nonneg_left h1 hr0'
    have hq := mul_le_mul_of_nonneg_left h0 (show 0 ≤ 9 * (1 - r) by linarith)
    dsimp [r] at hp hq
    nlinarith only [hp, hq, hD1]
  have hr1' : 0 ≤ r - 1 := by linarith
  by_cases hr2 : r ≤ 2
  · have hp := mul_le_mul_of_nonneg_left h1 (show 0 ≤ 8 * (2 - r) by linarith)
    have hq := mul_le_mul_of_nonneg_left h2 (show 0 ≤ 9 * (r - 1) by linarith)
    dsimp [r] at hp hq
    nlinarith only [hp, hq, hD2]
  · have hp := mul_le_mul_of_nonneg_left h2 hr0'
    have hq := mul_nonneg (show 0 ≤ r - 2 by linarith) hW
    dsimp [r] at hp hq
    nlinarith only [hp, hq, hD3]

private lemma envelope_bounds (m ε K : ℝ) (hm : 0 < m) (hε : 0 ≤ ε) :
    let D := envelope (2 * ε / m) K
    2 * ε ≤ 10 * m * D ∧
    2 * ε * (K + 9) ≤ (90 * m + 4 * ε) * D ∧
    2 * ε * (K + 7) ≤ (72 * m + 4 * ε) * D ∧
    2 * ε * K ≤ (16 * m + 4 * ε) * D := by
  let c := 2 * ε / m
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have scale (w n : ℝ) (hw : 0 < w) :
      c * n / (w + 2 * c) = 2 * ε * n / (w * m + 4 * ε) := by
    dsimp [c]
    field_simp
    ring
  have h0 : c / 10 ≤ envelope c K := le_max_left _ _
  have h1 : c * (K + 9) / (90 + 2 * c) ≤ envelope c K :=
    (le_max_left _ _).trans (le_max_right _ _)
  have h2 : c * (K + 7) / (72 + 2 * c) ≤ envelope c K :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have h3 : c * K / (16 + 2 * c) ≤ envelope c K :=
    (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have he : c / 10 = 2 * ε / (10 * m) := by dsimp [c]; ring
  rw [he] at h0
  rw [scale 90 (K + 9) (by norm_num)] at h1
  rw [scale 72 (K + 7) (by norm_num)] at h2
  rw [scale 16 K (by norm_num)] at h3
  refine ⟨?_, ?_, ?_, ?_⟩
  · nlinarith only [(div_le_iff₀ (by positivity : 0 < 10 * m)).mp h0]
  · nlinarith only [(div_le_iff₀ (by positivity : 0 < 90 * m + 4 * ε)).mp h1]
  · nlinarith only [(div_le_iff₀ (by positivity : 0 < 72 * m + 4 * ε)).mp h2]
  · nlinarith only [(div_le_iff₀ (by positivity : 0 < 16 * m + 4 * ε)).mp h3]

lemma calibration_bound (m H s u v A A' : ℝ)
    (hu : u ∈ prior H s) (hv : v ∈ prior H s) (huv : u ≤ v)
    (hA : m ≤ A) (hA' : m ≤ A') :
    let U := A - A'
    let W := 10 * U + 2 * (A * u - A' * v)
    2 * (m + |U|) * (v - u) ≤ (H + |s|) * |U| + |W| := by
  dsimp only
  let U := A - A'
  let W := 10 * U + 2 * (A * u - A' * v)
  change 2 * (m + |U|) * (v - u) ≤ (H + |s|) * |U| + |W|
  have hd : 0 ≤ v - u := sub_nonneg.mpr huv
  have hw := neg_le_abs W
  by_cases hU : 0 ≤ U
  · rw [abs_of_nonneg hU]
    have hp := mul_le_mul_of_nonneg_right
      (show m + U ≤ A by dsimp [U]; linarith) hd
    have hq := mul_le_mul_of_nonneg_left
      (show 2 * v + 10 ≤ H + s by linarith [hv.2]) hU
    have hs := mul_le_mul_of_nonneg_left (le_abs_self s) hU
    have he : 2 * A * (v - u) = U * (2 * v + 10) - W := by dsimp [U, W]; ring
    nlinarith only [hp, hq, hs, he, hw]
  · rw [abs_of_nonpos (le_of_not_ge hU)]
    have hp := mul_le_mul_of_nonneg_right
      (show m - U ≤ A' by dsimp [U]; linarith) hd
    have hq := mul_le_mul_of_nonpos_left
      (show -H + s ≤ 2 * u + 10 by linarith [hu.1]) (le_of_not_ge hU)
    have hs := mul_le_mul_of_nonneg_left (neg_le_abs s) (show 0 ≤ -U by linarith)
    have he : 2 * A' * (v - u) = U * (2 * u + 10) - W := by dsimp [U, W]; ring
    nlinarith only [hp, hq, hs, he, hw]

private lemma ordered_gap (m ε H s u v : ℝ) (hm : 0 < m) (hε : 0 ≤ ε)
    (hu : u ∈ prior H s) (hv : v ∈ prior H s) (huv : u ≤ v)
    (hp : PairCompatible m ε full u v) :
    v - u ≤ envelope (2 * ε / m) (H + |s|) := by
  obtain ⟨A, A', hA, hA', hstrip⟩ := (pairCompatible_iff_strips m ε full u v).1 hp
  let U := A - A'
  let V := 2 * (A * u - A' * v)
  have hs := full_strips ε U V hstrip
  have hb := envelope_bounds m ε (H + |s|) hm hε
  have hsupp := polygon_support m ε (H + |s|) (envelope (2 * ε / m) (H + |s|))
    |U| |10 * U + V| (abs_nonneg _) (abs_nonneg _) hs.1 hs.2.1 hs.2.2
    hb.1 hb.2.1 hb.2.2.1 hb.2.2.2
  have hcal := calibration_bound m H s u v A A' hu hv huv hA hA'
  change 2 * (m + |U|) * (v - u) ≤ (H + |s|) * |U| + |10 * U + V| at hcal
  apply (mul_le_mul_iff_left₀ (show 0 < 2 * (m + |U|) by positivity)).mp
  nlinarith only [hcal, hsupp]

private lemma full_lower (m ε H s : ℝ) (hm : 0 < m) (hε : 0 ≤ ε) :
    ENNReal.ofReal (min H (envelope (2 * ε / m) (H + |s|)) / 2) ≤
      minimaxRisk m ε H s full := by
  let c := 2 * ε / m
  let g : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (min H x / 2)
  let R := minimaxRisk m ε H s full
  have hbase : g (c / 10) ≤ R := by
    have hs : Strips ε full 0 (-2 * ε / 5) := by
      intro i _ j _
      have hjn : j.val ≤ 10 := by
        have hh := j.property
        simp only [positions, Finset.mem_insert, Finset.mem_singleton] at hh
        omega
      have hj : (j.val : ℝ) ≤ 10 := by exact_mod_cast hjn
      have hp := mul_nonneg hε (show 0 ≤ (i.val : ℝ) by positivity)
      have hq := mul_nonneg hε (show 0 ≤ 10 - (j.val : ℝ) by linarith)
      nlinarith only [hp, hq]
    have he : (H * 0 + |s * 0 - (10 * 0 + -2 * ε / 5)|) / (2 * (m + 0)) =
        c / 10 := by
      rw [show s * 0 - (10 * 0 + -2 * ε / 5) = 2 * ε / 5 by ring,
        abs_of_nonneg (show 0 ≤ 2 * ε / 5 by positivity)]
      dsimp [c]
      ring
    simpa only [he] using coefficient_lower m ε H s 0 (-2 * ε / 5) full hm hε le_rfl hs
  have hB : g (c * (H + |s| + 9) / (90 + 2 * c)) ≤ R := by
    by_cases hs : 0 ≤ s
    · have he : |s + 19 - 10| = |s| + 9 := by
        rw [abs_of_nonneg hs, abs_of_nonneg (by linarith : 0 ≤ s + 19 - 10)]
        ring
      simpa only [he, add_assoc] using
        ray_lower m ε H s 19 90 full hm hε (by norm_num)
          (full_range 19 90 (Or.inr (Or.inl ⟨rfl, rfl⟩)))
    · have he : |s + 1 - 10| = |s| + 9 := by
        rw [abs_of_nonpos (le_of_not_ge hs), abs_of_nonpos (by linarith : s + 1 - 10 ≤ 0)]
        ring
      simpa only [he, add_assoc] using
        ray_lower m ε H s 1 90 full hm hε (by norm_num)
          (full_range 1 90 (Or.inl ⟨rfl, rfl⟩))
  have hA : g (c * (H + |s| + 7) / (72 + 2 * c)) ≤ R := by
    by_cases hs : 0 ≤ s
    · have he : |s + 17 - 10| = |s| + 7 := by
        rw [abs_of_nonneg hs, abs_of_nonneg (by linarith : 0 ≤ s + 17 - 10)]
        ring
      simpa only [he, add_assoc] using
        ray_lower m ε H s 17 72 full hm hε (by norm_num)
          (full_range 17 72 (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))))
    · have he : |s + 3 - 10| = |s| + 7 := by
        rw [abs_of_nonpos (le_of_not_ge hs), abs_of_nonpos (by linarith : s + 3 - 10 ≤ 0)]
        ring
      simpa only [he, add_assoc] using
        ray_lower m ε H s 3 72 full hm hε (by norm_num)
          (full_range 3 72 (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))
  have hC : g (c * (H + |s|) / (16 + 2 * c)) ≤ R := by
    simpa only [add_sub_cancel_right] using
      ray_lower m ε H s 10 16 full hm hε (by norm_num)
        (full_range 10 16 (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))))
  have combine (x y : ℝ) (hx : g x ≤ R) (hy : g y ≤ R) : g (max x y) ≤ R := by
    rcases le_total x y with h | h
    · simpa only [max_eq_right h] using hy
    · simpa only [max_eq_left h] using hx
  exact combine _ _ hbase (combine _ _ hB (combine _ _ hA hC))

/-- The exact raw deterministic minimax value for every positive prior width and signed center. -/
theorem full_risk (m ε H s : ℝ) (hm : 0 < m) (hε : 0 < ε) (_hH : 0 < H) :
    minimaxRisk m ε H s full =
      ENNReal.ofReal (min H (envelope (2 * ε / m) (H + |s|)) / 2) := by
  apply le_antisymm ?_ (full_lower m ε H s hm hε.le)
  have hupper : minimaxRisk m ε H s full ≤
      ENNReal.ofReal (envelope (2 * ε / m) (H + |s|) / 2) := by
    rw [(raw_minimax m ε H s hε.le full).1]
    refine iSup_le fun u => iSup_le fun v => iSup_le fun hu => iSup_le fun hv =>
      iSup_le fun hp => ENNReal.ofReal_le_ofReal ?_
    have hg : |u - v| ≤ envelope (2 * ε / m) (H + |s|) := by
      rcases le_total u v with huv | hvu
      · rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr huv)]
        exact ordered_gap m ε H s u v hm hε.le hu hv huv hp
      · rw [abs_of_nonneg (sub_nonneg.mpr hvu)]
        have hp' : PairCompatible m ε full v u := by
          obtain ⟨A, A', B, B', hA, hA', hh⟩ := hp
          exact ⟨A', A, B', B, hA', hA, fun i hi => by
            simpa only [abs_sub_comm] using hh i hi⟩
        exact ordered_gap m ε H s v u hm hε.le hv hu hvu hp'
    linarith
  by_cases h : H ≤ envelope (2 * ε / m) (H + |s|)
  · simpa only [min_eq_left h] using (raw_minimax m ε H s hε.le full).2.2.1
  · simpa only [min_eq_right (le_of_not_ge h)] using hupper

#print axioms full_risk
#print axioms deletion_lower

end D5.S3.Observer.MetricGeometry.QuadraticSixPositionRisk
