/- GID: D5/S3/Analytic/SeriesInequalities/PrescribedRatioFloorSmoothing
   generality: G
   mirror-B: D5/B/S3/Analytic/SeriesInequalities/PrescribedRatioFloorSmoothing
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Fixed geometric smoothing preserves doubling floors uniformly. -/

/- Every declaration concerns arbitrary infinite sequences or real functions,
   with noncomputable real powers, infinite sums or suprema. No bounded
   enumeration, checker, numeric reduction or certified finite instance is
   supplied. The computational-content kind is none; the other utility
   fields are not applicable. -/

import Mathlib.Analysis.ODE.DiscreteGronwall
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Algebra.Order.Floor.Ring

open Filter Finset Set
open scoped Topology

noncomputable section

namespace D5.S3.Analytic.SeriesInequalities.PrescribedRatioFloorSmoothing

/-- A geometric average with an unchanged initial value. -/
def smooth (q : ℝ) (ω : ℕ → ℝ) : ℕ → ℝ
  | 0 => ω 0
  | k + 1 => q * smooth q ω k + (1 - q) * ω (k + 1)

private lemma smooth_bounds {q : ℝ} {ω : ℕ → ℝ}
    (hq : 0 < q) (hqone : q < 1) (hpos : ∀ k, 0 < ω k) (hanti : Antitone ω) :
    (∀ k, ω k ≤ smooth q ω k) ∧ Antitone (smooth q ω) ∧
      (∀ k, 0 < smooth q ω k) ∧ (∀ k, q * smooth q ω k ≤ smooth q ω (k + 1)) := by
  have hlo : ∀ k, ω k ≤ smooth q ω k := by
    intro k
    induction k with
    | zero => exact le_rfl
    | succ k ih =>
      have hstep := (hanti (Nat.le_succ k)).trans ih
      simp only [smooth]
      nlinarith
  refine ⟨hlo, antitone_nat_of_succ_le (fun k => ?_),
    (fun k => (hpos k).trans_le (hlo k)), fun k => ?_⟩
  · have hstep := (hanti (Nat.le_succ k)).trans (hlo k)
    simp only [smooth]
    nlinarith
  · simp only [smooth]
    have := hpos (k + 1)
    nlinarith

private lemma smooth_block {q : ℝ} {ω : ℕ → ℝ} (hq : 0 ≤ q)
    (hqone : q ≤ 1) (l t : ℕ) (B : ℝ)
    (hB : ∀ j, l < j → j ≤ l + t → ω j ≤ B) :
    smooth q ω (l + t) ≤ q ^ t * smooth q ω l + (1 - q ^ t) * B := by
  induction t with
  | zero => simp
  | succ t ih =>
    have hi := ih (fun j hj hjt => hB j hj (by omega))
    have hb := hB (l + t + 1) (by omega) (by omega)
    rw [show l + (t + 1) = (l + t) + 1 by omega, smooth, pow_succ]
    have hmul := mul_le_mul_of_nonneg_left hi hq
    have hbmul := mul_le_mul_of_nonneg_left hb (sub_nonneg.mpr hqone)
    nlinarith

private lemma geometric_power_bound {q d : ℝ} (hq : 0 < q) (hqone : q < 1) :
    ∃ A : ℝ, 0 < A ∧ ∀ n : ℕ, q ^ n * (2 * (n : ℝ) + 3) ^ d ≤ A := by
  let b := -Real.log q / 2
  have hb : 0 < b := by
    dsimp [b]
    exact div_pos (neg_pos.mpr (Real.log_neg hq hqone)) (by norm_num)
  have ht : Tendsto (fun n : ℕ => 2 * (n : ℝ) + 3) atTop atTop := by
    have hn : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
    exact (hn.const_mul_atTop (show (0 : ℝ) < 2 by norm_num)).atTop_add tendsto_const_nhds
  have hdecay := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero d b hb).comp ht
  have hlim : Tendsto (fun n : ℕ => q ^ n * (2 * (n : ℝ) + 3) ^ d) atTop (𝓝 0) := by
    convert hdecay.mul_const (Real.exp (3 * b)) using 1
    · ext n
      rw [show q ^ n = Real.exp ((n : ℝ) * Real.log q) by
        rw [Real.exp_nat_mul, Real.exp_log hq]]
      change Real.exp ((n : ℝ) * Real.log q) * (2 * (n : ℝ) + 3) ^ d =
        ((2 * (n : ℝ) + 3) ^ d * Real.exp (-b * (2 * (n : ℝ) + 3))) * Real.exp (3 * b)
      rw [mul_assoc, ← Real.exp_add]
      have heq : -b * (2 * (n : ℝ) + 3) + 3 * b = (n : ℝ) * Real.log q := by
        dsimp [b]; ring
      rw [heq, mul_comm]
    · simp
  obtain ⟨A, hA⟩ := hlim.bddAbove_range
  refine ⟨max A 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), fun n => ?_⟩
  exact (hA (mem_range_self n)).trans (le_max_left _ _)

/-- A fixed geometric smoothing preserves a sequence at every index.
The half-scale condition and power lower bound control the old prefix
uniformly as the splitting index tends to infinity. -/
theorem uniform_smoothing_equivalence {q C c d : ℝ} {ω : ℕ → ℝ}
    (hq : 0 < q) (hqone : q < 1) (hpos : ∀ k, 0 < ω k)
    (hanti : Antitone ω) (hC : 1 ≤ C) (hc : 0 < c) (hd : 0 ≤ d)
    (hhalf : ∀ j k : ℕ, j ≤ k → k + 2 ≤ 2 * (j + 2) → ω j ≤ C * ω k)
    (hlower : ∀ k : ℕ, c ≤ ω k * ((k : ℝ) + 2) ^ d) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ k, ω k ≤ smooth q ω k ∧ smooth q ω k ≤ B * ω k := by
  obtain ⟨hlo, hantiZ, _, _⟩ := smooth_bounds hq hqone hpos hanti
  obtain ⟨A, hApos, hA⟩ := geometric_power_bound (d := d) hq hqone
  let B := C + A * ω 0 / c
  have hB : 1 ≤ B := by
    dsimp [B]
    have := div_pos (mul_pos hApos (hpos 0)) hc
    linarith
  refine ⟨B, hB, fun k => ⟨hlo k, ?_⟩⟩
  let l := k / 2
  have hlk : l ≤ k := Nat.div_le_self _ _
  have hkl : k + 2 ≤ 2 * (l + 2) := by dsimp [l]; omega
  have hblock := smooth_block hq.le hqone.le l (k - l) (C * ω k)
    (fun j hj hjk => hhalf j k (by omega) (by omega))
  rw [Nat.add_sub_of_le hlk] at hblock
  have hprefix : smooth q ω l ≤ ω 0 := by
    exact (hantiZ (Nat.zero_le l)).trans_eq rfl
  have hpow : q ^ (k - l) ≤ q ^ l :=
    pow_le_pow_of_le_one hq.le hqone.le (by dsimp [l]; omega)
  have hscale : ((k : ℝ) + 2) ^ d ≤ (2 * (l : ℝ) + 3) ^ d := by
    apply Real.rpow_le_rpow (by positivity) _ hd
    have : k ≤ 2 * l + 1 := by dsimp [l]; omega
    exact_mod_cast show k + 2 ≤ 2 * l + 3 by omega
  have hweighted : q ^ (k - l) * ((k : ℝ) + 2) ^ d ≤ A := by
    calc
      _ ≤ q ^ l * (2 * (l : ℝ) + 3) ^ d :=
        mul_le_mul hpow hscale (Real.rpow_nonneg (by positivity) _) (pow_nonneg hq.le _)
      _ ≤ A := hA l
  have htail : q ^ (k - l) * ω 0 ≤ (A * ω 0 / c) * ω k := by
    have h₁ := mul_le_mul_of_nonneg_left (hlower k) (pow_nonneg hq.le (k - l))
    have h₂ := mul_le_mul_of_nonneg_right hweighted (hpos k).le
    have hqc : q ^ (k - l) * c ≤ A * ω k := by nlinarith
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hc).2
    have := mul_le_mul_of_nonneg_right hqc (hpos 0).le
    nlinarith
  have hpowzero := pow_nonneg hq.le (k - l)
  have hCn : 0 ≤ C * ω k := mul_nonneg (zero_le_one.trans hC) (hpos k).le
  have hprefixmul := mul_le_mul_of_nonneg_left hprefix hpowzero
  dsimp [B]
  nlinarith

/-- The unscaled floor associated with a real growth function. -/
def doublingFloor (g : ℝ → ℝ) (a : ℝ) (k : ℕ) : ℝ :=
  1 / (((k : ℝ) + 2) * g ((k : ℝ) + 2) ^ (1 / a))

lemma doubling_iterate {g : ℝ → ℝ} {D : ℝ}
    (hD : 1 ≤ D) (hdouble : ∀ t : ℝ, 2 ≤ t → g (2 * t) ≤ D * g t)
    (j : ℕ) (t : ℝ) (ht : 2 ≤ t) : g ((2 : ℝ) ^ j * t) ≤ D ^ j * g t := by
  have hstep (n : ℕ) (_ : 0 ≤ n) :
      g ((2 : ℝ) ^ (n + 1) * t) ≤ D * g ((2 : ℝ) ^ n * t) + 0 := by
    have harg : 2 ≤ (2 : ℝ) ^ n * t := by
      have : 1 ≤ (2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
      nlinarith
    simpa only [pow_succ, mul_assoc, mul_comm, mul_left_comm, add_zero] using
      hdouble ((2 : ℝ) ^ n * t) harg
  have h := discrete_gronwall_prod_general (n₀ := 0)
    (u := fun n => g ((2 : ℝ) ^ n * t)) (c := fun _ => D) (b := fun _ => 0)
    hstep (fun _ _ => zero_le_one.trans hD) (Nat.zero_le j)
  simpa [Finset.prod_const, Nat.card_Ico, mul_comm] using h

lemma doubling_polynomial {g : ℝ → ℝ} {D : ℝ}
    (hg : ∀ t : ℝ, 2 ≤ t → 1 ≤ g t) (hmono : MonotoneOn g (Ici 2))
    (hD : 1 ≤ D) (hdouble : ∀ t : ℝ, 2 ≤ t → g (2 * t) ≤ D * g t) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ t : ℝ, 2 ≤ t →
      g t ≤ C * t ^ (Real.log D / Real.log 2) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogD : 0 ≤ Real.log D := Real.log_nonneg hD
  have hDpos := zero_lt_one.trans_le hD
  refine ⟨D * g 2, by nlinarith [hg 2 le_rfl], fun t ht => ?_⟩
  let j := ⌈Real.log t / Real.log 2⌉₊
  have htpos : 0 < t := by linarith
  have hnlo : Real.log t / Real.log 2 ≤ (j : ℝ) := Nat.le_ceil _
  have hnhi : (j : ℝ) ≤ Real.log t / Real.log 2 + 1 :=
    (Nat.ceil_lt_add_one (div_nonneg (Real.log_nonneg (by linarith)) hlog2.le)).le
  have hcover : t ≤ (2 : ℝ) ^ j := by
    rw [← Real.exp_log htpos, show (2 : ℝ) ^ j = Real.exp ((j : ℝ) * Real.log 2) by
      rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]]
    exact Real.exp_le_exp.mpr (by nlinarith [(div_le_iff₀ hlog2).mp hnlo])
  have harg : 2 ≤ (2 : ℝ) ^ j * 2 := by
    have := one_le_pow₀ (a := (2 : ℝ)) (by norm_num) (n := j)
    linarith
  have hgrowth := doubling_iterate hD hdouble j 2 le_rfl
  have hpowD : D ^ j ≤ D * t ^ (Real.log D / Real.log 2) := by
    rw [show D ^ j = Real.exp ((j : ℝ) * Real.log D) by
      rw [Real.exp_nat_mul, Real.exp_log hDpos]]
    rw [Real.rpow_def_of_pos htpos, ← Real.exp_log hDpos, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    simp only [Real.log_exp]
    have hmul := mul_le_mul_of_nonneg_right hnhi hlogD
    exact hmul.trans_eq (by ring)
  calc
    g t ≤ g ((2 : ℝ) ^ j * 2) := hmono ht harg (by nlinarith [hcover])
    _ ≤ D ^ j * g 2 := hgrowth
    _ ≤ (D * t ^ (Real.log D / Real.log 2)) * g 2 :=
      mul_le_mul_of_nonneg_right hpowD (zero_le_one.trans (hg 2 le_rfl))
    _ = (D * g 2) * t ^ (Real.log D / Real.log 2) := by ring

private lemma floor_conditions {g : ℝ → ℝ} {a D : ℝ}
    (ha : 0 < a) (hg : ∀ t : ℝ, 2 ≤ t → 1 ≤ g t)
    (hmono : MonotoneOn g (Ici 2)) (hD : 1 ≤ D)
    (hdouble : ∀ t : ℝ, 2 ≤ t → g (2 * t) ≤ D * g t) :
    (∀ k, 0 < doublingFloor g a k) ∧ Antitone (doublingFloor g a) ∧
    (∃ C c d : ℝ, 1 ≤ C ∧ 0 < c ∧ 0 ≤ d ∧
      (∀ j k : ℕ, j ≤ k → k + 2 ≤ 2 * (j + 2) →
        doublingFloor g a j ≤ C * doublingFloor g a k) ∧
      (∀ k : ℕ, c ≤ doublingFloor g a k * ((k : ℝ) + 2) ^ d)) := by
  let p := 1 / a
  have hp : 0 < p := one_div_pos.mpr ha
  have hx (k : ℕ) : 0 < (k : ℝ) + 2 := by positivity
  have hx2 (k : ℕ) : 2 ≤ (k : ℝ) + 2 := by
    have := Nat.cast_nonneg (α := ℝ) k; linarith
  have hgp (k : ℕ) : 0 < g ((k : ℝ) + 2) := zero_lt_one.trans_le (hg _ (hx2 k))
  have hden (k : ℕ) : 0 < ((k : ℝ) + 2) * g ((k : ℝ) + 2) ^ p :=
    mul_pos (hx k) (Real.rpow_pos_of_pos (hgp k) p)
  have hpos (k : ℕ) : 0 < doublingFloor g a k := one_div_pos.mpr (hden k)
  refine ⟨hpos, ?_, ?_⟩
  · intro j k hjk
    apply one_div_le_one_div_of_le (hden j)
    have hxjk : (j : ℝ) + 2 ≤ (k : ℝ) + 2 := by exact_mod_cast (show j + 2 ≤ k + 2 by omega)
    exact mul_le_mul hxjk (Real.rpow_le_rpow (hgp j).le
      (hmono (hx2 j) (hx2 k) hxjk) hp.le)
      (Real.rpow_nonneg (hgp j).le _) (hx k).le
  · obtain ⟨Cg, hCg, hpoly⟩ := doubling_polynomial hg hmono hD hdouble
    let δ := Real.log D / Real.log 2
    have hδ : 0 ≤ δ := div_nonneg (Real.log_nonneg hD) (Real.log_pos (by norm_num)).le
    have hCgpos : 0 < Cg := zero_lt_one.trans_le hCg
    refine ⟨2 * D ^ p, 1 / Cg ^ p, 1 + δ * p, ?_, ?_, by positivity, ?_, ?_⟩
    · have := Real.one_le_rpow hD hp.le
      linarith
    · exact one_div_pos.mpr (Real.rpow_pos_of_pos hCgpos p)
    · intro j k hjk hhalf
      have hxy : (k : ℝ) + 2 ≤ 2 * ((j : ℝ) + 2) := by exact_mod_cast hhalf
      have hgy : g ((k : ℝ) + 2) ≤ D * g ((j : ℝ) + 2) :=
        (hmono (hx2 k) (by
          change 2 ≤ 2 * ((j : ℝ) + 2)
          linarith [hx2 j]) hxy).trans (hdouble _ (hx2 j))
      have hpower := Real.rpow_le_rpow (hgp k).le hgy hp.le
      rw [Real.mul_rpow (zero_le_one.trans hD) (hgp j).le] at hpower
      change 1 / (((j : ℝ) + 2) * g ((j : ℝ) + 2) ^ p) ≤
        (2 * D ^ p) * (1 / (((k : ℝ) + 2) * g ((k : ℝ) + 2) ^ p))
      rw [mul_one_div, div_le_div_iff₀ (hden j) (hden k)]
      have hmul := mul_le_mul hxy hpower (Real.rpow_nonneg (hgp k).le _) (by positivity)
      nlinarith
    · intro k
      have hpower := Real.rpow_le_rpow (hgp k).le (hpoly _ (hx2 k)) hp.le
      rw [Real.mul_rpow hCgpos.le (Real.rpow_nonneg (hx k).le _),
        ← Real.rpow_mul (hx k).le] at hpower
      have hmul := mul_le_mul_of_nonneg_left hpower (hx k).le
      have hpoweq : ((k : ℝ) + 2) * ((k : ℝ) + 2) ^ (δ * p) =
          ((k : ℝ) + 2) ^ (1 + δ * p) := by
        rw [Real.rpow_add (hx k), Real.rpow_one]
      change 1 / Cg ^ p ≤ (1 / (((k : ℝ) + 2) * g ((k : ℝ) + 2) ^ p)) *
        ((k : ℝ) + 2) ^ (1 + δ * p)
      rw [one_div_mul_eq_div, div_le_div_iff₀
        (Real.rpow_pos_of_pos hCgpos p) (hden k)]
      dsimp [δ] at hpoweq ⊢
      calc
        _ ≤ ((k : ℝ) + 2) *
            (Cg ^ p * ((k : ℝ) + 2) ^ (Real.log D / Real.log 2 * p)) := by
          simpa using hmul
        _ = _ := by rw [← hpoweq]; ring

private lemma smooth_mass {q : ℝ} {ω : ℕ → ℝ}
    (hq : 0 < q) (hqone : q < 1) (hpos : ∀ k, 0 < ω k)
    (hs : Summable ω) {B : ℝ}
    (hbound : ∀ k, smooth q ω k ≤ B * ω k) :
    Summable (smooth q ω) ∧
      (∑' k, smooth q ω k) = ω 0 / (1 - q) + ∑' k, ω (k + 1) := by
  have hzpos : ∀ k, 0 ≤ smooth q ω k := by
    intro k
    induction k with
    | zero => exact (hpos 0).le
    | succ k ih =>
      exact add_nonneg (mul_nonneg hq.le ih)
        (mul_nonneg (sub_nonneg.mpr hqone.le) (hpos (k + 1)).le)
  have hsz : Summable (smooth q ω) :=
    Summable.of_nonneg_of_le hzpos hbound (hs.mul_left B)
  refine ⟨hsz, ?_⟩
  have hsωshift : Summable (fun k => ω (k + 1)) := (summable_nat_add_iff 1).2 hs
  have hszshift : Summable (fun k => smooth q ω (k + 1)) := (summable_nat_add_iff 1).2 hsz
  have hrec : (∑' k, smooth q ω (k + 1)) =
      q * (∑' k, smooth q ω k) + (1 - q) * (∑' k, ω (k + 1)) := by
    simp only [smooth]
    rw [Summable.tsum_add (hsz.mul_left q) (hsωshift.mul_left (1 - q)),
      tsum_mul_left, tsum_mul_left]
  have hhead := hsz.sum_add_tsum_nat_add 1
  simp only [sum_range_one] at hhead
  change ω 0 + (∑' i, smooth q ω (i + 1)) = (∑' i, smooth q ω i) at hhead
  have hqpos : 0 < 1 - q := sub_pos.mpr hqone
  apply (mul_right_injective₀ hqpos.ne')
  change (1 - q) * (∑' k, smooth q ω k) =
    (1 - q) * (ω 0 / (1 - q) + ∑' k, ω (k + 1))
  rw [mul_add, mul_div_cancel₀ _ hqpos.ne']
  nlinarith

/-- One fixed smoothing keeps the original doubling floor uniformly comparable,
with positive nonincreasing entries and adjacent ratio at most `1/q`.
When the floor is summable, its smoothed total mass is given exactly. -/
theorem doubling_floor_smoothing {g : ℝ → ℝ} {a D q : ℝ}
    (ha : 0 < a) (hg : ∀ t : ℝ, 2 ≤ t → 1 ≤ g t)
    (hmono : MonotoneOn g (Ici 2)) (hD : 1 ≤ D)
    (hdouble : ∀ t : ℝ, 2 ≤ t → g (2 * t) ≤ D * g t)
    (hq : 0 < q) (hqone : q < 1) :
    ∃ B : ℝ, 1 ≤ B ∧
      (∀ k, doublingFloor g a k ≤ smooth q (doublingFloor g a) k ∧
        smooth q (doublingFloor g a) k ≤ B * doublingFloor g a k) ∧
      (∀ k, 0 < smooth q (doublingFloor g a) k) ∧
      Antitone (smooth q (doublingFloor g a)) ∧
      (∀ k, q * smooth q (doublingFloor g a) k ≤ smooth q (doublingFloor g a) (k + 1)) ∧
      (Summable (doublingFloor g a) → Summable (smooth q (doublingFloor g a)) ∧
        (∑' k, smooth q (doublingFloor g a) k) =
          doublingFloor g a 0 / (1 - q) + ∑' k, doublingFloor g a (k + 1)) := by
  obtain ⟨hpos, hanti, C, c, d, hC, hc, hd, hhalf, hlower⟩ :=
    floor_conditions ha hg hmono hD hdouble
  obtain ⟨B, hB, hbounds⟩ := uniform_smoothing_equivalence hq hqone hpos hanti hC hc hd hhalf hlower
  obtain ⟨_, hantiZ, hposZ, hratio⟩ := smooth_bounds hq hqone hpos hanti
  exact ⟨B, hB, hbounds, hposZ, hantiZ, hratio,
    fun hs => smooth_mass hq hqone hpos hs (fun k => (hbounds k).2)⟩

/-- Any prescribed ratio and positive total budget admit a single normalized
smoothed floor. The smoothing parameter is selected before the growth function. -/
theorem prescribed_ratio_floor {R : ℝ} (hR : 1 < R) :
    ∃ q : ℚ, 0 < (q : ℝ) ∧ (q : ℝ) < 1 ∧ 1 / R ≤ (q : ℝ) ∧
      ∀ (g : ℝ → ℝ) (a D K : ℝ), 0 < a → 0 < K →
        (∀ t : ℝ, 2 ≤ t → 1 ≤ g t) → MonotoneOn g (Ici 2) → 1 ≤ D →
        (∀ t : ℝ, 2 ≤ t → g (2 * t) ≤ D * g t) → Summable (doublingFloor g a) →
        ∃ c : ℚ, 0 < (c : ℝ) ∧ (c : ℝ) ≤ 1 ∧
          let η := fun k => (c : ℝ) * smooth (q : ℝ) (doublingFloor g a) k
          (∀ k, 0 < η k ∧ η k ≤ 1) ∧ Antitone η ∧ Summable η ∧
          (∑' k, η k) ≤ K ∧ (∀ k, η k ≤ R * η (k + 1)) ∧
          ∃ B : ℝ, 1 ≤ B ∧ ∀ k,
            (c : ℝ) * doublingFloor g a k ≤ η k ∧
              η k ≤ B * ((c : ℝ) * doublingFloor g a k) := by
  have hRp : 0 < R := zero_lt_one.trans hR
  have hinv : 1 / R < (1 : ℝ) := by rw [div_lt_iff₀ hRp]; simpa
  obtain ⟨q, hqR, hqone⟩ := exists_rat_btwn hinv
  have hqpos : 0 < (q : ℝ) := (one_div_pos.mpr hRp).trans hqR
  refine ⟨q, hqpos, hqone, hqR.le, ?_⟩
  intro g a D K ha hK hg hmono hD hdouble hs
  obtain ⟨B, hB, hbounds, hpos, hanti, hratio, hmass⟩ :=
    doubling_floor_smoothing ha hg hmono hD hdouble hqpos hqone
  obtain ⟨hsz, _⟩ := hmass hs
  let z := smooth (q : ℝ) (doublingFloor g a)
  let M := ∑' k, z k
  have hM : 0 < M := by
    exact (hpos 0).trans_le (hsz.le_tsum 0 (fun k _ => (hpos k).le))
  have heps : 0 < min 1 (K / M) := lt_min zero_lt_one (div_pos hK hM)
  obtain ⟨c, hcpos, hceps⟩ := exists_rat_btwn heps
  have hcone : (c : ℝ) ≤ 1 := (hceps.trans_le (min_le_left _ _)).le
  have hcK : (c : ℝ) * M ≤ K :=
    (le_div_iff₀ hM).mp (hceps.le.trans (min_le_right _ _))
  refine ⟨c, hcpos, hcone, ?_⟩
  change (∀ k, 0 < (c : ℝ) * z k ∧ (c : ℝ) * z k ≤ 1) ∧
    Antitone (fun k => (c : ℝ) * z k) ∧ Summable (fun k => (c : ℝ) * z k) ∧
    (∑' k, (c : ℝ) * z k) ≤ K ∧
    (∀ k, (c : ℝ) * z k ≤ R * ((c : ℝ) * z (k + 1))) ∧
    ∃ B : ℝ, 1 ≤ B ∧ ∀ k,
      (c : ℝ) * doublingFloor g a k ≤ (c : ℝ) * z k ∧
      (c : ℝ) * z k ≤ B * ((c : ℝ) * doublingFloor g a k)
  have hzle (k : ℕ) : z k ≤ 1 := by
    have hden : 1 ≤ (2 : ℝ) * g 2 ^ (1 / a) := by
      have := Real.one_le_rpow (hg 2 le_rfl) (one_div_pos.mpr ha).le
      linarith
    exact (hanti (Nat.zero_le k)).trans (by
      rw [smooth, doublingFloor]; norm_num only [Nat.cast_zero, zero_add]
      exact (div_le_one (by positivity)).mpr hden)
  refine ⟨fun k => ⟨mul_pos hcpos (hpos k), ?_⟩, ?_, hsz.mul_left _, ?_, ?_, B, hB, ?_⟩
  · exact (mul_le_mul_of_nonneg_left (hzle k) hcpos.le).trans (by simpa using hcone)
  · intro j k hjk
    exact mul_le_mul_of_nonneg_left (hanti hjk) hcpos.le
  · rw [tsum_mul_left]; exact hcK
  · intro k
    have hqmul : 1 ≤ R * (q : ℝ) := by simpa [mul_comm] using (div_le_iff₀ hRp).mp hqR.le
    have := mul_le_mul_of_nonneg_left (hratio k) hRp.le
    have := (mul_le_mul_of_nonneg_right hqmul (hpos k).le).trans (by simpa [mul_assoc] using this)
    have := mul_le_mul_of_nonneg_left this hcpos.le
    nlinarith
  · intro k
    constructor
    · exact mul_le_mul_of_nonneg_left (hbounds k).1 hcpos.le
    · have := mul_le_mul_of_nonneg_left (hbounds k).2 hcpos.le
      nlinarith

end D5.S3.Analytic.SeriesInequalities.PrescribedRatioFloorSmoothing
