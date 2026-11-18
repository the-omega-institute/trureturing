/- GID: D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/Analytic/OmegaSecond/Entropy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite binomial entropy bounds from the maximum binomial term. -/


import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Real Finset MeasureTheory Set
open Filter
open scoped Topology BigOperators

namespace D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy

private def term (m : ℕ) (p : ℝ) (j : ℕ) : ℝ :=
  (m.choose j : ℝ) * p ^ j * (1 - p) ^ (m - j)

private lemma term_succ (m j : ℕ) (p : ℝ) (hj : j < m) :
    term m p (j + 1) * ((j + 1 : ℕ) : ℝ) * (1 - p) =
      term m p j * ((m - j : ℕ) : ℝ) * p := by
  have hc : (m.choose (j + 1) : ℝ) * (j + 1 : ℕ) =
      (m.choose j : ℝ) * (m - j : ℕ) := by
    exact_mod_cast Nat.choose_succ_right_eq m j
  have hd : m - j = m - (j + 1) + 1 := by omega
  dsimp only [term]
  have hp : p ^ (j + 1) = p ^ j * p := pow_succ p j
  have hq : (1 - p) ^ (m - j) = (1 - p) ^ (m - (j + 1)) * (1 - p) := by
    rw [hd, pow_succ]
  rw [hp, hq]
  linear_combination p ^ j * p * (1 - p) ^ (m - (j + 1)) * (1 - p) * hc

private lemma term_maximum (m a : ℕ) (ha : a ≤ m) (ha0 : 0 < a) (ham : a < m)
    (j : ℕ) (hj : j ≤ m) :
    term m ((a : ℝ) / m) j ≤ term m ((a : ℝ) / m) a := by
  have hm : (0 : ℝ) < m := by exact_mod_cast ha0.trans ham
  have hap : (0 : ℝ) < a := by exact_mod_cast ha0
  have haR : (a : ℝ) < m := by exact_mod_cast ham
  let p : ℝ := (a : ℝ) / m
  have hp : 0 < p := div_pos hap hm
  have hp1 : 0 < 1 - p := sub_pos.mpr ((div_lt_one hm).mpr haR)
  have hnonneg (i : ℕ) : 0 ≤ term m p i := by unfold term; positivity
  have hrelation (i : ℕ) (hi : i < m) := term_succ m i p hi
  have hcoeff (i : ℕ) (hi : i ≤ m) :
      ((m - i : ℕ) : ℝ) * p - (i + 1 : ℕ) * (1 - p) =
        (a : ℝ) - i - 1 + p := by
    rw [Nat.cast_sub hi, Nat.cast_add, Nat.cast_one]
    dsimp only [p]
    field_simp
    <;> ring
  have hup (i : ℕ) (hi : i < a) : term m p i ≤ term m p (i + 1) := by
    have him : i < m := hi.trans ham
    have hle : ((i + 1 : ℕ) : ℝ) * (1 - p) ≤ ((m - i : ℕ) : ℝ) * p := by
      have hh : (i : ℝ) + 1 ≤ a := by exact_mod_cast hi
      have := hcoeff i him.le
      linarith
    have hh := mul_le_mul_of_nonneg_left hle (hnonneg i)
    have hr := hrelation i him
    have hd : 0 < ((i + 1 : ℕ) : ℝ) * (1 - p) := by positivity
    apply (mul_le_mul_iff_left₀ hd).mp
    nlinarith only [hh, hr]
  have hdown (i : ℕ) (hai : a ≤ i) (him : i < m) :
      term m p (i + 1) ≤ term m p i := by
    have hle : ((m - i : ℕ) : ℝ) * p ≤ ((i + 1 : ℕ) : ℝ) * (1 - p) := by
      have hh : (a : ℝ) ≤ i := by exact_mod_cast hai
      have := hcoeff i him.le
      have : p < 1 := by linarith
      linarith
    have hh := mul_le_mul_of_nonneg_left hle (hnonneg i)
    have hr := hrelation i him
    have hd : 0 < ((i + 1 : ℕ) : ℝ) * (1 - p) := by positivity
    apply (mul_le_mul_iff_left₀ hd).mp
    nlinarith only [hh, hr]
  change term m p j ≤ term m p a
  rcases le_total j a with hja | haj
  · have hh : ∀ b, j ≤ b → b ≤ a → term m p j ≤ term m p b := by
      intro b hb
      induction b, hb using Nat.le_induction with
      | base => exact fun _ => le_rfl
      | succ b hb ih =>
        intro hba
        exact (ih (by omega)).trans (hup b (by omega))
    exact hh a hja le_rfl
  · have hh : ∀ b, a ≤ b → b ≤ m → term m p b ≤ term m p a := by
      intro b hb
      induction b, hb using Nat.le_induction with
      | base => exact fun _ => le_rfl
      | succ b hb ih =>
        intro hbm
        exact (hdown b hb (by omega)).trans (ih (by omega))
    exact hh j haj hj

/-- A finite binomial coefficient dominates its entropy exponential, with only
the exact maximum-term loss `log (m+1)`. -/
theorem log_choose_ge_binEntropy (m a : ℕ) (ha : a ≤ m) :
    (m : ℝ) * binEntropy ((a : ℝ) / m) - log ((m : ℝ) + 1) ≤
      log (m.choose a : ℝ) := by
  by_cases ha0 : a = 0
  · subst a
    simp only [Nat.cast_zero, zero_div, binEntropy_zero, mul_zero, zero_sub,
      Nat.choose_zero_right, Nat.cast_one, log_one]
    exact neg_nonpos.mpr (log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) m]))
  by_cases ham : a = m
  · subst a
    have hm : (m : ℝ) ≠ 0 := by exact_mod_cast ha0
    simp only [div_self hm, binEntropy_one, mul_zero, zero_sub, Nat.choose_self,
      Nat.cast_one, log_one]
    exact neg_nonpos.mpr (log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) m]))
  have ha0' : 0 < a := Nat.pos_of_ne_zero ha0
  have ham' : a < m := lt_of_le_of_ne ha ham
  have hm : (0 : ℝ) < m := by exact_mod_cast ha0'.trans ham'
  have haR : (0 : ℝ) < a := by exact_mod_cast ha0'
  have haRm : (a : ℝ) < m := by exact_mod_cast ham'
  let p : ℝ := (a : ℝ) / m
  have hp : 0 < p := div_pos haR hm
  have hp1 : 0 < 1 - p := sub_pos.mpr ((div_lt_one hm).mpr haRm)
  have hchoose : (0 : ℝ) < m.choose a := by exact_mod_cast Nat.choose_pos ha
  have hterm : 0 < term m p a := by unfold term; positivity
  have hsum : (∑ j ∈ range (m + 1), term m p j) = 1 := by
    have h := add_pow p (1 - p) m
    simp only [show p + (1 - p) = 1 by ring, one_pow] at h
    calc
      _ = ∑ j ∈ range (m + 1), p ^ j * (1 - p) ^ (m - j) * (m.choose j : ℝ) := by
        apply sum_congr rfl
        intro j hj
        dsimp only [term]
        ring
      _ = 1 := h.symm
  have hmax : 1 ≤ ((m : ℝ) + 1) * term m p a := by
    calc
      1 = ∑ j ∈ range (m + 1), term m p j := hsum.symm
      _ ≤ ∑ _j ∈ range (m + 1), term m p a := by
        apply sum_le_sum
        intro j hj
        exact term_maximum m a ha ha0' ham' j (by simpa using (mem_range.mp hj))
      _ = _ := by simp
  have hlog := log_le_log (by norm_num : (0 : ℝ) < 1) hmax
  have hlogterm : log (term m p a) = log (m.choose a : ℝ) - (m : ℝ) * binEntropy p := by
    dsimp only [term]
    rw [log_mul (mul_pos hchoose (pow_pos hp _)).ne' (pow_pos hp1 _).ne',
      log_mul hchoose.ne' (pow_pos hp _).ne', log_pow, log_pow,
      binEntropy, log_inv, log_inv, Nat.cast_sub ha]
    have hmp : (m : ℝ) * p = a := by dsimp only [p]; field_simp
    linear_combination -(log p - log (1 - p)) * hmp
  rw [log_one, log_mul (by positivity : (m : ℝ) + 1 ≠ 0) hterm.ne', hlogterm] at hlog
  change (m : ℝ) * binEntropy p - log ((m : ℝ) + 1) ≤ _
  linarith

/-- The explicit finite entropy lower estimate. -/
def entropyLower (m a : ℕ) : ℝ :=
  (m : ℝ) * binEntropy ((a : ℝ) / m) - log ((m : ℝ) + 1)

/-- The finite maximum-term loss disappears on every growing common scale. -/
theorem entropy_lower_scaled {α : Type*} {l : Filter α}
    (W : α → ℝ) (n k : α → ℕ) {d q : ℝ}
    (hW : Tendsto W l atTop) (hd : 0 < d)
    (hn : Tendsto (fun x => (n x : ℝ) / W x) l (𝓝 d))
    (hk : Tendsto (fun x => (k x : ℝ) / W x) l (𝓝 (d * q))) :
    Tendsto (fun x => entropyLower (n x) (k x) / W x) l (𝓝 (d * binEntropy q)) := by
  have hnR : Tendsto (fun x => (n x : ℝ)) l atTop := by
    apply (hW.atTop_mul_pos hd hn).congr'
    filter_upwards [hW.eventually_gt_atTop 0] with x hx
    exact mul_div_cancel₀ _ hx.ne'
  have hq : Tendsto (fun x => (k x : ℝ) / n x) l (𝓝 q) := by
    have h := hk.div hn hd.ne'
    rw [mul_div_cancel_left₀ q hd.ne'] at h
    apply h.congr'
    filter_upwards [hW.eventually_gt_atTop 0] with x hx
    exact div_div_div_cancel_right₀ hx.ne' _ _
  have hn1 : Tendsto (fun x => ((n x : ℝ) + 1) / W x) l (𝓝 d) := by
    have h := hn.add (hW.const_div_atTop 1)
    simpa only [add_div, add_zero] using h
  have hlog : Tendsto (fun x => log ((n x : ℝ) + 1) / W x) l (𝓝 0) := by
    have htop := tendsto_atTop_add_const_right l 1 hnR
    have h := (isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp htop).mul hn1
    simp only [zero_mul] at h
    apply h.congr'
    filter_upwards [] with x
    dsimp only [Function.comp_def, id_eq]
    exact div_mul_div_cancel₀ (by positivity : (n x : ℝ) + 1 ≠ 0)
  have h := (hn.mul (binEntropy_continuous.continuousAt.tendsto.comp hq)).sub hlog
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards [] with x
  dsimp only [entropyLower, Function.comp_def]
  ring

/-- Taking a fixed nonnegative fraction and rounding down preserves its scale. -/
theorem floor_scaled {α : Type*} {l : Filter α}
    (W : α → ℝ) (M : α → ℕ) {d q : ℝ}
    (hW : Tendsto W l atTop) (hd : 0 < d) (hq : 0 ≤ q)
    (hM : Tendsto (fun x => (M x : ℝ) / W x) l (𝓝 d)) :
    Tendsto (fun x => (⌊q * (M x : ℝ)⌋₊ : ℝ) / W x) l (𝓝 (q * d)) := by
  have hMR : Tendsto (fun x => (M x : ℝ)) l atTop := by
    apply (hW.atTop_mul_pos hd hM).congr'
    filter_upwards [hW.eventually_gt_atTop 0] with x hx
    exact mul_div_cancel₀ _ hx.ne'
  have h := ((tendsto_nat_floor_mul_div_atTop hq).comp hMR).mul hM
  apply h.congr'
  filter_upwards [hMR.eventually_gt_atTop 0] with x hx
  exact div_mul_div_cancel₀ hx.ne'

/-- Equal limits for two capacities give the same limit for their common capacity. -/
theorem min_scaled {α : Type*} {l : Filter α}
    (W : α → ℝ) (M N : α → ℕ) {d : ℝ}
    (hW : Tendsto W l atTop)
    (hM : Tendsto (fun x => (M x : ℝ) / W x) l (𝓝 d))
    (hN : Tendsto (fun x => (N x : ℝ) / W x) l (𝓝 d)) :
    Tendsto (fun x => ((min (M x) (N x) : ℕ) : ℝ) / W x) l (𝓝 d) := by
  have h := hM.min hN
  simp only [min_self] at h
  apply h.congr'
  filter_upwards [hW.eventually_gt_atTop 0] with x hx
  rw [Nat.cast_min, min_div_div_right hx.le]

end D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy
namespace D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.KernelLimit

/-- A normalized majorant with the sharp limiting coefficient. -/
def correctionMajorant (s : ℝ) : ℝ :=
  π ^ 2 / (6 * (1 - π ^ 2 / (6 * s ^ 2)))

/-- Cubic sine control retains the sharp one-sixth coefficient. -/
theorem kernel_correction_upper {s : ℝ} (hs : π ≤ s) :
    0 ≤ s * (π / sin (π / s) - s) ∧
      s * (π / sin (π / s) - s) ≤ correctionMajorant s := by
  have hs0 : 0 < s := pi_pos.trans_le hs
  let t : ℝ := π / s
  have ht0 : 0 < t := div_pos pi_pos hs0
  have ht1 : t ≤ 1 := (div_le_one hs0).mpr hs
  have htp : t < π := by dsimp [t]; exact div_lt_self pi_pos (by linarith [pi_gt_three])
  have hsin : 0 < sin t := sin_pos_of_pos_of_lt_pi ht0 htp
  have hd : 0 < 1 - t ^ 2 / 6 := by nlinarith
  have hcube := sin_ge_sub_cube ht0.le
  have hquot : t / sin t ≤ 1 / (1 - t ^ 2 / 6) := by
    apply (div_le_div_iff₀ hsin hd).mpr
    nlinarith
  have hnonneg : 0 ≤ t / sin t - 1 := by
    have h : 1 ≤ t / sin t := (le_div_iff₀ hsin).mpr
      (by simpa only [one_mul] using sin_le ht0.le)
    linarith
  have hbound : t / sin t - 1 ≤ t ^ 2 / (6 * (1 - t ^ 2 / 6)) := by
    have hid : 1 / (1 - t ^ 2 / 6) - 1 =
        t ^ 2 / (6 * (1 - t ^ 2 / 6)) := by
      have hd' : 6 - t ^ 2 ≠ 0 := by nlinarith
      field_simp [hd.ne', hd']
      <;> ring
    linarith
  have hid : s * (π / sin (π / s) - s) = s ^ 2 * (t / sin t - 1) := by
    dsimp [t]
    field_simp [hs0.ne', hsin.ne']
    <;> ring
  rw [hid]
  constructor
  · exact mul_nonneg (sq_nonneg _) hnonneg
  · have hb := mul_le_mul_of_nonneg_left hbound (sq_nonneg s)
    convert hb using 1
    dsimp only [correctionMajorant, t]
    field_simp [hs0.ne']
    <;> ring

/-- The correction majorant approaches the sharp coefficient pi squared over six. -/
theorem correction_majorant_limit :
    Tendsto correctionMajorant atTop (𝓝 (π ^ 2 / 6)) := by
  have hi : Tendsto (fun s : ℝ => 1 / s) atTop (𝓝 0) :=
    tendsto_id.const_div_atTop 1
  have h := (tendsto_const_nhds (x := π ^ 2)).div
    (((tendsto_const_nhds (x := (1 : ℝ))).sub
      ((hi.pow 2).const_mul (π ^ 2 / 6))).const_mul 6)
    (by norm_num : 6 * (1 - π ^ 2 / 6 * 0 ^ 2) ≠ 0)
  norm_num only [zero_pow, mul_zero, sub_zero, one_mul] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
  change π ^ 2 / (6 * (1 - π ^ 2 / 6 * (1 / s) ^ 2)) =
    π ^ 2 / (6 * (1 - π ^ 2 / (6 * s ^ 2)))
  congr 1
  ring

end D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.KernelLimit

namespace D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.Tail

private lemma log_softplus_le_exp (v : ℝ) : log (1 + exp v) ≤ exp v := by
  simpa only [add_sub_cancel_left] using log_le_sub_one_of_pos (by positivity : 0 < 1 + exp v)

/-- An inverse-power sum over any finite set beyond an integer cutoff. -/
theorem finite_power_tail {s : ℝ} (hs : 1 < s) {N : ℕ} (hN : 0 < N)
    (S : Finset ℕ) (hS : ∀ n ∈ S, N < n) :
    ∑ n ∈ S, (n : ℝ) ^ (-s) ≤ (N : ℝ) ^ (1 - s) / (s - 1) := by
  classical
  let M := S.sup id
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hsub : S ⊆ Finset.Ioc N M := by
    intro n hn
    exact Finset.mem_Ioc.mpr ⟨hS n hn, Finset.le_sup (f := id) hn⟩
  have hanti : AntitoneOn (fun t : ℝ => t ^ (-s)) (Icc (N : ℝ) M) := by
    intro a ha b hb hab
    exact rpow_le_rpow_of_nonpos (hN0.trans_le ha.1) hab (by linarith)
  have hsum : (∑ n ∈ Finset.Ioc N M, (n : ℝ) ^ (-s)) =
      ∑ n ∈ Finset.Ico N M, ((n + 1 : ℕ) : ℝ) ^ (-s) := by
    rw [← Finset.Ico_add_one_add_one_eq_Ioc, ← Finset.sum_Ico_add']
  calc
    _ ≤ ∑ n ∈ Finset.Ioc N M, (n : ℝ) ^ (-s) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => rpow_nonneg (Nat.cast_nonneg _) _)
    _ = _ := hsum
    _ ≤ ∫ t in Ioi (N : ℝ), t ^ (-s) :=
      hanti.sum_Ico_le_integral (integrableOn_Ioi_rpow_of_lt (by linarith) hN0)
        (fun t ht => rpow_nonneg (hN0.trans ht).le _)
    _ = (N : ℝ) ^ (1 - s) / (s - 1) := by
      rw [integral_Ioi_rpow_of_lt (by linarith : -s < -1) hN0]
      rw [show -s + 1 = 1 - s by ring]
      have h1 : s - 1 ≠ 0 := by linarith
      have h2 : 1 - s ≠ 0 := by linarith
      field_simp [h1, h2]
      ring

/-- The small side is bounded by the number of integers times geometric decay. -/
theorem small_weight_tail {P s : ℝ} (hP : 2 ≤ P) (hs : 0 ≤ s)
    (S : Finset ℕ) (hS : ∀ n ∈ S, 0 < n ∧ (n : ℝ) ≤ P / 2) :
    ∑ n ∈ S, log (1 + exp (-s * |log ((n : ℝ) / P)|)) ≤ P * (1 / 2 : ℝ) ^ s := by
  have hP0 : 0 < P := by linarith
  have hsub : S ⊆ Finset.Icc 1 ⌊P / 2⌋₊ := by
    intro n hn
    exact Finset.mem_Icc.mpr ⟨(hS n hn).1, (Nat.le_floor_iff (by positivity)).mpr (hS n hn).2⟩
  have hcard : (S.card : ℝ) ≤ P := by
    have hc := Finset.card_le_card hsub
    simp only [Nat.card_Icc, Nat.add_sub_cancel] at hc
    have hc' : (S.card : ℝ) ≤ ⌊P / 2⌋₊ := by exact_mod_cast hc
    exact hc'.trans ((Nat.floor_le (by positivity)).trans (by linarith))
  have hpoint (n : ℕ) (hn : n ∈ S) :
      log (1 + exp (-s * |log ((n : ℝ) / P)|)) ≤ (1 / 2 : ℝ) ^ s := by
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (hS n hn).1
    have hratio : (n : ℝ) / P ≤ 1 / 2 := (div_le_iff₀ hP0).mpr (by linarith [(hS n hn).2])
    have hl : log ((n : ℝ) / P) ≤ log (1 / 2 : ℝ) :=
      log_le_log (div_pos hn0 hP0) hratio
    have hl0 : log ((n : ℝ) / P) ≤ 0 :=
      log_nonpos (div_nonneg hn0.le hP0.le) (hratio.trans (by norm_num))
    refine (log_softplus_le_exp _).trans ?_
    rw [abs_of_nonpos hl0, neg_mul_neg,
      rpow_def_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    exact exp_le_exp.mpr (by nlinarith)
  calc
    _ ≤ ∑ n ∈ S, (1 / 2 : ℝ) ^ s := Finset.sum_le_sum hpoint
    _ = (S.card : ℝ) * (1 / 2 : ℝ) ^ s := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hcard (rpow_nonneg (by norm_num) _)

/-- The large side is bounded using all integers and an actual tail integral. -/
theorem large_weight_tail {P s : ℝ} (hP : 2 ≤ P) (hs : 2 ≤ s)
    (S : Finset ℕ) (hS : ∀ n ∈ S, 2 * P < (n : ℝ)) :
    ∑ n ∈ S, log (1 + exp (-s * |log ((n : ℝ) / P)|)) ≤
      2 * P * (2 / 3 : ℝ) ^ s := by
  have hP0 : 0 < P := by linarith
  let N := ⌊2 * P⌋₊
  have hNlo : 3 * P / 2 ≤ (N : ℝ) := by
    have h := Nat.lt_floor_add_one (2 * P)
    dsimp [N]
    linarith
  have hN0 : (0 : ℝ) < N := by nlinarith
  have hNN : 0 < N := by exact_mod_cast hN0
  have hS' : ∀ n ∈ S, N < n := by
    intro n hn
    exact (Nat.floor_lt (by positivity : 0 ≤ 2 * P)).mpr (hS n hn)
  have hpoint (n : ℕ) (hn : n ∈ S) :
      log (1 + exp (-s * |log ((n : ℝ) / P)|)) ≤ P ^ s * (n : ℝ) ^ (-s) := by
    have hn0 : (0 : ℝ) < n := by linarith [hS n hn]
    have hratio : 1 ≤ (n : ℝ) / P := (le_div_iff₀ hP0).mpr (by linarith [hS n hn])
    have hl : 0 ≤ log ((n : ℝ) / P) := log_nonneg hratio
    refine (log_softplus_le_exp _).trans_eq ?_
    rw [abs_of_nonneg hl, log_div hn0.ne' hP0.ne',
      rpow_def_of_pos hP0, rpow_def_of_pos hn0, ← exp_add]
    congr 1
    ring
  have hfinite := finite_power_tail (by linarith : 1 < s) hNN S hS'
  have hmono : (N : ℝ) ^ (1 - s) ≤ (3 * P / 2) ^ (1 - s) :=
    rpow_le_rpow_of_nonpos (by positivity) hNlo (by linarith)
  have hid : P ^ s * (3 * P / 2) ^ (1 - s) =
      (3 * P / 2) * (2 / 3 : ℝ) ^ s := by
    rw [rpow_sub (by positivity), rpow_one]
    calc
      P ^ s * ((3 * P / 2) / (3 * P / 2) ^ s) =
          (3 * P / 2) * (P ^ s / (3 * P / 2) ^ s) := by ring
      _ = (3 * P / 2) * (P / (3 * P / 2)) ^ s := by
        rw [div_rpow hP0.le (by positivity)]
      _ = _ := by
        congr 2
        field_simp [hP0.ne']
        <;> ring
  calc
    _ ≤ ∑ n ∈ S, P ^ s * (n : ℝ) ^ (-s) := Finset.sum_le_sum hpoint
    _ = P ^ s * ∑ n ∈ S, (n : ℝ) ^ (-s) := by rw [Finset.mul_sum]
    _ ≤ P ^ s * ((N : ℝ) ^ (1 - s) / (s - 1)) :=
      mul_le_mul_of_nonneg_left hfinite (rpow_nonneg hP0.le _)
    _ ≤ P ^ s * ((3 * P / 2) ^ (1 - s) / (s - 1)) :=
      mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right hmono (by linarith)) (rpow_nonneg hP0.le _)
    _ = ((3 * P / 2) * (2 / 3 : ℝ) ^ s) / (s - 1) := by rw [← mul_div_assoc, hid]
    _ ≤ (3 * P / 2) * (2 / 3 : ℝ) ^ s :=
      div_le_self (by positivity) (by linarith)
    _ ≤ _ := by gcongr; linarith

/-- Every fixed geometric decay kills the second-threshold logarithmic scale
when the exponent grows as a positive multiple of its square root. -/
theorem geometric_sqrt_decay {c q : ℝ} (hc : 0 < c) (hq0 : 0 < q) (hq1 : q < 1) :
    Tendsto (fun t : ℝ => t * sqrt t * q ^ (c * sqrt t)) atTop (𝓝 0) := by
  let b : ℝ := -c * log q
  have hb : 0 < b := mul_pos_of_neg_of_neg (by linarith) (log_neg hq0 hq1)
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 3 b hb).comp tendsto_sqrt_atTop
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  simp only [Function.comp_def, rpow_ofNat]
  rw [rpow_def_of_pos hq0]
  have he : -b * sqrt t = log q * (c * sqrt t) := by dsimp [b]; ring
  have hp : sqrt t ^ 3 = t * sqrt t := by
    calc
      sqrt t ^ 3 = sqrt t ^ 2 * sqrt t := by ring
      _ = t * sqrt t := by rw [sq_sqrt ht.le]
  rw [he, hp]

end D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.Tail
