/- GID: D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy generality: I mirror-B: D5/B/S3/Arith/Robin/Analytic/OmegaSecond/Entropy mirror-E: none(waiver:evidence-not-specified-by-formal-manifest) anchors: [] utility: none digest: Finite binomial entropy bounds from the maximum binomial term. -/
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic
import D5.S3.Arith.Robin.Analytic.OmegaSecond.Exchange
import D5.S3.Arith.Robin.Analytic.OmegaTail.Selection
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped Topology BigOperators
open Real Filter MeasureTheory Finset Set Asymptotics
namespace D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy
private def term (m : ℕ) (p : ℝ) (j : ℕ) : ℝ := (m.choose j : ℝ) * p ^ j * (1 - p) ^ (m - j)
private lemma term_succ (m j : ℕ) (p : ℝ) (hj : j < m) : term m p (j + 1) * ((j + 1 : ℕ) : ℝ) * (1 - p) =
      term m p j * ((m - j : ℕ) : ℝ) * p := by
  have hc : (m.choose (j + 1) : ℝ) * (j + 1 : ℕ) = (m.choose j : ℝ) * (m - j : ℕ) := by
    exact_mod_cast Nat.choose_succ_right_eq m j
  have hd : m - j = m - (j + 1) + 1 := by omega
  dsimp only [term]
  have hp : p ^ (j + 1) = p ^ j * p := pow_succ p j
  have hq : (1 - p) ^ (m - j) = (1 - p) ^ (m - (j + 1)) * (1 - p) := by
    rw [hd, pow_succ]
  rw [hp, hq]
  linear_combination p ^ j * p * (1 - p) ^ (m - (j + 1)) * (1 - p) * hc
private lemma term_maximum (m a : ℕ) (ha : a ≤ m) (ha0 : 0 < a) (ham : a < m) (j : ℕ) (hj : j ≤ m) :
    term m ((a : ℝ) / m) j ≤ term m ((a : ℝ) / m) a := by
  have hm : (0 : ℝ) < m := by exact_mod_cast ha0.trans ham
  have hap : (0 : ℝ) < a := by exact_mod_cast ha0
  have haR : (a : ℝ) < m := by exact_mod_cast ham
  let p : ℝ := (a : ℝ) / m
  have hp : 0 < p := div_pos hap hm
  have hp1 : 0 < 1 - p := sub_pos.mpr ((div_lt_one hm).mpr haR)
  have hnonneg (i : ℕ) : 0 ≤ term m p i := by unfold term; positivity
  have hrelation (i : ℕ) (hi : i < m) := term_succ m i p hi
  have hcoeff (i : ℕ) (hi : i ≤ m) : ((m - i : ℕ) : ℝ) * p - (i + 1 : ℕ) * (1 - p) = (a : ℝ) - i - 1 + p := by
    rw [Nat.cast_sub hi, Nat.cast_add, Nat.cast_one]
    dsimp only [p]
    field_simp <;> ring
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
  have hdown (i : ℕ) (hai : a ≤ i) (him : i < m) : term m p (i + 1) ≤ term m p i := by
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
theorem log_choose_ge_binEntropy (m a : ℕ) (ha : a ≤ m) : (m : ℝ) * binEntropy ((a : ℝ) / m) - log ((m : ℝ) + 1) ≤
      log (m.choose a : ℝ) := by
  by_cases ha0 : a = 0
  · subst a
    simp only [Nat.cast_zero, zero_div, binEntropy_zero, mul_zero, zero_sub, Nat.choose_zero_right, Nat.cast_one, log_one]
    exact neg_nonpos.mpr (log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) m]))
  by_cases ham : a = m
  · subst a
    have hm : (m : ℝ) ≠ 0 := by exact_mod_cast ha0
    simp only [div_self hm, binEntropy_one, mul_zero, zero_sub, Nat.choose_self, Nat.cast_one, log_one]
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
    rw [log_mul (mul_pos hchoose (pow_pos hp _)).ne' (pow_pos hp1 _).ne', log_mul hchoose.ne' (pow_pos hp _).ne', log_pow, log_pow,
      binEntropy, log_inv, log_inv, Nat.cast_sub ha]
    have hmp : (m : ℝ) * p = a := by dsimp only [p]; field_simp
    linear_combination -(log p - log (1 - p)) * hmp
  rw [log_one, log_mul (by positivity : (m : ℝ) + 1 ≠ 0) hterm.ne', hlogterm] at hlog
  change (m : ℝ) * binEntropy p - log ((m : ℝ) + 1) ≤ _
  linarith
def entropyLower (m a : ℕ) : ℝ := (m : ℝ) * binEntropy ((a : ℝ) / m) - log ((m : ℝ) + 1)
theorem entropy_lower_scaled {α : Type*} {l : Filter α} (W : α → ℝ) (n k : α → ℕ) {d q : ℝ} (hW : Tendsto W l atTop) (hd : 0 < d)
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
theorem floor_scaled {α : Type*} {l : Filter α} (W : α → ℝ) (M : α → ℕ) {d q : ℝ} (hW : Tendsto W l atTop) (hd : 0 < d) (hq : 0 ≤ q)
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
theorem min_scaled {α : Type*} {l : Filter α} (W : α → ℝ) (M N : α → ℕ) {d : ℝ} (hW : Tendsto W l atTop)
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
def correctionMajorant (s : ℝ) : ℝ := π ^ 2 / (6 * (1 - π ^ 2 / (6 * s ^ 2)))
theorem kernel_correction_upper {s : ℝ} (hs : π ≤ s) : 0 ≤ s * (π / sin (π / s) - s) ∧
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
    have h : 1 ≤ t / sin t := (le_div_iff₀ hsin).mpr (by simpa only [one_mul] using sin_le ht0.le)
    linarith
  have hbound : t / sin t - 1 ≤ t ^ 2 / (6 * (1 - t ^ 2 / 6)) := by
    have hid : 1 / (1 - t ^ 2 / 6) - 1 = t ^ 2 / (6 * (1 - t ^ 2 / 6)) := by
      have hd' : 6 - t ^ 2 ≠ 0 := by nlinarith
      field_simp [hd.ne', hd'] <;> ring
    linarith
  have hid : s * (π / sin (π / s) - s) = s ^ 2 * (t / sin t - 1) := by
    dsimp [t]
    field_simp [hs0.ne', hsin.ne'] <;> ring
  rw [hid]
  constructor
  · exact mul_nonneg (sq_nonneg _) hnonneg
  · have hb := mul_le_mul_of_nonneg_left hbound (sq_nonneg s)
    convert hb using 1
    dsimp only [correctionMajorant, t]
    field_simp [hs0.ne'] <;> ring
theorem correction_majorant_limit : Tendsto correctionMajorant atTop (𝓝 (π ^ 2 / 6)) := by
  have hi : Tendsto (fun s : ℝ => 1 / s) atTop (𝓝 0) := tendsto_id.const_div_atTop 1
  have h := (tendsto_const_nhds (x := π ^ 2)).div (((tendsto_const_nhds (x := (1 : ℝ))).sub ((hi.pow 2).const_mul (π ^ 2 / 6))).const_mul 6)
    (by norm_num : 6 * (1 - π ^ 2 / 6 * 0 ^ 2) ≠ 0)
  norm_num only [zero_pow, mul_zero, sub_zero, one_mul] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
  change π ^ 2 / (6 * (1 - π ^ 2 / 6 * (1 / s) ^ 2)) = π ^ 2 / (6 * (1 - π ^ 2 / (6 * s ^ 2)))
  congr 1
  ring
end D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.KernelLimit
namespace D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.Tail
private lemma log_softplus_le_exp (v : ℝ) : log (1 + exp v) ≤ exp v := by
  simpa only [add_sub_cancel_left] using log_le_sub_one_of_pos (by positivity : 0 < 1 + exp v)
theorem finite_power_tail {s : ℝ} (hs : 1 < s) {N : ℕ} (hN : 0 < N) (S : Finset ℕ) (hS : ∀ n ∈ S, N < n) :
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
  have hsum : (∑ n ∈ Finset.Ioc N M, (n : ℝ) ^ (-s)) = ∑ n ∈ Finset.Ico N M, ((n + 1 : ℕ) : ℝ) ^ (-s) := by
    rw [← Finset.Ico_add_one_add_one_eq_Ioc, ← Finset.sum_Ico_add']
  calc
    _ ≤ ∑ n ∈ Finset.Ioc N M, (n : ℝ) ^ (-s) := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => rpow_nonneg (Nat.cast_nonneg _) _)
    _ = _ := hsum
    _ ≤ ∫ t in Ioi (N : ℝ), t ^ (-s) := hanti.sum_Ico_le_integral (integrableOn_Ioi_rpow_of_lt (by linarith) hN0)
        (fun t ht => rpow_nonneg (hN0.trans ht).le _)
    _ = (N : ℝ) ^ (1 - s) / (s - 1) := by
      rw [integral_Ioi_rpow_of_lt (by linarith : -s < -1) hN0]
      rw [show -s + 1 = 1 - s by ring]
      have h1 : s - 1 ≠ 0 := by linarith
      have h2 : 1 - s ≠ 0 := by linarith
      field_simp [h1, h2]
      ring
theorem small_weight_tail {P s : ℝ} (hP : 2 ≤ P) (hs : 0 ≤ s) (S : Finset ℕ) (hS : ∀ n ∈ S, 0 < n ∧ (n : ℝ) ≤ P / 2) :
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
  have hpoint (n : ℕ) (hn : n ∈ S) : log (1 + exp (-s * |log ((n : ℝ) / P)|)) ≤ (1 / 2 : ℝ) ^ s := by
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (hS n hn).1
    have hratio : (n : ℝ) / P ≤ 1 / 2 := (div_le_iff₀ hP0).mpr (by linarith [(hS n hn).2])
    have hl : log ((n : ℝ) / P) ≤ log (1 / 2 : ℝ) := log_le_log (div_pos hn0 hP0) hratio
    have hl0 : log ((n : ℝ) / P) ≤ 0 := log_nonpos (div_nonneg hn0.le hP0.le) (hratio.trans (by norm_num))
    refine (log_softplus_le_exp _).trans ?_
    rw [abs_of_nonpos hl0, neg_mul_neg, rpow_def_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    exact exp_le_exp.mpr (by nlinarith)
  calc
    _ ≤ ∑ n ∈ S, (1 / 2 : ℝ) ^ s := Finset.sum_le_sum hpoint
    _ = (S.card : ℝ) * (1 / 2 : ℝ) ^ s := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hcard (rpow_nonneg (by norm_num) _)
theorem large_weight_tail {P s : ℝ} (hP : 2 ≤ P) (hs : 2 ≤ s) (S : Finset ℕ) (hS : ∀ n ∈ S, 2 * P < (n : ℝ)) :
    ∑ n ∈ S, log (1 + exp (-s * |log ((n : ℝ) / P)|)) ≤ 2 * P * (2 / 3 : ℝ) ^ s := by
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
  have hpoint (n : ℕ) (hn : n ∈ S) : log (1 + exp (-s * |log ((n : ℝ) / P)|)) ≤ P ^ s * (n : ℝ) ^ (-s) := by
    have hn0 : (0 : ℝ) < n := by linarith [hS n hn]
    have hratio : 1 ≤ (n : ℝ) / P := (le_div_iff₀ hP0).mpr (by linarith [hS n hn])
    have hl : 0 ≤ log ((n : ℝ) / P) := log_nonneg hratio
    refine (log_softplus_le_exp _).trans_eq ?_
    rw [abs_of_nonneg hl, log_div hn0.ne' hP0.ne', rpow_def_of_pos hP0, rpow_def_of_pos hn0, ← exp_add]
    congr 1
    ring
  have hfinite := finite_power_tail (by linarith : 1 < s) hNN S hS'
  have hmono : (N : ℝ) ^ (1 - s) ≤ (3 * P / 2) ^ (1 - s) := rpow_le_rpow_of_nonpos (by positivity) hNlo (by linarith)
  have hid : P ^ s * (3 * P / 2) ^ (1 - s) = (3 * P / 2) * (2 / 3 : ℝ) ^ s := by
    rw [rpow_sub (by positivity), rpow_one]
    calc
      P ^ s * ((3 * P / 2) / (3 * P / 2) ^ s) = (3 * P / 2) * (P ^ s / (3 * P / 2) ^ s) := by ring
      _ = (3 * P / 2) * (P / (3 * P / 2)) ^ s := by
        rw [div_rpow hP0.le (by positivity)]
      _ = _ := by
        congr 2
        field_simp [hP0.ne'] <;> ring
  calc
    _ ≤ ∑ n ∈ S, P ^ s * (n : ℝ) ^ (-s) := Finset.sum_le_sum hpoint
    _ = P ^ s * ∑ n ∈ S, (n : ℝ) ^ (-s) := by rw [Finset.mul_sum]
    _ ≤ P ^ s * ((N : ℝ) ^ (1 - s) / (s - 1)) := mul_le_mul_of_nonneg_left hfinite (rpow_nonneg hP0.le _)
    _ ≤ P ^ s * ((3 * P / 2) ^ (1 - s) / (s - 1)) := mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right hmono (by linarith)) (rpow_nonneg hP0.le _)
    _ = ((3 * P / 2) * (2 / 3 : ℝ) ^ s) / (s - 1) := by rw [← mul_div_assoc, hid]
    _ ≤ (3 * P / 2) * (2 / 3 : ℝ) ^ s := div_le_self (by positivity) (by linarith)
    _ ≤ _ := by gcongr; linarith
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
namespace D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy
open D5.S3.Arith.Robin.PriceRecord.QuantitativePrimeAbel
open Exchange Entropy.KernelLimit
private lemma half_power (s : ℝ) : (1 / 2 : ℝ) ^ s = (2 : ℝ) ^ (-s) := by
  rw [div_rpow (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) ≤ 2), one_rpow, one_div, rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
/-- Explicit central quadrature and geometric-tail majorant. -/
def majorant (P s : ℝ) : ℝ := P / (s * log P) * correctionMajorant s + (s / 2 + 2) * P * (1 / 2 : ℝ) ^ s / log P + 112 * log 2 * (P / log P ^ 2) + P * (1 / 2 : ℝ) ^ s + 2 * P * (2 / 3 : ℝ) ^ s
/-- The finite prime remainder is controlled uniformly in the endpoint x. -/
theorem remainder_le_majorant : ∀ᶠ P : ℝ in atTop, ∀ s : ℝ, π ≤ s → 2 ≤ s → ∀ x : ℝ, remainder P s x ≤ majorant P s := by
  classical
  filter_upwards [Exchange.central_prime_weight_upper, eventually_ge_atTop (2 : ℝ)] with P hcentral hP
  intro s hsπ hs x
  have hP0 : 0 < P := by linarith
  have hl : 0 < log P := log_pos (by linarith)
  have hs0 : 0 < s := by linarith
  let S := Nat.primesLE ⌊x⌋₊
  let A := S.filter (fun p : ℕ => (p : ℝ) ≤ P / 2)
  let B := S.filter (fun p : ℕ => P / 2 < (p : ℝ) ∧ (p : ℝ) ≤ 2 * P)
  let C := S.filter (fun p : ℕ => 2 * P < (p : ℝ))
  have hpartition : remainder P s x = (∑ p ∈ A, weight P s p) + (∑ p ∈ B, weight P s p) + ∑ p ∈ C, weight P s p := by
    dsimp only [remainder, A, B, C, S]
    simp only [sum_filter]
    rw [← sum_add_distrib, ← sum_add_distrib]
    apply sum_congr rfl
    intro p hp
    by_cases hp1 : (p : ℝ) ≤ P / 2
    · have hp2 : ¬ 2 * P < (p : ℝ) := by linarith
      simp [hp1, hp2]
    · by_cases hp2 : (p : ℝ) ≤ 2 * P
      · simp [hp1, hp2, lt_of_not_ge hp1]
      · simp [hp1, hp2, lt_of_not_ge hp2]
  have hA : (∑ p ∈ A, weight P s p) ≤ P * (1 / 2 : ℝ) ^ s := by
    apply Entropy.Tail.small_weight_tail hP hs0.le A
    intro p hp
    obtain ⟨hpS, hpP⟩ := mem_filter.mp hp
    exact ⟨(Nat.mem_primesLE.mp hpS).2.pos, hpP⟩
  have hC : (∑ p ∈ C, weight P s p) ≤ 2 * P * (2 / 3 : ℝ) ^ s := by
    apply Entropy.Tail.large_weight_tail hP hs C
    intro p hp
    exact (mem_filter.mp hp).2
  have hsub : B ⊆ primeInterval (P / 2) (2 * P) := by
    intro p hp
    obtain ⟨hpS, hpL, hpU⟩ := mem_filter.mp hp
    refine mem_filter.mpr ⟨mem_Ioc.mpr ⟨?_, ?_⟩, (Nat.mem_primesLE.mp hpS).2⟩
    · exact (Nat.floor_lt (by positivity : 0 ≤ P / 2)).mpr hpL
    · exact (Nat.le_floor_iff (by positivity : 0 ≤ 2 * P)).mpr hpU
  have hB : (∑ p ∈ B, weight P s p) ≤ (∫ t in (P / 2)..(2 * P), weight P s t) / log P + 112 * log 2 * (P / log P ^ 2) := by
    exact (sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => weight_nonneg _ _ _)).trans
      (hcentral s hs0.le)
  have hi := Exchange.central_integral_upper hP0 (by linarith : 1 < s)
  have hi' := div_le_div_of_nonneg_right hi hl.le
  rw [← half_power s, add_div] at hi'
  have hk := (kernel_correction_upper hsπ).2
  have hk' : P * (π / sin (π / s) - s) / log P ≤ P / (s * log P) * correctionMajorant s := by
    have h := mul_le_mul_of_nonneg_left hk (div_nonneg hP0.le (mul_pos hs0 hl).le)
    convert h using 1 <;> field_simp [hs0.ne', hl.ne'] <;> ring
  rw [hpartition]
  dsimp only [majorant]
  have h := add_le_add (add_le_add hA hB) hC
  linarith only [h, hi', hk']
private lemma sharpness_top {c : ℝ} (hc : 0 < c) : Tendsto (fun P : ℝ => c * sqrt (log P)) atTop atTop := (tendsto_sqrt_atTop.comp tendsto_log_atTop).const_mul_atTop hc
/-- The explicit majorant has the sharp normalized upper coefficient. -/
theorem majorant_limit {c : ℝ} (hc : 0 < c) : Tendsto (fun P : ℝ => majorant P (c * sqrt (log P)) / (P / (log P * sqrt (log P)))) atTop (𝓝 (π ^ 2 / (6 * c))) := by
  have hhalf := (Entropy.Tail.geometric_sqrt_decay hc
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)).comp tendsto_log_atTop
  have hthird := (Entropy.Tail.geometric_sqrt_decay hc
    (by norm_num : (0 : ℝ) < 2 / 3) (by norm_num : (2 / 3 : ℝ) < 1)).comp tendsto_log_atTop
  have hsqrt : Tendsto (fun P : ℝ => 1 / sqrt (log P)) atTop (𝓝 0) := (tendsto_sqrt_atTop.comp tendsto_log_atTop).const_div_atTop 1
  have hlog : Tendsto (fun P : ℝ => 1 / log P) atTop (𝓝 0) := tendsto_log_atTop.const_div_atTop 1
  have hmain := (correction_majorant_limit.comp (sharpness_top hc)).div_const c
  have hcontinuum := hhalf.mul ((hsqrt.const_mul (c / 2)).add (hlog.const_mul 2))
  have hcount := hsqrt.const_mul (112 * log 2)
  have h := ((((hmain.add hcontinuum).add hcount).add hhalf).add (hthird.const_mul 2))
  norm_num only [mul_zero, zero_add, add_zero] at h
  convert h.congr' (show _ =ᶠ[atTop] _ from ?_) using 1
  · ring
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with P hP
    have hP0 : P ≠ 0 := by linarith
    have hl := log_pos hP
    have hs := sqrt_pos.mpr hl
    change correctionMajorant (c * sqrt (log P)) / c + (log P * sqrt (log P) * (1 / 2 : ℝ) ^ (c * sqrt (log P))) * (c / 2 * (1 / sqrt (log P)) + 2 * (1 / log P)) + 112 * log 2 * (1 / sqrt (log P)) + log P * sqrt (log P) * (1 / 2 : ℝ) ^ (c * sqrt (log P)) + 2 * (log P * sqrt (log P) * (2 / 3 : ℝ) ^ (c * sqrt (log P))) = majorant P (c * sqrt (log P)) / (P / (log P * sqrt (log P)))
    dsimp only [majorant]
    generalize hr : sqrt (log P) = r
    have hr0 : 0 < r := by rw [← hr]; exact hs
    have hr2 : r ^ 2 = log P := by rw [← hr]; exact sq_sqrt hl.le
    rw [← hr2]
    field_simp [hP0, hr0.ne', hc.ne'] <;> ring
/-- At square-root logarithmic sharpness, the finite prime remainder has the sharp upper coefficient pi squared divided by six c, uniformly in x. -/
theorem moving_weight_upper {c ε : ℝ} (hc : 0 < c) (hε : 0 < ε) : ∀ᶠ P : ℝ in atTop, ∀ x : ℝ, remainder P (c * sqrt (log P)) x ≤ (π ^ 2 / (6 * c) + ε) * (P / (log P * sqrt (log P))) := by
  filter_upwards [remainder_le_majorant, (sharpness_top hc).eventually_ge_atTop π, (sharpness_top hc).eventually_ge_atTop 2, (majorant_limit hc).eventually_lt_const (by linarith : π ^ 2 / (6 * c) < π ^ 2 / (6 * c) + ε), eventually_gt_atTop (1 : ℝ)] with P hbound hsπ hs hlimit hP
  intro x
  refine (hbound _ hsπ hs x).trans ?_
  have hscale : 0 < P / (log P * sqrt (log P)) := by
    have := log_pos hP
    positivity
  exact ((div_lt_iff₀ hscale).mp hlimit).le
end D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy
open D5.S3.Arith.Robin.PriceRecord.QuantitativePrimeAbel
open D5.S3.Arith.Robin.Analytic.OmegaTail.Selection
namespace D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy
open D5.S3.Arith.Robin.Analytic.OmegaTailUpper
open D5.S3.Arith.Robin.Analytic.OmegaSecond.Exchange
open D5.S3.Arith.Robin.Analytic.OmegaSecond.Exchange
/-- The finer counting scale at the second threshold. -/
def secondScale (x : ℝ) : ℝ := log x / (log (log x) * sqrt (log (log x)))
/-- The explicit saddle parameter as a function of the prime cutoff. -/
def saddle (P : ℝ) : ℝ := π / (2 * sqrt 3) * sqrt (log P)
/-- A fixed bound for the unweighted inverse Euler factors. -/
def eulerCost : ℝ := log (1 + ∑' n : ℕ, (n : ℝ) ^ (-2 : ℝ))
private lemma pseries_le_square {s : ℝ} (hs : 2 ≤ s) : (∑' n : ℕ, (n : ℝ) ^ (-s)) ≤ ∑' n : ℕ, (n : ℝ) ^ (-2 : ℝ) := by
  apply (Real.summable_nat_rpow.mpr (by linarith : -s < -1)).tsum_le_tsum ?_
    (Real.summable_nat_rpow.mpr (by norm_num : (-2 : ℝ) < -1))
  intro n
  by_cases hn : n = 0
  · subst n
    simp [Real.zero_rpow (by linarith : -s ≠ 0)]
  · apply Real.rpow_le_rpow_of_exponent_le
    · exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn)
    · linarith
/-- The strict integer tail is bounded by the exact prime budget and localized remainder, uniformly in every real Rankin parameter at least two. -/
theorem rankin_reduction {x s : ℝ} (hx : exp 1 < x) (hs : 2 ≤ s) : (tailCount 1 x : ℝ) ≤ exp (s * budget (log x) + remainder (log x) s x + eulerCost) := by
  have hx0 : 0 < x := (exp_pos 1).trans hx
  have hL : 1 < log x := (lt_log_iff_exp_lt hx0).mpr hx
  have hL0 : 0 < log x := zero_lt_one.trans hL
  have hs0 : 0 < s := by linarith
  have hz : 1 ≤ (log x) ^ s := Real.one_le_rpow hL.le hs0.le
  have h := rankin_exponential_bound (T := threshold 1 x) (by linarith : 1 < s) hz hx0
  have hprimes : ((Icc 1 ⌊x⌋₊).filter Nat.Prime) = Nat.primesLE ⌊x⌋₊ := by
    rw [Nat.primesLE_eq_filter_Ioc_zero]
    congr 1
  rw [hprimes, prime_weight_split hL0 (log_le_sub_one_of_pos hx0 |>.trans (by linarith)) hs0.le] at h
  have heq : s * log x - threshold 1 x * log ((log x) ^ s) + s * ((Nat.primeCounting ⌊log x⌋₊ : ℝ) * log (log x) - Chebyshev.theta (log x)) = s * budget (log x) := by
    rw [log_rpow hL0]
    dsimp only [threshold, scale, budget,
      D5.S3.Arith.Robin.PriceRecord.QuantitativePrimeAbel.primeCount]
    field_simp [(log_pos hL).ne'] <;> ring
  have hcost : log (1 + ∑' n : ℕ, (n : ℝ) ^ (-s)) ≤ eulerCost := by
    apply log_le_log
    · positivity
    · simpa only [add_comm] using add_le_add_left (pseries_le_square hs) 1
  change (tailCount 1 x : ℝ) ≤ _ at h
  refine h.trans (exp_le_exp.mpr ?_)
  linarith only [heq, hcost]
private lemma log_rpow_over_id_zero : Tendsto (fun P : ℝ => (log P * sqrt (log P)) / P) atTop (𝓝 0) := by
  have h := (isLittleO_log_rpow_rpow_atTop (3 / 2 : ℝ) (by norm_num : (0 : ℝ) < 1)).tendsto_div_nhds_zero
  apply h.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with P hP
  rw [rpow_one, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
    rpow_add (log_pos hP), rpow_one, ← sqrt_eq_rpow]
/-- The second-threshold counting scale diverges. -/
theorem secondScale_top : Tendsto secondScale atTop atTop := by
  have hp : ∀ᶠ P : ℝ in atTop, 0 < (log P * sqrt (log P)) / P := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with P hP
    exact div_pos (mul_pos (log_pos hP) (sqrt_pos.mpr (log_pos hP))) (by linarith)
  have h := tendsto_inv_nhdsGT_zero.comp (tendsto_nhdsWithin_iff.mpr ⟨log_rpow_over_id_zero, hp⟩)
  change Tendsto (fun x : ℝ => log x / (log (log x) * sqrt (log (log x)))) atTop atTop
  simpa only [inv_div, Function.comp_def] using h.comp tendsto_log_atTop
/-- The budget contribution at the explicit saddle has coefficient pi/sqrt(3). -/
theorem saddle_budget_limit : Tendsto (fun P : ℝ => saddle P * budget P / (P / (log P * sqrt (log P)))) atTop (𝓝 (π / sqrt 3)) := by
  have h := budget_limit.const_mul (π / (2 * sqrt 3))
  convert h.congr' (show (fun P : ℝ =>
      π / (2 * sqrt 3) * (budget P / (P / log P ^ 2))) =ᶠ[atTop]
        (fun P => saddle P * budget P / (P / (log P * sqrt (log P)))) from ?_) using 1
  · field_simp
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with P hP
    have hlog := log_pos hP
    dsimp only [saddle]
    generalize hr : sqrt (log P) = r
    have hr0 : 0 < r := by rw [← hr]; exact sqrt_pos.mpr hlog
    have hr2 : r ^ 2 = log P := by rw [← hr]; exact sq_sqrt hlog.le
    rw [← hr2]
    field_simp [(show P ≠ 0 by linarith), hr0.ne'] <;> ring
private lemma saddle_top : Tendsto saddle atTop atTop := by
  have hc : 0 < π / (2 * sqrt 3) := by positivity
  exact (tendsto_const_mul_atTop_of_pos hc).mpr
    (tendsto_sqrt_atTop.comp tendsto_log_atTop)
/-- At the second threshold the integer count has upper coefficient two pi over square root three on the finer logarithmic scale. -/
theorem upper : ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℝ in atTop, (tailCount 1 x : ℝ) ≤ exp ((2 * π / sqrt 3 + ε) * log x / (log (log x)) ^ (3 / 2 : ℝ)) := by
  intro ε hε
  have hc : 0 < π / (2 * sqrt 3) := by positivity
  have hb := saddle_budget_limit.comp tendsto_log_atTop
  have he := secondScale_top.const_div_atTop eulerCost
  have hsum := (hb.add he).eventually_lt_const (by linarith : π / sqrt 3 + 0 < π / sqrt 3 + ε / 2)
  have hR := tendsto_log_atTop.eventually (Entropy.moving_weight_upper hc (by linarith : 0 < ε / 2))
  have hcoef : π ^ 2 / (6 * (π / (2 * sqrt 3))) = π / sqrt 3 := by
    have hsqrt := sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
    have hp := pi_pos.ne'
    have hs := (sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3)).ne'
    field_simp [hp, hs]
    nlinarith
  filter_upwards [hsum, hR, (saddle_top.comp tendsto_log_atTop).eventually_ge_atTop 2, eventually_gt_atTop (exp 1)] with x hsum hR hs hx
  have hx0 : 0 < x := (exp_pos 1).trans hx
  have hL : 1 < log x := (lt_log_iff_exp_lt hx0).mpr hx
  have hell : 0 < log (log x) := log_pos hL
  have hscale : 0 < secondScale x := by dsimp [secondScale]; positivity
  have hfront : saddle (log x) * budget (log x) + eulerCost ≤ (π / sqrt 3 + ε / 2) * secondScale x := by
    have hsum' : (saddle (log x) * budget (log x) + eulerCost) / secondScale x < π / sqrt 3 + ε / 2 := by
      simpa only [secondScale, Function.comp_def, ← add_div] using hsum
    exact ((div_lt_iff₀ hscale).mp hsum').le
  have hrem : remainder (log x) (saddle (log x)) x ≤ (π / sqrt 3 + ε / 2) * secondScale x := by
    simpa only [saddle, secondScale, hcoef] using hR x
  refine (rankin_reduction hx hs).trans (exp_le_exp.mpr ?_)
  have heq : (log (log x)) ^ (3 / 2 : ℝ) = log (log x) * sqrt (log (log x)) := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, rpow_add hell,
      rpow_one, ← sqrt_eq_rpow]
  rw [heq, show (2 * π / sqrt 3 + ε) * log x /
      (log (log x) * sqrt (log (log x))) =
      (2 * π / sqrt 3 + ε) * secondScale x by dsimp [secondScale]; ring]
  simp only [Function.comp_def]
  calc
    _ = (saddle (log x) * budget (log x) + eulerCost) +
        remainder (log x) (saddle (log x)) x := by ring
    _ ≤ (π / sqrt 3 + ε / 2) * secondScale x +
        (π / sqrt 3 + ε / 2) * secondScale x := add_le_add hfront hrem
    _ = _ := by ring
/-- The integer strictly above the second threshold at the real prime center. -/
def thresholdK (P : ℝ) : ℕ := ⌊P / log P + P / log P ^ 2⌋₊ + 1
/-- The number of primes removed far below the active boxes. -/
def excess (P : ℝ) : ℕ := Nat.primeCounting ⌊P⌋₊ - thresholdK P
/-- The deterministic budget guaranteed after the remote deletion. -/
def coreBudget (P : ℝ) : ℝ := P - Chebyshev.theta P + (excess P : ℝ) * log (P / 2)
private lemma inverse_log_scale (n : ℕ) : Tendsto (fun P : ℝ => log P ^ n / P) atTop (𝓝 0) := by
  simpa only [rpow_natCast, rpow_one] using
    (isLittleO_log_rpow_rpow_atTop (n : ℝ)
      (by norm_num : (0 : ℝ) < 1)).tendsto_div_nhds_zero
private lemma rounding_error {P : ℝ} (hP : 1 < P) : 0 ≤ (thresholdK P : ℝ) - (P / log P + P / log P ^ 2) ∧ (thresholdK P : ℝ) - (P / log P + P / log P ^ 2) ≤ 1 := by
  have hPpos : 0 < P := zero_lt_one.trans hP
  have hlogpos := log_pos hP
  have hpos : 0 ≤ P / log P + P / log P ^ 2 := by positivity
  have hl := Nat.floor_le hpos
  have hu := Nat.lt_floor_add_one (P / log P + P / log P ^ 2)
  simp only [thresholdK, Nat.cast_add, Nat.cast_one]
  exact ⟨by linarith, by linarith⟩
private lemma rounding_scaled (n : ℕ) : Tendsto (fun P : ℝ => ((thresholdK P : ℝ) - (P / log P + P / log P ^ 2)) / (P / log P ^ n)) atTop (𝓝 0) := by
  apply squeeze_zero' _ _ (inverse_log_scale n)
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with P hP
    have hPpos : 0 < P := zero_lt_one.trans hP
    have hlogpos := log_pos hP
    exact div_nonneg (rounding_error hP).1 (by positivity)
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with P hP
    have hPpos : 0 < P := zero_lt_one.trans hP
    have hlogpos := log_pos hP
    have hscale : 0 < P / log P ^ n := by positivity
    calc
      _ ≤ 1 / (P / log P ^ n) := div_le_div_of_nonneg_right (rounding_error hP).2 hscale.le
      _ = _ := by rw [one_div_div]
private lemma excess_real_limit : Tendsto (fun P : ℝ => (D5.S3.Arith.Robin.PriceRecord.QuantitativePrimeAbel.primeCount P - thresholdK P) / (P / log P ^ 3)) atTop (𝓝 2) := by
  have hi : Tendsto (fun P : ℝ => 1 / log P) atTop (𝓝 0) := tendsto_log_atTop.const_div_atTop 1
  have h := ((prime_counting_three_terms.mul hi).add_const 2).sub (rounding_scaled 3)
  norm_num only [mul_zero, zero_add, sub_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with P hP
  dsimp only [countingThreeTerms]
  field_simp [(show P ≠ 0 by linarith), (log_pos hP).ne'] <;> ring
/-- There are eventually enough primes at the real center for the strict threshold. -/
theorem thresholdK_le_primeCount : ∀ᶠ P : ℝ in atTop, thresholdK P ≤ Nat.primeCounting ⌊P⌋₊ := by
  filter_upwards [excess_real_limit.eventually_const_lt (by norm_num : (0 : ℝ) < 2), eventually_gt_atTop (1 : ℝ)] with P h hP
  have hPpos : 0 < P := zero_lt_one.trans hP
  have hlogpos := log_pos hP
  have hscale : 0 < P / log P ^ 3 := by positivity
  have hd := (div_pos_iff_of_pos_right hscale).mp h
  change 0 < (Nat.primeCounting ⌊P⌋₊ : ℝ) - thresholdK P at hd
  exact_mod_cast (sub_pos.mp hd).le
/-- The remote deletion has asymptotic size 2P/log(P)^3. -/
theorem excess_limit : Tendsto (fun P : ℝ => (excess P : ℝ) / (P / log P ^ 3)) atTop (𝓝 2) := by
  apply excess_real_limit.congr'
  filter_upwards [thresholdK_le_primeCount] with P hP
  simp only [excess, Nat.cast_sub hP, D5.S3.Arith.Robin.PriceRecord.QuantitativePrimeAbel.primeCount]
/-- The cost saved by remote deletion has the same leading budget as Rankin's expression. -/
theorem coreBudget_limit : Tendsto (fun P : ℝ => coreBudget P / (P / log P ^ 2)) atTop (𝓝 2) := by
  have hi : Tendsto (fun P : ℝ => log 2 / log P) atTop (𝓝 0) := tendsto_log_atTop.const_div_atTop (log 2)
  have h := (budget_limit.sub (rounding_scaled 3)).sub (excess_limit.mul hi)
  norm_num only [sub_zero, mul_zero] at h
  apply h.congr'
  filter_upwards [thresholdK_le_primeCount, eventually_gt_atTop (1 : ℝ)] with P hk hP
  have hp : P ≠ 0 := by linarith
  rw [coreBudget, log_div hp (by norm_num : (2 : ℝ) ≠ 0)]
  dsimp only [budget, excess, D5.S3.Arith.Robin.PriceRecord.QuantitativePrimeAbel.primeCount]
  rw [Nat.cast_sub hk]
  field_simp [hp, (log_pos hP).ne'] <;> ring
/-- A reserve separated from every fixed active logarithmic box. -/
def reserve (P : ℝ) : Finset ℕ := primeInterval (P / 2) (3 * P / 4)
private lemma reserve_limit : Tendsto (fun P : ℝ => ((reserve P).card : ℝ) / (P / log P)) atTop (𝓝 (1 / 4 : ℝ)) := by
  have hi : Tendsto (fun P : ℝ => 56 / log P) atTop (𝓝 0) := tendsto_log_atTop.const_div_atTop 56
  have he : Tendsto (fun P : ℝ => ((reserve P).card : ℝ) / (P / log P) - 1 / 4) atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ hi
    filter_upwards [central_prime_counting_bound, eventually_gt_atTop (1 : ℝ)] with P h hP
    have hp : 0 < P := by linarith
    have hl := log_pos hP
    have h1 := h (P / 2) ⟨le_rfl, by linarith⟩
    have h2 := h (3 * P / 4) ⟨by linarith, by linarith⟩
    have heq := primeInterval_card (show P / 2 ≤ 3 * P / 4 by linarith)
    change ((reserve P).card : ℝ) = _ at heq
    rw [Real.norm_eq_abs, heq]
    have habs : |(primeCount (3 * P / 4) - primeCount (P / 2)) - P / (4 * log P)| ≤ 56 * (P / log P ^ 2) := by
      have htri := abs_sub (primeCount (3 * P / 4) - (3 * P / 4) / log P) (primeCount (P / 2) - (P / 2) / log P)
      have hid : (primeCount (3 * P / 4) - (3 * P / 4) / log P) - (primeCount (P / 2) - (P / 2) / log P) = (primeCount (3 * P / 4) - primeCount (P / 2)) - P / (4 * log P) := by ring
      rw [hid] at htri
      linarith
    have hid : (primeCount (3 * P / 4) - primeCount (P / 2)) / (P / log P) - 1 / 4 = ((primeCount (3 * P / 4) - primeCount (P / 2)) - P / (4 * log P)) / (P / log P) := by
      field_simp [hp.ne', hl.ne'] <;> ring
    rw [hid, abs_div, abs_of_pos (div_pos hp hl)]
    apply (div_le_iff₀ (div_pos hp hl)).mpr
    convert habs using 1 <;> field_simp [hl.ne'] <;> ring
  have h := he.add_const (1 / 4 : ℝ)
  simpa only [sub_add_cancel, zero_add] using h
private lemma reserve_enough : ∀ᶠ P : ℝ in atTop, excess P ≤ (reserve P).card := by
  have hi : Tendsto (fun P : ℝ => 1 / log P ^ 2) atTop (𝓝 0) := by
    simpa only [one_div_pow, zero_pow (by decide : (2 : ℕ) ≠ 0)] using ((tendsto_log_atTop.const_div_atTop 1).pow 2)
  have hr : Tendsto (fun P : ℝ => (excess P : ℝ) / (P / log P)) atTop (𝓝 0) := by
    have h := excess_limit.mul hi
    norm_num only [mul_zero] at h
    apply h.congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with P hP
    field_simp [(show P ≠ 0 by linarith), (log_pos hP).ne'] <;> ring
  filter_upwards [hr.eventually_lt reserve_limit (by norm_num : (0 : ℝ) < 1 / 4), eventually_gt_atTop (1 : ℝ)] with P h hP
  have hPpos : 0 < P := zero_lt_one.trans hP
  have hlogpos := log_pos hP
  have hscale : 0 < P / log P := by positivity
  exact_mod_cast ((div_lt_div_iff_of_pos_right hscale).mp h).le
/-- A remote deletion gives an actual prime base with the exact threshold size and the deterministic logarithmic budget. -/
private theorem trimmed_core : ∀ᶠ P : ℝ in atTop, ∃ R : Finset ℕ, R ⊆ reserve P ∧ R.card = excess P ∧ (Nat.primesLE ⌊P⌋₊ \ R).card = thresholdK P ∧ (∑ p ∈ Nat.primesLE ⌊P⌋₊ \ R, log (p : ℝ)) ≤ P - coreBudget P := by
  filter_upwards [reserve_enough, thresholdK_le_primeCount, eventually_gt_atTop (1 : ℝ)] with P hR hk hP
  obtain ⟨R, hsub, hcard⟩ := exists_subset_card_eq hR
  have hsub' : R ⊆ Nat.primesLE ⌊P⌋₊ := by
    intro p hp
    obtain ⟨hmem, hprime⟩ := mem_filter.mp (hsub hp)
    apply Nat.mem_primesLE.mpr
    exact ⟨(mem_Ioc.mp hmem).2.trans (Nat.floor_mono (by linarith : 3 * P / 4 ≤ P)), hprime⟩
  refine ⟨R, hsub, hcard, ?_, ?_⟩
  · rw [card_sdiff_of_subset hsub', Nat.primesLE_card_eq_primeCounting, hcard, excess]
    omega
  · have hsum : (∑ p ∈ R, log (p : ℝ)) +
        (∑ p ∈ Nat.primesLE ⌊P⌋₊ \ R, log (p : ℝ)) = Chebyshev.theta P := by
      rw [add_comm, sum_sdiff hsub', Chebyshev.theta_eq_sum_primesLE]
    have hsumlo : (excess P : ℝ) * log (P / 2) ≤ ∑ p ∈ R, log (p : ℝ) := by
      rw [← hcard]
      calc
        _ = ∑ _p ∈ R, log (P / 2) := by simp
        _ ≤ _ := by
          apply sum_le_sum
          intro p hp
          have hpmem := (mem_Ioc.mp (mem_filter.mp (hsub hp)).1).1
          exact log_le_log (by positivity : 0 < P / 2) (Nat.lt_of_floor_lt hpmem).le
    dsimp only [coreBudget]
    linarith
/-- Width scale of a fixed logarithmic prime box at a moving saddle. -/
def boxScale (c P : ℝ) : ℝ := P / (log P * (c * sqrt (log P)))
private lemma boxScale_top {c : ℝ} (hc : 0 < c) : Tendsto (boxScale c) atTop atTop := by
  have h : Tendsto (fun P : ℝ => P / (log P * sqrt (log P))) atTop atTop := by
    have hp : ∀ᶠ P : ℝ in atTop, 0 < (log P * sqrt (log P)) / P := by
      filter_upwards [eventually_gt_atTop (1 : ℝ)] with P hP
      have hPpos : 0 < P := zero_lt_one.trans hP
      have hlogpos := log_pos hP
      positivity
    have h := tendsto_inv_nhdsGT_zero.comp (tendsto_nhdsWithin_iff.mpr ⟨log_rpow_over_id_zero, hp⟩)
    simpa only [inv_div, Function.comp_def] using h
  convert h.atTop_div_const hc using 1
  ext P
  dsimp only [boxScale]
  ring
private lemma exp_saddle_difference {c : ℝ} (hc : 0 < c) (t : ℝ) : Tendsto (fun P : ℝ => (exp (t / (c * sqrt (log P))) - 1) * (c * sqrt (log P))) atTop (𝓝 t) := by
  have hs : Tendsto (fun P : ℝ => c * sqrt (log P)) atTop atTop := (tendsto_sqrt_atTop.comp tendsto_log_atTop).const_mul_atTop hc
  by_cases ht : t = 0
  · subst t
    simp
  have hi : Tendsto (fun P : ℝ => t / (c * sqrt (log P))) atTop (𝓝[≠] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hs.const_div_atTop t, ?_⟩
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with P hP
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    exact div_ne_zero ht (mul_ne_zero hc.ne' (sqrt_pos.mpr (log_pos hP)).ne')
  have h := ((hasDerivAt_exp (0 : ℝ)).tendsto_slope_zero.comp hi).mul_const t
  norm_num only [exp_zero, one_mul] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with P hP
  simp only [Function.comp_def, zero_add, smul_eq_mul]
  field_simp [ht, hc.ne', (sqrt_pos.mpr (log_pos hP)).ne'] <;> ring
private lemma central_endpoint {c : ℝ} (hc : 0 < c) (t : ℝ) : ∀ᶠ P : ℝ in atTop, P * exp (t / (c * sqrt (log P))) ∈ Set.Icc (P / 2) (2 * P) := by
  have hs : Tendsto (fun P : ℝ => c * sqrt (log P)) atTop atTop := (tendsto_sqrt_atTop.comp tendsto_log_atTop).const_mul_atTop hc
  have he := (hs.const_div_atTop t).rexp
  rw [exp_zero] at he
  filter_upwards [he.eventually_const_lt (by norm_num : (1 / 2 : ℝ) < 1), he.eventually_lt_const (by norm_num : (1 : ℝ) < 2), eventually_gt_atTop (1 : ℝ)] with P hlo hhi hP
  have hp : 0 < P := by linarith
  constructor <;> nlinarith
private lemma box_count_limit {c a b : ℝ} (hc : 0 < c) (hab : a ≤ b) : Tendsto (fun P : ℝ => ((primeInterval (P * exp (a / (c * sqrt (log P)))) (P * exp (b / (c * sqrt (log P))))).card : ℝ) / boxScale c P) atTop (𝓝 (b - a)) := by
  let A (P : ℝ) := P * exp (a / (c * sqrt (log P)))
  let B (P : ℝ) := P * exp (b / (c * sqrt (log P)))
  have hm := (exp_saddle_difference hc b).sub (exp_saddle_difference hc a)
  have hi : Tendsto (fun P : ℝ => 56 * c / sqrt (log P)) atTop (𝓝 0) := (tendsto_sqrt_atTop.comp tendsto_log_atTop).const_div_atTop (56 * c)
  have he : Tendsto (fun P : ℝ => (((primeInterval (A P) (B P)).card : ℝ) - (B P - A P) / log P) / boxScale c P) atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ hi
    filter_upwards [central_prime_counting_bound, central_endpoint hc a, central_endpoint hc b, eventually_gt_atTop (1 : ℝ)] with P h ha hb hP
    have hp : 0 < P := by linarith
    have hl := log_pos hP
    have hr := sqrt_pos.mpr hl
    have hab' : A P ≤ B P := by
      dsimp only [A, B]
      gcongr
    have hcard := primeInterval_card hab'
    have h1 := h (A P) ha
    have h2 := h (B P) hb
    have herror : |((primeInterval (A P) (B P)).card : ℝ) - (B P - A P) / log P| ≤ 56 * (P / log P ^ 2) := by
      rw [hcard]
      have ht := abs_sub (primeCount (B P) - B P / log P) (primeCount (A P) - A P / log P)
      have hid : (primeCount (B P) - B P / log P) - (primeCount (A P) - A P / log P) = (primeCount (B P) - primeCount (A P)) - (B P - A P) / log P := by ring
      rw [hid] at ht
      linarith
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (show 0 < boxScale c P by dsimp [boxScale]; positivity)]
    apply (div_le_iff₀ (show 0 < boxScale c P by dsimp [boxScale]; positivity)).mpr
    convert herror using 1
    dsimp only [boxScale]
    have hh := sq_sqrt hl.le
    field_simp [hp.ne', hl.ne', hr.ne']
    nlinarith
  have h := he.add hm
  simp only [zero_add] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with P hP
  dsimp only [A, B, boxScale]
  field_simp [(show P ≠ 0 by linarith), (log_pos hP).ne', hc.ne',
    (sqrt_pos.mpr (log_pos hP)).ne'] <;> ring
/-- Prime boxes below and above the real center, with half-open endpoints. -/
def negativeBox (G : Exchange.Mesh) (c P : ℝ) (i : Fin G.n) : Finset ℕ := primeInterval (P * exp (-G.node (i + 1) / (c * sqrt (log P)))) (P * exp (-G.node i / (c * sqrt (log P))))
def positiveBox (G : Exchange.Mesh) (c P : ℝ) (i : Fin G.n) : Finset ℕ := primeInterval (P * exp (G.node i / (c * sqrt (log P)))) (P * exp (G.node (i + 1) / (c * sqrt (log P))))
def capacity (G : Exchange.Mesh) (c P : ℝ) (i : Fin G.n) : ℕ := min (negativeBox G c P i).card (positiveBox G c P i).card
def occupancy (G : Exchange.Mesh) (c P : ℝ) (i : Fin G.n) : ℕ := ⌊Exchange.logistic (G.node (i + 1)) * (capacity G c P i : ℝ)⌋₊
def exchangeCost (G : Exchange.Mesh) (c P : ℝ) : ℝ := (2 / (c * sqrt (log P))) * ∑ i, G.node (i + 1) * (occupancy G c P i : ℝ)
def entropyEstimate (G : Exchange.Mesh) (c P : ℝ) : ℝ := 2 * ∑ i, Entropy.entropyLower (capacity G c P i) (occupancy G c P i)
private lemma mesh_node_mono (G : Exchange.Mesh) : Monotone G.node := by
  intro i j hij
  dsimp [Exchange.Mesh.node]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hij) (Exchange.step_pos G).le
private lemma capacity_limit (G : Exchange.Mesh) {c : ℝ} (hc : 0 < c) (i : Fin G.n) : Tendsto (fun P : ℝ => (capacity G c P i : ℝ) / boxScale c P) atTop (𝓝 G.step) := by
  have hn := box_count_limit hc (neg_le_neg (mesh_node_mono G (Nat.le_succ (i : ℕ))))
  have hp := box_count_limit hc (mesh_node_mono G (Nat.le_succ (i : ℕ)))
  have hn' : Tendsto (fun P : ℝ => ((negativeBox G c P i).card : ℝ) / boxScale c P) atTop (𝓝 G.step) := by
    convert hn using 1
    dsimp only [negativeBox]
    all_goals simp only [neg_sub_neg, Exchange.node_step]
  have hp' : Tendsto (fun P : ℝ => ((positiveBox G c P i).card : ℝ) / boxScale c P) atTop (𝓝 G.step) := by
    simpa only [positiveBox, Exchange.node_step] using hp
  exact Entropy.min_scaled _ _ _ (boxScale_top hc) hn' hp'
private lemma occupancy_fits (G : Exchange.Mesh) (c P : ℝ) (i : Fin G.n) : occupancy G c P i ≤ capacity G c P i := by
  have hq0 : 0 ≤ Exchange.logistic (G.node (i + 1)) := by dsimp [Exchange.logistic]; positivity
  have hq1 : Exchange.logistic (G.node (i + 1)) ≤ 1 := by
    dsimp [Exchange.logistic]
    exact (inv_lt_one_of_one_lt₀ (by linarith [exp_pos (G.node (i+1))])).le
  have h := Nat.floor_le (mul_nonneg hq0 (Nat.cast_nonneg (capacity G c P i)))
  have h' : (occupancy G c P i : ℝ) ≤ capacity G c P i := by
    exact h.trans (by nlinarith [Nat.cast_nonneg (capacity G c P i)])
  exact_mod_cast h'
private lemma occupancy_limit (G : Exchange.Mesh) {c : ℝ} (hc : 0 < c) (i : Fin G.n) : Tendsto (fun P : ℝ => (occupancy G c P i : ℝ) / boxScale c P) atTop (𝓝 (G.step * Exchange.logistic (G.node (i + 1)))) := by
  simpa only [occupancy, mul_comm] using Entropy.floor_scaled (boxScale c)
    (fun P => capacity G c P i) (boxScale_top hc) (Exchange.step_pos G)
    (show 0 ≤ Exchange.logistic (G.node (i+1)) by dsimp [Exchange.logistic]; positivity)
    (capacity_limit G hc i)
private lemma entropyEstimate_limit (G : Exchange.Mesh) {c : ℝ} (hc : 0 < c) : Tendsto (fun P : ℝ => entropyEstimate G c P / boxScale c P) atTop (𝓝 G.mass) := by
  have h := (tendsto_finset_sum univ (fun i (_ : i ∈ (univ : Finset (Fin G.n))) => Entropy.entropy_lower_scaled (boxScale c) (fun P => capacity G c P i) (fun P => occupancy G c P i) (boxScale_top hc) (Exchange.step_pos G) (capacity_limit G hc i) (occupancy_limit G hc i))).const_mul 2
  convert h using 1
  · ext P
    dsimp only [entropyEstimate]
    rw [mul_div_assoc, sum_div]
  · dsimp only [Exchange.Mesh.mass]
    rw [← Fin.sum_univ_eq_sum_range]
    rfl
private lemma exchangeCost_limit (G : Exchange.Mesh) {c : ℝ} (hc : 0 < c) : Tendsto (fun P : ℝ => exchangeCost G c P / coreBudget P) atTop (𝓝 (G.cost / (2 * c ^ 2))) := by
  have hsum := tendsto_finset_sum univ (fun i (_ : i ∈ (univ : Finset (Fin G.n))) => (occupancy_limit G hc i).const_mul (G.node (i + 1)))
  have h := ((hsum.const_mul (2 / c ^ 2)).div coreBudget_limit (by norm_num : (2 : ℝ) ≠ 0))
  convert h.congr' (show (fun P : ℝ =>
      (2 / c ^ 2 * ∑ i : Fin G.n, G.node (i+1) *
        ((occupancy G c P i : ℝ) / boxScale c P)) / (coreBudget P / (P / log P ^ 2)))
      =ᶠ[atTop] (fun P => exchangeCost G c P / coreBudget P) from ?_) using 1
  · dsimp only [Exchange.Mesh.cost]
    rw [← Fin.sum_univ_eq_sum_range]
    rw [mul_sum]
    ring
  · filter_upwards [eventually_gt_atTop (1 : ℝ),
      coreBudget_limit.eventually_const_lt (by norm_num : (0 : ℝ) < 2)] with P hP hD
    have hPpos : 0 < P := zero_lt_one.trans hP
    have hl := log_pos hP
    have hr := sqrt_pos.mpr hl
    have hDpos : 0 < coreBudget P := (div_pos_iff_of_pos_right (show 0 < P / log P ^ 2 by positivity)).mp hD
    dsimp only [boxScale, exchangeCost]
    simp_rw [← mul_div_assoc]
    rw [← sum_div]
    have hr2 := sq_sqrt hl.le
    field_simp [(show P ≠ 0 by linarith), hl.ne', hc.ne', hr.ne', hDpos.ne']
    nlinarith
private lemma entropyEstimate_le_log_choices (G : Exchange.Mesh) (c P : ℝ) : entropyEstimate G c P ≤ log (∏ i : Fin G.n, ((capacity G c P i).choose (occupancy G c P i)) ^ 2 : ℕ) := by
  have hp (i : Fin G.n) : (0 : ℝ) < (capacity G c P i).choose (occupancy G c P i) := by
    exact_mod_cast Nat.choose_pos (occupancy_fits G c P i)
  rw [Nat.cast_prod, log_prod (fun i _ => by push_cast; positivity)]
  simp_rw [Nat.cast_pow, log_pow]
  dsimp only [entropyEstimate, Entropy.entropyLower]
  rw [mul_sum]
  apply sum_le_sum
  intro i _
  exact mul_le_mul_of_nonneg_left
    (Entropy.log_choose_ge_binEntropy _ _ (occupancy_fits G c P i)) (by norm_num)
/-- Each accuracy is achieved by one grid fixed independently of the prime center. -/
theorem fixed_grid_exists (ε : ℝ) (hε : 0 < ε) : ∃ c : ℝ, 0 < c ∧ ∃ G : Exchange.Mesh, ∀ᶠ P : ℝ in atTop, exchangeCost G c P ≤ coreBudget P ∧ (2 * π / sqrt 3 - ε) * (P / (log P * sqrt (log P))) ≤ log (∏ i : Fin G.n, ((capacity G c P i).choose (occupancy G c P i)) ^ 2 : ℕ) := by
  let K : ℝ := 2 * π / sqrt 3
  let c₀ : ℝ := π / (2 * sqrt 3)
  let η : ℝ := ε / (8 * K)
  let ρ : ℝ := ε * c₀ / 8
  have hK : 0 < K := by dsimp [K]; positivity
  have hc₀ : 0 < c₀ := by dsimp [c₀]; positivity
  have hη : 0 < η := by dsimp [η]; positivity
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  obtain ⟨G, hcost, hmass⟩ := Exchange.exists_good_grid hη hρ
  let c : ℝ := (1 + η) * c₀
  have hc : 0 < c := by dsimp [c]; positivity
  have hA : 2 * c ^ 2 = (π ^ 2 / 6) * (1 + η) ^ 2 := by
    dsimp [c, c₀]
    have hs := sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
    field_simp
    nlinarith
  have hstrict : G.cost / (2 * c ^ 2) < 1 := by
    apply (div_lt_one (by positivity : 0 < 2 * c ^ 2)).mpr
    rw [hA]
    have hpi : 0 < π ^ 2 / 6 := by positivity
    have hgap : 1 + η / 2 < (1 + η) ^ 2 := by nlinarith
    exact hcost.trans_lt (mul_lt_mul_of_pos_left hgap hpi)
  have hBc : π ^ 2 / 3 = K * c₀ := by
    dsimp [K, c₀]
    have hs := sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
    field_simp
    nlinarith
  have hηK : K * η = ε / 8 := by dsimp [η]; field_simp; ring
  have hcoef : K - ε / 2 < G.mass / c := by
    apply (lt_div_iff₀ hc).mpr
    have haux : (K - ε / 2) * (1 + η) < K - ε / 8 := by
      nlinarith [mul_pos hε hη]
    have haux' := mul_lt_mul_of_pos_right haux hc₀
    dsimp only [c]
    rw [hBc] at hmass
    dsimp only [ρ] at hmass
    nlinarith
  have he : Tendsto (fun P : ℝ => entropyEstimate G c P / (P / (log P * sqrt (log P)))) atTop (𝓝 (G.mass / c)) := by
    apply ((entropyEstimate_limit G hc).div_const c).congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with P hP
    dsimp only [boxScale]
    field_simp [hc.ne', (log_pos hP).ne',
      (sqrt_pos.mpr (log_pos hP)).ne', (show P ≠ 0 by linarith)] <;> ring
  refine ⟨c, hc, G, ?_⟩
  filter_upwards [(exchangeCost_limit G hc).eventually_lt_const hstrict, coreBudget_limit.eventually_const_lt (by norm_num : (0 : ℝ) < 2), he.eventually_const_lt (show K - ε < G.mass / c by linarith), eventually_gt_atTop (1 : ℝ)] with P hV hD hE hP
  have hp : 0 < P := zero_lt_one.trans hP
  have hl := log_pos hP
  have hscale : 0 < P / (log P * sqrt (log P)) := by positivity
  have hDpos : 0 < coreBudget P := (div_pos_iff_of_pos_right (show 0 < P / log P ^ 2 by positivity)).mp hD
  constructor
  · exact ((div_lt_one hDpos).mp hV).le
  · change (K - ε) * (P / (log P * sqrt (log P))) ≤ _
    exact ((lt_div_iff₀ hscale).mp hE).le.trans (entropyEstimate_le_log_choices G c P)
private lemma choices_le_tail (G : Exchange.Mesh) {c : ℝ} (hc : 0 < c) : ∀ᶠ P : ℝ in atTop, exchangeCost G c P ≤ coreBudget P → (∏ i : Fin G.n, ((capacity G c P i).choose (occupancy G c P i)) ^ 2 : ℕ) ≤ tailCount 1 (exp P) := by
  have hs : Tendsto (fun P : ℝ => c * sqrt (log P)) atTop atTop := (tendsto_sqrt_atTop.comp tendsto_log_atTop).const_mul_atTop hc
  have hf := (hs.const_div_atTop (-G.node G.n)).rexp
  rw [exp_zero] at hf
  filter_upwards [trimmed_core, hf.eventually_const_lt (by norm_num : (3 / 4 : ℝ) < 1), eventually_gt_atTop (1 : ℝ)] with P hcore hfar hP
  intro hV
  obtain ⟨R, hR, hcard, hsize, hbase⟩ := hcore
  have hp : 0 < P := zero_lt_one.trans hP
  have hl := log_pos hP
  have hspos : 0 < c * sqrt (log P) := by positivity
  have hfar' : 3 * P / 4 ≤ P * exp (-G.node G.n / (c * sqrt (log P))) := by nlinarith
  have hthreshold : threshold 1 (exp P) < ((Nat.primesLE ⌊P⌋₊ \ R).card : ℝ) := by
    rw [hsize]
    have h := Nat.lt_floor_add_one (P / log P + P / log P ^ 2)
    simpa only [threshold, scale, log_exp, thresholdK, Nat.cast_add, Nat.cast_one,
      one_mul, div_div, pow_two] using h
  have hcount := Exchange.logarithmic_exchange_bound G.n P (c * sqrt (log P)) G.node R hp hspos (mesh_node_mono G) (by simp [Exchange.Mesh.node]) hfar' hR (occupancy G c P) (coreBudget P) 1 (exp P) hbase hV hthreshold (by rw [log_exp]) (exp_pos P)
  apply le_trans _ hcount
  apply prod_le_prod'
  intro i _
  have hn := Nat.choose_le_choose (occupancy G c P i) (min_le_left (negativeBox G c P i).card (positiveBox G c P i).card)
  have hp' := Nat.choose_le_choose (occupancy G c P i) (min_le_right (negativeBox G c P i).card (positiveBox G c P i).card)
  simpa only [pow_two, capacity, negativeBox, positiveBox] using Nat.mul_le_mul hn hp'
/-- The lower coefficient at the strict second distinct-prime threshold. -/
theorem lower : ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℝ in atTop, (2 * π / sqrt 3 - ε) * log x / (log (log x)) ^ (3 / 2 : ℝ) ≤ log (tailCount 1 x : ℝ) := by
  intro ε hε
  obtain ⟨c, hc, G, hgrid⟩ := fixed_grid_exists ε hε
  have hP : ∀ᶠ P : ℝ in atTop, (2 * π / sqrt 3 - ε) * (P / (log P * sqrt (log P))) ≤ log (tailCount 1 (exp P) : ℝ) := by
    filter_upwards [hgrid, choices_le_tail G hc] with P hgrid hcount
    have hchoose : 0 < (∏ i : Fin G.n, ((capacity G c P i).choose (occupancy G c P i)) ^ 2 : ℕ) := by
      exact prod_pos (fun i _ => pow_pos (Nat.choose_pos (occupancy_fits G c P i)) _)
    exact hgrid.2.trans (log_le_log (by exact_mod_cast hchoose)
      (by exact_mod_cast hcount hgrid.1))
  filter_upwards [tendsto_log_atTop.eventually hP, eventually_gt_atTop (exp 1)] with x hx hx1
  have hx0 : 0 < x := (exp_pos 1).trans hx1
  have hell : 0 < log (log x) := log_pos ((lt_log_iff_exp_lt hx0).mpr hx1)
  rw [exp_log hx0] at hx
  rw [show (log (log x)) ^ (3 / 2 : ℝ) = log (log x) * sqrt (log (log x)) by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, rpow_add hell,
      rpow_one, ← sqrt_eq_rpow]]
  simpa only [mul_div_assoc] using hx
/-- The exact second-threshold logarithmic counting limit. -/
theorem result : Tendsto (fun x : ℝ => log (tailCount 1 x : ℝ) / (log x / (log (log x)) ^ (3 / 2 : ℝ))) atTop (𝓝 (2 * π / sqrt 3)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hK : 0 < 2 * π / sqrt 3 := by positivity
  filter_upwards [lower (ε / 2) (by positivity), lower (π / sqrt 3) (by positivity), upper (ε / 2) (by positivity), eventually_gt_atTop (exp 1)] with x hlo hpositive hup hx
  have hx0 : 0 < x := (exp_pos 1).trans hx
  have hL : 1 < log x := (lt_log_iff_exp_lt hx0).mpr hx
  have hell : 0 < log (log x) := log_pos hL
  have hy : 0 < log x / (log (log x)) ^ (3 / 2 : ℝ) := div_pos (zero_lt_one.trans hL) (rpow_pos_of_pos hell _)
  have hn : 0 < (tailCount 1 x : ℝ) := by
    by_contra h
    have hz : (tailCount 1 x : ℝ) = 0 := le_antisymm (le_of_not_gt h) (Nat.cast_nonneg _)
    rw [hz, log_zero] at hpositive
    have hp := mul_pos (show 0 < 2 * π / sqrt 3 - π / sqrt 3 by positivity) hy
    rw [mul_div_assoc] at hpositive
    linarith
  have hlog := log_le_log hn hup
  rw [log_exp, mul_div_assoc] at hlog
  rw [mul_div_assoc] at hlo
  have hhi := (div_le_iff₀ hy).mpr hlog
  have hlo' := (le_div_iff₀ hy).mpr hlo
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith
end D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy
