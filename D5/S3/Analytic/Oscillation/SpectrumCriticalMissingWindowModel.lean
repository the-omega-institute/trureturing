/- GID: D5/S3/Analytic/Oscillation/SpectrumCriticalMissingWindowModel
   generality: G
   mirror-B: D5/B/S3/Analytic/Oscillation/SpectrumCriticalMissingWindowModel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Fourth-root intervals give an infinite spectrum with small square tail. -/

import D5.S3.Analytic.Oscillation.SpectrumCriticalMissingWindow
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Analysis.PSeries

/-! An infinite realization of the critical missing-window hypotheses. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter Set
open scoped Topology BigOperators

namespace D5.S3.Analytic.Oscillation.SpectrumCriticalMissingWindowModel

open OrdinateCounting (Spectrum)
open SpectrumPhaseCutoff (mass mem_cut)
open SpectrumCriticalMissingWindow (HasLogSquaredMass HasSmallSquareTail)

private theorem rational_scale_into {v l h : ℝ} (hv : v ≠ 0) (hl : 0 < l) (hlh : l < h) :
    ∃ q : ℚˣ, l < q • v ∧ q • v < h := by
  have hav : 0 < |v| := abs_pos.mpr hv
  obtain ⟨q, hql, hqh⟩ := exists_rat_btwn (div_lt_div_of_pos_right hlh hav)
  have hlo := (div_lt_iff₀ hav).mp hql
  have hhi := (lt_div_iff₀ hav).mp hqh
  have hq : q ≠ 0 := by
    intro he
    rw [he, Rat.cast_zero, zero_mul] at hlo
    exact (not_lt_of_ge hl.le) hlo
  let c : ℚˣ := Units.mk0 q hq
  by_cases hp : 0 ≤ v
  · exact ⟨c, by simpa [c, Rat.smul_def, abs_of_nonneg hp] using hlo,
      by simpa [c, Rat.smul_def, abs_of_nonneg hp] using hhi⟩
  · have he (k : ℚˣ) : (-k) • v = ((k : ℚ) : ℝ) * |v| := by
      change (((-k : ℚˣ) : ℚ) : ℝ) * v = _
      simp [abs_of_neg (lt_of_not_ge hp)]
    exact ⟨-c, by simpa only [he, c, Units.val_mk0] using hlo,
      by simpa only [he, c, Units.val_mk0] using hhi⟩

theorem exists_independent_bins :
    ∃ g : ℕ → ℝ, LinearIndependent ℚ g ∧
      ∀ n, 0 < g n ∧ (n : ℝ) + 1 < g n ^ 4 ∧ g n ^ 4 < (n : ℝ) + 2 := by
  let b := Module.Free.chooseBasis ℚ ℝ
  have hcard : Cardinal.mk ℕ ≤ Cardinal.mk (Module.Free.ChooseBasisIndex ℚ ℝ) := by
    rw [← Module.Free.rank_eq_card_chooseBasisIndex, Real.rank_rat_real, Cardinal.mk_nat]
    exact Cardinal.aleph0_le_continuum
  obtain ⟨e⟩ := (Cardinal.le_def _ _).mp hcard
  let f : ℕ → ℝ := b ∘ e
  have hf : LinearIndependent ℚ f := b.linearIndependent.comp e e.injective
  have hchoice (n : ℕ) : ∃ q : ℚˣ,
      ((n : ℝ) + 1) ^ (4 : ℝ)⁻¹ < q • f n ∧ q • f n < ((n : ℝ) + 2) ^ (4 : ℝ)⁻¹ :=
    rational_scale_into (hf.ne_zero n) (by positivity)
      (Real.rpow_lt_rpow (by positivity) (by linarith) (by norm_num))
  choose q hq using hchoice
  refine ⟨q • f, hf.units_smul q, fun n => ?_⟩
  rcases hq n with ⟨hl, hh⟩
  change 0 < q n • f n ∧ (n : ℝ) + 1 < (q n • f n) ^ 4 ∧
    (q n • f n) ^ 4 < (n : ℝ) + 2
  have hpos : 0 < q n • f n := (by positivity : 0 < ((n : ℝ) + 1) ^ (4 : ℝ)⁻¹).trans hl
  refine ⟨hpos, ?_, ?_⟩
  · have h := Real.rpow_lt_rpow (by positivity) hl (by norm_num : (0 : ℝ) < 4)
    rw [Real.rpow_inv_rpow (by positivity) (by norm_num : (4 : ℝ) ≠ 0)] at h
    simpa only [Real.rpow_ofNat] using h
  · have h := Real.rpow_lt_rpow hpos.le hh (by norm_num : (0 : ℝ) < 4)
    rw [Real.rpow_inv_rpow (by positivity) (by norm_num : (4 : ℝ) ≠ 0)] at h
    simpa only [Real.rpow_ofNat] using h

def modelWeight (n : ℕ) : ℝ :=
  Real.log ((n : ℝ) + 2) ^ 2 - Real.log ((n : ℝ) + 1) ^ 2

theorem modelWeight_pos (n : ℕ) : 0 < modelWeight n := by
  unfold modelWeight
  have hl := Real.log_lt_log (by positivity : 0 < (n : ℝ) + 1)
    (show (n : ℝ) + 1 < (n : ℝ) + 2 by linarith)
  have h₀ := Real.log_nonneg (show 1 ≤ (n : ℝ) + 1 by linarith only [Nat.cast_nonneg (α := ℝ) n])
  exact sub_pos.mpr (pow_lt_pow_left₀ hl h₀ (by omega : (2 : ℕ) ≠ 0))

private theorem sum_modelWeight (n : ℕ) :
    ∑ j ∈ Finset.range n, modelWeight j = Real.log ((n : ℝ) + 1) ^ 2 := by
  have h := Finset.sum_range_sub (fun j : ℕ => Real.log ((j : ℝ) + 1) ^ 2) n
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_add, add_assoc,
    show (1 : ℝ) + 1 = 2 by norm_num, Real.log_one] at h
  norm_num at h
  simpa only [modelWeight, Finset.sum_sub_distrib] using h

abbrev modelSpectrum (g : ℕ → ℝ)
    (hg : ∀ n, 0 < g n ∧ (n : ℝ) + 1 < g n ^ 4 ∧ g n ^ 4 < (n : ℝ) + 2)
    (hinj : Function.Injective g) : Spectrum where
  index := ℕ
  gamma := g
  mult := fun _ => 1
  gamma_pos n := (hg n).1
  gamma_injective := hinj
  mult_pos _ := Nat.one_pos
  finite_le T := by
    apply (Set.finite_Iio (⌊T ^ 4⌋₊ + 1)).subset
    intro n (hn : g n ≤ T)
    have h : (n : ℝ) ≤ T ^ 4 :=
      (by linarith only [(hg n).2.1] : (n : ℝ) ≤ g n ^ 4).trans
        (pow_le_pow_left₀ (hg n).1.le hn _)
    exact Nat.lt_succ_of_le ((Nat.le_floor_iff (by positivity)).mpr h)

theorem eventually_model_mass (g : ℕ → ℝ)
    (hg : ∀ n, 0 < g n ∧ (n : ℝ) + 1 < g n ^ 4 ∧ g n ^ 4 < (n : ℝ) + 2)
    (hinj : Function.Injective g) :
    HasLogSquaredMass (modelSpectrum g hg hinj) modelWeight := by
  let S := modelSpectrum g hg hinj
  have hmono : StrictMono g := by
    intro i j hij
    have hij' : (i : ℝ) + 2 ≤ (j : ℝ) + 1 := by
      have hn : (i : ℝ) + 1 ≤ j := by exact_mod_cast (Nat.succ_le_of_lt hij)
      linarith
    have hpow := ((hg i).2.2.trans_le hij').trans (hg j).2.1
    exact lt_of_not_ge fun h => (not_lt_of_ge (pow_le_pow_left₀ (hg j).1.le h 4)) hpow
  have hcut (T : ℝ) (n : ℕ) : n ∈ S.cut T ↔ g n ≤ T :=
    mem_cut
  refine ⟨16, 9, by norm_num, by norm_num, ?_⟩
  filter_upwards [eventually_ge_atTop (max 1 (g 0))] with T hT
  have hT₁ : 1 ≤ T := (le_max_left _ _).trans hT
  have hTpos := zero_lt_one.trans_le hT₁
  have hc : (S.cut T).Nonempty := ⟨0, (hcut T 0).mpr ((le_max_right _ _).trans hT)⟩
  let n := (S.cut T).max' hc
  have hn : n ∈ S.cut T := Finset.max'_mem _ _
  have hn1 : T < g (n + 1) := by
    apply lt_of_not_ge
    intro h
    exact (Nat.not_succ_le_self n) (Finset.le_max' _ _ ((hcut _ _).mpr h))
  have hrange : S.cut T = Finset.range (n + 1) := by
    ext j
    rw [Finset.mem_range, Nat.lt_succ_iff]
    exact ⟨fun h => Finset.le_max' _ _ h,
      fun h => (hcut _ _).mpr ((hmono.monotone h).trans ((hcut _ _).mp hn))⟩
  have hlo : (n : ℝ) + 1 < T ^ 4 :=
    (hg n).2.1.trans_le (pow_le_pow_left₀ (hg n).1.le ((hcut _ _).mp hn) _)
  have hhi : T ^ 4 < (n : ℝ) + 3 := by
    have h := (pow_lt_pow_left₀ hn1 hTpos.le (by omega : (4 : ℕ) ≠ 0)).trans (hg (n + 1)).2.2
    push_cast at h
    linarith only [h]
  have hlowLog := Real.log_le_log (show 0 < T ^ 4 by positivity)
    (show T ^ 4 ≤ 2 * ((n : ℝ) + 2) by linarith [Nat.cast_nonneg (α := ℝ) n])
  have hhighLog := Real.log_le_log (show 0 < (n : ℝ) + 2 by positivity)
    (show (n : ℝ) + 2 ≤ 2 * T ^ 4 by linarith [Nat.cast_nonneg (α := ℝ) n])
  rw [Real.log_pow, Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by positivity)] at hlowLog
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by positivity), Real.log_pow] at hhighLog
  have hlog2 := Real.log_le_sub_one_of_pos (show 0 < (2 : ℝ) by norm_num)
  have hdiff : |Real.log ((n : ℝ) + 2) - 4 * Real.log T| ≤ 1 := by
    apply abs_le.mpr
    constructor <;> norm_num at hlowLog hhighLog hlog2 ⊢ <;> linarith
  have hlogn := Real.log_nonneg (show 1 ≤ (n : ℝ) + 2 by linarith only [Nat.cast_nonneg (α := ℝ) n])
  have hlogT := Real.log_nonneg hT₁
  change |mass S modelWeight T - 16 * Real.log T ^ 2| ≤ 9 * (1 + Real.log T)
  rw [mass, hrange, sum_modelWeight, Nat.cast_add, Nat.cast_one, add_assoc,
    show (1 : ℝ) + 1 = 2 by norm_num]
  rw [show Real.log ((n : ℝ) + 2) ^ 2 - 16 * Real.log T ^ 2 =
    (Real.log ((n : ℝ) + 2) - 4 * Real.log T) *
      (Real.log ((n : ℝ) + 2) + 4 * Real.log T) by ring,
    abs_mul, abs_of_nonneg (by positivity : 0 ≤ Real.log ((n : ℝ) + 2) + 4 * Real.log T)]
  calc
    _ ≤ 1 * (Real.log ((n : ℝ) + 2) + 4 * Real.log T) := by gcongr
    _ ≤ _ := by linarith only [(abs_le.mp hdiff).2, hlogT]

private theorem modelWeight_bound (n : ℕ) :
    modelWeight n ≤ 32 * ((n : ℝ) + 1) ^ (-(7 / 8) : ℝ) := by
  let x : ℝ := (n : ℝ) + 1
  have hx : 0 < x := by dsimp [x]; positivity
  have hx1 : 1 ≤ x := by dsimp [x]; linarith only [Nat.cast_nonneg (α := ℝ) n]
  have hlogmono := Real.log_le_log hx (le_add_of_nonneg_right (show 0 ≤ (1 : ℝ) by norm_num))
  have hdiff : Real.log (x + 1) - Real.log x ≤ 1 / x := by
    have hh := Real.log_le_sub_one_of_pos (show 0 < (x + 1) / x by positivity)
    rw [Real.log_div (by positivity : x + 1 ≠ 0) hx.ne',
      show (x + 1) / x - 1 = 1 / x by field_simp; ring] at hh
    exact hh
  have hpow : 1 ≤ x ^ (1 / 8 : ℝ) := Real.one_le_rpow hx1 (by norm_num)
  have hlog2 := Real.log_le_sub_one_of_pos (show 0 < (2 : ℝ) by norm_num)
  have hlog : Real.log (x + 1) ≤ 16 * x ^ (1 / 8 : ℝ) := by
    calc
      _ ≤ Real.log (2 * x) := Real.log_le_log (by positivity) (by linarith)
      _ = Real.log 2 + Real.log x := Real.log_mul (by norm_num) hx.ne'
      _ ≤ _ := by
        have h := Real.log_le_rpow_div hx.le (show (0 : ℝ) < 1 / 8 by norm_num)
        linarith
  rw [modelWeight, show (n : ℝ) + 2 = x + 1 by dsimp [x]; ring]
  change Real.log (x + 1) ^ 2 - Real.log x ^ 2 ≤ 32 * x ^ (-(7 / 8) : ℝ)
  calc
    _ = (Real.log (x + 1) - Real.log x) * (Real.log (x + 1) + Real.log x) := by ring
    _ ≤ (1 / x) * (32 * x ^ (1 / 8 : ℝ)) := by
      apply mul_le_mul hdiff _ _ (by positivity)
      · linarith
      · exact add_nonneg (Real.log_nonneg (by linarith)) (Real.log_nonneg hx1)
    _ = _ := by
      rw [div_mul_eq_mul_div, one_mul, mul_div_assoc, ← Real.rpow_sub_one hx.ne']
      congr 1
      norm_num

private theorem summable_model_square :
    Summable (fun n : ℕ => ((n : ℝ) + 1) ^ (1 / 2 : ℝ) * modelWeight n ^ 2) := by
  have hs : Summable (fun n : ℕ => (n : ℝ) ^ (-(5 / 4) : ℝ)) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  have hs' : Summable (fun n : ℕ => (32 : ℝ) ^ 2 * ((n : ℝ) + 1) ^ (-(5 / 4) : ℝ)) := by
    have hh := ((summable_nat_add_iff 1).mpr hs).mul_left ((32 : ℝ) ^ 2)
    simpa only [Nat.cast_add, Nat.cast_one] using hh
  apply hs'.of_nonneg_of_le (fun n => by positivity)
  intro n
  have hx : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  calc
    _ ≤ ((n : ℝ) + 1) ^ (1 / 2 : ℝ) * (32 * ((n : ℝ) + 1) ^ (-(7 / 8) : ℝ)) ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (modelWeight_pos n).le (modelWeight_bound n) _)
        (by positivity)
    _ = _ := by
      have he : (((n : ℝ) + 1) ^ (-(7 / 8) : ℝ)) ^ 2 =
          ((n : ℝ) + 1) ^ (-(7 / 4) : ℝ) := by
        rw [← Real.rpow_ofNat, ← Real.rpow_mul hx.le]
        norm_num
      rw [mul_pow, he, ← mul_assoc, mul_comm (((n : ℝ) + 1) ^ (1 / 2 : ℝ)),
        mul_assoc, ← Real.rpow_add hx]
      norm_num

theorem model_square_tail_bound (g : ℕ → ℝ)
    (hg : ∀ n, 0 < g n ∧ (n : ℝ) + 1 < g n ^ 4 ∧ g n ^ 4 < (n : ℝ) + 2)
    (hinj : Function.Injective g) :
    let S := modelSpectrum g hg hinj
    ∃ B : ℝ, 0 < B ∧ ∀ (decEq : DecidableEq ℕ) (X T : ℝ), 1 ≤ X →
      ∑ n ∈ @SDiff.sdiff _ (@Finset.instSDiff ℕ decEq) (S.cut T) (S.cut X),
        modelWeight n ^ 2 ≤ B / X ^ 2 := by
  let S := modelSpectrum g hg hinj
  let f (n : ℕ) := ((n : ℝ) + 1) ^ (1 / 2 : ℝ) * modelWeight n ^ 2
  let C := ∑' n, f n
  have hsum : Summable f := summable_model_square
  have hf (n : ℕ) : 0 ≤ f n := by dsimp [f]; positivity
  have hC : 0 ≤ C := tsum_nonneg hf
  refine ⟨2 * C + 1, by linarith, ?_⟩
  intro decEq X T hX
  let tail : Finset ℕ := @SDiff.sdiff _ (@Finset.instSDiff ℕ decEq) (S.cut T) (S.cut X)
  have hXpos := zero_lt_one.trans_le hX
  have hbound (n : ℕ) (hn : n ∈ tail) : X ^ 2 ≤ 2 * ((n : ℝ) + 1) ^ (1 / 2 : ℝ) := by
    have hXn : X < g n := by
      exact lt_of_not_ge fun h =>
        ((@Finset.mem_sdiff ℕ decEq _ _ _).mp hn).2 (mem_cut.mpr h)
    have h4 : X ^ 4 ≤ 4 * ((n : ℝ) + 1) := by
      have hh := (pow_lt_pow_left₀ hXn hXpos.le (by omega : (4 : ℕ) ≠ 0)).trans (hg n).2.2
      linarith only [hh, Nat.cast_nonneg (α := ℝ) n]
    have hp : (((n : ℝ) + 1) ^ (1 / 2 : ℝ)) ^ 2 = (n : ℝ) + 1 := by
      rw [← Real.rpow_ofNat, ← Real.rpow_mul (by positivity),
        show (1 / 2 : ℝ) * (2 : ℝ) = 1 by norm_num, Real.rpow_one]
    apply le_of_not_gt
    intro h
    have hh := pow_lt_pow_left₀ h
      (show 0 ≤ 2 * ((n : ℝ) + 1) ^ (1 / 2 : ℝ) by positivity) (by omega : (2 : ℕ) ≠ 0)
    rw [mul_pow, hp, ← pow_mul] at hh
    norm_num at hh
    linarith
  have htail : X ^ 2 * ∑ n ∈ tail, modelWeight n ^ 2 ≤ 2 * C := by
    calc
      _ = ∑ n ∈ tail, X ^ 2 * modelWeight n ^ 2 := Finset.mul_sum _ _ _
      _ ≤ ∑ n ∈ tail, 2 * f n :=
        Finset.sum_le_sum fun n hn => by
          change X ^ 2 * modelWeight n ^ 2 ≤
            2 * (((n : ℝ) + 1) ^ (1 / 2 : ℝ) * modelWeight n ^ 2)
          rw [← mul_assoc]
          exact mul_le_mul_of_nonneg_right (hbound n hn) (sq_nonneg _)
      _ = 2 * ∑ n ∈ tail, f n := (Finset.mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (hsum.sum_le_tsum tail fun n _ => hf n) (by norm_num)
  change (∑ n ∈ tail, modelWeight n ^ 2) ≤ (2 * C + 1) / X ^ 2
  apply (le_div_iff₀ (sq_pos_of_pos hXpos)).mpr
  rw [mul_comm]
  exact htail.trans (le_add_of_nonneg_right zero_le_one)

private theorem eventually_model_tail (g : ℕ → ℝ)
    (hg : ∀ n, 0 < g n ∧ (n : ℝ) + 1 < g n ^ 4 ∧ g n ^ 4 < (n : ℝ) + 2)
    (hinj : Function.Injective g) :
    HasSmallSquareTail (modelSpectrum g hg hinj) modelWeight := by
  obtain ⟨B, hB, hbound⟩ := model_square_tail_bound g hg hinj
  intro η hη
  filter_upwards [eventually_ge_atTop (B / η),
    Real.tendsto_log_atTop.eventually_ge_atTop 1, eventually_ge_atTop (1 : ℝ)]
    with X hXbig hlog hX
  intro T _
  have hXpos := zero_lt_one.trans_le hX
  have hBdiv : B / X ≤ η := (div_le_iff₀ hXpos).mpr
    (by simpa only [mul_comm] using (div_le_iff₀ hη).mp hXbig)
  have hlog₂ : 1 ≤ Real.log X ^ 2 := by
    simpa using pow_le_pow_left₀ zero_le_one hlog 2
  refine (hbound (fun a b => Classical.propDecidable (a = b)) X T hX).trans ?_
  rw [pow_two, ← div_div]
  exact div_le_div_of_nonneg_right
    (hBdiv.trans (le_mul_of_one_le_right hη.le hlog₂)) hXpos.le

/-- The endpoint hypotheses hold on an infinite spectrum with every weight strictly positive. -/
theorem exists_infinite_critical_model :
    ∃ (S : Spectrum) (w : S.index → ℝ), Infinite S.index ∧
      (∀ j, 0 < w j) ∧ LinearIndependent ℚ S.gamma ∧
      HasLogSquaredMass S w ∧ HasSmallSquareTail S w := by
  obtain ⟨g, hli, hg⟩ := exists_independent_bins
  let S := modelSpectrum g hg hli.injective
  exact ⟨S, modelWeight, inferInstanceAs (Infinite ℕ), modelWeight_pos, hli,
    eventually_model_mass g hg hli.injective, eventually_model_tail g hg hli.injective⟩

#print axioms exists_infinite_critical_model

end D5.S3.Analytic.Oscillation.SpectrumCriticalMissingWindowModel
