/- GID: D5/S3/Estimation/TimeArrow/MarkedPoissonEventComparison
   generality: G
   mirror-B: D5/B/S3/Estimation/TimeArrow/MarkedPoissonEventComparison
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Genuine product Poisson moments control both actual directions and every marked-count event. -/

import D5.S3.Estimation.TimeArrow.ActualReverseMarkedPath
import D5.S3.Estimation.TimeArrow.ArbitraryMarkedCountPoissonRelative
import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.Real

open Finset MeasureTheory ProbabilityTheory
open scoped NNReal Classical
open D5.S3.Estimation.SequentialDecisionRisk.FiniteSupportSelectionBayes
open D5.S3.Estimation.TimeArrow.ActualMarkedPathPgfPoissonEnvelope
open D5.S3.Estimation.TimeArrow.MarkedHistoryAlgebra
open D5.S3.Estimation.TimeArrow.ActualReverseMarkedPath
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace D5.S3.Estimation.TimeArrow.MarkedPoissonEventComparison

/-- Independent Poisson coordinates, with a genuine probability measure on all count tuples. -/
def poissonProduct {ι : Type*} [Fintype ι] (μ : ι → ℝ≥0) : Measure (ι → ℕ) :=
  Measure.pi (fun i => poissonMeasure (μ i))

private theorem poisson_two_moment (μ : ℝ≥0) :
    Integrable (fun n : ℕ => (2 : ℝ) ^ n) (poissonMeasure μ) ∧
      (∫ n : ℕ, (2 : ℝ) ^ n ∂poissonMeasure μ) = Real.exp μ := by
  have hseries : HasSum (fun n : ℕ =>
      Real.exp (-(μ : ℝ)) * (μ : ℝ) ^ n / n.factorial * 2 ^ n) (Real.exp μ) := by
    have hh := (NormedSpace.expSeries_div_hasSum_exp (2 * (μ : ℝ))).mul_left
      (Real.exp (-(μ : ℝ)))
    convert hh using 1
    · funext n
      simp only [smul_eq_mul, mul_pow]
      ring
    · rw [← Real.exp_eq_exp_ℝ, ← Real.exp_add]
      congr 1
      ring
  constructor
  · apply integrable_poissonMeasure_iff.mpr
    convert hseries.summable using 1
    funext n
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (2 : ℝ) ^ n)]
  · rw [integral_poissonMeasure]
    simpa only [smul_eq_mul] using hseries.tsum_eq

private theorem poisson_product_two_moment {ι : Type*} [Fintype ι] (μ : ι → ℝ≥0) :
    Integrable (fun n : ι → ℕ => (2 : ℝ) ^ (∑ i, n i)) (poissonProduct μ) ∧
      (∫ n : ι → ℕ, (2 : ℝ) ^ (∑ i, n i) ∂poissonProduct μ) =
        Real.exp (∑ i, (μ i : ℝ)) := by
  have he (n : ι → ℕ) : (2 : ℝ) ^ (∑ i, n i) = ∏ i, (2 : ℝ) ^ n i := by
    exact (prod_pow_eq_pow_sum _ _ _).symm
  constructor
  · simp_rw [he]
    exact Integrable.fintype_prod fun i => (poisson_two_moment (μ i)).1
  · simp_rw [he]
    rw [poissonProduct, integral_fintype_prod_eq_prod]
    simp_rw [(poisson_two_moment _).2]
    exact (Real.exp_sum _ _).symm

/-- A uniform exponential tail for the sum of genuinely independent Poisson coordinates. -/
theorem product_poisson_tail {ι : Type*} [Fintype ι] (μ : ι → ℝ≥0) (B : ℕ) :
    (poissonProduct μ).real {n | B < ∑ i, n i} ≤
      Real.exp (∑ i, (μ i : ℝ)) / (2 : ℝ) ^ B := by
  classical
  let ν := poissonProduct μ
  haveI : IsProbabilityMeasure ν := by dsimp [ν, poissonProduct]; infer_instance
  have hmoment := poisson_product_two_moment μ
  have hm := mul_meas_ge_le_integral_of_nonneg (μ := ν)
    (f := fun n : ι → ℕ => (2 : ℝ) ^ (∑ i, n i))
    (Filter.Eventually.of_forall fun n => by positivity) hmoment.1 ((2 : ℝ) ^ B)
  have hsub : {n : ι → ℕ | B < ∑ i, n i} ⊆
      {n | (2 : ℝ) ^ B ≤ (2 : ℝ) ^ (∑ i, n i)} := by
    intro n hn
    exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hn.le
  have hmono := measureReal_mono (μ := ν) hsub
  rw [le_div_iff₀ (by positivity : 0 < (2 : ℝ) ^ B)]
  calc
    _ ≤ (2 : ℝ) ^ B * ν.real {n | (2 : ℝ) ^ B ≤ (2 : ℝ) ^ (∑ i, n i)} := by
      simpa [mul_comm] using mul_le_mul_of_nonneg_left hmono (by positivity : 0 ≤ (2 : ℝ) ^ B)
    _ ≤ _ := hm.trans_eq hmoment.2

private theorem finite_weighted_tail {Ω : Type*} [Fintype Ω]
    (w : Ω → ℝ) (hw : ∀ o, 0 ≤ w o) (N : Ω → ℕ) (B : ℕ) :
    (∑ o, if B < N o then w o else 0) ≤
      (∑ o, w o * (2 : ℝ) ^ N o) / (2 : ℝ) ^ B := by
  classical
  rw [le_div_iff₀ (by positivity : 0 < (2 : ℝ) ^ B), sum_mul]
  apply sum_le_sum
  intro o _
  split_ifs with h
  · exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) h.le) (hw o)
  · simp only [zero_mul]
    exact mul_nonneg (hw o) (by positivity)

private def markedVector {M s k : ℕ} (e : Experiment) (m : Fin k → Fin M)
    (o : Obs M s e) : (Fin k ⊕ Fin k) → ℕ
  | .inl j => count e o (m j) 1
  | .inr j => count e o (m j) (-1)

private theorem reverse_two_moment {M q s k : ℕ} {r : ℝ}
    (hM64 : 64 ≤ M) (hq : 1 ≤ q) (hqm : q < M) (hr : 0 < r) (hr1 : r < 1)
    (hc1 : compensation M q r < 1) (hk : k = 1 ∨ k = 2)
    (S : Support M q) (m : Fin k → Fin M) (hm : Function.Injective m) (e : Experiment)
    (hsmall : (s : ℝ) / (M : ℝ) ^ 2 ≤ 1 / 256) :
    (∑ o : Obs M s e, reverseProbability r e S o *
      (2 : ℝ) ^ (∑ i, markedVector e m o i)) ≤
      2 * Real.exp ((k : ℝ) * ((s : ℝ) / (2 * M))) := by
  classical
  have hM : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hMc : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  let η : ℝ := 1 / M
  have hη : 0 ≤ η := by dsimp [η]; positivity
  have hη1 : η ≤ 1 / 64 := by
    dsimp [η]
    apply (div_le_iff₀ hM).mpr
    have hh : (64 : ℝ) ≤ M := by exact_mod_cast hM64
    linarith
  have hT : (s : ℝ) * η ^ 2 ≤ 1 / 256 := by simpa [η, div_pow, div_eq_mul_inv] using hsmall
  have hc : 0 ≤ compensation M q r := by unfold compensation; positivity
  have hb (j : Fin k) : ‖(b r S (.inl (m j)) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    dsimp [b]
    split_ifs
    · rw [abs_of_pos hr]; exact hr1.le
    · rw [abs_neg, abs_of_nonneg hc]; exact hc1.le
  have hA : reverseA (M := M) (fun _ : Fin k => 2) (fun _ => 2) = (k : ℂ) / (2 * M) := by
    simp [reverseA, tiltU] <;> ring
  have hG : reverseG (M := M) (fun _ : Fin k => 2) (fun _ => 2) = 0 := by
    simp [reverseG, tiltV]
  have hE : reverseE r S m (fun _ => 2) (fun _ => 2) = 0 := by
    simp [reverseE, tiltV]
  have hAbound : ‖(k : ℂ) / (2 * M)‖ ≤ η := by
    rw [norm_div, Complex.norm_natCast, norm_mul, Complex.norm_natCast]
    norm_num
    apply (div_le_iff₀ (by positivity : 0 < 2 * (M : ℝ))).mpr
    have he : η * (2 * M) = 2 := by dsimp [η]; field_simp
    rw [he]
    rcases hk with rfl | rfl <;> norm_num
  have hDbound : ‖reverseD r S m (fun _ => 2) (fun _ => 2)‖ ≤ η := by
    simp only [reverseD, tiltU]
    norm_num
    have hsum := marked_sum_norm hk 1 (by norm_num) (fun j => (b r S (.inl (m j)) : ℂ)) hb
    apply (div_le_iff₀ (by positivity : 0 < 2 * (M : ℝ))).mpr
    have he : η * (2 * M) = 2 := by dsimp [η]; field_simp
    rw [he]
    simpa only [mul_one] using hsum
  have hh := actual_reverse_marked_poisson_envelope hq hqm hr hr1 hc1 S m hm
    (fun _ => 2) (fun _ => 2) e hη hη1 (by simpa [hA] using hAbound)
    (by simpa [hG] using hη) hDbound (by simpa [hE] using hη) hT
  let P : ℝ := ∑ o : Obs M s e, reverseProbability r e S o *
    (2 : ℝ) ^ (∑ i, markedVector e m o i)
  have hPGF : reversePGF r S m (fun _ => 2) (fun _ => 2) s e = (P : ℂ) := by
    dsimp [reversePGF, P]
    push_cast
    apply sum_congr rfl
    intro o _
    rw [Fintype.sum_sum_type, pow_add, ← prod_pow_eq_pow_sum, ← prod_pow_eq_pow_sum,
      ← prod_mul_distrib]
    rfl
  have hmean : (s : ℂ) * reverseA (M := M) (fun _ : Fin k => 2) (fun _ => 2) =
      (((k : ℝ) * ((s : ℝ) / (2 * M)) : ℝ) : ℂ) := by
    rw [hA]
    push_cast
    ring
  rw [hPGF, hmean, ← Complex.ofReal_exp, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs] at hh
  have hreal : (s : ℝ) * (reverseA (M := M) (fun _ : Fin k => 2) (fun _ => 2)).re =
      (k : ℝ) * ((s : ℝ) / (2 * M)) := by
    have h := congrArg Complex.re hmean
    simpa only [Complex.ofReal_re, Complex.mul_re, Complex.natCast_re,
      Complex.natCast_im, zero_mul, sub_zero] using h
  rw [hreal] at hh
  have hpow : 0 ≤ Real.exp ((k : ℝ) * ((s : ℝ) / (2 * M))) := (Real.exp_pos _).le
  have hcoef : 80 * (s : ℝ) * η ^ 2 ≤ 1 := by nlinarith
  have hbound := mul_le_mul_of_nonneg_right hcoef hpow
  have hupper := (abs_le.mp hh).2
  change P ≤ _
  nlinarith

/-- Actual transpose histories and their exact-mean independent Poisson comparison have one
uniform total-count tail bound, for both experiments and all marked support memberships. -/
theorem actual_reverse_marked_count_tail {M q s k : ℕ} {r : ℝ}
    (hM64 : 64 ≤ M) (hq : 1 ≤ q) (hqm : q < M) (hr : 0 < r) (hr1 : r < 1)
    (hc1 : compensation M q r < 1) (hk : k = 1 ∨ k = 2)
    (S : Support M q) (m : Fin k → Fin M) (hm : Function.Injective m) (e : Experiment)
    (hsmall : (s : ℝ) / (M : ℝ) ^ 2 ≤ 1 / 256) (B : ℕ) :
    let L := (s : ℝ) / (2 * M)
    let μ : (Fin k ⊕ Fin k) → ℝ≥0 := fun _ => ⟨L / 2, by positivity⟩
    (∑ o : Obs M s e,
      if B < ∑ j, (count e o (m j) 1 + count e o (m j) (-1))
      then reverseProbability r e S o else 0) +
      (poissonProduct μ).real {n | B < ∑ i, n i} ≤
      3 * Real.exp ((k : ℝ) * L) / (2 : ℝ) ^ B := by
  classical
  intro L μ
  have hc : 0 ≤ compensation M q r := by unfold compensation; positivity
  have hK := ((finite_support_bayes (s := s) hq hqm hr hr1 hc hc1 e).1 S).1.1
  have hw (o : Obs M s e) : 0 ≤ reverseProbability r e S o := by
    cases e with
    | pair => exact prod_nonneg fun t _ => mul_nonneg (by positivity) (hK _ _)
    | path => exact mul_nonneg (by positivity) (prod_nonneg fun t _ => hK _ _)
  have ht := finite_weighted_tail (reverseProbability r e S) hw (fun o => ∑ i, markedVector e m o i) B
  have hmom := reverse_two_moment hM64 hq hqm hr hr1 hc1 hk S m hm e hsmall
  have htail := product_poisson_tail μ B
  have hsum : (∑ i, (μ i : ℝ)) = (k : ℝ) * L := by
    change (∑ _ : Fin k ⊕ Fin k, L / 2) = (k : ℝ) * L
    simp only [sum_const, card_univ, Fintype.card_sum, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    ring
  rw [hsum] at htail
  have hcount (o : Obs M s e) : (∑ i, markedVector e m o i) =
      ∑ j, (count e o (m j) 1 + count e o (m j) (-1)) := by
    simp [Fintype.sum_sum_type, markedVector, sum_add_distrib]
  simp_rw [hcount] at ht hmom
  have hmom' := div_le_div_of_nonneg_right hmom (show 0 ≤ (2 : ℝ) ^ B by positivity)
  change _ ≤ _
  have h := add_le_add (ht.trans hmom') htail
  convert h using 1 <;> ring


private theorem finite_history_event_comparison {Ω X : Type*} [Fintype Ω]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    (w : Ω → ℝ) (hw : ∀ o, 0 ≤ w o) (N : Ω → X)
    (ν : Measure X) [IsFiniteMeasure ν] (box : Finset X) (ε : ℝ) (hε : 0 ≤ ε)
    (hlocal : ∀ n ∈ box, 0 < ν.real {n} ∧
      |(∑ o, if N o = n then w o else 0) / ν.real {n} - 1| ≤ ε)
    (E : Set X) :
    |(∑ o, if N o ∈ E then w o else 0) - ν.real E| ≤
      ε * ν.real E + (∑ o, if N o ∉ box then w o else 0) + ν.real (box : Set X)ᶜ := by
  classical
  let core := box.filter (fun n => n ∈ E)
  let p (n : X) := ∑ o, if N o = n then w o else 0
  have hsplit : (∑ o, if N o ∈ E then w o else 0) =
      (∑ n ∈ core, p n) + (∑ o, if N o ∈ E ∧ N o ∉ box then w o else 0) := by
    dsimp only [p]
    rw [sum_comm, ← sum_add_distrib]
    apply sum_congr rfl
    intro o _
    simp only [core, sum_ite_eq', mem_filter]
    by_cases he : N o ∈ E <;> by_cases hb : N o ∈ box <;> simp [he, hb]
  have hcore : (∑ n ∈ core, ν.real {n}) = ν.real (E ∩ (box : Set X)) := by
    rw [sum_measureReal_singleton]
    congr 1
    ext n
    simp [core, and_comm]
  have herr : |(∑ n ∈ core, p n) - ν.real (E ∩ (box : Set X))| ≤
      ε * ν.real (E ∩ (box : Set X)) := by
    rw [← hcore, ← sum_sub_distrib, mul_sum]
    apply (abs_sum_le_sum_abs _ _).trans
    apply sum_le_sum
    intro n hn
    have hb : n ∈ box := (mem_filter.mp hn).1
    obtain ⟨hν, hn⟩ := hlocal n hb
    rw [div_sub_one hν.ne', abs_div, abs_of_pos hν] at hn
    exact (div_le_iff₀ hν).mp hn
  have hνsplit := measureReal_sdiff_add_inter (μ := ν) (s := E)
    (t := (box : Set X)) box.measurableSet
  have hνmono : ν.real (E ∩ (box : Set X)) ≤ ν.real E :=
    measureReal_mono Set.inter_subset_left
  have hνout : ν.real (E \ (box : Set X)) ≤ ν.real (box : Set X)ᶜ :=
    measureReal_mono (by intro n hn; exact hn.2)
  have hpout : 0 ≤ (∑ o, if N o ∈ E ∧ N o ∉ box then w o else 0) := by
    apply sum_nonneg; intro o _; split_ifs
    · exact hw o
    · exact le_rfl
  have hpoutle : (∑ o, if N o ∈ E ∧ N o ∉ box then w o else 0) ≤
      (∑ o, if N o ∉ box then w o else 0) := by
    apply sum_le_sum
    intro o _
    by_cases he : N o ∈ E <;> by_cases hb : N o ∈ box <;> simp [he, hb, hw]
  have hid : (∑ o, if N o ∈ E then w o else 0) - ν.real E =
      ((∑ n ∈ core, p n) - ν.real (E ∩ (box : Set X))) +
      ((∑ o, if N o ∈ E ∧ N o ∉ box then w o else 0) - ν.real (E \ (box : Set X))) := by
    rw [hsplit]
    linarith
  rw [hid]
  have htailabs : |(∑ o, if N o ∈ E ∧ N o ∉ box then w o else 0) -
      ν.real (E \ (box : Set X))| ≤
      (∑ o, if N o ∉ box then w o else 0) + ν.real (box : Set X)ᶜ := by
    have hνnonneg : 0 ≤ ν.real (E \ (box : Set X)) := measureReal_nonneg
    have hh : |(∑ o, if N o ∈ E ∧ N o ∉ box then w o else 0) -
        ν.real (E \ (box : Set X))| ≤
        (∑ o, if N o ∈ E ∧ N o ∉ box then w o else 0) + ν.real (E \ (box : Set X)) := by
      apply abs_le.mpr
      constructor <;> linarith
    exact hh.trans (add_le_add hpoutle hνout)
  exact (abs_add_le _ _).trans ((add_le_add
    (herr.trans (mul_le_mul_of_nonneg_left hνmono hε)) htailabs).trans_eq (by ring))

private def countBox (ι : Type*) [Fintype ι] (B : ℕ) : Finset (ι → ℕ) :=
  (Fintype.piFinset (fun _ => range (B + 1))).filter (fun n => ∑ i, n i ≤ B)

private theorem mem_countBox {ι : Type*} [Fintype ι] (B : ℕ) (n : ι → ℕ) :
    n ∈ countBox ι B ↔ ∑ i, n i ≤ B := by
  classical
  simp only [countBox, mem_filter, Fintype.mem_piFinset, mem_range]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_, h⟩
    intro i
    have hi : n i ≤ ∑ j, n j := single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ i)
    omega

private theorem poisson_product_singleton {ι : Type*} [Fintype ι]
    (μ : ι → ℝ≥0) (n : ι → ℕ) :
    (poissonProduct μ).real {n} =
      ∏ i, (Real.exp (-(μ i : ℝ)) * (μ i : ℝ) ^ n i / (n i).factorial) := by
  simp only [poissonProduct, measureReal_def, Measure.pi_singleton, ENNReal.toReal_prod]
  exact prod_congr rfl fun i _ => poissonMeasure_real_singleton (μ i) (n i)

set_option maxHeartbeats 2000000 in
/-- Every reverse count event admits a relative error plus an exponential tail remainder.
The event, support and complete history law in every term are identical. -/
theorem actual_reverse_marked_every_event (C₀ : ℝ) (hC : 1 ≤ C₀) :
    ∃ (A : ℝ) (M₀ : ℕ) (η₀ : ℝ), 0 < A ∧ 64 ≤ M₀ ∧ 0 < η₀ ∧
      ∀ (M q s k : ℕ) (r : ℝ), M₀ ≤ M → 1 ≤ q → q < M →
        0 < r → r < 1 → compensation M q r < 1 →
        let L := (s : ℝ) / (2 * M)
        1 ≤ L → L / M ≤ η₀ → (k = 1 ∨ k = 2) →
        ∀ (S : Support M q) (m : Fin k → Fin M), Function.Injective m →
          ∀ (e : Experiment) (B : ℕ), (B : ℝ) ≤ C₀ * L →
          ∀ E : Set ((Fin k ⊕ Fin k) → ℕ),
            let μ : (Fin k ⊕ Fin k) → ℝ≥0 := fun _ => ⟨L / 2, by positivity⟩
            |(∑ o : Obs M s e, if markedVector e m o ∈ E then reverseProbability r e S o else 0) -
              (poissonProduct μ).real E| ≤
                (A * L ^ (k + 1) / M) * (poissonProduct μ).real E +
                3 * Real.exp ((k : ℝ) * L) / (2 : ℝ) ^ B := by
  classical
  obtain ⟨A, M₁, η₁, hA, hM₁, hη₁, hlocal⟩ := actual_reverse_marked_count_relative C₀ hC
  refine ⟨A, max 64 M₁, min η₁ (1 / 512), hA, le_max_left _ _, lt_min hη₁ (by norm_num), ?_⟩
  intro M q s k r hMM hq hqm hr hr1 hc1 L hL hLη hk S m hm e B hB E μ
  have hM64 : 64 ≤ M := (le_max_left _ _).trans hMM
  have hM : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hsmall : (s : ℝ) / (M : ℝ) ^ 2 ≤ 1 / 256 := by
    have hh : L / M ≤ 1 / 512 := hLη.trans (min_le_right _ _)
    have he : (s : ℝ) / (M : ℝ) ^ 2 = 2 * (L / M) := by dsimp [L]; field_simp <;> ring
    rw [he]
    linarith
  have hc : 0 ≤ compensation M q r := by unfold compensation; positivity
  have hK := ((finite_support_bayes (s := s) hq hqm hr hr1 hc hc1 e).1 S).1.1
  have hw (o : Obs M s e) : 0 ≤ reverseProbability r e S o := by
    cases e with
    | pair => exact prod_nonneg fun t _ => mul_nonneg (by positivity) (hK _ _)
    | path => exact mul_nonneg (by positivity) (prod_nonneg fun t _ => hK _ _)
  let ν := poissonProduct μ
  haveI : IsProbabilityMeasure ν := by dsimp [ν, poissonProduct]; infer_instance
  let box := countBox (Fin k ⊕ Fin k) B
  have hpoint (n : (Fin k ⊕ Fin k) → ℕ) (hn : n ∈ box) :
      0 < ν.real {n} ∧ |(∑ o : Obs M s e,
        @ite ℝ (markedVector e m o = n) (Classical.propDecidable _)
          (reverseProbability r e S o) 0) / ν.real {n} - 1| ≤
          A * L ^ (k + 1) / M := by
    have htotal : ∑ i, n i ≤ B := (mem_countBox B n).mp hn
    have hcounts (j : Fin k) : (n (.inl j) : ℝ) ≤ C₀ * L ∧ (n (.inr j) : ℝ) ≤ C₀ * L := by
      have hi : n (.inl j) ≤ ∑ i, n i := single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ _)
      have hj : n (.inr j) ≤ ∑ i, n i := single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ _)
      constructor
      · exact (show (n (.inl j) : ℝ) ≤ B by exact_mod_cast hi.trans htotal).trans hB
      · exact (show (n (.inr j) : ℝ) ≤ B by exact_mod_cast hj.trans htotal).trans hB
    have hν : ν.real {n} = ∏ j : Fin k,
        (Real.exp (-(L / 2)) * (L / 2) ^ n (.inl j) / (n (.inl j)).factorial) *
        (Real.exp (-(L / 2)) * (L / 2) ^ n (.inr j) / (n (.inr j)).factorial) := by
      rw [poisson_product_singleton, Fintype.prod_sum_type, ← prod_mul_distrib]
      rfl
    have hνpos : 0 < ν.real {n} := by rw [hν]; exact prod_pos fun j _ => by positivity
    refine ⟨hνpos, ?_⟩
    have he (o : Obs M s e) : markedVector e m o = n ↔
        ∀ j, count e o (m j) 1 = n (.inl j) ∧ count e o (m j) (-1) = n (.inr j) := by
      constructor
      · intro h j; constructor
        · exact congrFun h (.inl j)
        · exact congrFun h (.inr j)
      · intro h; funext i; cases i with
        | inl j => exact (h j).1
        | inr j => exact (h j).2
    simp_rw [he]
    rw [hν]
    exact hlocal M q s k r ((le_max_right _ _).trans hMM) hq hqm hr hr1 hc1
      hL (hLη.trans (min_le_left _ _)) hk S m hm (fun j => n (.inl j)) (fun j => n (.inr j)) hcounts e
  have hε : 0 ≤ A * L ^ (k + 1) / M := by positivity
  haveI : IsFiniteMeasure ν := inferInstance
  haveI : MeasurableSingletonClass ((Fin k ⊕ Fin k) → ℕ) := inferInstance
  have hgeneric := finite_history_event_comparison
    (Ω := Obs M s e) (X := (Fin k ⊕ Fin k) → ℕ)
    (reverseProbability r e S) hw (markedVector e m)
    ν box (A * L ^ (k + 1) / M) hε
  have hpointGeneric := hgeneric hpoint
  have hcomp := hpointGeneric E
  have htail := actual_reverse_marked_count_tail hM64 hq hqm hr hr1 hc1 hk S m hm e hsmall B
  have hcount (o : Obs M s e) : markedVector e m o ∉ box ↔
      B < ∑ j, (count e o (m j) 1 + count e o (m j) (-1)) := by
    rw [mem_countBox, not_le]
    simp [Fintype.sum_sum_type, markedVector, sum_add_distrib]
  have hcompl : (box : Set ((Fin k ⊕ Fin k) → ℕ))ᶜ = {n | B < ∑ i, n i} := by
    ext n; simp [box, mem_countBox]
  simp_rw [hcount] at hcomp
  rw [hcompl] at hcomp
  apply hcomp.trans
  simpa only [add_assoc] using add_le_add_right htail
    ((A * L ^ (k + 1) / M) * ν.real E)


private def forwardRates {M q s k : ℕ} (r : ℝ) (S : Support M q) (m : Fin k → Fin M) :
    (Fin k ⊕ Fin k) → ℝ≥0 :=
  Sum.elim
    (fun j => Real.toNNReal (((s : ℝ) / (2 * M)) * (1 + b r S (.inl (m j))) / 2))
    (fun j => Real.toNNReal (((s : ℝ) / (2 * M)) * (1 - b r S (.inl (m j))) / 2))

private theorem forward_rate_values {M q s k : ℕ} {r : ℝ}
    (hM : 0 < M) (hq : 1 ≤ q) (hqm : q < M) (hr : 0 < r) (hr1 : r < 1)
    (hc1 : compensation M q r < 1) (S : Support M q) (m : Fin k → Fin M) :
    (∀ j, (forwardRates (s := s) r S m (.inl j) : ℝ) =
      ((s : ℝ) / (2 * M)) * (1 + b r S (.inl (m j))) / 2) ∧
    (∀ j, (forwardRates (s := s) r S m (.inr j) : ℝ) =
      ((s : ℝ) / (2 * M)) * (1 - b r S (.inl (m j))) / 2) ∧
    (∑ i, (forwardRates (s := s) r S m i : ℝ)) =
      (k : ℝ) * ((s : ℝ) / (2 * M)) := by
  have hc : 0 ≤ compensation M q r := by unfold compensation; positivity
  have hb (j : Fin k) : -1 ≤ b r S (.inl (m j)) ∧ b r S (.inl (m j)) ≤ 1 := by
    dsimp [b]; split_ifs <;> constructor <;> linarith
  have hp (j : Fin k) : (forwardRates (s := s) r S m (.inl j) : ℝ) =
      ((s : ℝ) / (2 * M)) * (1 + b r S (.inl (m j))) / 2 := by
    change ((Real.toNNReal _ : ℝ≥0) : ℝ) = _
    apply Real.coe_toNNReal
    exact div_nonneg (mul_nonneg (by positivity) (by linarith [(hb j).1])) (by norm_num)
  have hm (j : Fin k) : (forwardRates (s := s) r S m (.inr j) : ℝ) =
      ((s : ℝ) / (2 * M)) * (1 - b r S (.inl (m j))) / 2 := by
    change ((Real.toNNReal _ : ℝ≥0) : ℝ) = _
    apply Real.coe_toNNReal
    exact div_nonneg (mul_nonneg (by positivity) (by linarith [(hb j).2])) (by norm_num)
  refine ⟨hp, hm, ?_⟩
  rw [Fintype.sum_sum_type]
  simp_rw [hp, hm]
  rw [← sum_add_distrib]
  have he (j : Fin k) :
      ((s : ℝ) / (2 * M)) * (1 + b r S (.inl (m j))) / 2 +
      ((s : ℝ) / (2 * M)) * (1 - b r S (.inl (m j))) / 2 = (s : ℝ) / (2 * M) := by ring
  simp_rw [he]
  simp

private theorem forward_two_moment {M q s k : ℕ} {r : ℝ}
    (hM64 : 64 ≤ M) (hq : 1 ≤ q) (hqm : q < M) (hr : 0 < r) (hr1 : r < 1)
    (hc1 : compensation M q r < 1) (hk : k = 1 ∨ k = 2)
    (S : Support M q) (m : Fin k → Fin M) (hm : Function.Injective m) (e : Experiment)
    (hsmall : (s : ℝ) / (M : ℝ) ^ 2 ≤ 1 / 256) :
    (∑ o : Obs M s e, probability r e S o *
      (2 : ℝ) ^ (∑ i, markedVector e m o i)) ≤
      2 * Real.exp ((k : ℝ) * ((s : ℝ) / (2 * M))) := by
  classical
  have hMnat : 0 < M := by omega
  have hM : (0 : ℝ) < M := by exact_mod_cast hMnat
  have hMc : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  let P : ℝ := ∑ o : Obs M s e, probability r e S o *
    (2 : ℝ) ^ (∑ i, markedVector e m o i)
  let F : ℂ := ∑ o : Obs M s e, (probability r e S o : ℂ) *
    ∏ j, (2 : ℂ) ^ count e o (m j) 1 * (2 : ℂ) ^ count e o (m j) (-1)
  have hFP : F = (P : ℂ) := by
    dsimp [F, P]
    push_cast
    apply sum_congr rfl
    intro o _
    rw [Fintype.sum_sum_type, pow_add, ← prod_pow_eq_pow_sum, ← prod_pow_eq_pow_sum,
      ← prod_mul_distrib]
    rfl
  have hA : driftA r S m (fun _ => 2) (fun _ => 2) = (k : ℂ) / (2 * M) := by
    simp [driftA, tiltU, tiltV] <;> ring
  have hmean : (s : ℂ) * driftA r S m (fun _ => 2) (fun _ => 2) =
      (((k : ℝ) * ((s : ℝ) / (2 * M)) : ℝ) : ℂ) := by
    rw [hA]; push_cast; ring
  cases e with
  | pair =>
    have hpair := D5.S3.Estimation.TimeArrow.ArbitraryMarkedCountPoissonRelative.actual_marked_pair_pgf
      (s := s) hMnat r S m hm (fun _ => 2) (fun _ => 2)
    change F = _ at hpair
    rw [hFP, hA] at hpair
    have he : P = (1 + (k : ℝ) / (2 * M)) ^ s := by
      apply Complex.ofReal_injective
      push_cast
      exact hpair
    change P ≤ _
    rw [he]
    have hbase : 0 ≤ 1 + (k : ℝ) / (2 * M) := by positivity
    have hh : (1 + (k : ℝ) / (2 * M)) ^ s ≤
        (Real.exp ((k : ℝ) / (2 * M))) ^ s := by
      gcongr
      simpa only [add_comm] using Real.add_one_le_exp ((k : ℝ) / (2 * M))
    rw [← Real.exp_nat_mul] at hh
    have harg : (s : ℝ) * ((k : ℝ) / (2 * M)) =
        (k : ℝ) * ((s : ℝ) / (2 * M)) := by ring
    rw [harg] at hh
    exact hh.trans (by linarith [Real.exp_pos ((k : ℝ) * ((s : ℝ) / (2 * M)))])
  | path =>
    let η : ℝ := 1 / M
    have hη : 0 ≤ η := by dsimp [η]; positivity
    have hη1 : η ≤ 1 / 4 := by
      dsimp [η]
      apply (div_le_iff₀ hM).mpr
      have h64 : (64 : ℝ) ≤ M := by exact_mod_cast hM64
      linarith
    have hTsmall : (s : ℝ) * η ^ 2 ≤ 1 / 256 := by
      simpa [η, div_pow, div_eq_mul_inv] using hsmall
    have hT : (s : ℝ) * η ^ 2 ≤ 1 / 10 := by linarith
    have hc : 0 ≤ compensation M q r := by unfold compensation; positivity
    have hb (j : Fin k) : ‖(b r S (.inl (m j)) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      dsimp [b]; split_ifs
      · rw [abs_of_pos hr]; exact hr1.le
      · rw [abs_neg, abs_of_nonneg hc]; exact hc1.le
    have hAbound : ‖driftA r S m (fun _ => 2) (fun _ => 2)‖ ≤ η := by
      rw [hA, norm_div, Complex.norm_natCast, norm_mul, Complex.norm_natCast]
      norm_num
      apply (div_le_iff₀ (by positivity : 0 < 2 * (M : ℝ))).mpr
      have he : η * (2 * M) = 2 := by dsimp [η]; field_simp
      rw [he]
      rcases hk with rfl | rfl <;> norm_num
    have hBbound : ‖driftB r S m (fun _ => 2) (fun _ => 2)‖ ≤ η := by
      simp only [driftB, tiltU, tiltV]
      norm_num
      have hsum := marked_sum_norm hk 1 (by norm_num) (fun j => (b r S (.inl (m j)) : ℂ)) hb
      apply (div_le_iff₀ (by positivity : 0 < 2 * (M : ℝ))).mpr
      have he : η * (2 * M) = 2 := by dsimp [η]; field_simp
      rw [he]
      simpa only [mul_one] using hsum
    have hh := actual_marked_path_pgf_poisson_envelope hq hqm hr hr1 hc1 S hk m hm
      (fun _ => 2) (fun _ => 2) hη hη1 hAbound hBbound hT
    change ‖F - _‖ ≤ _ at hh
    rw [hFP, hmean, ← Complex.ofReal_exp, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs] at hh
    have hreal : (s : ℝ) * (driftA r S m (fun _ => 2) (fun _ => 2)).re =
        (k : ℝ) * ((s : ℝ) / (2 * M)) := by
      have h := congrArg Complex.re hmean
      simpa only [Complex.ofReal_re, Complex.mul_re, Complex.natCast_re,
      Complex.natCast_im, zero_mul, sub_zero] using h
    rw [hreal] at hh
    have hcoef : 20 * (s : ℝ) * η ^ 2 ≤ 1 := by nlinarith
    have hbound := mul_le_mul_of_nonneg_right hcoef
      (Real.exp_pos ((k : ℝ) * ((s : ℝ) / (2 * M)))).le
    have hupper := (abs_le.mp hh).2
    change P ≤ _
    nlinarith

/-- Both forward experiments and the product law at their exact directional means share a tail
bound on the same fixed support and marked rows. -/
theorem actual_forward_marked_count_tail {M q s k : ℕ} {r : ℝ}
    (hM64 : 64 ≤ M) (hq : 1 ≤ q) (hqm : q < M) (hr : 0 < r) (hr1 : r < 1)
    (hc1 : compensation M q r < 1) (hk : k = 1 ∨ k = 2)
    (S : Support M q) (m : Fin k → Fin M) (hm : Function.Injective m) (e : Experiment)
    (hsmall : (s : ℝ) / (M : ℝ) ^ 2 ≤ 1 / 256) (B : ℕ) :
    let L := (s : ℝ) / (2 * M)
    (∑ o : Obs M s e,
      if B < ∑ j, (count e o (m j) 1 + count e o (m j) (-1))
      then probability r e S o else 0) +
      (poissonProduct (forwardRates (s := s) r S m)).real {n | B < ∑ i, n i} ≤
      3 * Real.exp ((k : ℝ) * L) / (2 : ℝ) ^ B := by
  classical
  intro L
  have hc : 0 ≤ compensation M q r := by unfold compensation; positivity
  have hK := ((finite_support_bayes (s := s) hq hqm hr hr1 hc hc1 e).1 S).1.1
  have hw (o : Obs M s e) : 0 ≤ probability r e S o := by
    cases e with
    | pair => exact prod_nonneg fun t _ => mul_nonneg (by positivity) (hK _ _)
    | path => exact mul_nonneg (by positivity) (prod_nonneg fun t _ => hK _ _)
  have ht := finite_weighted_tail (probability r e S) hw (fun o => ∑ i, markedVector e m o i) B
  have hmom := forward_two_moment hM64 hq hqm hr hr1 hc1 hk S m hm e hsmall
  have htail := product_poisson_tail (forwardRates (s := s) r S m) B
  rw [(forward_rate_values (s := s) (by omega) hq hqm hr hr1 hc1 S m).2.2] at htail
  have hcount (o : Obs M s e) : (∑ i, markedVector e m o i) =
      ∑ j, (count e o (m j) 1 + count e o (m j) (-1)) := by
    simp [Fintype.sum_sum_type, markedVector, sum_add_distrib]
  simp_rw [hcount] at ht hmom
  have hmom' := div_le_div_of_nonneg_right hmom (show 0 ≤ (2 : ℝ) ^ B by positivity)
  have h := add_le_add (ht.trans hmom') htail
  convert h using 1 <;> ring

set_option maxHeartbeats 2000000 in
/-- Every forward count event admits a relative error plus an exponential tail remainder at
its exact support-dependent directional means. -/
theorem actual_forward_marked_every_event (κ C₀ : ℝ)
    (hκ : 0 < κ) (hκ1 : κ < 1) (hC : 1 ≤ C₀) :
    ∃ (A : ℝ) (M₀ : ℕ) (η₀ : ℝ), 0 < A ∧ 64 ≤ M₀ ∧ 0 < η₀ ∧
      ∀ (M q s k : ℕ) (r : ℝ), M₀ ≤ M → 1 ≤ q → q < M →
        0 < r → r ≤ 1 - κ → compensation M q r ≤ 1 - κ →
        let L := (s : ℝ) / (2 * M)
        1 ≤ L → L / M ≤ η₀ → (k = 1 ∨ k = 2) →
        ∀ (S : Support M q) (m : Fin k → Fin M), Function.Injective m →
          ∀ (e : Experiment) (B : ℕ), (B : ℝ) ≤ C₀ * L →
          ∀ E : Set ((Fin k ⊕ Fin k) → ℕ),
            |(∑ o : Obs M s e, if markedVector e m o ∈ E then probability r e S o else 0) -
              (poissonProduct (forwardRates (s := s) r S m)).real E| ≤
                (A * L ^ (k + 1) / M) * (poissonProduct (forwardRates (s := s) r S m)).real E +
                3 * Real.exp ((k : ℝ) * L) / (2 : ℝ) ^ B := by
  classical
  obtain ⟨A, M₁, η₁, hA, hM₁, hη₁, hlocal⟩ := D5.S3.Estimation.TimeArrow.ArbitraryMarkedCountPoissonRelative.arbitrary_marked_count_poisson_relative κ C₀ hκ hκ1 hC
  refine ⟨A, max 64 M₁, min η₁ (1 / 512), hA, le_max_left _ _, lt_min hη₁ (by norm_num), ?_⟩
  intro M q s k r hMM hq hqm hr hrκ hcκ L hL hLη hk S m hm e B hB E
  have hr1 : r < 1 := by linarith
  have hc1 : compensation M q r < 1 := by linarith
  have hM64 : 64 ≤ M := (le_max_left _ _).trans hMM
  have hM : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hsmall : (s : ℝ) / (M : ℝ) ^ 2 ≤ 1 / 256 := by
    have hh : L / M ≤ 1 / 512 := hLη.trans (min_le_right _ _)
    have he : (s : ℝ) / (M : ℝ) ^ 2 = 2 * (L / M) := by dsimp [L]; field_simp <;> ring
    rw [he]
    linarith
  have hc : 0 ≤ compensation M q r := by unfold compensation; positivity
  have hK := ((finite_support_bayes (s := s) hq hqm hr hr1 hc hc1 e).1 S).1.1
  have hw (o : Obs M s e) : 0 ≤ probability r e S o := by
    cases e with
    | pair => exact prod_nonneg fun t _ => mul_nonneg (by positivity) (hK _ _)
    | path => exact mul_nonneg (by positivity) (prod_nonneg fun t _ => hK _ _)
  let ν := poissonProduct (forwardRates (s := s) r S m)
  haveI : IsProbabilityMeasure ν := by dsimp [ν, poissonProduct]; infer_instance
  let box := countBox (Fin k ⊕ Fin k) B
  have hpoint (n : (Fin k ⊕ Fin k) → ℕ) (hn : n ∈ box) :
      0 < ν.real {n} ∧ |(∑ o : Obs M s e,
        @ite ℝ (markedVector e m o = n) (Classical.propDecidable _)
          (probability r e S o) 0) / ν.real {n} - 1| ≤
          A * L ^ (k + 1) / M := by
    have htotal : ∑ i, n i ≤ B := (mem_countBox B n).mp hn
    have hcounts (j : Fin k) : (n (.inl j) : ℝ) ≤ C₀ * L ∧ (n (.inr j) : ℝ) ≤ C₀ * L := by
      have hi : n (.inl j) ≤ ∑ i, n i := single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ _)
      have hj : n (.inr j) ≤ ∑ i, n i := single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ _)
      constructor
      · exact (show (n (.inl j) : ℝ) ≤ B by exact_mod_cast hi.trans htotal).trans hB
      · exact (show (n (.inr j) : ℝ) ≤ B by exact_mod_cast hj.trans htotal).trans hB
    have hb (j : Fin k) : -(1 - κ) ≤ b r S (.inl (m j)) ∧ b r S (.inl (m j)) ≤ 1 - κ := by
      dsimp [b]; split_ifs <;> constructor <;> linarith
    have hpmean (j : Fin k) : 0 < L * (1 + b r S (.inl (m j))) / 2 := by
      apply div_pos _ (by norm_num)
      apply mul_pos (by linarith)
      linarith [(hb j).1]
    have hmmean (j : Fin k) : 0 < L * (1 - b r S (.inl (m j))) / 2 := by
      apply div_pos _ (by norm_num)
      apply mul_pos (by linarith)
      linarith [(hb j).2]
    have hν : ν.real {n} = ∏ j : Fin k,
        (Real.exp (-(L * (1 + b r S (.inl (m j))) / 2)) *
          (L * (1 + b r S (.inl (m j))) / 2) ^ n (.inl j) / (n (.inl j)).factorial) *
        (Real.exp (-(L * (1 - b r S (.inl (m j))) / 2)) *
          (L * (1 - b r S (.inl (m j))) / 2) ^ n (.inr j) / (n (.inr j)).factorial) := by
      rw [poisson_product_singleton, Fintype.prod_sum_type]
      have hvals := forward_rate_values (s := s) (by omega) hq hqm hr hr1 hc1 S m
      simp_rw [hvals.1, hvals.2.1]
      rw [← prod_mul_distrib]
    have hνpos : 0 < ν.real {n} := by
      rw [hν]
      apply prod_pos
      intro j _
      exact mul_pos
        (div_pos (mul_pos (Real.exp_pos _) (pow_pos (hpmean j) _)) (by positivity))
        (div_pos (mul_pos (Real.exp_pos _) (pow_pos (hmmean j) _)) (by positivity))
    refine ⟨hνpos, ?_⟩
    have he (o : Obs M s e) : markedVector e m o = n ↔
        ∀ j, count e o (m j) 1 = n (.inl j) ∧ count e o (m j) (-1) = n (.inr j) := by
      constructor
      · intro h j; constructor
        · exact congrFun h (.inl j)
        · exact congrFun h (.inr j)
      · intro h; funext i; cases i with
        | inl j => exact (h j).1
        | inr j => exact (h j).2
    simp_rw [he]
    rw [hν]
    exact hlocal M q s k r ((le_max_right _ _).trans hMM) hq hqm hr hrκ hcκ
      hL (hLη.trans (min_le_left _ _)) hk S m hm (fun j => n (.inl j)) (fun j => n (.inr j)) hcounts e
  have hε : 0 ≤ A * L ^ (k + 1) / M := by positivity
  haveI : IsFiniteMeasure ν := inferInstance
  haveI : MeasurableSingletonClass ((Fin k ⊕ Fin k) → ℕ) := inferInstance
  have hgeneric := finite_history_event_comparison
    (Ω := Obs M s e) (X := (Fin k ⊕ Fin k) → ℕ)
    (probability r e S) hw (markedVector e m)
    ν box (A * L ^ (k + 1) / M) hε
  have hpointGeneric := hgeneric hpoint
  have hcomp := hpointGeneric E
  have htail := actual_forward_marked_count_tail hM64 hq hqm hr hr1 hc1 hk S m hm e hsmall B
  have hcount (o : Obs M s e) : markedVector e m o ∉ box ↔
      B < ∑ j, (count e o (m j) 1 + count e o (m j) (-1)) := by
    rw [mem_countBox, not_le]
    simp [Fintype.sum_sum_type, markedVector, sum_add_distrib]
  have hcompl : (box : Set ((Fin k ⊕ Fin k) → ℕ))ᶜ = {n | B < ∑ i, n i} := by
    ext n; simp [box, mem_countBox]
  simp_rw [hcount] at hcomp
  rw [hcompl] at hcomp
  apply hcomp.trans
  simpa only [add_assoc] using add_le_add_right htail
    ((A * L ^ (k + 1) / M) * ν.real E)



end D5.S3.Estimation.TimeArrow.MarkedPoissonEventComparison
