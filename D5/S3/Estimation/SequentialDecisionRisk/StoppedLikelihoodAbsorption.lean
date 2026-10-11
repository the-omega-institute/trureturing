/- GID: D5/S3/Estimation/SequentialDecisionRisk/StoppedLikelihoodAbsorption
   generality: G
   mirror-B: D5/B/S3/Estimation/SequentialDecisionRisk/StoppedLikelihoodAbsorption
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite martingale maximal moments and stopped likelihood absorption. -/

import Mathlib.Probability.Martingale.OptionalStopping
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

noncomputable section

open MeasureTheory Filter Finset
open scoped BigOperators ENNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace D5.S3.Estimation.SequentialDecisionRisk.StoppedLikelihoodAbsorption

local notation "PMax" => fun (f : ℕ → ℝ) (n : ℕ) =>
  (range (n + 1)).sup' nonempty_range_add_one f

private lemma prefix_max_zero (f : ℕ → ℝ) : PMax f 0 = f 0 := by
  simp

private lemma prefix_max_succ (f : ℕ → ℝ) (n : ℕ) :
    PMax f (n + 1) = max (PMax f n) (f (n + 1)) := by
  calc
    PMax f (n + 1) = f (n + 1) ⊔ PMax f n := by
      simpa only [range_add_one] using
        (sup'_insert (s := range (n + 1)) nonempty_range_add_one f (b := n + 1))
    _ = _ := max_comm _ _

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  [IsFiniteMeasure μ] {ℱ : Filtration ℕ mΩ}

private lemma martingale_abs_submartingale {f : ℕ → Ω → ℝ}
    (hf : Martingale f ℱ μ) : Submartingale (fun n ω => |f n ω|) ℱ μ := by
  refine ⟨fun n => ?_, ?_, fun n => (hf.integrable n).abs⟩
  · simpa only [Real.norm_eq_abs] using (hf.stronglyMeasurable n).norm
  · intro i j hij
    filter_upwards [hf.condExp_ae_eq hij,
      norm_condExp_le (m := ℱ i) (μ := μ) (f j)] with ω hω hle
    simpa only [Real.norm_eq_abs, hω] using hle

private lemma submartingale_integral_nonneg {f : ℕ → Ω → ℝ}
    (hf : Submartingale f ℱ μ) (hzero : f 0 = 0) (n : ℕ) :
    0 ≤ ∫ ω, f n ω ∂μ := by
  have h := hf.setIntegral_le (i := 0) (j := n) (Nat.zero_le n)
    (s := Set.univ) MeasurableSet.univ
  simpa [hzero] using h

private lemma prefix_max_adapted {f : ℕ → Ω → ℝ}
    (hf : StronglyAdapted ℱ f) :
    StronglyAdapted ℱ (fun n ω => PMax (fun i => f i ω) n) := by
  intro n
  induction n with
  | zero => simpa only [prefix_max_zero] using hf 0
  | succ n ih =>
    have heq : (fun ω => PMax (fun i => f i ω) (n + 1)) =
        (fun ω => max (PMax (fun i => f i ω) n) (f (n + 1) ω)) := by
      funext ω
      exact prefix_max_succ _ _
    change StronglyMeasurable[ℱ (n + 1)] (fun ω => PMax (fun i => f i ω) (n + 1))
    rw [heq]
    exact @StronglyMeasurable.sup Ω ℝ _ _ (ℱ (n + 1)) _ _ _
      (ih.mono (ℱ.mono (Nat.le_succ n))) (hf (n + 1))

private lemma pathwise_max_pow (f : ℕ → ℝ) (hf : ∀ i, 0 ≤ f i) (k n : ℕ) :
    (k + 1 : ℝ) * (PMax f n) ^ (k + 2) ≤
      (k + 2 : ℝ) * (PMax f n) ^ (k + 1) * f n -
      (k + 2 : ℝ) * ∑ i ∈ range n,
        (PMax f i) ^ (k + 1) * (f (i + 1) - f i) := by
  induction n with
  | zero =>
    simp only [prefix_max_zero, range_zero, sum_empty, mul_zero, sub_zero]
    have hpow := pow_nonneg (hf 0) (k + 2)
    rw [show k + 2 = (k + 1) + 1 by omega, pow_succ] at hpow ⊢
    nlinarith
  | succ n ih =>
    rw [prefix_max_succ, sum_range_succ]
    by_cases h : f (n + 1) ≤ PMax f n
    · rw [max_eq_left h]
      nlinarith
    · have ha : 0 ≤ PMax f n :=
        (hf 0).trans (le_sup' f (mem_range.mpr (by omega)))
      have h' : PMax f n ≤ f (n + 1) := le_of_not_ge h
      have ht := pow_add_mul_le_add_pow ha
        (show 0 ≤ 2 * PMax f n + (f (n + 1) - PMax f n) by linarith) (k + 2)
      simp only [add_sub_cancel, show k + 2 - 1 = k + 1 by omega,
        Nat.cast_add, Nat.cast_ofNat] at ht
      rw [max_eq_right h']
      simp only [show k + 2 = (k + 1) + 1 by omega, pow_succ] at ih ht ⊢
      nlinarith

private lemma pathwise_doob_pow (f : ℕ → ℝ) (hf : ∀ i, 0 ≤ f i) (k n : ℕ) :
    (k + 1 : ℝ) * (PMax f n) ^ (k + 2) ≤
      (2 : ℝ) ^ (k + 2) * (f n) ^ (k + 2) -
      2 * (k + 2 : ℝ) * ∑ i ∈ range n,
        (PMax f i) ^ (k + 1) * (f (i + 1) - f i) := by
  have ha : 0 ≤ PMax f n :=
    (hf 0).trans (le_sup' f (mem_range.mpr (by omega)))
  have ht := pow_add_mul_le_add_pow ha
    (show 0 ≤ 2 * PMax f n + (2 * f n - PMax f n) by nlinarith [hf n]) (k + 2)
  simp only [add_sub_cancel, show k + 2 - 1 = k + 1 by omega,
    Nat.cast_add, Nat.cast_ofNat] at ht
  rw [mul_pow] at ht
  have hpath := pathwise_max_pow f hf k n
  simp only [show k + 2 = (k + 1) + 1 by omega, pow_succ] at ht hpath ⊢
  nlinarith

private lemma doob_power_bound {f : ℕ → Ω → ℝ} (hf : Submartingale f ℱ μ)
    (hnonneg : ∀ i ω, 0 ≤ f i ω) {R : ℝ} (hbdd : ∀ i ω, f i ω ≤ R) (k n : ℕ) :
    (k + 1 : ℝ) * (∫ ω, (PMax (fun i => f i ω) n) ^ (k + 2) ∂μ) ≤
      (2 : ℝ) ^ (k + 2) * ∫ ω, (f n ω) ^ (k + 2) ∂μ := by
  let maxF : ℕ → Ω → ℝ := fun n ω => PMax (fun i => f i ω) n
  have hmax : StronglyAdapted ℱ maxF := prefix_max_adapted hf.stronglyAdapted
  have hmax0 : ∀ i ω, 0 ≤ maxF i ω := fun i ω =>
    (hnonneg 0 ω).trans (le_sup' (fun j => f j ω) (mem_range.mpr (by omega)))
  have hmaxR : ∀ i ω, maxF i ω ≤ R := fun i ω =>
    sup'_le _ _ (fun j _ => hbdd j ω)
  have hmaxpow : ∀ i, Integrable (fun ω => maxF i ω ^ (k + 2)) μ := fun i =>
    ⟨((hmax i).mono (ℱ.le i)).pow _ |>.aestronglyMeasurable,
      HasFiniteIntegral.of_bounded (ae_of_all μ (fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (hmax0 i ω) _)]
        exact pow_le_pow_left₀ (hmax0 i ω) (hmaxR i ω) _))⟩
  have hfnpow : Integrable (fun ω => f n ω ^ (k + 2)) μ :=
    ⟨((hf.stronglyMeasurable n).mono (ℱ.le n)).pow _ |>.aestronglyMeasurable,
      HasFiniteIntegral.of_bounded (ae_of_all μ (fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (hnonneg n ω) _)]
        exact pow_le_pow_left₀ (hnonneg n ω) (hbdd n ω) _))⟩
  have hsum := hf.sum_mul_sub (fun i => (hmax i).pow (k + 1))
    (fun i ω => pow_le_pow_left₀ (hmax0 i ω) (hmaxR i ω) (k + 1))
    (fun i ω => pow_nonneg (hmax0 i ω) (k + 1))
  have hsum0 : 0 ≤ ∫ ω, ∑ i ∈ range n,
      maxF i ω ^ (k + 1) * (f (i + 1) ω - f i ω) ∂μ := by
    simpa only [Finset.sum_apply, Pi.mul_apply, Pi.sub_apply, Pi.pow_apply] using
      submartingale_integral_nonneg hsum (by ext ω; simp) n
  have hsumint : Integrable (fun ω => ∑ i ∈ range n,
      maxF i ω ^ (k + 1) * (f (i + 1) ω - f i ω)) μ := by
    convert hsum.integrable n using 1
    ext ω
    simp only [Finset.sum_apply, Pi.mul_apply, Pi.sub_apply, Pi.pow_apply]
  have hrightint : Integrable (fun ω => (2 : ℝ) ^ (k + 2) * f n ω ^ (k + 2) -
      2 * (k + 2 : ℝ) * ∑ i ∈ range n,
        maxF i ω ^ (k + 1) * (f (i + 1) ω - f i ω)) μ :=
    (hfnpow.const_mul _).sub (hsumint.const_mul _)
  have hineq := integral_mono ((hmaxpow n).const_mul (k + 1 : ℝ))
    hrightint
    (fun ω => pathwise_doob_pow (fun i => f i ω) (fun i => hnonneg i ω) k n)
  rw [integral_sub (hfnpow.const_mul _) (hsumint.const_mul _),
    integral_const_mul, integral_const_mul, integral_const_mul] at hineq
  change (k + 1 : ℝ) * (∫ ω, maxF n ω ^ (k + 2) ∂μ) ≤ _ at hineq
  have hk : 0 ≤ (k + 2 : ℝ) := by positivity
  nlinarith

private lemma power_remainder_bound (x y S : ℝ) (hS : 0 ≤ S)
    (hx : |x| ≤ S) (hy : |y| ≤ S) (k : ℕ) :
    |y ^ (k + 2) - x ^ (k + 2) - (k + 2 : ℝ) * x ^ (k + 1) * (y - x)| ≤
      (k + 2 : ℝ) ^ 2 * S ^ k * (y - x) ^ 2 := by
  have hrep : y ^ (k + 2) - x ^ (k + 2) -
      (k + 2 : ℝ) * x ^ (k + 1) * (y - x) =
      (y - x) * ∑ j ∈ range (k + 2),
        (y ^ j - x ^ j) * x ^ (k + 1 - j) := by
    have hg := (Commute.all y x).mul_geom_sum₂ (k + 2)
    have hs := geom_sum₂_self x (k + 2)
    simp only [show k + 2 - 1 = k + 1 by omega, Nat.cast_add, Nat.cast_ofNat] at hg hs
    rw [← hg]
    calc
      _ = (y - x) * ((∑ j ∈ range (k + 2), y ^ j * x ^ (k + 1 - j)) -
          (∑ j ∈ range (k + 2), x ^ j * x ^ (k + 1 - j))) := by rw [hs]; ring
      _ = _ := by
        rw [← sum_sub_distrib]
        congr 1
        apply sum_congr rfl
        intro j _
        ring
  have hterm : ∀ j ∈ range (k + 2),
      |(y ^ j - x ^ j) * x ^ (k + 1 - j)| ≤ |y - x| * (k + 2 : ℝ) * S ^ k := by
    intro j hj
    have hjlt := mem_range.mp hj
    by_cases hj0 : j = 0
    · simp only [hj0, pow_zero, sub_self, zero_mul, abs_zero]
      positivity
    · have hjpos : 0 < j := Nat.pos_of_ne_zero hj0
      have hmax : max |y| |x| ≤ S := max_le hy hx
      calc
        _ = |y ^ j - x ^ j| * |x| ^ (k + 1 - j) := by rw [abs_mul, abs_pow]
        _ ≤ (|y - x| * (j : ℝ) * (max |y| |x|) ^ (j - 1)) *
            S ^ (k + 1 - j) := by
          apply mul_le_mul
          · exact abs_pow_sub_pow_le (a := y) (b := x) (n := j)
          · exact pow_le_pow_left₀ (abs_nonneg x) hx _
          · positivity
          · positivity
        _ ≤ (|y - x| * (j : ℝ) * S ^ (j - 1)) * S ^ (k + 1 - j) := by
          gcongr
        _ = |y - x| * (j : ℝ) * S ^ k := by
          rw [mul_assoc, ← pow_add, show j - 1 + (k + 1 - j) = k by omega]
        _ ≤ _ := by gcongr; exact_mod_cast hjlt.le
  have hsum : |∑ j ∈ range (k + 2), (y ^ j - x ^ j) * x ^ (k + 1 - j)| ≤
      (k + 2 : ℝ) * (|y - x| * (k + 2 : ℝ) * S ^ k) := by
    exact (abs_sum_le_sum_abs _ _).trans
      ((sum_le_sum hterm).trans_eq (by simp))
  rw [hrep, abs_mul]
  calc
    _ ≤ |y - x| * ((k + 2 : ℝ) * (|y - x| * (k + 2 : ℝ) * S ^ k)) :=
      mul_le_mul_of_nonneg_left hsum (abs_nonneg _)
    _ = _ := by rw [← sq_abs (y - x)]; ring

private lemma predictable_increment_integral_zero {f : ℕ → Ω → ℝ}
    (hf : Martingale f ℱ μ) {g : Ω → ℝ} {i : ℕ}
    (hg : StronglyMeasurable[ℱ i] g)
    (hgi : Integrable (g * (f (i + 1) - f i)) μ) :
    (∫ ω, g ω * (f (i + 1) ω - f i ω) ∂μ) = 0 := by
  have hp := condExp_mul_of_stronglyMeasurable_left hg hgi
    ((hf.integrable (i + 1)).sub (hf.integrable i))
  have hd := condExp_sub (hf.integrable (i + 1)) (hf.integrable i) (ℱ i)
  rw [← integral_condExp (ℱ.le i)]
  apply integral_eq_zero_of_ae
  filter_upwards [hp, hd, hf.condExp_ae_eq (Nat.le_succ i), hf.condExp_ae_eq (le_refl i)]
    with ω hω hδ hnext hself
  simp only [Pi.mul_apply, Pi.sub_apply] at hω hδ
  change μ[g * (f (i + 1) - f i) | ℱ i] ω = 0
  rw [hω, hδ, hnext, hself, sub_self, mul_zero]

local notation "Quad" => fun (f : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) =>
  ∑ i ∈ range n, (f (i + 1) ω - f i ω) ^ 2

private lemma terminal_power_bound (f : ℕ → ℝ) (hf0 : f 0 = 0)
    {m : ℕ} (hm : 0 < m) (n : ℕ) :
    f n ^ (2 * m) ≤ (2 * m : ℝ) *
      (∑ i ∈ range n, f i ^ (2 * m - 1) * (f (i + 1) - f i)) +
      (2 * m : ℝ) ^ 2 * (PMax (fun i => |f i|) n) ^ (2 * m - 2) *
        (∑ i ∈ range n, (f (i + 1) - f i) ^ 2) := by
  let S := PMax (fun i => |f i|) n
  have hS : 0 ≤ S := (abs_nonneg (f 0)).trans
    (le_sup' (fun i => |f i|) (mem_range.mpr (by omega)))
  have hstep : ∀ i ∈ range n,
      f (i + 1) ^ (2 * m) - f i ^ (2 * m) ≤
        (2 * m : ℝ) * f i ^ (2 * m - 1) * (f (i + 1) - f i) +
        (2 * m : ℝ) ^ 2 * S ^ (2 * m - 2) * (f (i + 1) - f i) ^ 2 := by
    intro i hi
    have hin := mem_range.mp hi
    have hrem := power_remainder_bound (f i) (f (i + 1)) S hS
      (le_sup' (fun i => |f i|) (mem_range.mpr (by omega)))
      (le_sup' (fun i => |f i|) (mem_range.mpr (by omega))) (2 * m - 2)
    have hq : 2 * m - 2 + 2 = 2 * m := by omega
    have hr : 2 * m - 2 + 1 = 2 * m - 1 := by omega
    have hcast : (2 * m - 2 : ℕ) + 2 = (2 * m : ℝ) := by exact_mod_cast hq
    rw [hq, hr, hcast] at hrem
    linarith [(le_abs_self _).trans hrem]
  have hsum := sum_le_sum hstep
  rw [sum_range_sub (fun i => f i ^ (2 * m)), hf0, zero_pow (by omega), sub_zero,
    sum_add_distrib] at hsum
  simp only [mul_assoc] at hsum
  simp_rw [← mul_sum] at hsum
  simpa only [mul_assoc] using hsum

private lemma bounded_integrable {g : Ω → ℝ} (hg : StronglyMeasurable g)
    {R : ℝ} (hb : ∀ ω, |g ω| ≤ R) : Integrable g μ :=
  ⟨hg.aestronglyMeasurable, HasFiniteIntegral.of_bounded
    (ae_of_all μ (fun ω => by simpa only [Real.norm_eq_abs] using hb ω))⟩

private lemma finite_even_terminal_integral {f : ℕ → Ω → ℝ}
    (hf : Martingale f ℱ μ) (hf0 : ∀ ω, f 0 ω = 0)
    {R : ℝ} (hR : 0 ≤ R) (hbdd : ∀ i ω, |f i ω| ≤ R)
    {m : ℕ} (hm : 0 < m) (n : ℕ) :
    (∫ ω, f n ω ^ (2 * m) ∂μ) ≤ (2 * m : ℝ) ^ 2 *
      ∫ ω, (PMax (fun i => |f i ω|) n) ^ (2 * m - 2) * Quad f n ω ∂μ := by
  let S : Ω → ℝ := fun ω => PMax (fun i => |f i ω|) n
  have hSstrong : StronglyMeasurable S :=
    (prefix_max_adapted (martingale_abs_submartingale hf).stronglyAdapted n).mono (ℱ.le n)
  have hS0 : ∀ ω, 0 ≤ S ω := fun ω =>
    (abs_nonneg (f 0 ω)).trans (le_sup' (fun i => |f i ω|) (mem_range.mpr (by omega)))
  have hSR : ∀ ω, S ω ≤ R := fun ω => sup'_le _ _ (fun i _ => hbdd i ω)
  have hfn : Integrable (fun ω => f n ω ^ (2 * m)) μ :=
    bounded_integrable (((hf.stronglyMeasurable n).mono (ℱ.le n)).pow _)
      (fun ω => by rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hbdd n ω) _)
  have hdelta : ∀ i, Integrable (fun ω => (f (i + 1) ω - f i ω) ^ 2) μ := fun i =>
    bounded_integrable (R := (2 * R) ^ 2) ((((hf.stronglyMeasurable (i + 1)).mono (ℱ.le (i + 1))).sub
      ((hf.stronglyMeasurable i).mono (ℱ.le i))).pow 2)
      (fun ω => by
        rw [abs_pow]
        apply pow_le_pow_left₀ (abs_nonneg _)
        exact (abs_sub _ _).trans (by linarith [hbdd (i + 1) ω, hbdd i ω]))
  have hQ : Integrable (Quad f n) μ := integrable_finsetSum _ (fun i _ => hdelta i)
  have hSQ : Integrable (fun ω => S ω ^ (2 * m - 2) * Quad f n ω) μ :=
    hQ.bdd_mul (hSstrong.pow _).aestronglyMeasurable
      (ae_of_all μ (fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (hS0 ω) _)]
        exact pow_le_pow_left₀ (hS0 ω) (hSR ω) _))
  have hcross : ∀ i, Integrable (fun ω => f i ω ^ (2 * m - 1) *
      (f (i + 1) ω - f i ω)) μ := fun i =>
    ((hf.integrable (i + 1)).sub (hf.integrable i)).bdd_mul
      (((hf.stronglyMeasurable i).mono (ℱ.le i)).pow _).aestronglyMeasurable
      (ae_of_all μ (fun ω => by
        rw [Real.norm_eq_abs, abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) (hbdd i ω) _))
  have hcross0 : ∀ i, (∫ ω, f i ω ^ (2 * m - 1) *
      (f (i + 1) ω - f i ω) ∂μ) = 0 := fun i =>
    predictable_increment_integral_zero hf ((hf.stronglyMeasurable i).pow _) (hcross i)
  have hcsum : Integrable (fun ω => ∑ i ∈ range n,
      f i ω ^ (2 * m - 1) * (f (i + 1) ω - f i ω)) μ :=
    integrable_finsetSum _ (fun i _ => hcross i)
  have hbound := integral_mono hfn
    ((hcsum.const_mul (2 * m : ℝ)).add (hSQ.const_mul ((2 * m : ℝ) ^ 2)))
    (fun ω => by
      simpa only [Pi.add_apply, mul_assoc] using
        terminal_power_bound (fun i => f i ω) (hf0 ω) hm n)
  simp only [Pi.add_apply] at hbound
  rw [integral_add (hcsum.const_mul _) (hSQ.const_mul _), integral_const_mul,
    integral_const_mul, integral_finsetSum _ (fun i _ => hcross i)] at hbound
  simp only [hcross0, sum_const_zero, mul_zero, zero_add] at hbound
  exact hbound

private lemma finite_even_maximal_integral {f : ℕ → Ω → ℝ}
    (hf : Martingale f ℱ μ) (hf0 : ∀ ω, f 0 ω = 0)
    {R : ℝ} (hR : 0 ≤ R) (hbdd : ∀ i ω, |f i ω| ≤ R)
    {m : ℕ} (hm : 0 < m) (n : ℕ) :
    (∫ ω, (PMax (fun i => |f i ω|) n) ^ (2 * m) ∂μ) ≤
      ((2 : ℝ) ^ (2 * m + 1) * (2 * m : ℝ) ^ 2) ^ m *
        ∫ ω, (Quad f n ω) ^ m ∂μ := by
  let S : Ω → ℝ := fun ω => PMax (fun i => |f i ω|) n
  let C : ℝ := (2 : ℝ) ^ (2 * m) * (2 * m : ℝ) ^ 2
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hSstrong : StronglyMeasurable S :=
    (prefix_max_adapted (martingale_abs_submartingale hf).stronglyAdapted n).mono (ℱ.le n)
  have hS0 : ∀ ω, 0 ≤ S ω := fun ω =>
    (abs_nonneg (f 0 ω)).trans (le_sup' (fun i => |f i ω|) (mem_range.mpr (by omega)))
  have hSR : ∀ ω, S ω ≤ R := fun ω => sup'_le _ _ (fun i _ => hbdd i ω)
  have hQ0 : ∀ ω, 0 ≤ Quad f n ω := fun ω => sum_nonneg (fun i _ => sq_nonneg _)
  have hQstrong : StronglyMeasurable (Quad f n) :=
    Finset.stronglyMeasurable_fun_sum _ (fun i _ =>
      ((((hf.stronglyMeasurable (i + 1)).mono (ℱ.le (i + 1))).sub
        ((hf.stronglyMeasurable i).mono (ℱ.le i))).pow 2))
  have hQR : ∀ ω, Quad f n ω ≤ (n : ℝ) * (2 * R) ^ 2 := by
    intro ω
    have ht : ∀ i ∈ range n, (f (i + 1) ω - f i ω) ^ 2 ≤ (2 * R) ^ 2 := by
      intro i _
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _)
        ((abs_sub _ _).trans (show |f (i + 1) ω| + |f i ω| ≤ 2 * R by
          linarith [hbdd (i + 1) ω, hbdd i ω])) 2
    exact (sum_le_sum ht).trans_eq (by simp)
  have hSQpow : Integrable (fun ω => S ω ^ (2 * m)) μ :=
    bounded_integrable (hSstrong.pow _) (fun ω => by
      rw [abs_of_nonneg (pow_nonneg (hS0 ω) _)]
      exact pow_le_pow_left₀ (hS0 ω) (hSR ω) _)
  have hQpow : Integrable (fun ω => (Quad f n ω) ^ m) μ :=
    bounded_integrable (hQstrong.pow _) (fun ω => by
      rw [abs_of_nonneg (pow_nonneg (hQ0 ω) _)]
      exact pow_le_pow_left₀ (hQ0 ω) (hQR ω) _)
  have hQint : Integrable (Quad f n) μ := bounded_integrable hQstrong
    (fun ω => by rw [abs_of_nonneg (hQ0 ω)]; exact hQR ω)
  have hSQ : Integrable (fun ω => S ω ^ (2 * m - 2) * Quad f n ω) μ :=
    hQint.bdd_mul (hSstrong.pow _).aestronglyMeasurable
      (ae_of_all μ (fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (hS0 ω) _)]
        exact pow_le_pow_left₀ (hS0 ω) (hSR ω) _))
  have hT0 : 0 ≤ ∫ ω, S ω ^ (2 * m) ∂μ := integral_nonneg (fun ω => pow_nonneg (hS0 ω) _)
  have hd := doob_power_bound (martingale_abs_submartingale hf)
    (fun i ω => abs_nonneg _) hbdd (2 * m - 2) n
  have hq : 2 * m - 2 + 2 = 2 * m := by omega
  have hc : ((2 * m - 2 : ℕ) : ℝ) + 1 = (2 * m : ℝ) - 1 := by
    rw [Nat.cast_sub (show 2 ≤ 2 * m by omega)]
    push_cast
    ring
  rw [hq, hc] at hd
  simp only [pow_abs_two_mul] at hd
  have hterminal := finite_even_terminal_integral hf hf0 hR hbdd hm n
  have hfirst : (∫ ω, S ω ^ (2 * m) ∂μ) ≤
      C * ∫ ω, S ω ^ (2 * m - 2) * Quad f n ω ∂μ := by
    have hfactor : (1 : ℝ) ≤ (2 * m : ℝ) - 1 := by
      have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
      linarith
    calc
      _ ≤ ((2 * m : ℝ) - 1) * (∫ ω, S ω ^ (2 * m) ∂μ) := by nlinarith
      _ ≤ (2 : ℝ) ^ (2 * m) * ∫ ω, f n ω ^ (2 * m) ∂μ := hd
      _ ≤ (2 : ℝ) ^ (2 * m) * ((2 * m : ℝ) ^ 2 *
          ∫ ω, S ω ^ (2 * m - 2) * Quad f n ω ∂μ) :=
        mul_le_mul_of_nonneg_left hterminal (by positivity)
      _ = _ := by dsimp [C]; ring
  have hy : ∀ ω, 2 * (m : ℝ) * C * (S ω ^ (2 * m - 2) * Quad f n ω) ≤
      ((m : ℝ) - 1) * S ω ^ (2 * m) + (2 * C) ^ m * (Quad f n ω) ^ m := by
    intro ω
    have h := pow_add_mul_le_add_pow (sq_nonneg (S ω))
      (show 0 ≤ 2 * S ω ^ 2 + (2 * C * Quad f n ω - S ω ^ 2) by
        nlinarith [hQ0 ω, sq_nonneg (S ω)]) m
    simp only [add_sub_cancel, ← pow_mul, show 2 * (m - 1) = 2 * m - 2 by omega,
      mul_pow] at h
    have hpow : S ω ^ (2 * m - 2) * S ω ^ 2 = S ω ^ (2 * m) := by
      rw [← pow_add, show 2 * m - 2 + 2 = 2 * m by omega]
    simp only [mul_pow]
    nlinarith [congrArg (fun z : ℝ => (m : ℝ) * z) hpow]
  have hyint := integral_mono (hSQ.const_mul (2 * (m : ℝ) * C))
    ((hSQpow.const_mul ((m : ℝ) - 1)).add (hQpow.const_mul ((2 * C) ^ m))) hy
  simp only [Pi.add_apply] at hyint
  rw [integral_add (hSQpow.const_mul _) (hQpow.const_mul _),
    integral_const_mul, integral_const_mul, integral_const_mul] at hyint
  have hscaled := mul_le_mul_of_nonneg_left hfirst (show 0 ≤ 2 * (m : ℝ) by positivity)
  have hm0 : 0 ≤ (m : ℝ) := by positivity
  have hfinal : (∫ ω, S ω ^ (2 * m) ∂μ) ≤
      (2 * C) ^ m * ∫ ω, (Quad f n ω) ^ m ∂μ := by nlinarith
  have hceq : 2 * C = (2 : ℝ) ^ (2 * m + 1) * (2 * m : ℝ) ^ 2 := by dsimp [C]; rw [pow_succ]; ring
  simpa only [hceq] using hfinal

private lemma stopped_likelihood_uniform_bound (L ξ : ℕ → Ω → ℝ) (τ : Ω → ℕ)
    (lam : ℝ) (n : ℕ) (hinit : ∀ ω, L 0 ω = 1) (hτn : ∀ ω, τ ω ≤ n)
    (hξ : ∀ i ω, |ξ i ω| ≤ 1)
    (hstep : ∀ i ω, L (i + 1) ω - L i ω =
      if i < τ ω then lam * L i ω * ξ i ω else 0) :
    ∀ i ω, |L i ω| ≤ (1 + |lam|) ^ n := by
  have hbase : (1 : ℝ) ≤ 1 + |lam| := by linarith [abs_nonneg lam]
  have hind : ∀ i ω, |L i ω| ≤ (1 + |lam|) ^ (min i (τ ω)) := by
    intro i ω
    induction i with
    | zero => simp [hinit]
    | succ i ih =>
      have hs := hstep i ω
      by_cases hi : i < τ ω
      · simp only [hi, if_true] at hs
        have heq : L (i + 1) ω = L i ω * (1 + lam * ξ i ω) := by nlinarith [hs]
        have hfac : |1 + lam * ξ i ω| ≤ 1 + |lam| := by
          calc
            _ ≤ |(1 : ℝ)| + |lam * ξ i ω| := abs_add_le _ _
            _ ≤ 1 + |lam| * 1 := by rw [abs_mul, abs_one]; gcongr; exact hξ i ω
            _ = _ := by ring
        rw [min_eq_left hi.le] at ih
        rw [min_eq_left (Nat.succ_le_of_lt hi), heq, abs_mul, pow_succ]
        exact mul_le_mul ih hfac (abs_nonneg _) (by positivity)
      · simp only [hi, if_false] at hs
        have heq : L (i + 1) ω = L i ω := sub_eq_zero.mp hs
        rw [heq, min_eq_right (show τ ω ≤ i + 1 by omega)]
        simpa only [min_eq_right (show τ ω ≤ i by omega)] using ih
  intro i ω
  exact (hind i ω).trans (pow_le_pow_right₀ hbase ((min_le_right _ _).trans (hτn ω)))

private lemma likelihood_quad_bound (L ξ : ℕ → Ω → ℝ) (τ : Ω → ℕ)
    (lam : ℝ) (n : ℕ) (hτn : ∀ ω, τ ω ≤ n) (hξ : ∀ i ω, |ξ i ω| ≤ 1)
    (hstep : ∀ i ω, L (i + 1) ω - L i ω =
      if i < τ ω then lam * L i ω * ξ i ω else 0) (ω : Ω) :
    Quad (fun i ω => L i ω - 1) n ω ≤ |lam| ^ 2 * (τ ω : ℝ) *
      (1 + PMax (fun i => |L i ω - 1|) n) ^ 2 := by
  let S := PMax (fun i => |L i ω - 1|) n
  let K := |lam| ^ 2 * (1 + S) ^ 2
  have hS0 : 0 ≤ S := (abs_nonneg (L 0 ω - 1)).trans
    (le_sup' (fun i => |L i ω - 1|) (mem_range.mpr (by omega)))
  have hterm : ∀ i ∈ range n,
      ((L (i + 1) ω - 1) - (L i ω - 1)) ^ 2 ≤ if i < τ ω then K else 0 := by
    intro i hi
    have hin := mem_range.mp hi
    rw [show (L (i + 1) ω - 1) - (L i ω - 1) = L (i + 1) ω - L i ω by ring, hstep]
    by_cases hit : i < τ ω
    · simp only [hit, if_true]
      have hL : |L i ω| ≤ 1 + S := by
        calc
          _ = |(L i ω - 1) + 1| := by congr 1; ring
          _ ≤ |L i ω - 1| + |(1 : ℝ)| := abs_add_le _ _
          _ ≤ S + 1 := by
            rw [abs_one]
            simpa only [S, add_comm] using add_le_add_right (le_sup' (s := range (n + 1))
              (fun i => |L i ω - 1|) (mem_range.mpr (show i < n + 1 by omega))) 1
          _ = _ := by ring
      have hab : |lam * L i ω * ξ i ω| ≤ |lam| * (1 + S) := by
        rw [abs_mul, abs_mul]
        calc
          _ ≤ |lam| * (1 + S) * 1 := by gcongr; exact hξ i ω
          _ = _ := mul_one _
      simpa only [K, sq_abs, mul_pow] using pow_le_pow_left₀ (abs_nonneg _) hab 2
    · simp [hit]
  have hfilter : (range n).filter (fun i => i < τ ω) = range (τ ω) := by
    ext i
    simp only [mem_filter, mem_range]
    constructor
    · exact And.right
    · intro hi
      exact ⟨lt_of_lt_of_le hi (hτn ω), hi⟩
  have hcount : (∑ i ∈ range n, if i < τ ω then K else 0) = (τ ω : ℝ) * K := by
    rw [sum_ite, hfilter]
    simp
  have h := (sum_le_sum hterm).trans_eq hcount
  dsimp [K] at h
  simpa only [mul_left_comm, mul_assoc] using h


local notation "MomentConstant" => fun m : ℕ =>
  ((2 : ℝ) ^ (2 * m + 1) * (2 * m : ℝ) ^ 2) ^ m * (2 : ℝ) ^ (2 * m)

private lemma stopping_nat_measurable {τ : Ω → ℕ}
    (hτ : IsStoppingTime ℱ (fun ω => (τ ω : WithTop ℕ))) : Measurable τ := by
  apply measurable_to_countable'
  intro k
  have h := (ℱ.le k) _ (hτ.measurableSet_eq k)
  simpa only [WithTop.coe_eq_coe] using h

private lemma stopping_power_integrable {τ : Ω → ℕ} (hτ : Measurable τ)
    {n : ℕ} (hτn : ∀ ω, τ ω ≤ n) (m : ℕ) :
    Integrable (fun ω => (τ ω : ℝ) ^ m) μ := by
  apply bounded_integrable ((hτ.cast_real).stronglyMeasurable.pow m)
  intro ω
  rw [abs_of_nonneg (by positivity)]
  exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast hτn ω) m

private lemma stopped_likelihood_absorption_aux {L : ℕ → Ω → ℝ}
    (hL : Martingale L ℱ μ) (ξ : ℕ → Ω → ℝ) (τ : Ω → ℕ)
    (hτ : Measurable τ) (lam : ℝ) (n : ℕ) (hinit : ∀ ω, L 0 ω = 1)
    (hτn : ∀ ω, τ ω ≤ n) (hξ : ∀ i ω, |ξ i ω| ≤ 1)
    (hstep : ∀ i ω, L (i + 1) ω - L i ω =
      if i < τ ω then lam * L i ω * ξ i ω else 0)
    {m : ℕ} (hm : 0 < m)
    (hsmall : 2 * MomentConstant m * |lam| ^ (2 * m) * (n : ℝ) ^ m ≤ 1) :
    (∫ ω, (PMax (fun i => |L i ω - 1|) n) ^ (2 * m) ∂μ) ≤
      2 * MomentConstant m * |lam| ^ (2 * m) * ∫ ω, (τ ω : ℝ) ^ m ∂μ := by
  let f : ℕ → Ω → ℝ := fun i ω => L i ω - 1
  let S : Ω → ℝ := fun ω => PMax (fun i => |f i ω|) n
  let R := (1 + |lam|) ^ n + 1
  let b : ℝ := ((2 : ℝ) ^ (2 * m + 1) * (2 * m : ℝ) ^ 2) ^ m
  let K : ℝ := |lam| ^ (2 * m) * (2 : ℝ) ^ (2 * m)
  have hf : Martingale f ℱ μ := hL.sub (martingale_const ℱ μ (1 : ℝ))
  have hf0 : ∀ ω, f 0 ω = 0 := fun ω => by dsimp [f]; rw [hinit]; ring
  have hfbdd : ∀ i ω, |f i ω| ≤ R := fun i ω =>
    (abs_sub _ _).trans (by
      dsimp [R]
      rw [abs_one]
      exact add_le_add_right (stopped_likelihood_uniform_bound L ξ τ lam n
        hinit hτn hξ hstep i ω) 1)
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hS0 : ∀ ω, 0 ≤ S ω := fun ω =>
    (abs_nonneg (f 0 ω)).trans
      (le_sup' (fun i => |f i ω|) (mem_range.mpr (show 0 < n + 1 by omega)))
  have hSR : ∀ ω, S ω ≤ R := fun ω => sup'_le _ _ (fun i _ => hfbdd i ω)
  have hSstrong : StronglyMeasurable S :=
    (prefix_max_adapted (martingale_abs_submartingale hf).stronglyAdapted n).mono (ℱ.le n)
  have hTint : Integrable (fun ω => S ω ^ (2 * m)) μ :=
    bounded_integrable (hSstrong.pow _) (fun ω => by
      rw [abs_of_nonneg (pow_nonneg (hS0 ω) _)]
      exact pow_le_pow_left₀ (hS0 ω) (hSR ω) _)
  have hUint := stopping_power_integrable hτ hτn m
  have hpoint : ∀ ω, (Quad f n ω) ^ m ≤
      K * ((τ ω : ℝ) ^ m + (n : ℝ) ^ m * S ω ^ (2 * m)) := by
    intro ω
    have hQ0 : 0 ≤ Quad f n ω := sum_nonneg (fun i _ => sq_nonneg _)
    have hQ := likelihood_quad_bound L ξ τ lam n hτn hξ hstep ω
    have hp := pow_le_pow_left₀ hQ0 hQ m
    have hplus : (1 + S ω) ^ (2 * m) ≤
        (2 : ℝ) ^ (2 * m) * (1 + S ω ^ (2 * m)) := by
      have h := add_pow_le (show (0 : ℝ) ≤ 1 by norm_num) (hS0 ω) (2 * m)
      simp only [one_pow] at h
      exact h.trans (mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (Nat.sub_le _ _))
        (by positivity))
    have ht : (τ ω : ℝ) ^ m ≤ (n : ℝ) ^ m :=
      pow_le_pow_left₀ (by positivity) (by exact_mod_cast hτn ω) m
    change (Quad f n ω) ^ m ≤ _
    calc
      _ ≤ |lam| ^ (2 * m) * (τ ω : ℝ) ^ m * (1 + S ω) ^ (2 * m) := by
        simpa only [mul_pow, ← pow_mul] using hp
      _ ≤ |lam| ^ (2 * m) * (τ ω : ℝ) ^ m *
          ((2 : ℝ) ^ (2 * m) * (1 + S ω ^ (2 * m))) :=
        mul_le_mul_of_nonneg_left hplus (by positivity)
      _ ≤ K * ((τ ω : ℝ) ^ m + (n : ℝ) ^ m * S ω ^ (2 * m)) := by
        dsimp [K]
        nlinarith [mul_le_mul_of_nonneg_right ht (pow_nonneg (hS0 ω) (2 * m))]
  have hi := integral_mono_of_nonneg (ae_of_all μ (fun ω =>
    pow_nonneg (sum_nonneg (fun i _ => sq_nonneg _)) m))
    ((hUint.add (hTint.const_mul ((n : ℝ) ^ m))).const_mul K) (ae_of_all μ hpoint)
  simp only [Pi.add_apply] at hi
  rw [integral_const_mul, integral_add hUint (hTint.const_mul _), integral_const_mul] at hi
  have hmax := finite_even_maximal_integral hf hf0 hR hfbdd hm n
  have hT0 : 0 ≤ ∫ ω, S ω ^ (2 * m) ∂μ :=
    integral_nonneg (fun ω => pow_nonneg (hS0 ω) _)
  have hfirst := hmax.trans (mul_le_mul_of_nonneg_left hi (show 0 ≤ b by
    dsimp [b]; positivity))
  change (∫ ω, S ω ^ (2 * m) ∂μ) ≤
    b * (K * ((∫ ω, (τ ω : ℝ) ^ m ∂μ) +
      (n : ℝ) ^ m * ∫ ω, S ω ^ (2 * m) ∂μ)) at hfirst
  have hbK : b * K = MomentConstant m * |lam| ^ (2 * m) := by dsimp [b, K]; ring
  rw [← mul_assoc, hbK] at hfirst
  have hs := mul_le_mul_of_nonneg_right hsmall hT0
  nlinarith

end D5.S3.Estimation.SequentialDecisionRisk.StoppedLikelihoodAbsorption
