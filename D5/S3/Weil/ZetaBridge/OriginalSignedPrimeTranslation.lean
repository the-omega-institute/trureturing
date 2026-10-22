/- GID: D5/S3/Weil/ZetaBridge/OriginalSignedPrimeTranslation
   generality: G
   mirror-B: D5/B/S3/Weil/ZetaBridge/OriginalSignedPrimeTranslation
   mirror-E: none(waiver:complex-Ioc-weighted-translation)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Weil/ZetaBridge/OriginalSignedPrimeBound.original_prime80; instance=D5/S3/Weil/ZetaBridge/OriginalSignedPrimeBound.original_prime80
   digest: Continuous weighted Young and variable-certificate inference on the literal full-complex L2 form. -/

import D5.S3.Weil.ZetaBridge.OriginalSignedPrimeArithmetic
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace OriginalSignedPrimeFourier

open MeasureTheory Set
open scoped BigOperators ComplexConjugate
open PhysicalCompressedCosineMatrix
open OriginalSignedCompressedFourier
open D5.S3.Weil.ZetaBridge.PrimeJumpDecomposition (primeWeight)
open D5.S3.Weil.ZetaBridge.WeilMellinPrimeIntertwining (primeSymmetric)

lemma prime_bilinear (a : ℝ) (M : ℕ) (f : ℝ → ℂ)
    (hi : ∀ s : ℝ, Integrable (fun x => conj (f x) * compression a s f x)) :
    primeQuadratic a M f =
      ∑ q ∈ Finset.Icc 1 M, (primeWeight q : ℂ) *
        (pairing a (Real.log (q : ℝ)) (fun x => conj (f x)) f +
          pairing a (-Real.log (q : ℝ)) (fun x => conj (f x)) f) := by
  have he : (fun x => conj (f x) * primeAction a M f x) =
      (fun x => ∑ q ∈ Finset.Icc 1 M, (primeWeight q : ℂ) *
        (conj (f x) * compression a (Real.log (q : ℝ)) f x +
          conj (f x) * compression a (-Real.log (q : ℝ)) f x)) := by
    funext x
    unfold primeAction
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q _
    ring
  rw [primeQuadratic, he, integral_finsetSum _ (by
    intro q _; exact ((hi _).add (hi _)).const_mul _)]
  apply Finset.sum_congr rfl
  intro q _
  rw [integral_const_mul, integral_add (hi _) (hi _)]
  rfl

namespace Prime80

private lemma weight_nonneg (q : ℕ) : 0 ≤ primeWeight q := by
  exact D5.S3.Weil.ZetaBridge.PrimeJumpDecomposition.prime_weight_nonnegative q

private def h (x : ℝ) : ℝ := Real.cosh (x / 2)

private lemma h_pos (x : ℝ) : 0 < h x := Real.cosh_pos _

private lemma h_continuous : Continuous h := by
  unfold h
  simp_rw [Real.cosh_eq]
  fun_prop

private lemma h_even (x : ℝ) : h (-x) = h x := by
  simp only [h, neg_div, Real.cosh_neg]

private def rho (a s : ℝ) : ℝ → ℝ :=
  (overlap a s).indicator (fun x => h (x + s) / h x)

private def weightedSquare (a s : ℝ) (f : ℝ → ℂ) (x : ℝ) : ℝ :=
  rho a s x * ‖f x‖ ^ 2

private lemma rho_nonneg (a s x : ℝ) : 0 ≤ rho a s x := by
  unfold rho
  by_cases hx : x ∈ overlap a s
  · rw [Set.indicator_of_mem hx]
    exact div_nonneg (h_pos _).le (h_pos _).le
  · simp only [Set.indicator_of_notMem hx, le_refl]

private lemma h_ratio_bound (s x : ℝ) : h (x + s) / h x ≤ Real.exp (|s| / 2) := by
  have hp : Real.exp (s / 2) ≤ Real.exp (|s| / 2) :=
    Real.exp_le_exp.mpr (div_le_div_of_nonneg_right (le_abs_self s) (by norm_num))
  have hm : Real.exp (-s / 2) ≤ Real.exp (|s| / 2) :=
    Real.exp_le_exp.mpr (div_le_div_of_nonneg_right (neg_le_abs s) (by norm_num))
  have hs : h (x + s) =
      (Real.exp (x / 2) * Real.exp (s / 2) +
        Real.exp (-x / 2) * Real.exp (-s / 2)) / 2 := by
    have he₁ : Real.exp ((x + s) / 2) = Real.exp (x / 2) * Real.exp (s / 2) := by
      rw [← Real.exp_add]; congr 1 <;> ring
    have he₂ : Real.exp (-((x + s) / 2)) =
        Real.exp (-x / 2) * Real.exp (-s / 2) := by
      rw [← Real.exp_add]; congr 1 <;> ring
    rw [h, Real.cosh_eq, he₁, he₂]
  have hx : h x = (Real.exp (x / 2) + Real.exp (-x / 2)) / 2 := by
    simp only [h, Real.cosh_eq, neg_div]
  apply (div_le_iff₀ (h_pos x)).mpr
  rw [hs, hx]
  have hp' := mul_le_mul_of_nonneg_left hp (Real.exp_pos (x / 2)).le
  have hm' := mul_le_mul_of_nonneg_left hm (Real.exp_pos (-x / 2)).le
  nlinarith

private lemma rho_measurable (a s : ℝ) : Measurable (rho a s) := by
  exact (((h_continuous.comp (continuous_id.add continuous_const)).div h_continuous
    (fun x => (h_pos x).ne')).measurable).indicator measurableSet_Ioc

private lemma rho_norm_bound (a s x : ℝ) : ‖rho a s x‖ ≤ Real.exp (|s| / 2) := by
  rw [Real.norm_eq_abs, abs_of_nonneg (rho_nonneg a s x)]
  by_cases hx : x ∈ overlap a s
  · simpa only [rho, Set.indicator_of_mem hx] using h_ratio_bound s x
  · simpa only [rho, Set.indicator_of_notMem hx] using (Real.exp_pos (|s| / 2)).le

private lemma square_indicator_integrable (a : ℝ) {f : ℝ → ℂ}
    (hf : MemLp f 2 (volume.restrict (window a))) :
    Integrable ((window a).indicator (fun x => ‖f x‖ ^ 2)) := by
  have hi := (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf
  exact (integrable_indicator_iff (s := window a) measurableSet_Ioc).mpr hi

private lemma weightedSquare_integrable (a s : ℝ) {f : ℝ → ℂ}
    (hf : MemLp f 2 (volume.restrict (window a))) : Integrable (weightedSquare a s f) := by
  have hi := (square_indicator_integrable a hf).bdd_mul
    (c := Real.exp (|s| / 2)) (rho_measurable a s).aestronglyMeasurable
    (Filter.Eventually.of_forall (rho_norm_bound a s))
  apply hi.congr
  exact Filter.Eventually.of_forall fun x => by
    by_cases hx : x ∈ window a
    · simp only [Set.indicator_of_mem hx, weightedSquare]
    · have hn : x ∉ overlap a s := fun h => hx ((overlap_mem a s x).mp h).1
      simp only [Set.indicator_of_notMem hx, weightedSquare, rho,
        Set.indicator_of_notMem hn, mul_zero, zero_mul]

private lemma zeroExtension_memLp (a : ℝ) {f : ℝ → ℂ}
    (hf : MemLp f 2 (volume.restrict (window a))) :
    MemLp (zeroExtension a f) 2 (volume : Measure ℝ) := by
  have hf' : MemLp f 2 (volume.restrict (Ioc (-a) (-a + 2 * a))) := by
    simpa only [show -a + 2 * a = a by ring, window] using hf
  simpa only [D5.S3.Weil.ZetaGamma.PeriodicEnergyTransport.zeroExtension,
    zeroExtension, window, show -a + 2 * a = a by ring] using
    D5.S3.Weil.ZetaGamma.PeriodicEnergyTransport.zero_extension_memLp (2 * a) (-a) f hf'

-- Reuse the existing arbitrary-complex L2 correlation theorem; no new
-- Holder/Cauchy--Schwarz, Fourier density or prime-factorization proof.
private lemma integrable_l2_compression (a s : ℝ) {f : ℝ → ℂ}
    (hf : MemLp f 2 (volume.restrict (window a))) :
    Integrable (fun x => conj (f x) * compression a s f x) := by
  have hF := zeroExtension_memLp a hf
  have hFs := hF.comp_measurePreserving
    (measurePreserving_add_right (volume : Measure ℝ) s)
  have hi := D5.S3.Weil.ZetaGamma.PeriodicEnergyTransport.l2_complex_correlation_integrable hF hFs
  apply hi.congr
  exact Filter.Eventually.of_forall fun x => by
    by_cases hx : x ∈ window a <;>
      simp [Function.comp_def, compression, zeroExtension, hx]

private lemma weighted_young (A B u v : ℝ) (hA : 0 < A) (hB : 0 < B) :
    2 * u * v ≤ B / A * u ^ 2 + A / B * v ^ 2 := by
  have h₁ : B / A * u ^ 2 = B ^ 2 * u ^ 2 / (A * B) := by
    field_simp [hA.ne', hB.ne']
    <;> ring
  have h₂ : A / B * v ^ 2 = A ^ 2 * v ^ 2 / (A * B) := by
    field_simp [hA.ne', hB.ne']
    <;> ring
  rw [h₁, h₂, ← add_div]
  apply (le_div_iff₀ (mul_pos hA hB)).mpr
  nlinarith [sq_nonneg (B * u - A * v)]

private lemma weighted_young_compression (a s : ℝ) (f : ℝ → ℂ) (x : ℝ) :
    2 * ‖conj (f x) * compression a s f x‖ ≤
      weightedSquare a s f x + weightedSquare a (-s) f (x + s) := by
  have hs : x + s ∈ overlap a (-s) ↔ x ∈ overlap a s := by
    rw [overlap_mem, overlap_mem]
    simp only [add_neg_cancel_right, and_comm]
  by_cases hx : x ∈ overlap a s
  · obtain ⟨hx₀, hx₁⟩ := (overlap_mem a s x).mp hx
    have hb := hs.mpr hx
    simpa [weightedSquare, rho, hx, hb, compression, zeroExtension, hx₀, hx₁,
      norm_mul, Complex.norm_conj, mul_assoc] using
      weighted_young (h x) (h (x + s)) ‖f x‖ ‖f (x + s)‖ (h_pos _) (h_pos _)
  · have hb := mt hs.mp hx
    have hz' : conj (f x) * compression a s f x = 0 := by
      have he := congrFun (compression_product a s (fun y => conj (f y)) f) x
      simpa only [Set.indicator_of_notMem hx] using he
    simp [hz', weightedSquare, rho, hx, hb]

private lemma pairing_weighted_young (a s : ℝ) {f : ℝ → ℂ}
    (hf : MemLp f 2 (volume.restrict (window a))) :
    2 * ‖pairing a s (fun x => conj (f x)) f‖ ≤
      (∫ x, weightedSquare a s f x) + (∫ x, weightedSquare a (-s) f x) := by
  have hi := integrable_l2_compression a s hf
  have hp := weightedSquare_integrable a s hf
  have hm := weightedSquare_integrable a (-s) hf
  have hms : Integrable (fun x => weightedSquare a (-s) f (x + s)) :=
    hm.comp_add_right s
  have hb := integral_mono (hi.norm.const_mul 2) (hp.add hms)
    (weighted_young_compression a s f)
  change (∫ x, 2 * ‖conj (f x) * compression a s f x‖) ≤
    ∫ x, weightedSquare a s f x + weightedSquare a (-s) f (x + s) at hb
  rw [integral_const_mul, integral_add hp hms,
    integral_add_right_eq_self (weightedSquare a (-s) f) s] at hb
  exact (mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (by norm_num)).trans hb

private lemma paired_weighted_young (a s : ℝ) {f : ℝ → ℂ}
    (hf : MemLp f 2 (volume.restrict (window a))) :
    ‖pairing a s (fun x => conj (f x)) f +
        pairing a (-s) (fun x => conj (f x)) f‖ ≤
      (∫ x, weightedSquare a s f x) + (∫ x, weightedSquare a (-s) f x) := by
  have hp := pairing_weighted_young a s hf
  have hm := pairing_weighted_young a (-s) hf
  simp only [neg_neg] at hm
  have ht := norm_add_le (pairing a s (fun x => conj (f x)) f)
    (pairing a (-s) (fun x => conj (f x)) f)
  linarith

private def actualRow (a : ℝ) (M : ℕ) (x : ℝ) : ℝ :=
  ∑ q ∈ Finset.Icc 1 M, primeWeight q *
    (rho a (Real.log (q : ℝ)) x + rho a (-Real.log (q : ℝ)) x)

-- This estimates the LITERAL original complex form, not a finite matrix
-- supplied as a premise and not a substitute integral kernel.
private theorem primeQuadratic_weightedYoung (a : ℝ) (M : ℕ)
    {f : ℝ → ℂ} (hf : MemLp f 2 (volume.restrict (window a))) :
    ‖primeQuadratic a M f‖ ≤ ∫ x, actualRow a M x * ‖f x‖ ^ 2 := by
  have hi (q : ℕ) : Integrable (fun x => primeWeight q *
      (weightedSquare a (Real.log (q : ℝ)) f x +
        weightedSquare a (-Real.log (q : ℝ)) f x)) :=
    ((weightedSquare_integrable _ _ hf).add
      (weightedSquare_integrable _ _ hf)).const_mul _
  rw [prime_bilinear a M f (fun s => integrable_l2_compression a s hf)]
  calc
    _ ≤ ∑ q ∈ Finset.Icc 1 M, primeWeight q *
        ((∫ x, weightedSquare a (Real.log (q : ℝ)) f x) +
          (∫ x, weightedSquare a (-Real.log (q : ℝ)) f x)) := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro q _
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (weight_nonneg q)]
      exact mul_le_mul_of_nonneg_left (paired_weighted_young a _ hf) (weight_nonneg q)
    _ = ∫ x, actualRow a M x * ‖f x‖ ^ 2 := by
      rw [show (fun x => actualRow a M x * ‖f x‖ ^ 2) =
        (fun x => ∑ q ∈ Finset.Icc 1 M, primeWeight q *
          (weightedSquare a (Real.log (q : ℝ)) f x +
            weightedSquare a (-Real.log (q : ℝ)) f x)) by
          funext x
          unfold actualRow weightedSquare
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro q _
          ring]
      rw [integral_finsetSum _ (fun q _ => hi q)]
      apply Finset.sum_congr rfl
      intro q _
      rw [integral_const_mul, integral_add
        (weightedSquare_integrable _ _ hf) (weightedSquare_integrable _ _ hf)]

private lemma h_exp (x : ℝ) :
    h x = Real.exp (-x / 2) * (Real.exp x + 1) / 2 := by
  have he : Real.exp (x / 2) = Real.exp (-x / 2) * Real.exp x := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [h, Real.cosh_eq, show -(x / 2) = -x / 2 by ring, he]
  ring

private lemma exp_half_log {q : ℝ} (hq : 0 < q) :
    Real.exp (Real.log q / 2) = Real.sqrt q := by
  rw [← Real.log_sqrt hq.le, Real.exp_log (Real.sqrt_pos.mpr hq)]

-- Both identities keep the ORIGINAL weight and the ORIGINAL signed shift.
private lemma cosh_plus_identity {q : ℝ} (hq : 0 < q) (p x : ℝ) :
    (Real.log p / Real.sqrt q) * (h (x + Real.log q) / h x) =
      Real.log p * (Real.exp x + 1 / q) / (Real.exp x + 1) := by
  have hd := Real.sqrt_pos.mpr hq
  have hs := Real.sq_sqrt hq.le
  have he := Real.exp_pos (-x / 2)
  have hr : 0 < Real.exp x + 1 := by positivity
  rw [h_exp, h_exp, show -(x + Real.log q) / 2 = -x / 2 - Real.log q / 2 by ring,
    Real.exp_sub, exp_half_log hq, Real.exp_add, Real.exp_log hq]
  generalize Real.sqrt q = d at *
  rw [← hs]
  field_simp [hd.ne', he.ne', hr.ne']
  <;> ring

private lemma cosh_minus_identity {q : ℝ} (hq : 0 < q) (p x : ℝ) :
    (Real.log p / Real.sqrt q) * (h (x - Real.log q) / h x) =
      Real.log p * (Real.exp x / q + 1) / (Real.exp x + 1) := by
  have hd := Real.sqrt_pos.mpr hq
  have he := Real.exp_pos (-x / 2)
  have hr : 0 < Real.exp x + 1 := by positivity
  rw [h_exp, h_exp, show -(x - Real.log q) / 2 = -x / 2 + Real.log q / 2 by ring,
    Real.exp_add, exp_half_log hq, Real.exp_sub, Real.exp_log hq]
  field_simp [hd.ne', he.ne', hr.ne', hq.ne']
  <;> ring

def halfWindow : ℝ := Real.log 71

private lemma exp_halfWindow : Real.exp halfWindow = 71 := Real.exp_log (by norm_num)

private def closedRho (s x : ℝ) : ℝ :=
  if |x + s| ≤ halfWindow then h (x + s) / h x else 0

private lemma closedRho_nonneg (s x : ℝ) : 0 ≤ closedRho s x := by
  unfold closedRho
  split_ifs
  · exact div_nonneg (h_pos _).le (h_pos _).le
  · exact le_rfl

private lemma closedRho_reflect (s x : ℝ) : closedRho s (-x) = closedRho (-s) x := by
  unfold closedRho
  rw [show -x + s = -(x + -s) by ring, abs_neg, h_even, h_even]

private lemma rho_le_closed {a : ℝ} (ha : a ≤ halfWindow) (s x : ℝ) :
    rho a s x ≤ closedRho s x := by
  by_cases hx : x ∈ overlap a s
  · have hy := ((overlap_mem a s x).mp hx).2
    have hc : |x + s| ≤ halfWindow :=
      (abs_le.mpr ⟨by linarith [hy.1], hy.2⟩).trans ha
    simp [rho, closedRho, hx, hc]
  · simpa only [rho, Set.indicator_of_notMem hx] using closedRho_nonneg s x

private lemma rho_eq_ratio_compression (a s x : ℝ) :
    rho a s x = (h (x + s) / h x) *
      compression a s (fun _ : ℝ => (1 : ℝ)) x := by
  by_cases hx : x ∈ window a <;> by_cases hs : x + s ∈ window a <;>
    simp [rho, compression, zeroExtension, (overlap_mem a s x), hx, hs]

private lemma rho_zero_right (a s : ℝ) (hs : 2 * a ≤ s) : rho a s = 0 := by
  funext x
  rw [rho_eq_ratio_compression, compression_zero_right a s _ hs]
  simp

private lemma rho_zero_left (a s : ℝ) (hs : s ≤ -(2 * a)) : rho a s = 0 := by
  funext x
  rw [rho_eq_ratio_compression, compression_zero_left a s _ hs]
  simp

private lemma actualRow_mono (a : ℝ) {M N : ℕ} (hMN : M ≤ N) (x : ℝ) :
    actualRow a M x ≤ actualRow a N x := by
  unfold actualRow
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro q hq
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hq).1, (Finset.mem_Icc.mp hq).2.trans hMN⟩
  · intro q _ _
    exact mul_nonneg (weight_nonneg q) (add_nonneg (rho_nonneg _ _ _) (rho_nonneg _ _ _))

private lemma actualRow_integrable (a : ℝ) (M : ℕ) {f : ℝ → ℂ}
    (hf : MemLp f 2 (volume.restrict (window a))) :
    Integrable (fun x => actualRow a M x * ‖f x‖ ^ 2) := by
  have he : (fun x => actualRow a M x * ‖f x‖ ^ 2) =
      (fun x => ∑ q ∈ Finset.Icc 1 M, primeWeight q *
        (weightedSquare a (Real.log (q : ℝ)) f x +
          weightedSquare a (-Real.log (q : ℝ)) f x)) := by
    funext x
    unfold actualRow weightedSquare
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro q _
    ring
  rw [he]
  apply integrable_finsetSum
  intro q _
  exact ((weightedSquare_integrable _ _ hf).add
    (weightedSquare_integrable _ _ hf)).const_mul _

private lemma actualRow_zero_outside (a : ℝ) (M : ℕ) {x : ℝ}
    (hx : x ∉ window a) : actualRow a M x = 0 := by
  have hz (s : ℝ) : rho a s x = 0 := by
    have hn : x ∉ overlap a s := fun h => hx ((overlap_mem a s x).mp h).1
    simp only [rho, Set.indicator_of_notMem hn]
  simp only [actualRow, hz, add_zero, mul_zero, Finset.sum_const_zero]

lemma original_prime_integral (a : ℝ) (M : ℕ) (f : ℝ → ℂ) :
    (∫ x in window a, conj (zeroExtension a f x) *
      (-primeSymmetric a M (zeroExtension a f) x)) = -primeQuadratic a M f := by
  rw [primeQuadratic_physical, ← integral_neg]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro x hx
  have hF : zeroExtension a f x = f x := Set.indicator_of_mem hx _
  dsimp only
  rw [hF, ← primeAction_existing a M f x hx]
  ring


variable {ts : List Row} {cs : List Cell}

private def closedTerm (t : Row) (x : ℝ) : ℝ :=
  primeWeight t.q * (closedRho (Real.log (t.q : ℝ)) x +
    closedRho (-Real.log (t.q : ℝ)) x)

private def closedRow (ts : List Row) (x : ℝ) : ℝ := (ts.map (fun t => closedTerm t x)).sum

private lemma closedRow_even (ts : List Row) (x : ℝ) : closedRow ts (-x) = closedRow ts x := by
  unfold closedRow
  congr 1
  apply List.map_congr_left
  intro t _
  simp only [closedTerm, closedRho_reflect, neg_neg]
  ring

private lemma row_coefficient_bounds (ac : ArithmeticCertificate ts) (t : Row) (ht : t ∈ ts) {x : ℝ} :
    primeWeight t.q * (h (x + Real.log (t.q : ℝ)) / h x) ≤ plus t (Real.exp x) ∧
      primeWeight t.q * (h (x - Real.log (t.q : ℝ)) / h x) ≤ minus t (Real.exp x) := by
  have hq : (0 : ℝ) < t.q := by
    have := (row_of_mem ac ht).1
    exact_mod_cast (by omega : 0 < t.q)
  have hb := row_log_bounds ac t ht
  have hr := (Real.exp_pos x).le
  have hd : 0 < Real.exp x + 1 := by positivity
  rw [weight_row ac t ht, cosh_plus_identity hq, cosh_minus_identity hq]
  constructor
  · calc
      _ = (Real.exp x * Real.log (t.p : ℝ) + Real.log (t.p : ℝ) / t.q) /
          (Real.exp x + 1) := by ring
      _ ≤ (Real.exp x * ((t.b : ℝ) / 1000000) + (t.a : ℝ) / 1000000) /
          (Real.exp x + 1) :=
        div_le_div_of_nonneg_right (add_le_add
          (mul_le_mul_of_nonneg_left hb.2 hr) hb.1) hd.le
      _ = plus t (Real.exp x) := by unfold plus; field_simp [hd.ne']
  · calc
      _ = (Real.exp x * (Real.log (t.p : ℝ) / t.q) + Real.log (t.p : ℝ)) /
          (Real.exp x + 1) := by ring
      _ ≤ (Real.exp x * ((t.a : ℝ) / 1000000) + (t.b : ℝ) / 1000000) /
          (Real.exp x + 1) :=
        div_le_div_of_nonneg_right (add_le_add
          (mul_le_mul_of_nonneg_left hb.1 hr) hb.2) hd.le
      _ = minus t (Real.exp x) := by unfold minus; field_simp [hd.ne']

private lemma closedTerm_le_rounded (ac : ArithmeticCertificate ts) (t : Row) (ht : t ∈ ts) (x : ℝ) :
    closedTerm t x ≤ rowTerm t (Real.exp x) := by
  have hq : (0 : ℝ) < t.q := by
    have := (row_of_mem ac ht).1
    exact_mod_cast (by omega : 0 < t.q)
  have hb := row_coefficient_bounds ac t ht (x := x)
  unfold closedTerm rowTerm
  rw [mul_add]
  apply add_le_add
  · by_cases hx : |x + Real.log (t.q : ℝ)| ≤ halfWindow
    · have hflag : (t.q : ℝ) * Real.exp x ≤ 71 := by
        have he := Real.exp_le_exp.mpr ((le_abs_self _).trans hx)
        rw [Real.exp_add, Real.exp_log hq, exp_halfWindow] at he
        simpa only [mul_comm] using he
      simpa [closedRho, hx, hflag] using hb.1
    · simp only [closedRho, if_neg hx, mul_zero]
      split_ifs <;> first | exact plus_nonneg t (Real.exp_pos x).le | exact le_rfl
  · by_cases hx : |x + -Real.log (t.q : ℝ)| ≤ halfWindow
    · have hflag : (t.q : ℝ) ≤ 71 * Real.exp x := by
        have hl := (neg_le_neg hx).trans (neg_abs_le (x + -Real.log (t.q : ℝ)))
        have hl' : Real.log (t.q : ℝ) ≤ x + halfWindow := by linarith
        have he := Real.exp_le_exp.mpr hl'
        rw [Real.exp_log hq, Real.exp_add, exp_halfWindow] at he
        simpa only [mul_comm] using he
      simpa [closedRho, hx, hflag, sub_eq_add_neg] using hb.2
    · simp only [closedRho, if_neg hx, mul_zero]
      split_ifs <;> first | exact minus_nonneg t (Real.exp_pos x).le | exact le_rfl

private lemma closedRow_lt_eighty (ac : ArithmeticCertificate ts)
    (cc : CellCertificate ts cs) {x : ℝ} (hx : |x| ≤ halfWindow) : closedRow ts x < 80 := by
  have he : closedRow ts x = closedRow ts |x| := by
    rcases le_or_gt 0 x with hp | hn
    · rw [abs_of_nonneg hp]
    · rw [abs_of_neg hn, closedRow_even ts]
  have hb : closedRow ts |x| ≤ roundedRow ts (Real.exp |x|) := by
    unfold closedRow roundedRow
    exact List.sum_le_sum (fun t ht => closedTerm_le_rounded ac t ht |x|)
  have hl : 1 ≤ Real.exp |x| := by
    simpa only [Real.exp_zero] using Real.exp_le_exp.mpr (abs_nonneg x)
  have hr : Real.exp |x| ≤ 71 := by
    simpa only [exp_halfWindow] using Real.exp_le_exp.mpr hx
  rw [he]
  exact hb.trans_lt (roundedRow_lt_eighty (fun t ht => (row_of_mem ac ht).2.2.2.1) cc hl hr)

lemma log_5041 : Real.log (5041 : ℝ) = 2 * halfWindow := by
  have he : (5041 : ℝ) = 71 ^ (2 : ℕ) := by norm_num
  rw [he, Real.log_pow]
  rfl

-- 5041 is INCLUDED in actualRow. Its density weight is NOT set to zero.
-- Only the two endpoint compressions are zero, by the existing owner.
private lemma actualRow_table (ac : ArithmeticCertificate ts) {a : ℝ} (ha : a ≤ halfWindow) (x : ℝ) :
    actualRow a 5041 x = (ts.map (fun t => primeWeight t.q *
      (rho a (Real.log (t.q : ℝ)) x + rho a (-Real.log (t.q : ℝ)) x))).sum := by
  let Q := (ts.map Row.q).toFinset
  let G := fun q : ℕ => primeWeight q *
    (rho a (Real.log (q : ℝ)) x + rho a (-Real.log (q : ℝ)) x)
  have hsub : Q ⊆ Finset.Icc 1 5041 := by
    intro q hq
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hq)
    have hr := row_of_mem ac ht
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have hsum : (∑ q ∈ Finset.Icc 1 5041, G q) = ∑ q ∈ Q, G q := by
    symm
    apply Finset.sum_subset hsub
    intro q hq hmiss
    by_cases he : q = 5041
    · subst q
      have hs : 2 * a ≤ Real.log (5041 : ℝ) := by rw [log_5041]; linarith
      change primeWeight 5041 * (rho a (Real.log (5041 : ℝ)) x +
        rho a (-Real.log (5041 : ℝ)) x) = 0
      rw [rho_zero_right a (Real.log (5041 : ℝ)) hs,
        rho_zero_left a (-Real.log (5041 : ℝ)) (by linarith)]
      simp
    · have hq' : q < 5041 := by have := (Finset.mem_Icc.mp hq).2; omega
      have hz := weight_zero_of_missing ac hq' (by simpa [Q] using hmiss)
      simp [G, hz]
  change (∑ q ∈ Finset.Icc 1 5041, G q) = _
  rw [hsum, List.sum_toFinset G ac.nodup]
  simp only [List.map_map, Function.comp_def, G]

private lemma actualRow_le_closed (ac : ArithmeticCertificate ts) {a : ℝ} (ha : a ≤ halfWindow) (x : ℝ) :
    actualRow a 5041 x ≤ closedRow ts x := by
  rw [actualRow_table ac ha]
  unfold closedRow
  apply List.sum_le_sum
  intro t _
  exact mul_le_mul_of_nonneg_left (add_le_add (rho_le_closed ha _ x)
    (rho_le_closed ha _ x)) (weight_nonneg t.q)

private lemma actualRow_lt_eighty (ac : ArithmeticCertificate ts)
    (cc : CellCertificate ts cs) {a : ℝ} (ha : a ≤ halfWindow) {M : ℕ}
    (hM : M ≤ 5041) {x : ℝ} (hx : x ∈ window a) : actualRow a M x < 80 := by
  have habs : |x| ≤ halfWindow := (abs_le.mpr ⟨hx.1.le, hx.2⟩).trans ha
  exact ((actualRow_mono a hM x).trans (actualRow_le_closed ac ha x)).trans_lt
    (closedRow_lt_eighty ac cc habs)

theorem memLp_quadratic_prime80 (ac : ArithmeticCertificate ts)
    (cc : CellCertificate ts cs) {a : ℝ} (ha : a ≤ halfWindow) {M : ℕ}
    (hM : M ≤ 5041) {f : ℝ → ℂ}
    (hf : MemLp f 2 (volume.restrict (window a))) :
    ‖primeQuadratic a M f‖ ≤ 80 * ∫ x in window a, ‖f x‖ ^ 2 := by
  have hi := square_indicator_integrable a hf
  have hb : (∫ x, actualRow a M x * ‖f x‖ ^ 2) ≤
      ∫ x, 80 * (window a).indicator (fun y => ‖f y‖ ^ 2) x := by
    apply integral_mono (actualRow_integrable a M hf) (hi.const_mul 80)
    intro x
    change actualRow a M x * ‖f x‖ ^ 2 ≤
      80 * (window a).indicator (fun y => ‖f y‖ ^ 2) x
    by_cases hx : x ∈ window a
    · rw [Set.indicator_of_mem hx]
      exact mul_le_mul_of_nonneg_right (actualRow_lt_eighty ac cc ha hM hx).le (sq_nonneg _)
    · simp only [Set.indicator_of_notMem hx, actualRow_zero_outside a M hx, mul_zero, zero_mul]
      exact le_rfl
  rw [integral_const_mul, integral_indicator (s := window a) measurableSet_Ioc] at hb
  exact (primeQuadratic_weightedYoung a M hf).trans hb

end Prime80
end OriginalSignedPrimeFourier
