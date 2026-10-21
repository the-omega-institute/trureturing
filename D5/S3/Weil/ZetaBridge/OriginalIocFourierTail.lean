/- GID: D5/S3/Weil/ZetaBridge/OriginalIocFourierTail
   generality: G
   mirror-B: D5/B/S3/Weil/ZetaBridge/OriginalIocFourierTail
   mirror-E: none(waiver:infinite-dimensional-analytic-estimate)
   anchors: []
   utility: none
   digest: Identify the actual arbitrary-L2 exterior transform, its mass and physical leakage. -/

import D5.S3.Weil.ZetaBridge.OriginalIocFourierEvaluation
import D5.S3.Weil.ZetaBridge.WeilInfiniteComplementLeakage
import Mathlib.Tactic.LinearCombination

open scoped BigOperators ComplexConjugate
open MeasureTheory Set Zeta23
noncomputable section
namespace D5.S3.Weil.ZetaBridge.OriginalIocFourier

def positiveTail (N : ℕ) (z : ℤ → ℂ) : ℕ → ℂ :=
  fun j ↦ z ((N : ℤ) + (j : ℤ) + 1)

def negativeTail (N : ℕ) (z : ℤ → ℂ) : ℕ → ℂ :=
  fun j ↦ z (-((N : ℤ) + (j : ℤ) + 1))

def squareMass (u : ℕ → ℂ) : ℝ := ∑' j : ℕ, ‖u j‖ ^ 2

/-- Explicit public expression. The leakage owner's private Cauchy helper
is not referenced: its defining series is used literally here. -/
def exteriorSeries (N : ℕ) (z : ℤ → ℂ) (s : ℝ) : ℂ :=
  (∑' j : ℕ, positiveTail N z j * (((N : ℝ) + s + (j : ℝ) + 1)⁻¹ : ℝ)) -
  (∑' j : ℕ, negativeTail N z j * (((N : ℝ) - s + (j : ℝ) + 1)⁻¹ : ℝ))

private theorem positive_index_injective (N : ℕ) :
    Function.Injective (fun j : ℕ ↦ (N : ℤ) + (j : ℤ) + 1) := by
  intro i j h
  dsimp only at h
  omega

private theorem negative_index_injective (N : ℕ) :
    Function.Injective (fun j : ℕ ↦ -((N : ℤ) + (j : ℤ) + 1)) := by
  intro i j h
  dsimp only at h
  omega

/-- Reindex a genuinely summable two-sided series after its low modes vanish.
The shift N+1 on the nonnegative side and N on Int.negSucc are both paid. -/
private theorem tsum_eq_two_exterior_tails {E : Type*} [NormedAddCommGroup E]
    [CompleteSpace E] (N : ℕ) (z : ℤ → E) (hz : Summable z)
    (hzero : ∀ n : ℤ, |n| ≤ (N : ℤ) → z n = 0) :
    (∑' n : ℤ, z n) =
      (∑' j : ℕ, z ((N : ℤ) + (j : ℤ) + 1)) +
      (∑' j : ℕ, z (-((N : ℤ) + (j : ℤ) + 1))) := by
  classical
  have hp : Summable (fun j : ℕ ↦ z (j : ℤ)) :=
    hz.comp_injective (show Function.Injective (fun j : ℕ ↦ (j : ℤ)) from
      Nat.cast_injective)
  have hm : Summable (fun j : ℕ ↦ z (-((j : ℤ) + 1))) :=
    hz.comp_injective (by
      intro i j hij
      dsimp only at hij
      omega)
  have hp0 : (∑ j ∈ Finset.range (N + 1), z (j : ℤ)) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    apply hzero
    rw [abs_of_nonneg (by omega : 0 ≤ (j : ℤ))]
    have := Finset.mem_range.mp hj
    omega
  have hm0 : (∑ j ∈ Finset.range N, z (-((j : ℤ) + 1))) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    apply hzero
    rw [abs_neg, abs_of_nonneg (by omega : 0 ≤ (j : ℤ) + 1)]
    have := Finset.mem_range.mp hj
    omega
  have hpt : (∑' j : ℕ, z ((N : ℤ) + (j : ℤ) + 1)) = ∑' j : ℕ, z (j : ℤ) := by
    calc
      _ = ∑' j : ℕ, z ((j + (N + 1) : ℕ) : ℤ) := by
        apply tsum_congr
        intro j
        congr 1
        omega
      _ = _ := by simpa only [hp0, zero_add] using hp.sum_add_tsum_nat_add (N + 1)
  have hmt : (∑' j : ℕ, z (-((N : ℤ) + (j : ℤ) + 1))) =
      ∑' j : ℕ, z (-((j : ℤ) + 1)) := by
    calc
      _ = ∑' j : ℕ, z (-(((j + N : ℕ) : ℤ) + 1)) := by
        apply tsum_congr
        intro j
        congr 1
        omega
      _ = _ := by simpa only [hm0, zero_add] using hm.sum_add_tsum_nat_add N
  rw [tsum_of_nat_of_neg_add_one hp hm, hpt, hmt]

private theorem signedCoeff_sq_summable {L : ℝ} (hL : 0 < L) {f : ℝ → ℂ}
    (hf : MemLp f 2 (volume.restrict (interval L))) :
    Summable (fun n : ℤ ↦ ‖signedCoeff L hL f n‖ ^ 2) := by
  simpa only [signedCoeff_sq hL] using
    (hasSum_sq_fourierCoeffOn (interval_left_lt_right hL) hf).summable.mul_left L

/-- Both actual ordered tails are square summable, and their combined mass is
exactly the original dx mass, with no reality or evenness assumption. -/
theorem signedCoeff_tail_mass {L : ℝ} (hL : 0 < L) {f : ℝ → ℂ}
    (hf : MemLp f 2 (volume.restrict (interval L))) (N : ℕ)
    (hlow : ∀ n : ℤ, |n| ≤ (N : ℤ) → signedCoeff L hL f n = 0) :
    Summable (fun j ↦ ‖positiveTail N (signedCoeff L hL f) j‖ ^ 2) ∧
    Summable (fun j ↦ ‖negativeTail N (signedCoeff L hL f) j‖ ^ 2) ∧
    squareMass (positiveTail N (signedCoeff L hL f)) +
      squareMass (negativeTail N (signedCoeff L hL f)) =
        ∫ x in (-L / 2)..(L / 2), ‖f x‖ ^ 2 := by
  have hz := signedCoeff_sq_summable hL hf
  refine ⟨hz.comp_injective (positive_index_injective N),
    hz.comp_injective (negative_index_injective N), ?_⟩
  rw [← tsum_signedCoeff_sq_eq_mass hL hf]
  exact (tsum_eq_two_exterior_tails N _ hz (fun n hn ↦ by simp [hlow n hn])).symm

theorem scaled_basis_sinc {L : ℝ} (hL : 0 < L) (n : ℤ) (s : ℝ) :
    basisPaperFT L n (2 * Real.pi * s / L) =
      phase n * (Real.sqrt L : ℂ) *
        (Real.sinc (Real.pi * (s + (n : ℝ))) : ℂ) := by
  rw [basisPaperFT_eq_sinc hL]
  have harg : (2 * Real.pi * s / L + frequency L n) * L / 2 =
      Real.pi * (s + (n : ℝ)) := by
    dsimp [frequency]
    field_simp [hL.ne', Real.pi_ne_zero]
    <;> ring
  rw [harg]
  have hs : (Real.sqrt L : ℂ) ^ 2 = (L : ℂ) := by
    exact_mod_cast Real.sq_sqrt hL.le
  have hs0 : (Real.sqrt L : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr hL)
  rw [← hs]
  field_simp [hL.ne', Real.pi_ne_zero]
  <;> ring

/-- The phase-adjusted basis loses its alternating sign away from resonance.
The all-frequency sinc statement above is retained, so no resonant mode is lost. -/
private theorem scaled_basis_rational {L : ℝ} (hL : 0 < L) (n : ℤ)
    {s : ℝ} (hs : s + (n : ℝ) ≠ 0) :
    basisPaperFT L n (2 * Real.pi * s / L) =
      ((Real.sqrt L / Real.pi * Real.sin (Real.pi * s) : ℝ) : ℂ) *
        (((s + (n : ℝ))⁻¹ : ℝ) : ℂ) := by
  rw [scaled_basis_sinc hL, Real.sinc_of_ne_zero (mul_ne_zero Real.pi_ne_zero hs)]
  have hsin : Real.sin (Real.pi * (s + (n : ℝ))) =
      (-1 : ℝ) ^ n * Real.sin (Real.pi * s) := by
    convert Real.sin_add_int_mul_pi (Real.pi * s) n using 1 <;> congr 1 <;> ring
  rw [hsin]
  have hp : phase n * phase n = 1 := by
    simp only [phase, ← mul_zpow, neg_one_mul, neg_neg, one_zpow]
  push_cast
  dsimp [phase] at hp ⊢
  simp only [div_eq_mul_inv, mul_inv]
  linear_combination
    ((Real.sqrt L : ℂ) * Complex.sin ((Real.pi : ℂ) * (s : ℂ)) *
      (Real.pi : ℂ)⁻¹ * ((s : ℂ) + (n : ℂ))⁻¹) * hp

private theorem band_tail_separation {N : ℕ} (hN : 0 < N) {s : ℝ}
    (hs : |s| ≤ (N : ℝ) / 4) (j : ℕ) :
    0 < (N : ℝ) + s + (j : ℝ) + 1 ∧
    0 < (N : ℝ) - s + (j : ℝ) + 1 := by
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  have hj : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
  constructor <;> linarith [(abs_le.mp hs).1, (abs_le.mp hs).2]

/-- Absolute convergence of the two literal response series, including
integer s where the common sine factor vanishes. -/
theorem exteriorSeries_norm_summable {L : ℝ} (hL : 0 < L) {f : ℝ → ℂ}
    (hf : MemLp f 2 (volume.restrict (interval L))) {N : ℕ} (hN : 0 < N)
    {s : ℝ} (hs : |s| ≤ (N : ℝ) / 4) :
    Summable (fun j : ℕ ↦ ‖positiveTail N (signedCoeff L hL f) j *
      (((N : ℝ) + s + (j : ℝ) + 1)⁻¹ : ℝ)‖) ∧
    Summable (fun j : ℕ ↦ ‖negativeTail N (signedCoeff L hL f) j *
      (((N : ℝ) - s + (j : ℝ) + 1)⁻¹ : ℝ)‖) := by
  have hz := signedCoeff_sq_summable hL hf
  have hu := hz.comp_injective (positive_index_injective N)
  have hv := hz.comp_injective (negative_index_injective N)
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  have hp : 0 < (N : ℝ) + s := by linarith [(abs_le.mp hs).1]
  have hm : 0 < (N : ℝ) - s := by linarith [(abs_le.mp hs).2]
  exact ⟨WeilInfiniteComplementLeakage.cauchyHalf_norm_summable hp _ hu,
    WeilInfiniteComplementLeakage.cauchyHalf_norm_summable hm _ hv⟩

/-- Exact signed series on the leakage owner's band, for the original arbitrary
complex L2 function with its actual low coefficients zero. -/
theorem paperFT_eq_exteriorSeries {L : ℝ} (hL : 0 < L) {f : ℝ → ℂ}
    (hf : MemLp f 2 (volume.restrict (interval L))) {N : ℕ} (hN : 0 < N)
    (hlow : ∀ n : ℤ, |n| ≤ (N : ℤ) → signedCoeff L hL f n = 0)
    {s : ℝ} (hs : |s| ≤ (N : ℝ) / 4) :
    paperFT (iocZeroExtend L f) ((2 * Real.pi * s / L : ℝ) : ℂ) =
      ((Real.sqrt L / Real.pi * Real.sin (Real.pi * s) : ℝ) : ℂ) *
        exteriorSeries N (signedCoeff L hL f) s := by
  have hresponses := exteriorSeries_norm_summable hL hf hN hs
  let z := signedCoeff L hL f
  let C : ℂ := ((Real.sqrt L / Real.pi * Real.sin (Real.pi * s) : ℝ) : ℂ)
  have h := hasSum_signedCoeff_mul_basisPaperFT hL hf (2 * Real.pi * s / L)
  rw [← h.tsum_eq, tsum_eq_two_exterior_tails N _ h.summable
    (fun n hn ↦ by simp [hlow n hn])]
  have hp (j : ℕ) : z ((N : ℤ) + (j : ℤ) + 1) *
      basisPaperFT L ((N : ℤ) + (j : ℤ) + 1) (2 * Real.pi * s / L) =
        C * (positiveTail N z j * (((N : ℝ) + s + (j : ℝ) + 1)⁻¹ : ℝ)) := by
    rw [scaled_basis_rational hL _ (by
      push_cast
      linarith [(band_tail_separation hN hs j).1])]
    dsimp [positiveTail, C]
    push_cast
    ring
  have hm (j : ℕ) : z (-((N : ℤ) + (j : ℤ) + 1)) *
      basisPaperFT L (-((N : ℤ) + (j : ℤ) + 1)) (2 * Real.pi * s / L) =
        -(C * (negativeTail N z j * (((N : ℝ) - s + (j : ℝ) + 1)⁻¹ : ℝ))) := by
    rw [scaled_basis_rational hL _ (by
      push_cast
      linarith [(band_tail_separation hN hs j).2])]
    have heq : s + ((-((N : ℤ) + (j : ℤ) + 1) : ℤ) : ℝ) =
        -((N : ℝ) - s + (j : ℝ) + 1) := by push_cast; ring
    rw [heq, inv_neg]
    dsimp [negativeTail, C]
    push_cast
    ring
  dsimp only [z] at hp hm
  simp_rw [hp, hm, tsum_neg]
  rw [(hresponses.1.of_norm.hasSum.mul_left C).tsum_eq,
    (hresponses.2.of_norm.hasSum.mul_left C).tsum_eq]
  dsimp [exteriorSeries, C, z]
  ring

/-- The actual squared PLUS transform is the existing owner's exact density.
Only the public density is unfolded; no private owner theorem is exposed. -/
theorem norm_paperFT_sq_eq_exteriorFourierDensity {L : ℝ} (hL : 0 < L) {f : ℝ → ℂ}
    (hf : MemLp f 2 (volume.restrict (interval L))) {N : ℕ} (hN : 0 < N)
    (hlow : ∀ n : ℤ, |n| ≤ (N : ℤ) → signedCoeff L hL f n = 0)
    {s : ℝ} (hs : |s| ≤ (N : ℝ) / 4) :
    ‖paperFT (iocZeroExtend L f) ((2 * Real.pi * s / L : ℝ) : ℂ)‖ ^ 2 =
      WeilInfiniteComplementLeakage.exteriorFourierDensity L N
        (positiveTail N (signedCoeff L hL f)) (negativeTail N (signedCoeff L hL f)) s := by
  rw [paperFT_eq_exteriorSeries hL hf hN hlow hs, norm_mul, mul_pow]
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs, mul_pow, div_pow,
    Real.sq_sqrt hL.le]
  rfl

#print axioms signedCoeff_tail_mass
#print axioms paperFT_eq_exteriorSeries
#print axioms norm_paperFT_sq_eq_exteriorFourierDensity

/-- Physical-band leakage of the original arbitrary complex Ioc L2 function.
The normalization is dt/(2*pi), so the affine frequency substitution gives
exactly ds/L. Integrability is part of the conclusion. -/
theorem original_low_frequency_mass {L : ℝ} (hL : 0 < L) {f : ℝ → ℂ}
    (hf : MemLp f 2 (volume.restrict (interval L))) {N : ℕ} (hN : 0 < N)
    (hlow : ∀ n : ℤ, |n| ≤ (N : ℤ) → signedCoeff L hL f n = 0) :
    IntervalIntegrable (fun t : ℝ ↦ ‖paperFT (iocZeroExtend L f) t‖ ^ 2) volume
      (-(Real.pi * (N : ℝ) / (2 * L))) (Real.pi * (N : ℝ) / (2 * L)) ∧
    (1 / (2 * Real.pi)) *
      (∫ t in (-(Real.pi * (N : ℝ) / (2 * L)))..(Real.pi * (N : ℝ) / (2 * L)),
        ‖paperFT (iocZeroExtend L f) t‖ ^ 2) ≤
      (4 / (3 * Real.pi ^ 2)) * (∫ x in (-L / 2)..(L / 2), ‖f x‖ ^ 2) := by
  obtain ⟨hu, hv, hmass⟩ := signedCoeff_tail_mass hL hf N hlow
  obtain ⟨hi, hb⟩ := WeilInfiniteComplementLeakage.infinite_complement_low_frequency_mass
    hN hL (positiveTail N (signedCoeff L hL f)) (negativeTail N (signedCoeff L hL f)) hu hv
  let D : ℝ → ℝ := fun t ↦ ‖paperFT (iocZeroExtend L f) t‖ ^ 2
  let c : ℝ := 2 * Real.pi / L
  have hc : c ≠ 0 := ne_of_gt (by dsimp [c]; positivity)
  have hab : -(N : ℝ) / 4 ≤ (N : ℝ) / 4 := by
    linarith [show (0 : ℝ) ≤ (N : ℝ) from Nat.cast_nonneg N]
  have heq : Set.EqOn
      (WeilInfiniteComplementLeakage.exteriorFourierDensity L N
        (positiveTail N (signedCoeff L hL f)) (negativeTail N (signedCoeff L hL f)))
      (fun s ↦ D (c * s)) (uIoc (-(N : ℝ) / 4) ((N : ℝ) / 4)) := by
    intro s hs
    rw [uIoc_of_le hab] at hs
    dsimp [D, c]
    rw [div_mul_eq_mul_div]
    have hsrange : |s| ≤ (N : ℝ) / 4 := abs_le.mpr ⟨by linarith [hs.1], hs.2⟩
    exact (norm_paperFT_sq_eq_exteriorFourierDensity hL hf hN hlow hsrange).symm
  have his : IntervalIntegrable (fun s ↦ D (c * s)) volume
      (-(N : ℝ) / 4) ((N : ℝ) / 4) := (intervalIntegrable_congr heq).mp hi
  have hbound : (1 / L) * (∫ s in (-(N : ℝ) / 4)..((N : ℝ) / 4), D (c * s)) ≤
      (4 / (3 * Real.pi ^ 2)) * (∫ x in (-L / 2)..(L / 2), ‖f x‖ ^ 2) := by
    have hint := intervalIntegral.integral_congr_ae
      (μ := volume) (Filter.Eventually.of_forall heq)
    rw [hint] at hb
    change (1 / L) * _ ≤ (4 / (3 * Real.pi ^ 2)) *
      (squareMass (positiveTail N (signedCoeff L hL f)) +
       squareMass (negativeTail N (signedCoeff L hL f))) at hb
    rw [hmass] at hb
    exact hb
  have ha : (-(N : ℝ) / 4) / c⁻¹ = -(Real.pi * (N : ℝ) / (2 * L)) := by
    dsimp [c]
    field_simp [hL.ne', Real.pi_ne_zero]
    <;> ring
  have hb' : ((N : ℝ) / 4) / c⁻¹ = Real.pi * (N : ℝ) / (2 * L) := by
    dsimp [c]
    field_simp [hL.ne', Real.pi_ne_zero]
    <;> ring
  have hip := his.comp_mul_left (c := c⁻¹)
  simp only [mul_inv_cancel_left₀ hc, ha, hb'] at hip
  refine ⟨hip, ?_⟩
  have hja : c * (-(N : ℝ) / 4) = -(Real.pi * (N : ℝ) / (2 * L)) := by
    dsimp [c]
    field_simp [hL.ne', Real.pi_ne_zero]
    <;> ring
  have hjb : c * ((N : ℝ) / 4) = Real.pi * (N : ℝ) / (2 * L) := by
    dsimp [c]
    field_simp [hL.ne', Real.pi_ne_zero]
    <;> ring
  have hj := intervalIntegral.smul_integral_comp_mul_left D
    (a := -(N : ℝ) / 4) (b := (N : ℝ) / 4) c
  rw [hja, hjb, smul_eq_mul] at hj
  change (1 / (2 * Real.pi)) *
    (∫ t in (-(Real.pi * (N : ℝ) / (2 * L)))..(Real.pi * (N : ℝ) / (2 * L)), D t) ≤ _
  rw [← hj, ← mul_assoc]
  have hjac : (1 / (2 * Real.pi)) * c = 1 / L := by
    dsimp [c]
    field_simp [hL.ne', Real.pi_ne_zero]
  rw [hjac]
  exact hbound

#print axioms original_low_frequency_mass

end D5.S3.Weil.ZetaBridge.OriginalIocFourier
