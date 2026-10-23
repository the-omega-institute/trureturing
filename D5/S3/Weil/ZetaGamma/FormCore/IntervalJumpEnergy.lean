/- GID: D5/S3/Weil/ZetaGamma/FormCore/IntervalJumpEnergy
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaGamma/FormCore/IntervalJumpEnergy
   mirror-E: none(waiver:analytic-Gamma-form-core)
   anchors: []
   utility: none
   digest: Interval Lipschitz regularity pays both zero-extension endpoint strips. -/

import D5.S3.Weil.ZetaGamma.FormCore.DomainPassage
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
The interval endpoints need not agree and need not vanish. No periodicity,
Fourier support, spectral summability, or finite jump-energy premise is used.
The exact original-domain applications are transient examples downstream.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace D5.S3.Weil.ZetaGamma.FormCore.IntervalJumpEnergy

open D5.S3.Weil.ZetaGamma.PeriodicEnergyTransport
open D5.S3.Weil.ZetaGamma.FormCore.DomainPassage

/-- Three genuine spatial pieces: the interior and the two endpoint strips. -/
private def stripMajorant (d t : ℝ) (K : ℝ≥0) (B s x : ℝ) : ℝ :=
  (Ioc t (t + d)).indicator (fun _ => ((K : ℝ) * s) ^ 2) x +
    (Ioc t (t + s)).indicator (fun _ => B ^ 2) x +
    (Ioc (t + d) (t + d + s)).indicator (fun _ => B ^ 2) x

private lemma window_memLp_of_lipschitzOnWith
    {d t : ℝ} {K : ℝ≥0} {B : ℝ} {u : ℝ → ℂ}
    (hK : LipschitzOnWith K u (Icc t (t + d)))
    (hB : ∀ x ∈ Icc t (t + d), ‖u x‖ ≤ B) :
    MemLp u 2 (windowMeasure d t) := by
  have hm : AEStronglyMeasurable u (windowMeasure d t) :=
    (hK.continuousOn.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  apply MemLp.of_bound hm B
  filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with x hx
  exact hB x ⟨hx.1.le, hx.2⟩

/-- Pointwise strip accounting. The right strip is present even when `s > d`;
this makes the same estimate valid at every positive displacement. -/
private lemma gap_normSq_le_stripMajorant
    {d t s B : ℝ} {K : ℝ≥0} {u : ℝ → ℂ}
    (hs : 0 < s)
    (hK : LipschitzOnWith K u (Icc t (t + d)))
    (hB : ∀ x ∈ Icc t (t + d), ‖u x‖ ≤ B) (x : ℝ) :
    Complex.normSq (zeroExtension d t u x - zeroExtension d t u (x - s)) ≤
      stripMajorant d t K B s x := by
  have hnn (S : Set ℝ) (c : ℝ) (hc : 0 ≤ c) :
      0 ≤ S.indicator (fun _ => c) x := by
    by_cases hx : x ∈ S
    · simpa only [Set.indicator_of_mem hx] using hc
    · simp only [Set.indicator_of_notMem hx, le_refl]
  have hL := hnn (Ioc t (t + s)) (B ^ 2) (sq_nonneg _)
  have hR := hnn (Ioc (t + d) (t + d + s)) (B ^ 2) (sq_nonneg _)
  by_cases hx : x ∈ Ioc t (t + d)
  · by_cases hy : x - s ∈ Ioc t (t + d)
    · have hdist : dist x (x - s) = s := by
        rw [Real.dist_eq, show x - (x - s) = s by ring, abs_of_pos hs]
      have hnorm : ‖u x - u (x - s)‖ ≤ (K : ℝ) * s := by
        have h := hK.dist_le_mul x ⟨hx.1.le, hx.2⟩ (x - s) ⟨hy.1.le, hy.2⟩
        rw [hdist, dist_eq_norm] at h
        exact h
      have hsq := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
      simp only [zeroExtension, Set.indicator_of_mem hx,
        Set.indicator_of_mem hy, Complex.normSq_eq_norm_sq, stripMajorant]
      linarith
    · have hylo : x - s ≤ t := by
        by_contra hn
        apply hy
        exact ⟨lt_of_not_ge hn, by linarith [hx.2]⟩
      have hstrip : x ∈ Ioc t (t + s) := ⟨hx.1, by linarith⟩
      have hsq : ‖u x‖ ^ 2 ≤ B ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (hB x ⟨hx.1.le, hx.2⟩) 2
      simp only [zeroExtension, Set.indicator_of_mem hx,
        Set.indicator_of_notMem hy, sub_zero, Complex.normSq_eq_norm_sq, stripMajorant]
      rw [Set.indicator_of_mem hstrip]
      linarith [sq_nonneg ((K : ℝ) * s)]
  · by_cases hy : x - s ∈ Ioc t (t + d)
    · have hxhi : t + d < x := by
        by_contra hn
        apply hx
        exact ⟨by linarith [hy.1], le_of_not_gt hn⟩
      have hstrip : x ∈ Ioc (t + d) (t + d + s) := ⟨hxhi, by linarith [hy.2]⟩
      have hsq : ‖u (x - s)‖ ^ 2 ≤ B ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (hB (x - s) ⟨hy.1.le, hy.2⟩) 2
      simp only [zeroExtension, Set.indicator_of_notMem hx,
        Set.indicator_of_mem hy, zero_sub, Complex.normSq_eq_norm_sq, norm_neg, stripMajorant]
      rw [Set.indicator_of_mem hstrip]
      linarith
    · simp only [zeroExtension, Set.indicator_of_notMem hx,
        Set.indicator_of_notMem hy, sub_self, Complex.normSq_eq_norm_sq,
        norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), stripMajorant]
      linarith

private lemma stripMajorant_integrable (d t : ℝ) (K : ℝ≥0) (B s : ℝ) :
    Integrable (stripMajorant d t K B s) := by
  have hi (a b c : ℝ) : Integrable ((Ioc a b).indicator (fun _ : ℝ => c)) :=
    (integrableOn_const measure_Ioc_lt_top.ne).integrable_indicator measurableSet_Ioc
  exact ((hi t (t + d) _).add (hi t (t + s) _)).add (hi (t + d) (t + d + s) _)

private lemma integral_stripMajorant
    {d s : ℝ} (hd : 0 < d) (hs : 0 < s) (t : ℝ) (K : ℝ≥0) (B : ℝ) :
    (∫ x, stripMajorant d t K B s x) =
      d * ((K : ℝ) * s) ^ 2 + 2 * B ^ 2 * s := by
  have hi (a b c : ℝ) : Integrable ((Ioc a b).indicator (fun _ : ℝ => c)) :=
    (integrableOn_const measure_Ioc_lt_top.ne).integrable_indicator measurableSet_Ioc
  unfold stripMajorant
  have hsum := integral_add
    ((hi t (t + d) (((K : ℝ) * s) ^ 2)).add (hi t (t + s) (B ^ 2)))
    (hi (t + d) (t + d + s) (B ^ 2))
  have hpair := integral_add (hi t (t + d) (((K : ℝ) * s) ^ 2))
    (hi t (t + s) (B ^ 2))
  simp only [Pi.add_apply] at hsum
  rw [hsum, hpair]
  simp only [integral_indicator_const, measurableSet_Ioc, smul_eq_mul,
    Real.volume_real_Ioc_of_le (show t ≤ t + d by linarith),
    Real.volume_real_Ioc_of_le (show t ≤ t + s by linarith),
    Real.volume_real_Ioc_of_le (show t + d ≤ t + d + s by linarith)]
  ring

/-- All inner integrals are genuine L1 integrals. In particular no lower-bound
argument uses a default-zero integral of a nonintegrable L2 expression. -/
theorem zeroTranslationEnergy_le_of_lipschitzOnWith
    {d t s B : ℝ} {K : ℝ≥0} {u : ℝ → ℂ}
    (hd : 0 < d) (hs : 0 < s)
    (hK : LipschitzOnWith K u (Icc t (t + d)))
    (hB : ∀ x ∈ Icc t (t + d), ‖u x‖ ≤ B) :
    Integrable (fun x : ℝ => Complex.normSq
      (zeroExtension d t u x - zeroExtension d t u (x - s))) ∧
    zeroTranslationEnergy d t u s ≤ d * ((K : ℝ) * s) ^ 2 + 2 * B ^ 2 * s := by
  have hu := window_memLp_of_lipschitzOnWith hK hB
  have hz := zero_extension_memLp d t u hu
  have hshift := hz.comp_measurePreserving (measurePreserving_sub_right volume s)
  have hinner : Integrable (fun x : ℝ => Complex.normSq
      (zeroExtension d t u x - zeroExtension d t u (x - s))) := by
    simpa only [Complex.normSq_eq_norm_sq, Pi.sub_apply, Function.comp_def] using
      ((memLp_two_iff_integrable_sq_norm (hz.sub hshift).aestronglyMeasurable).mp
        (hz.sub hshift))
  refine ⟨hinner, ?_⟩
  calc
    zeroTranslationEnergy d t u s ≤ ∫ x, stripMajorant d t K B s x :=
      integral_mono hinner (stripMajorant_integrable d t K B s)
        (gap_normSq_le_stripMajorant hs hK hB)
    _ = _ := integral_stripMajorant hd hs t K B

/-- A bound for the actual density at ALL positive displacements. It captures
its 1/s singularity and exponential tail in the same expression. -/
private lemma density_le_exp_mul {s : ℝ} (hs : 0 < s) :
    density s ≤ Real.exp (-s / 2) * (1 + 1 / (2 * s)) := by
  have hden : 0 < 1 - Real.exp (-2 * s) := by
    have h := Real.exp_lt_one_iff.mpr (show -2 * s < 0 by linarith)
    linarith
  have he : 1 + 2 * s ≤ Real.exp (2 * s) := by
    linarith [Real.add_one_le_exp (2 * s)]
  have he' : (1 + 2 * s) * Real.exp (-2 * s) ≤ 1 := by
    calc
      _ ≤ Real.exp (2 * s) * Real.exp (-2 * s) :=
        mul_le_mul_of_nonneg_right he (Real.exp_pos _).le
      _ = 1 := by
        rw [← Real.exp_add, show 2 * s + (-2 * s) = 0 by ring, Real.exp_zero]
  have hc : (2 * s) * (1 + 1 / (2 * s)) = 1 + 2 * s := by
    field_simp [ne_of_gt hs]
    <;> ring
  have hi : 1 ≤ (1 + 1 / (2 * s)) * (1 - Real.exp (-2 * s)) := by
    apply (mul_le_mul_iff_left₀ (show 0 < 2 * s by positivity)).mp
    calc
      1 * (2 * s) ≤ (1 + 2 * s) * (1 - Real.exp (-2 * s)) := by nlinarith [he']
      _ = ((2 * s) * (1 + 1 / (2 * s))) * (1 - Real.exp (-2 * s)) := by rw [hc]
      _ = ((1 + 1 / (2 * s)) * (1 - Real.exp (-2 * s))) * (2 * s) := by ring
  change Real.exp (-s / 2) / (1 - Real.exp (-2 * s)) ≤ _
  apply (div_le_iff₀ hden).mpr
  calc
    Real.exp (-s / 2) = Real.exp (-s / 2) * 1 := by ring
    _ ≤ Real.exp (-s / 2) *
        ((1 + 1 / (2 * s)) * (1 - Real.exp (-2 * s))) :=
      mul_le_mul_of_nonneg_left hi (Real.exp_pos _).le
    _ = _ := by ring

private def energyMajorant (d : ℝ) (K : ℝ≥0) (B s : ℝ) : ℝ :=
  Real.exp (-s / 2) *
    (d * (K : ℝ) ^ 2 * s ^ 2 +
      (2 * B ^ 2 + d * (K : ℝ) ^ 2 / 2) * s + B ^ 2)

private lemma energyMajorant_integrable (d : ℝ) (K : ℝ≥0) (B : ℝ) :
    IntegrableOn (energyMajorant d K B) (Ioi 0) := by
  have hp (n : ℕ) : IntegrableOn
      (fun s : ℝ => s ^ n * Real.exp (-s / 2)) (Ioi 0) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow
      (p := (1 : ℝ)) (s := (n : ℝ)) (b := (1 / 2 : ℝ))
      (by have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n; linarith)
      (by norm_num) (by norm_num)
    convert h using 1
    ext s
    simp only [Real.rpow_natCast, Real.rpow_one]
    congr 2 <;> ring
  have h0 : IntegrableOn (fun s : ℝ => Real.exp (-s / 2)) (Ioi 0) := by
    simpa only [pow_zero, one_mul] using hp 0
  have h1 := (hp 1).const_mul (2 * B ^ 2 + d * (K : ℝ) ^ 2 / 2)
  have h2 := (hp 2).const_mul (d * (K : ℝ) ^ 2)
  have h := (h2.add h1).add (h0.const_mul (B ^ 2))
  apply h.congr
  filter_upwards [] with s
  dsimp only [energyMajorant, Pi.add_apply]
  ring

/-- Genuine interval regularity implies finite ACTUAL zero-extension Gamma
jump energy, without endpoint matching. The compact bound B is obtained from
Lipschitz continuity, rather than assumed as an energy/spectral premise. -/
theorem zeroEnergyDensity_integrableOn_of_lipschitzOnWith
    {d t : ℝ} {K : ℝ≥0} {u : ℝ → ℂ} (hd : 0 < d)
    (hK : LipschitzOnWith K u (Icc t (t + d))) :
    IntegrableOn (zeroEnergyDensity d t u) (Ioi 0) := by
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hK.continuousOn
  have hu := window_memLp_of_lipschitzOnWith hK hB
  have hdensity : Measurable density := by
    unfold density
      D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition.archimedeanJumpDensity
    fun_prop
  have hm : AEStronglyMeasurable (zeroEnergyDensity d t u)
      (volume.restrict (Ioi 0)) :=
    (hdensity.aestronglyMeasurable.mul
      (zeroTranslationEnergy_aestronglyMeasurable d t u hu)).restrict
  refine (energyMajorant_integrable d K B).mono' hm ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
  have hs0 : 0 < s := hs
  have hE := (zeroTranslationEnergy_le_of_lipschitzOnWith hd hs0 hK hB).2
  have hn : 0 ≤ zeroTranslationEnergy d t u s :=
    integral_nonneg fun x => Complex.normSq_nonneg _
  have hd0 := density_nonneg hs0
  have hb0 : 0 ≤ d * ((K : ℝ) * s) ^ 2 + 2 * B ^ 2 * s := by positivity
  have hbound : zeroEnergyDensity d t u s ≤ energyMajorant d K B s := by
    calc
      zeroEnergyDensity d t u s ≤
          density s * (d * ((K : ℝ) * s) ^ 2 + 2 * B ^ 2 * s) :=
        mul_le_mul_of_nonneg_left hE hd0
      _ ≤ (Real.exp (-s / 2) * (1 + 1 / (2 * s))) *
          (d * ((K : ℝ) * s) ^ 2 + 2 * B ^ 2 * s) :=
        mul_le_mul_of_nonneg_right (density_le_exp_mul hs0) hb0
      _ = energyMajorant d K B s := by
        dsimp only [energyMajorant]
        field_simp [ne_of_gt hs0]
        <;> ring
  rw [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ zeroEnergyDensity d t u s from
    mul_nonneg hd0 hn)]
  exact hbound

end D5.S3.Weil.ZetaGamma.FormCore.IntervalJumpEnergy
