import D5.S3.Quantum.Semigroups.WuCubicOperatorNormalization
import D5.S3.Quantum.Semigroups.WuCubicTranslationEnergy
import D5.S3.Quantum.Divergence.GibbsCubicSignedMoment
import D5.S3.Quantum.Divergence.GibbsCubicJensenAbsorption
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.Matrix.Order

/-! The derivative of the Wu cubic deficit along conditioned scalar translations. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder

namespace D5.S3.Quantum.Semigroups.WuCubicConditionedTranslation

open WuCubicOperatorBridge (D G GInv Mat Occupation)
open WuCubicOperatorNormalization (operatorDeficit)
open WuCubicTranslationEnergy (base baseEntry sandwich translate cubicEnergy V V₁
  cubicEnergy_hasDerivAt_degree cubicEnergy_deriv_ge)
open WuRepeatedMiddleCubic (alpha)
open D5.S3.Quantum.Divergence.GibbsCubicTranslationEntropy
  (cubicEntropy spectralRatio spectralWeight)
open D5.S3.Quantum.Divergence.GibbsCubicSignedMoment
  (spectralPair_centeredMoments spectralPair_squareEntropy_le)
open D5.S3.Quantum.Divergence.GibbsCubicJensenAbsorption (focal_cubicEntropy_slope)
open D5.S3.Quantum.Divergence.SpectralCeilingRelativeEntropy
  (overlap trace_cfc_product overlap_weighted_row)
open private G_pow_six GInv_mul_G G_mul_GInv rootScale rootRatio_sq rootValue
  rootScale_pos rootValue_pos from D5.S3.Quantum.Semigroups.WuCubicOperatorBridge
open private gibbsOccupation gibbsLow gibbsHigh from
  D5.S3.Quantum.Semigroups.WuRepeatedMiddleCubic
open private base_diagonal sandwich_translate from
  D5.S3.Quantum.Semigroups.WuCubicTranslationEnergy
open private sum_normSq_eq_trace from D5.S3.Quantum.Divergence.GibbsCubicJensenAbsorption
open WuCubicAngularCertificate (normalizedDeficit physicalFrame)
open WuCubicOperatorNormalization (operatorDeficit_eq_scaled)
open private G_adjoint exists_ordered_frame from D5.S3.Quantum.Semigroups.WuCubicOperatorNormalization
open private levelsAt from D5.S3.Quantum.Semigroups.WuCubicSignedTransfer

/-- The embedded translate is `G r * translate A t * G r`. -/
def embedded (r : ℝ) (A : Mat) (t : ℝ) : Mat := t • base r + sandwich r A

/-- The signed third central moment of the spectral pair law. -/
def C (r : ℝ) (A : Mat) : ℝ := ((sandwich r A) ^ 3).trace.re

/-- The Hilbert–Schmidt residual in the compensated Jensen gap. -/
def residual (r : ℝ) (A : Mat) (t : ℝ) : Mat :=
  let M := embedded r A t
  let S := (base r * M ^ 2).trace.re
  M - (((M ^ 3).trace.re / S : ℝ) : ℂ) • base r

/-- The actual Hermitian spectrum lies in an enclosure of positive upper endpoint
and lower-to-upper ratio at least `2/3`. -/
def Conditioned {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) : Prop :=
  ∃ (hM : M.IsHermitian) (mmin mmax : ℝ),
    0 < mmax ∧ (2 / 3 : ℝ) ≤ mmin / mmax ∧
      ∀ i, hM.eigenvalues i ∈ Icc mmin mmax

section

open scoped Matrix.Norms.L2Operator

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

local notation "ComplexMatrix" => Matrix ι ι ℂ

/-- The matrix on a scalar translation ray. -/
def rayMatrix (B U : ComplexMatrix) (t : ℝ) : ComplexMatrix := t • B + U

private theorem rayMatrix_isHermitian {U B : ComplexMatrix} (hU : U.IsHermitian)
    (hB : B.IsHermitian) (t : ℝ) : (rayMatrix B U t).IsHermitian := by
  exact (hB.smul (IsSelfAdjoint.all t)).add hU

private abbrev spectralMin (M : ComplexMatrix) : ℝ := sInf (spectrum ℝ M)
private abbrev spectralMax (M : ComplexMatrix) : ℝ := sSup (spectrum ℝ M)

private theorem spectralMin_isLeast {M : ComplexMatrix} (hM : M.IsHermitian) :
    IsLeast (spectrum ℝ M) (spectralMin M) :=
  (ContinuousFunctionalCalculus.isCompact_spectrum (R := ℝ) M).isLeast_sInf
    (by rw [hM.spectrum_real_eq_range_eigenvalues]; exact Set.range_nonempty _)

private theorem spectralMax_isGreatest {M : ComplexMatrix} (hM : M.IsHermitian) :
    IsGreatest (spectrum ℝ M) (spectralMax M) :=
  (ContinuousFunctionalCalculus.isCompact_spectrum (R := ℝ) M).isGreatest_sSup
    (by rw [hM.spectrum_real_eq_range_eigenvalues]; exact Set.range_nonempty _)

private theorem le_spectralMin {M : ComplexMatrix} (hM : M.IsHermitian) (c : ℝ) :
    c ≤ spectralMin M ↔ algebraMap ℝ ComplexMatrix c ≤ M := by
  rw [algebraMap_le_iff_le_spectrum hM.isSelfAdjoint]
  exact ⟨fun h _ hx => h.trans ((spectralMin_isLeast hM).2 hx),
    fun h => h _ (spectralMin_isLeast hM).1⟩

private theorem spectralMax_le {M : ComplexMatrix} (hM : M.IsHermitian) (c : ℝ) :
    spectralMax M ≤ c ↔ M ≤ algebraMap ℝ ComplexMatrix c := by
  rw [le_algebraMap_iff_spectrum_le hM.isSelfAdjoint]
  exact ⟨fun h _ hx => ((spectralMax_isGreatest hM).2 hx).trans h,
    fun h => h _ (spectralMax_isGreatest hM).1⟩

private theorem spectralExtrema_add_le {M N : ComplexMatrix} (hM : M.IsHermitian)
    (hN : N.IsHermitian) {c : ℝ} (h : algebraMap ℝ ComplexMatrix c ≤ N - M) :
    spectralMin M + c ≤ spectralMin N ∧ spectralMax M + c ≤ spectralMax N := by
  have hshift : M + algebraMap ℝ ComplexMatrix c ≤ N := by
    simpa only [add_comm] using le_sub_iff_add_le.mp h
  constructor
  · apply (le_spectralMin hN _).mpr
    rw [map_add]
    have hmin : algebraMap ℝ ComplexMatrix (spectralMin M) ≤ M :=
      (le_spectralMin hM (spectralMin M)).mp le_rfl
    calc
      _ ≤ M + algebraMap ℝ ComplexMatrix c := add_le_add hmin le_rfl
      _ ≤ N := hshift
  · apply le_sub_iff_add_le.mp
    apply (spectralMax_le hM _).mpr
    rw [map_sub]
    have hmax : N ≤ algebraMap ℝ ComplexMatrix (spectralMax N) :=
      (spectralMax_le hN (spectralMax N)).mp le_rfl
    exact le_sub_iff_add_le.mpr (hshift.trans hmax)

private theorem spectralExtrema_abs_sub_le {M N : ComplexMatrix} (hM : M.IsHermitian)
    (hN : N.IsHermitian) :
    |spectralMin M - spectralMin N| ≤ ‖M - N‖ ∧
      |spectralMax M - spectralMax N| ≤ ‖M - N‖ := by
  have h₁ := spectralExtrema_add_le hN hM (c := -‖M - N‖)
    (by simpa only [map_neg] using
      IsSelfAdjoint.neg_algebraMap_norm_le_self (M - N) (hM.sub hN).isSelfAdjoint)
  have h₂ := spectralExtrema_add_le hM hN (c := -‖M - N‖)
    (by simpa only [map_neg, norm_sub_rev] using
      IsSelfAdjoint.neg_algebraMap_norm_le_self (N - M) (hN.sub hM).isSelfAdjoint)
  exact ⟨abs_le.mpr ⟨by linarith [h₁.1], by linarith [h₂.1]⟩,
    abs_le.mpr ⟨by linarith [h₁.2], by linarith [h₂.2]⟩⟩

/-- The signed gap between the smallest eigenvalue and two thirds of the largest. -/
def conditionedGap (M : ComplexMatrix) : ℝ := spectralMin M - (2 / 3 : ℝ) * spectralMax M

private theorem rayMatrix_sub (B U : ComplexMatrix) (s t : ℝ) :
    rayMatrix B U t - rayMatrix B U s = (t - s) • B := by
  simp only [rayMatrix, sub_smul, add_sub_add_right_eq_sub]

private theorem ray_extrema_continuous {B U : ComplexMatrix} (hB : B.IsHermitian)
    (hU : U.IsHermitian) :
    Continuous (fun t => spectralMin (rayMatrix B U t)) ∧
      Continuous (fun t => spectralMax (rayMatrix B U t)) := by
  have hbound (s t : ℝ) :=
    spectralExtrema_abs_sub_le (rayMatrix_isHermitian hU hB s) (rayMatrix_isHermitian hU hB t)
  have hnorm (s t : ℝ) : ‖rayMatrix B U s - rayMatrix B U t‖ = ‖B‖ * dist s t := by
    rw [rayMatrix_sub, norm_smul, dist_eq_norm, mul_comm]
  have hlo : LipschitzWith ‖B‖₊ (fun t => spectralMin (rayMatrix B U t)) := by
    apply lipschitzWith_iff_dist_le_mul.mpr
    intro s t
    rw [Real.dist_eq, coe_nnnorm, ← hnorm]
    exact (hbound s t).1
  have hhi : LipschitzWith ‖B‖₊ (fun t => spectralMax (rayMatrix B U t)) := by
    apply lipschitzWith_iff_dist_le_mul.mpr
    intro s t
    rw [Real.dist_eq, coe_nnnorm, ← hnorm]
    exact (hbound s t).2
  exact ⟨hlo.continuous, hhi.continuous⟩

private theorem ray_extrema_growth {B U : ComplexMatrix} (hB : B.IsHermitian)
    (hU : U.IsHermitian) {lo hi : ℝ} (hlo : algebraMap ℝ ComplexMatrix lo ≤ B)
    (hhi : B ≤ algebraMap ℝ ComplexMatrix hi) {s t : ℝ} (hst : s ≤ t) :
    (t - s) * lo ≤ spectralMin (rayMatrix B U t) - spectralMin (rayMatrix B U s) ∧
      spectralMax (rayMatrix B U t) - spectralMax (rayMatrix B U s) ≤ (t - s) * hi := by
  have hl : algebraMap ℝ ComplexMatrix ((t - s) * lo) ≤ rayMatrix B U t - rayMatrix B U s := by
    rw [rayMatrix_sub, Algebra.algebraMap_eq_smul_one, ← smul_smul]
    exact smul_le_smul_of_nonneg_left
      (by simpa only [Algebra.algebraMap_eq_smul_one] using hlo) (sub_nonneg.mpr hst)
  have hu : algebraMap ℝ ComplexMatrix (-((t - s) * hi)) ≤ rayMatrix B U s - rayMatrix B U t := by
    rw [map_neg, neg_le, neg_sub, rayMatrix_sub, Algebra.algebraMap_eq_smul_one, ← smul_smul]
    exact smul_le_smul_of_nonneg_left
      (by simpa only [Algebra.algebraMap_eq_smul_one] using hhi) (sub_nonneg.mpr hst)
  have hs := rayMatrix_isHermitian hU hB s
  have ht := rayMatrix_isHermitian hU hB t
  exact ⟨by linarith [(spectralExtrema_add_le hs ht hl).1],
    by linarith [(spectralExtrema_add_le ht hs hu).2]⟩

/-- A positive affine lower slope forces one and only one zero, with the
positive half-line exactly the nonnegative side of that zero. -/
private theorem existsUnique_conditionedEntry {ψ : ℝ → ℝ} {d : ℝ} (hd : 0 < d)
    (hψ : Continuous ψ)
    (hgrowth : ∀ s t, s ≤ t → d * (t - s) ≤ ψ t - ψ s) :
    ∃! τ, ψ τ = 0 ∧ ∀ t, 0 ≤ ψ t ↔ τ ≤ t := by
  let R : ℝ := |ψ 0| / d + 1
  have hR : 0 < R := by
    dsimp [R]
    positivity
  have hprod : d * R = |ψ 0| + d := by
    dsimp [R]
    field_simp [ne_of_gt hd] <;> ring
  have hleft : ψ (-R) < 0 := by
    have hs := hgrowth (-R) 0 (by linarith)
    rw [zero_sub, neg_neg, hprod] at hs
    linarith [le_abs_self (ψ 0)]
  have hright : 0 < ψ R := by
    have hs := hgrowth 0 R hR.le
    rw [sub_zero, hprod] at hs
    linarith [neg_le_abs (ψ 0)]
  obtain ⟨τ, _, hroot⟩ := intermediate_value_Icc (show -R ≤ R by linarith)
    hψ.continuousOn (show (0 : ℝ) ∈ Icc (ψ (-R)) (ψ R) from ⟨hleft.le, hright.le⟩)
  have hstrict : StrictMono ψ := by
    intro s t hst
    have hs := hgrowth s t hst.le
    linarith [mul_pos hd (sub_pos.mpr hst)]
  refine ⟨τ, ⟨hroot, fun t => ?_⟩, ?_⟩
  · rw [← hroot]
    exact hstrict.le_iff_le
  · intro σ hσ
    exact hstrict.injective (hσ.1.trans hroot.symm)

/-- Affine lower growth of the actual spectral gap under a two-sided Loewner bound. -/
theorem conditionedGap_growth {B U : ComplexMatrix} (hB : B.IsHermitian)
    (hU : U.IsHermitian) {lo hi s t : ℝ} (hlo : algebraMap ℝ ComplexMatrix lo ≤ B)
    (hhi : B ≤ algebraMap ℝ ComplexMatrix hi) (hst : s ≤ t) :
    (lo - (2 / 3 : ℝ) * hi) * (t - s) ≤
      conditionedGap (rayMatrix B U t) - conditionedGap (rayMatrix B U s) := by
  obtain ⟨hmin, hmax⟩ := ray_extrema_growth hB hU hlo hhi hst
  calc
    _ = (t - s) * lo - (2 / 3 : ℝ) * ((t - s) * hi) := by ring
    _ ≤ (spectralMin (rayMatrix B U t) - spectralMin (rayMatrix B U s)) -
        (2 / 3 : ℝ) * (spectralMax (rayMatrix B U t) - spectralMax (rayMatrix B U s)) :=
      sub_le_sub hmin (mul_le_mul_of_nonneg_left hmax (by norm_num))
    _ = _ := by unfold conditionedGap; ring

/-- The spectral gap has a unique zero for every Hermitian direction. -/
theorem existsUnique_conditionedGap_eq_zero {B U : ComplexMatrix} (hB : B.IsHermitian)
    (hU : U.IsHermitian) {lo hi : ℝ} (hlo : algebraMap ℝ ComplexMatrix lo ≤ B)
    (hhi : B ≤ algebraMap ℝ ComplexMatrix hi) (hd : 0 < lo - (2 / 3 : ℝ) * hi) :
    ∃! τ, conditionedGap (rayMatrix B U τ) = 0 ∧
      ∀ t, 0 ≤ conditionedGap (rayMatrix B U t) ↔ τ ≤ t := by
  obtain ⟨hcmin, hcmax⟩ := ray_extrema_continuous hB hU
  exact existsUnique_conditionedEntry hd (hcmin.sub (hcmax.const_mul (2 / 3)))
    (fun _ _ hst => conditionedGap_growth hB hU hlo hhi hst)

private theorem spectralMax_pos_of_psd_ne_zero {M : ComplexMatrix} (hM : M.PosSemidef)
    (hne : M ≠ 0) : 0 < spectralMax M :=
  (norm_pos_iff.mpr hne).trans_le ((spectralMax_isGreatest hM.isHermitian).2
    (CStarAlgebra.norm_mem_spectrum_of_nonneg M (Matrix.nonneg_iff_posSemidef.mpr hM)))

/-- On a nonvanishing Hermitian ray the positive-semidefinite onset is
singular, and the conditioned half-line starts strictly after it. -/
theorem conditioned_entry_q_two_thirds {U B : ComplexMatrix} {lo hi : ℝ}
    (hU : U.IsHermitian) (hB : B.IsHermitian) (hlo_pos : 0 < lo)
    (hlo : algebraMap ℝ ComplexMatrix lo ≤ B) (hhi : B ≤ algebraMap ℝ ComplexMatrix hi)
    (hband : hi ≤ (36 / 25 : ℝ) * lo) (hne : ∀ t, rayMatrix B U t ≠ 0) :
    ∃ t₀, (∀ t, (rayMatrix B U t).PosSemidef ↔ t₀ ≤ t) ∧
      ¬ (rayMatrix B U t₀).PosDef ∧
      ∃! τ, conditionedGap (rayMatrix B U τ) = 0 ∧ t₀ < τ ∧
        spectralMin (rayMatrix B U τ) / spectralMax (rayMatrix B U τ) = (2 / 3 : ℝ) ∧
        ∀ t, Conditioned (rayMatrix B U t) ↔ τ ≤ t := by
  let M := rayMatrix B U
  have hM (t : ℝ) := rayMatrix_isHermitian hU hB t
  have hcmin := (ray_extrema_continuous hB hU).1
  obtain ⟨t₀, ⟨hzero, hsign⟩, _⟩ :=
    existsUnique_conditionedEntry hlo_pos hcmin (fun s t hst => by
      simpa only [mul_comm] using (ray_extrema_growth hB hU hlo hhi hst).1)
  have hpsd (t : ℝ) : (M t).PosSemidef ↔ t₀ ≤ t := by
    rw [← Matrix.nonneg_iff_posSemidef, ← map_zero (algebraMap ℝ ComplexMatrix),
      ← le_spectralMin (hM t) 0]
    exact hsign t
  have hsingular : ¬ (M t₀).PosDef := by
    intro hpd
    have hmin : spectralMin (M t₀) ∈ Set.range (hM t₀).eigenvalues := by
      simpa only [← (hM t₀).spectrum_real_eq_range_eigenvalues] using
        (spectralMin_isLeast (hM t₀)).1
    obtain ⟨i, hi⟩ := hmin
    exact (hpd.eigenvalues_pos i).ne' (hi.trans hzero)
  have hd : 0 < lo - (2 / 3 : ℝ) * hi := by linarith
  obtain ⟨τ, ⟨hτ, hτsign⟩, _⟩ := existsUnique_conditionedGap_eq_zero hB hU hlo hhi hd
  have hmaxAt (t : ℝ) (ht : t₀ ≤ t) : 0 < spectralMax (M t) :=
    spectralMax_pos_of_psd_ne_zero ((hpsd t).mpr ht) (hne t)
  have hgap₀ : conditionedGap (M t₀) < 0 := by
    unfold conditionedGap
    rw [hzero]
    linarith [hmaxAt t₀ le_rfl]
  have hafter : t₀ < τ := lt_of_not_ge fun h => hgap₀.not_ge ((hτsign t₀).mpr h)
  have hratio : spectralMin (M τ) / spectralMax (M τ) = (2 / 3 : ℝ) :=
    (div_eq_iff (hmaxAt τ hafter.le).ne').mpr (sub_eq_zero.mp hτ)
  have hcond (t : ℝ) : Conditioned (M t) ↔ τ ≤ t := by
    constructor
    · rintro ⟨h, a, b, hb, hratio, hbounds⟩
      have hmin : spectralMin (M t) ∈ Set.range h.eigenvalues := by
        simpa only [← h.spectrum_real_eq_range_eigenvalues] using (spectralMin_isLeast h).1
      have hmax : spectralMax (M t) ∈ Set.range h.eigenvalues := by
        simpa only [← h.spectrum_real_eq_range_eigenvalues] using (spectralMax_isGreatest h).1
      obtain ⟨i, hi⟩ := hmin
      obtain ⟨j, hj⟩ := hmax
      apply (hτsign t).mp
      unfold conditionedGap
      linarith [(hbounds i).1, (hbounds j).2, (le_div_iff₀ hb).mp hratio]
    · intro ht
      refine ⟨hM t, spectralMin (M t), spectralMax (M t), hmaxAt t (hafter.le.trans ht),
        (le_div_iff₀ (hmaxAt t (hafter.le.trans ht))).mpr
          (sub_nonneg.mp ((hτsign t).mpr ht)), fun i => ?_⟩
      have hi := (hM t).eigenvalues_mem_spectrum_real i
      exact ⟨(spectralMin_isLeast (hM t)).2 hi, (spectralMax_isGreatest (hM t)).2 hi⟩
  refine ⟨t₀, hpsd, hsingular, τ, ⟨hτ, hafter, hratio, hcond⟩, ?_⟩
  intro σ hσ
  exact le_antisymm ((hσ.2.2.2 τ).mp ((hcond τ).mpr le_rfl))
    ((hcond σ).mp ((hσ.2.2.2 σ).mpr le_rfl))

/-- The actual crossing is stable under perturbation of the Hermitian direction
in operator norm, with the same Loewner bounds for the translation matrix. -/
theorem conditioned_entry_stable {B U W : ComplexMatrix} {lo hi τ σ : ℝ}
    (hB : B.IsHermitian) (hU : U.IsHermitian) (hW : W.IsHermitian)
    (hlo : algebraMap ℝ ComplexMatrix lo ≤ B) (hhi : B ≤ algebraMap ℝ ComplexMatrix hi)
    (hd : 0 < lo - (2 / 3 : ℝ) * hi)
    (hτ : conditionedGap (rayMatrix B U τ) = 0)
    (hσ : conditionedGap (rayMatrix B W σ) = 0) :
    |τ - σ| ≤ ((5 / 3 : ℝ) * ‖U - W‖) / (lo - (2 / 3 : ℝ) * hi) := by
  have hcompare {X Y : ComplexMatrix} (hX : X.IsHermitian) (hY : Y.IsHermitian) (t : ℝ) :
      conditionedGap (rayMatrix B Y t) - conditionedGap (rayMatrix B X t) ≤
        (5 / 3 : ℝ) * ‖X - Y‖ := by
    have ⟨hmin, hmax⟩ := spectralExtrema_abs_sub_le
      (rayMatrix_isHermitian hX hB t) (rayMatrix_isHermitian hY hB t)
    have hsub : rayMatrix B X t - rayMatrix B Y t = X - Y := by
      simp only [rayMatrix, add_sub_add_left_eq_sub]
    rw [hsub] at hmin hmax
    unfold conditionedGap
    linarith only [(abs_le.mp hmin).1, (abs_le.mp hmax).2]
  apply (le_div_iff₀ hd).mpr
  rcases le_total σ τ with h | h
  · have hg := conditionedGap_growth hB hU hlo hhi h
    have hc := hcompare hU hW σ
    rw [hτ, zero_sub] at hg
    rw [hσ, zero_sub] at hc
    rw [abs_of_nonneg (sub_nonneg.mpr h), mul_comm]
    exact hg.trans hc
  · have hg := conditionedGap_growth hB hW hlo hhi h
    have hc := hcompare hW hU τ
    rw [hσ, zero_sub] at hg
    rw [hτ, zero_sub, norm_sub_rev] at hc
    rw [abs_of_nonpos (sub_nonpos.mpr h), neg_sub, mul_comm]
    exact hg.trans hc

end

private theorem posDef_of_spectral_bounds {M : Mat} (hM : M.IsHermitian)
    {mmin mmax : ℝ} (hmmax : 0 < mmax) (hρ : (2 / 3 : ℝ) ≤ mmin / mmax)
    (hbounds : ∀ i, hM.eigenvalues i ∈ Icc mmin mmax) : M.PosDef := by
  have hmmin := (mul_pos (by norm_num : (0 : ℝ) < 2 / 3) hmmax).trans_le
    ((le_div_iff₀ hmmax).mp hρ)
  exact hM.posDef_iff_eigenvalues_pos.mpr fun i => hmmin.trans_le (hbounds i).1

/-- The thermal endpoints of `B = G²`, in ordinary-trace normalization. -/
def bmin (r : ℝ) : ℝ := rootScale r ^ 2

def bmax (r : ℝ) : ℝ := bmin r * r ^ 2

theorem bmin_pos {r : ℝ} (hr : 1 ≤ r) : 0 < bmin r :=
  pow_pos (rootScale_pos (zero_le_one.trans hr)) 2

theorem bmax_div_bmin {r : ℝ} (hr : 1 ≤ r) : bmax r / bmin r = r ^ 2 := by
  rw [bmax, mul_comm, mul_div_cancel_right₀ _ (bmin_pos hr).ne']

private theorem baseEntry_levels {r : ℝ} (hr : 1 ≤ r) (i : Occupation) :
    baseEntry r i = ![bmin r, bmin r * r, bmin r * r, bmax r] (finProdFinEquiv i) := by
  obtain ⟨i, j⟩ := i
  fin_cases i <;> fin_cases j <;>
    simp [baseEntry, rootValue, finProdFinEquiv, bmin, bmax, mul_pow,
      rootRatio_sq (zero_le_one.trans hr)]

private theorem base_spectrum (r : ℝ) : spectrum ℝ (base r) = Set.range (baseEntry r) := by
  ext x
  rw [base_diagonal, ← spectrum.algebraMap_mem_iff ℂ, spectrum_diagonal]
  change ((x : ℂ) ∈ Set.range (fun i => (baseEntry r i : ℂ))) ↔ _
  simp only [Set.mem_range, Complex.ofReal_inj]

/-- Both ends of the thermal enclosure are attained by the physical matrix. -/
theorem base_spectral_endpoints {r : ℝ} (hr : 1 ≤ r) :
    IsLeast (spectrum ℝ (base r)) (bmin r) ∧
      IsGreatest (spectrum ℝ (base r)) (bmax r) := by
  rw [base_spectrum]
  have hr2 : r ≤ r ^ 2 := by
    simpa only [pow_two, one_mul] using
      mul_le_mul_of_nonneg_right hr (zero_le_one.trans hr)
  have hlo : bmin r ≤ bmin r * r := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hr (bmin_pos hr).le
  have hhi : bmin r * r ≤ bmax r := mul_le_mul_of_nonneg_left hr2 (bmin_pos hr).le
  have hbounds (i : Occupation) : baseEntry r i ∈ Icc (bmin r) (bmax r) := by
    obtain ⟨i, j⟩ := i
    rw [baseEntry_levels hr]
    fin_cases i <;> fin_cases j <;>
      simp [finProdFinEquiv, hlo, hhi, hlo.trans hhi]
  constructor
  · refine ⟨⟨(0, 0), ?_⟩, ?_⟩
    · simp [baseEntry_levels hr, finProdFinEquiv]
    · rintro _ ⟨i, rfl⟩
      exact (hbounds i).1
  · refine ⟨⟨(1, 1), ?_⟩, ?_⟩
    · simp [baseEntry_levels hr, finProdFinEquiv]
    · rintro _ ⟨i, rfl⟩
      exact (hbounds i).2

private theorem base_posDef {r : ℝ} (hr : 1 ≤ r) : (base r).PosDef := by
  rw [base_diagonal]
  exact Matrix.PosDef.diagonal fun i => Complex.zero_lt_real.mpr (pow_pos (rootValue_pos hr i) 2)

private theorem base_bounds {r : ℝ} (hr : 1 ≤ r) (i : Occupation) :
    (base_posDef hr).isHermitian.eigenvalues i ∈ Icc (bmin r) (bmax r) := by
  obtain ⟨hl, hu⟩ := base_spectral_endpoints hr
  have hi := (base_posDef hr).isHermitian.eigenvalues_mem_spectrum_real i
  exact ⟨hl.2 hi, hu.2 hi⟩

private theorem base_cube {r : ℝ} (hr : 1 ≤ r) : base r ^ 3 = D r := by
  simpa only [base, ← pow_mul] using G_pow_six hr

private theorem base_cube_trace {r : ℝ} (hr : 1 ≤ r) : (base r ^ 3).trace.re = 1 := by
  have hmass : gibbsLow r + gibbsHigh r = 1 := by
    have hr0 : 0 < r := zero_lt_one.trans_le hr
    unfold gibbsHigh gibbsLow
    field_simp [(show 0 < 1 + r ^ 3 by positivity).ne']
  rw [base_cube hr]
  simp only [D, Matrix.trace_diagonal, Fintype.sum_prod_type, Fin.sum_univ_two,
    Complex.add_re, Complex.ofReal_re]
  change gibbsLow r * gibbsLow r + gibbsLow r * gibbsHigh r +
    (gibbsHigh r * gibbsLow r + gibbsHigh r * gibbsHigh r) = 1
  calc
    _ = (gibbsLow r + gibbsHigh r) ^ 2 := by ring
    _ = 1 := by rw [hmass, one_pow]

private theorem base_center {r : ℝ} (hr : 1 ≤ r) {A : Mat} (hcenter : (D r * A).trace = 0) :
    (base r ^ 2 * sandwich r A).trace.re = 0 := by
  have htrace : (base r ^ 2 * sandwich r A).trace = (D r * A).trace := by
    calc
      _ = (G r ^ 5 * A * G r).trace := by
        congr 1
        unfold base sandwich
        noncomm_ring
      _ = _ := by rw [Matrix.trace_mul_cycle, ← pow_succ' (G r) 5, G_pow_six hr]
  rw [htrace, hcenter, Complex.zero_re]

private theorem embedded_trace_mean {r : ℝ} (hr : 1 ≤ r) {A : Mat}
    (hcenter : (D r * A).trace = 0) (t : ℝ) :
    (base r ^ 2 * embedded r A t).trace.re = t := by
  rw [embedded, mul_add, mul_smul_comm, Matrix.trace_add, Complex.add_re,
    Matrix.trace_smul, Complex.smul_re, smul_eq_mul, ← pow_succ (base r) 2,
    base_cube_trace hr, base_center hr hcenter, mul_one, add_zero]

/-- Centering forces any translate proportional to `B` to have zero direction. -/
theorem residual_trace_pos {r t : ℝ} (hr : 1 ≤ r) {A : Mat}
    (hcenter : (D r * A).trace = 0) (hA0 : A ≠ 0) :
    ((residual r A t)ᴴ * residual r A t).trace.re > 0 := by
  let H := residual r A t
  let M := embedded r A t
  let γ : ℝ := (M ^ 3).trace.re / (base r * M ^ 2).trace.re
  have hH : H ≠ 0 := by
    intro hz
    have hM : M = (γ : ℂ) • base r := sub_eq_zero.mp hz
    have hsmul : (γ : ℂ) • base r = γ • base r := by
      ext i j
      simp only [Matrix.smul_apply, Complex.real_smul, smul_eq_mul]
    rw [hsmul] at hM
    have hmean := embedded_trace_mean hr hcenter t
    change (base r ^ 2 * M).trace.re = t at hmean
    rw [hM, mul_smul_comm, Matrix.trace_smul, Complex.smul_re, smul_eq_mul,
      ← pow_succ (base r) 2, base_cube_trace hr, mul_one] at hmean
    have hU : sandwich r A = 0 := by
      rw [hmean] at hM
      exact add_left_cancel (hM.trans (add_zero (t • base r)).symm)
    apply hA0
    calc
      A = (GInv r * G r) * A * (G r * GInv r) := by
        rw [GInv_mul_G hr, G_mul_GInv hr, one_mul, mul_one]
      _ = GInv r * sandwich r A * GInv r := by simp only [sandwich, mul_assoc]
      _ = 0 := by rw [hU, mul_zero, zero_mul]
  change 0 < (Hᴴ * H).trace.re
  rw [← sum_normSq_eq_trace]
  apply Finset.sum_pos'
  · exact fun _ _ => Complex.normSq_nonneg _
  · have hex : ∃ i j, H i j ≠ 0 := by
      by_contra! hzero
      exact hH (Matrix.ext fun i j => hzero i j)
    obtain ⟨i, j, hij⟩ := hex
    have hnorm : Complex.normSq (H i j) ≠ 0 := fun h => hij (Complex.normSq_eq_zero.mp h)
    exact ⟨(i, j), Finset.mem_univ _, lt_of_le_of_ne (Complex.normSq_nonneg _) hnorm.symm⟩

/-- The literal Wu coefficient is positive, including at the tracial endpoint. -/
theorem alpha_pos {r : ℝ} (hr : 1 ≤ r) : 0 < alpha r := by
  rcases eq_or_lt_of_le hr with h | h
  · rw [← h]
    norm_num [alpha]
  have hr0 : 0 < r := zero_lt_one.trans h
  have hnum : 0 < r ^ 2 - 1 := by nlinarith only [h, sq_nonneg (r - 1)]
  rw [alpha, if_neg (ne_of_gt h)]
  exact div_pos (mul_pos (by norm_num) hnum) (mul_pos (by positivity) (Real.log_pos h))

private theorem variance_nonneg {r : ℝ} (hr : 1 ≤ r) {A : Mat} (hA : A.IsHermitian) :
    0 ≤ V r A := by
  rw [WuCubicTranslationEnergy.V_eq_entries r A hA]
  refine Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => ?_
  have hi : 0 < baseEntry r i := pow_pos (rootValue_pos hr i) 2
  have hj : 0 < baseEntry r j := pow_pos (rootValue_pos hr j) 2
  unfold WuCubicTranslationEnergy.pairWeight
  exact mul_nonneg (by positivity) (Complex.normSq_nonneg _)

private theorem operatorDeficit_translate_eq {r : ℝ} (hr : 1 ≤ r) (A : Mat) (t : ℝ) :
    operatorDeficit r (translate A t) =
      cubicEnergy r (translate A t) - alpha r * cubicEntropy (base r) (embedded r A t) := by
  have hm : sandwich r (translate A t) = embedded r A t := sandwich_translate r A t
  have hm' : G r * translate A t * G r = embedded r A t := hm
  unfold operatorDeficit cubicEnergy
  simp only [hm, hm', cubicEntropy, base_cube hr, Matrix.mul_sub, Matrix.trace_sub,
    Complex.sub_re, sandwich] <;> ring

/-- The derivative exists at a conditioned translate, with the signed cubic
moment and the full positive coefficient of the Hilbert–Schmidt residual. -/
theorem operatorDeficit_hasDerivAt_conditioned {r t : ℝ} {A : Mat}
    (hr₀ : 1049 / 1000 ≤ r) (hr₁ : r ≤ 6 / 5) (ht : 0 < t)
    (hA : A.IsHermitian) (hcenter : (D r * A).trace = 0)
    (hcond : Conditioned (embedded r A t)) :
    ∃ d, HasDerivAt (fun s : ℝ => operatorDeficit r (translate A s)) d t ∧
      (9 / 4 : ℝ) * (2 * V r A - V₁ r A) - alpha r * (6 * V r A + 2 * C r A / t) +
        3 * alpha r * (bmin r / 18) * ((residual r A t)ᴴ * residual r A t).trace.re ≤ d := by
  have hr : 1 ≤ r := (by norm_num : (1 : ℝ) ≤ 1049 / 1000).trans hr₀
  obtain ⟨hHerm, mmin, mmax, hmmax, hρ, hbounds⟩ := hcond
  let M := embedded r A t
  have hM : M.PosDef := posDef_of_spectral_bounds hHerm hmmax hρ hbounds
  have hb := bmin_pos hr
  have hbmax : bmin r ≤ bmax r := (base_bounds hr (0, 0)).1.trans (base_bounds hr (0, 0)).2
  have hκ : bmax r / bmin r ≤ 36 / 25 := by
    rw [bmax_div_bmin hr]
    calc
      _ ≤ (6 / 5 : ℝ) ^ 2 := pow_le_pow_left₀ (zero_le_one.trans hr) hr₁ 2
      _ = _ := by norm_num
  obtain ⟨_, d, hd, hdupper⟩ := focal_cubicEntropy_slope (base_posDef hr) hM
    (base_cube_trace hr) hb hbmax hmmax (base_bounds hr) hbounds hκ hρ
  have hE := spectralPair_squareEntropy_le (base r) (sandwich r A) ht (base_posDef hr)
    hM.posSemidef (base_cube_trace hr) (base_center hr hcenter)
  have hgap : d / 3 + (bmin r / 18) * ((residual r A t)ᴴ * residual r A t).trace.re ≤
      2 * V r A + (2 / (3 * t)) * C r A := by
    exact (le_sub_iff_add_le.mp hdupper).trans hE
  have hd' : HasDerivAt (fun s : ℝ => cubicEntropy (base r) (embedded r A s)) d t := by
    have hshift : HasDerivAt (fun s : ℝ => s - t) 1 t := (hasDerivAt_id t).sub_const t
    have h := hd.comp_of_eq t hshift (sub_self t).symm
    have heq : (fun s : ℝ => cubicEntropy (base r) (M + s • base r)) ∘ (fun s => s - t) =
        fun s => cubicEntropy (base r) (embedded r A s) := by
      funext s
      dsimp only [Function.comp_apply, M, embedded]
      congr 1
      rw [sub_smul]
      abel
    rwa [heq, mul_one] at h
  have he := cubicEnergy_hasDerivAt_degree hr A hA t
  have henergy := cubicEnergy_deriv_ge hr A hA hcenter t
  rw [he.deriv] at henergy
  refine ⟨(9 / 4 : ℝ) * (∑ k, (WuCubicThermalBasis.degree k : ℝ) *
    WuCubicTranslationEnergy.vWeight r A k) - alpha r * d, ?_, ?_⟩
  · simp_rw [operatorDeficit_translate_eq hr]
    exact he.sub (hd'.const_mul (alpha r))
  · have halg : 3 * ((2 / (3 * t)) * C r A) = 2 * C r A / t := by
      field_simp [ht.ne'] <;> ring
    have hdupper' : d ≤ 6 * V r A + 2 * C r A / t -
        3 * ((bmin r / 18) * ((residual r A t)ᴴ * residual r A t).trace.re) := by
      rw [← halg]
      linarith only [hgap]
    have hscaled := mul_le_mul_of_nonneg_left hdupper' (alpha_pos hr).le
    calc
      _ = (9 / 4 : ℝ) * (2 * V r A - V₁ r A) -
          alpha r * (6 * V r A + 2 * C r A / t -
            3 * ((bmin r / 18) * ((residual r A t)ᴴ * residual r A t).trace.re)) := by ring
      _ ≤ _ := sub_le_sub henergy hscaled

/-- Lower bound on the literal deficit derivative in the residual temperature band. -/
theorem operatorDeficit_deriv_ge_conditioned {r t : ℝ} {A : Mat}
    (hr₀ : 1049 / 1000 ≤ r) (hr₁ : r ≤ 6 / 5) (ht : 0 < t)
    (hA : A.IsHermitian) (hcenter : (D r * A).trace = 0)
    (hcond : Conditioned (embedded r A t)) :
    (3 / 2 : ℝ) * V r A - (9 / 4 : ℝ) * V₁ r A - max (C r A) 0 / t +
        3 * alpha r * (bmin r / 18) * ((residual r A t)ᴴ * residual r A t).trace.re ≤
      deriv (fun s : ℝ => operatorDeficit r (translate A s)) t := by
  have hr : 1 ≤ r := (by norm_num : (1 : ℝ) ≤ 1049 / 1000).trans hr₀
  have hα := alpha_pos hr
  have hhalf := (WuCubicOccupationTaylor.alpha_bounds_of_one_le hr).2
  have hV := variance_nonneg hr hA
  have hquad : alpha r * (6 * V r A) ≤ 3 * V r A := by
    calc
      _ ≤ (1 / 2 : ℝ) * (6 * V r A) := mul_le_mul_of_nonneg_right hhalf (by positivity)
      _ = _ := by ring
  have hcub : alpha r * (2 * C r A / t) ≤ max (C r A) 0 / t := by
    have hmax : 0 ≤ max (C r A) 0 := le_max_right _ _
    calc
      _ ≤ alpha r * (2 * max (C r A) 0 / t) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (le_max_left _ _) (by norm_num)) ht.le) hα.le
      _ ≤ (1 / 2 : ℝ) * (2 * max (C r A) 0 / t) :=
        mul_le_mul_of_nonneg_right hhalf (by positivity)
      _ = _ := by ring
  obtain ⟨d, hd, hbound⟩ := operatorDeficit_hasDerivAt_conditioned hr₀ hr₁ ht hA hcenter hcond
  rw [hd.deriv]
  rw [mul_add] at hbound
  linarith only [hbound, hquad, hcub]

/-- The upper cutoff of the actual spectral pair yields the pointwise signed
third-moment estimate, even when the cubic moment is negative. -/
theorem C_le_spectralUpper_sub_mul_variance {r t mmax : ℝ} {A : Mat}
    (hr : 1 ≤ r) (hcenter : (D r * A).trace = 0) (hmmax : 0 ≤ mmax)
    (hM : (embedded r A t).IsHermitian) (hupper : ∀ j, hM.eigenvalues j ≤ mmax) :
    C r A ≤ (mmax / bmin r - t) * V r A := by
  let hB := base_posDef hr
  let pi := spectralWeight hB.isHermitian hM
  let x := spectralRatio hB.isHermitian hM
  obtain ⟨_, _, hsecond, hthird⟩ := spectralPair_centeredMoments (base r) (sandwich r A) t
    hB hM (base_cube_trace hr) (base_center hr hcenter)
  change (∑ p, pi p * (x p - t) ^ 2) = V r A at hsecond
  change (∑ p, pi p * (x p - t) ^ 3) = C r A at hthird
  rw [← hthird, ← hsecond, Finset.mul_sum]
  refine Finset.sum_le_sum fun p _ => ?_
  have hpi : 0 ≤ pi p :=
    mul_nonneg (pow_nonneg (hB.eigenvalues_pos p.1).le 3) (sq_nonneg _)
  have hx : x p ≤ mmax / bmin r :=
    (div_le_div_of_nonneg_right (hupper p.2) (hB.eigenvalues_pos p.1).le).trans
      (div_le_div_of_nonneg_left hmmax (bmin_pos hr) (base_bounds hr p.1).1)
  rw [mul_left_comm (mmax / bmin r - t)]
  apply mul_le_mul_of_nonneg_left _ hpi
  calc
    _ = (x p - t) * (x p - t) ^ 2 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (sub_le_sub_right hx t) (sq_nonneg _)

private theorem thermal_trace_square {r : ℝ} (hr : 1 ≤ r) :
    bmin r * (base r ^ 2).trace.re = ((1 + r ^ 2) / (1 + r ^ 3)) ^ 2 := by
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  have hg : 0 ≤ gibbsLow r := by unfold gibbsLow; positivity
  have hpow : bmin r ^ 3 = ((1 + r ^ 3)⁻¹) ^ 2 := by
    rw [bmin, ← pow_mul]
    change rootScale r ^ 6 = _
    have hs : rootScale r ^ 6 = gibbsLow r ^ 2 := by
      unfold rootScale
      rw [← Real.rpow_mul_natCast hg]
      norm_num
    rw [hs]
    simp [gibbsLow, one_div]
  have htrace : (base r ^ 2).trace.re = bmin r ^ 2 * (1 + r ^ 2) ^ 2 := by
    simp only [base_diagonal, Matrix.diagonal_pow, Pi.pow_apply, ← Complex.ofReal_pow,
      Matrix.trace_diagonal, Complex.re_sum, Complex.ofReal_re, Fintype.sum_prod_type,
      Fin.sum_univ_two]
    simp [baseEntry_levels hr, finProdFinEquiv, bmax, ← Complex.ofReal_pow,
      ← Complex.ofReal_mul] <;> ring
  rw [htrace, ← mul_assoc, ← pow_succ' (bmin r) 2, hpow, div_eq_mul_inv, mul_pow]
  exact mul_comm _ _

private theorem thermal_trace_square_ge {r : ℝ} (hr : 1 ≤ r) (hr₁ : r ≤ 6 / 5) :
    (4 / 5 : ℝ) ≤ bmin r * (base r ^ 2).trace.re := by
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  have ha : 0 < 1 + r ^ 2 := by positivity
  have hb : 0 < 1 + r ^ 3 := by positivity
  have hrsq : r ^ 2 ≤ (6 / 5 : ℝ) ^ 2 := pow_le_pow_left₀ hr0.le hr₁ 2
  have hf : r ^ 2 / (1 + r ^ 2) ≤ 36 / 61 := by
    apply (div_le_iff₀ ha).mpr
    linarith only [hrsq]
  have hfactor : (r - 1) * (r ^ 2 / (1 + r ^ 2)) ≤ (1 / 5 : ℝ) * (36 / 61) :=
    mul_le_mul (by linarith only [hr₁]) hf (by positivity) (by norm_num)
  have hq : (1 + r ^ 3) / (1 + r ^ 2) = 1 + (r - 1) * (r ^ 2 / (1 + r ^ 2)) := by
    field_simp [ha.ne'] <;> ring
  have hqle : (1 + r ^ 3) / (1 + r ^ 2) ≤ 341 / 305 := by
    rw [hq]
    linarith only [hfactor]
  have hsq := pow_le_pow_left₀ (div_nonneg hb.le ha.le) hqle 2
  have hsq' : (1 + r ^ 3) ^ 2 / (1 + r ^ 2) ^ 2 ≤ (5 / 4 : ℝ) := by
    rw [← div_pow]
    exact hsq.trans (by norm_num)
  have hcross := (div_le_iff₀ (pow_pos ha 2)).mp hsq'
  rw [thermal_trace_square hr, div_pow]
  apply (le_div_iff₀ (pow_pos hb 2)).mpr
  linarith only [hcross]

private theorem spectral_min_mul_trace_square_le {r t mmin : ℝ} {A : Mat}
    (hr : 1 ≤ r) (hcenter : (D r * A).trace = 0) (hM : (embedded r A t).IsHermitian)
    (hlower : ∀ j, mmin ≤ hM.eigenvalues j) :
    mmin * (base r ^ 2).trace.re ≤ t := by
  let hB := (base_posDef hr).isHermitian
  let b := hB.eigenvalues
  let w := overlap hB hM
  have htrace : (base r ^ 2).trace.re = ∑ i, b i ^ 2 := by
    rw [← cfc_pow_id (R := ℝ) (base r) 2 hB]
    exact D5.S3.Resource.LogDet.PathSpectralClassical.trace_cfc_eq_sum (base r) hB _
  have hmean := trace_cfc_product (base r) (embedded r A t) hB hM (fun z => z ^ 2) id
  rw [cfc_pow_id (R := ℝ) (base r) 2 hB.isSelfAdjoint,
    cfc_id ℝ (embedded r A t) hM.isSelfAdjoint,
    embedded_trace_mean hr hcenter] at hmean
  calc
    _ = mmin * ∑ i, ∑ j, b i ^ 2 * w i j :=
      congrArg (mmin * ·) (htrace.trans (overlap_weighted_row hB hM (fun i => b i ^ 2)).symm)
    _ ≤ ∑ i, ∑ j, b i ^ 2 * hM.eigenvalues j * w i j := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun j _ => ?_
      calc
        _ ≤ hM.eigenvalues j * (b i ^ 2 * w i j) :=
          mul_le_mul_of_nonneg_right (hlower j) (mul_nonneg (sq_nonneg _) (sq_nonneg _))
        _ = _ := by ring
    _ = t := hmean.symm

/-- In the conditioned band the signed cubic moment divided by `t` is at most
`7/8` of the ordinary trace variance. -/
theorem C_div_le_seven_eighths_variance {r t : ℝ} {A : Mat}
    (hr₀ : 1049 / 1000 ≤ r) (hr₁ : r ≤ 6 / 5) (ht : 0 < t)
    (hcenter : (D r * A).trace = 0) (hcond : Conditioned (embedded r A t)) :
    C r A / t ≤ (7 / 8 : ℝ) * V r A := by
  have hr : 1 ≤ r := (by norm_num : (1 : ℝ) ≤ 1049 / 1000).trans hr₀
  obtain ⟨hM, mmin, mmax, hmmax, hρ, hbounds⟩ := hcond
  have hmin := (le_div_iff₀ hmmax).mp hρ
  have hmean := spectral_min_mul_trace_square_le hr hcenter hM (fun j => (hbounds j).1)
  have hb := bmin_pos hr
  have hthermal := thermal_trace_square_ge hr hr₁
  have htrace : 0 ≤ (base r ^ 2).trace.re := by
    by_contra! h
    exact (not_lt_of_ge ((by norm_num : (0 : ℝ) ≤ 4 / 5).trans hthermal))
      (mul_neg_of_pos_of_neg hb h)
  have hscaled : (4 / 5 : ℝ) * ((2 / 3 : ℝ) * mmax) ≤ t * bmin r := by
    calc
      _ ≤ (bmin r * (base r ^ 2).trace.re) * ((2 / 3 : ℝ) * mmax) :=
        mul_le_mul_of_nonneg_right hthermal (by positivity)
      _ = ((2 / 3 : ℝ) * mmax * (base r ^ 2).trace.re) * bmin r := by ring
      _ ≤ (mmin * (base r ^ 2).trace.re) * bmin r :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hmin htrace) hb.le
      _ ≤ _ := mul_le_mul_of_nonneg_right hmean hb.le
  have hR : mmax / bmin r ≤ (15 / 8 : ℝ) * t := by
    apply (div_le_iff₀ hb).mpr
    nlinarith only [hscaled]
  let hB := base_posDef hr
  have hV : 0 ≤ V r A := by
    obtain ⟨_, _, hsecond, _⟩ := spectralPair_centeredMoments (base r) (sandwich r A) t
      hB hM (base_cube_trace hr) (base_center hr hcenter)
    change (∑ p, spectralWeight hB.isHermitian hM p *
      (spectralRatio hB.isHermitian hM p - t) ^ 2) = V r A at hsecond
    rw [← hsecond]
    exact Finset.sum_nonneg fun p _ => mul_nonneg
      (mul_nonneg (pow_nonneg (hB.eigenvalues_pos p.1).le 3) (sq_nonneg _)) (sq_nonneg _)
  apply (div_le_iff₀ ht).mpr
  calc
    _ ≤ (mmax / bmin r - t) * V r A :=
      C_le_spectralUpper_sub_mul_variance hr hcenter hmmax.le hM (fun j => (hbounds j).2)
    _ ≤ ((15 / 8 : ℝ) * t - t) * V r A :=
      mul_le_mul_of_nonneg_right (sub_le_sub_right hR t) hV
    _ = _ := by ring

/-- The derivative is strictly positive in either degree sector, including the
two threshold equalities. -/
theorem operatorDeficit_deriv_pos_conditioned {r t : ℝ} {A : Mat}
    (hr₀ : 1049 / 1000 ≤ r) (hr₁ : r ≤ 6 / 5) (ht : 0 < t)
    (hA : A.IsHermitian) (hcenter : (D r * A).trace = 0) (hA0 : A ≠ 0)
    (hcond : Conditioned (embedded r A t))
    (hdegree : V₁ r A ≤ (5 / 18 : ℝ) * V r A ∨
      (C r A ≤ 0 ∧ V₁ r A ≤ (2 / 3 : ℝ) * V r A)) :
    0 < deriv (fun s : ℝ => operatorDeficit r (translate A s)) t := by
  have hr : 1 ≤ r := (by norm_num : (1 : ℝ) ≤ 1049 / 1000).trans hr₀
  have hgap : 0 < 3 * alpha r * (bmin r / 18) * ((residual r A t)ᴴ * residual r A t).trace.re :=
    mul_pos (mul_pos (mul_pos (by norm_num) (alpha_pos hr))
      (div_pos (bmin_pos hr) (by norm_num))) (residual_trace_pos hr hcenter hA0)
  have hmain := operatorDeficit_deriv_ge_conditioned hr₀ hr₁ ht hA hcenter hcond
  have hbulk : 0 ≤ (3 / 2 : ℝ) * V r A - (9 / 4 : ℝ) * V₁ r A - max (C r A) 0 / t := by
    rcases hdegree with hdegree | ⟨hC, hdegree⟩
    · have hc := C_div_le_seven_eighths_variance hr₀ hr₁ ht hcenter hcond
      have hV := variance_nonneg hr hA
      have hmax : max (C r A) 0 / t ≤ (7 / 8 : ℝ) * V r A := by
        rw [div_le_iff₀ ht]
        exact max_le ((div_le_iff₀ ht).mp hc) (by positivity)
      linarith only [hdegree, hmax]
    · rw [max_eq_right hC, zero_div, sub_zero]
      linarith only [hdegree]
  exact (add_pos_of_nonneg_of_pos hbulk hgap).trans_le hmain

/-- At fixed residual temperature the literal deficit is strictly increasing
on an interval of positive, conditioned translations. -/
theorem operatorDeficit_strictMonoOn_conditioned {r lo hi : ℝ} {A : Mat}
    (hr₀ : 1049 / 1000 ≤ r) (hr₁ : r ≤ 6 / 5)
    (hA : A.IsHermitian) (hcenter : (D r * A).trace = 0) (hA0 : A ≠ 0)
    (hdegree : V₁ r A ≤ (5 / 18 : ℝ) * V r A ∨
      (C r A ≤ 0 ∧ V₁ r A ≤ (2 / 3 : ℝ) * V r A))
    (hinterval : ∀ t ∈ Icc lo hi, 0 < t ∧ Conditioned (embedded r A t)) :
    StrictMonoOn (fun t : ℝ => operatorDeficit r (translate A t)) (Icc lo hi) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc lo hi)
  · intro t ht
    obtain ⟨ht₀, hcond⟩ := hinterval t ht
    obtain ⟨_, hd, _⟩ := operatorDeficit_hasDerivAt_conditioned hr₀ hr₁ ht₀ hA hcenter hcond
    exact hd.continuousAt.continuousWithinAt
  · intro t ht
    obtain ⟨ht₀, hcond⟩ := hinterval t (interior_subset ht)
    exact operatorDeficit_deriv_pos_conditioned hr₀ hr₁ ht₀ hA hcenter hA0 hcond hdegree

/-- The actual Gibbs ray has a singular PSD onset followed by its unique
conditioned entry. The normalized deficit at entry has first spectral
coordinate `2/3`. The boundary margin is the input supplied by the
interval certificate at this coordinate. -/
theorem operatorDeficit_conditioned_entry {r : ℝ} {A : Mat}
    (hr₀ : 1049 / 1000 ≤ r) (hr₁ : r ≤ 6 / 5)
    (hA : A.IsHermitian) (hcenter : (D r * A).trace = 0) (hA0 : A ≠ 0) :
    ∃ t₀ τ, 0 < τ ∧ t₀ < τ ∧
      (∀ t, (embedded r A t).PosSemidef ↔ t₀ ≤ t) ∧
      ¬ (embedded r A t₀).PosDef ∧ embedded r A t₀ ≠ 0 ∧
      (∀ t, Conditioned (embedded r A t) ↔ τ ≤ t) ∧
      ∃ (W : unitary WuCubicDirectedOccupationCap.Mat) (ell n q : ℝ),
        0 < ell ∧ (2 / 3 : ℝ) ≤ n ∧ n ≤ q ∧ q ≤ 1 ∧
        IsGreatest (spectrum ℝ (embedded r A τ)) ell ∧
        embedded r A τ = physicalFrame W *
          diagonal (fun i => ((ell * levelsAt (2 / 3) n q i : ℝ) : ℂ)) *
          (physicalFrame W)ᴴ ∧
        operatorDeficit r (translate A τ) =
          ell ^ 3 * normalizedDeficit r W (2 / 3) n q ∧
        ((V₁ r A ≤ (5 / 18 : ℝ) * V r A ∨
          (C r A ≤ 0 ∧ V₁ r A ≤ (2 / 3 : ℝ) * V r A)) →
          (1 / 100000 : ℝ) < normalizedDeficit r W (2 / 3) n q →
          ∀ t, τ ≤ t → ell ^ 3 * (1 / 100000 : ℝ) < operatorDeficit r (translate A t)) := by
  have hr : 1 ≤ r := (by norm_num : (1 : ℝ) ≤ 1049 / 1000).trans hr₀
  have hU : (sandwich r A).IsHermitian := by
    rw [Matrix.IsHermitian, sandwich, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      G_adjoint, hA.eq, Matrix.mul_assoc]
  have hB := (base_posDef hr).isHermitian
  have hlo : algebraMap ℝ Mat (bmin r) ≤ base r :=
    (algebraMap_le_iff_le_spectrum hB.isSelfAdjoint).mpr (fun _ hx =>
      (base_spectral_endpoints hr).1.2 hx)
  have hhi : base r ≤ algebraMap ℝ Mat (bmax r) :=
    (le_algebraMap_iff_spectrum_le hB.isSelfAdjoint).mpr (fun _ hx =>
      (base_spectral_endpoints hr).2.2 hx)
  have hband : bmax r ≤ (36 / 25 : ℝ) * bmin r := by
    apply (div_le_iff₀ (bmin_pos hr)).mp
    rw [bmax_div_bmin hr]
    exact (pow_le_pow_left₀ (zero_le_one.trans hr) hr₁ 2).trans_eq (by norm_num)
  have hne (t : ℝ) : embedded r A t ≠ 0 := by
    intro hz
    have ht := embedded_trace_mean hr hcenter t
    rw [hz, mul_zero, Matrix.trace_zero, Complex.zero_re] at ht
    have hUzero : sandwich r A = 0 := by
      simpa only [embedded, ← ht, zero_smul, zero_add] using hz
    apply hA0
    calc
      A = (GInv r * G r) * A * (G r * GInv r) := by
        rw [GInv_mul_G hr, G_mul_GInv hr, one_mul, mul_one]
      _ = GInv r * sandwich r A * GInv r := by simp only [sandwich, mul_assoc]
      _ = 0 := by rw [hUzero, mul_zero, zero_mul]
  obtain ⟨t₀, hpsd, hsingular, τ, ⟨_, hafter, hratio, hcond⟩, _⟩ :=
    conditioned_entry_q_two_thirds hU hB (bmin_pos hr) hlo hhi hband hne
  have hpsd₀ : (embedded r A t₀).PosSemidef := (hpsd t₀).mpr le_rfl
  have ht₀ : 0 ≤ t₀ := by
    simpa only [zero_mul] using spectral_min_mul_trace_square_le hr hcenter hpsd₀.isHermitian
      (fun i => hpsd₀.eigenvalues_nonneg i)
  have hτ : 0 < τ := ht₀.trans_lt hafter
  have hM : (embedded r A τ).PosSemidef := (hpsd τ).mpr hafter.le
  obtain ⟨W, v, hv, _, hspec, hdiag⟩ := exists_ordered_frame hM
  let ell := v 3
  let m := v 0 / ell
  let n := v 1 / ell
  let q := v 2 / ell
  have hmin : spectralMin (embedded r A τ) = v 0 := by
    apply (spectralMin_isLeast hM.isHermitian).unique
    rw [← hspec]
    exact ⟨⟨0, rfl⟩, by rintro _ ⟨i, rfl⟩; exact hv (Fin.zero_le i)⟩
  have hellMax : IsGreatest (spectrum ℝ (embedded r A τ)) ell := by
    rw [← hspec]
    exact ⟨⟨3, rfl⟩, by rintro _ ⟨i, rfl⟩; exact hv (Fin.le_last i)⟩
  have hmax := (spectralMax_isGreatest hM.isHermitian).unique hellMax
  have hell : 0 < ell := hmax ▸ spectralMax_pos_of_psd_ne_zero hM (hne τ)
  change spectralMin (embedded r A τ) / spectralMax (embedded r A τ) = _ at hratio
  rw [hmin, hmax] at hratio
  have hm : m = (2 / 3 : ℝ) := hratio
  have hn : (2 / 3 : ℝ) ≤ n := by
    rw [← hm]
    exact div_le_div_of_nonneg_right (hv (by decide : (0 : Fin 4) ≤ 1)) hell.le
  have hnq : n ≤ q := div_le_div_of_nonneg_right (hv (by decide : (1 : Fin 4) ≤ 2)) hell.le
  have hq : q ≤ 1 := (div_le_one hell).mpr (hv (by decide : (2 : Fin 4) ≤ 3))
  have hlevels : v = fun i => ell * levelsAt m n q i := by
    funext i
    have hscale (x : ℝ) : ell * (x / ell) = x := by
      rw [mul_comm, div_mul_cancel₀ _ hell.ne']
    fin_cases i <;> simp [levelsAt, m, n, q, hscale] <;> rfl
  rw [hm] at hlevels
  have hnormalized : embedded r A τ = physicalFrame W *
      diagonal (fun i => ((ell * levelsAt (2 / 3) n q i : ℝ) : ℂ)) * (physicalFrame W)ᴴ := by
    simpa only [hlevels] using hdiag
  have hscaled := operatorDeficit_eq_scaled hr (translate A τ) W ell (2 / 3) n q (by
    change sandwich r (translate A τ) = _
    exact (sandwich_translate r A τ).trans hnormalized)
  refine ⟨t₀, τ, hτ, hafter, hpsd, hsingular, hne t₀, hcond, W, ell, n, q,
    hell, hn, hnq, hq, hellMax, hnormalized, hscaled, ?_⟩
  intro hdegree hboundary t ht
  have hbound : ell ^ 3 * (1 / 100000 : ℝ) < operatorDeficit r (translate A τ) := by
    rw [hscaled]
    exact mul_lt_mul_of_pos_left hboundary (pow_pos hell 3)
  have hmono := operatorDeficit_strictMonoOn_conditioned hr₀ hr₁ hA hcenter hA0 hdegree
    (lo := τ) (hi := t) (fun s hs => ⟨hτ.trans_le hs.1, (hcond s).mpr hs.1⟩)
  exact hbound.trans_le (hmono.monotoneOn ⟨le_rfl, ht⟩ ⟨ht, le_rfl⟩ ht)

end D5.S3.Quantum.Semigroups.WuCubicConditionedTranslation
