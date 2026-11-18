/- GID: D5/S3/Quantum/Divergence/UmegakiKernelContraction
   generality: G
   mirror-B: D5/B/S3/Quantum/Divergence/UmegakiKernelContraction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Uniform endpoint contraction implies contraction of the arithmetic inverse forms. -/

import D5.S3.Quantum.Divergence.UmegakiReferenceTransport

/-! The endpoint bound yields the original universal positive trace test.
The simultaneous residual Gram bounds then give two weighted Cauchy–Schwarz
inequalities for the same output inverse direction. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
open Matrix
open scoped ComplexOrder MatrixOrder Kronecker
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction
open D5.S3.Quantum.Divergence.UniversalPositiveScalarizer
open D5.S3.Quantum.Divergence.UmegakiConditionalKernel
open D5.S3.Quantum.Divergence.UmegakiReferenceTransport

namespace D5.S3.Quantum.Divergence.UmegakiKernelContraction

universe u
variable {a b : Type u} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

/-- Uniform left-endpoint bound on every complex direction in the
partial-trace kernel, with every finite quantum reference and correlated base. -/
def EndpointBound (N : QuantumChannel a b) (c : ℝ) : Prop :=
  ∀ {R : Type u} [Fintype R] [DecidableEq R]
    (Z V : Matrix (R × a) (R × a) ℂ), Z.PosDef → partialTraceRight V = 0 →
    q (amp N Z) (amp N V) 0 ≤ c * q Z V 0

private lemma energy_grams {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Z Y : Matrix ι ι ℂ) (u : ℝ) :
    energy Z Y u = (1-u) * (Z * (Y * Yᴴ)).trace.re +
      u * (Z * (Yᴴ * Y)).trace.re := by
  simp only [energy, arithmetic, Matrix.mul_add, Matrix.mul_smul, Matrix.trace_add,
    Matrix.trace_smul, Complex.add_re, Complex.smul_re, smul_eq_mul]
  rw [← Matrix.mul_assoc Yᴴ Z Y, Matrix.trace_mul_cycle Yᴴ Z Y,
    Matrix.trace_mul_comm (Y * Yᴴ) Z, ← Matrix.mul_assoc Yᴴ Y Z,
    Matrix.trace_mul_comm (Yᴴ * Y) Z]

private lemma trace_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Z D : Matrix ι ι ℂ} (hZ : Z.PosSemidef) (hD : D.PosSemidef) :
    0 ≤ (Z * D).trace.re :=
  RHLinalg.trace_mul_nonneg_of_posSemidef hZ hD

private lemma trace_sub_gram {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Z D G : Matrix ι ι ℂ) (k : ℝ) :
    (Z * ((k : ℂ) • D - G)).trace.re =
      k * (Z * D).trace.re - (Z * G).trace.re := by
  simp [Matrix.mul_sub, Matrix.mul_smul, Matrix.trace_sub, Matrix.trace_smul,
    Complex.mul_re]

section Local
variable [Nonempty a] [Nonempty b]
variable {R : Type u} [Fintype R] [DecidableEq R]

private lemma energy_defects (N : QuantumChannel a b)
    (Z : Matrix (R × a) (R × a) ℂ) (Y : Matrix (R × b) (R × b) ℂ) (u : ℝ) :
    energy (amp N Z) Y u - energy Z (PhiR N Y) u =
      (1-u) * (Z * defectR N Y).trace.re + u * (Z * defectR N Yᴴ).trace.re := by
  rw [energy_grams, energy_grams]
  simp only [defectR, PhiR_star, Matrix.conjTranspose_conjTranspose, Matrix.mul_sub,
    Matrix.trace_sub, Complex.sub_re]
  rw [Matrix.trace_mul_comm Z (PhiR N _), PhiR_trace_pair,
    Matrix.trace_mul_comm (Y * Yᴴ) (amp N Z),
    Matrix.trace_mul_comm Z (PhiR N _), PhiR_trace_pair,
    Matrix.trace_mul_comm (Yᴴ * Y) (amp N Z)]
  ring

private lemma centered_pair (N : QuantumChannel a b)
    (Y : Matrix (R × b) (R × b) ℂ) (V : Matrix (R × a) (R × a) ℂ)
    (X : Matrix R R ℂ) (hV : partialTraceRight V = 0) :
    (((Y - X ⊗ₖ (1 : Matrix b b ℂ))ᴴ) * amp N V).trace =
      (((PhiR N Y - X ⊗ₖ (1 : Matrix a a ℂ))ᴴ) * V).trace := by
  have hOut : partialTraceRight (amp N V) = 0 := (ptr_amp N V).trans hV
  simp [Matrix.conjTranspose_sub, Matrix.sub_mul, Matrix.trace_sub,
    trace_embed_pair, hV, hOut, PhiR_hs_pair]

private lemma energy_zero_sub {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Z Y W : Matrix ι ι ℂ) (hZ : Z.IsHermitian) :
    energy Z (Y - W) 0 =
      energy Z Y 0 + energy Z W 0 - 2 * (Yᴴ * (Z * W)).trace.re := by
  have h := congrArg Complex.re (Matrix.trace_conjTranspose (Yᴴ * (Z * W)))
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hZ.eq,
    Matrix.trace_conjTranspose, map_star, Complex.star_def, Complex.conj_re] at h
  simp only [energy, arithmetic, sub_zero, one_smul, zero_smul, add_zero,
    Matrix.conjTranspose_sub, Matrix.mul_sub, Matrix.sub_mul, Matrix.trace_sub,
    Complex.sub_re]
  rw [← Matrix.mul_assoc Wᴴ Z Y, h]
  ring

private lemma endpoint_trace_test (N : QuantumChannel a b) (c : ℝ)
    (hN : (act N 1).PosDef) (hc : 0 ≤ c) (hc1 : c < 1)
    (hEnd : EndpointBound N c) : UniversalPositiveTraceTest N (c / (1-c)) := by
  intro R _ _ Y Z hZ
  let S := partialTraceRight Z
  let F := PhiR N Y
  let X := S⁻¹ * partialTraceRight (Z * F)
  let Wa := X ⊗ₖ (1 : Matrix a a ℂ)
  let Wb := X ⊗ₖ (1 : Matrix b b ℂ)
  let K := F - Wa
  let G := Y - Wb
  let V := Z * K
  let a₀ := energy Z K 0
  let d := (Z * defectR N Y).trace.re
  let k := c / (1-c)
  have hu : (0 : ℝ) ∈ Set.Icc 0 1 := by simp
  have hTZ := amp_posDef N hN Z hZ
  have hs : S.PosDef := partialTraceRight_posDef Z hZ
  have hV : partialTraceRight V = 0 := by
    change partialTraceRight (Z * (F - Wa)) = 0
    rw [Matrix.mul_sub, show partialTraceRight (Z * F - Z * Wa) =
        partialTraceRight (Z * F) - partialTraceRight (Z * Wa) by
      simpa only [ptr, one_smul] using ptr_sub_smul 1 (Z * F) (Z * Wa),
      partialTraceRight_mul_embed, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ (Matrix.isUnit_iff_isUnit_det _ |>.mp hs.isUnit), Matrix.one_mul, sub_self]
  have hq : q Z V 0 = a₀ := by
    rw [q_zero_parameter Z V hZ, Matrix.mul_assoc]
    change ((Z*K)ᴴ * (Z⁻¹ * (Z*K))).trace.re = energy Z K 0
    simp only [Matrix.nonsing_inv_mul_cancel_left Z K ((Matrix.isUnit_iff_isUnit_det Z).mp hZ.isUnit),
      energy, arithmetic, sub_zero, one_smul, zero_smul, add_zero]
    rw [Matrix.conjTranspose_mul, hZ.isHermitian.eq, Matrix.mul_assoc]
  have hpair : (Gᴴ * amp N V).trace.re = a₀ := by
    rw [centered_pair N Y V X hV]
    change (Kᴴ * (Z*K)).trace.re = energy Z K 0
    simp only [energy, arithmetic, sub_zero, one_smul, zero_smul, add_zero]
  have hshift : energy (amp N Z) Wb 0 = energy Z Wa 0 := by
    simp only [energy, arithmetic, sub_zero, one_smul, zero_smul, add_zero, Wb, Wa,
      trace_embed_pair, partialTraceRight_mul_embed]
    rw [show partialTraceRight (amp N Z) = S from ptr_amp N Z]
  have hcross : (Yᴴ * (amp N Z * Wb)).trace = (Fᴴ * (Z * Wa)).trace := by
    rw [PhiR_hs_pair, amp_mul_embed]
  have he : energy (amp N Z) G 0 = a₀ + d := by
    have hd := energy_defects N Z Y 0
    simp only [sub_zero, one_mul, zero_mul, add_zero] at hd
    change energy (amp N Z) (Y-Wb) 0 = energy Z (F-Wa) 0 + d
    rw [energy_zero_sub _ Y Wb hTZ.isHermitian, energy_zero_sub _ F Wa hZ.isHermitian]
    linarith only [hd, hshift, congrArg Complex.re hcross]
  have ha : 0 ≤ a₀ := energy_nonneg _ _ _ hZ.posSemidef hu
  have hd : 0 ≤ d := trace_nonneg hZ.posSemidef (defectR_posSemidef N Y)
  have hk : 0 ≤ k := div_nonneg hc (sub_pos.mpr hc1).le
  have hcs := weighted_cauchy (amp N Z) G (amp N V) 0 hTZ hu
  rw [hpair, he] at hcs
  have hEnd' := hEnd Z V hZ hV
  rw [hq] at hEnd'
  have hsquare : a₀ ^ 2 ≤ (a₀ + d) * (c * a₀) :=
    hcs.trans (mul_le_mul_of_nonneg_left hEnd' (add_nonneg ha hd))
  have hab : a₀ ≤ k * d := by
    rcases ha.eq_or_lt with hz | hp
    · rw [← hz]
      exact mul_nonneg hk hd
    · have hcancel : a₀ ≤ (a₀ + d) * c := by
        apply le_of_mul_le_mul_right _ hp
        nlinarith only [hsquare]
      rw [show k * d = (c*d) / (1-c) by dsimp [k]; ring]
      apply (le_div_iff₀ (sub_pos.mpr hc1)).2
      nlinarith only [hcancel]
  let f := fun W : Matrix R R ℂ =>
    (Z * ((F - W ⊗ₖ (1 : Matrix a a ℂ)) *
      (F - W ⊗ₖ (1 : Matrix a a ℂ))ᴴ)).trace.re
  have hbelow : BddBelow (Set.range f) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨W, rfl⟩
    exact trace_nonneg hZ.posSemidef (Matrix.posSemidef_self_mul_conjTranspose _)
  have hcost : f X = a₀ := by
    change f X = energy Z K 0
    rw [energy_grams Z K 0]
    simp [f, K, Wa]
  change sInf (Set.range f) ≤ (Z * ((k : ℂ) • defectR N Y)).trace.re
  calc
    _ ≤ f X := csInf_le hbelow (Set.mem_range_self X)
    _ = a₀ := hcost
    _ ≤ k * d := hab
    _ = _ := by simp [d, Matrix.mul_smul, Matrix.trace_smul, Complex.mul_re]

/-- For every arithmetic parameter, the common-center residual and the
uncentered adjoint give simultaneous estimates of the output inverse form. -/
theorem kernel_contraction (N : QuantumChannel a b) (c : ℝ)
    (hN : (act N 1).PosDef) (hc : c ∈ Set.Icc (0 : ℝ) 1)
    (hEnd : EndpointBound N c)
    (Z V : Matrix (R × a) (R × a) ℂ) (u : ℝ) (hZ : Z.PosDef)
    (hV : partialTraceRight V = 0) (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    q (amp N Z) (amp N V) u ≤ c * q Z V u := by
  let U := amp N V
  let T := amp N Z
  let Y := inverseMatrix T U u
  let F := PhiR N Y
  let p := q Z V u
  let q₀ := q T U u
  let f := energy Z F u
  let d := energy T Y u - f
  have hT : T.PosDef := amp_posDef N hN Z hZ
  have hp : 0 ≤ p := q_nonneg _ _ _ hZ hu
  have hq : 0 ≤ q₀ := q_nonneg _ _ _ hT hu
  have he : energy T Y u = q₀ := (q_eq_energy_inverse T U u hT hu).symm
  have hpair : (Yᴴ * U).trace.re = q₀ := by
    rw [← he, energy, arithmetic_inverseMatrix T U u hT hu]
  have hpairF : (Fᴴ * V).trace.re = q₀ := by
    rw [PhiR_hs_pair, hpair]
  have hcsF := weighted_cauchy Z F V u hZ hu
  rw [hpairF] at hcsF
  change q₀ ^ 2 ≤ f * p at hcsF
  have hd : 0 ≤ d := by
    change 0 ≤ energy T Y u - energy Z (PhiR N Y) u
    rw [energy_defects]
    exact add_nonneg
      (mul_nonneg (sub_nonneg.mpr hu.2) (trace_nonneg hZ.posSemidef (defectR_posSemidef N Y)))
      (mul_nonneg hu.1 (trace_nonneg hZ.posSemidef (defectR_posSemidef N Yᴴ)))
  change q₀ ≤ c * p
  rcases hq.eq_or_lt with hz | hq'
  · rw [← hz]
    exact mul_nonneg hc.1 hp
  rcases hc.2.eq_or_lt with hc1 | hc1
  · rw [hc1, one_mul]
    have hf : f ≤ q₀ := by simpa only [d, he, sub_nonneg] using hd
    apply le_of_mul_le_mul_left _ hq'
    simpa only [pow_two] using hcsF.trans (mul_le_mul_of_nonneg_right hf hp)
  let k := c / (1-c)
  have hk : 0 ≤ k := div_nonneg hc.1 (sub_pos.mpr hc1).le
  obtain ⟨σ,hσ⟩ := common_positive_state_scalarizer N k hk
    (endpoint_trace_test N c hN hc.1 hc1 hEnd)
  let X := stateCenter σ Y
  let Δ := F - X ⊗ₖ (1 : Matrix a a ℂ)
  have hpairΔ : (Δᴴ * V).trace.re = q₀ := by
    rw [← centered_pair N Y V X hV]
    change (((Y - X ⊗ₖ (1 : Matrix b b ℂ))ᴴ) * U).trace.re = _
    simp only [Matrix.conjTranspose_sub, Matrix.sub_mul, Matrix.trace_sub, trace_embed_pair,
      show partialTraceRight U = 0 from (ptr_amp N V).trans hV, Matrix.mul_zero,
      Matrix.trace_zero, sub_zero, hpair]
  obtain ⟨_,hl,hr⟩ := hσ Y
  have hl' := trace_nonneg hZ.posSemidef hl
  have hr' := trace_nonneg hZ.posSemidef hr
  change 0 ≤ (Z * ((k : ℂ) • defectR N Y - Δ * Δᴴ)).trace.re at hl'
  change 0 ≤ (Z * ((k : ℂ) • (PhiR N (Yᴴ * Y) - Fᴴ * F) - Δᴴ * Δ)).trace.re at hr'
  have hright : PhiR N (Yᴴ * Y) - Fᴴ * F = defectR N Yᴴ := by
    simp [defectR, PhiR_star, F]
  rw [hright, trace_sub_gram] at hr'
  rw [trace_sub_gram] at hl'
  have hE : energy Z Δ u ≤ k * d := by
    rw [energy_grams]
    change _ ≤ k * (energy T Y u - energy Z (PhiR N Y) u)
    rw [energy_defects]
    have hL := mul_nonneg (sub_nonneg.mpr hu.2) hl'
    have hR := mul_nonneg hu.1 hr'
    nlinarith only [hL, hR]
  have hcsΔ := weighted_cauchy Z Δ V u hZ hu
  rw [hpairΔ] at hcsΔ
  have hcs' : q₀^2 ≤ (k*d)*p := hcsΔ.trans (mul_le_mul_of_nonneg_right hE hp)
  have hd' : d = q₀ - f := by rw [show d = energy T Y u - f from rfl, he]
  have hdP : d * p ≤ q₀ * p - q₀^2 := by rw [hd']; linarith only [hcsF]
  have hcombine := hcs'.trans (show (k*d)*p ≤ k * (q₀*p - q₀^2) by
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hdP hk)
  have hscaled : (1+k)*q₀ ≤ k*p := by
    apply le_of_mul_le_mul_right _ hq'
    nlinarith only [hcombine]
  have hkEq : (1+k)*c = k := by
    dsimp [k]
    field_simp [ne_of_gt (sub_pos.mpr hc1)]
    ring
  apply le_of_mul_le_mul_left _ (show 0 < 1+k by linarith)
  rwa [← mul_assoc, hkEq]

end Local
end D5.S3.Quantum.Divergence.UmegakiKernelContraction
