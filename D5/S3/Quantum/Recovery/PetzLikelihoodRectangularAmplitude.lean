import D5.S3.Quantum.Recovery.PetzPositiveTracePostselection
import D5.S3.Quantum.Recovery.QuadraticBayesRiskGeometricPetz
import D5.S3.Quantum.Entanglement.TriangleIndependentSourceNoise

/-!
# Rectangular amplitudes for commuting ordinary Petz recovery

The likelihood pieces are positive matrices on the input carrier. The PGM is
formed from their actual images. Its extra outcome is the complement of the
output support, and its trace-dual pullback vanishes on the input support.
The rectangular amplitudes use only the retained outcomes.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius
open D5.S3.Quantum.Foundation.FiniteStateChannel (DensityState)
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf (MatrixMap)
open D5.S3.Quantum.Foundation.FiniteTraceDistance (traceNorm)
open D5.S3.Quantum.Entanglement.TriangleIndependentSourceNoise (LocalPOVM)
open D5.S3.Quantum.Information.PartialTraceMutualInformation (density_posSemidef)
open D5.S3.Quantum.Divergence.SupportAwareRelativeEntropy (SupportContained)
open D5.S3.Quantum.Lieb.SupportPerspectiveTransport
  (spectral_sqrt_normalization support_of_nonneg_le_smul)
open D5.S3.Quantum.Lieb.SupportPerspectiveTransformer (spectral_sqrt_inverse_products)
open D5.S3.Quantum.Recovery.SpectralTransposeRecovery (spectralInverseSqrt spectralSupport)
open PetzPositiveTraceFidelity (fidelityEigenvalues traceDual_unital)
open PetzPositiveTracePostselection (ordinaryPetz)
open PetzPostselectionSpectralJensen (stateMatrix)

namespace PetzLikelihoodRectangularAmplitude

section Rectangular

variable {a ι : Type*} [Fintype a] [Fintype ι]

/-- Horizontally stack square blocks, with columns indexed by outcome and input. -/
def horizontal (X : ι → Matrix a a ℂ) : Matrix a (ι × a) ℂ :=
  Matrix.of fun x column => X column.1 x column.2

private theorem horizontal_mul_adjoint (X Y : ι → Matrix a a ℂ) :
    horizontal X * (horizontal Y)ᴴ = ∑ j, X j * (Y j)ᴴ := by
  apply Matrix.ext
  intro x y
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.sum_apply, horizontal,
    Matrix.of_apply, Fintype.sum_prod_type]

private theorem horizontal_cross_trace (X Y : ι → Matrix a a ℂ) :
    ((horizontal X)ᴴ * horizontal Y).trace = ∑ j, ((X j)ᴴ * Y j).trace := by
  rw [Matrix.trace_mul_comm, horizontal_mul_adjoint, Matrix.trace_sum]
  exact Finset.sum_congr rfl fun j _ => Matrix.trace_mul_comm _ _

private theorem frobenius_eq_one_of_gram_trace {m n : Type*} [Fintype m] [Fintype n]
    (X : Matrix m n ℂ) (hX : (X * Xᴴ).trace = 1) : ‖X‖ = 1 := by
  have hnorm : ‖X‖ ^ 2 = ∑ i, ∑ j, ‖X i j‖ ^ 2 := by
    change ‖WithLp.toLp 2 (fun i => WithLp.toLp 2 (X i))‖ ^ 2 = _
    simp only [PiLp.norm_sq_eq_of_L2]
  have htrace : ((‖X‖ ^ 2 : ℝ) : ℂ) = (Xᴴ * X).trace := by
    rw [hnorm, Complex.ofReal_sum]
    simp_rw [Complex.ofReal_sum]
    simp only [Complex.ofReal_pow, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply, RCLike.star_def, Complex.conj_mul']
    rw [Finset.sum_comm]
  apply (sq_eq_sq₀ (norm_nonneg X) zero_le_one).mp
  have h := congrArg Complex.re htrace
  simpa only [Complex.ofReal_re, Matrix.trace_mul_comm Xᴴ X, hX,
    Complex.one_re, one_pow] using h

end Rectangular

variable {a b ι : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
  [Fintype ι]

set_option linter.unusedDecidableInType false in
private theorem sqrt_adjoint {n : Type*} [Fintype n] [DecidableEq n] (X : Matrix n n ℂ) :
    (CFC.sqrt X)ᴴ = CFC.sqrt X :=
  (CFC.sqrt_nonneg X).posSemidef.isHermitian.eq

/-- A spectral likelihood resolution records the three weights on the same
reference pieces. It allows zero pieces and zero likelihoods. -/
structure LikelihoodResolution (ρ σ : Matrix a a ℂ) (ι : Type*) [Fintype ι] where
  piece : ι → Matrix a a ℂ
  likelihood : ι → ℝ
  piece_pos : ∀ j, (piece j).PosSemidef
  likelihood_nonneg : ∀ j, 0 ≤ likelihood j
  sum_piece : (∑ j, piece j) = σ
  sum_weighted : (∑ j, likelihood j • piece j) = ρ
  sum_sqrt_weighted : (∑ j, Real.sqrt (likelihood j) • piece j) = CFC.sqrt ρ * CFC.sqrt σ

namespace LikelihoodResolution

variable {ρ σ : Matrix a a ℂ} (L : LikelihoodResolution ρ σ ι) (Φ : MatrixMap a b ℂ)

/-- The retained pretty-good effect belonging to one image piece. -/
def retainedEffect (j : ι) : Matrix b b ℂ :=
  let H := spectralInverseSqrt (Φ σ)
  H * Φ (L.piece j) * H

theorem sum_retainedEffect (hΦ : Φ.IsPositive) (hσ : σ.PosSemidef) :
    (∑ j, L.retainedEffect Φ j) = spectralSupport (Φ σ) := by
  obtain ⟨_, _, _, _, _, _, _, hnorm⟩ := spectral_sqrt_normalization (Φ σ) (hΦ hσ)
  simp only [retainedEffect, ← Matrix.sum_mul, ← Matrix.mul_sum, ← map_sum, L.sum_piece]
  exact hnorm

private theorem retainedEffect_pos (hΦ : Φ.IsPositive) (hσ : σ.PosSemidef) (j : ι) :
    (L.retainedEffect Φ j).PosSemidef := by
  obtain ⟨_, hH, _, _, _, _, _, _⟩ := spectral_sqrt_normalization (Φ σ) (hΦ hσ)
  change (spectralInverseSqrt (Φ σ))ᴴ = spectralInverseSqrt (Φ σ) at hH
  simpa only [retainedEffect, hH] using
    (hΦ (L.piece_pos j)).mul_mul_conjTranspose_same (spectralInverseSqrt (Φ σ))

/-- Complete the retained effects to an actual POVM with a separate outcome
for the complement of the output support. -/
def outputPovm (hΦ : Φ.IsPositive) (hσ : σ.PosSemidef) : LocalPOVM b (Option ι) where
  effect := Option.elim' (1 - spectralSupport (Φ σ)) (L.retainedEffect Φ)
  positive j := by
    cases j with
    | none =>
        obtain ⟨_, _, hQ, hQQ, _, _, _, _⟩ := spectral_sqrt_normalization (Φ σ) (hΦ hσ)
        have hproj : IsStarProjection (spectralSupport (Φ σ)) := ⟨hQQ, hQ⟩
        exact hproj.one_sub_nonneg.posSemidef
    | some j => exact L.retainedEffect_pos Φ hΦ hσ j
  complete := by
    rw [Fintype.sum_option]
    change 1 - spectralSupport (Φ σ) + (∑ j, L.retainedEffect Φ j) = 1
    rw [L.sum_retainedEffect Φ hΦ hσ, sub_add_cancel]

/-- Pull back the completed measurement by the actual trace dual. -/
def inputPovm (hΦ : Φ.IsPositive) (hTP : Φ.IsTracePreserving) (hσ : σ.PosSemidef) :
    LocalPOVM a (Option ι) where
  effect j := Φ.dual ((L.outputPovm Φ hΦ hσ).effect j)
  positive j := hΦ.dual ((L.outputPovm Φ hΦ hσ).positive j)
  complete := by
    rw [← map_sum, (L.outputPovm Φ hΦ hσ).complete, traceDual_unital Φ hTP]

/-- The pulled-back effect of a retained outcome. -/
def inputEffect (j : ι) : Matrix a a ℂ :=
  Φ.dual (L.retainedEffect Φ j)

private theorem sum_inputEffect (hΦ : Φ.IsPositive) (hσ : σ.PosSemidef) :
    (∑ j, L.inputEffect Φ j) = Φ.dual (spectralSupport (Φ σ)) := by
  simp only [inputEffect, ← map_sum, L.sum_retainedEffect Φ hΦ hσ]

/-- The retained geometric pair weight, computed by the genuine PGM effect. -/
def geometricWeight (i j : ι) : ℝ :=
  (Φ (L.piece i) * L.retainedEffect Φ j).trace.re

/-- Half the ordered-pair sum counts each off-diagonal geometric loss once. -/
def likelihoodMismatch : ℝ :=
  (∑ i, ∑ j, (Real.sqrt (L.likelihood i) - Real.sqrt (L.likelihood j)) ^ 2 *
    L.geometricWeight Φ i j) / 2

/-- The pairwise mismatch is the geometric risk of the actual image pieces
with square-root likelihood scores. -/
theorem likelihoodMismatch_eq_geometricRisk (hΦ : Φ.IsPositive) :
    L.likelihoodMismatch Φ =
      QuadraticBayesRiskGeometricPetz.geometricRisk (fun i => Φ (L.piece i))
        (fun i => Real.sqrt (L.likelihood i)) := by
  have hsum : (∑ i, Φ (L.piece i)) = Φ σ := by rw [← map_sum, L.sum_piece]
  rw [QuadraticBayesRiskGeometricPetz.geometricRisk_eq_half_pairwise _ _
    (fun i => hΦ (L.piece_pos i))]
  simp only [likelihoodMismatch, QuadraticBayesRiskGeometricPetz.tracePair,
    QuadraticBayesRiskGeometricPetz.pgmEffects, geometricWeight, retainedEffect, hsum]
  ring

/-- The blocks are the square root of the input times the square roots of the
pulled-back effects. -/
def inputAmplitude : Matrix a (ι × a) ℂ :=
  horizontal fun j => CFC.sqrt ρ * CFC.sqrt (L.inputEffect Φ j)

/-- The blocks use the square root of the reference, weighted by the square
root of the input likelihood at the same outcome. -/
def petzAmplitude : Matrix a (ι × a) ℂ :=
  horizontal fun j =>
    Real.sqrt (L.likelihood j) • (CFC.sqrt σ * CFC.sqrt (L.inputEffect Φ j))

private theorem images_supported (hΦ : Φ.IsPositive) (hσ : σ.PosSemidef) (i : ι) :
    spectralSupport (Φ σ) * Φ (L.piece i) = Φ (L.piece i) ∧
    Φ (L.piece i) * spectralSupport (Φ σ) = Φ (L.piece i) := by
  obtain ⟨_, _, hQ, _, _, _, hQq, _⟩ := spectral_sqrt_normalization (Φ σ) (hΦ hσ)
  have hsum : (∑ j, Φ (L.piece j)) = Φ σ := by rw [← map_sum, L.sum_piece]
  have hle : Φ (L.piece i) ≤ Φ σ := by
    rw [← hsum]
    exact Finset.single_le_sum (fun j _ => (hΦ (L.piece_pos j)).nonneg) (Finset.mem_univ i)
  exact support_of_nonneg_le_smul (Φ σ) (Φ (L.piece i)) (spectralSupport (Φ σ))
    hQ hQq (hΦ (L.piece_pos i)) 1 (by simpa only [one_smul] using hle)

omit [Fintype b] [DecidableEq b] in
private theorem weighted_image :
    (∑ j, L.likelihood j • Φ (L.piece j)) = Φ ρ := by
  simp only [← LinearMap.map_smul_of_tower, ← map_sum, L.sum_weighted]

include L in
private theorem image_input_supported (hΦ : Φ.IsPositive) (hσ : σ.PosSemidef) :
    spectralSupport (Φ σ) * Φ ρ = Φ ρ := by
  rw [← L.weighted_image Φ]
  simp only [Matrix.mul_sum, Matrix.mul_smul, fun j => (L.images_supported Φ hΦ hσ j).1]

/-- The positive complement effect annihilates the input square root whenever
the forward image is supported by the output reference. -/
private theorem dual_complement_mul_sqrt (hΦ : Φ.IsPositive) (hσ : σ.PosSemidef)
    {X : Matrix a a ℂ} (hX : X.PosSemidef)
    (hs : spectralSupport (Φ σ) * Φ X = Φ X) :
    Φ.dual (1 - spectralSupport (Φ σ)) * CFC.sqrt X = 0 := by
  let Q := spectralSupport (Φ σ)
  let C := Φ.dual (1 - Q)
  let S := CFC.sqrt X
  obtain ⟨_, _, hQ, hQQ, _, _, _, _⟩ := spectral_sqrt_normalization (Φ σ) (hΦ hσ)
  have hproj : IsStarProjection Q := ⟨hQQ, hQ⟩
  have hC : C.PosSemidef := hΦ.dual hproj.one_sub_nonneg.posSemidef
  have hSC : (S * C * S).PosSemidef := by
    simpa only [show Sᴴ = S from sqrt_adjoint X] using hC.mul_mul_conjTranspose_same S
  have htr : (S * C * S).trace = 0 := by
    calc
      _ = (X * C).trace := by
        rw [Matrix.trace_mul_cycle, CFC.sqrt_mul_sqrt_self X hX.nonneg]
      _ = (Φ X * (1 - Q)).trace := (MatrixMap.Dual.trace_eq Φ X (1 - Q)).symm
      _ = 0 := by
        rw [Matrix.trace_mul_comm, Matrix.sub_mul, Matrix.one_mul, hs, sub_self, Matrix.trace_zero]
  have hzero : S * C * S = 0 := hSC.trace_eq_zero_iff.mp htr
  let D := CFC.sqrt C
  have hDS : D * S = 0 := by
    apply Matrix.conjTranspose_mul_self_eq_zero.mp
    calc
      (D * S)ᴴ * (D * S) = S * (D * D) * S := by
        simp only [Matrix.conjTranspose_mul, D, S, sqrt_adjoint, Matrix.mul_assoc]
      _ = 0 := by rw [CFC.sqrt_mul_sqrt_self C hC.nonneg, hzero]
  change C * S = 0
  rw [← CFC.sqrt_mul_sqrt_self C hC.nonneg, Matrix.mul_assoc, hDS, Matrix.mul_zero]

/-- The retained effects act as the identity on the supported square root. -/
theorem inputSupportCompression (hΦ : Φ.IsPositive) (hTP : Φ.IsTracePreserving)
    (hσ : σ.PosSemidef) {X : Matrix a a ℂ} (hX : X.PosSemidef)
    (hs : spectralSupport (Φ σ) * Φ X = Φ X) :
    (∑ j, L.inputEffect Φ j) * CFC.sqrt X = CFC.sqrt X ∧
      CFC.sqrt X * (∑ j, L.inputEffect Φ j) = CFC.sqrt X := by
  have hc := dual_complement_mul_sqrt Φ hΦ hσ hX hs
  rw [map_sub, traceDual_unital Φ hTP, Matrix.sub_mul, Matrix.one_mul] at hc
  rw [L.sum_inputEffect Φ hΦ hσ]
  have hleft : Φ.dual (spectralSupport (Φ σ)) * CFC.sqrt X = CFC.sqrt X :=
    (sub_eq_zero.mp hc).symm
  obtain ⟨_, _, hQ, hQQ, _, _, _, _⟩ := spectral_sqrt_normalization (Φ σ) (hΦ hσ)
  have hproj : IsStarProjection (spectralSupport (Φ σ)) := ⟨hQQ, hQ⟩
  have hdual := (hΦ.dual hproj.nonneg.posSemidef).isHermitian.eq
  constructor
  · exact hleft
  · simpa only [Matrix.conjTranspose_mul, sqrt_adjoint, hdual] using
      congrArg Matrix.conjTranspose hleft

/-- The retained effects also compress the original reference exactly. -/
theorem referenceSupportCompression (hΦ : Φ.IsPositive) (hTP : Φ.IsTracePreserving)
    (hσ : σ.PosSemidef) :
    (∑ j, L.inputEffect Φ j) * CFC.sqrt σ = CFC.sqrt σ ∧
      CFC.sqrt σ * (∑ j, L.inputEffect Φ j) = CFC.sqrt σ := by
  obtain ⟨_, _, _, _, _, _, hQq, _⟩ := spectral_sqrt_normalization (Φ σ) (hΦ hσ)
  exact L.inputSupportCompression Φ hΦ hTP hσ hσ hQq

/-- The two rectangular left Grams are the physical input and the actual
ordinary Petz image of its forward state. -/
theorem amplitude_grams (hΦ : Φ.IsPositive) (hTP : Φ.IsTracePreserving)
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) :
    L.inputAmplitude Φ * (L.inputAmplitude Φ)ᴴ = ρ ∧
      L.petzAmplitude Φ * (L.petzAmplitude Φ)ᴴ = ordinaryPetz Φ σ (Φ ρ) := by
  let T := CFC.sqrt ρ
  let S := CFC.sqrt σ
  let N := L.inputEffect Φ
  let H := spectralInverseSqrt (Φ σ)
  have hN (j : ι) : (N j).PosSemidef :=
    (L.inputPovm Φ hΦ hTP hσ).positive (some j)
  have hblock (X : Matrix a a ℂ) (j : ι) :
      (X * CFC.sqrt (N j)) * (X * CFC.sqrt (N j))ᴴ = X * N j * Xᴴ := by
    rw [Matrix.conjTranspose_mul, sqrt_adjoint]
    calc
      _ = X * (CFC.sqrt (N j) * CFC.sqrt (N j)) * Xᴴ := by
        simp only [Matrix.mul_assoc]
      _ = _ := by rw [CFC.sqrt_mul_sqrt_self (N j) (hN j).nonneg]
  have hweighted : (∑ j, L.likelihood j • N j) = Φ.dual (H * Φ ρ * H) := by
    calc
      _ = Φ.dual (∑ j, H * (L.likelihood j • Φ (L.piece j)) * H) := by
        simp only [N, inputEffect, retainedEffect, Matrix.mul_smul, Matrix.smul_mul,
          map_sum, LinearMap.map_smul_of_tower, H]
      _ = _ := by rw [← Matrix.sum_mul, ← Matrix.mul_sum, L.weighted_image Φ]
  constructor
  · change horizontal (fun j => T * CFC.sqrt (N j)) *
      (horizontal (fun j => T * CFC.sqrt (N j)))ᴴ = ρ
    rw [horizontal_mul_adjoint]
    simp_rw [hblock]
    rw [← Matrix.sum_mul, ← Matrix.mul_sum, show Tᴴ = T from sqrt_adjoint ρ,
      Matrix.mul_assoc, (L.inputSupportCompression Φ hΦ hTP hσ hρ
        (L.image_input_supported Φ hΦ hσ)).1, CFC.sqrt_mul_sqrt_self ρ hρ.nonneg]
  · change horizontal (fun j => Real.sqrt (L.likelihood j) • (S * CFC.sqrt (N j))) *
      (horizontal (fun j => Real.sqrt (L.likelihood j) • (S * CFC.sqrt (N j))))ᴴ =
        ordinaryPetz Φ σ (Φ ρ)
    rw [horizontal_mul_adjoint]
    have hv (j : ι) :
        (Real.sqrt (L.likelihood j) • (S * CFC.sqrt (N j))) *
          (Real.sqrt (L.likelihood j) • (S * CFC.sqrt (N j)))ᴴ =
        S * (L.likelihood j • N j) * S := by
      simp only [Matrix.conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul,
        smul_smul, Real.mul_self_sqrt (L.likelihood_nonneg j), hblock,
        show Sᴴ = S from sqrt_adjoint σ]
    simp_rw [hv]
    rw [← Matrix.sum_mul, ← Matrix.mul_sum, hweighted]
    rfl

include L in
private theorem ordinaryPetz_trace_one (hΦ : Φ.IsPositive) (hTP : Φ.IsTracePreserving)
    (hσ : σ.PosSemidef) (htr : ρ.trace = 1) :
    (ordinaryPetz Φ σ (Φ ρ)).trace = 1 := by
  let q := Φ σ
  let p := Φ ρ
  let H := spectralInverseSqrt q
  let S := CFC.sqrt σ
  obtain ⟨_, _, _, _, _, _, _, hHqH⟩ := spectral_sqrt_normalization q (hΦ hσ)
  change (S * Φ.dual (H * p * H) * S).trace = 1
  calc
    _ = (σ * Φ.dual (H * p * H)).trace := by
      rw [Matrix.trace_mul_cycle, CFC.sqrt_mul_sqrt_self σ hσ.nonneg]
    _ = (q * (H * p * H)).trace := (MatrixMap.Dual.trace_eq Φ σ (H * p * H)).symm
    _ = ((H * q * H) * p).trace := by
      rw [← Matrix.mul_assoc q (H * p) H, Matrix.trace_mul_cycle q (H * p) H]
      simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hHqH, L.image_input_supported Φ hΦ hσ, hTP ρ, htr]

private theorem weight_trace_nonneg (hΦ : Φ.IsPositive) (hσ : σ.PosSemidef) (i j : ι) :
    0 ≤ (Φ (L.piece i) * L.retainedEffect Φ j).trace :=
  (hΦ (L.piece_pos i)).trace_mul_nonneg (L.retainedEffect_pos Φ hΦ hσ j)

private theorem weight_trace (hΦ : Φ.IsPositive) (hσ : σ.PosSemidef) (i j : ι) :
    (L.geometricWeight Φ i j : ℂ) = (Φ (L.piece i) * L.retainedEffect Φ j).trace := by
  apply Complex.ext
  · exact Complex.ofReal_re _
  · simpa only [Complex.ofReal_im] using
      (Complex.nonneg_iff.mp (L.weight_trace_nonneg Φ hΦ hσ i j)).2

private theorem weight_nonneg (hΦ : Φ.IsPositive) (hσ : σ.PosSemidef) (i j : ι) :
    0 ≤ L.geometricWeight Φ i j :=
  (Complex.nonneg_iff.mp (L.weight_trace_nonneg Φ hΦ hσ i j)).1

/-- The complex cross trace evaluates the products of the input square roots
against the actual pulled-back effects. -/
theorem amplitude_cross_trace_input (hΦ : Φ.IsPositive) (hσ : σ.PosSemidef) :
    ((L.inputAmplitude Φ)ᴴ * L.petzAmplitude Φ).trace =
      ∑ j, Real.sqrt (L.likelihood j) •
        ((CFC.sqrt ρ * CFC.sqrt σ) * L.inputEffect Φ j).trace := by
  unfold inputAmplitude petzAmplitude
  rw [horizontal_cross_trace]
  apply Finset.sum_congr rfl
  intro j _
  let T := CFC.sqrt ρ
  let S := CFC.sqrt σ
  let D := CFC.sqrt (L.inputEffect Φ j)
  have hN : (L.inputEffect Φ j).PosSemidef :=
    hΦ.dual (L.retainedEffect_pos Φ hΦ hσ j)
  change ((T * D)ᴴ * (Real.sqrt (L.likelihood j) • (S * D))).trace =
    Real.sqrt (L.likelihood j) • ((T * S) * L.inputEffect Φ j).trace
  simp only [Matrix.mul_smul, Matrix.conjTranspose_mul, Matrix.trace_smul,
    show Dᴴ = D from sqrt_adjoint (L.inputEffect Φ j), show Tᴴ = T from sqrt_adjoint ρ]
  congr 1
  calc
    _ = (D * ((T * S) * D)).trace := by simp only [Matrix.mul_assoc]
    _ = (((T * S) * D) * D).trace := Matrix.trace_mul_comm _ _
    _ = _ := by
      rw [Matrix.mul_assoc, CFC.sqrt_mul_sqrt_self (L.inputEffect Φ j) hN.nonneg]

private theorem amplitude_cross_trace_weights (hΦ : Φ.IsPositive) (hσ : σ.PosSemidef) :
    ((L.inputAmplitude Φ)ᴴ * L.petzAmplitude Φ).trace =
      ∑ i, ∑ j, ((Real.sqrt (L.likelihood i) * Real.sqrt (L.likelihood j) *
        L.geometricWeight Φ i j : ℝ) : ℂ) := by
  calc
    _ = ∑ j, Real.sqrt (L.likelihood j) •
        ((CFC.sqrt ρ * CFC.sqrt σ) * L.inputEffect Φ j).trace :=
      L.amplitude_cross_trace_input Φ hΦ hσ
    _ = ∑ j, ∑ i, ((Real.sqrt (L.likelihood i) * Real.sqrt (L.likelihood j) *
        L.geometricWeight Φ i j : ℝ) : ℂ) := by
      rw [← L.sum_sqrt_weighted]
      simp only [Matrix.sum_mul, Matrix.smul_mul, Matrix.trace_sum, Matrix.trace_smul,
        Finset.smul_sum, inputEffect]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro i _
      rw [← MatrixMap.Dual.trace_eq Φ (L.piece i) (L.retainedEffect Φ j),
        ← L.weight_trace Φ hΦ hσ i j]
      simp only [Complex.real_smul, Complex.ofReal_mul]
      ring
    _ = _ := Finset.sum_comm

/-- The overlap is real and equals one minus the geometric likelihood loss. -/
theorem amplitude_cross_trace (hΦ : Φ.IsPositive) (hTP : Φ.IsTracePreserving)
    (hσ : σ.PosSemidef) (htr : ρ.trace = 1) :
    ((L.inputAmplitude Φ)ᴴ * L.petzAmplitude Φ).trace =
      ((1 - L.likelihoodMismatch Φ : ℝ) : ℂ) := by
  let s := fun i => Real.sqrt (L.likelihood i)
  let A := fun i => Φ (L.piece i)
  let B := QuadraticBayesRiskGeometricPetz.scoreMoment A s
  let H := spectralInverseSqrt (Φ σ)
  let overlap := ∑ i, ∑ j, s i * s j * L.geometricWeight Φ i j
  have henergy : (∑ i, L.likelihood i * (Φ (L.piece i)).trace.re) = 1 := by
    have h := congrArg (fun X : Matrix b b ℂ => X.trace.re) (L.weighted_image Φ)
    simpa only [Matrix.trace_sum, Matrix.trace_smul, Complex.re_sum, Complex.real_smul,
      Complex.re_ofReal_mul, hTP ρ, htr, Complex.one_re] using h
  have htrace : QuadraticBayesRiskGeometricPetz.tracePair B (H * B * H) = overlap := by
    change (((∑ i, s i • A i) * (H * (∑ j, s j • A j) * H)).trace).re = overlap
    rw [Matrix.sum_mul]
    simp only [Matrix.smul_mul, Matrix.sum_mul, Matrix.mul_smul,
      Matrix.trace_sum, Matrix.trace_smul, Complex.re_sum, Complex.real_smul,
      Complex.re_ofReal_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    simp only [geometricWeight, retainedEffect, A, H, Matrix.mul_assoc]
    ring
  have hJ : L.likelihoodMismatch Φ = 1 - overlap := by
    have hsum : (∑ i, A i) = Φ σ := by
      change (∑ i, Φ (L.piece i)) = Φ σ
      rw [← map_sum, L.sum_piece]
    have hsq (i : ι) : s i ^ 2 = L.likelihood i := Real.sq_sqrt (L.likelihood_nonneg i)
    rw [L.likelihoodMismatch_eq_geometricRisk Φ hΦ]
    change (∑ i, s i ^ 2 * (A i).trace.re) -
      QuadraticBayesRiskGeometricPetz.tracePair B
        (spectralInverseSqrt (∑ i, A i) * B * spectralInverseSqrt (∑ i, A i)) =
      1 - overlap
    simp only [hsq, A] at henergy ⊢
    rw [show (∑ i, Φ (L.piece i)) = Φ σ from hsum, henergy, htrace]
  rw [L.amplitude_cross_trace_weights Φ hΦ hσ, hJ]
  simp only [← Complex.ofReal_sum]
  change (overlap : ℂ) = ((1 - (1 - overlap) : ℝ) : ℂ)
  congr 1
  ring

/-- The geometric likelihood mismatch is between zero and one. -/
theorem likelihoodMismatch_bounds (hΦ : Φ.IsPositive) (hTP : Φ.IsTracePreserving)
    (hσ : σ.PosSemidef) (htr : ρ.trace = 1) :
    0 ≤ L.likelihoodMismatch Φ ∧ L.likelihoodMismatch Φ ≤ 1 := by
  constructor
  · exact div_nonneg (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      mul_nonneg (sq_nonneg _) (L.weight_nonneg Φ hΦ hσ i j)) (by norm_num)
  · have h := congrArg Complex.re (L.amplitude_cross_trace Φ hΦ hTP hσ htr)
    rw [L.amplitude_cross_trace_weights Φ hΦ hσ] at h
    simp only [Complex.re_sum, Complex.ofReal_re] at h
    have hn : 0 ≤ ∑ i, ∑ j, Real.sqrt (L.likelihood i) * Real.sqrt (L.likelihood j) *
        L.geometricWeight Φ i j :=
      Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
        mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
          (L.weight_nonneg Φ hΦ hσ i j)
    rw [h] at hn
    exact sub_nonneg.mp hn

/-- The rectangular Schatten bound applied to the two physical Grams. -/
theorem traceNorm_sub_ordinaryPetz_sq_le (hΦ : Φ.IsPositive)
    (hTP : Φ.IsTracePreserving) (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    (htr : ρ.trace = 1) :
    traceNorm (ρ - ordinaryPetz Φ σ (Φ ρ)) ^ 2 ≤
      4 * (2 * L.likelihoodMismatch Φ - (L.likelihoodMismatch Φ) ^ 2) := by
  obtain ⟨hU, hV⟩ := L.amplitude_grams Φ hΦ hTP hρ hσ
  have hnU := frobenius_eq_one_of_gram_trace (L.inputAmplitude Φ) (by rw [hU, htr])
  have hnV := frobenius_eq_one_of_gram_trace (L.petzAmplitude Φ)
    (by rw [hV, L.ordinaryPetz_trace_one Φ hΦ hTP hσ htr])
  have h := PetzPostselectedReference.traceNorm_gram_sub_sq_le
    (L.inputAmplitude Φ) (L.petzAmplitude Φ) hnU hnV
  rw [hU, hV, L.amplitude_cross_trace Φ hΦ hTP hσ htr, Complex.ofReal_re] at h
  calc
    _ ≤ 4 * (1 - (1 - L.likelihoodMismatch Φ) ^ 2) := h
    _ = _ := by ring

end LikelihoodResolution

section CommutingInputs

/-- The input likelihood operator, with the inverse root zero on the
kernel of the reference. -/
def likelihoodOperator (ρ σ : DensityState a) : Matrix a a ℂ :=
  let H := spectralInverseSqrt (stateMatrix σ)
  H * stateMatrix ρ * H

private theorem likelihoodOperator_pos (ρ σ : DensityState a) :
    (likelihoodOperator ρ σ).PosSemidef := by
  let H := spectralInverseSqrt (stateMatrix σ)
  obtain ⟨_, hH, _, _, _, _, _, _⟩ :=
    spectral_sqrt_normalization (stateMatrix σ) (density_posSemidef σ)
  change Hᴴ = H at hH
  change (H * stateMatrix ρ * H).PosSemidef
  simpa only [hH] using (density_posSemidef ρ).mul_mul_conjTranspose_same H

/-- The distinct spectral likelihood values on the original carrier. A zero
value arising solely from the kernel of the reference has a zero piece. -/
abbrev LikelihoodValues (ρ σ : DensityState a) :=
  ↥(fidelityEigenvalues (likelihoodOperator_pos ρ σ).isHermitian)

private def indicator (k x : ℝ) : ℝ := by
  classical
  exact if x = k then 1 else 0

private theorem sum_spectral_indicators (K : Matrix a a ℂ) (hK : K.IsHermitian)
    (f : ℝ → ℝ) :
    (∑ j : ↥(fidelityEigenvalues hK), f j.val • cfc (indicator j.val) K) = cfc f K := by
  classical
  let g : ↥(fidelityEigenvalues hK) → ℝ → ℝ := fun j x => f j.val * indicator j.val x
  calc
    _ = ∑ j, cfc (g j) K := by
      apply Finset.sum_congr rfl
      intro j _
      exact (cfc_const_mul (f j.val) (indicator j.val) K
        (K.finite_real_spectrum.continuousOn _)).symm
    _ = cfc (∑ j, g j) K :=
      (cfc_sum_univ g K (fun j => K.finite_real_spectrum.continuousOn (g j))).symm
    _ = cfc f K := by
      apply cfc_congr
      intro x hx
      have hm : x ∈ fidelityEigenvalues hK := by
        rw [hK.spectrum_real_eq_range_eigenvalues] at hx
        obtain ⟨j, rfl⟩ := hx
        exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
      let i : ↥(fidelityEigenvalues hK) := ⟨x, hm⟩
      rw [Finset.sum_apply, Finset.sum_eq_single i]
      · simp [g, indicator, i]
      · intro j _ hji
        have hne : x ≠ j.val := fun he => hji (Subtype.ext he.symm)
        simp [g, indicator, hne]
      · simp

private theorem support_mul_input (ρ σ : DensityState a) (hSupp : SupportContained ρ σ) :
    spectralSupport (stateMatrix σ) * stateMatrix ρ = stateMatrix ρ ∧
      stateMatrix ρ * spectralSupport (stateMatrix σ) = stateMatrix ρ := by
  let P := spectralSupport (stateMatrix σ)
  obtain ⟨_, _, hP, _, _, _, hPσ, _⟩ :=
    spectral_sqrt_normalization (stateMatrix σ) (density_posSemidef σ)
  change Pᴴ = P at hP
  change P * stateMatrix σ = stateMatrix σ at hPσ
  have hσP : stateMatrix σ * P = stateMatrix σ := by
    simpa only [Matrix.conjTranspose_mul, hP, (density_posSemidef σ).isHermitian.eq] using
      congrArg Matrix.conjTranspose hPσ
  have hσker : stateMatrix σ * (1 - P) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, hσP, sub_self]
  have hρker : stateMatrix ρ * (1 - P) = 0 := by
    apply Matrix.ext
    intro i j
    let v : a → ℂ := fun k => (1 - P) k j
    have hv : stateMatrix σ *ᵥ v = 0 := by
      funext k
      simpa only [Matrix.mulVec, dotProduct, v, Matrix.mul_apply, Matrix.zero_apply,
        Pi.zero_apply] using congrArg (fun X : Matrix a a ℂ => X k j) hσker
    have hvρ : stateMatrix ρ *ᵥ v = 0 := hSupp hv
    simpa only [Matrix.mulVec, dotProduct, v, Matrix.mul_apply, Matrix.zero_apply,
      Pi.zero_apply] using congrFun hvρ i
  rw [Matrix.mul_sub, Matrix.mul_one] at hρker
  have hρP : stateMatrix ρ * P = stateMatrix ρ := (sub_eq_zero.mp hρker).symm
  constructor
  · simpa only [Matrix.conjTranspose_mul, hP, (density_posSemidef ρ).isHermitian.eq] using
      congrArg Matrix.conjTranspose hρP
  · exact hρP

private theorem sqrt_eq_real_cfc {X : Matrix a a ℂ} (hX : X.PosSemidef) :
    CFC.sqrt X = cfc Real.sqrt X := by
  rw [CFC.sqrt_eq_real_sqrt X hX.nonneg,
    cfcₙ_eq_cfc (f := Real.sqrt) (a := X) (hf0 := by simp)]

/-- Resolve the commuting input into the positive pieces
sqrt(σ) Pⱼ sqrt(σ) of its actual supported likelihood operator. -/
def commutingResolution (ρ σ : DensityState a)
    (hComm : Commute (stateMatrix ρ) (stateMatrix σ)) (hSupp : SupportContained ρ σ) :
    LikelihoodResolution (stateMatrix ρ) (stateMatrix σ) (LikelihoodValues ρ σ) := by
  let S := CFC.sqrt (stateMatrix σ)
  let H := spectralInverseSqrt (stateMatrix σ)
  let K := likelihoodOperator ρ σ
  have hσ := density_posSemidef σ
  have hK : K.PosSemidef := likelihoodOperator_pos ρ σ
  let E : LikelihoodValues ρ σ → Matrix a a ℂ := fun j => cfc (indicator j.val) K
  let T : LikelihoodValues ρ σ → Matrix a a ℂ := fun j => S * E j * S
  have hS : Sᴴ = S := sqrt_adjoint (stateMatrix σ)
  have hE (j : LikelihoodValues ρ σ) : (E j).PosSemidef := by
    classical
    apply Matrix.nonneg_iff_posSemidef.mp
    apply cfc_nonneg
    intro x _
    by_cases hx : x = j.val <;> simp [indicator, hx]
  have hvalue (j : LikelihoodValues ρ σ) : 0 ≤ j.val := by
    classical
    have hm := j.property
    change j.val ∈ fidelityEigenvalues hK.isHermitian at hm
    change j.val ∈ Finset.univ.image hK.isHermitian.eigenvalues at hm
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hm
    rw [← hi]
    exact hK.eigenvalues_nonneg i
  have hdecomp (f : ℝ → ℝ) : (∑ j, f j.val • T j) = S * cfc f K * S := by
    have hsum : (∑ j : LikelihoodValues ρ σ, f j.val • E j) = cfc f K :=
      sum_spectral_indicators K hK.isHermitian f
    have hterm (j : LikelihoodValues ρ σ) : f j.val • T j = S * (f j.val • E j) * S := by
      simp only [T, Matrix.mul_smul, Matrix.smul_mul]
    simp_rw [hterm]
    rw [← Matrix.sum_mul, ← Matrix.mul_sum, hsum]
  have hroots := spectral_sqrt_inverse_products (stateMatrix σ) hσ
  have hsupport := support_mul_input ρ σ hSupp
  have hSKS : S * K * S = stateMatrix ρ := by
    calc
      _ = (S * H) * stateMatrix ρ * (H * S) := by
        dsimp only [K, likelihoodOperator, H]
        simp only [Matrix.mul_assoc]
      _ = _ := by rw [hroots.1, hroots.2.1, hsupport.1, hsupport.2]
  have hSK : Commute S K := by
    have hSρ : Commute S (stateMatrix ρ) := by
      change Commute (CFC.sqrt (stateMatrix σ)) (stateMatrix ρ)
      rw [sqrt_eq_real_cfc hσ]
      exact hComm.symm.cfc_real _
    have hSH' : Commute S H := by
      change Commute (CFC.sqrt (stateMatrix σ))
        (cfc (fun x : ℝ => (Real.sqrt x)⁻¹) (stateMatrix σ))
      rw [sqrt_eq_real_cfc hσ]
      exact cfc_commute_cfc _ _ _
    exact (hSH'.mul_right hSρ).mul_right hSH'
  let D := CFC.sqrt K
  have hSD : Commute S D := by
    change Commute S (CFC.sqrt K)
    rw [sqrt_eq_real_cfc hK]
    exact (hSK.symm.cfc_real _).symm
  have hsquare : (S * D) * (S * D) = stateMatrix ρ := by
    calc
      _ = S * (D * (S * D)) := by simp only [Matrix.mul_assoc]
      _ = S * (D * (D * S)) := by rw [hSD.eq]
      _ = S * K * S := by
        rw [← Matrix.mul_assoc D D S, CFC.sqrt_mul_sqrt_self K hK.nonneg, Matrix.mul_assoc]
      _ = _ := hSKS
  have hρsqrt : CFC.sqrt (stateMatrix ρ) = S * D :=
    CFC.sqrt_unique hsquare (Commute.mul_nonneg (CFC.sqrt_nonneg _) (CFC.sqrt_nonneg _) hSD)
  have hpiece (j : LikelihoodValues ρ σ) : (T j).PosSemidef := by
    simpa only [T, hS] using (hE j).mul_mul_conjTranspose_same S
  have hsum : (∑ j, T j) = stateMatrix σ := by
    have hSS : S * S = stateMatrix σ := CFC.sqrt_mul_sqrt_self (stateMatrix σ) hσ.nonneg
    simpa only [one_smul, cfc_const_one ℝ K hK.isHermitian.isSelfAdjoint, Matrix.mul_one, hSS] using
      hdecomp (fun _ => (1 : ℝ))
  have hweighted : (∑ j, j.val • T j) = stateMatrix ρ := by
    simpa only [cfc_id' ℝ K hK.isHermitian.isSelfAdjoint, hSKS] using
      hdecomp (fun x : ℝ => x)
  have hrootWeighted : (∑ j, Real.sqrt j.val • T j) = CFC.sqrt (stateMatrix ρ) * S := by
    rw [hρsqrt]
    simpa only [← sqrt_eq_real_cfc hK] using hdecomp Real.sqrt
  exact ⟨T, fun j => j.val, hpiece, hvalue, hsum, hweighted, hrootWeighted⟩

/-- The supported commuting-input ordinary Petz error in terms of the actual
geometric mismatch of the image likelihood pieces. -/
theorem traceNorm_sub_ordinaryPetz_sq_le_of_commute
    (ρ σ : DensityState a) (hComm : Commute (stateMatrix ρ) (stateMatrix σ))
    (hSupp : SupportContained ρ σ) (Φ : MatrixMap a b ℂ) (hΦ : Φ.IsPositive)
    (hTP : Φ.IsTracePreserving) :
    let J := (commutingResolution ρ σ hComm hSupp).likelihoodMismatch Φ
    traceNorm (stateMatrix ρ - ordinaryPetz Φ (stateMatrix σ) (Φ (stateMatrix ρ))) ^ 2 ≤
      4 * (2 * J - J ^ 2) :=
  (commutingResolution ρ σ hComm hSupp).traceNorm_sub_ordinaryPetz_sq_le Φ hΦ hTP
    (density_posSemidef ρ) (density_posSemidef σ) ρ.2.2

end CommutingInputs

end PetzLikelihoodRectangularAmplitude
