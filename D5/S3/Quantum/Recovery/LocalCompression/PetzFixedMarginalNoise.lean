/- GID: D5/S3/Quantum/Recovery/LocalCompression/PetzFixedMarginalNoise
   generality: I
   mirror-B: D5/B/S3/Quantum/Recovery/LocalCompression/PetzFixedMarginalNoise
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Fixed-marginal noise makes the Petz reference faithful and preserves strict scores. -/

/-
escape_witness: finiteTraceLog_uniform_product and noise_loss_contract.
The supported block decomposition scales each block by the inverse environment
cardinality. Its exact entropy is used in the mixture inequality after both
retained marginals have been identified. The strict-score theorem then uses the
fixed Petz middle factor and right continuity to choose a positive weight.
-/

import D5.S3.Quantum.Divergence.SupportedTraceLog
import D5.S3.Quantum.Divergence.UmegakiSupportedNoise
import D5.S3.Quantum.Recovery.BKMFlagRefinementPetz
import D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity

/-!
# Marginal-preserving environmental noise for ordinary Petz recovery

Both inputs retain their original `R` marginal. The replacement state is the
product of that marginal and the normalized identity on `E`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Matrix Filter
open scoped BigOperators Topology CStarAlgebra ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator
open D5.S3.Quantum.Foundation.FiniteStateChannel (DensityState)
open D5.S3.Quantum.Foundation.FiniteTraceDistance (traceNorm)
open D5.S3.Quantum.Information.PartialTraceMutualInformation
  (partialTraceRight partialTraceRight_add partialTraceRight_kronecker marginalRight
    marginalRight_productState productState density_posSemidef)
open D5.S3.Quantum.Divergence.SupportAwareRelativeEntropy
open D5.S3.Quantum.Divergence.SupportedTraceLog (traceLog_jointConvex)
open D5.S3.Quantum.Divergence.UmegakiSupportedNoise (tendsto_finiteTraceLogRelativeEntropy_of_noise)
open D5.S3.Quantum.Divergence.CanonicalChannelDPI (extended_quantum_relative_entropy_channel_dpi)
open D5.S3.Quantum.Divergence.FannesRootFidelityHolevo (exists_eraseChannel)
open D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction (partialTraceRight_smul)
open D5.S3.Quantum.Recovery.BKMFlagRefinement (joint lift lift_eq_joint cfc_joint partialTracePetz
    relativeEntropyOfMatrices)
open D5.S3.Quantum.Matrix.SpectralPower (mpow)

namespace D5.S3.Quantum.Recovery.LocalCompression.PetzFixedMarginalNoise

universe u

section MatrixEntropy
variable {n : Type u} [Fintype n] [DecidableEq n]

private abbrev raw (X : DensityState n) : Matrix n n ℂ :=
  CStarMatrix.ofMatrix.symm X.1

private lemma finiteTraceLog_eq_raw (X Y : DensityState n) :
    finiteTraceLogRelativeEntropy X Y = relativeEntropyOfMatrices (raw X) (raw Y) := by
  have mapLog (A : Matrix n n ℂ) (hA : A.IsHermitian) :
      CStarMatrix.ofMatrix (CFC.log A) = CFC.log (CStarMatrix.ofMatrix A) :=
    StarAlgHomClass.map_cfc CStarMatrix.ofMatrixStarAlgEquiv Real.log A
      (A.finite_real_spectrum.continuousOn _) CStarMatrix.ofMatrixL.continuous
      hA.isSelfAdjoint hA.isSelfAdjoint
  change (CStarMatrix.ofMatrix (raw X) * (CFC.log (CStarMatrix.ofMatrix (raw X)) -
    CFC.log (CStarMatrix.ofMatrix (raw Y))) : CStarMatrix n n ℂ).trace.re = _
  rw [← mapLog _ (density_posSemidef X).isHermitian,
    ← mapLog _ (density_posSemidef Y).isHermitian] <;> rfl

/-- Homogeneity on supported PSD pairs, via the singleton case of joint convexity
in both directions. This includes a singular numerator. -/
private lemma traceLog_smul_same (S T : Matrix n n ℂ)
    (hS : S.PosSemidef) (hT : T.PosSemidef)
    (hST : ∀ x, T *ᵥ x = 0 → S *ᵥ x = 0) {a : ℝ} (ha : 0 < a) :
    relativeEntropyOfMatrices (a • S) (a • T) = a * relativeEntropyOfMatrices S T := by
  have hscale (b : ℝ) (hb : 0 ≤ b) (U V : Matrix n n ℂ)
      (hU : U.PosSemidef) (hV : V.PosSemidef)
      (hUV : ∀ x, V *ᵥ x = 0 → U *ᵥ x = 0) :
      relativeEntropyOfMatrices (b • U) (b • V) ≤ b * relativeEntropyOfMatrices U V := by
    have h := traceLog_jointConvex (fun _ : Unit => b) (fun _ => U) (fun _ => V)
      (fun _ => hb) (fun _ => hU) (fun _ => hV) (fun _ => hUV)
    simpa [relativeEntropyOfMatrices] using h
  apply le_antisymm (hscale a ha.le S T hS hT hST)
  have hscaled : ∀ x, (a • T) *ᵥ x = 0 → (a • S) *ᵥ x = 0 := by
    intro x hx
    rw [Matrix.smul_mulVec] at hx ⊢
    rw [hST x ((smul_eq_zero.mp hx).resolve_left ha.ne'), smul_zero]
  have h := hscale a⁻¹ (inv_nonneg.mpr ha.le) (a • S) (a • T)
    (hS.smul ha.le) (hT.smul ha.le) hscaled
  simp only [smul_smul, inv_mul_cancel₀ ha.ne', one_smul] at h
  have h' := mul_le_mul_of_nonneg_left h ha.le
  rwa [← mul_assoc, mul_inv_cancel₀ ha.ne', one_mul] at h'

/-- The two weights of environmental noise are the two entries of a supported
joint-convexity inequality. Neither reference in the original pair need be PD. -/
private lemma traceLog_mix_le (S T U V : Matrix n n ℂ)
    (hS : S.PosSemidef) (hT : T.PosSemidef) (hU : U.PosSemidef) (hV : V.PosSemidef)
    (hST : ∀ x, T *ᵥ x = 0 → S *ᵥ x = 0)
    (hUV : ∀ x, V *ᵥ x = 0 → U *ᵥ x = 0)
    {e : ℝ} (he : e ∈ Set.Icc (0 : ℝ) 1) :
    relativeEntropyOfMatrices ((1-e) • S + e • U) ((1-e) • T + e • V) ≤
      (1-e) * relativeEntropyOfMatrices S T + e * relativeEntropyOfMatrices U V := by
  let w : Bool → ℝ := fun b => if b then e else 1-e
  let A : Bool → Matrix n n ℂ := fun b => if b then U else S
  let B : Bool → Matrix n n ℂ := fun b => if b then V else T
  have hw (i : Bool) : 0 ≤ w i := by cases i <;> simp [w, he.1, sub_nonneg.mpr he.2]
  have hA (i : Bool) : (A i).PosSemidef := by cases i <;> simp [A, hS, hU]
  have hB (i : Bool) : (B i).PosSemidef := by cases i <;> simp [B, hT, hV]
  have hs (i : Bool) (x : n → ℂ) : B i *ᵥ x = 0 → A i *ᵥ x = 0 := by
    cases i
    · exact hST x
    · exact hUV x
  have h := traceLog_jointConvex w A B hw hA hB hs
  simpa [relativeEntropyOfMatrices, Fintype.sum_bool, w, A, B, add_comm] using h

end MatrixEntropy

section Environment
variable {R E : Type u} [Fintype R] [DecidableEq R] [Nonempty R]
  [Fintype E] [DecidableEq E] [Nonempty E]

private lemma envCard_pos : 0 < (Fintype.card E : ℝ) :=
  Nat.cast_pos.mpr Fintype.card_pos

/-- The normalized identity on the environment. -/
def environmentUniform (E : Type u) [Fintype E] [DecidableEq E] [Nonempty E] :
    DensityState E := by
  let U : Matrix E E ℂ := (Fintype.card E : ℝ)⁻¹ • 1
  have hU : U.PosSemidef := Matrix.PosSemidef.one.smul (inv_nonneg.mpr (envCard_pos (E := E)).le)
  refine ⟨CStarMatrix.ofMatrix U, map_nonneg CStarMatrix.ofMatrixStarAlgEquiv hU.nonneg, ?_⟩
  change U.trace = 1
  rw [show U = (Fintype.card E : ℝ)⁻¹ • 1 from rfl,
    Matrix.trace_smul, Matrix.trace_one, Complex.real_smul]
  exact_mod_cast (inv_mul_cancel₀ (envCard_pos (E := E)).ne')

private lemma environmentUniform_posDef : (raw (environmentUniform E)).PosDef :=
  Matrix.PosDef.one.smul (inv_pos.mpr (envCard_pos (E := E)))

/-- Replace E with its uniform state while retaining the actual R marginal. -/
def replacement (X : DensityState (R × E)) : DensityState (R × E) :=
  productState (marginalRight X) (environmentUniform E)

/-- The action on matrices, including Hermitian tangent directions. -/
def replacementMatrix (X : Matrix (R × E) (R × E) ℂ) : Matrix (R × E) (R × E) ℂ :=
  partialTraceRight X ⊗ₖ raw (environmentUniform E)

@[simp] private theorem raw_replacement (X : DensityState (R × E)) :
    raw (replacement X) = replacementMatrix (raw X) := rfl

@[simp] private theorem partialTrace_replacementMatrix (X : Matrix (R × E) (R × E) ℂ) :
    partialTraceRight (replacementMatrix X) = partialTraceRight X := by
  change partialTraceRight
    (Matrix.kronecker (partialTraceRight X) (raw (environmentUniform E))) = partialTraceRight X
  exact (partialTraceRight_kronecker _ _).trans (by
    rw [show (raw (environmentUniform E)).trace = 1 from (environmentUniform E).2.2, one_smul])

/-- The environmental replacement of a state with a faithful actual marginal
is faithful, even when the original joint state is singular. -/
private theorem replacement_posDef (X : DensityState (R × E))
    (hX : (partialTraceRight (raw X)).PosDef) : (raw (replacement X)).PosDef := by
  rw [raw_replacement, replacementMatrix]
  exact hX.kronecker (environmentUniform_posDef (E := E))

private lemma uniform_product_block (S : Matrix R R ℂ) :
    S ⊗ₖ raw (environmentUniform E) =
      joint (fun _ : E => (Fintype.card E : ℝ)⁻¹ • S) := by
  change S ⊗ₖ ((Fintype.card E : ℝ)⁻¹ • (1 : Matrix E E ℂ)) = _
  rw [Matrix.kronecker_smul, ← Matrix.smul_kronecker]
  exact lift_eq_joint ((Fintype.card E : ℝ)⁻¹ • S)

/-- Exact product entropy observation. The same normalized identity is appended
on both sides. Support inclusion handles zero source eigenvalues and singular
references. -/
private theorem finiteTraceLog_uniform_product (X Y : DensityState R) (hXY : SupportContained X Y) :
    finiteTraceLogRelativeEntropy (productState X (environmentUniform E))
      (productState Y (environmentUniform E)) = finiteTraceLogRelativeEntropy X Y := by
  let a : ℝ := (Fintype.card E : ℝ)⁻¹
  have ha : 0 < a := inv_pos.mpr (envCard_pos (E := E))
  rw [finiteTraceLog_eq_raw, finiteTraceLog_eq_raw]
  change relativeEntropyOfMatrices (raw X ⊗ₖ raw (environmentUniform E))
    (raw Y ⊗ₖ raw (environmentUniform E)) = relativeEntropyOfMatrices (raw X) (raw Y)
  rw [uniform_product_block, uniform_product_block]
  let A : E → Matrix R R ℂ := fun _ => a • raw X
  let B : E → Matrix R R ℂ := fun _ => a • raw Y
  change relativeEntropyOfMatrices (joint A) (joint B) = _
  have hA (i : E) : (A i).IsHermitian := ((density_posSemidef X).smul ha.le).isHermitian
  have hB (i : E) : (B i).IsHermitian := ((density_posSemidef Y).smul ha.le).isHermitian
  have hb : relativeEntropyOfMatrices (joint A) (joint B) = ∑ i : E, relativeEntropyOfMatrices (A i) (B i) := by
    unfold relativeEntropyOfMatrices CFC.log
    rw [cfc_joint _ A hA, cfc_joint _ B hB]
    simp only [joint, ← Matrix.blockDiagonal_sub, ← Matrix.blockDiagonal_mul,
      Matrix.trace_blockDiagonal, Complex.re_sum] <;> rfl
  rw [hb]
  have hscale := traceLog_smul_same (raw X) (raw Y) (density_posSemidef X)
    (density_posSemidef Y) (fun x hx => hXY hx) ha
  change (∑ _ : E, relativeEntropyOfMatrices (a • raw X) (a • raw Y)) = _
  simp only [hscale, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  change (Fintype.card E : ℝ) * ((Fintype.card E : ℝ)⁻¹ * relativeEntropyOfMatrices (raw X) (raw Y)) = _
  rw [← mul_assoc, mul_inv_cancel₀ (envCard_pos (E := E)).ne', one_mul]

private def noiseWithEnvironment (X : DensityState (R × E)) (e : ℝ) : DensityState (R × E) :=
  if he : e ∈ Set.Icc (0 : ℝ) 1 then
    ⟨CStarMatrix.ofMatrix ((1-e) • raw X + e • raw (replacement X)),
      map_nonneg CStarMatrix.ofMatrixStarAlgEquiv
        (((density_posSemidef X).smul (sub_nonneg.mpr he.2)).add
          ((density_posSemidef (replacement X)).smul he.1)).nonneg,
      by
        change (((1-e) • raw X + e • raw (replacement X)).trace) = 1
        rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul,
          show (raw X).trace = 1 from X.2.2,
          show (raw (replacement X)).trace = 1 from (replacement X).2.2,
          Complex.real_smul, Complex.real_smul, mul_one, mul_one]
        exact_mod_cast (show (1-e) + e = (1 : ℝ) by ring)⟩
  else X

open scoped Classical in
/-- Environmental noise on the closed unit interval. Outside the interval the
path is constant. An empty environment cannot carry a joint density state. -/
def noise (X : DensityState (R × E)) (e : ℝ) : DensityState (R × E) :=
  if h : Nonempty E then
    letI := h
    noiseWithEnvironment X e
  else X

/-- The affine map on all matrices, applicable to tangent directions as well. -/
def noiseMatrix (e : ℝ) (X : Matrix (R × E) (R × E) ℂ) : Matrix (R × E) (R × E) ℂ :=
  (1-e) • X + e • replacementMatrix X

@[simp] private theorem raw_noise (X : DensityState (R × E)) {e : ℝ}
    (he : e ∈ Set.Icc (0 : ℝ) 1) : raw (noise X e) = noiseMatrix e (raw X) := by
  rw [noise, dite_eq_left (inferInstance : Nonempty E), noiseWithEnvironment, dite_eq_left he]
  rfl

private lemma raw_noise_affine (X : DensityState (R × E)) {e : ℝ}
    (he : e ∈ Set.Icc (0 : ℝ) 1) :
    raw (noise X e) = (1-e) • raw X + e • raw (replacement X) := by
  simpa only [noiseMatrix, ← raw_replacement] using raw_noise X he

@[simp] private theorem partialTrace_noiseMatrix (e : ℝ) (X : Matrix (R × E) (R × E) ℂ) :
    partialTraceRight (noiseMatrix e X) = partialTraceRight X := by
  rw [noiseMatrix, partialTraceRight_add, partialTraceRight_smul, partialTraceRight_smul,
    partialTrace_replacementMatrix, ← add_smul, sub_add_cancel, one_smul]

@[simp] private theorem marginal_noise (X : DensityState (R × E)) (e : ℝ) :
    marginalRight (noise X e) = marginalRight X := by
  by_cases he : e ∈ Set.Icc (0 : ℝ) 1
  · apply Subtype.ext
    apply CStarMatrix.ofMatrix.symm.injective
    change partialTraceRight (raw (noise X e)) = partialTraceRight (raw X)
    rw [raw_noise X he, partialTrace_noiseMatrix]
  · simp [noise, noiseWithEnvironment, he, (inferInstance : Nonempty E)]

/-- The positive environment replacement supplies a strict spectral floor.
For a singular source marginal, the source still is a density state. -/
private theorem noise_posDef (X : DensityState (R × E))
    (hX : (partialTraceRight (raw X)).PosDef) {e : ℝ} (he : 0 < e) (he' : e ≤ 1) :
    (raw (noise X e)).PosDef := by
  rw [raw_noise X ⟨he.le, he'⟩, noiseMatrix, ← raw_replacement]
  exact Matrix.PosDef.posSemidef_add ((density_posSemidef X).smul (sub_nonneg.mpr he'))
    ((replacement_posDef X hX).smul he)

/-- Supported inputs remain feasible at every noise weight. At positive weight
only the reference's retained marginal must be faithful. -/
private theorem noise_support (X Y : DensityState (R × E)) (hXY : SupportContained X Y)
    (hY : (partialTraceRight (raw Y)).PosDef) {e : ℝ} (he : e ∈ Set.Icc (0 : ℝ) 1) :
    SupportContained (noise X e) (noise Y e) := by
  rcases eq_or_lt_of_le he.1 with h | h
  · subst e
    have hzero (W : DensityState (R × E)) : noise W 0 = W := by
      apply Subtype.ext
      apply CStarMatrix.ofMatrix.symm.injective
      change raw (noise W 0) = raw W
      rw [raw_noise W he]
      simp [noiseMatrix]
    simpa only [hzero] using hXY
  · exact support_of_posDef _ _ (noise_posDef Y hY h he.2)

private lemma marginal_entropy_le (X Y : DensityState (R × E)) (hXY : SupportContained X Y) :
    SupportContained (marginalRight X) (marginalRight Y) ∧
      finiteTraceLogRelativeEntropy (marginalRight X) (marginalRight Y) ≤
      finiteTraceLogRelativeEntropy X Y := by
  obtain ⟨C, hC⟩ := exists_eraseChannel (n := R) (ι := E)
  have hstate (W : DensityState (R × E)) : C.mapState W = marginalRight W := by
    apply Subtype.ext
    apply CStarMatrix.ofMatrix.symm.injective
    change CStarMatrix.ofMatrix.symm (C.toCompletelyPositiveMap (CStarMatrix.ofMatrix (raw W))) =
      partialTraceRight (raw W)
    rw [hC]
    ext r s
    simp [Matrix.sum_apply, partialTraceRight]
  have hdpi := extended_quantum_relative_entropy_channel_dpi C X Y
  rw [hstate X, hstate Y] at hdpi
  have hs := (extendedQuantumRelativeEntropy_ne_top_iff _ _).mp
    (ne_top_of_le_ne_top ((extendedQuantumRelativeEntropy_ne_top_iff X Y).mpr hXY) hdpi)
  rw [extendedQuantumRelativeEntropy_eq_coe_of_support hXY,
    extendedQuantumRelativeEntropy_eq_coe_of_support hs] at hdpi
  exact ⟨hs, WithTop.coe_le_coe.mp hdpi⟩

/-- The actual full-minus-retained entropy loss. Every use below supplies support. -/
def loss (X Y : DensityState (R × E)) : ℝ :=
  finiteTraceLogRelativeEntropy X Y -
    finiteTraceLogRelativeEntropy (marginalRight X) (marginalRight Y)

private theorem loss_nonneg (X Y : DensityState (R × E)) (hXY : SupportContained X Y) :
    0 ≤ loss X Y := sub_nonneg.mpr (marginal_entropy_le X Y hXY).2

/-- The replacement pair has exactly the retained relative entropy. -/
private theorem replacement_entropy (X Y : DensityState (R × E)) (hXY : SupportContained X Y) :
    finiteTraceLogRelativeEntropy (replacement X) (replacement Y) =
      finiteTraceLogRelativeEntropy (marginalRight X) (marginalRight Y) :=
  finiteTraceLog_uniform_product _ _ (marginal_entropy_le X Y hXY).1

/-- Dimension-independent contraction of the true supported loss. The original
joint reference may be singular and the original source marginal may be singular. -/
theorem noise_loss_contract (X Y : DensityState (R × E)) (hXY : SupportContained X Y)
    (hY : (partialTraceRight (raw Y)).PosDef) {e : ℝ} (he : e ∈ Set.Icc (0 : ℝ) 1) :
    let noisyLoss := loss (noise X e) (noise Y e)
    0 ≤ noisyLoss ∧ noisyLoss ≤ (1-e) * loss X Y := by
  dsimp only
  refine ⟨loss_nonneg _ _ (noise_support X Y hXY hY he), ?_⟩
  have hrep := support_of_posDef (replacement X) (replacement Y) (replacement_posDef Y hY)
  have h := traceLog_mix_le (raw X) (raw Y) (raw (replacement X)) (raw (replacement Y))
    (density_posSemidef X) (density_posSemidef Y)
    (density_posSemidef (replacement X)) (density_posSemidef (replacement Y))
    (fun x hx => hXY hx) (fun x hx => hrep hx) he
  have hmix : finiteTraceLogRelativeEntropy (noise X e) (noise Y e) ≤
      (1-e) * finiteTraceLogRelativeEntropy X Y +
        e * finiteTraceLogRelativeEntropy (replacement X) (replacement Y) := by
    simp only [finiteTraceLog_eq_raw, raw_noise X he, raw_noise Y he, noiseMatrix,
      ← raw_replacement]
    exact h
  rw [replacement_entropy X Y hXY] at hmix
  simp only [loss, marginal_noise]
  calc
    _ ≤ (1-e) * finiteTraceLogRelativeEntropy X Y +
        e * finiteTraceLogRelativeEntropy (marginalRight X) (marginalRight Y) -
        finiteTraceLogRelativeEntropy (marginalRight X) (marginalRight Y) :=
      sub_le_sub_right hmix _
    _ = _ := by ring

/-- Since the actual two marginals are fixed, the supported mixture continuity
supplier applies with the entropy upper bound furnished by loss contraction. -/
private theorem tendsto_loss_noise (X Y : DensityState (R × E)) (hXY : SupportContained X Y)
    (hY : (partialTraceRight (raw Y)).PosDef) :
    Tendsto (fun e : ℝ => loss (noise X e) (noise Y e)) (𝓝[>] 0) (𝓝 (loss X Y)) := by
  have hNear : ∀ᶠ e : ℝ in 𝓝[>] 0, e ∈ Set.Ioo (0 : ℝ) 1 := Ioo_mem_nhdsGT zero_lt_one
  have hD : Tendsto (fun e : ℝ => finiteTraceLogRelativeEntropy (noise X e) (noise Y e))
      (𝓝[>] 0) (𝓝 (finiteTraceLogRelativeEntropy X Y)) := by
    apply tendsto_finiteTraceLogRelativeEntropy_of_noise X Y (replacement X) (replacement Y)
      (noise X) (noise Y) hXY
    · filter_upwards [hNear] with e he
      exact raw_noise_affine X ⟨he.1.le, he.2.le⟩
    · filter_upwards [hNear] with e he
      exact raw_noise_affine Y ⟨he.1.le, he.2.le⟩
    · filter_upwards [hNear] with e he
      exact noise_support X Y hXY hY ⟨he.1.le, he.2.le⟩
    · filter_upwards [hNear] with e he
      have h := (noise_loss_contract X Y hXY hY ⟨he.1.le, he.2.le⟩).2
      have hΔ := loss_nonneg X Y hXY
      have hle : (1-e) * loss X Y ≤ loss X Y := by
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right (show 1-e ≤ 1 by linarith [he.1]) hΔ
      have h' := h.trans hle
      simp only [loss, marginal_noise] at h'
      exact (sub_le_sub_iff_right _).mp h'
  simpa only [loss, marginal_noise] using hD.sub
    (tendsto_const_nhds (x := finiteTraceLogRelativeEntropy (marginalRight X) (marginalRight Y)))

end Environment

section PetzScore
variable {R E : Type u} [Fintype R] [DecidableEq R] [Nonempty R]
  [Fintype E] [DecidableEq E] [Nonempty E]

/-- The unhalved squared trace error of the physical recovered marginal. -/
def errorSq (X Y : DensityState (R × E)) : ℝ :=
  traceNorm (raw X - partialTracePetz (raw Y) (partialTraceRight (raw X))) ^ 2

private lemma continuous_sqrtMatrix {n : Type u} [Fintype n] [DecidableEq n]
    {T : Type*} [TopologicalSpace T] {M : T → Matrix n n ℂ}
    (hM : Continuous M) (hHerm : ∀ t, (M t).IsHermitian) :
    Continuous (fun t => cfc Real.sqrt (M t)) :=
  Continuous.cfc_of_mem_nhdsSet Real.sqrt (s := Set.univ)
    (by simp (config := { congrConsts := false })) hM
    (fun t => (hHerm t).isSelfAdjoint) Real.continuous_sqrt.continuousOn

private lemma continuous_traceNorm {n : Type u} [Fintype n] [DecidableEq n] :
    Continuous (traceNorm : Matrix n n ℂ → ℝ) := by
  have hGram : Continuous (fun M : Matrix n n ℂ => Mᴴ * M) := by fun_prop
  have hSqrt := continuous_sqrtMatrix hGram Matrix.isHermitian_conjTranspose_mul_self
  have hTrace : Continuous (fun M : Matrix n n ℂ => M.trace.re) := by
    unfold Matrix.trace
    fun_prop
  have hFormula (M : Matrix n n ℂ) :
      traceNorm M = (cfc Real.sqrt (Mᴴ * M)).trace.re := by
    change (CFC.sqrt (Mᴴ * M)).trace.re = _
    rw [CFC.sqrt_eq_real_sqrt (Mᴴ * M) M.posSemidef_conjTranspose_mul_self.nonneg,
      cfcₙ_eq_cfc (a := Mᴴ * M) Real.continuous_sqrt.continuousOn Real.sqrt_zero]
  rw [funext hFormula]
  exact hTrace.comp hSqrt

private lemma tendsto_raw_noise (X : DensityState (R × E)) :
    Tendsto (fun e : ℝ => raw (noise X e)) (𝓝[>] 0) (𝓝 (raw X)) := by
  let path (e : ℝ) := (1-e) • raw X + e • raw (replacement X)
  have hpath : Continuous path := by unfold path; fun_prop
  have hlim : Tendsto path (𝓝[>] (0 : ℝ)) (𝓝 (raw X)) := by
    simpa [path] using (hpath.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
  apply Tendsto.congr' _ hlim
  filter_upwards [Ioo_mem_nhdsGT (zero_lt_one : (0 : ℝ) < 1)] with e he
  rw [raw_noise X ⟨he.1.le, he.2.le⟩, noiseMatrix, ← raw_replacement]

private lemma tendsto_sqrt_noise (Y : DensityState (R × E)) :
    Tendsto (fun e : ℝ => cfc Real.sqrt (raw (noise Y e)))
      (𝓝[>] 0) (𝓝 (cfc Real.sqrt (raw Y))) := by
  let path (e : ℝ) := (1-e) • raw Y + e • raw (replacement Y)
  have hHerm (e : ℝ) : (path e).IsHermitian :=
    ((density_posSemidef Y).isHermitian.smul (show IsSelfAdjoint (1-e) from rfl)).add
      ((density_posSemidef (replacement Y)).isHermitian.smul (show IsSelfAdjoint e from rfl))
  have hcont := continuous_sqrtMatrix (M := path) (by unfold path; fun_prop) hHerm
  have hlim : Tendsto (fun e => cfc Real.sqrt (path e)) (𝓝[>] (0 : ℝ))
      (𝓝 (cfc Real.sqrt (raw Y))) := by
    simpa [path] using (hcont.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
  apply Tendsto.congr' _ hlim
  filter_upwards [Ioo_mem_nhdsGT (zero_lt_one : (0 : ℝ) < 1)] with e he
  rw [raw_noise Y ⟨he.1.le, he.2.le⟩, noiseMatrix, ← raw_replacement]

private lemma raw_marginal_noise (X : DensityState (R × E)) (e : ℝ) :
    partialTraceRight (raw (noise X e)) = partialTraceRight (raw X) := by
  exact congrArg (fun W : DensityState R => raw W) (marginal_noise X e)

/-- The two marginals are fixed, so the Petz middle factor is literally
constant. The square-root continuity argument includes singular joint references. -/
private theorem tendsto_ordinaryPetz_noise (X Y : DensityState (R × E)) :
    Tendsto (fun e : ℝ => partialTracePetz (raw (noise Y e))
      (partialTraceRight (raw (noise X e)))) (𝓝[>] 0)
      (𝓝 (partialTracePetz (raw Y) (partialTraceRight (raw X)))) := by
  let W := mpow (partialTraceRight (raw Y)) (-(1 / 2))
  let J := lift (ι := E) (W * partialTraceRight (raw X) * W)
  have hS := tendsto_sqrt_noise Y
  have hlim := (hS.mul (tendsto_const_nhds (x := J))).mul hS
  have hhalf (A : Matrix (R × E) (R × E) ℂ) : mpow A (1 / 2) = cfc Real.sqrt A := by
    unfold mpow
    exact congrArg (fun f : ℝ → ℝ => cfc f A)
      (funext fun t => (Real.sqrt_eq_rpow t).symm)
  simpa only [partialTracePetz, hhalf, raw_marginal_noise, J, W] using hlim

/-- The actual ordinary-Petz squared error tends to its original value. -/
private theorem tendsto_errorSq_noise (X Y : DensityState (R × E)) :
    Tendsto (fun e : ℝ => errorSq (noise X e) (noise Y e))
      (𝓝[>] 0) (𝓝 (errorSq X Y)) := by
  exact (continuous_traceNorm.continuousAt.tendsto.comp
    ((tendsto_raw_noise X).sub (tendsto_ordinaryPetz_noise X Y))).pow 2

/-- At positive original loss, the actual finite-pair score converges under
marginal-preserving environmental noise. -/
private theorem tendsto_score_noise (X Y : DensityState (R × E))
    (hXY : SupportContained X Y) (hY : (partialTraceRight (raw Y)).PosDef)
    (hΔ : 0 < loss X Y) :
    Tendsto (fun e : ℝ => errorSq (noise X e) (noise Y e) / loss (noise X e) (noise Y e))
      (𝓝[>] 0) (𝓝 (errorSq X Y / loss X Y)) :=
  (tendsto_errorSq_noise X Y).div (tendsto_loss_noise X Y hXY hY) hΔ.ne'

/-- A strict finite-pair score violation at any threshold C survives a positive
noise weight with exactly the original marginals and a faithful joint reference.
The source may have singular marginal, and is faithful whenever that marginal
is faithful. The additional bound on the noisy loss is the exact contraction. -/
theorem exists_strict_score_noise (X Y : DensityState (R × E))
    (hXY : SupportContained X Y) (hY : (partialTraceRight (raw Y)).PosDef)
    (hΔ : 0 < loss X Y) {C : ℝ} (hstrict : C < errorSq X Y / loss X Y) :
    ∃ e : ℝ,
      let Ynoisy := noise Y e
      0 < e ∧ e < 1 ∧
      marginalRight (noise X e) = marginalRight X ∧
      marginalRight Ynoisy = marginalRight Y ∧
      (raw Ynoisy).PosDef ∧
      ((partialTraceRight (raw X)).PosDef → (raw (noise X e)).PosDef) ∧
      SupportContained (noise X e) Ynoisy ∧
      0 < loss (noise X e) Ynoisy ∧
      loss (noise X e) Ynoisy ≤ (1-e) * loss X Y ∧
      C < errorSq (noise X e) Ynoisy / loss (noise X e) Ynoisy := by
  have hNear : ∀ᶠ e : ℝ in 𝓝[>] 0, e ∈ Set.Ioo (0 : ℝ) 1 := Ioo_mem_nhdsGT zero_lt_one
  have hpos := (tendsto_loss_noise X Y hXY hY).eventually (Ioi_mem_nhds hΔ)
  have hscore := (tendsto_score_noise X Y hXY hY hΔ).eventually (Ioi_mem_nhds hstrict)
  obtain ⟨e, he, hp, hs⟩ := (hNear.and (hpos.and hscore)).exists
  exact ⟨e, he.1, he.2, marginal_noise X e, marginal_noise Y e,
    noise_posDef Y hY he.1 he.2.le,
    fun hX => noise_posDef X hX he.1 he.2.le,
    noise_support X Y hXY hY ⟨he.1.le, he.2.le⟩,
    hp, (noise_loss_contract X Y hXY hY ⟨he.1.le, he.2.le⟩).2, hs⟩

end PetzScore

end D5.S3.Quantum.Recovery.LocalCompression.PetzFixedMarginalNoise
