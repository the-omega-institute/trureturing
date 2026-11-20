import D5.S3.Quantum.Recovery.PetzStinespringCompression
import D5.S3.Quantum.Recovery.PetzSupportCompressionInvariants
import D5.S3.Quantum.Recovery.PetzCommonUniformNoise

/-!
# Ordinary Petz recovery with the output support dimension

The right partial trace of a retained-first dilation realizes the channel.
Compressing its retained factor to the positive spectrum of the output
reference gives a faithful marginal and preserves the two entropy terms
and the ordinary Petz error.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe u v

namespace PetzChannelDimensionRecovery

open Matrix
open scoped CStarAlgebra ComplexOrder Kronecker Matrix MatrixOrder
open D5.S3.Quantum.Foundation.FiniteStateChannel (DensityState QuantumChannel)
open D5.S3.Quantum.Foundation.FiniteTraceDistance (traceNorm)
open D5.S3.Quantum.Information.PartialTraceMutualInformation
  (density_posSemidef marginalRight partialTraceRight partialTraceRight_posSemidef)
open D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction (act)
open D5.S3.Quantum.Divergence.CanonicalChannelDPI (actual_kraus_representation krausAdjoint)
open D5.S3.Quantum.Divergence.SupportAwareRelativeEntropy
  (SupportContained finiteTraceLogRelativeEntropy)
open D5.S3.Quantum.Lieb.SupportPerspectiveTransport (spectral_sqrt_normalization)
open D5.S3.Quantum.Recovery.SpectralTransposeRecovery (spectralSupport spectralInverseSqrt)
open PetzPhysicalAmplitude (lift ordinaryPetz)
open PetzStinespringCompression
  (cfc_isometric_embed exists_retainedFirst_stinespring ordinaryPetz_embed)
open PetzSupportCompressionInvariants

private abbrev raw {n : Type*} [Fintype n] [DecidableEq n]
    (X : DensityState n) : Matrix n n ℂ :=
  CStarMatrix.ofMatrix.symm X.1

section Isometries

variable {n : Type u} {m : Type v} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

private theorem embed_mul (J : Matrix m n ℂ) (hJ : Jᴴ * J = 1) (A B : Matrix n n ℂ) :
    (J * A * Jᴴ) * (J * B * Jᴴ) = J * (A * B) * Jᴴ := by
  calc
    _ = (J * A) * (Jᴴ * J) * B * Jᴴ := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hJ, Matrix.mul_one, Matrix.mul_assoc J A B]

private theorem embed_mulVec_eq_zero_iff (J : Matrix m n ℂ) (hJ : Jᴴ * J = 1)
    (A : Matrix n n ℂ) (w : m → ℂ) :
    (J * A * Jᴴ) *ᵥ w = 0 ↔ A *ᵥ (Jᴴ *ᵥ w) = 0 := by
  simp only [← Matrix.mulVec_mulVec]
  constructor
  · intro hw
    have h := congrArg (fun z : m → ℂ => Jᴴ *ᵥ z) hw
    change Jᴴ *ᵥ (J *ᵥ (A *ᵥ (Jᴴ *ᵥ w))) = Jᴴ *ᵥ (0 : m → ℂ) at h
    rwa [Matrix.mulVec_mulVec, hJ, Matrix.one_mulVec, Matrix.mulVec_zero] at h
  · intro hw
    rw [hw, Matrix.mulVec_zero]

private theorem supportContained_embed_iff (J : Matrix m n ℂ) (hJ : Jᴴ * J = 1)
    (X Y : DensityState n) :
    SupportContained (embedDensityState J hJ X) (embedDensityState J hJ Y) ↔
      SupportContained X Y := by
  constructor
  · intro h v hv
    change raw Y *ᵥ v = 0 at hv
    change raw X *ᵥ v = 0
    have hJv : Jᴴ *ᵥ (J *ᵥ v) = v := by
      rw [Matrix.mulVec_mulVec, hJ, Matrix.one_mulVec]
    have hv' : (J * raw Y * Jᴴ) *ᵥ (J *ᵥ v) = 0 :=
      (embed_mulVec_eq_zero_iff J hJ (raw Y) (J *ᵥ v)).mpr (by rw [hJv]; exact hv)
    have hXv : (J * raw X * Jᴴ) *ᵥ (J *ᵥ v) = 0 := h hv'
    simpa only [hJv] using (embed_mulVec_eq_zero_iff J hJ (raw X) (J *ᵥ v)).mp hXv
  · intro h w hw
    change (J * raw Y * Jᴴ) *ᵥ w = 0 at hw
    change (J * raw X * Jᴴ) *ᵥ w = 0
    exact (embed_mulVec_eq_zero_iff J hJ (raw X) w).mpr
      (h ((embed_mulVec_eq_zero_iff J hJ (raw Y) w).mp hw))

private def compressDensityState (J : Matrix m n ℂ) (hJ : Jᴴ * J = 1)
    (X : DensityState m) (hX : J * (Jᴴ * raw X * J) * Jᴴ = raw X) : DensityState n := by
  let A := Jᴴ * raw X * J
  refine ⟨CStarMatrix.ofMatrix A, ?_, ?_⟩
  · exact map_nonneg CStarMatrix.ofMatrixStarAlgEquiv
      ((density_posSemidef X).conjTranspose_mul_mul_same J).nonneg
  · change A.trace = 1
    calc
      A.trace = (J * A * Jᴴ).trace := (trace_isometric_embed J hJ A).symm
      _ = (raw X).trace := congrArg Matrix.trace hX
      _ = 1 := X.2.2

private theorem embed_compressDensityState (J : Matrix m n ℂ) (hJ : Jᴴ * J = 1)
    (X : DensityState m) (hX : J * (Jᴴ * raw X * J) * Jᴴ = raw X) :
    embedDensityState J hJ (compressDensityState J hJ X hX) = X := by
  apply Subtype.ext
  apply CStarMatrix.ofMatrix.symm.injective
  exact hX

private theorem traceNorm_sub_embed (J : Matrix m n ℂ) (hJ : Jᴴ * J = 1)
    (A B : Matrix n n ℂ) :
    traceNorm (J * A * Jᴴ - J * B * Jᴴ) = traceNorm (A - B) := by
  calc
    _ = traceNorm (J * (A - B) * Jᴴ) := by rw [Matrix.mul_sub, Matrix.sub_mul]
    _ = _ := traceNorm_isometric_embed J hJ (A - B)

end Isometries

private theorem spectralSupport_mul_of_support {n : Type*} [Fintype n] [DecidableEq n]
    {X Y : DensityState n} (hXY : SupportContained X Y) :
    spectralSupport (raw Y) * raw X = raw X := by
  let P := spectralSupport (raw Y)
  have hY := density_posSemidef Y
  have hX := (density_posSemidef X).isHermitian
  obtain ⟨_, _, hP, _, _, _, hPY, _⟩ := spectral_sqrt_normalization (raw Y) hY
  have hYP : raw Y * P = raw Y := by
    simpa only [P, Matrix.conjTranspose_mul, hP, hY.isHermitian.eq] using
      congrArg Matrix.conjTranspose hPY
  have hYzero : raw Y * (1 - P) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, hYP, sub_self]
  have hXzero : raw X * (1 - P) = 0 := by
    apply Matrix.ext_iff_mulVec.mpr
    intro v
    rw [Matrix.zero_mulVec, ← Matrix.mulVec_mulVec]
    have hYv : raw Y *ᵥ ((1 - P) *ᵥ v) = 0 := by
      rw [Matrix.mulVec_mulVec, hYzero, Matrix.zero_mulVec]
    exact hXY hYv
  have hXP : raw X * P = raw X := by
    rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at hXzero
    exact hXzero.symm
  simpa only [P, Matrix.conjTranspose_mul, hP, hX.eq] using
    congrArg Matrix.conjTranspose hXP

section Retained

variable {b s e : Type u}
  [Fintype b] [DecidableEq b] [Fintype s] [DecidableEq s] [Fintype e] [DecidableEq e]

/-- The ordinary partial-trace Petz map commutes with any isometric inclusion
of the retained carrier. The spectral inverse square root vanishes at zero. -/
theorem ordinaryPetz_retained_embed (U : Matrix b s ℂ) (hU : Uᴴ * U = 1)
    {Y : Matrix (s × e) (s × e) ℂ} (hY : Y.PosSemidef) (p : Matrix s s ℂ) :
    let L := U ⊗ₖ (1 : Matrix e e ℂ)
    ordinaryPetz (L * Y * Lᴴ) (U * p * Uᴴ) = L * ordinaryPetz Y p * Lᴴ := by
  dsimp only
  let L := U ⊗ₖ (1 : Matrix e e ℂ)
  let q := partialTraceRight Y
  let W := spectralInverseSqrt q
  have hL : Lᴴ * L = 1 := retained_lift_isometry U hU
  have hMarginal : partialTraceRight (L * Y * Lᴴ) = U * q * Uᴴ :=
    partialTraceRight_retained_sandwich U Y
  have hSqrt : cfc Real.sqrt (L * Y * Lᴴ) = L * cfc Real.sqrt Y * Lᴴ := by
    simpa only [Real.sqrt_zero, zero_smul, add_zero] using
      cfc_isometric_embed L hL hY.isHermitian Real.sqrt
  have hInverse : spectralInverseSqrt (U * q * Uᴴ) = U * W * Uᴴ := by
    simpa only [spectralInverseSqrt, W, Real.sqrt_zero, _root_.inv_zero, zero_smul, add_zero] using
      cfc_isometric_embed U hU (partialTraceRight_posSemidef hY).isHermitian
        (fun x : ℝ => (Real.sqrt x)⁻¹)
  have hMiddle : spectralInverseSqrt (partialTraceRight (L * Y * Lᴴ)) *
      (U * p * Uᴴ) * spectralInverseSqrt (partialTraceRight (L * Y * Lᴴ)) =
      U * (W * p * W) * Uᴴ := by
    rw [hMarginal, hInverse, embed_mul U hU, embed_mul U hU]
  have hLift : lift (B := e) (U * (W * p * W) * Uᴴ) =
      (L * lift (B := e) (W * p * W) : Matrix (b × e) (s × e) ℂ) * Lᴴ := by
    simp only [lift, L, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
      ← Matrix.mul_kronecker_mul, Matrix.mul_one]
  unfold ordinaryPetz
  dsimp only
  rw [hSqrt, hMiddle, hLift, embed_mul L hL, embed_mul L hL]

end Retained

section Channel

variable {a b : Type u} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

/-- The ordinary Petz map of the actual channel at the reference `Y`. -/
def channelOrdinaryPetz (Φ : QuantumChannel a b) (Y : Matrix a a ℂ) (p : Matrix b b ℂ) :
    Matrix a a ℂ :=
  let Q := spectralInverseSqrt (act Φ Y)
  cfc Real.sqrt Y * krausAdjoint (actual_kraus_representation Φ).kraus (Q * p * Q) *
    cfc Real.sqrt Y

set_option maxHeartbeats 1000000 in
/-- For every supported input, the squared ordinary Petz error is bounded by
`8 * (1 + d²)` times the finite relative entropy loss, where `d` is the rank
of the actual channel output on the reference. -/
theorem traceNorm_sub_channelOrdinaryPetz_sq_le_finiteTraceLog
    (Φ : QuantumChannel a b) (X Y : DensityState a) (hXY : SupportContained X Y) :
    let R : Matrix a a ℂ := CStarMatrix.ofMatrix.symm X.1
    let S : Matrix a a ℂ := CStarMatrix.ofMatrix.symm Y.1
    let d := (act Φ S).rank
    traceNorm (R - channelOrdinaryPetz Φ S (act Φ R)) ^ 2 ≤
      (8 * (1 + (d : ℝ) ^ 2)) *
        (finiteTraceLogRelativeEntropy X Y -
          finiteTraceLogRelativeEntropy (Φ.mapState X) (Φ.mapState Y)) := by
  obtain ⟨V, hV, hAction⟩ := exists_retainedFirst_stinespring Φ
  let XV := embedDensityState V hV X
  let YV := embedDensityState V hV Y
  have hY := density_posSemidef Y
  let q := partialTraceRight (raw YV)
  have hq : q.PosSemidef := partialTraceRight_posSemidef (density_posSemidef YV)
  let U := spectralInclusion hq
  let L := U ⊗ₖ (1 : Matrix (b × a) (b × a) ℂ)
  have hU : Uᴴ * U = 1 := spectralInclusion_isometry hq
  have hL : Lᴴ * L = 1 := retained_lift_isometry U hU
  have hXreconstruct : L * (Lᴴ * raw XV * L) * Lᴴ = raw XV :=
    stinespring_support_compression V hY (density_posSemidef X).isHermitian
      (spectralSupport_mul_of_support hXY)
  obtain ⟨_, _, hFaithful, hYreconstruct, _, _⟩ := faithful_retained_marginal V hY
  let X' := compressDensityState L hL XV hXreconstruct
  let Y' := compressDensityState L hL YV hYreconstruct
  have hXembed : embedDensityState L hL X' = XV :=
    embed_compressDensityState L hL XV hXreconstruct
  have hYembed : embedDensityState L hL Y' = YV :=
    embed_compressDensityState L hL YV hYreconstruct
  have hXY' : SupportContained X' Y' := by
    apply (supportContained_embed_iff L hL X' Y').mp
    exact (congrArg₂ SupportContained hXembed hYembed).mpr
      ((supportContained_embed_iff V hV X Y).mpr hXY)
  have hJointEntropy : finiteTraceLogRelativeEntropy X' Y' = finiteTraceLogRelativeEntropy X Y := by
    calc
      _ = finiteTraceLogRelativeEntropy (embedDensityState L hL X') (embedDensityState L hL Y') :=
        (finiteTraceLogRelativeEntropy_isometric_embed L hL X' Y').symm
      _ = _ := (congrArg₂ finiteTraceLogRelativeEntropy hXembed hYembed).trans
        (finiteTraceLogRelativeEntropy_isometric_embed V hV X Y)
  have hMarginal (Z : DensityState a) : marginalRight (embedDensityState V hV Z) = Φ.mapState Z := by
    apply Subtype.ext
    apply CStarMatrix.ofMatrix.symm.injective
    change partialTraceRight (V * raw Z * Vᴴ) = act Φ (raw Z)
    exact hAction (raw Z)
  have hOutput (Z : DensityState a) (Z' : DensityState (PositiveSpectralIndex hq × (b × a)))
      (hZ : embedDensityState L hL Z' = embedDensityState V hV Z) :
      embedDensityState U hU (marginalRight Z') = Φ.mapState Z := by
    exact (marginalRight_embedDensityState U hU Z').symm.trans
      ((congrArg (marginalRight (A := b) (B := b × a)) hZ).trans (hMarginal Z))
  have hMarginalEntropy :
      finiteTraceLogRelativeEntropy (marginalRight X') (marginalRight Y') =
        finiteTraceLogRelativeEntropy (Φ.mapState X) (Φ.mapState Y) := by
    calc
      _ = finiteTraceLogRelativeEntropy (embedDensityState U hU (marginalRight X'))
          (embedDensityState U hU (marginalRight Y')) :=
        (finiteTraceLogRelativeEntropy_isometric_embed U hU (marginalRight X') (marginalRight Y')).symm
      _ = _ := congrArg₂ finiteTraceLogRelativeEntropy (hOutput X X' hXembed)
        (hOutput Y Y' hYembed)
  have hRawX : L * raw X' * Lᴴ = raw XV := hXreconstruct
  have hRawY : L * raw Y' * Lᴴ = raw YV := hYreconstruct
  have hRecoveryL : L * ordinaryPetz (raw Y') (partialTraceRight (raw X')) * Lᴴ =
      ordinaryPetz (raw YV) (partialTraceRight (raw XV)) := by
    calc
      _ = ordinaryPetz (L * raw Y' * Lᴴ) (U * partialTraceRight (raw X') * Uᴴ) :=
        (ordinaryPetz_retained_embed U hU (density_posSemidef Y') (partialTraceRight (raw X'))).symm
      _ = _ := by
        rw [hRawY, ← partialTraceRight_retained_sandwich U (raw X'), hRawX]
  have hRecoveryV : ordinaryPetz (raw YV) (partialTraceRight (raw XV)) =
      V * channelOrdinaryPetz Φ (raw Y) (act Φ (raw X)) * Vᴴ := by
    change ordinaryPetz (V * raw Y * Vᴴ) (partialTraceRight (V * raw X * Vᴴ)) = _
    rw [hAction (raw X)]
    simpa only [ordinaryPetz, lift, channelOrdinaryPetz] using
      ordinaryPetz_embed Φ V hV hAction hY.isHermitian (act Φ (raw X))
  have hNormL : traceNorm (raw XV - ordinaryPetz (raw YV) (partialTraceRight (raw XV))) =
      traceNorm (raw X' - ordinaryPetz (raw Y') (partialTraceRight (raw X'))) := by
    rw [← hRecoveryL, ← hRawX]
    exact traceNorm_sub_embed L hL _ _
  have hNormV : traceNorm (raw XV - ordinaryPetz (raw YV) (partialTraceRight (raw XV))) =
      traceNorm (raw X - channelOrdinaryPetz Φ (raw Y) (act Φ (raw X))) := by
    rw [hRecoveryV]
    exact traceNorm_sub_embed V hV _ _
  have hRank : Fintype.card (PositiveSpectralIndex hq) = (act Φ (raw Y)).rank :=
    (card_positiveSpectralIndex_eq_rank hq).trans (congrArg Matrix.rank (hAction (raw Y)))
  have hBound := PetzCommonUniformNoise.traceNorm_sub_ordinaryPetz_sq_le_finiteTraceLog
    X' Y' hXY' hFaithful
  rw [hJointEntropy, hMarginalEntropy, hRank] at hBound
  dsimp only
  rw [← hNormV, hNormL]
  exact hBound

end Channel

end PetzChannelDimensionRecovery
