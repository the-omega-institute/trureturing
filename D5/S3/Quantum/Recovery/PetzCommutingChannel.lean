import Batteries.Tactic.OpenPrivate
import D5.S3.Quantum.Recovery.PetzCommutingPartialTrace
import D5.S3.Quantum.Recovery.PetzChannelDimensionRecovery

/-!
# Ordinary Petz recovery for finite channels with commuting outputs

Common uniform noise extends the faithful partial-trace bound to supported
joint states on a carrier with faithful retained reference. For a finite
channel, compress its retained-first Stinespring dilation to the support of
the actual output reference. The recovery matrix and the two finite trace-log
terms transport through the retained inclusion and the dilation isometry.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe u v

namespace PetzCommutingChannel

open Matrix Filter
open scoped Topology CStarAlgebra ComplexOrder Kronecker Matrix MatrixOrder
open D5.S3.Quantum.Foundation.FiniteStateChannel (DensityState QuantumChannel)
open D5.S3.Quantum.Foundation.FiniteTraceDistance (traceNorm)
open D5.S3.Quantum.Information.PartialTraceMutualInformation
  (density_posSemidef marginalRight partialTraceRight partialTraceRight_posSemidef)
open D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction (act)
open D5.S3.Quantum.Divergence.SupportAwareRelativeEntropy
  (SupportContained finiteTraceLogRelativeEntropy)
open PetzPhysicalAmplitude (lift ordinaryPetz)
open PetzSingularInputLimit (finiteTraceLog_eq_raw)
open PetzCommonUniformNoise
  (uniformMatrix uniformNoise uniformNoise_raw marginalRight_uniformNoise
    tendsto_finiteTraceLog_uniformNoise tendsto_marginal_finiteTraceLog_uniformNoise
    tendsto_traceNorm_sub_ordinaryPetz_sq_uniformNoise)
open PetzStinespringCompression (exists_retainedFirst_stinespring ordinaryPetz_embed)
open PetzSupportCompressionInvariants
open PetzChannelDimensionRecovery (channelOrdinaryPetz ordinaryPetz_retained_embed)

private abbrev raw {n : Type*} [Fintype n] [DecidableEq n]
    (X : DensityState n) : Matrix n n ℂ :=
  CStarMatrix.ofMatrix.symm X.1

section UniformNoise

open private uniformNoise_posDef from D5.S3.Quantum.Recovery.PetzCommonUniformNoise

private theorem commute_uniformMixture {n : Type u} [Fintype n] [DecidableEq n]
    {P Q : Matrix n n ℂ} (hPQ : Commute P Q) (t : ℝ) :
    Commute ((1 - t) • P + t • uniformMatrix n) ((1 - t) • Q + t • uniformMatrix n) := by
  have hIdentity (M : Matrix n n ℂ) : Commute M (uniformMatrix n) := by
    unfold uniformMatrix
    exact (Commute.one_right M).smul_right ((Fintype.card n : ℝ)⁻¹)
  have hP : Commute P ((1 - t) • Q + t • uniformMatrix n) :=
    (hPQ.smul_right (1 - t)).add_right ((hIdentity P).smul_right t)
  have hU : Commute (uniformMatrix n) ((1 - t) • Q + t • uniformMatrix n) :=
    (hIdentity _).symm
  exact (hP.smul_left (1 - t)).add_left (hU.smul_left t)

variable {A B : Type u} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

/-- The commuting retained coefficient-eight bound for supported joint states
when the retained reference is faithful. -/
theorem traceNorm_sub_ordinaryPetz_sq_le_eight_of_faithful_marginal
    (X Y : DensityState (A × B)) (hXY : SupportContained X Y)
    (hY : (partialTraceRight (CStarMatrix.ofMatrix.symm Y.1)).PosDef)
    (hComm : Commute (partialTraceRight (CStarMatrix.ofMatrix.symm X.1))
      (partialTraceRight (CStarMatrix.ofMatrix.symm Y.1))) :
    traceNorm (CStarMatrix.ofMatrix.symm X.1 -
      ordinaryPetz (CStarMatrix.ofMatrix.symm Y.1)
        (partialTraceRight (CStarMatrix.ofMatrix.symm X.1))) ^ 2 ≤
      8 * (finiteTraceLogRelativeEntropy X Y -
        finiteTraceLogRelativeEntropy (marginalRight X) (marginalRight Y)) := by
  have hEntropy := (tendsto_finiteTraceLog_uniformNoise X Y hXY).sub
    (tendsto_marginal_finiteTraceLog_uniformNoise X Y hY)
  have hRight := (tendsto_const_nhds (x := (8 : ℝ))).mul hEntropy
  letI : NeBot (𝓝[>] (0 : ℝ)) := nhdsWithin_Ioi_neBot le_rfl
  apply le_of_tendsto_of_tendsto (tendsto_traceNorm_sub_ordinaryPetz_sq_uniformNoise X Y hY) hRight
  filter_upwards [Ioo_mem_nhdsGT (zero_lt_one : (0 : ℝ) < 1)] with t ht
  have hNoisyMarginal (Z : DensityState (A × B)) :
      partialTraceRight (raw (uniformNoise Z t)) =
        (1 - t) • partialTraceRight (raw Z) + t • uniformMatrix A := by
    change raw (marginalRight (uniformNoise Z t)) = _
    rw [marginalRight_uniformNoise Z t]
    exact uniformNoise_raw (marginalRight Z) ht
  have hNoisyComm : Commute (partialTraceRight (raw (uniformNoise X t)))
      (partialTraceRight (raw (uniformNoise Y t))) := by
    rw [hNoisyMarginal X, hNoisyMarginal Y]
    exact commute_uniformMixture hComm t
  rw [finiteTraceLog_eq_raw (uniformNoise X t) (uniformNoise Y t),
    finiteTraceLog_eq_raw (marginalRight (uniformNoise X t)) (marginalRight (uniformNoise Y t))]
  exact PetzCommutingPartialTrace.traceNorm_sub_ordinaryPetz_sq_le_eight
    (uniformNoise_posDef X ht) (uniformNoise_posDef Y ht) (uniformNoise X t).2.2 hNoisyComm

end UniformNoise

section Channel

open private embed_mul supportContained_embed_iff compressDensityState
  embed_compressDensityState traceNorm_sub_embed spectralSupport_mul_of_support
  from D5.S3.Quantum.Recovery.PetzChannelDimensionRecovery

private theorem commute_of_isometric_embed {s : Type u} {b : Type v}
    [Fintype s] [DecidableEq s] [Fintype b] [DecidableEq b]
    (U : Matrix b s ℂ) (hU : Uᴴ * U = 1) {P Q : Matrix s s ℂ}
    (hComm : Commute (U * P * Uᴴ) (U * Q * Uᴴ)) : Commute P Q := by
  have hProduct : U * (P * Q) * Uᴴ = U * (Q * P) * Uᴴ := by
    simpa only [embed_mul U hU] using hComm.eq
  change P * Q = Q * P
  simpa only [compress_isometric_embed U hU] using
    congrArg (fun M : Matrix b b ℂ => Uᴴ * M * U) hProduct

variable {a b : Type u} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

set_option maxHeartbeats 1000000 in
/-- For any finite CPTP channel and supported pair of density states with
commuting actual outputs, the squared trace-norm error of ordinary Petz
recovery is at most eight times the actual finite Umegaki entropy deficit. -/
theorem traceNorm_sub_channelOrdinaryPetz_sq_le_eight
    (Φ : QuantumChannel a b) (X Y : DensityState a) (hXY : SupportContained X Y)
    (hComm : Commute (act Φ (CStarMatrix.ofMatrix.symm X.1))
      (act Φ (CStarMatrix.ofMatrix.symm Y.1))) :
    traceNorm (CStarMatrix.ofMatrix.symm X.1 -
      channelOrdinaryPetz Φ (CStarMatrix.ofMatrix.symm Y.1)
        (act Φ (CStarMatrix.ofMatrix.symm X.1))) ^ 2 ≤
      8 * (finiteTraceLogRelativeEntropy X Y -
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

  have hMarginal (Z : DensityState a) : marginalRight (embedDensityState V hV Z) = Φ.mapState Z := by
    apply Subtype.ext
    apply CStarMatrix.ofMatrix.symm.injective
    change partialTraceRight (V * raw Z * Vᴴ) = act Φ (raw Z)
    exact hAction (raw Z)
  have hOutput (Z : DensityState a) (Z' : DensityState (PositiveSpectralIndex hq × (b × a)))
      (hZ : embedDensityState L hL Z' = embedDensityState V hV Z) :
      embedDensityState U hU (marginalRight Z') = Φ.mapState Z :=
    (marginalRight_embedDensityState U hU Z').symm.trans
      ((congrArg (marginalRight (A := b) (B := b × a)) hZ).trans (hMarginal Z))
  have hPOutput : U * partialTraceRight (raw X') * Uᴴ = act Φ (raw X) :=
    congrArg (fun Z : DensityState b => raw Z) (hOutput X X' hXembed)
  have hQOutput : U * partialTraceRight (raw Y') * Uᴴ = act Φ (raw Y) :=
    congrArg (fun Z : DensityState b => raw Z) (hOutput Y Y' hYembed)
  have hComm' : Commute (partialTraceRight (raw X')) (partialTraceRight (raw Y')) := by
    apply commute_of_isometric_embed U hU
    rwa [hPOutput, hQOutput]

  have hJointEntropy : finiteTraceLogRelativeEntropy X' Y' = finiteTraceLogRelativeEntropy X Y := by
    calc
      _ = finiteTraceLogRelativeEntropy (embedDensityState L hL X') (embedDensityState L hL Y') :=
        (finiteTraceLogRelativeEntropy_isometric_embed L hL X' Y').symm
      _ = _ := (congrArg₂ finiteTraceLogRelativeEntropy hXembed hYembed).trans
        (finiteTraceLogRelativeEntropy_isometric_embed V hV X Y)
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
  have hRecovery :
      L * ordinaryPetz (raw Y') (partialTraceRight (raw X')) * Lᴴ =
        V * channelOrdinaryPetz Φ (raw Y) (act Φ (raw X)) * Vᴴ := by
    calc
      _ = ordinaryPetz (raw YV) (act Φ (raw X)) := by
        rw [← hRawY, ← hPOutput]
        exact (ordinaryPetz_retained_embed U hU (density_posSemidef Y')
          (partialTraceRight (raw X'))).symm
      _ = _ := by
        change ordinaryPetz (V * raw Y * Vᴴ) (act Φ (raw X)) = _
        simpa only [ordinaryPetz, lift, channelOrdinaryPetz] using
          ordinaryPetz_embed Φ V hV hAction hY.isHermitian (act Φ (raw X))
  have hNorm :
      traceNorm (raw X' - ordinaryPetz (raw Y') (partialTraceRight (raw X'))) =
        traceNorm (raw X - channelOrdinaryPetz Φ (raw Y) (act Φ (raw X))) := by
    calc
      _ = traceNorm (raw XV - L * ordinaryPetz (raw Y') (partialTraceRight (raw X')) * Lᴴ) := by
        rw [← hRawX]
        exact (traceNorm_sub_embed L hL _ _).symm
      _ = _ := by
        rw [hRecovery]
        exact traceNorm_sub_embed V hV _ _
  have hBound := traceNorm_sub_ordinaryPetz_sq_le_eight_of_faithful_marginal
    X' Y' hXY' hFaithful hComm'
  simpa only [hNorm, hJointEntropy, hMarginalEntropy] using hBound

end Channel

end PetzCommutingChannel
