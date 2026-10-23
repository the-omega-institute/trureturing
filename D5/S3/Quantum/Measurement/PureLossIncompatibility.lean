/- GID: D5/S3/Quantum/Measurement/PureLossIncompatibility
   generality: I
   mirror-B: D5/B/S3/Quantum/Measurement/PureLossIncompatibility
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Pure-loss dual effects admit an exact compressed binary incompatibility certificate. -/

import D5.S3.Quantum.QuantumChannels.FockAttenuator.Attenuator
import D5.S3.Estimation.TransmissivityBetaPriorProbeRefutation
import D5.S3.Quantum.QuantumChannels.FockAttenuator.FiniteFockBeamSplitterNonExtremality
import D5.S3.Quantum.QuantumChannels.ConcealmentKernelNecessityRefutation

noncomputable section
open scoped BigOperators InnerProductSpace ENNReal NNReal ComplexOrder MatrixOrder
open Matrix
open D5.S3.Quantum.QuantumChannels.FockAttenuator.BeamSplitter
open D5.S3.Quantum.QuantumChannels.FockAttenuator.Attenuator
open D5.S3.Quantum.QuantumChannels.FockAttenuator.DisplacementCovariance
  (purePartialTrace mixture)
open D5.S3.Quantum.QuantumChannels.ConcealmentKernelNecessityRefutation (IsPOVM)
open D5.S3.Estimation.TransmissivityBetaPriorProbeRefutation (e compression)
open D5.S3.Quantum.QuantumChannels.FockAttenuator.FiniteFockBeamSplitterNonExtremality
  (fockPair_apply)

namespace D5.S3.Quantum.Measurement.PureLossIncompatibility

abbrev H := D5.S3.Estimation.TransmissivityBetaPriorProbeRefutation.FockSpace
abbrev K := lp (fun _ : ℕ => H) 2
abbrev Op := H →L[ℂ] H

-- Amplification acts on the retained vector at each environment coordinate.
def amplify (M : Op) : K →L[ℂ] K :=
  lp.mapCLM 2 (fun _ : ℕ => M) (norm_nonneg M) (fun _ => le_rfl)

private theorem amplify_apply (M : Op) (w : K) (k : ℕ) :
    (amplify M w) k = M (w k) :=
  rfl

def vacuumEmbedding : H →L[ℂ] K :=
  lp.singleContinuousLinearMap
    (𝕜 := ℂ) (E := fun _ : ℕ => H) (p := 2) 0

def stinespring (τ : Set.Icc (0 : ℝ) 1) : H →L[ℂ] K :=
  (beamSplitter τ.1 τ.2).toLinearIsometry.toContinuousLinearMap ∘L vacuumEmbedding

def dualLoss (τ : Set.Icc (0 : ℝ) 1) (M : Op) : Op :=
  (stinespring τ).adjoint ∘L amplify M ∘L stinespring τ

def IsLossDual (τ : Set.Icc (0 : ℝ) 1) (M N : Op) : Prop :=
  ∀ ψ : H, HasSum (fun n : ℕ =>
    ⟪e n, (M ∘L purePartialTrace (beamSplitter τ.1 τ.2 (tensor ψ (e 0)))) (e n)⟫_ℂ)
    ⟪ψ, N ψ⟫_ℂ

def IsBinaryPOVM (M : Fin 2 → Op) : Prop :=
  (∀ b, (M b).IsPositive) ∧ M 0 + M 1 = 1

def HasParent {m : ℕ} (F : Fin m → Fin 2 → Op) : Prop :=
  ∃ G : (Fin m → Fin 2) → Op,
    (∀ a, (G a).IsPositive) ∧
    (∑ a, G a) = 1 ∧
    ∀ j b,
      (∑ a ∈ Finset.univ.filter
        (fun a : Fin m → Fin 2 => a j = b), G a) = F j b

def inverseTransmissivity (n : ℕ) (hn : 1 ≤ n) : Set.Icc (0 : ℝ) 1 :=
  ⟨1 / (n : ℝ), by
    have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hn0 : (0 : ℝ) < (n : ℝ) := lt_of_lt_of_le zero_lt_one hnR
    constructor
    · exact (div_pos zero_lt_one hn0).le
    · exact (div_le_iff₀ hn0).2 (by simpa using hnR)⟩

def claim : Prop :=
  ∀ (n : ℕ) (hn : 1 ≤ n),
    ∃ M : Fin (n + 1) → Fin 2 → Op,
      (∀ j, IsBinaryPOVM (M j)) ∧
      (∃ N : Fin (n + 1) → Fin 2 → Op,
        ∀ j b, IsLossDual (inverseTransmissivity n hn) (M j b) (N j b)) ∧
      ∀ N : Fin (n + 1) → Fin 2 → Op,
        (∀ j b, IsLossDual (inverseTransmissivity n hn) (M j b) (N j b)) → ¬ HasParent N

private def onOff (μ : ℂ) (b : Fin 2) : Op :=
  if b = 0 then
    InnerProductSpace.rankOne ℂ (coherent μ) (coherent μ)
  else
    1 - InnerProductSpace.rankOne ℂ (coherent μ) (coherent μ)

private theorem coherent_norm (μ : ℂ) : ‖coherent μ‖ = 1 := by
  have ht := (coherentDensity μ).trace_one
  change HasSum (fun n : ℕ =>
    (inner ℂ (e n) (InnerProductSpace.rankOne ℂ (coherent μ) (coherent μ) (e n))).re) 1 at ht
  have hc : ∀ n : ℕ,
      (inner ℂ (e n) (InnerProductSpace.rankOne ℂ (coherent μ) (coherent μ) (e n))).re =
        ‖coherent μ n‖ ^ 2 := by
    intro n
    unfold e
    simp only [InnerProductSpace.rankOne_apply, inner_smul_right,
      lp.inner_single_left, lp.inner_single_right, RCLike.inner_apply,
      map_one, one_mul, mul_one, RCLike.conj_mul]
    norm_cast
  have hs := lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by norm_num) (coherent μ)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at hs
  have hn : ‖coherent μ‖ ^ 2 = 1 := hs.unique (ht.congr_fun (fun n => (hc n).symm))
  nlinarith [norm_nonneg (coherent μ)]

private theorem rankOne_complement_pos (v : H) (hv : ‖v‖ = 1) :
    (1 - InnerProductSpace.rankOne ℂ v v).IsPositive := by
  have hp : IsStarProjection (InnerProductSpace.rankOne ℂ v v) :=
    ⟨InnerProductSpace.isIdempotentElem_rankOne_self hv,
      ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
        (InnerProductSpace.isSymmetric_rankOne_self v)⟩
  exact ContinuousLinearMap.IsPositive.of_isStarProjection hp.one_sub

private theorem onOff_binary (μ : ℂ) : IsBinaryPOVM (onOff μ) := by
  have hv := coherent_norm μ
  constructor
  · intro b
    by_cases hb : b = 0
    · subst b
      change (InnerProductSpace.rankOne ℂ (coherent μ) (coherent μ)).IsPositive
      exact InnerProductSpace.isPositive_rankOne_self (coherent μ)
    · have hb1 : b = 1 := by fin_cases b <;> simp_all
      subst b
      change (1 - InnerProductSpace.rankOne ℂ (coherent μ) (coherent μ)).IsPositive
      exact rankOne_complement_pos _ hv
  · change InnerProductSpace.rankOne ℂ (coherent μ) (coherent μ) +
      (1 - InnerProductSpace.rankOne ℂ (coherent μ) (coherent μ)) = 1
    abel

private theorem amplify_add (M N : Op) : amplify (M + N) = amplify M + amplify N := by
  apply ContinuousLinearMap.ext
  intro w
  apply lp.ext
  funext k
  change (amplify (M + N) w) k = ((amplify M + amplify N) w) k
  simp only [amplify_apply, _root_.add_apply, lp.coeFn_add, Pi.add_apply]

private theorem amplify_one : amplify (1 : Op) = 1 := by
  apply ContinuousLinearMap.ext
  intro w
  apply lp.ext
  funext k
  rw [amplify_apply]
  rfl

private theorem vacuum_norm (v : H) : ‖vacuumEmbedding v‖ = ‖v‖ := by
  change ‖lp.single (E := fun _ : ℕ => H) (2 : ℝ≥0∞) 0 v‖ = ‖v‖
  rw [lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2)]

private def vacuumIso : H →ₗᵢ[ℂ] K :=
  LinearIsometry.mk vacuumEmbedding.toLinearMap vacuum_norm

private def stinespringIso (τ : Set.Icc (0 : ℝ) 1) : H →ₗᵢ[ℂ] K :=
  (beamSplitter τ.1 τ.2).toLinearIsometry.comp vacuumIso

private theorem stinespring_eq_iso (τ : Set.Icc (0 : ℝ) 1) :
    stinespring τ = (stinespringIso τ).toContinuousLinearMap := by
  ext v k
  rfl

private theorem dualLoss_add (τ : Set.Icc (0 : ℝ) 1) (M N : Op) :
    dualLoss τ (M + N) = dualLoss τ M + dualLoss τ N := by
  unfold dualLoss
  simp only [amplify_add, ContinuousLinearMap.comp_add, ContinuousLinearMap.add_comp]

private theorem dualLoss_one (τ : Set.Icc (0 : ℝ) 1) : dualLoss τ 1 = 1 := by
  unfold dualLoss
  rw [stinespring_eq_iso, amplify_one]
  rw [show (1 : K →L[ℂ] K) = ContinuousLinearMap.id ℂ K from rfl,
    ContinuousLinearMap.id_comp]
  exact LinearIsometry.adjoint_comp_self (stinespringIso τ)

-- Compression pulls quadratic forms back through the two-dimensional Fock embedding.
private def embed (v : Fin 2 → ℂ) : H := ∑ i, v i • e i.val

private theorem compress_pos (X : Op) (hX : X.IsPositive) :
    (compression (N := 1) X).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · rw [Matrix.IsHermitian]
    ext i j
    simp only [Matrix.conjTranspose_apply]
    change (starRingEnd ℂ) (inner ℂ (e j.val) (X (e i.val))) = _
    rw [inner_conj_symm]
    exact hX.isSymmetric (e i.val) (e j.val)
  · intro v
    have hq := hX.inner_nonneg_right (embed v)
    rw [show star v ⬝ᵥ (compression (N := 1) X) *ᵥ v = inner ℂ (embed v) (X (embed v)) by
      dsimp only [compression, embed, dotProduct, Matrix.mulVec]
      simp [Fin.sum_univ_two]
      ring]
    exact hq

private theorem compress_one : compression (N := 1) (1 : Op) = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  unfold compression
  ext i j
  by_cases h : i = j
  · subst j
    unfold e
    simp
  · have hv : (j : ℕ) ≠ i := by
      intro hj
      apply h
      exact Fin.ext hj.symm
    unfold e
    simp [lp.inner_single_right, h, hv]

private theorem compress_add (X Y : Op) :
    compression (N := 1) (X + Y) =
      compression (N := 1) X + compression (N := 1) Y := by
  ext i j
  simp only [Matrix.add_apply]
  change inner ℂ (e i.val) ((X + Y) (e j.val)) =
    inner ℂ (e i.val) (X (e j.val)) + inner ℂ (e i.val) (Y (e j.val))
  simp

private theorem compress_sum {ι : Type} [Fintype ι] (X : ι → Op) :
    compression (N := 1) (∑ i, X i) = ∑ i, compression (N := 1) (X i) := by
  ext i j
  simp only [Matrix.sum_apply]
  change inner ℂ (e i.val) ((∑ k, X k) (e j.val)) =
    ∑ k, inner ℂ (e i.val) (X k (e j.val))
  simp

private theorem compress_finset_sum {ι : Type} (s : Finset ι) (X : ι → Op) :
    compression (N := 1) (s.sum X) = s.sum (fun i => compression (N := 1) (X i)) := by
  ext i j
  simp only [Matrix.sum_apply]
  change inner ℂ (e i.val) ((∑ k ∈ s, X k) (e j.val)) =
    ∑ k ∈ s, inner ℂ (e i.val) (X k (e j.val))
  simp

private theorem compressed_parent {m : ℕ} (F : Fin m → Fin 2 → Op)
    (hF : HasParent F) :
    ∃ G : (Fin m → Fin 2) → Matrix (Fin 2) (Fin 2) ℂ,
      IsPOVM G ∧ ∀ j b,
        (∑ a ∈ Finset.univ.filter (fun a : Fin m → Fin 2 => a j = b), G a) =
          compression (N := 1) (F j b) := by
  obtain ⟨G, hGpos, hGsum, hGmarg⟩ := hF
  let GC : (Fin m → Fin 2) → Matrix (Fin 2) (Fin 2) ℂ := fun a => compression (N := 1) (G a)
  refine ⟨GC, ?_, ?_⟩
  · refine ⟨fun a => compress_pos (G a) (hGpos a), ?_⟩
    rw [← compress_one, ← hGsum, compress_sum]
  · intro j b
    dsimp only [GC]
    let s := Finset.univ.filter (fun a : Fin m → Fin 2 => a j = b)
    change s.sum (fun a => compression (N := 1) (G a)) = compression (N := 1) (F j b)
    rw [← compress_finset_sum s G]
    exact congrArg (compression (N := 1)) (hGmarg j b)

private theorem dual_inner (τ : Set.Icc (0 : ℝ) 1) (M : Op) (u v : H) :
    inner ℂ u (dualLoss τ M v) =
      ∑' k : ℕ, inner ℂ ((stinespring τ u) k)
        (M ((stinespring τ v) k)) := by
  unfold dualLoss
  change inner ℂ u
      ((stinespring τ).adjoint (amplify M (stinespring τ v))) = _
  rw [ContinuousLinearMap.adjoint_inner_right, lp.inner_eq_tsum]
  apply tsum_congr
  intro k
  change inner ℂ ((stinespring τ u) k)
      ((amplify M (stinespring τ v)) k) = _
  rw [amplify_apply]

private theorem dual_rankOne_inner (τ : Set.Icc (0 : ℝ) 1) (μ : ℂ) (u v : H) :
    inner ℂ u (dualLoss τ (InnerProductSpace.rankOne ℂ (coherent μ) (coherent μ)) v) =
      ∑' k : ℕ, inner ℂ ((stinespring τ u) k) (coherent μ) *
        inner ℂ (coherent μ) ((stinespring τ v) k) := by
  rw [dual_inner]
  apply tsum_congr
  intro k
  simp only [InnerProductSpace.rankOne_apply, inner_smul_right]
  ring

theorem vacuum_tensor (v : H) : vacuumEmbedding v = tensor v (e 0) := by
  apply lp.ext
  funext k
  change (lp.single (E := fun _ : ℕ => H) 2 0 v) k = (e 0 k) • v
  unfold e
  simp only [lp.single_apply, Pi.single_apply]
  split_ifs <;> simp_all

private theorem trace_partialTrace (M : Op) (w : K) :
    HasSum (fun n : ℕ => ⟪e n, (M ∘L purePartialTrace w) (e n)⟫_ℂ)
      (∑' k : ℕ, ⟪w k, M (w k)⟫_ℂ) := by
  have hw := lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by norm_num) w
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at hw
  have hr : Summable (fun k => InnerProductSpace.rankOne ℂ (w k) (w k)) := by
    apply Summable.of_norm
    simpa only [InnerProductSpace.norm_rankOne, ← sq] using hw.summable
  let f (k n : ℕ) : ℂ := inner ℂ (w k n) (M (w k) n)
  have hf (k n : ℕ) : f k n = ⟪w k, e n⟫_ℂ * ⟪e n, M (w k)⟫_ℂ := by
    simp only [f, e, lp.inner_single_left, lp.inner_single_right,
      RCLike.inner_apply, map_one, one_mul, mul_one]
    ring
  have hn (k n : ℕ) : ‖f k n‖ = ‖w k n‖ * ‖M (w k) n‖ := by
    simp only [f, RCLike.inner_apply, norm_mul, RCLike.norm_conj, mul_comm]
  have hholder (k : ℕ) := lp.tsum_mul_le_mul_norm
    (by rw [Real.holderConjugate_iff]; norm_num) (w k) (M (w k))
  have habs (k : ℕ) : Summable (fun n => ‖f k n‖) := by
    simpa only [hn] using (hholder k).1
  have hbound (k : ℕ) : (∑' n, ‖f k n‖) ≤ ‖M‖ * ‖w k‖ ^ 2 := by
    simp only [hn]
    calc
      _ ≤ ‖w k‖ * ‖M (w k)‖ := (hholder k).2
      _ ≤ ‖w k‖ * (‖M‖ * ‖w k‖) :=
        mul_le_mul_of_nonneg_left (M.le_opNorm _) (norm_nonneg _)
      _ = _ := by ring
  have hall : Summable (fun p : ℕ × ℕ => f p.1 p.2) := by
    apply Summable.of_norm
    apply (summable_prod_of_nonneg (fun p => norm_nonneg (f p.1 p.2))).2
    exact ⟨habs, Summable.of_nonneg_of_le (fun k => tsum_nonneg (fun n => norm_nonneg _))
      hbound (hw.summable.mul_left ‖M‖)⟩
  have hrow (k : ℕ) : HasSum (f k) ⟪w k, M (w k)⟫_ℂ :=
    lp.hasSum_inner (w k) (M (w k))
  have hcol (n : ℕ) : HasSum (fun k => f k n)
      ⟪e n, (M ∘L purePartialTrace w) (e n)⟫_ℂ := by
    let L := (innerSL ℂ (e n)).comp (M.comp (ContinuousLinearMap.apply ℂ H (e n)))
    have h := hr.hasSum.mapL L
    change HasSum (fun k => ⟪e n, M (InnerProductSpace.rankOne ℂ (w k) (w k) (e n))⟫_ℂ)
      ⟪e n, M ((∑' k, InnerProductSpace.rankOne ℂ (w k) (w k)) (e n))⟫_ℂ at h
    convert h using 1
    · funext k
      rw [hf, InnerProductSpace.rankOne_apply, map_smul, inner_smul_right]
    · rfl
  have ht := hall.hasSum.prod_fiberwise hrow
  have hs := hall.prod_symm.hasSum.prod_fiberwise hcol
  have hswap : (∑' p : ℕ × ℕ, f p.swap.1 p.swap.2) = ∑' p : ℕ × ℕ, f p.1 p.2 :=
    (Equiv.prodComm ℕ ℕ).tsum_eq (fun p : ℕ × ℕ => f p.1 p.2)
  rw [hswap, ← ht.tsum_eq] at hs
  exact hs

private theorem isLossDual_dualLoss (τ : Set.Icc (0 : ℝ) 1) (M : Op) :
    IsLossDual τ M (dualLoss τ M) := by
  intro ψ
  rw [dual_inner]
  have heq : beamSplitter τ.1 τ.2 (tensor ψ (e 0)) = stinespring τ ψ := by
    change _ = beamSplitter τ.1 τ.2 (vacuumEmbedding ψ)
    rw [vacuum_tensor]
  rw [heq]
  exact trace_partialTrace M (stinespring τ ψ)

private theorem eq_dualLoss_of_isLossDual (τ : Set.Icc (0 : ℝ) 1) (M N : Op)
    (h : IsLossDual τ M N) : N = dualLoss τ M := by
  apply ContinuousLinearMap.coe_injective
  apply (ext_inner_map N.toLinearMap (dualLoss τ M).toLinearMap).mp
  intro ψ
  change ⟪N ψ, ψ⟫_ℂ = ⟪dualLoss τ M ψ, ψ⟫_ℂ
  simpa only [inner_conj_symm] using
    congrArg (starRingEnd ℂ) ((h ψ).unique (isLossDual_dualLoss τ M ψ))

private theorem vacuum_fock (n : ℕ) : vacuumEmbedding (e n) = fockPair n 0 := by
  rw [vacuum_tensor]
  rfl

theorem split_zero (τ : Set.Icc (0 : ℝ) 1) : stinespring τ (e 0) = fockPair 0 0 := by
  unfold stinespring
  change (beamSplitter τ.1 τ.2).toLinearIsometry.toContinuousLinearMap
      (vacuumEmbedding (e 0)) = _
  rw [vacuum_fock]
  have hτ : (Real.sqrt τ.1)^2 + (Real.sqrt (1 - τ.1))^2 = 1 := by
    rw [Real.sq_sqrt τ.2.1, Real.sq_sqrt (by linarith [τ.2.2])]
    ring
  change beamUnitary (Real.sqrt τ.1) (Real.sqrt (1 - τ.1)) hτ
      (fockPair 0 0) = _
  rw [beamUnitary_fock]
  unfold fockExpansion fockPair tensor
  simp [lp.single_apply, Pi.single_apply]

theorem split_one (τ : Set.Icc (0 : ℝ) 1) : stinespring τ (e 1) =
    (Real.sqrt τ.1 : ℂ) • fockPair 1 0 +
      (Real.sqrt (1-τ.1) : ℂ) • fockPair 0 1 := by
  unfold stinespring
  change (beamSplitter τ.1 τ.2).toLinearIsometry.toContinuousLinearMap
      (vacuumEmbedding (e 1)) = _
  rw [vacuum_fock]
  have hτ : (Real.sqrt τ.1)^2 + (Real.sqrt (1 - τ.1))^2 = 1 := by
    rw [Real.sq_sqrt τ.2.1, Real.sq_sqrt (by linarith [τ.2.2])]
    ring
  change beamUnitary (Real.sqrt τ.1) (Real.sqrt (1 - τ.1)) hτ
      (fockPair 1 0) = _
  rw [beamUnitary_fock]
  unfold fockExpansion fockPair tensor
  simp [lp.single_apply, Pi.single_apply]
  ac_rfl

theorem split_zero_coord (τ : Set.Icc (0 : ℝ) 1) (k : ℕ) :
    (stinespring τ (e 0)) k = if k = 0 then e 0 else 0 := by
  rw [split_zero]
  apply lp.ext
  funext p
  simp only [fockPair_apply]
  split_ifs <;> simp_all [e, lp.single_apply]

theorem split_one_coord (τ : Set.Icc (0 : ℝ) 1) (k : ℕ) :
    (stinespring τ (e 1)) k =
      if k = 0 then (Real.sqrt τ.1 : ℂ) • e 1
      else if k = 1 then (Real.sqrt (1 - τ.1) : ℂ) • e 0 else 0 := by
  rw [split_one]
  by_cases hk : k = 0
  · subst k
    apply lp.ext
    funext p
    change (Real.sqrt τ.1 : ℂ) * fockPair 1 0 0 p +
        (Real.sqrt (1 - τ.1) : ℂ) * fockPair 0 1 0 p =
      (Real.sqrt τ.1 : ℂ) * e 1 p
    rw [fockPair_apply, fockPair_apply]
    simp [e, lp.single_apply, Pi.single_apply]
  · by_cases hk' : k = 1
    · subst k
      apply lp.ext
      funext p
      change (Real.sqrt τ.1 : ℂ) * fockPair 1 0 1 p +
          (Real.sqrt (1 - τ.1) : ℂ) * fockPair 0 1 1 p =
        (Real.sqrt (1 - τ.1) : ℂ) * e 0 p
      rw [fockPair_apply, fockPair_apply]
      simp [e, lp.single_apply, Pi.single_apply]
    · rw [if_neg hk, if_neg hk']
      apply lp.ext
      funext p
      change (Real.sqrt τ.1 : ℂ) * fockPair 1 0 k p +
          (Real.sqrt (1 - τ.1) : ℂ) * fockPair 0 1 k p = 0
      rw [fockPair_apply, fockPair_apply]
      simp [hk, hk']

-- These input occupations populate only environment sectors zero and one.
private theorem rank_entry (τ : Set.Icc (0 : ℝ) 1) (μ : ℂ) (i j : Fin 2) :
    compression (N := 1) (dualLoss τ (InnerProductSpace.rankOne ℂ (coherent μ) (coherent μ))) i j =
      ∑ k ∈ ({0, 1} : Finset ℕ), inner ℂ ((stinespring τ (e i.val)) k) (coherent μ) *
        inner ℂ (coherent μ) ((stinespring τ (e j.val)) k) := by
  unfold compression
  rw [dual_rankOne_inner]
  apply tsum_eq_sum
  intro k hk
  have hk' : k ≠ 0 ∧ k ≠ 1 := by simpa using hk
  fin_cases i <;> fin_cases j <;>
    simp [split_zero_coord, split_one_coord, hk'.1, hk'.2]

private theorem coherent_entries (x : ℝ) (hx : 0 < x) (z : ℂ) (hz : ‖z‖ = 1) :
    inner ℂ (e 0) (coherent ((Real.sqrt x : ℂ) * z)) = (Real.exp (-x / 2) : ℂ) ∧
    inner ℂ (e 1) (coherent ((Real.sqrt x : ℂ) * z)) =
      (Real.exp (-x / 2) : ℂ) * (Real.sqrt x : ℂ) * z := by
  have hμ : ‖(Real.sqrt x : ℂ) * z‖ ^ 2 = x := by
    rw [norm_mul, hz, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg x), Real.sq_sqrt hx.le]
  have hf (k : ℕ) (μ : ℂ) : inner ℂ (e k) (coherent μ) = coherentCoeff μ k := by
    unfold e
    rw [lp.inner_single_left]
    change coherentCoeff μ k * (starRingEnd ℂ) 1 = _
    simp
  rw [hf, hf]
  constructor
  · simp only [coherentCoeff, hμ, pow_zero, Nat.factorial_zero, Nat.cast_one,
      Real.sqrt_one, Complex.ofReal_one, mul_one, div_one]
  · simp only [coherentCoeff, hμ, pow_one, Nat.factorial_one, Nat.cast_one,
      Real.sqrt_one, Complex.ofReal_one, div_one]
    ring

-- The upper-right entry conjugates the phase in the first inner-product argument.
private theorem compressed_rankOne (τ : Set.Icc (0 : ℝ) 1) (x : ℝ) (hx : 0 < x)
    (z : ℂ) (hz : ‖z‖ = 1) :
    compression (N := 1) (dualLoss τ (InnerProductSpace.rankOne ℂ
      (coherent ((Real.sqrt x : ℂ) * z)) (coherent ((Real.sqrt x : ℂ) * z)))) =
    !![(Real.exp (-x) : ℂ),
        (Real.sqrt τ.1 * Real.exp (-x) * Real.sqrt x : ℝ) * starRingEnd ℂ z;
       (Real.sqrt τ.1 * Real.exp (-x) * Real.sqrt x : ℝ) * z,
        (Real.exp (-x) * (1 - τ.1 + τ.1 * x) : ℝ)] := by
  have h0 := (coherent_entries x hx z hz).1
  have h1 := (coherent_entries x hx z hz).2
  have hc0 : inner ℂ (coherent ((Real.sqrt x : ℂ) * z)) (e 0) =
      (Real.exp (-x / 2) : ℂ) := by
    rw [← inner_conj_symm, h0, Complex.conj_ofReal]
  have hc1 : inner ℂ (coherent ((Real.sqrt x : ℂ) * z)) (e 1) =
      (Real.exp (-x / 2) : ℂ) * (Real.sqrt x : ℂ) * starRingEnd ℂ z := by
    rw [← inner_conj_symm, h1, map_mul, map_mul, Complex.conj_ofReal, Complex.conj_ofReal]
  have ht : (Real.sqrt τ.1 : ℂ) ^ 2 = (τ.1 : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt τ.2.1]
  have hr : (Real.sqrt (1 - τ.1) : ℂ) ^ 2 = (1 - τ.1 : ℝ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by linarith [τ.2.2])]
  have hx' : (Real.sqrt x : ℂ) ^ 2 = (x : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt hx.le]
  have he : (Real.exp (-x / 2) : ℂ) ^ 2 = (Real.exp (-x) : ℂ) := by
    rw [← Complex.ofReal_pow, sq, ← Real.exp_add]
    congr 2
    ring
  have hz' : z * starRingEnd ℂ z = 1 := by
    rw [RCLike.mul_conj, hz]
    norm_num
  ext i j
  rw [rank_entry, Finset.sum_pair (by decide : (0 : ℕ) ≠ 1)]
  fin_cases i <;> fin_cases j <;>
    simp only [split_zero_coord, split_one_coord, ite_true, Nat.zero_ne_one, Nat.one_ne_zero,
      ite_false, inner_smul_left, inner_smul_right, inner_zero_left, inner_zero_right,
      mul_zero, zero_mul, add_zero, Complex.conj_ofReal, h0, h1, hc0, hc1]
  · change (Real.exp (-x / 2) : ℂ) * (Real.exp (-x / 2) : ℂ) = (Real.exp (-x) : ℂ)
    exact (pow_two _).symm.trans he
  · change (Real.exp (-x / 2) : ℂ) * ((Real.sqrt τ.1 : ℂ) *
        ((Real.exp (-x / 2) : ℂ) * (Real.sqrt x : ℂ) * starRingEnd ℂ z)) =
        (Real.sqrt τ.1 * Real.exp (-x) * Real.sqrt x : ℝ) * starRingEnd ℂ z
    rw [Complex.ofReal_mul, Complex.ofReal_mul, ← he]
    ring
  · change ((Real.sqrt τ.1 : ℂ) *
        ((Real.exp (-x / 2) : ℂ) * (Real.sqrt x : ℂ) * z)) * (Real.exp (-x / 2) : ℂ) =
        (Real.sqrt τ.1 * Real.exp (-x) * Real.sqrt x : ℝ) * z
    rw [Complex.ofReal_mul, Complex.ofReal_mul, ← he]
    ring
  · change ((Real.sqrt τ.1 : ℂ) * ((Real.exp (-x / 2) : ℂ) * (Real.sqrt x : ℂ) * z)) *
        ((Real.sqrt τ.1 : ℂ) *
          ((Real.exp (-x / 2) : ℂ) * (Real.sqrt x : ℂ) * starRingEnd ℂ z)) +
        ((Real.sqrt (1 - τ.1) : ℂ) * (Real.exp (-x / 2) : ℂ)) *
          ((Real.sqrt (1 - τ.1) : ℂ) * (Real.exp (-x / 2) : ℂ)) =
        (Real.exp (-x) * (1 - τ.1 + τ.1 * x) : ℝ)
    calc
      _ = (Real.exp (-x / 2) : ℂ) ^ 2 *
          ((Real.sqrt τ.1 : ℂ) ^ 2 * (Real.sqrt x : ℂ) ^ 2 *
            (z * starRingEnd ℂ z) + (Real.sqrt (1 - τ.1) : ℂ) ^ 2) := by ring
      _ = _ := by
        rw [he, ht, hx', hz', hr, mul_one, Complex.ofReal_mul,
          Complex.ofReal_add, Complex.ofReal_mul]
        ring

private def clickMatrix (τ : Set.Icc (0 : ℝ) 1) (x : ℝ) (z : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  let A := Real.exp (-x)
  let a := 1 - A
  let b := Real.sqrt τ.1 * A * Real.sqrt x
  let c := 1 - A * (1 - τ.1 + τ.1 * x)
  !![(a : ℂ), -(b : ℂ) * starRingEnd ℂ z; -(b : ℂ) * z, (c : ℂ)]

private theorem dualLoss_sub (τ : Set.Icc (0 : ℝ) 1) (M N : Op) :
    dualLoss τ (M - N) = dualLoss τ M - dualLoss τ N := by
  have h := dualLoss_add τ (M - N) N
  rw [sub_add_cancel] at h
  exact eq_sub_iff_add_eq.mpr h.symm

private theorem compress_sub (X Y : Op) :
    compression (N := 1) (X - Y) =
      compression (N := 1) X - compression (N := 1) Y := by
  have h := compress_add (X - Y) Y
  rw [sub_add_cancel] at h
  exact eq_sub_iff_add_eq.mpr h.symm

-- The click effect complements the coherent no-click effect.
private theorem compressed_click (τ : Set.Icc (0 : ℝ) 1) (x : ℝ) (hx : 0 < x)
    (z : ℂ) (hz : ‖z‖ = 1) :
    compression (N := 1) (dualLoss τ (onOff ((Real.sqrt x : ℂ) * z) 1)) = clickMatrix τ x z := by
  change compression (N := 1) (dualLoss τ (1 - InnerProductSpace.rankOne ℂ
    (coherent ((Real.sqrt x : ℂ) * z)) (coherent ((Real.sqrt x : ℂ) * z)))) = _
  rw [dualLoss_sub, dualLoss_one, compress_sub, compress_one, compressed_rankOne τ x hx z hz]
  unfold clickMatrix
  ext i j
  fin_cases i <;> fin_cases j <;> simp

private theorem scalar_bounds (τ : Set.Icc (0 : ℝ) 1) (x : ℝ) (hx : 0 < x) :
    let A := Real.exp (-x)
    let a := 1 - A
    let b := Real.sqrt τ.1 * A * Real.sqrt x
    let c := 1 - A * (1 - τ.1 + τ.1 * x)
    0 < a ∧ a ≤ x ∧ c - b ^ 2 / a ≤ x ∧ τ.1 - x ≤ c := by
  dsimp
  have hτ0 : (0 : ℝ) ≤ τ.1 := τ.2.1
  have hτ1 : τ.1 ≤ 1 := τ.2.2
  have hA0 : 0 < Real.exp (-x) := Real.exp_pos _
  have hA1 : Real.exp (-x) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  have hAle : Real.exp (-x) ≤ 1 := hA1.le
  have ha : 0 < 1 - Real.exp (-x) := by linarith
  have hax : 1 - Real.exp (-x) ≤ x := by
    linarith [Real.one_sub_le_exp_neg x]
  have hsq : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt hx.le
  have hτsq : (Real.sqrt τ.1) ^ 2 = τ.1 := Real.sq_sqrt hτ0
  have hδa :
      1 - Real.exp (-x) * (1 - τ.1 + τ.1 * x) -
          (Real.sqrt τ.1 * Real.exp (-x) * Real.sqrt x) ^ 2 /
            (1 - Real.exp (-x)) ≤ 1 - Real.exp (-x) := by
    have hfac : 0 ≤ τ.1 * Real.exp (-x) / (1 - Real.exp (-x)) :=
      div_nonneg (mul_nonneg hτ0 hA0.le) ha.le
    have hid :
        (1 - Real.exp (-x) * (1 - τ.1 + τ.1 * x) -
            (Real.sqrt τ.1 * Real.exp (-x) * Real.sqrt x) ^ 2 /
              (1 - Real.exp (-x))) - (1 - Real.exp (-x)) =
          (τ.1 * Real.exp (-x) / (1 - Real.exp (-x))) *
            ((1 - Real.exp (-x)) - x) := by
      field_simp
      rw [hτsq, hsq]
      ring
    rw [← sub_nonpos, hid]
    exact mul_nonpos_of_nonneg_of_nonpos hfac (sub_nonpos.mpr hax)
  have hc : τ.1 - x ≤ 1 - Real.exp (-x) * (1 - τ.1 + τ.1 * x) := by
    have hτA : τ.1 * Real.exp (-x) ≤ 1 :=
      calc
          τ.1 * Real.exp (-x) ≤ 1 * Real.exp (-x) :=
          mul_le_mul_of_nonneg_right hτ1 hA0.le
        _ ≤ 1 := by simpa using hAle
    nlinarith [mul_nonneg (sub_nonneg.mpr hτ1) ha.le,
      mul_nonneg hx.le (sub_nonneg.mpr hτA)]
  exact ⟨ha, hax, hδa.trans hax, hc⟩

private def quad (H : Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 2 → ℂ) : ℝ :=
  (star v ⬝ᵥ H *ᵥ v).re

private def schurVector (a b : ℝ) (z : ℂ) : Fin 2 → ℂ :=
  ![((b / a : ℝ) : ℂ) * starRingEnd ℂ z, 1]

private theorem common_subeffect_bound
    (a b x : ℝ)
    (zi zj : ℂ) (hzi : ‖zi‖ = 1) (hzj : ‖zj‖ = 1) (hne : zi ≠ zj)
    (H : Matrix (Fin 2) (Fin 2) ℂ) (hH : H.PosSemidef)
    (hqi : quad H (schurVector a b zi) ≤ x)
    (hqj : quad H (schurVector a b zj) ≤ x) :
    (H 1 1).re ≤ 4 * x / ‖zi - zj‖ ^ 2 := by
  have hzi' : zi * starRingEnd ℂ zi = 1 := by
    rw [RCLike.mul_conj, hzi]
    norm_num
  have hzj' : zj * starRingEnd ℂ zj = 1 := by
    rw [RCLike.mul_conj, hzj]
    norm_num
  let p : Fin 2 → ℂ := zi • schurVector a b zi
  let q : Fin 2 → ℂ := zj • schurVector a b zj
  have hscale (z : ℂ) (v : Fin 2 → ℂ) (hz : ‖z‖ = 1) :
      quad H (z • v) = quad H v := by
    have hz' : starRingEnd ℂ z * z = 1 := by
      rw [RCLike.conj_mul, hz]
      norm_num
    have hz'' : star z * z = 1 := by simpa only [starRingEnd_apply] using hz'
    have hc : star (z • v) ⬝ᵥ (H *ᵥ (z • v)) =
        star v ⬝ᵥ (H *ᵥ v) := by
      simp only [star_smul, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul,
        smul_smul]
      rw [mul_comm z (star z), hz'', one_smul]
    dsimp [quad]
    exact congrArg Complex.re hc
  have hp : quad H p ≤ x := by
    dsimp [p]
    rw [hscale zi _ hzi]
    exact hqi
  have hq : quad H q ≤ x := by
    dsimp [q]
    rw [hscale zj _ hzj]
    exact hqj
  have hpar : quad H (p - q) = 2 * quad H p + 2 * quad H q - quad H (p + q) := by
    have hh : star (p - q) ⬝ᵥ (H *ᵥ (p - q)) =
        (2 : ℂ) * (star p ⬝ᵥ (H *ᵥ p)) +
            (2 : ℂ) * (star q ⬝ᵥ (H *ᵥ q)) -
            star (p + q) ⬝ᵥ (H *ᵥ (p + q)) := by
      simp only [star_sub, star_add, Matrix.mulVec_sub, Matrix.mulVec_add,
        sub_dotProduct, dotProduct_sub, add_dotProduct, dotProduct_add]
      ring
    dsimp [quad]
    simpa [map_mul, map_sub] using congrArg Complex.re hh
  have hnon : 0 ≤ quad H (p + q) := by
    exact (Complex.le_def.mp (hH.dotProduct_mulVec_nonneg (p + q))).1
  have hbound : quad H (p - q) ≤ 4 * x := by
    rw [hpar]
    linarith
  have hpq : p - q = ![0, zi - zj] := by
    funext k
    fin_cases k
    · dsimp [p, q, schurVector]
      calc
        zi * ((b / a : ℝ) * starRingEnd ℂ zi) -
            zj * ((b / a : ℝ) * starRingEnd ℂ zj) =
          (b / a : ℝ) * (zi * starRingEnd ℂ zi) -
            (b / a : ℝ) * (zj * starRingEnd ℂ zj) := by ring
        _ = 0 := by rw [hzi', hzj']; ring
    · dsimp [p, q, schurVector]
      simp
  have hentry :
      quad H (![0, zi - zj] : Fin 2 → ℂ) =
        ‖zi - zj‖ ^ 2 * (H 1 1).re := by
    dsimp only [quad, dotProduct, Matrix.mulVec]
    simp [Fin.sum_univ_two, Complex.sq_norm, Complex.normSq, Complex.mul_re]
    ring
  rw [hpq, hentry] at hbound
  have hdist : 0 < ‖zi - zj‖ ^ 2 := by
    have : 0 < ‖zi - zj‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
    positivity
  exact (le_div_iff₀ hdist).2 (by linarith)

private theorem choose_count_bound (k : ℕ) :
    (k : ℝ) ≤ 1 + (Nat.choose k 2 : ℝ) := by
  induction k with
  | zero => norm_num
  | succ k ih =>
      rw [Nat.choose_succ_succ, Nat.choose_one_right]
      norm_num at ih ⊢
      linarith

private theorem residual_quad_le (a b c x : ℝ) (ha : 0 < a)
    (z : ℂ) (hz : ‖z‖ = 1) (H : Matrix (Fin 2) (Fin 2) ℂ)
    (hR : (!![(a : ℂ), -(b : ℂ) * starRingEnd ℂ z;
        -(b : ℂ) * z, (c : ℂ)] - H).PosSemidef)
    (hδ : c - b ^ 2 / a ≤ x) :
    quad H (schurVector a b z) ≤ x := by
  have hqR : 0 ≤ quad
      (!![(a : ℂ), -(b : ℂ) * starRingEnd ℂ z;
        -(b : ℂ) * z, (c : ℂ)] - H) (schurVector a b z) := by
    exact (Complex.le_def.mp (hR.dotProduct_mulVec_nonneg _)).1
  have hsum : quad H (schurVector a b z) + quad
      (!![(a : ℂ), -(b : ℂ) * starRingEnd ℂ z;
        -(b : ℂ) * z, (c : ℂ)] - H) (schurVector a b z) = c - b ^ 2 / a := by
    dsimp only [quad, schurVector, dotProduct, Matrix.mulVec]
    have hzn : z.re ^ 2 + z.im ^ 2 = 1 := by
      have ht : Complex.normSq z = 1 := by
        rw [← Complex.sq_norm, hz]
        norm_num
      simpa [Complex.normSq, pow_two] using ht
    simp [Fin.sum_univ_two, Complex.mul_re]
    field_simp
    ring_nf at hzn ⊢
    linear_combination (-b ^ 2 * a) * hzn
  linarith

private theorem weighted_counting_bound {m : ℕ} (c x Q : ℝ)
    (g : (Fin m → Fin 2) → ℝ) (k : (Fin m → Fin 2) → ℕ)
    (p q : Fin m → Fin m → ℝ)
    (hg : ∀ a, 0 ≤ g a) (hsum : ∑ a, g a = 1)
    (hmc : (m : ℝ) * c = ∑ a, (k a : ℝ) * g a)
    (hpairs : ∑ a, (Nat.choose (k a) 2 : ℝ) * g a =
      ∑ i, ∑ j ∈ Finset.univ.filter (fun j : Fin m => i < j), p i j)
    (hp : ∀ (i j : Fin m), j ∈ Finset.univ.filter (fun j : Fin m => i < j) →
      p i j ≤ 4 * x * q i j)
    (hQ : ∑ i : Fin m, ∑ j ∈ Finset.univ.filter (fun j : Fin m => i < j), q i j = Q) :
    (m : ℝ) * c ≤ 1 + 4 * x * Q := by
  have hweighted : ∑ a, (k a : ℝ) * g a ≤
      ∑ a, (1 + (Nat.choose (k a) 2 : ℝ)) * g a := by
    apply Finset.sum_le_sum
    intro a ha
    exact mul_le_mul_of_nonneg_right (choose_count_bound (k a)) (hg a)
  have hpair : ∑ i, ∑ j ∈ Finset.univ.filter (fun j : Fin m => i < j), p i j ≤
      4 * x * Q := by
    calc
      _ ≤ ∑ i, ∑ j ∈ Finset.univ.filter (fun j : Fin m => i < j),
          4 * x * q i j := by
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro j hj
        exact hp i j hj
      _ = 4 * x * (∑ i : Fin m,
          ∑ j ∈ Finset.univ.filter (fun j : Fin m => i < j), q i j) := by
        simp_rw [← Finset.mul_sum]
      _ = 4 * x * Q := by rw [hQ]
  rw [hmc]
  calc
    ∑ a, (k a : ℝ) * g a ≤
        ∑ a, (1 + (Nat.choose (k a) 2 : ℝ)) * g a := hweighted
    _ = ∑ a, g a + ∑ a, (Nat.choose (k a) 2 : ℝ) * g a := by
      simp_rw [add_mul, one_mul]
      rw [Finset.sum_add_distrib]
    _ = 1 + ∑ a, (Nat.choose (k a) 2 : ℝ) * g a := by rw [hsum]
    _ = 1 + ∑ i, ∑ j ∈ Finset.univ.filter (fun j : Fin m => i < j), p i j := by
      exact congrArg (fun r : ℝ => 1 + r) hpairs
    _ ≤ 1 + 4 * x * Q := by linarith

private def phaseQ {m : ℕ} (z : Fin m → ℂ) : ℝ :=
  ∑ i, ∑ j ∈ Finset.univ.filter (fun j : Fin m => i < j), (‖z i - z j‖ ^ 2)⁻¹

private theorem pair_count {m : ℕ} (ω : Fin m → Fin 2) (r : ℝ) :
    (Nat.choose (Finset.univ.filter (fun i => ω i = 1)).card 2 : ℝ) * r =
      ∑ i, ∑ j ∈ Finset.univ.filter (fun j : Fin m => i < j),
        if ω i = 1 ∧ ω j = 1 then r else 0 := by
  let S := Finset.univ.filter (fun i : Fin m => ω i = 1)
  calc
    _ = ∑ p ∈ (S ×ˢ S).filter (fun p => p.1 < p.2), r := by
      simp only [Finset.sum_const, Finset.card_product_filter_lt, nsmul_eq_mul]
      rfl
    _ = ∑ i ∈ S, ∑ j ∈ S, if i < j then r else 0 := by
      rw [Finset.sum_filter, Finset.sum_product]
    _ = _ := by
      dsimp only [S]
      simp only [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i hi
      by_cases hωi : ω i = 1
      · simp only [hωi, true_and, ite_true]
        apply Finset.sum_congr rfl
        intro j hj
        by_cases hωj : ω j = 1 <;> by_cases hij : i < j <;> simp [hωj, hij]
      · simp [hωi]

private theorem parent_bound {m : ℕ} (a b c x : ℝ) (ha : 0 < a)
    (hδ : c - b ^ 2 / a ≤ x) (z : Fin m → ℂ)
    (hz : ∀ i, ‖z i‖ = 1) (hinj : Function.Injective z)
    (G : (Fin m → Fin 2) → Matrix (Fin 2) (Fin 2) ℂ) (hG : IsPOVM G)
    (hmarg : ∀ i, (∑ ω ∈ Finset.univ.filter (fun ω : Fin m → Fin 2 => ω i = 1),
      G ω) = !![(a : ℂ), -(b : ℂ) * starRingEnd ℂ (z i); -(b : ℂ) * z i, (c : ℂ)]) :
    (m : ℝ) * c ≤ 1 + 4 * x * phaseQ z := by
  let s (i : Fin m) := Finset.univ.filter (fun ω : Fin m → Fin 2 => ω i = 1)
  let t (i j : Fin m) :=
    Finset.univ.filter (fun ω : Fin m → Fin 2 => ω i = 1 ∧ ω j = 1)
  let H (i j : Fin m) := ∑ ω ∈ t i j, G ω
  let g (ω : Fin m → Fin 2) := (G ω 1 1).re
  let k (ω : Fin m → Fin 2) := (Finset.univ.filter (fun i => ω i = 1)).card
  have hpos (i j : Fin m) : (H i j).PosSemidef :=
    Matrix.posSemidef_sum (t i j) (fun ω _ => hG.1 ω)
  have hres (i j : Fin m) :
      (!![(a : ℂ), -(b : ℂ) * starRingEnd ℂ (z i);
        -(b : ℂ) * z i, (c : ℂ)] - H i j).PosSemidef := by
    have hsub : t i j ⊆ s i := by
      intro ω hω
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hω).2.1⟩
    have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun ω _ _ => (hG.1 ω).nonneg)
    rw [hmarg i] at hle
    exact Matrix.le_iff.mp hle
  have hres' (i j : Fin m) :
      (!![(a : ℂ), -(b : ℂ) * starRingEnd ℂ (z j);
        -(b : ℂ) * z j, (c : ℂ)] - H i j).PosSemidef := by
    have ht : t i j = t j i := by
      ext ω
      simp only [t, Finset.mem_filter, Finset.mem_univ, true_and, and_comm]
    simpa only [H, ht] using hres j i
  have hg : ∀ ω, 0 ≤ g ω := fun ω =>
    (Complex.nonneg_iff.mp (hG.1 ω).diag_nonneg).1
  have hsum : ∑ ω, g ω = 1 := by
    have h := congrArg (fun T : Matrix (Fin 2) (Fin 2) ℂ => (T 1 1).re) hG.2
    simpa [g, Matrix.sum_apply] using h
  have hm (i : Fin m) : ∑ ω ∈ s i, g ω = c := by
    have h := congrArg (fun T : Matrix (Fin 2) (Fin 2) ℂ => (T 1 1).re) (hmarg i)
    simpa [s, g, Matrix.sum_apply] using h
  have hmc : (m : ℝ) * c = ∑ ω, (k ω : ℝ) * g ω := by
    calc
      _ = ∑ i : Fin m, c := by simp
      _ = ∑ i : Fin m, ∑ ω ∈ s i, g ω := by
        apply Finset.sum_congr rfl
        intro i hi
        exact (hm i).symm
      _ = ∑ ω, ∑ i : Fin m, if ω i = 1 then g ω else 0 := by
        simp only [s, Finset.sum_filter]
        rw [Finset.sum_comm]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro ω hω
        rw [← Finset.sum_filter]
        simp [k]
  have hpairs : ∑ ω, (Nat.choose (k ω) 2 : ℝ) * g ω =
      ∑ i, ∑ j ∈ Finset.univ.filter (fun j : Fin m => i < j), (H i j 1 1).re := by
    calc
      _ = ∑ ω, ∑ i, ∑ j ∈ Finset.univ.filter (fun j : Fin m => i < j),
          if ω i = 1 ∧ ω j = 1 then g ω else 0 := by
        exact Finset.sum_congr rfl (fun ω _ => pair_count ω (g ω))
      _ = ∑ i, ∑ j ∈ Finset.univ.filter (fun j : Fin m => i < j),
          ∑ ω, if ω i = 1 ∧ ω j = 1 then g ω else 0 := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl (fun i _ => Finset.sum_comm)
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        simp only [H, t, Matrix.sum_apply, Complex.re_sum, Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro ω hω
        by_cases hωij : ω i = 1 ∧ ω j = 1 <;> simp [hωij, g]
  apply weighted_counting_bound c x (phaseQ z) g k
    (fun i j => (H i j 1 1).re) (fun i j => (‖z i - z j‖ ^ 2)⁻¹)
    hg hsum hmc hpairs
  · intro i j hj
    have hij : i ≠ j := ne_of_lt (Finset.mem_filter.mp hj).2
    have hne : z i ≠ z j := fun h => hij (hinj h)
    have hi := residual_quad_le a b c x ha (z i) (hz i) (H i j) (hres i j) hδ
    have hj' := residual_quad_le a b c x ha (z j) (hz j) (H i j) (hres' i j) hδ
    simpa only [div_eq_mul_inv] using
      common_subeffect_bound a b x (z i) (z j) (hz i) (hz j) hne (H i j) (hpos i j) hi hj'
  · rfl

private theorem phaseQ_pos {m : ℕ} (hm : 2 ≤ m) (z : Fin m → ℂ)
    (hinj : Function.Injective z) : 0 < phaseQ z := by
  let i : Fin m := ⟨0, by omega⟩
  let j : Fin m := ⟨1, by omega⟩
  have hij : i < j := by change (0 : ℕ) < 1; omega
  have hne : z i ≠ z j := fun h => (ne_of_lt hij) (hinj h)
  unfold phaseQ
  apply Finset.sum_pos' (fun _ _ => Finset.sum_nonneg (fun _ _ => by positivity))
  refine ⟨i, Finset.mem_univ _, ?_⟩
  apply Finset.sum_pos' (fun _ _ => by positivity)
  refine ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩, ?_⟩
  exact inv_pos.mpr (pow_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hne)) _)

private def chosenX {m : ℕ} (τ : Set.Icc (0 : ℝ) 1) (z : Fin m → ℂ) : ℝ :=
  ((m : ℝ) * τ.1 - 1) / (2 * ((m : ℝ) + 4 * phaseQ z))

private theorem stronger {m : ℕ} (hm : 2 ≤ m) (τ : Set.Icc (0 : ℝ) 1) (hτ : 0 < τ.1)
    (hgap : 1 < (m : ℝ) * τ.1) (z : Fin m → ℂ)
    (hz : ∀ i, ‖z i‖ = 1) (hinj : Function.Injective z) :
    (∀ j, IsBinaryPOVM (onOff ((Real.sqrt (chosenX τ z) : ℂ) * z j))) ∧
      ¬ HasParent (fun j b => dualLoss τ (onOff ((Real.sqrt (chosenX τ z) : ℂ) * z j) b)) := by
  have hQ := phaseQ_pos hm z hinj
  have hm0 : 0 < (m : ℝ) :=
    (mul_pos_iff_of_pos_right hτ).mp (lt_trans zero_lt_one hgap)
  have hden : 0 < (m : ℝ) + 4 * phaseQ z := by linarith
  let x := chosenX τ z
  have hx : 0 < x := div_pos (sub_pos.mpr hgap) (by positivity)
  let a := 1 - Real.exp (-x)
  let b := Real.sqrt τ.1 * Real.exp (-x) * Real.sqrt x
  let c := 1 - Real.exp (-x) * (1 - τ.1 + τ.1 * x)
  have hs := scalar_bounds τ x hx
  refine ⟨fun j => onOff_binary _, ?_⟩
  intro hparent
  obtain ⟨G, hG, hmarg⟩ := compressed_parent _ hparent
  have hcount : (m : ℝ) * c ≤ 1 + 4 * x * phaseQ z := by
    apply parent_bound a b c x hs.1 hs.2.2.1 z hz hinj G hG
    intro i
    change (∑ ω ∈ Finset.univ.filter (fun ω : Fin m → Fin 2 => ω i = 1), G ω) =
      clickMatrix τ x (z i)
    exact (hmarg i 1).trans (compressed_click τ x hx (z i) (hz i))
  have hxid : x * (2 * ((m : ℝ) + 4 * phaseQ z)) = (m : ℝ) * τ.1 - 1 :=
    div_mul_cancel₀ _ (by positivity)
  have hc : τ.1 - x ≤ c := hs.2.2.2
  have hmargin : ((m : ℝ) * τ.1 - 1) / 2 ≤ (m : ℝ) * c - 1 - 4 * x * phaseQ z := by
    nlinarith [mul_le_mul_of_nonneg_left hc hm0.le]
  linarith

theorem result : claim := by
  intro n hn
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hm0 : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
  let z (j : Fin (n + 1)) : ℂ :=
    (Circle.exp (2 * Real.pi * (j.val : ℝ) / ((n + 1 : ℕ) : ℝ)) : ℂ)
  have hz (j : Fin (n + 1)) : ‖z j‖ = 1 := Circle.norm_coe _
  have hr (j : Fin (n + 1)) :
      2 * Real.pi * (j.val : ℝ) / ((n + 1 : ℕ) : ℝ) ∈ Set.Ico 0 (2 * Real.pi) := by
    refine ⟨div_nonneg (mul_nonneg Real.two_pi_pos.le (Nat.cast_nonneg _)) hm0.le, ?_⟩
    apply (div_lt_iff₀ hm0).mpr
    exact mul_lt_mul_of_pos_left (by exact_mod_cast j.isLt) Real.two_pi_pos
  have hinj : Function.Injective z := by
    intro i j hij
    have hangle := Circle.exp_injOn_Ico (a := 0) (b := 2 * Real.pi)
      (by simp) (hr i) (hr j) (Subtype.ext hij)
    apply Fin.ext
    exact_mod_cast mul_left_cancel₀ Real.two_pi_pos.ne' ((div_left_inj' hm0.ne').mp hangle)
  have hτ : 0 < (inverseTransmissivity n hn).1 := by
    change 0 < 1 / (n : ℝ)
    positivity
  have hgap : 1 < ((n + 1 : ℕ) : ℝ) * (inverseTransmissivity n hn).1 := by
    change 1 < ((n + 1 : ℕ) : ℝ) * (1 / (n : ℝ))
    rw [mul_one_div]
    apply (lt_div_iff₀ hn0).mpr
    push_cast
    linarith
  refine ⟨fun j => onOff ((Real.sqrt (chosenX (inverseTransmissivity n hn) z) : ℂ) * z j), ?_⟩
  obtain ⟨hM, hno⟩ := stronger (by omega) (inverseTransmissivity n hn) hτ hgap z hz hinj
  refine ⟨hM, ⟨fun j b => dualLoss (inverseTransmissivity n hn)
    (onOff ((Real.sqrt (chosenX (inverseTransmissivity n hn) z) : ℂ) * z j) b),
    fun j b => isLossDual_dualLoss _ _⟩, ?_⟩
  intro N hN
  have heq : N = fun j b => dualLoss (inverseTransmissivity n hn)
      (onOff ((Real.sqrt (chosenX (inverseTransmissivity n hn) z) : ℂ) * z j) b) := by
    funext j b
    exact eq_dualLoss_of_isLossDual _ _ _ (hN j b)
  rwa [heq]

end D5.S3.Quantum.Measurement.PureLossIncompatibility
