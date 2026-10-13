/- GID: D5/S3/Quantum/Measurement/PureLossIncompatibility
   generality: I
   mirror-B: D5/B/S3/Quantum/Measurement/PureLossIncompatibility
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Pure-loss dual effects admit an exact compressed binary incompatibility certificate. -/

import Mathlib.Analysis.Normed.Lp.lpHolder
import D5.S3.Quantum.QuantumChannels.FockAttenuator.BeamSplitter
import D5.S3.Quantum.QuantumChannels.FockAttenuator.Attenuator
import D5.S3.Quantum.QuantumChannels.ConcealmentKernelNecessityRefutation

noncomputable section
open scoped BigOperators InnerProductSpace ENNReal NNReal ComplexOrder MatrixOrder
open Matrix
open D5.S3.Quantum.QuantumChannels.FockAttenuator.BeamSplitter
open D5.S3.Quantum.QuantumChannels.FockAttenuator.Attenuator
open D5.S3.Quantum.QuantumChannels.ConcealmentKernelNecessityRefutation (IsPOVM)

namespace D5.S3.Quantum.Measurement.PureLossIncompatibility

abbrev H := lp (fun _ : ℕ => ℂ) 2
abbrev K := lp (fun _ : ℕ => H) 2
abbrev Op := H →L[ℂ] H
abbrev Loss := Set.Icc (0 : ℝ) 1

private def e (k : ℕ) : H :=
  lp.single (E := fun _ : ℕ => ℂ) 2 k (1 : ℂ)

-- Amplification acts on the retained vector at each environment coordinate.
private theorem lift_exists (M : Op) :
    ∃ T : K →L[ℂ] K, ∀ (w : K) (k : ℕ), (T w) k = M (w k) := by
  refine ⟨lp.mapCLM 2 (fun _ : ℕ => M) (norm_nonneg M) (fun _ => le_rfl), ?_⟩
  intro w k
  rfl

def amplify (M : Op) : K →L[ℂ] K :=
  Classical.choose (lift_exists M)

private theorem amplify_apply (M : Op) (w : K) (k : ℕ) :
    (amplify M w) k = M (w k) :=
  Classical.choose_spec (lift_exists M) w k

def vacuumEmbedding : H →L[ℂ] K :=
  lp.singleContinuousLinearMap
    (𝕜 := ℂ) (E := fun _ : ℕ => H) (p := 2) 0

def stinespring (τ : Loss) : H →L[ℂ] K :=
  (beamSplitter τ.1 τ.2).toLinearIsometry.toContinuousLinearMap ∘L vacuumEmbedding

def dualLoss (τ : Loss) (M : Op) : Op :=
  (stinespring τ).adjoint ∘L amplify M ∘L stinespring τ

def IsBinaryPOVM (M : Fin 2 → Op) : Prop :=
  (∀ b, (M b).IsPositive) ∧ M 0 + M 1 = 1

def HasParent {m : ℕ} (F : Fin m → Fin 2 → Op) : Prop :=
  ∃ G : (Fin m → Fin 2) → Op,
    (∀ a, (G a).IsPositive) ∧
    (∑ a, G a) = 1 ∧
    ∀ j b,
      (∑ a ∈ Finset.univ.filter
        (fun a : Fin m → Fin 2 => a j = b), G a) = F j b

def inverseTransmissivity (n : ℕ) (hn : 1 ≤ n) : Loss :=
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
      ¬ HasParent (fun j b =>
        dualLoss (inverseTransmissivity n hn) (M j b))

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
    simp only [InnerProductSpace.rankOne_apply, inner_smul_right, e,
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
      simp only [onOff]
      norm_num
      exact rankOne_complement_pos _ hv
  · ext v
    simp [onOff]

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

private def stinespringIso (τ : Loss) : H →ₗᵢ[ℂ] K :=
  (beamSplitter τ.1 τ.2).toLinearIsometry.comp vacuumIso

private theorem stinespring_eq_iso (τ : Loss) :
    stinespring τ = (stinespringIso τ).toContinuousLinearMap := by
  ext v k
  rfl

private theorem amplify_pos (M : Op) (hM : M.IsPositive) : (amplify M).IsPositive := by
  rw [ContinuousLinearMap.isPositive_iff]
  constructor
  · intro x y
    rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
    apply tsum_congr
    intro k
    change inner ℂ (amplify M x k) (y k) = inner ℂ (x k) (amplify M y k)
    rw [amplify_apply, amplify_apply]
    exact hM.isSymmetric (x k) (y k)
  · intro x
    rw [lp.inner_eq_tsum]
    apply tsum_nonneg
    intro k
    change inner ℂ (amplify M x k) (x k) ≥ 0
    rw [amplify_apply]
    exact hM.inner_nonneg_left _

private theorem dualLoss_pos (τ : Loss) (M : Op) (hM : M.IsPositive) :
    (dualLoss τ M).IsPositive := by
  unfold dualLoss
  exact (amplify_pos M hM).adjoint_conj (stinespring τ)

private theorem dualLoss_add (τ : Loss) (M N : Op) :
    dualLoss τ (M + N) = dualLoss τ M + dualLoss τ N := by
  unfold dualLoss
  simp only [amplify_add, ContinuousLinearMap.comp_add, ContinuousLinearMap.add_comp]

private theorem dualLoss_one (τ : Loss) : dualLoss τ 1 = 1 := by
  unfold dualLoss
  rw [stinespring_eq_iso, amplify_one]
  rw [show (1 : K →L[ℂ] K) = ContinuousLinearMap.id ℂ K from rfl,
    ContinuousLinearMap.id_comp]
  exact LinearIsometry.adjoint_comp_self (stinespringIso τ)

private theorem dualLoss_binary (τ : Loss) (M : Fin 2 → Op)
    (hM : IsBinaryPOVM M) : IsBinaryPOVM (fun b => dualLoss τ (M b)) := by
  refine ⟨fun b => dualLoss_pos τ (M b) (hM.1 b), ?_⟩
  change dualLoss τ (M 0) + dualLoss τ (M 1) = 1
  rw [← dualLoss_add, hM.2, dualLoss_one]

-- Compression pulls quadratic forms back through the two-dimensional Fock embedding.
private def compress (X : Op) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => inner ℂ (e i.val) (X (e j.val))

private def embed (v : Fin 2 → ℂ) : H := ∑ i, v i • e i.val

private theorem compress_pos (X : Op) (hX : X.IsPositive) : (compress X).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · rw [Matrix.IsHermitian]
    ext i j
    simp only [Matrix.conjTranspose_apply, compress]
    change (starRingEnd ℂ) (inner ℂ (e j.val) (X (e i.val))) = _
    rw [inner_conj_symm]
    exact hX.isSymmetric (e i.val) (e j.val)
  · intro v
    have hq := hX.inner_nonneg_right (embed v)
    rw [show star v ⬝ᵥ (compress X) *ᵥ v = inner ℂ (embed v) (X (embed v)) by
      simp [dotProduct, Matrix.mulVec, compress, embed, Fin.sum_univ_two]
      ring]
    exact hq

private theorem compress_one : compress (1 : Op) = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  by_cases h : i = j
  · subst j
    simp [compress, e]
  · have hv : (j : ℕ) ≠ i := by
      intro hj
      apply h
      exact Fin.ext hj.symm
    simp [compress, e, lp.inner_single_right, h, hv]

private theorem compress_add (X Y : Op) : compress (X + Y) = compress X + compress Y := by
  ext i j
  simp [compress]

private theorem compress_sum {ι : Type} [Fintype ι] (X : ι → Op) :
    compress (∑ i, X i) = ∑ i, compress (X i) := by
  ext i j
  simp [compress, Matrix.sum_apply]

private theorem compress_finset_sum {ι : Type} (s : Finset ι) (X : ι → Op) :
    compress (s.sum X) = s.sum (fun i => compress (X i)) := by
  ext i j
  simp [compress, Matrix.sum_apply]

private theorem compressed_parent {m : ℕ} (F : Fin m → Fin 2 → Op)
    (hF : HasParent F) :
    ∃ G : (Fin m → Fin 2) → Matrix (Fin 2) (Fin 2) ℂ,
      IsPOVM G ∧ ∀ j b,
        (∑ a ∈ Finset.univ.filter (fun a : Fin m → Fin 2 => a j = b), G a) =
          compress (F j b) := by
  obtain ⟨G, hGpos, hGsum, hGmarg⟩ := hF
  let GC : (Fin m → Fin 2) → Matrix (Fin 2) (Fin 2) ℂ := fun a => compress (G a)
  refine ⟨GC, ?_, ?_⟩
  · refine ⟨fun a => compress_pos (G a) (hGpos a), ?_⟩
    rw [← compress_one, ← hGsum, compress_sum]
  · intro j b
    dsimp only [GC]
    let s := Finset.univ.filter (fun a : Fin m → Fin 2 => a j = b)
    change s.sum (fun a => compress (G a)) = compress (F j b)
    rw [← compress_finset_sum s G]
    exact congrArg compress (hGmarg j b)

private theorem dual_inner (τ : Loss) (M : Op) (u v : H) :
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

private theorem dual_rankOne_inner (τ : Loss) (μ : ℂ) (u v : H) :
    inner ℂ u (dualLoss τ (InnerProductSpace.rankOne ℂ (coherent μ) (coherent μ)) v) =
      ∑' k : ℕ, inner ℂ ((stinespring τ u) k) (coherent μ) *
        inner ℂ (coherent μ) ((stinespring τ v) k) := by
  rw [dual_inner]
  apply tsum_congr
  intro k
  simp only [InnerProductSpace.rankOne_apply, inner_smul_right]
  ring

private theorem fock_slice (m n k : ℕ) :
    fockPair m n k = if k = n then e m else 0 := by
  simp only [fockPair, tensor, e, lp.single_apply, Pi.single_apply]
  split_ifs <;> simp_all

private theorem vacuum_tensor (v : H) : vacuumEmbedding v = tensor v (e 0) := by
  apply lp.ext
  funext k
  simp only [vacuumEmbedding, lp.singleContinuousLinearMap_apply, tensor]
  change (lp.single (E := fun _ : ℕ => H) 2 0 v) k = (e 0 k) • v
  simp only [lp.single_apply, e, Pi.single_apply]
  split_ifs <;> simp_all

private theorem vacuum_fock (n : ℕ) : vacuumEmbedding (e n) = fockPair n 0 := by
  rw [vacuum_tensor]
  rfl

private theorem split_zero (τ : Loss) : stinespring τ (e 0) = fockPair 0 0 := by
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
  simp [fockExpansion, fockPair, tensor, lp.single_apply, Pi.single_apply]

private theorem split_one (τ : Loss) : stinespring τ (e 1) =
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
  simp [fockExpansion, fockPair, tensor, lp.single_apply, Pi.single_apply]
  ac_rfl

private theorem split_zero_coord (τ : Loss) (k : ℕ) :
    (stinespring τ (e 0)) k = if k = 0 then e 0 else 0 := by
  rw [split_zero, fock_slice]

private theorem split_one_coord (τ : Loss) (k : ℕ) :
    (stinespring τ (e 1)) k =
      if k = 0 then (Real.sqrt τ.1 : ℂ) • e 1
      else if k = 1 then (Real.sqrt (1 - τ.1) : ℂ) • e 0 else 0 := by
  rw [split_one]
  simp only [lp.coeFn_add, lp.coeFn_smul, Pi.add_apply, Pi.smul_apply, fock_slice]
  split_ifs <;> simp_all

-- These input occupations populate only environment sectors zero and one.
private theorem rank_entry (τ : Loss) (μ : ℂ) (i j : Fin 2) :
    compress (dualLoss τ (InnerProductSpace.rankOne ℂ (coherent μ) (coherent μ))) i j =
      ∑ k ∈ ({0, 1} : Finset ℕ), inner ℂ ((stinespring τ (e i.val)) k) (coherent μ) *
        inner ℂ (coherent μ) ((stinespring τ (e j.val)) k) := by
  unfold compress
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
private theorem compressed_rankOne (τ : Loss) (x : ℝ) (hx : 0 < x)
    (z : ℂ) (hz : ‖z‖ = 1) :
    compress (dualLoss τ (InnerProductSpace.rankOne ℂ
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

private def clickMatrix (τ : Loss) (x : ℝ) (z : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  let A := Real.exp (-x)
  let a := 1 - A
  let b := Real.sqrt τ.1 * A * Real.sqrt x
  let c := 1 - A * (1 - τ.1 + τ.1 * x)
  !![(a : ℂ), -(b : ℂ) * starRingEnd ℂ z; -(b : ℂ) * z, (c : ℂ)]

private theorem dualLoss_sub (τ : Loss) (M N : Op) :
    dualLoss τ (M - N) = dualLoss τ M - dualLoss τ N := by
  have h := dualLoss_add τ (M - N) N
  rw [sub_add_cancel] at h
  exact eq_sub_iff_add_eq.mpr h.symm

private theorem compress_sub (X Y : Op) : compress (X - Y) = compress X - compress Y := by
  have h := compress_add (X - Y) Y
  rw [sub_add_cancel] at h
  exact eq_sub_iff_add_eq.mpr h.symm

-- The click effect complements the coherent no-click effect.
private theorem compressed_click (τ : Loss) (x : ℝ) (hx : 0 < x)
    (z : ℂ) (hz : ‖z‖ = 1) :
    compress (dualLoss τ (onOff ((Real.sqrt x : ℂ) * z) 1)) = clickMatrix τ x z := by
  change compress (dualLoss τ (1 - InnerProductSpace.rankOne ℂ
    (coherent ((Real.sqrt x : ℂ) * z)) (coherent ((Real.sqrt x : ℂ) * z)))) = _
  rw [dualLoss_sub, dualLoss_one, compress_sub, compress_one, compressed_rankOne τ x hx z hz]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [clickMatrix]

private theorem scalar_bounds (τ : Loss) (x : ℝ) (hx : 0 < x) :
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
      simp only [dotProduct, Fin.sum_univ_two, Matrix.mulVec, Pi.smul_apply,
        StarModule.star_smul, smul_eq_mul]
      ring_nf
      have h1 : star z * star v 0 * H 0 0 * z * v 0 =
          star v 0 * H 0 0 * v 0 := by
        calc
          _ = (star z * z) * (star v 0 * H 0 0 * v 0) := by ring
          _ = _ := by rw [hz'']; simp
      have h2 : star z * star v 0 * z * H 0 1 * v 1 =
          star v 0 * H 0 1 * v 1 := by
        calc
          _ = (star z * z) * (star v 0 * H 0 1 * v 1) := by ring
          _ = _ := by rw [hz'']; simp
      have h3 : v 0 * star z * z * star v 1 * H 1 0 =
          v 0 * star v 1 * H 1 0 := by
        calc
          _ = (star z * z) * (v 0 * star v 1 * H 1 0) := by ring
          _ = _ := by rw [hz'']; simp
      have h4 : v 1 * star z * z * star v 1 * H 1 1 =
          v 1 * star v 1 * H 1 1 := by
        calc
          _ = (star z * z) * (v 1 * star v 1 * H 1 1) := by ring
          _ = _ := by rw [hz'']; simp
      have h5 : star z * z * v 0 * star v 1 * H 1 0 =
          v 0 * star v 1 * H 1 0 := by
        calc
          _ = (star z * z) * (v 0 * star v 1 * H 1 0) := by ring
          _ = _ := by rw [hz'']; simp
      have h6 : star z * z * v 1 * star v 1 * H 1 1 =
          v 1 * star v 1 * H 1 1 := by
        calc
          _ = (star z * z) * (v 1 * star v 1 * H 1 1) := by ring
          _ = _ := by rw [hz'']; simp
      rw [h1, h2, h5, h6]
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
      have hs : star (p - q) = star p - star q := by
        funext k
        simp
      have hs' : star (p + q) = star p + star q := by
        funext k
        simp
      rw [hs, hs']
      simp only [dotProduct, Fin.sum_univ_two, Matrix.mulVec, Pi.sub_apply, Pi.add_apply]
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
  have hdiag : (H 1 1).im = 0 := by
    have hh := (Matrix.IsHermitian.ext_iff.mp hH.isHermitian)
      (1 : Fin 2) (1 : Fin 2)
    have ht := congrArg Complex.im hh
    simp at ht
    linarith
  have hentry :
      quad H (![0, zi - zj] : Fin 2 → ℂ) =
        ‖zi - zj‖ ^ 2 * (H 1 1).re := by
    dsimp [quad]
    simp only [dotProduct, Fin.sum_univ_two, Matrix.mulVec, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    simp only [mul_zero]
    rw [show H (1 : Fin 2) (1 : Fin 2) =
        ((H (1 : Fin 2) (1 : Fin 2)).re : ℂ) by
      apply Complex.ext
      · rfl
      · simp [hdiag]]
    simp [Complex.sq_norm, Complex.normSq, Complex.mul_re]
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
    dsimp [quad, schurVector]
    have hzn : z.re ^ 2 + z.im ^ 2 = 1 := by
      have ht : Complex.normSq z = 1 := by
        rw [← Complex.sq_norm, hz]
        norm_num
      simpa [Complex.normSq, pow_two] using ht
    simp [dotProduct, Fin.sum_univ_two, Matrix.mulVec, Complex.mul_re]
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


end D5.S3.Quantum.Measurement.PureLossIncompatibility
