/- GID: D5/S3/Quantum/Measurement/PureLossIncompatibility
   generality: I
   mirror-B: D5/B/S3/Quantum/Measurement/PureLossIncompatibility
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Pure-loss dual effects admit an exact compressed binary incompatibility certificate. -/

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

private theorem lift_exists (M : Op) :
    ∃ T : K →L[ℂ] K, ∀ (w : K) (k : ℕ), (T w) k = M (w k) := by
  let f : K →ₗ[ℂ] K :=
    { toFun := fun w =>
        ⟨fun k => M (w k), by
          apply memℓp_gen
          have hs := lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by norm_num) w
          simp only [ENNReal.toReal_ofNat, Real.rpow_two] at hs ⊢
          apply Summable.of_nonneg_of_le (fun k => sq_nonneg _)
          · intro k
            calc
              ‖M (w k)‖ ^ 2 ≤ (‖M‖ * ‖w k‖) ^ 2 := by gcongr; exact M.le_opNorm _
              _ = ‖w k‖ ^ 2 * ‖M‖ ^ 2 := by ring
          · exact (hs.summable.mul_right (‖M‖ ^ 2)).congr (fun k => by ring)⟩
      map_add' := by
        intro x y
        apply lp.ext
        funext k
        change M ((x + y).1 k) = _
        rw [show (x + y).1 k = x.1 k + y.1 k by rfl]
        exact M.map_add _ _
      map_smul' := by
        intro c x
        apply lp.ext
        funext k
        change M ((c • x).1 k) = _
        rw [show (c • x).1 k = c • x.1 k by rfl]
        exact M.map_smul c (x k) }
  have hbound : ∀ w : K, ‖f w‖ ≤ ‖M‖ * ‖w‖ := by
    intro w
    have h := lp.norm_mono (p := (2 : ℝ≥0∞)) (x := f w) (y := (‖M‖ : ℂ) • w)
      (by norm_num)
      (fun k => by
        change ‖M (w k)‖ ≤ ‖((‖M‖ : ℂ) • w).1 k‖
        rw [show ((‖M‖ : ℂ) • w).1 k = (‖M‖ : ℂ) • w.1 k by rfl,
          norm_smul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (norm_nonneg M)]
        exact M.le_opNorm (w k))
    simpa only [norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg M)] using h
  let T : K →L[ℂ] K := f.mkContinuous ‖M‖ hbound
  refine ⟨T, ?_⟩
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

def onOff (μ : ℂ) (b : Fin 2) : Op :=
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
  rw [ContinuousLinearMap.isPositive_iff]
  constructor
  · exact LinearMap.IsSymmetric.one.sub (InnerProductSpace.isSymmetric_rankOne_self v)
  · intro x
    simp only [_root_.sub_apply, one_apply_eq_self,
      InnerProductSpace.rankOne_apply, inner_sub_left, inner_smul_left]
    have hi := (norm_inner_le_norm (𝕜 := ℂ) (E := H) v x)
    have hi0 : ‖inner ℂ v x‖ ≤ ‖x‖ := by simpa [hv] using hi
    have hi' : ‖inner ℂ v x‖ ^ 2 ≤ ‖x‖ ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hi0
    rw [RCLike.conj_mul, inner_self_eq_norm_sq_to_K]
    have hreal : 0 ≤ ‖x‖ ^ 2 - ‖inner ℂ v x‖ ^ 2 := by linarith
    have hc := Complex.zero_le_real.mpr hreal
    rw [Complex.ofReal_sub, Complex.ofReal_pow, Complex.ofReal_pow] at hc
    exact hc

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
  rw [amplify_apply, _root_.add_apply]
  rw [_root_.add_apply]
  rw [show ((amplify M) w + (amplify N) w).1 k =
      (amplify M w) k + (amplify N w) k by rfl]
  rw [amplify_apply, amplify_apply]

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
  exact (by
    rw [show amplify M = amplify M from rfl]
    exact (by
      have h := amplify_pos M hM
      exact h.adjoint_conj (stinespring τ)))

private theorem dualLoss_add (τ : Loss) (M N : Op) :
    dualLoss τ (M + N) = dualLoss τ M + dualLoss τ N := by
  unfold dualLoss
  rw [amplify_add]
  apply ContinuousLinearMap.ext
  intro x
  change (stinespring τ).adjoint ((amplify M + amplify N) (stinespring τ x)) =
    (stinespring τ).adjoint (amplify M (stinespring τ x)) +
      (stinespring τ).adjoint (amplify N (stinespring τ x))
  rw [_root_.add_apply]
  exact (stinespring τ).adjoint.map_add _ _

private theorem dualLoss_one (τ : Loss) : dualLoss τ 1 = 1 := by
  unfold dualLoss
  rw [stinespring_eq_iso, amplify_one]
  have hcomp : (1 : K →L[ℂ] K) ∘L (stinespringIso τ).toContinuousLinearMap =
      (stinespringIso τ).toContinuousLinearMap := by
    ext x
    rfl
  rw [hcomp]
  exact LinearIsometry.adjoint_comp_self (stinespringIso τ)

private theorem dualLoss_binary (τ : Loss) (M : Fin 2 → Op)
    (hM : IsBinaryPOVM M) : IsBinaryPOVM (fun b => dualLoss τ (M b)) := by
  refine ⟨fun b => dualLoss_pos τ (M b) (hM.1 b), ?_⟩
  change dualLoss τ (M 0) + dualLoss τ (M 1) = 1
  rw [← dualLoss_add, hM.2, dualLoss_one]


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
      simp [dotProduct, Matrix.mulVec, compress, embed, Fin.sum_univ_two,
         ]
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
  classical
  induction s using Finset.induction_on with
  | empty =>
      ext i j
      simp [compress]
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha, compress_add, ih]

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

private theorem pair_inner (m n k : ℕ) (μ : ℂ) :
    inner ℂ (fockPair m n k) (coherent μ) =
      if k = n then inner ℂ (e m) (coherent μ) else 0 := by
  rw [fock_slice]
  split_ifs <;> simp

private theorem vacuum_fock (n : ℕ) : vacuumEmbedding (e n) = fockPair n 0 := by
  apply lp.ext
  funext k
  simp only [vacuumEmbedding, lp.singleContinuousLinearMap_apply, fockPair, tensor]
  apply lp.ext
  funext l
  simp [e, lp.single_apply, Pi.single_apply]

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

private theorem rank_entry00 (τ : Loss) (μ : ℂ) :
    inner ℂ (e 0)
      (dualLoss τ (InnerProductSpace.rankOne ℂ (coherent μ) (coherent μ)) (e 0)) =
      inner ℂ (e 0) (coherent μ) * inner ℂ (coherent μ) (e 0) := by
  rw [dual_rankOne_inner]
  have h0 : ∀ k : ℕ, inner ℂ ((stinespring τ (e 0)) k) (coherent μ) *
      inner ℂ (coherent μ) ((stinespring τ (e 0)) k) =
      if k = 0 then inner ℂ (e 0) (coherent μ) *
        inner ℂ (coherent μ) (e 0) else 0 := by
    intro k
    rw [split_zero_coord]
    by_cases h : k = 0
    · subst k; simp
    · simp [h]
  simp_rw [h0]
  rw [tsum_eq_single 0]
  · simp
  · intro k hk
    simp [hk]

private theorem rank_entry01 (τ : Loss) (μ : ℂ) :
    inner ℂ (e 0)
      (dualLoss τ (InnerProductSpace.rankOne ℂ (coherent μ) (coherent μ)) (e 1)) =
      (Real.sqrt τ.1 : ℂ) * inner ℂ (e 0) (coherent μ) *
        inner ℂ (coherent μ) (e 1) := by
  rw [dual_rankOne_inner]
  have h0 : ∀ k : ℕ, inner ℂ ((stinespring τ (e 0)) k) (coherent μ) *
      inner ℂ (coherent μ) ((stinespring τ (e 1)) k) =
      if k = 0 then (Real.sqrt τ.1 : ℂ) * inner ℂ (e 0) (coherent μ) *
        inner ℂ (coherent μ) (e 1) else 0 := by
    intro k
    rw [split_zero_coord, split_one_coord]
    split_ifs <;> simp
    ring
  simp_rw [h0]
  rw [tsum_eq_single 0]
  · simp
  · intro k hk
    simp [hk]

private theorem rank_entry10 (τ : Loss) (μ : ℂ) :
    inner ℂ (e 1)
      (dualLoss τ (InnerProductSpace.rankOne ℂ (coherent μ) (coherent μ)) (e 0)) =
      (Real.sqrt τ.1 : ℂ) * inner ℂ (e 1) (coherent μ) *
        inner ℂ (coherent μ) (e 0) := by
  rw [dual_rankOne_inner]
  have h0 : ∀ k : ℕ, inner ℂ ((stinespring τ (e 1)) k) (coherent μ) *
      inner ℂ (coherent μ) ((stinespring τ (e 0)) k) =
      if k = 0 then (Real.sqrt τ.1 : ℂ) * inner ℂ (e 1) (coherent μ) *
        inner ℂ (coherent μ) (e 0) else 0 := by
    intro k
    rw [split_one_coord, split_zero_coord]
    split_ifs <;> simp
  simp_rw [h0]
  rw [tsum_eq_single 0]
  · simp
  · intro k hk
    simp [hk]

private theorem rank_entry11 (τ : Loss) (μ : ℂ) :
    inner ℂ (e 1)
      (dualLoss τ (InnerProductSpace.rankOne ℂ (coherent μ) (coherent μ)) (e 1)) =
      (τ.1 : ℂ) * inner ℂ (e 1) (coherent μ) * inner ℂ (coherent μ) (e 1) +
        ((1 - τ.1 : ℝ) : ℂ) * inner ℂ (e 0) (coherent μ) *
          inner ℂ (coherent μ) (e 0) := by
  rw [dual_rankOne_inner]
  have h0 : ∀ k : ℕ, inner ℂ ((stinespring τ (e 1)) k) (coherent μ) *
      inner ℂ (coherent μ) ((stinespring τ (e 1)) k) =
      if k = 0 then (τ.1 : ℂ) * inner ℂ (e 1) (coherent μ) *
          inner ℂ (coherent μ) (e 1)
      else if k = 1 then ((1 - τ.1 : ℝ) : ℂ) * inner ℂ (e 0) (coherent μ) *
          inner ℂ (coherent μ) (e 0) else 0 := by
    intro k
    rw [split_one_coord]
    split_ifs <;> simp
    · ring_nf
      rw [← Complex.ofReal_pow, Real.sq_sqrt τ.2.1]
      ring
    · ring_nf
      rw [← Complex.ofReal_pow, Real.sq_sqrt (by linarith [τ.2.2]), Complex.ofReal_sub, Complex.ofReal_one]
      ring
  simp_rw [h0]
  rw [tsum_eq_sum (s := {0, 1})]
  · simp
  · intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
    simp [hk.1, hk.2]

end D5.S3.Quantum.Measurement.PureLossIncompatibility
