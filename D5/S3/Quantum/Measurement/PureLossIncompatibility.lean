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
open D5.S3.Quantum.QuantumChannels.FockAttenuator.BeamSplitter
open D5.S3.Quantum.QuantumChannels.FockAttenuator.Attenuator
open D5.S3.Quantum.QuantumChannels.ConcealmentKernelNecessityRefutation (IsPOVM)

namespace D5.S3.Quantum.Measurement.PureLossIncompatibility

abbrev H := lp (fun _ : ℕ => ℂ) 2
abbrev K := lp (fun _ : ℕ => H) 2
abbrev Op := H →L[ℂ] H
abbrev Loss := Set.Icc (0 : ℝ) 1

def e (k : ℕ) : H :=
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
  have h_FockAttProbe_coherent_norm_sq (α : ℂ) (n : ℕ) :
      ‖coherentCoeff α n‖ ^ 2 =
        Real.exp (-‖α‖ ^ 2 / 2) ^ 2 * (‖α‖ ^ 2) ^ n / (n.factorial : ℝ) := by
    rw [coherentCoeff, norm_div, norm_mul, norm_pow]
    simp only [Complex.norm_real, Real.norm_eq_abs, Real.abs_exp,
      abs_of_nonneg (Real.sqrt_nonneg _), div_pow, mul_pow,
      Real.sq_sqrt (Nat.cast_nonneg n.factorial), pow_right_comm ‖α‖ n 2]
  have h_FockAttProbe_coherent_hasSum (α : ℂ) :
      HasSum (fun n : ℕ => ‖coherentCoeff α n‖ ^ 2) 1 := by
    have hseries : HasSum (fun n : ℕ => (‖α‖ ^ 2) ^ n / (n.factorial : ℝ))
        (Real.exp (‖α‖ ^ 2)) := by
      simpa only [Real.exp_eq_exp_ℝ] using
        (NormedSpace.expSeries_div_hasSum_exp (‖α‖ ^ 2))
    have hs := hseries.mul_left (Real.exp (-‖α‖ ^ 2 / 2) ^ 2)
    have he : Real.exp (-‖α‖ ^ 2 / 2) ^ 2 * Real.exp (‖α‖ ^ 2) = 1 := by
      rw [sq, ← Real.exp_add, ← Real.exp_add]
      ring_nf
      exact Real.exp_zero
    have hs' : HasSum (fun n : ℕ => ‖coherentCoeff α n‖ ^ 2)
        (Real.exp (-‖α‖ ^ 2 / 2) ^ 2 * Real.exp (‖α‖ ^ 2)) :=
      HasSum.congr_fun hs (fun n => by rw [h_FockAttProbe_coherent_norm_sq]; ring)
    rwa [he] at hs'
  have hn := lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞)) (by norm_num) (coherent μ)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at hn
  have hs : ‖coherent μ‖ ^ 2 = 1 := hn.trans (h_FockAttProbe_coherent_hasSum μ).tsum_eq
  nlinarith [norm_nonneg (coherent μ)]


private theorem rankOne_complement_pos (v : H) (hv : ‖v‖ = 1) :
    (1 - InnerProductSpace.rankOne ℂ v v).IsPositive := by
  rw [ContinuousLinearMap.isPositive_iff]
  constructor
  · exact LinearMap.IsSymmetric.one.sub (InnerProductSpace.isSymmetric_rankOne_self v)
  · intro x
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply,
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
  rw [amplify_apply, ContinuousLinearMap.add_apply]
  rw [ContinuousLinearMap.add_apply]
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
  rw [ContinuousLinearMap.add_apply]
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

end D5.S3.Quantum.Measurement.PureLossIncompatibility
