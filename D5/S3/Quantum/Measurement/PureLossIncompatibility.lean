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

end D5.S3.Quantum.Measurement.PureLossIncompatibility
