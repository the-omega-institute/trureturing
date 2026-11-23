/- GID: D5/S3/Quantum/Recovery/LocalCompression/ProductNoiseDecoder
   generality: G
   mirror-B: D5/B/S3/Quantum/Recovery/LocalCompression/ProductNoiseDecoder
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Faithful product-noise marginal shifts and their exact joint decoder error. -/

import D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction
import D5.S3.Quantum.Recovery.QubitCenteredTransport
import D5.S3.Quantum.ProcessReconstruction.HiddenProcessSemigroup

/-! A faithful fixed marginal admits every traceless Hermitian decoder direction. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Quantum.Recovery.LocalCompression.ProductNoiseDecoder

open _root_.Matrix
open scoped CStarAlgebra ComplexOrder MatrixOrder Kronecker Matrix.Norms.L2Operator
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Foundation.FiniteDiamondDistance (referenceState)
open D5.S3.Quantum.Foundation.FiniteTraceDistance
  (traceNorm traceNorm_add_le traceDistance traceDistance_le_one)
open D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction
  (act amp amp_entry amp_smul state_nonempty)
open D5.S3.Quantum.Divergence.UmegakiReferenceTransport (amp_kronecker)
open D5.S3.Quantum.Information.PartialTraceMutualInformation
  (density_posSemidef marginalRight partialTraceRight productState)
open D5.S3.Quantum.Recovery.QubitResidualRounding (traceNorm_tensor)
open D5.S3.Quantum.Entanglement.ConicalDesignConcurrenceComparability (traceNorm_smul_nonneg)
open UnitaryReconstruction.GibbsHiddenProcess (mix mix_entry identity reset reset_act)

universe ur ub um

variable {R : Type ur} {B : Type ub} {M : Type um}
  [Fintype R] [DecidableEq R] [Fintype B] [DecidableEq B] [Fintype M] [DecidableEq M]

private abbrev raw {n : Type*} [Fintype n] [DecidableEq n] (ρ : DensityState n) :
    Matrix n n ℂ := CStarMatrix.ofMatrix.symm ρ.1

private lemma exists_shifted_density (τ : DensityState B) (hτ : (raw τ).PosDef)
    (K : Matrix B B ℂ) (hK : K.IsHermitian) (htr : K.trace = 0) :
    ∃ L : ℝ, 0 < L ∧ ∃ σ : DensityState B, raw σ = raw τ - L⁻¹ • K := by
  let : Nonempty B := state_nonempty ⟨hτ.posSemidef, τ.trace_eq_one⟩
  obtain ⟨m, hm, hfloor⟩ := (CFC.exists_pos_algebraMap_le_iff (raw τ)).mpr
    (fun x hx => hτ.isStrictlyPositive.spectrum_pos hx)
  let L : ℝ := (‖K‖ + 1) / m
  have hL : 0 < L := div_pos (by positivity) hm
  have hcap : ‖K‖ ≤ L * m := by
    dsimp [L]
    rw [div_mul_cancel₀ _ hm.ne']
    exact le_add_of_nonneg_right zero_le_one
  have hKle : K ≤ (L * m) • (1 : Matrix B B ℂ) := by
    have hupper := IsSelfAdjoint.le_algebraMap_norm_self K (show IsSelfAdjoint K from hK)
    simpa only [Algebra.algebraMap_eq_smul_one] using
      hupper.trans (algebraMap_mono (Matrix B B ℂ) hcap)
  have hshift : L⁻¹ • K ≤ raw τ := by
    calc
      L⁻¹ • K ≤ L⁻¹ • ((L * m) • (1 : Matrix B B ℂ)) :=
        smul_le_smul_of_nonneg_left hKle (inv_nonneg.mpr hL.le)
      _ = m • (1 : Matrix B B ℂ) := by rw [smul_smul, ← mul_assoc, inv_mul_cancel₀ hL.ne', one_mul]
      _ ≤ raw τ := by simpa only [Algebra.algebraMap_eq_smul_one] using hfloor
  let Z := raw τ - L⁻¹ • K
  have hZ : 0 ≤ Z := sub_nonneg.mpr hshift
  have hZtr : Z.trace = 1 := by
    rw [show Z.trace = (raw τ - L⁻¹ • K).trace from rfl, trace_sub, trace_smul,
      htr, smul_zero, sub_zero]
    exact τ.2.2
  exact ⟨L, hL, ⟨CStarMatrix.ofMatrix Z, map_nonneg CStarMatrix.ofMatrixStarAlgEquiv hZ, hZtr⟩, rfl⟩

private lemma act_mixed_reset (T : QuantumChannel B B) (σ : DensityState B)
    (p : ℝ) (hp : 0 ≤ p) (hp' : p ≤ 1) (X : Matrix B B ℂ) :
    act ((mix p hp hp' (reset σ) identity).comp T) X =
      (1 - p) • act T X + p • (X.trace • raw σ) := by
  have htrace : (act T X).trace = X.trace := T.trace_preserving (CStarMatrix.ofMatrix X)
  ext i j
  change Foundation.FiniteTraceDistance.act (mix p hp hp' (reset σ) identity)
    (act T X) i j = _
  rw [mix_entry, reset_act, htrace]
  change (p : ℂ) * (X.trace • raw σ) i j + ((1 - p : ℝ) : ℂ) * act T X i j =
    ((1 - p) • act T X + p • (X.trace • raw σ)) i j
  simp only [Matrix.add_apply, Matrix.smul_apply, Complex.real_smul, smul_eq_mul, add_comm]

private lemma amp_mixed_reset (T : QuantumChannel B B) (σ : DensityState B)
    (p : ℝ) (hp : 0 ≤ p) (hp' : p ≤ 1) (X : Matrix (R × B) (R × B) ℂ) :
    amp ((mix p hp hp' (reset σ) identity).comp T) X =
      (1 - p) • amp T X + p • (partialTraceRight X ⊗ₖ raw σ) := by
  ext ⟨r, i⟩ ⟨s, j⟩
  let block : Matrix B B ℂ := fun a b => X (r, a) (s, b)
  rw [amp_entry]
  change act ((mix p hp hp' (reset σ) identity).comp T) block i j = _
  rw [act_mixed_reset T σ p hp hp' block]
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.kroneckerMap_apply,
    amp_entry T X r s i j]
  rfl

private lemma amp_add (T : QuantumChannel B B) (X Y : Matrix (R × B) (R × B) ℂ) :
    amp T (X + Y) = amp T X + amp T Y := by
  exact (CStarMatrix.ofMatrixₗ.symm.toLinearMap.comp
    ((D5.S3.Quantum.Foundation.FiniteDiamondDistance.referenceLinear T).comp
      CStarMatrix.ofMatrixₗ.toLinearMap)).map_add X Y

private lemma traceNorm_real_smul {n : Type*} [Fintype n]
    (c : ℝ) (hc : 0 ≤ c) (X : Matrix n n ℂ) :
    traceNorm (c • X) = c * traceNorm X := by
  classical
  convert traceNorm_smul_nonneg X c hc using 2

/-- A decoder perturbation through the same memory realizes the prescribed
signed marginal direction and controls the full joint reconstruction error. -/
theorem faithful_decoder_marginal_shift
    (E : QuantumChannel B M) (D : QuantumChannel M B)
    (τ : DensityState B) (hτ : (CStarMatrix.ofMatrix.symm τ.1).PosDef)
    (hfix : (D.comp E).mapState τ = τ)
    (K : Matrix B B ℂ) (hK : K.IsHermitian) (htr : K.trace = 0) :
    ∃ (L : ℝ) (hL : 0 < L) (σ : DensityState B),
      CStarMatrix.ofMatrix.symm σ.1 = CStarMatrix.ofMatrix.symm τ.1 - L⁻¹ • K ∧
      ∀ (ε : ℝ) (hε : 0 < ε) (_hε' : ε ≤ 1) (hp : ε * L ≤ 1),
        let T := D.comp E
        let Dε := (mix (ε * L) (mul_nonneg hε.le hL.le) hp
          (reset σ) identity).comp D
        let Tε := Dε.comp E
        act Tε (CStarMatrix.ofMatrix.symm τ.1) = CStarMatrix.ofMatrix.symm τ.1 - ε • K ∧
        ∀ (ω : DensityState R) (ρ : DensityState (R × B)),
          let ρR : DensityState R := marginalRight ρ
          let X := (1 - ε) • (raw ω ⊗ₖ raw τ) + ε • raw ρ
          let H := raw ρ - amp T (raw ρ) + raw ω ⊗ₖ K
          let Hε := ε⁻¹ • (X - amp Tε X)
          Hε = H + (ε * L) • (amp T (raw ρ) - raw ρR ⊗ₖ raw τ) +
              ε • ((raw ρR - raw ω) ⊗ₖ K) ∧
          traceNorm (Hε - H) / 2 ≤
            ε * (L + traceDistance ρR ω * traceNorm K) := by
  obtain ⟨L, hL, σ, hσ⟩ := exists_shifted_density τ hτ K hK htr
  refine ⟨L, hL, σ, hσ, ?_⟩
  intro ε hε _ hp T Dε Tε
  have ht : act T (raw τ) = raw τ := congrArg raw hfix
  have hcomp : Tε = (mix (ε * L) (mul_nonneg hε.le hL.le) hp (reset σ) identity).comp T := rfl
  have hre : (ε * L) * L⁻¹ = ε := by rw [mul_assoc, mul_inv_cancel₀ hL.ne', mul_one]
  have hshift : act Tε (raw τ) = raw τ - ε • K := by
    rw [hcomp, act_mixed_reset, ht, show (raw τ).trace = 1 from τ.2.2, one_smul, hσ,
      smul_sub, smul_smul, hre, ← add_sub_assoc, ← add_smul, sub_add_cancel, one_smul]
  refine ⟨hshift, ?_⟩
  intro ω ρ ρR X H Hε
  have hraw : partialTraceRight (raw ρ) = raw ρR := rfl
  have hY : amp Tε (raw ρ) =
      (1 - ε * L) • amp T (raw ρ) + (ε * L) • (raw ρR ⊗ₖ raw σ) := by
    rw [hcomp, amp_mixed_reset, hraw]
  have hbase : amp Tε (raw ω ⊗ₖ raw τ) = raw ω ⊗ₖ (raw τ - ε • K) := by
    rw [amp_kronecker, hshift]
  have hidentity : Hε = H + (ε * L) • (amp T (raw ρ) - raw ρR ⊗ₖ raw τ) +
      ε • ((raw ρR - raw ω) ⊗ₖ K) := by
    dsimp only [Hε, X, H]
    rw [amp_add, amp_smul, amp_smul, hbase, hY, hσ]
    ext i j
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.kroneckerMap_apply, Complex.real_smul, Complex.ofReal_sub,
      Complex.ofReal_mul, Complex.ofReal_one, Complex.ofReal_inv]
    have hεc : (ε : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hε.ne'
    have hLc : (L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hL.ne'
    field_simp [hεc, hLc]
    ring
  refine ⟨hidentity, ?_⟩
  let Y := amp T (raw ρ) - raw ρR ⊗ₖ raw τ
  let Z := (raw ρR - raw ω) ⊗ₖ K
  have hdiff : Hε - H = (ε * L) • Y + ε • Z := by rw [hidentity]; abel
  have hYn : traceNorm Y / 2 ≤ 1 :=
    traceDistance_le_one (referenceState T ρ) (productState ρR τ)
  have hZn : traceNorm Z / 2 = traceDistance ρR ω * traceNorm K := by
    dsimp only [Z]
    rw [traceNorm_tensor]
    unfold traceDistance
    ring
  rw [hdiff]
  calc
    traceNorm ((ε * L) • Y + ε • Z) / 2 ≤
        (traceNorm ((ε * L) • Y) + traceNorm (ε • Z)) / 2 :=
      div_le_div_of_nonneg_right (traceNorm_add_le _ _) (by norm_num)
    _ = (ε * L) * (traceNorm Y / 2) + ε * (traceNorm Z / 2) := by
      rw [traceNorm_real_smul _ (mul_nonneg hε.le hL.le), traceNorm_real_smul _ hε.le]
      ring
    _ ≤ ε * (L + traceDistance ρR ω * traceNorm K) := by
      rw [hZn, mul_add]
      exact add_le_add_left
        (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hYn (mul_nonneg hε.le hL.le)) _

#print axioms faithful_decoder_marginal_shift

end D5.S3.Quantum.Recovery.LocalCompression.ProductNoiseDecoder
