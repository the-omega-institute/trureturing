/- GID: D5/S3/Quantum/Recovery/LocalCompression/SingularProductNoiseDecoder
   generality: G
   mirror-B: D5/B/S3/Quantum/Recovery/LocalCompression/SingularProductNoiseDecoder
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Physical same-memory decoder perturbations at a singular product reference. -/

import D5.S3.Quantum.Recovery.LocalCompression.ProductNoiseDecoder

/-! A quadratic preparation correction permits off-diagonal marginal directions at a singular
reference. The decoder mixes in the corrected preparation at the square root of the noise weight. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Quantum.Recovery.LocalCompression.SingularProductNoiseDecoder

open _root_.Matrix
open scoped CStarAlgebra ComplexOrder MatrixOrder Kronecker Matrix.Norms.L2Operator
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Foundation.FiniteDiamondDistance (referenceLinear referenceState)
open D5.S3.Quantum.Foundation.FiniteTraceDistance
  (traceNorm traceNorm_add_le traceNorm_of_posSemidef traceDistance_le_one)
open D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction
  (act amp amp_entry amp_smul)
open D5.S3.Quantum.Divergence.UmegakiReferenceTransport (amp_kronecker)
open D5.S3.Quantum.Information.PartialTraceMutualInformation
  (density_posSemidef marginalRight partialTraceRight productState)
open D5.S3.Quantum.Recovery.QubitResidualRounding (traceNorm_tensor)
open D5.S3.Quantum.Entanglement.ConicalDesignConcurrenceComparability (traceNorm_smul_nonneg)
open UnitaryReconstruction.GibbsHiddenProcess (mix mix_entry identity reset reset_act)

universe ur up uq um

variable {R : Type ur} {P : Type up} {Q : Type uq} {M : Type um}
  [Fintype R] [DecidableEq R] [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]
  [Fintype M] [DecidableEq M]

local notation:max "raw" => CStarMatrix.ofMatrix.symm

private lemma le_norm_one {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (h : A.IsHermitian) : A ≤ ‖A‖ • (1 : Matrix n n ℂ) := by
  simpa only [Algebra.algebraMap_eq_smul_one] using
    IsSelfAdjoint.le_algebraMap_norm_self A (show IsSelfAdjoint A from h)

private lemma schur_of_floor
    (A : Matrix P P ℂ) (B : Matrix P Q ℂ) (D : Matrix Q Q ℂ)
    (a : ℝ) (ha : 0 < a) (hA : a • (1 : Matrix P P ℂ) ≤ A)
    (hD : (a⁻¹ * ‖B‖ ^ 2) • (1 : Matrix Q Q ℂ) ≤ D) :
    (fromBlocks A B Bᴴ D).PosSemidef := by
  have hfloor : IsStrictlyPositive (a • (1 : Matrix P P ℂ)) :=
    IsStrictlyPositive.smul ha isStrictlyPositive_one
  have hpos : A.PosDef := (hfloor.of_le hA).posDef
  letI := hpos.isUnit.invertible
  apply (PosSemidef.fromBlocks₁₁ B D hpos).mpr
  have hinv : A⁻¹ ≤ a⁻¹ • (1 : Matrix P P ℂ) := by
    have h := CStarAlgebra.ringInverse_le_ringInverse hA hfloor
    rw [← Matrix.nonsing_inv_eq_ringInverse, ← Matrix.nonsing_inv_eq_ringInverse] at h
    have hscalar : (a • (1 : Matrix P P ℂ))⁻¹ = a⁻¹ • (1 : Matrix P P ℂ) := by
      letI : Invertible (a : ℂ) := invertibleOfNonzero (Complex.ofReal_ne_zero.mpr ha.ne')
      simp [show a • (1 : Matrix P P ℂ) = (a : ℂ) • (1 : Matrix P P ℂ) by
        ext i j
        simp [Complex.real_smul, smul_eq_mul],
        Matrix.inv_smul, invOf_eq_inv, Matrix.inv_one, ← Complex.ofReal_inv,
        Complex.coe_smul]
    exact h.trans_eq hscalar
  have hcongr : Bᴴ * A⁻¹ * B ≤ a⁻¹ • (Bᴴ * B) := by
    have h := (Matrix.le_iff.mp hinv).conjTranspose_mul_mul_same B
    apply Matrix.le_iff.mpr
    convert h using 1
    simp [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul]
  have hgram : Bᴴ * B ≤ (‖B‖ ^ 2) • (1 : Matrix Q Q ℂ) := by
    simpa only [Matrix.l2_opNorm_conjTranspose_mul_self, pow_two] using
      le_norm_one (Bᴴ * B) (isHermitian_conjTranspose_mul_self B)
  have hbound := smul_le_smul_of_nonneg_left hgram (inv_nonneg.mpr ha.le)
  rw [smul_smul] at hbound
  exact Matrix.le_iff.mp (hcongr.trans (hbound.trans hD))

private lemma replacement_density
    (τ : DensityState (P ⊕ Q)) (hτ : raw τ.1 = fromBlocks (raw τ.1).toBlocks₁₁ 0 0 0)
    (m : ℝ) (hm : 0 < m) (hfloor : m • (1 : Matrix P P ℂ) ≤ (raw τ.1).toBlocks₁₁)
    (K : Matrix (P ⊕ Q) (P ⊕ Q) ℂ) (hK : K.IsHermitian) (htr : K.trace = 0)
    (hQQ : K.toBlocks₂₂ ≤ 0)
    (C : ℝ) (hC : 1 + 2 * ‖K.toBlocks₁₂‖ ^ 2 / m ≤ C) :
    let Z := fromBlocks (0 : Matrix P P ℂ) 0 0 (1 : Matrix Q Q ℂ) -
      (Fintype.card Q : ℝ) • raw τ.1
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ η : ℝ, 0 < η → η ≤ δ →
      ∃ σ : DensityState (P ⊕ Q), raw σ.1 = raw τ.1 - η • K + (C * η ^ 2) • Z := by
  intro Z
  let S := (raw τ.1).toBlocks₁₁
  let k : ℝ := Fintype.card Q
  let δ := min 1 (min (m / (4 * (‖K.toBlocks₁₁‖ + 1))) (1 / (4 * (C * k + 1))))
  have hk : 0 ≤ k := by dsimp [k]; positivity
  have hCp : 0 < C := lt_of_lt_of_le (by positivity) hC
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδ₁ : δ ≤ 1 := min_le_left _ _
  refine ⟨δ, hδ, hδ₁, fun η hη hηδ => ?_⟩
  have hη₁ : η ≤ 1 := hηδ.trans hδ₁
  have hηK : η * ‖K.toBlocks₁₁‖ ≤ m / 4 := by
    have h := hηδ.trans ((min_le_right _ _).trans (min_le_left _ _))
    have hh := (le_div_iff₀ (by positivity : 0 < 4 * (‖K.toBlocks₁₁‖ + 1))).mp h
    nlinarith [norm_nonneg K.toBlocks₁₁]
  have hηk : C * η ^ 2 * k ≤ 1 / 4 := by
    have h := hηδ.trans ((min_le_right _ _).trans (min_le_right _ _))
    have hh := (le_div_iff₀ (by positivity : 0 < 4 * (C * k + 1))).mp h
    have hη₂ : η ^ 2 ≤ η := by nlinarith [mul_nonneg hη.le (sub_nonneg.mpr hη₁)]
    have hprod := mul_le_mul_of_nonneg_left hη₂ (mul_nonneg hCp.le hk)
    nlinarith
  let A := (1 - C * η ^ 2 * k) • S - η • K.toBlocks₁₁
  let B := (-η) • K.toBlocks₁₂
  let D := (C * η ^ 2) • (1 : Matrix Q Q ℂ) - η • K.toBlocks₂₂
  have hA : (m / 2) • (1 : Matrix P P ℂ) ≤ A := by
    have hscale : 0 ≤ 1 - C * η ^ 2 * k := by linarith
    have hlower := smul_le_smul_of_nonneg_left hfloor hscale
    have hupper := smul_le_smul_of_nonneg_left
      (le_norm_one K.toBlocks₁₁ (hK.submatrix Sum.inl)) hη.le
    rw [smul_smul] at hlower hupper
    have hdiff := sub_le_sub hlower hupper
    rw [← sub_smul] at hdiff
    refine (smul_le_smul_of_nonneg_right ?_ zero_le_one).trans hdiff
    nlinarith [mul_le_mul_of_nonneg_right hηk hm.le]
  have hB : ‖B‖ = η * ‖K.toBlocks₁₂‖ := by
    simp [B, norm_smul, Real.norm_eq_abs, abs_of_pos hη]
  have hD : ((m / 2)⁻¹ * ‖B‖ ^ 2) • (1 : Matrix Q Q ℂ) ≤ D := by
    have hscalar : (m / 2)⁻¹ * ‖B‖ ^ 2 ≤ C * η ^ 2 := by
      rw [hB, mul_pow]
      have hsmall : (m / 2)⁻¹ * ‖K.toBlocks₁₂‖ ^ 2 ≤ C := by
        rw [inv_div]
        linarith [show 2 / m * ‖K.toBlocks₁₂‖ ^ 2 = 2 * ‖K.toBlocks₁₂‖ ^ 2 / m by ring]
      calc
        _ = ((m / 2)⁻¹ * ‖K.toBlocks₁₂‖ ^ 2) * η ^ 2 := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hsmall (sq_nonneg η)
    refine (smul_le_smul_of_nonneg_right hscalar zero_le_one).trans ?_
    exact le_sub_comm.mp (by
      simpa [D] using smul_le_smul_of_nonneg_left hQQ hη.le)
  have hblock : (raw τ.1 - η • K + (C * η ^ 2) • Z) = fromBlocks A B Bᴴ D := by
    ext (i | i) (j | j)
    all_goals
      simp [A, B, D, S, Z, k, Matrix.toBlocks₁₁, Matrix.toBlocks₁₂, Matrix.toBlocks₂₂,
        hτ, Matrix.conjTranspose_apply, Complex.real_smul, ← Complex.star_def, hK.apply]
      <;> ring
  have hZtr : Z.trace = 0 := by
    have hproj : (fromBlocks (0 : Matrix P P ℂ) 0 0 (1 : Matrix Q Q ℂ)).trace =
        (Fintype.card Q : ℂ) := by
      simp [Matrix.trace, Fintype.sum_sum_type]
    change ((fromBlocks (0 : Matrix P P ℂ) 0 0 (1 : Matrix Q Q ℂ)) - k • raw τ.1).trace = 0
    rw [trace_sub, trace_smul, hproj, show (raw τ.1).trace = 1 from τ.2.2]
    simp [k, Complex.real_smul]
  have htrace : (raw τ.1 - η • K + (C * η ^ 2) • Z).trace = 1 := by
    rw [trace_add, trace_sub, trace_smul, trace_smul, htr, hZtr,
      show (raw τ.1).trace = 1 from τ.2.2]
    simp
  have hpos : 0 ≤ raw τ.1 - η • K + (C * η ^ 2) • Z := by
    rw [hblock]
    exact (schur_of_floor A B D (m / 2) (by positivity) hA hD).nonneg
  exact ⟨⟨CStarMatrix.ofMatrix _, map_nonneg CStarMatrix.ofMatrixStarAlgEquiv hpos, htrace⟩, rfl⟩

omit [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q] in
private lemma act_mix_reset {B : Type*} [Fintype B] [DecidableEq B]
    (T : QuantumChannel B B) (σ : DensityState B) (p : ℝ) (hp : 0 ≤ p) (hp₁ : p ≤ 1)
    (X : Matrix B B ℂ) :
    act ((mix p hp hp₁ (reset σ) identity).comp T) X =
      (1 - p) • act T X + p • (X.trace • raw σ.1) := by
  have htrace : (act T X).trace = X.trace := T.trace_preserving (CStarMatrix.ofMatrix X)
  ext i j
  change Foundation.FiniteTraceDistance.act (mix p hp hp₁ (reset σ) identity)
    (act T X) i j = _
  rw [mix_entry, reset_act, htrace]
  change (p : ℂ) * (X.trace • raw σ.1) i j + ((1 - p : ℝ) : ℂ) * act T X i j =
    ((1 - p) • act T X + p • (X.trace • raw σ.1)) i j
  simp only [Matrix.add_apply, Matrix.smul_apply, Complex.real_smul, smul_eq_mul, add_comm]

/-- The exact residual correction at noise weight η² and its uniform half trace-norm bound. -/
def SingularJointErrorExpansion (T Tη : QuantumChannel (P ⊕ Q) (P ⊕ Q))
    (τ σ : DensityState (P ⊕ Q)) (K Z : Matrix (P ⊕ Q) (P ⊕ Q) ℂ) (C η : ℝ) : Prop :=
  ∀ (ω : DensityState R) (ρ : DensityState (R × (P ⊕ Q))),
    let X := (1 - η ^ 2) • (raw ω.1 ⊗ₖ raw τ.1) + η ^ 2 • raw ρ.1
    let H := raw ρ.1 - amp T (raw ρ.1) + raw ω.1 ⊗ₖ K
    let Hη := (η ^ 2)⁻¹ • (X - amp Tη X)
    Hη - H = η • (amp T (raw ρ.1) - raw (marginalRight ρ).1 ⊗ₖ raw σ.1) -
        η ^ 2 • (raw ω.1 ⊗ₖ K) - ((1 - η ^ 2) * C * η) • (raw ω.1 ⊗ₖ Z) ∧
    traceNorm (Hη - H) / 2 ≤ η * (1 + (traceNorm K + C * traceNorm Z) / 2)

/-- A quadratic replacement correction realizes an admissible marginal direction with a
physical decoder through the original memory, uniformly over joint probes. -/
theorem singular_decoder_marginal_shift
    (E : QuantumChannel (P ⊕ Q) M) (D : QuantumChannel M (P ⊕ Q))
    (τ : DensityState (P ⊕ Q)) (hτ : raw τ.1 = fromBlocks (raw τ.1).toBlocks₁₁ 0 0 0)
    (m : ℝ) (hm : 0 < m) (hfloor : m • (1 : Matrix P P ℂ) ≤ (raw τ.1).toBlocks₁₁)
    (hfix : (D.comp E).mapState τ = τ)
    (K : Matrix (P ⊕ Q) (P ⊕ Q) ℂ) (hK : K.IsHermitian) (htr : K.trace = 0)
    (hQQ : K.toBlocks₂₂ ≤ 0)
    (C : ℝ) (hC : 1 + 2 * ‖K.toBlocks₁₂‖ ^ 2 / m ≤ C) :
    let Z := fromBlocks (0 : Matrix P P ℂ) 0 0 (1 : Matrix Q Q ℂ) -
      (Fintype.card Q : ℝ) • raw τ.1
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
      ∀ (η : ℝ) (hη : 0 < η) (hη₁ : η ≤ 1), η ≤ δ →
        ∃ σ : DensityState (P ⊕ Q),
          raw σ.1 = raw τ.1 - η • K + (C * η ^ 2) • Z ∧
          let T := D.comp E
          let Dη := (mix η hη.le hη₁ (reset σ) identity).comp D
          let Tη := Dη.comp E
          raw τ.1 - act Tη (raw τ.1) = η ^ 2 • K - (C * η ^ 3) • Z ∧
          SingularJointErrorExpansion (R := R) T Tη τ σ K Z C η := by
  intro Z
  obtain ⟨δ, hδ, hδ₁, hprepare⟩ := replacement_density τ hτ m hm hfloor K hK htr hQQ C hC
  refine ⟨δ, hδ, hδ₁, fun η hη hη₁ hηδ => ?_⟩
  obtain ⟨σ, hσ⟩ := hprepare η hη hηδ
  change raw σ.1 = raw τ.1 - η • K + (C * η ^ 2) • Z at hσ
  refine ⟨σ, hσ, ?_⟩
  intro T Dη Tη
  have hcomp : Tη = (mix η hη.le hη₁ (reset σ) identity).comp T := rfl
  have ht : act T (raw τ.1) = raw τ.1 :=
    congrArg (fun s : DensityState (P ⊕ Q) => raw s.1) hfix
  have hshift : raw τ.1 - act Tη (raw τ.1) = η ^ 2 • K - (C * η ^ 3) • Z := by
    rw [hcomp, act_mix_reset, ht, show (raw τ.1).trace = 1 from τ.2.2, one_smul, hσ]
    ext i j
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Complex.real_smul,
      Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_mul, Complex.ofReal_pow]
    ring
  refine ⟨hshift, ?_⟩
  intro ω ρ X H Hη
  let Y := amp T (raw ρ.1) - raw (marginalRight ρ).1 ⊗ₖ raw σ.1
  let W := raw ω.1 ⊗ₖ K
  let V := raw ω.1 ⊗ₖ Z
  let c := (1 - η ^ 2) * C * η
  have hY : amp Tη (raw ρ.1) = (1 - η) • amp T (raw ρ.1) +
      η • (raw (marginalRight ρ).1 ⊗ₖ raw σ.1) := by
    ext ⟨r, i⟩ ⟨s, j⟩
    let block : Matrix (P ⊕ Q) (P ⊕ Q) ℂ := fun a b => (raw ρ.1) (r, a) (s, b)
    rw [amp_entry]
    change act Tη block i j = _
    rw [hcomp, act_mix_reset]
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.kroneckerMap_apply,
      amp_entry T (raw ρ.1) r s i j]
    rfl
  have hshift' : act Tη (raw τ.1) = raw τ.1 - (η ^ 2 • K - (C * η ^ 3) • Z) := by
    rw [← hshift]
    abel
  have hadd (A B : Matrix (R × (P ⊕ Q)) (R × (P ⊕ Q)) ℂ) :
      amp Tη (A + B) = amp Tη A + amp Tη B :=
    (CStarMatrix.ofMatrixₗ.symm.toLinearMap.comp
      ((referenceLinear Tη).comp CStarMatrix.ofMatrixₗ.toLinearMap)).map_add A B
  have hdiff : Hη - H = η • Y - η ^ 2 • W - c • V := by
    dsimp only [Hη, X, H, Y, W, V, c]
    rw [hadd, amp_smul, amp_smul, amp_kronecker, hshift', hY]
    ext i j
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.kroneckerMap_apply, Complex.real_smul, Complex.ofReal_sub,
      Complex.ofReal_mul, Complex.ofReal_one, Complex.ofReal_inv, Complex.ofReal_pow]
    have hηc := Complex.ofReal_ne_zero.mpr hη.ne'
    field_simp [hηc]
    ring
  refine ⟨hdiff, ?_⟩
  have hYn : traceNorm Y / 2 ≤ 1 :=
    traceDistance_le_one (referenceState T ρ) (productState (marginalRight ρ) σ)
  have hω : traceNorm (raw ω.1) = 1 := by
    have h := congrArg Complex.re (traceNorm_of_posSemidef (density_posSemidef ω))
    rw [show (raw ω.1).trace = 1 from ω.2.2] at h
    simpa only [Complex.ofReal_re, Complex.one_re] using h
  have hW : traceNorm W = traceNorm K := by
    dsimp only [W]
    rw [traceNorm_tensor, hω, one_mul]
  have hV : traceNorm V = traceNorm Z := by
    dsimp only [V]
    rw [traceNorm_tensor, hω, one_mul]
  have hη₂ : η ^ 2 ≤ η := by nlinarith [mul_nonneg hη.le (sub_nonneg.mpr hη₁)]
  have hC₀ : 0 ≤ C := le_trans (by positivity) hC
  have hc : 0 ≤ c := mul_nonneg (mul_nonneg (sub_nonneg.mpr (hη₂.trans hη₁)) hC₀) hη.le
  have hc' : c ≤ η * C := by
    dsimp [c]
    calc
      (1 - η ^ 2) * C * η ≤ 1 * C * η :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (sub_le_self _ (sq_nonneg η)) hC₀) hη.le
      _ = η * C := by ring
  have hsub {n : Type*} [Fintype n] [DecidableEq n] (A B : Matrix n n ℂ) :
      traceNorm (A - B) ≤ traceNorm A + traceNorm B := by
    simpa only [sub_eq_add_neg, Foundation.FiniteTraceDistance.traceNorm_neg] using
      traceNorm_add_le A (-B)
  rw [hdiff]
  calc
    traceNorm (η • Y - η ^ 2 • W - c • V) / 2 ≤
        (traceNorm (η • Y) + traceNorm (η ^ 2 • W) + traceNorm (c • V)) / 2 :=
      div_le_div_of_nonneg_right
        ((hsub (η • Y - η ^ 2 • W) (c • V)).trans
          (add_le_add_right (hsub (η • Y) (η ^ 2 • W)) _)) (by norm_num)
    _ = η * (traceNorm Y / 2) + (η ^ 2 * traceNorm K + c * traceNorm Z) / 2 := by
      have hsmul (X : Matrix (R × (P ⊕ Q)) (R × (P ⊕ Q)) ℂ) (d : ℝ) (hd : 0 ≤ d) :
          traceNorm (d • X) = d * traceNorm X := by
        convert traceNorm_smul_nonneg X d hd using 2
      rw [hsmul _ _ hη.le, hsmul _ _ (sq_nonneg η), hsmul _ _ hc, hW, hV]
      ring
    _ ≤ η * 1 + (η * traceNorm K + (η * C) * traceNorm Z) / 2 := by
      exact add_le_add (mul_le_mul_of_nonneg_left hYn hη.le) (div_le_div_of_nonneg_right
        (add_le_add (mul_le_mul_of_nonneg_right hη₂ (Foundation.FiniteTraceDistance.traceNorm_nonneg K))
          (mul_le_mul_of_nonneg_right hc' (Foundation.FiniteTraceDistance.traceNorm_nonneg Z))) (by norm_num))
    _ = _ := by ring

#print axioms singular_decoder_marginal_shift

end D5.S3.Quantum.Recovery.LocalCompression.SingularProductNoiseDecoder
