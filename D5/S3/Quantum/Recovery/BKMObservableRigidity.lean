/- GID: D5/S3/Quantum/Recovery/BKMObservableRigidity
   generality: G
   mirror-B: D5/B/S3/Quantum/Recovery/BKMObservableRigidity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Fixed-observable BKM rigidity for the actual partial trace. -/

import D5.S3.Quantum.Recovery.BKMFlagRefinement
import D5.S3.Quantum.Divergence.EntropyDefectResolventIntegralBudget
import D5.S3.Quantum.Divergence.UmegakiKernelContraction
import D5.S3.Quantum.Divergence.ResolventFunctionalRigidity
import D5.S3.Quantum.Information.RenyiInformationCombiningOrderThree
import D5.S3.Weil.ZetaLinear.HermitianPosPart
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.IntegralRepresentation

/-! # Fixed-observable BKM rigidity for the actual partial trace -/

noncomputable section

open Matrix MeasureTheory Set
open scoped BigOperators ComplexOrder Kronecker Matrix MatrixOrder Matrix.Norms.L2Operator
open D5.S3.Quantum.Matrix.SpectralPower (mpow mpow_one)
open D5.S3.Quantum.Recovery.BKMRelativeDensity (omega continuous_mpow)
open D5.S3.Quantum.Recovery.BKMFlagRefinement (lift bkmGap)
open D5.S3.Quantum.Information.PartialTraceMutualInformation (partialTraceRight)
open D5.S3.Quantum.Information.RenyiInformationCombiningOrderThree
  (cfc_unitary_diagonal kronecker_rpow)
open D5.S3.Quantum.Divergence.UmegakiReferenceTransport
  (partialTraceRight_posDef partialTraceRight_mul_embed partialTraceRight_embed_mul
    trace_embed_pair)

namespace D5.S3.Quantum.Recovery.BKMObservableRigidity

universe u
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {R E : Type u} [Fintype R] [DecidableEq R] [Fintype E] [DecidableEq E]

/-- The right-weighted physical observable in column-first coordinates. -/
def weightedVec (X K : Matrix n n ℂ) : n × n → ℂ :=
  vec (K * mpow X (1 / 2))

/-- The modular operator implementing left multiplication by X and right multiplication by X⁻¹. -/
def modular (X : Matrix n n ℂ) : Matrix (n × n) (n × n) ℂ :=
  (X⁻¹)ᵀ ⊗ₖ X

private theorem mpow_add {X : Matrix n n ℂ} (hX : X.PosDef) (p q : ℝ) :
    mpow X p * mpow X q = mpow X (p + q) := by
  unfold mpow
  simp_rw [← CFC.rpow_eq_cfc_real hX.posSemidef.nonneg]
  exact (CFC.rpow_add hX.isUnit).symm

private theorem mpow_zero {X : Matrix n n ℂ} (hX : X.PosDef) : mpow X 0 = 1 := by
  rw [mpow, ← CFC.rpow_eq_cfc_real hX.posSemidef.nonneg, CFC.rpow_zero X hX.posSemidef.nonneg]

private def weightedEquiv (X : Matrix n n ℂ) (hX : X.PosDef) :
    Matrix n n ℂ ≃ₗ[ℂ] (n × n → ℂ) :=
  LinearEquiv.ofBijective
    { toFun := weightedVec X
      map_add' := fun K L => by rw [weightedVec, Matrix.add_mul, Matrix.vec_add]; rfl
      map_smul' := fun c K => by rw [weightedVec, Matrix.smul_mul, Matrix.vec_smul]; rfl }
    (by
      have hright : mpow X (1 / 2) * mpow X (-(1 / 2)) = 1 := by
        rw [mpow_add hX, add_neg_cancel, mpow_zero hX]
      have hleft : mpow X (-(1 / 2)) * mpow X (1 / 2) = 1 := by
        rw [mpow_add hX, neg_add_cancel, mpow_zero hX]
      constructor
      · intro K L he
        change vec (K * mpow X (1 / 2)) = vec (L * mpow X (1 / 2)) at he
        have hv := Matrix.vec_bijective.injective he
        simpa only [Matrix.mul_assoc, hright, Matrix.mul_one] using
          congrArg (fun M => M * mpow X (-(1 / 2))) hv
      · intro v
        obtain ⟨M, rfl⟩ := Matrix.vec_bijective.surjective v
        refine ⟨M * mpow X (-(1 / 2)), ?_⟩
        change vec (M * mpow X (-(1 / 2)) * mpow X (1 / 2)) = vec M
        rw [Matrix.mul_assoc, hleft, Matrix.mul_one])

private def liftLinear : Matrix R R ℂ →ₗ[ℂ] Matrix (R × E) (R × E) ℂ where
  toFun := lift
  map_add' X Y := by simp only [lift, Matrix.add_kronecker]
  map_smul' c X := by simp only [lift, Matrix.smul_kronecker, RingHom.id_apply]

/-- The physical inclusion, transported to right-weighted Hilbert–Schmidt coordinates. -/
def weightedLift [Nonempty E] (A : Matrix (R × E) (R × E) ℂ) (hA : A.PosDef) :
    Matrix ((R × E) × (R × E)) (R × R) ℂ :=
  LinearMap.toMatrix' ((weightedEquiv A hA).toLinearMap.comp
    (liftLinear.comp (weightedEquiv (partialTraceRight A)
      (partialTraceRight_posDef A hA)).symm.toLinearMap))

private theorem weightedLift_apply [Nonempty E] (A : Matrix (R × E) (R × E) ℂ)
    (hA : A.PosDef) (K : Matrix R R ℂ) :
    weightedLift A hA *ᵥ weightedVec (partialTraceRight A) K = weightedVec A (lift K) := by
  rw [weightedLift, LinearMap.toMatrix'_mulVec, LinearMap.comp_apply, LinearMap.comp_apply]
  have hK : weightedVec (partialTraceRight A) K =
      weightedEquiv (partialTraceRight A) (partialTraceRight_posDef A hA) K := by
    unfold weightedEquiv
    rfl
  rw [hK, LinearEquiv.coe_toLinearMap, LinearEquiv.coe_toLinearMap,
    LinearEquiv.symm_apply_apply]
  unfold weightedEquiv liftLinear
  rfl

private theorem half_hermitian {X : Matrix n n ℂ} (hX : X.PosDef) :
    (mpow X (1 / 2)).IsHermitian := by
  rw [mpow, ← CFC.rpow_eq_cfc_real hX.posSemidef.nonneg]
  exact (CFC.rpow_nonneg (a := X) (y := (1 / 2 : ℝ))).posSemidef.isHermitian

private theorem weighted_pair {X : Matrix n n ℂ} (hX : X.PosDef) (K L : Matrix n n ℂ) :
    star (weightedVec X K) ⬝ᵥ weightedVec X L = (Kᴴ * L * X).trace := by
  let H := mpow X (1 / 2)
  have hHH : H * H = X := by
    rw [show H * H = mpow X ((1 / 2 : ℝ) + 1 / 2) from mpow_add hX _ _,
      show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num, mpow_one hX.isHermitian]
  change star (vec (K * H)) ⬝ᵥ vec (L * H) = _
  rw [Matrix.star_vec_dotProduct_vec, Matrix.conjTranspose_mul,
    show Hᴴ = H from (half_hermitian hX).eq, Matrix.mul_assoc H, Matrix.trace_mul_comm H]
  simpa only [Matrix.mul_assoc] using congrArg Matrix.trace
    (show Kᴴ * L * (H * H) = Kᴴ * L * X by rw [hHH])

private theorem mpow_neg_one {X : Matrix n n ℂ} (hX : X.PosDef) :
    mpow X (-1) = X⁻¹ := by
  rw [mpow, ← CFC.rpow_eq_cfc_real hX.posSemidef.nonneg,
    ← CFC.inverse_eq_rpow_neg_one hX.isStrictlyPositive, Matrix.nonsing_inv_eq_ringInverse]

private theorem modular_pair {X : Matrix n n ℂ} (hX : X.PosDef) (K L : Matrix n n ℂ) :
    star (weightedVec X K) ⬝ᵥ (modular X *ᵥ weightedVec X L) = (Kᴴ * X * L).trace := by
  let H := mpow X (1 / 2)
  have hHH : (H * X⁻¹) * H = 1 := by
    dsimp only [H]
    rw [← mpow_neg_one hX, mpow_add hX, mpow_add hX,
      show (1 / 2 : ℝ) + (-1) + 1 / 2 = 0 by norm_num, mpow_zero hX]
  change star (vec (K * H)) ⬝ᵥ (((X⁻¹)ᵀ ⊗ₖ X) *ᵥ vec (L * H)) = _
  rw [Matrix.kronecker_mulVec_vec, Matrix.transpose_transpose, Matrix.star_vec_dotProduct_vec,
    Matrix.conjTranspose_mul, show Hᴴ = H from (half_hermitian hX).eq,
    Matrix.mul_assoc H, Matrix.trace_mul_comm H]
  calc
    _ = (Kᴴ * X * L * ((H * X⁻¹) * H)).trace := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hHH, Matrix.mul_one]

private theorem star_pair_mul {i j : Type*} [Fintype i] [Fintype j]
    (V : Matrix i j ℂ) (x : j → ℂ) (y : i → ℂ) :
    star (V *ᵥ x) ⬝ᵥ y = star x ⬝ᵥ (Vᴴ *ᵥ y) := by
  rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec]

omit [DecidableEq n] in
private theorem matrix_eq_of_pair (M N : Matrix n n ℂ)
    (h : ∀ x y, star x ⬝ᵥ (M *ᵥ y) = star x ⬝ᵥ (N *ᵥ y)) : M = N := by
  classical
  ext i j
  simpa [Matrix.mulVec_single_one, Pi.star_def, Pi.single_apply, dotProduct] using
    h (Pi.single i 1) (Pi.single j 1)

/-- Partial trace gives an exact isometry and the exact compression of the first modular moment. -/
theorem weightedLift_compression [Nonempty E] (A : Matrix (R × E) (R × E) ℂ) (hA : A.PosDef) :
    let V := weightedLift A hA
    (∀ K, V *ᵥ weightedVec (partialTraceRight A) K = weightedVec A (lift K)) ∧
      Vᴴ * V = 1 ∧ Vᴴ * modular A * V = modular (partialTraceRight A) := by
  dsimp only
  refine ⟨weightedLift_apply A hA, ?_, ?_⟩
  · apply matrix_eq_of_pair
    intro x y
    obtain ⟨K, rfl⟩ := (weightedEquiv (partialTraceRight A)
      (partialTraceRight_posDef A hA)).surjective x
    obtain ⟨L, rfl⟩ := (weightedEquiv (partialTraceRight A)
      (partialTraceRight_posDef A hA)).surjective y
    change star (weightedVec (partialTraceRight A) K) ⬝ᵥ
      (((weightedLift A hA)ᴴ * weightedLift A hA) *ᵥ weightedVec (partialTraceRight A) L) =
        star (weightedVec (partialTraceRight A) K) ⬝ᵥ (1 *ᵥ weightedVec (partialTraceRight A) L)
    rw [← Matrix.mulVec_mulVec, ← star_pair_mul, Matrix.one_mulVec,
      weightedLift_apply, weightedLift_apply, weighted_pair hA,
      weighted_pair (partialTraceRight_posDef A hA), Matrix.mul_assoc, lift, lift,
      trace_embed_pair, partialTraceRight_embed_mul, Matrix.mul_assoc]
  · apply matrix_eq_of_pair
    intro x y
    obtain ⟨K, rfl⟩ := (weightedEquiv (partialTraceRight A)
      (partialTraceRight_posDef A hA)).surjective x
    obtain ⟨L, rfl⟩ := (weightedEquiv (partialTraceRight A)
      (partialTraceRight_posDef A hA)).surjective y
    change star (weightedVec (partialTraceRight A) K) ⬝ᵥ
      (((weightedLift A hA)ᴴ * modular A * weightedLift A hA) *ᵥ
        weightedVec (partialTraceRight A) L) = star (weightedVec (partialTraceRight A) K) ⬝ᵥ
          (modular (partialTraceRight A) *ᵥ weightedVec (partialTraceRight A) L)
    rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← star_pair_mul, ← Matrix.mulVec_mulVec,
      weightedLift_apply, weightedLift_apply, modular_pair hA,
      modular_pair (partialTraceRight_posDef A hA), Matrix.mul_assoc, lift, lift,
      trace_embed_pair, partialTraceRight_mul_embed, Matrix.mul_assoc]

private theorem modular_posDef {X : Matrix n n ℂ} (hX : X.PosDef) : (modular X).PosDef :=
  hX.inv.transpose.kronecker hX

set_option maxHeartbeats 800000 in
private theorem modular_power {X : Matrix n n ℂ} (hX : X.PosDef) (p : ℝ) :
    mpow (modular X) p = (mpow X (-p))ᵀ ⊗ₖ mpow X p := by
  let U := hX.isHermitian.eigenvectorUnitary
  let Ubar := Matrix.UnitaryGroup.map_star U
  let d := hX.isHermitian.eigenvalues
  have hUbar : (Ubar : Matrix n n ℂ) = (U : Matrix n n ℂ)ᴴᵀ := rfl
  have transpose_cfc (f : ℝ → ℝ) :
      (cfc f X)ᵀ = (Ubar : Matrix n n ℂ) *
        diagonal (fun i => (f (d i) : ℂ)) * star (Ubar : Matrix n n ℂ) := by
    rw [hX.isHermitian.cfc_eq]
    simp only [Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply,
      Matrix.star_eq_conjTranspose, RCLike.ofReal_eq_complex_ofReal,
      Matrix.transpose_mul, Matrix.diagonal_transpose, ← Matrix.mul_assoc,
      hUbar, Matrix.conjTranspose_transpose_eq_transpose_conjTranspose,
      Matrix.conjTranspose_conjTranspose, U, d, Function.comp_def]
  have hinv : (X⁻¹)ᵀ = (Ubar : Matrix n n ℂ) *
      diagonal (fun i => ((d i ^ (-1 : ℝ) : ℝ) : ℂ)) * star (Ubar : Matrix n n ℂ) := by
    simpa only [← mpow_neg_one hX, mpow] using transpose_cfc (fun x => x ^ (-1 : ℝ))
  have hfactor : ((X⁻¹)ᵀ) ^ p = (mpow X (-p))ᵀ := by
    rw [CFC.rpow_eq_cfc_real hX.inv.transpose.posSemidef.nonneg, hinv,
      cfc_unitary_diagonal, mpow, transpose_cfc]
    have hp (i : n) : (d i ^ (-1 : ℝ)) ^ p = d i ^ (-p) := by
      rw [← Real.rpow_mul (hX.eigenvalues_pos i).le, neg_one_mul]
    simp only [hp]
  change cfc (fun x : ℝ => x ^ p) (modular X) =
    (mpow X (-p))ᵀ ⊗ₖ cfc (fun x : ℝ => x ^ p) X
  rw [← CFC.rpow_eq_cfc_real (modular_posDef hX).posSemidef.nonneg,
    modular, kronecker_rpow hX.inv.transpose.posSemidef hX.posSemidef p,
    hfactor, CFC.rpow_eq_cfc_real hX.posSemidef.nonneg]

private theorem weighted_power_action {X : Matrix n n ℂ} (hX : X.PosDef)
    (K : Matrix n n ℂ) (p : ℝ) :
    mpow (modular X) p *ᵥ weightedVec X K =
      vec (mpow X p * K * mpow X (1 / 2 - p)) := by
  rw [modular_power hX, weightedVec, Matrix.kronecker_mulVec_vec, Matrix.transpose_transpose]
  simp only [Matrix.mul_assoc, mpow_add hX, sub_eq_add_neg]

private theorem weighted_power_form {X : Matrix n n ℂ} (hX : X.PosDef)
    (K : Matrix n n ℂ) (p : ℝ) :
    (star (weightedVec X K) ⬝ᵥ (mpow (modular X) p *ᵥ weightedVec X K)).re =
      (Kᴴ * (mpow X p * K * mpow X (1 - p))).trace.re := by
  let H := mpow X (1 / 2)
  have hpow : mpow X (1 / 2 - p) * H = mpow X (1 - p) := by
    rw [show H = mpow X (1 / 2) from rfl, mpow_add hX,
      show (1 / 2 : ℝ) - p + 1 / 2 = 1 - p by ring]
  rw [weighted_power_action hX, weightedVec, Matrix.star_vec_dotProduct_vec,
    Matrix.conjTranspose_mul, (half_hermitian hX).eq,
    Matrix.mul_assoc (mpow X (1 / 2)), Matrix.trace_mul_comm (mpow X (1 / 2))]
  change (Kᴴ * (mpow X p * K * mpow X (1 / 2 - p)) * H).trace.re = _
  calc
    _ = (Kᴴ * (mpow X p * K * (mpow X (1 / 2 - p) * H))).trace.re := by
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [hpow]

/-- The retained minus joint quadratic form at a single modular power. -/
def powerDefect [Nonempty E] (A : Matrix (R × E) (R × E) ℂ)
    (hA : A.PosDef) (K : Matrix R R ℂ) (p : ℝ) : ℝ :=
  let S := partialTraceRight A
  let b := weightedVec S K
  let a := weightedLift A hA *ᵥ b
  (star b ⬝ᵥ (mpow (modular S) p *ᵥ b)).re -
    (star a ⬝ᵥ (mpow (modular A) p *ᵥ a)).re

private theorem powerDefect_trace [Nonempty E] (A : Matrix (R × E) (R × E) ℂ)
    (hA : A.PosDef) (K : Matrix R R ℂ) (p : ℝ) :
    powerDefect A hA K p =
      (Kᴴ * (mpow (partialTraceRight A) p * K * mpow (partialTraceRight A) (1 - p))).trace.re -
        ((lift K)ᴴ * (mpow A p * lift K * mpow A (1 - p))).trace.re := by
  rw [powerDefect, weightedLift_apply, weighted_power_form hA,
    weighted_power_form (partialTraceRight_posDef A hA)]

private def tracePair (K : Matrix n n ℂ) : Matrix n n ℂ →L[ℝ] ℝ :=
  Complex.reCLM.comp
    ((Matrix.traceLinearMap n ℝ ℂ).toContinuousLinearMap.comp
      (LinearMap.mulLeft ℝ Kᴴ).toContinuousLinearMap)

private theorem continuous_tracePair_power {X : Matrix n n ℂ} (hX : X.PosDef)
    (L : Matrix n n ℂ) :
    Continuous (fun p : ℝ => tracePair L (mpow X p * L * mpow X (1 - p))) :=
  (tracePair L).continuous.comp
    (((continuous_mpow X hX).mul continuous_const).mul
      ((continuous_mpow X hX).comp (continuous_const.sub continuous_id)))

private theorem continuous_powerDefect [Nonempty E] (A : Matrix (R × E) (R × E) ℂ)
    (hA : A.PosDef) (K : Matrix R R ℂ) : Continuous (powerDefect A hA K) := by
  have he : powerDefect A hA K = fun p : ℝ =>
      tracePair K (mpow (partialTraceRight A) p * K * mpow (partialTraceRight A) (1 - p)) -
        tracePair (lift K) (mpow A p * lift K * mpow A (1 - p)) :=
    funext (powerDefect_trace A hA K)
  rw [he]
  exact (continuous_tracePair_power (partialTraceRight_posDef A hA) K).sub
    (continuous_tracePair_power hA (lift K))

private theorem tracePair_omega {X : Matrix n n ℂ} (hX : X.PosDef) (L : Matrix n n ℂ) :
    tracePair L (omega X L) =
      ∫ p in (0 : ℝ)..1, tracePair L (mpow X p * L * mpow X (1 - p)) := by
  have hc : Continuous (fun p : ℝ => mpow X p * L * mpow X (1 - p)) :=
    ((continuous_mpow X hX).mul (continuous_const (y := L))).mul
      ((continuous_mpow X hX).comp ((continuous_const (y := (1 : ℝ))).sub continuous_id))
  exact ((tracePair L).intervalIntegral_comp_comm (hc.intervalIntegrable 0 1)).symm

private theorem bkmGap_integral [Nonempty E] (A : Matrix (R × E) (R × E) ℂ)
    (hA : A.PosDef) (K : Matrix R R ℂ) (hK : K.IsHermitian) :
    bkmGap A K = ∫ p in (0 : ℝ)..1, powerDefect A hA K p := by
  have hLift : (lift (ι := E) K).IsHermitian := by
    rw [Matrix.IsHermitian, lift, Matrix.conjTranspose_kronecker, hK.eq, Matrix.conjTranspose_one]
  let S := partialTraceRight A
  have hS := partialTraceRight_posDef A hA
  calc
    bkmGap A K = tracePair K (omega S K) - tracePair (lift K) (omega A (lift K)) := by
      change _ = (Kᴴ * omega S K).trace.re - ((lift K)ᴴ * omega A (lift K)).trace.re
      rw [hK.eq, hLift.eq]
      rfl
    _ = _ := by
      rw [tracePair_omega hS, tracePair_omega hA,
        ← intervalIntegral.integral_sub
          ((continuous_tracePair_power hS K).intervalIntegrable 0 1)
          ((continuous_tracePair_power hA (lift K)).intervalIntegrable 0 1)]
      congr 1
      funext p
      exact (powerDefect_trace A hA K p).symm

open D5.S3.Quantum.Divergence.ResolventDefectRigidity (resolvent_defect_identity_and_bound)
open D5.S3.Quantum.Divergence.ResolventFunctionalRigidity
  (cfc_shift_inverse zero_resolvent_defects_force_functional_intertwining)

private def quadratic (M : Matrix n n ℂ) (x : n → ℂ) : ℝ :=
  (star x ⬝ᵥ (M *ᵥ x)).re

private def shiftedForm (M : Matrix n n ℂ) (x : n → ℂ) (t : ℝ) : ℝ :=
  quadratic ((M + t • (1 : Matrix n n ℂ))⁻¹) x

private theorem quadratic_cfc {M : Matrix n n ℂ} (hM : M.IsHermitian)
    (x : n → ℂ) (f : ℝ → ℝ) :
    quadratic (cfc f M) x =
      ∑ i, f (hM.eigenvalues i) * ‖(hM.eigenvectorUnitaryᴴ *ᵥ x) i‖ ^ 2 := by
  rw [quadratic, hM.cfc_eq]
  exact RHLinalg.hermForm_specMap hM f x

private theorem compensated_integral {M : Matrix n n ℂ} (hM : M.PosDef)
    (x : n → ℂ) {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    let F := fun t : ℝ => t ^ p * (t⁻¹ * quadratic 1 x - shiftedForm M x t)
    let C := ∫ t in Ioi (0 : ℝ), Real.rpowIntegrand₀₁ p t 1
    IntegrableOn F (Ioi 0) ∧ (∫ t in Ioi (0 : ℝ), F t) = C * quadratic (mpow M p) x := by
  classical
  let d := hM.isHermitian.eigenvalues
  let w : n → ℝ := fun i => ‖(hM.isHermitian.eigenvectorUnitaryᴴ *ᵥ x) i‖ ^ 2
  let J : ℝ → ℝ := fun t => ∑ i, Real.rpowIntegrand₀₁ p t (d i) * w i
  have hi (i : n) : IntegrableOn
      (fun t : ℝ => Real.rpowIntegrand₀₁ p t (d i) * w i) (Ioi 0) :=
    (Real.integrableOn_rpowIntegrand₀₁_Ioi hp (hM.eigenvalues_pos i).le).mul_const _
  have hw : quadratic 1 x = ∑ i, w i := by
    simpa only [cfc_const_one ℝ M, one_mul] using quadratic_cfc hM.isHermitian x (fun _ => 1)
  have hpt : EqOn J (fun t : ℝ => t ^ p * (t⁻¹ * quadratic 1 x - shiftedForm M x t)) (Ioi 0) := by
    intro t ht
    change J t = t ^ p * (t⁻¹ * quadratic 1 x - shiftedForm M x t)
    rw [show shiftedForm M x t = quadratic (cfc (fun z : ℝ => (z + t)⁻¹) M) x by
      rw [shiftedForm, cfc_shift_inverse M hM.posSemidef t ht]]
    rw [quadratic_cfc hM.isHermitian, hw]
    simp only [J, Real.rpowIntegrand₀₁, add_comm t,
      mul_assoc, mul_sub, sub_mul, Finset.sum_sub_distrib, Finset.mul_sum, d, w]
  have hJ : IntegrableOn J (Ioi (0 : ℝ)) :=
    integrable_finsetSum Finset.univ (fun i _ => hi i)
  dsimp only
  refine ⟨hJ.congr_fun hpt measurableSet_Ioi, ?_⟩
  rw [← setIntegral_congr_fun measurableSet_Ioi hpt]
  change (∫ t in Ioi (0 : ℝ), ∑ i, Real.rpowIntegrand₀₁ p t (d i) * w i) = _
  rw [integral_finsetSum Finset.univ (fun i _ => hi i), mpow, quadratic_cfc hM.isHermitian,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_mul_const, Real.integral_rpowIntegrand₀₁_eq_rpow_mul_const hp
    (hM.eigenvalues_pos i).le]
  change d i ^ p * (∫ t in Ioi (0 : ℝ), Real.rpowIntegrand₀₁ p t 1) * w i = _
  ring

private theorem resolvent_integral {i j : Type*}
    [Fintype i] [DecidableEq i] [Fintype j] [DecidableEq j]
    {M : Matrix i i ℂ} {N : Matrix j j ℂ} (hM : M.PosDef) (hN : N.PosDef)
    (a : i → ℂ) (b : j → ℂ) (hmass : quadratic 1 a = quadratic 1 b)
    {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    let F := fun t : ℝ => t ^ p * (shiftedForm M a t - shiftedForm N b t)
    let C := ∫ t in Ioi (0 : ℝ), Real.rpowIntegrand₀₁ p t 1
    IntegrableOn F (Ioi 0) ∧
      (∫ t in Ioi (0 : ℝ), F t) = C * (quadratic (mpow N p) b - quadratic (mpow M p) a) := by
  obtain ⟨hA, hAi⟩ := compensated_integral hM a hp
  obtain ⟨hB, hBi⟩ := compensated_integral hN b hp
  have hpoint (t : ℝ) :
      t ^ p * (t⁻¹ * quadratic 1 b - shiftedForm N b t) -
        t ^ p * (t⁻¹ * quadratic 1 a - shiftedForm M a t) =
          t ^ p * (shiftedForm M a t - shiftedForm N b t) := by rw [hmass]; ring
  dsimp only at hA hB hAi hBi ⊢
  refine ⟨(hB.sub hA).congr_fun (fun t _ => hpoint t) measurableSet_Ioi, ?_⟩
  rw [← setIntegral_congr_fun measurableSet_Ioi (fun t _ => hpoint t),
    integral_sub hB hA, hBi, hAi, mul_sub]

private theorem shiftedForm_continuousOn {M : Matrix n n ℂ} (hM : M.PosDef) (x : n → ℂ) :
    ContinuousOn (shiftedForm M x) (Ioi (0 : ℝ)) := by
  intro t ht
  have hinv :=
    D5.S3.Quantum.Divergence.EntropyDefectResolventIntegralBudget.continuousAt_shift_inverse
      M hM.posSemidef t ht
  have hquad : Continuous (fun Y : Matrix n n ℂ => quadratic Y x) := by
    unfold quadratic
    exact Complex.continuous_re.comp
      (continuous_const.dotProduct (continuous_id.matrix_mulVec continuous_const))
  exact (hquad.continuousAt.comp hinv).continuousWithinAt

/-- The actual BKM gap is the integral of the power defects. It is nonnegative,
and it vanishes exactly when the entire real spectral calculus intertwines on the
fixed right-weighted physical observable. -/
theorem bkmGap_rigidity [Nonempty E] (A : Matrix (R × E) (R × E) ℂ)
    (hA : A.PosDef) (K : Matrix R R ℂ) (hK : K.IsHermitian) :
    let S := partialTraceRight A
    let V := weightedLift A hA
    let b := weightedVec S K
    bkmGap A K = (∫ p in (0 : ℝ)..1, powerDefect A hA K p) ∧
      0 ≤ bkmGap A K ∧
      (bkmGap A K = 0 ↔ ∀ f : ℝ → ℝ,
        cfc f (modular A) *ᵥ (V *ᵥ b) = V *ᵥ (cfc f (modular S) *ᵥ b)) := by
  let S := partialTraceRight A
  let V := weightedLift A hA
  let b := weightedVec S K
  let a := V *ᵥ b
  let M := modular A
  let N := modular S
  let g := fun t : ℝ => shiftedForm M a t - shiftedForm N b t
  let d := powerDefect A hA K
  have hM : M.PosDef := modular_posDef hA
  have hN : N.PosDef := modular_posDef (partialTraceRight_posDef A hA)
  obtain ⟨_, hV, hVN⟩ := weightedLift_compression A hA
  change Vᴴ * V = 1 at hV
  change Vᴴ * M * V = N at hVN
  have hV' : Vᴴ * V ≤ 1 := hV.le
  have hVN' : Vᴴ * M * V ≤ N := hVN.le
  have hadj (z : R × R → ℂ) : star a ⬝ᵥ (V *ᵥ z) = star b ⬝ᵥ z := by
    change star (V *ᵥ b) ⬝ᵥ (V *ᵥ z) = _
    rw [star_pair_mul, Matrix.mulVec_mulVec, hV, Matrix.one_mulVec]
  have hmass : quadratic 1 a = quadratic 1 b := by
    simpa only [quadratic, Matrix.one_mulVec, a] using congrArg Complex.re (hadj b)
  have hsaturation : (star a ⬝ᵥ a).re = (star b ⬝ᵥ b).re := by
    simpa only [quadratic, Matrix.one_mulVec] using hmass
  have hg (t : ℝ) (ht : 0 < t) : 0 ≤ g t := by
    have bound := (resolvent_defect_identity_and_bound M N hM.posSemidef hN.posSemidef
      V hV' hVN' b hsaturation t ht).2.1
    refine le_trans (mul_nonneg ht.le ?_) bound
    exact Complex.nonneg_iff.mp (dotProduct_star_self_nonneg _ ) |>.1
  have hi {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
      IntegrableOn (fun t => t ^ p * g t) (Ioi 0) ∧
        (∫ t in Ioi (0 : ℝ), t ^ p * g t) =
          (∫ t in Ioi (0 : ℝ), Real.rpowIntegrand₀₁ p t 1) * d p :=
    resolvent_integral hM hN a b hmass hp
  have hnonneg (p : ℝ) (hp : p ∈ Icc (0 : ℝ) 1) : 0 ≤ d p := by
    obtain hp0 | hp0 := hp.1.lt_or_eq
    · obtain hp1 | rfl := hp.2.lt_or_eq
      · have hpi : p ∈ Ioo (0 : ℝ) 1 := ⟨hp0, hp1⟩
        have h : 0 ≤ ∫ t in Ioi (0 : ℝ), t ^ p * g t :=
          setIntegral_nonneg measurableSet_Ioi
            (fun t ht => mul_nonneg (Real.rpow_nonneg ht.le p) (hg t ht))
        rw [(hi hpi).2] at h
        exact nonneg_of_mul_nonneg_right h (Real.integral_rpowIntegrand₀₁_one_pos hpi)
      · have hmoment : star a ⬝ᵥ (M *ᵥ a) = star b ⬝ᵥ (N *ᵥ b) := by
          change star (V *ᵥ b) ⬝ᵥ (M *ᵥ (V *ᵥ b)) = _
          rw [star_pair_mul, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hVN]
        change 0 ≤ quadratic (mpow N 1) b - quadratic (mpow M 1) a
        rw [mpow_one hN.isHermitian, mpow_one hM.isHermitian, quadratic, quadratic,
          hmoment, sub_self]
    · subst p
      change 0 ≤ quadratic (mpow N 0) b - quadratic (mpow M 0) a
      rw [mpow_zero hN, mpow_zero hM, hmass, sub_self]
  have hgap := bkmGap_integral A hA K hK
  refine ⟨hgap, ?_, ?_⟩
  · rw [hgap]
    exact intervalIntegral.integral_nonneg (by norm_num) hnonneg
  constructor
  · intro hz
    have hh : (1 / 2 : ℝ) ∈ Ioo 0 1 := by norm_num
    have hd : d (1 / 2) = 0 := by
      apply le_antisymm _ (hnonneg _ (Ioo_subset_Icc_self hh))
      by_contra! hpos
      have hI := intervalIntegral.integral_pos (by norm_num : (0 : ℝ) < 1)
        (continuous_powerDefect A hA K).continuousOn
        (fun p hp => hnonneg p (Ioc_subset_Icc_self hp))
        ⟨1 / 2, Ioo_subset_Icc_self hh, hpos⟩
      rw [← hgap, hz] at hI
      exact (lt_irrefl _ hI)
    let F : ℝ → ℝ := fun t => t ^ (1 / 2 : ℝ) * g t
    have hFnonneg : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] F := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact mul_nonneg (Real.rpow_nonneg ht.le _) (hg t ht)
    have hFzero : (∫ t in Ioi (0 : ℝ), F t) = 0 := by rw [(hi hh).2, hd, mul_zero]
    have hFae : F =ᵐ[volume.restrict (Ioi (0 : ℝ))] 0 :=
      (integral_eq_zero_iff_of_nonneg_ae hFnonneg (hi hh).1).mp hFzero
    have hFcont : ContinuousOn F (Ioi (0 : ℝ)) :=
      (Real.continuous_rpow_const (by norm_num)).continuousOn.mul
        ((shiftedForm_continuousOn hM a).sub (shiftedForm_continuousOn hN b))
    have hpoint := MeasureTheory.Measure.eqOn_open_of_ae_eq hFae isOpen_Ioi hFcont continuousOn_const
    have hgzero (t : ℝ) (ht : 0 < t) : g t = 0 :=
      (mul_eq_zero.mp (hpoint ht)).resolve_left (Real.rpow_pos_of_pos ht _).ne'
    exact zero_resolvent_defects_force_functional_intertwining M N hM.posSemidef
      hN.posSemidef V hV' hVN' b hsaturation hgzero
  · intro h
    have hzero (p : ℝ) : d p = 0 := by
      have hp := h (fun z : ℝ => z ^ p)
      change mpow M p *ᵥ a = V *ᵥ (mpow N p *ᵥ b) at hp
      change (star b ⬝ᵥ (mpow N p *ᵥ b)).re -
        (star a ⬝ᵥ (mpow M p *ᵥ a)).re = 0
      rw [hp, hadj, sub_self]
    rw [hgap]
    change (∫ p in (0 : ℝ)..1, d p) = 0
    simp_rw [hzero, intervalIntegral.integral_zero]

#print axioms weightedLift_compression
#print axioms bkmGap_rigidity

end D5.S3.Quantum.Recovery.BKMObservableRigidity
