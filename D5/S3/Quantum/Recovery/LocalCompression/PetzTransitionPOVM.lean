/- GID: D5/S3/Quantum/Recovery/LocalCompression/PetzTransitionPOVM
   generality: G
   mirror-B: D5/B/S3/Quantum/Recovery/LocalCompression/PetzTransitionPOVM
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The physical spectral transition POVM on complex matrix space admits a uniform fair-pair component of weight 1/16. -/

import D5.S3.Quantum.Recovery.LocalCompression.PetzSameSignCompression
import OmegaBuild.Commands

/-! Left and right spectral transitions compressed to the environment's
Hilbert–Schmidt matrix space. -/

compile_only_with_mathlib

set_option autoImplicit false

noncomputable section

namespace D5.S3.Quantum.Recovery.LocalCompression.PetzTransitionPOVM

open _root_.Matrix
open scoped BigOperators Matrix ComplexOrder MatrixOrder Matrix.Norms.Frobenius Kronecker
open D5.S3.Quantum.GNSMatrix (frobenius_norm_sq_eq_trace)
open D5.S3.Quantum.Recovery.LocalCompression.PetzSameSignCompression
  (physicalInvolution plusIsometry spectral_isometries same_sign_transition_lower)

/-- The trace inner product for the Frobenius norm on square complex matrices. -/
scoped instance frobeniusInner {d : Type*} [Fintype d] :
    InnerProductSpace ℂ (Matrix d d ℂ) where
  toNormedSpace := Matrix.frobeniusNormedSpace
  inner X Y := (Xᴴ * Y).trace
  norm_sq_eq_re_inner X := by
    change ‖X‖ ^ 2 = (Xᴴ * X).trace.re
    exact (congrArg Complex.re (frobenius_norm_sq_eq_trace X))
  conj_inner_symm X Y := by
    change star (Yᴴ * X).trace = (Xᴴ * Y).trace
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose]
  add_left X Y Z := by
    simp only [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.trace_add]
  smul_left X Y r := by
    simp only [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.trace_smul,
      smul_eq_mul] <;> rfl

variable {b d e : Type*} [Fintype b] [Fintype d] [Fintype e]

private theorem inner_eq_trace (X Y : Matrix d d ℂ) :
    inner ℂ X Y = (Xᴴ * Y).trace := rfl

private theorem inner_self_eq_frobenius_sq (X : Matrix d d ℂ) :
    inner ℂ X X = ((‖X‖ ^ 2 : ℝ) : ℂ) :=
  (inner_eq_trace X X).trans (frobenius_norm_sq_eq_trace X).symm

/-- The two spectral projections, with `true` denoting the positive sign. -/
def spectralProjector [DecidableEq d] (H : Matrix d d ℂ) : Bool → Matrix d d ℂ
  | true => (1 / 2 : ℝ) • (1 + H)
  | false => (1 / 2 : ℝ) • (1 - H)

private theorem spectralProjector_sum [DecidableEq d] (H : Matrix d d ℂ) :
    ∑ s, spectralProjector H s = 1 := by
  simp only [Fintype.sum_bool, spectralProjector]
  module

private theorem spectralProjector_hermitian [DecidableEq d]
    (H : Matrix d d ℂ) (hH : H.IsHermitian) (s : Bool) :
    (spectralProjector H s)ᴴ = spectralProjector H s := by
  cases s <;> simp [spectralProjector, Matrix.conjTranspose_smul, hH.eq]

private theorem spectralProjector_idempotent [DecidableEq d]
    (H : Matrix d d ℂ) (hHsq : H * H = 1) (s : Bool) :
    spectralProjector H s * spectralProjector H s = spectralProjector H s := by
  cases s
  · simp only [spectralProjector, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hHsq]
    module
  · simp only [spectralProjector, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, hHsq]
    module

/-- Amplification by the retained identity divided by the square root of its dimension. -/
def normalizedAmplification [DecidableEq b] :
    Matrix e e ℂ →ₗ[ℂ] Matrix (b × e) (b × e) ℂ where
  toFun q := (Real.sqrt (Fintype.card b : ℝ))⁻¹ • ((1 : Matrix b b ℂ) ⊗ₖ q)
  map_add' X Y := by rw [Matrix.kronecker_add, smul_add]
  map_smul' z X := by
    simp only [RingHom.id_apply, Matrix.kronecker_smul]
    exact smul_comm _ _ _

private theorem frobenius_sq_kronecker (X : Matrix b b ℂ) (Y : Matrix e e ℂ) :
    ‖X ⊗ₖ Y‖ ^ 2 = ‖X‖ ^ 2 * ‖Y‖ ^ 2 := by
  apply Complex.ofReal_injective
  rw [Complex.ofReal_mul]
  simp only [frobenius_norm_sq_eq_trace, Matrix.conjTranspose_kronecker,
    ← Matrix.mul_kronecker_mul, Matrix.trace_kronecker]

private theorem inv_sqrt_smul_norm_sq (c : ℝ) (hc : 0 < c) (X : Matrix d d ℂ) :
    ‖(Real.sqrt c)⁻¹ • X‖ ^ 2 = ‖X‖ ^ 2 / c := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)),
    mul_pow, inv_pow, Real.sq_sqrt hc.le, div_eq_mul_inv, mul_comm]

private theorem normalizedAmplification_norm [DecidableEq b] [Nonempty b]
    (q : Matrix e e ℂ) :
    ‖normalizedAmplification (b := b) q‖ = ‖q‖ := by
  have hb : (0 : ℝ) < Fintype.card b := by exact_mod_cast Fintype.card_pos (α := b)
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  change ‖(Real.sqrt (Fintype.card b : ℝ))⁻¹ • ((1 : Matrix b b ℂ) ⊗ₖ q)‖ ^ 2 = _
  have hI : ‖(1 : Matrix b b ℂ)‖ ^ 2 = (Fintype.card b : ℝ) := by
    apply Complex.ofReal_injective
    rw [frobenius_norm_sq_eq_trace, Matrix.conjTranspose_one, Matrix.one_mul,
      Matrix.trace_one, Complex.ofReal_natCast]
  rw [inv_sqrt_smul_norm_sq _ hb, frobenius_sq_kronecker, hI,
    mul_comm (Fintype.card b : ℝ), mul_div_cancel_right₀ _ hb.ne']

/-- The left/right spectral transition on the joint matrix space. -/
def transition [DecidableEq d] (H : Matrix d d ℂ) (o : Bool × Bool) :
    Matrix d d ℂ →ₗ[ℂ] Matrix d d ℂ :=
  LinearMap.mulLeftRight ℂ (spectralProjector H o.1, spectralProjector H o.2)

private theorem transition_isProjection [DecidableEq d] (H : Matrix d d ℂ)
    (hH : H.IsHermitian) (hHsq : H * H = 1) (o : Bool × Bool) :
    (transition H o).IsSymmetricProjection := by
  constructor
  · show transition H o * transition H o = transition H o
    apply LinearMap.ext
    intro X
    change spectralProjector H o.1 *
        (spectralProjector H o.1 * X * spectralProjector H o.2) *
        spectralProjector H o.2 = _
    calc
      _ = (spectralProjector H o.1 * spectralProjector H o.1) * X *
          (spectralProjector H o.2 * spectralProjector H o.2) := by
        simp only [Matrix.mul_assoc]
      _ = _ := by
        simp only [spectralProjector_idempotent H hHsq, transition,
          LinearMap.mulLeftRight_apply]
  · intro X Y
    simp only [inner_eq_trace, transition, LinearMap.mulLeftRight_apply,
      Matrix.conjTranspose_mul, spectralProjector_hermitian H hH]
    simpa only [Matrix.mul_assoc] using
      (Matrix.trace_mul_comm (spectralProjector H o.2)
        (Xᴴ * (spectralProjector H o.1 * Y)))

/-- Compression of the joint transition by the matrix-space amplification. -/
def transitionEffect [DecidableEq d] (H : Matrix d d ℂ)
    (J : Matrix e e ℂ →ₗ[ℂ] Matrix d d ℂ) (o : Bool × Bool) :
    Matrix e e ℂ →ₗ[ℂ] Matrix e e ℂ :=
  J.adjoint ∘ₗ transition H o ∘ₗ J

private theorem transitionEffect_inner [DecidableEq d] (H : Matrix d d ℂ)
    (hH : H.IsHermitian) (hHsq : H * H = 1)
    (J : Matrix e e ℂ →ₗ[ℂ] Matrix d d ℂ) (o : Bool × Bool) (q : Matrix e e ℂ) :
    inner ℂ (transitionEffect H J o q) q =
      ((‖spectralProjector H o.1 * J q * spectralProjector H o.2‖ ^ 2 : ℝ) : ℂ) := by
  have hp := transition_isProjection H hH hHsq o
  change inner ℂ (J.adjoint (transition H o (J q))) q = _
  rw [LinearMap.adjoint_inner_left]
  have hid : transition H o (transition H o (J q)) = transition H o (J q) :=
    DFunLike.congr_fun hp.isIdempotentElem (J q)
  calc
    inner ℂ (transition H o (J q)) (J q) =
        inner ℂ (transition H o (transition H o (J q))) (J q) := by rw [hid]
    _ = inner ℂ (transition H o (J q)) (transition H o (J q)) := hp.isSymmetric _ _
    _ = _ := inner_self_eq_frobenius_sq (transition H o (J q))

private theorem transition_povm [DecidableEq d] (H : Matrix d d ℂ)
    (hH : H.IsHermitian) (hHsq : H * H = 1)
    (J : Matrix e e ℂ →ₗ[ℂ] Matrix d d ℂ) (hJ : ∀ q, ‖J q‖ = ‖q‖) :
    (∀ o, (transitionEffect H J o).IsPositive) ∧
      (∑ o, transitionEffect H J o) = 1 := by
  refine ⟨fun o => (transition_isProjection H hH hHsq o).isPositive.adjoint_conj J, ?_⟩
  apply LinearMap.ext
  intro q
  have hsum : (∑ o, transition H o (J q)) = J q := by
    simp only [Fintype.sum_prod_type, transition, LinearMap.mulLeftRight_apply]
    calc
      _ = ∑ s, spectralProjector H s * J q := by
        apply Finset.sum_congr rfl
        intro s _
        rw [← Matrix.mul_sum, spectralProjector_sum, Matrix.mul_one]
      _ = _ := by rw [← Matrix.sum_mul, spectralProjector_sum, Matrix.one_mul]
  have hiso : J.adjoint (J q) = q := by
    apply ext_inner_left ℂ
    intro x
    rw [LinearMap.adjoint_inner_right]
    exact (LinearMap.norm_map_iff_inner_map_map J).mp hJ x q
  simp only [LinearMap.sum_apply, transitionEffect, LinearMap.comp_apply,
    Module.End.one_apply]
  rw [← map_sum, hsum]
  exact hiso

/-- The four effects of an actual involution with normalized retained-identity
amplification, including their transition weights on arbitrary complex matrices. -/
theorem normalized_transition_povm [DecidableEq b] [DecidableEq e] [Nonempty b]
    (H : Matrix (b × e) (b × e) ℂ) (hH : H.IsHermitian) (hHsq : H * H = 1) :
    let J := normalizedAmplification (b := b) (e := e)
    (∀ o, (transitionEffect H J o).IsPositive) ∧
      (∑ o, transitionEffect H J o) = 1 ∧
      (∀ o q, inner ℂ q (transitionEffect H J o q) =
        ((‖spectralProjector H o.1 * J q * spectralProjector H o.2‖ ^ 2 : ℝ) : ℂ)) := by
  let J := normalizedAmplification (b := b) (e := e)
  obtain ⟨hpos, hsum⟩ := transition_povm H hH hHsq J (normalizedAmplification_norm (b := b))
  refine ⟨hpos, hsum, fun o q => ?_⟩
  rw [← (hpos o).isSymmetric q q]
  exact transitionEffect_inner H hH hHsq J o q

/-- The normalized two-copy amplification in the coordinates of the physical involution. -/
def normalizedBlockAmplification :
    Matrix e e ℂ →ₗ[ℂ] Matrix (e ⊕ e) (e ⊕ e) ℂ where
  toFun q := (Real.sqrt 2)⁻¹ • Matrix.fromBlocks q 0 0 q
  map_add' X Y := by
    change (Real.sqrt 2)⁻¹ • Matrix.fromBlocks (X + Y) 0 0 (X + Y) =
      (Real.sqrt 2)⁻¹ • Matrix.fromBlocks X 0 0 X + (Real.sqrt 2)⁻¹ • Matrix.fromBlocks Y 0 0 Y
    rw [← smul_add, Matrix.fromBlocks_add, add_zero]
  map_smul' z X := by
    simp only [RingHom.id_apply]
    calc
      _ = (Real.sqrt 2)⁻¹ • (z • Matrix.fromBlocks X 0 0 X) := by
        simp only [Matrix.fromBlocks_smul, smul_zero]
      _ = _ := smul_comm _ _ _

private theorem normalizedBlockAmplification_norm (q : Matrix e e ℂ) :
    ‖normalizedBlockAmplification q‖ = ‖q‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  change ‖(Real.sqrt 2)⁻¹ • (Matrix.fromBlocks q 0 0 q)‖ ^ 2 = _
  have hblocks : ‖Matrix.fromBlocks q 0 0 q‖ ^ 2 = 2 * ‖q‖ ^ 2 := by
    apply Complex.ofReal_injective
    rw [Complex.ofReal_mul]
    simp only [Complex.ofReal_ofNat, frobenius_norm_sq_eq_trace,
      Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
      Matrix.conjTranspose_zero, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
    simp [Matrix.trace, Fintype.sum_sum_type, Matrix.fromBlocks_apply₁₁,
      Matrix.fromBlocks_apply₂₂, two_mul]
  rw [inv_sqrt_smul_norm_sq _ (by norm_num), hblocks]
  ring

variable [DecidableEq e]

private theorem physical_involution (a : Matrix e e ℂ) (U : Matrix.unitaryGroup e ℂ)
    (ha₁ : (1 / 4 : ℝ) • (1 : Matrix e e ℂ) ≤ a)
    (ha₂ : a ≤ (3 / 4 : ℝ) • (1 : Matrix e e ℂ)) :
    (physicalInvolution a U).IsHermitian ∧ physicalInvolution a U * physicalInvolution a U = 1 := by
  obtain ⟨hVp, _, _, hPp, _⟩ := spectral_isometries a U ha₁ ha₂
  let H := physicalInvolution a U
  let V := plusIsometry a U
  have hH : H = (2 : ℝ) • (V * Vᴴ) - 1 := by
    change V * Vᴴ = (1 / 2 : ℝ) • (1 + H) at hPp
    rw [hPp]
    module
  have hp : (V * Vᴴ) * (V * Vᴴ) = V * Vᴴ := by
    calc
      _ = V * (Vᴴ * V) * Vᴴ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hVp, Matrix.mul_one]
  refine ⟨?_, ?_⟩
  · change H.IsHermitian
    rw [hH]
    exact ((Matrix.isHermitian_mul_conjTranspose_self V).smul (IsSelfAdjoint.all (2 : ℝ))).sub
      Matrix.isHermitian_one
  · change H * H = 1
    rw [hH]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, Matrix.mul_one, smul_smul, hp]
    module

/-- The state-independent fair law gives half the identity to each same-sign pair. -/
def fairPairEffect (o : Bool × Bool) : Matrix e e ℂ →ₗ[ℂ] Matrix e e ℂ :=
  if o.1 = o.2 then (1 / 2 : ℂ) • 1 else 0

/-- Subtract the fair component of weight `1/16` and normalize the remainder. -/
def residualEffect (H : Matrix (e ⊕ e) (e ⊕ e) ℂ) (o : Bool × Bool) :
    Matrix e e ℂ →ₗ[ℂ] Matrix e e ℂ :=
  (16 / 15 : ℂ) •
    (transitionEffect H normalizedBlockAmplification o - (1 / 16 : ℂ) • fairPairEffect o)

/-- For the physical unflagged involution, both same-sign effects dominate
`I/32` simultaneously. The residual is a POVM and the original effects are
its mixture with the fair same-sign POVM at weight `1/16`. -/
theorem physical_transition_residual_povm (a : Matrix e e ℂ) (U : Matrix.unitaryGroup e ℂ)
    (ha₁ : (1 / 4 : ℝ) • (1 : Matrix e e ℂ) ≤ a)
    (ha₂ : a ≤ (3 / 4 : ℝ) • (1 : Matrix e e ℂ)) :
    let H := physicalInvolution a U
    let E := transitionEffect H normalizedBlockAmplification
    let R := residualEffect H
    (∀ o, (E o).IsPositive) ∧ (∑ o, E o) = 1 ∧
      (∀ o q, inner ℂ q (E o q) =
        ((‖spectralProjector H o.1 * Matrix.fromBlocks q 0 0 q *
          spectralProjector H o.2‖ ^ 2 / 2 : ℝ) : ℂ)) ∧
      (∀ s, (E (s, s) - (1 / 32 : ℂ) • 1).IsPositive) ∧
      (∀ o, (fairPairEffect (e := e) o).IsPositive) ∧ (∑ o, fairPairEffect (e := e) o) = 1 ∧
      (∀ o, (R o).IsPositive) ∧ (∑ o, R o) = 1 ∧
      (∀ o, E o = (1 / 16 : ℂ) • fairPairEffect o + (15 / 16 : ℂ) • R o) := by
  let H := physicalInvolution a U
  let E := transitionEffect H normalizedBlockAmplification
  let R := residualEffect H
  obtain ⟨hH, hHsq⟩ := physical_involution a U ha₁ ha₂
  obtain ⟨hEpos, hEsum⟩ := transition_povm H hH hHsq _ normalizedBlockAmplification_norm
  have hweight (o : Bool × Bool) (q : Matrix e e ℂ) :
      inner ℂ (E o q) q =
        ((‖spectralProjector H o.1 * Matrix.fromBlocks q 0 0 q *
          spectralProjector H o.2‖ ^ 2 / 2 : ℝ) : ℂ) := by
    rw [show E = transitionEffect H normalizedBlockAmplification from rfl,
      transitionEffect_inner H hH hHsq]
    change ((‖spectralProjector H o.1 * ((Real.sqrt 2)⁻¹ • Matrix.fromBlocks q 0 0 q) *
        spectralProjector H o.2‖ ^ 2 : ℝ) : ℂ) = _
    rw [Matrix.mul_smul, Matrix.smul_mul, inv_sqrt_smul_norm_sq _ (by norm_num)]
  have hfloor (s : Bool) : (E (s, s) - (1 / 32 : ℂ) • 1).IsPositive := by
    apply (LinearMap.isPositive_iff_complex _).mpr
    intro q
    obtain ⟨hplus, hminus⟩ := same_sign_transition_lower a q U ha₁ ha₂
    have hbound : ‖q‖ ^ 2 / 32 ≤
        ‖spectralProjector H s * Matrix.fromBlocks q 0 0 q * spectralProjector H s‖ ^ 2 / 2 := by
      cases s
      · exact hminus
      · exact hplus
    have hq : inner ℂ (((1 / 32 : ℂ) • (1 : Matrix e e ℂ →ₗ[ℂ] Matrix e e ℂ)) q) q =
        ((‖q‖ ^ 2 / 32 : ℝ) : ℂ) := by
      rw [LinearMap.smul_apply, Module.End.one_apply, inner_smul_left,
        inner_self_eq_frobenius_sq, starRingEnd_apply, star_div₀, star_one, star_ofNat]
      push_cast <;> ring
    rw [LinearMap.sub_apply, inner_sub_left, hweight, hq, ← Complex.ofReal_sub]
    constructor
    · rw [RCLike.re_to_complex, Complex.ofReal_re]
    · simpa only [RCLike.re_to_complex, Complex.ofReal_re] using sub_nonneg.mpr hbound
  have hFpos (o : Bool × Bool) : (fairPairEffect (e := e) o).IsPositive := by
    unfold fairPairEffect
    split
    · exact LinearMap.isPositive_one.smul_of_nonneg (by norm_num [Complex.le_def])
    · exact LinearMap.isPositive_zero
  have hFsum : (∑ o, fairPairEffect (e := e) o) = 1 := by
    simp only [Fintype.sum_prod_type, Fintype.sum_bool]
    change ((1 / 2 : ℂ) • (1 : Matrix e e ℂ →ₗ[ℂ] Matrix e e ℂ) + 0) +
      (0 + (1 / 2 : ℂ) • 1) = 1
    rw [add_zero, zero_add, ← add_smul, show (1 / 2 : ℂ) + 1 / 2 = 1 by norm_num, one_smul]
  have hRpos (o : Bool × Bool) : (R o).IsPositive := by
    change ((16 / 15 : ℂ) • (E o - (1 / 16 : ℂ) • fairPairEffect o)).IsPositive
    apply LinearMap.IsPositive.smul_of_nonneg _ (by norm_num [Complex.le_def] : (0 : ℂ) ≤ 16 / 15)
    rcases o with ⟨s, t⟩
    change (E (s, t) - (1 / 16 : ℂ) • (if s = t then (1 / 2 : ℂ) • 1 else 0)).IsPositive
    by_cases h : s = t
    · subst t
      rw [ite_eq_left rfl, smul_smul, show (1 / 16 : ℂ) * (1 / 2) = 1 / 32 by norm_num]
      exact hfloor s
    · rw [ite_eq_right h, smul_zero, sub_zero]
      exact hEpos (s, t)
  have hRsum : (∑ o, R o) = 1 := by
    change (∑ o, (16 / 15 : ℂ) • (E o - (1 / 16 : ℂ) • fairPairEffect o)) = 1
    rw [← Finset.smul_sum, Finset.sum_sub_distrib, ← Finset.smul_sum, hEsum, hFsum]
    module
  refine ⟨hEpos, hEsum, ?_, hfloor, hFpos, hFsum, hRpos, hRsum, ?_⟩
  · intro o q
    rw [← (hEpos o).isSymmetric q q]
    exact hweight o q
  · intro o
    change E o = (1 / 16 : ℂ) • fairPairEffect o +
      (15 / 16 : ℂ) • ((16 / 15 : ℂ) • (E o - (1 / 16 : ℂ) • fairPairEffect o))
    module

/-- In flag-first coordinates the flagged involution is `H ⊕ (-H)`.
Its action on a left/right flag block flips each sign independently according
to that block's flag. Each block can contain an arbitrary complex matrix. -/
private theorem flagged_transition_blocks [DecidableEq d] (H : Matrix d d ℂ)
    (s t : Bool) (Xpp Xpm Xmp Xmm : Matrix d d ℂ) :
    transition (Matrix.fromBlocks H 0 0 (-H)) (s, t) (Matrix.fromBlocks Xpp Xpm Xmp Xmm) =
      Matrix.fromBlocks (transition H (s, t) Xpp) (transition H (s, !t) Xpm)
        (transition H (!s, t) Xmp) (transition H (!s, !t) Xmm) := by
  have hI : (1 : Matrix (d ⊕ d) (d ⊕ d) ℂ) =
      Matrix.fromBlocks (1 : Matrix d d ℂ) 0 0 (1 : Matrix d d ℂ) :=
    Matrix.fromBlocks_one.symm
  have hproj (u : Bool) :
      spectralProjector (Matrix.fromBlocks H 0 0 (-H)) u =
        Matrix.fromBlocks (spectralProjector H u) 0 0 (spectralProjector H (!u)) := by
    cases u <;> simp only [Bool.not, spectralProjector, hI, sub_eq_add_neg,
      Matrix.fromBlocks_neg, Matrix.fromBlocks_add, Matrix.fromBlocks_smul,
      neg_zero, neg_neg, zero_add, smul_zero]
  simp only [transition, LinearMap.mulLeftRight_apply, hproj, Matrix.fromBlocks_multiply,
    Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero]

/-- The normalized amplification and the physical flag transitions act on
each left/right flag block with its own signs. The reindexing moves the
flag ahead of the retained qubit. -/
theorem physical_flag_transition_blocks (a : Matrix e e ℂ) (U : Matrix.unitaryGroup e ℂ)
    (s t : Bool) (qpp qpm qmp qmm : Matrix e e ℂ) :
    let H := physicalInvolution a U
    let Q := Matrix.fromBlocks qpp qpm qmp qmm
    let swap := Equiv.sumSumSumComm e e e e
    let J := normalizedBlockAmplification (e := e)
    transition (Matrix.fromBlocks H 0 0 (-H)) (s, t)
        ((normalizedBlockAmplification Q).submatrix swap swap) =
      Matrix.fromBlocks (transition H (s, t) (J qpp)) (transition H (s, !t) (J qpm))
        (transition H (!s, t) (J qmp)) (transition H (!s, !t) (J qmm)) := by
  dsimp only
  have hswap :
      let swap := Equiv.sumSumSumComm e e e e
      (normalizedBlockAmplification (Matrix.fromBlocks qpp qpm qmp qmm)).submatrix swap swap =
        Matrix.fromBlocks (normalizedBlockAmplification qpp) (normalizedBlockAmplification qpm)
          (normalizedBlockAmplification qmp) (normalizedBlockAmplification qmm) := by
    dsimp only
    ext i j
    rcases i with ((i | i) | (i | i)) <;> rcases j with ((j | j) | (j | j)) <;>
      simp [normalizedBlockAmplification, Matrix.submatrix_apply, Matrix.smul_apply,
        Equiv.sumSumSumComm, Matrix.fromBlocks]
  rw [hswap]
  exact flagged_transition_blocks _ _ _ _ _ _ _

/-- The squared two-site transition amplitude on Kronecker inputs is the
product of the two local squared amplitudes. The joint matrices are ordered by site. -/
theorem two_site_transition_norm_sq {d' e' : Type*} [Fintype d'] [Fintype e']
    [DecidableEq d] [DecidableEq d']
    (H₁ : Matrix d d ℂ) (H₂ : Matrix d' d' ℂ)
    (J₁ : Matrix e e ℂ →ₗ[ℂ] Matrix d d ℂ)
    (J₂ : Matrix e' e' ℂ →ₗ[ℂ] Matrix d' d' ℂ)
    (o₁ o₂ : Bool × Bool) (q₁ : Matrix e e ℂ) (q₂ : Matrix e' e' ℂ) :
    ‖(spectralProjector H₁ o₁.1 ⊗ₖ spectralProjector H₂ o₂.1) *
        (J₁ q₁ ⊗ₖ J₂ q₂) *
        (spectralProjector H₁ o₁.2 ⊗ₖ spectralProjector H₂ o₂.2)‖ ^ 2 =
      ‖transition H₁ o₁ (J₁ q₁)‖ ^ 2 * ‖transition H₂ o₂ (J₂ q₂)‖ ^ 2 := by
  simp only [← Matrix.mul_kronecker_mul, frobenius_sq_kronecker,
    transition, LinearMap.mulLeftRight_apply]

#print axioms normalized_transition_povm
#print axioms physical_transition_residual_povm
#print axioms physical_flag_transition_blocks
#print axioms two_site_transition_norm_sq

end D5.S3.Quantum.Recovery.LocalCompression.PetzTransitionPOVM
