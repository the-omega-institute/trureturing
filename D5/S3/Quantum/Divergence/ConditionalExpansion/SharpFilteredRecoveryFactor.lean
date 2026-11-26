/- GID: D5/S3/Quantum/Divergence/ConditionalExpansion/SharpFilteredRecoveryFactor
   generality: G
   mirror-B: D5/B/S3/Quantum/Divergence/ConditionalExpansion/SharpFilteredRecoveryFactor
   mirror-E: none(waiver:finite-matrix-proof)
   anchors: []
   utility: none
   digest: Filtered complementary depolarizing channels witness sharpness of the dimension-square recovery factor. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.Quantum.Divergence.ConditionalExpansion.FilteredChannelConditionalGap
import D5.S3.Quantum.Divergence.ConditionalExpansion.BellKernelLimit
import D5.S3.Quantum.Recovery.KrausLeftInverseNecessity

/-!
The complementary depolarizing family of Datta–Holevo,
"Complementarity and additivity for depolarizing channels",
arXiv:quant-ph/0510145, §3, (11), (16). The conditional expansion
coefficient is that of Hirche–George–Nuradha–Wilde,
arXiv:2608.27171v1, Eq. (2.42).

For this family the normalized inverse marginal gives a lower bound on
every conditional ratio, while the exact scalar-identity recovery
condition gives an upper bound on every finite recovery weight.
The parameter can be chosen algebraically for any proposed factor below d².
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace D5.S3.Quantum.Divergence.ConditionalExpansion.SharpFilteredRecoveryFactor

open scoped _root_.Matrix BigOperators ComplexOrder MatrixOrder Kronecker Matrix.Norms.L2Operator
open FilteredChannelConditionalGap
open D5.S3.Quantum.Divergence.ConditionalExpansion.BellCenteredConditionalTraceGap
  (bellProjector)
open D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction
  (act amp gap partialTraceRight_smul ptr ptr_sub_smul ratios)
open D5.S3.Quantum.Foundation.FiniteStateChannel (QuantumChannel)
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf (MatrixMap)
open D5.S3.Quantum.Information.PartialTraceMutualInformation
  (density_posSemidef partialTraceRight partialTraceRight_add)
open D5.S3.Quantum.Recovery.KrausLeftInverseNecessity (identity_kraus_scalar)
open UnitaryReconstruction.LiuWildChoiObstruction (bell bell_norm diagonalVector outer pairMatrix)

open private bell_marginal from D5.S3.Quantum.Divergence.CompleteHockeyStickChoiSupport
open private injection injection_expand from
  D5.S3.Quantum.Divergence.ConditionalExpansion.FilteredChannelConditionalGap

variable {A : Type} [Fintype A] [DecidableEq A] [Nonempty A]

/-- The complementary depolarizing parameter. -/
def complementaryParameter (d a : ℝ) : ℝ := (d ^ 2 - a) / (d ^ 2 - 1)

/-- The normalized inverse-marginal harmonic parameter. -/
def harmonicParameter (d a : ℝ) : ℝ :=
  ((a⁻¹ + (d ^ 2 - 1) * (complementaryParameter d a)⁻¹) / d ^ 2)⁻¹

/-- Datta–Holevo filter in the reference-first product basis. -/
def sharpFilter (A : Type) [Fintype A] [DecidableEq A] (a : ℝ) :
    Matrix (A × A) (A × A) ℂ :=
  a • bellProjector A +
    complementaryParameter (Fintype.card A) a • (1 - bellProjector A)

omit [Nonempty A] in
private theorem bell_psd : (bellProjector A).PosSemidef :=
  Matrix.posSemidef_vecMulVec_self_star (bell A)

private theorem bell_idempotent : bellProjector A * bellProjector A = bellProjector A := by
  simp only [bellProjector, outer, Matrix.vecMulVec_mul_vecMulVec, bell_norm, one_smul]

private theorem bell_complement_psd :
    ((1 : Matrix (A × A) (A × A) ℂ) - bellProjector A).PosSemidef := by
  let C := (1 : Matrix (A × A) (A × A) ℂ) - bellProjector A
  have h := Matrix.posSemidef_conjTranspose_mul_self C
  have hGram : Cᴴ * C = C := by
    dsimp only [C]
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
      (bell_psd (A := A)).isHermitian.eq, sub_mul, Matrix.one_mul, mul_sub,
      Matrix.mul_one, bell_idempotent, sub_self, sub_zero]
  rwa [hGram] at h

private theorem bell_partialTrace :
    partialTraceRight (bellProjector A) =
      (Fintype.card A : ℝ)⁻¹ • (1 : Matrix A A ℂ) := by
  have hbell : partialTraceRight (bellProjector A) =
      (Fintype.card A : ℂ)⁻¹ • (1 : Matrix A A ℂ) := bell_marginal
  rw [hbell]
  ext i j
  simp [Matrix.smul_apply, Complex.real_smul, smul_eq_mul]

private theorem normalized_bell_marginal (s t : ℝ) :
    let d : ℝ := Fintype.card A
    d⁻¹ • partialTraceRight
      (s • bellProjector A + t • (1 - bellProjector A)) =
        ((s + (d ^ 2 - 1) * t) / d ^ 2) • (1 : Matrix A A ℂ) := by
  intro d
  have hd : d ≠ 0 := by
    dsimp only [d]
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card A ≠ 0)
  have hI : partialTraceRight (1 : Matrix (A × A) (A × A) ℂ) =
      d • (1 : Matrix A A ℂ) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [partialTraceRight, Matrix.smul_apply, Complex.real_smul, d]
    · simp [partialTraceRight, Matrix.smul_apply, Prod.mk.injEq, hij]
  have hC : partialTraceRight (1 - bellProjector A) =
      (d - d⁻¹) • (1 : Matrix A A ℂ) := by
    change ptr (1 - bellProjector A) = _
    have hs := ptr_sub_smul (1 : ℝ) (1 : Matrix (A × A) (A × A) ℂ) (bellProjector A)
    simp only [one_smul, ptr] at hs
    change partialTraceRight (1 - bellProjector A) = _
    rw [hs, hI, bell_partialTrace, sub_smul]
  rw [partialTraceRight_add, partialTraceRight_smul, partialTraceRight_smul,
    bell_partialTrace, hC]
  change d⁻¹ • (s • (d⁻¹ • (1 : Matrix A A ℂ)) +
    t • ((d - d⁻¹) • (1 : Matrix A A ℂ))) = _
  rw [smul_smul, smul_smul, ← add_smul, smul_smul]
  congr 1
  field_simp [hd]

omit [DecidableEq A] [Nonempty A] in
private theorem dimension_square_gt_one (hd : 2 ≤ Fintype.card A) :
    1 < (Fintype.card A : ℝ) ^ 2 := by
  have h : (2 : ℝ) ≤ Fintype.card A := by exact_mod_cast hd
  nlinarith [sq_nonneg ((Fintype.card A : ℝ) - 2)]

omit [DecidableEq A] [Nonempty A] in
private theorem parameter_gt_a (a : ℝ) (ha : a < 1) (hd : 1 < (Fintype.card A : ℝ) ^ 2) :
    a < complementaryParameter (Fintype.card A) a := by
  unfold complementaryParameter
  apply (lt_div_iff₀ (sub_pos.mpr hd)).mpr
  nlinarith [mul_pos (sub_pos.mpr ha) (show 0 < (Fintype.card A : ℝ) ^ 2 by linarith)]

theorem sharpFilter_posDef (a : ℝ) (ha : 0 < a) (ha₁ : a < 1)
    (hd : 2 ≤ Fintype.card A) : (sharpFilter A a).PosDef := by
  let b := complementaryParameter (Fintype.card A) a
  let P := bellProjector A
  have hab : a < b := parameter_gt_a a ha₁ (dimension_square_gt_one hd)
  have hG : sharpFilter A a = a • (1 : Matrix (A × A) (A × A) ℂ) +
      (b - a) • (1 - P) := by
    change a • P + b • (1 - P) = _
    rw [sub_smul, smul_sub a]
    abel
  rw [hG]
  exact (Matrix.PosDef.one.smul ha).add_posSemidef
    ((bell_complement_psd (A := A)).smul (sub_nonneg.mpr hab.le))

theorem sharpFilter_normalized (a : ℝ) (hd : 2 ≤ Fintype.card A) :
    (Fintype.card A : ℝ)⁻¹ • partialTraceRight (sharpFilter A a) = 1 := by
  have hd' := dimension_square_gt_one hd
  have hn : (Fintype.card A : ℝ) ^ 2 ≠ 0 := by linarith
  unfold sharpFilter
  rw [normalized_bell_marginal]
  unfold complementaryParameter
  have he : (a + ((Fintype.card A : ℝ) ^ 2 - 1) *
      (((Fintype.card A : ℝ) ^ 2 - a) / ((Fintype.card A : ℝ) ^ 2 - 1))) /
      (Fintype.card A : ℝ) ^ 2 = 1 := by
    field_simp [hn, sub_ne_zero.mpr (ne_of_gt hd')]
    ring
  rw [he, one_smul]

private theorem bellCombination_inverse (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    (a • bellProjector A + b • (1 - bellProjector A))⁻¹ =
      a⁻¹ • bellProjector A + b⁻¹ • (1 - bellProjector A) := by
  let P := bellProjector A
  let C : Matrix (A × A) (A × A) ℂ := 1 - P
  have hPP : P * P = P := bell_idempotent
  have hPC : P * C = 0 := by
    dsimp only [C]
    rw [mul_sub, Matrix.mul_one, hPP, sub_self]
  have hCP : C * P = 0 := by
    dsimp only [C]
    rw [sub_mul, Matrix.one_mul, hPP, sub_self]
  have hCC : C * C = C := by
    change (1 - P) * C = C
    rw [sub_mul, Matrix.one_mul, hPC, sub_zero]
  apply Matrix.inv_eq_right_inv
  change (a • P + b • C) * (a⁻¹ • P + b⁻¹ • C) = 1
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, hPP, hPC, hCP, hCC, inv_mul_cancel₀ ha, inv_mul_cancel₀ hb,
    one_smul, smul_zero, add_zero, zero_add]
  dsimp only [C]
  abel

theorem sharpFilter_inverse_marginal (a : ℝ) (ha : 0 < a) (ha₁ : a < 1)
    (hd : 2 ≤ Fintype.card A) :
    (Fintype.card A : ℝ)⁻¹ • partialTraceRight (sharpFilter A a)⁻¹ =
      (harmonicParameter (Fintype.card A) a)⁻¹ • (1 : Matrix A A ℂ) := by
  have hb := ha.trans (parameter_gt_a a ha₁ (dimension_square_gt_one hd))
  unfold sharpFilter
  rw [bellCombination_inverse _ _ ha.ne' hb.ne', normalized_bell_marginal]
  simp only [harmonicParameter, inv_inv]

omit [DecidableEq A] [Nonempty A] in
private theorem inverse_harmonic_pos (a : ℝ) (ha : 0 < a) (ha₁ : a < 1)
    (hd : 2 ≤ Fintype.card A) :
    0 < (harmonicParameter (Fintype.card A) a)⁻¹ := by
  have hD := dimension_square_gt_one hd
  have hb := ha.trans (parameter_gt_a a ha₁ hD)
  simp only [harmonicParameter, inv_inv]
  exact div_pos (add_pos_of_pos_of_nonneg (inv_pos.mpr ha)
    (mul_nonneg (sub_nonneg.mpr hD.le) (inv_nonneg.mpr hb.le))) (by linarith)

/-- Every admissible ratio of the actual filtered channel is bounded below
by the explicit harmonic parameter, with arbitrary finite references. -/
theorem sharp_family_ratio_lower_bound
    (a : ℝ) (ha : 0 < a) (ha₁ : a < 1) (hd : 2 ≤ Fintype.card A)
    (N : QuantumChannel A (A × A))
    (hN : ∀ X, act N X = filterAction (sharpFilter A a) X)
    (γ : ℝ) (orth : Bool) {x : ℝ} (hx : x ∈ ratios N γ orth) :
    harmonicParameter (Fintype.card A) a ≤ x := by
  have h := filtered_channel_ratio_lower_bound (sharpFilter A a)
    (sharpFilter_posDef a ha ha₁ hd) (sharpFilter_normalized a hd) N hN γ orth hx
  rw [sharpFilter_inverse_marginal a ha ha₁ hd, norm_smul, norm_one, mul_one,
    Real.norm_eq_abs, abs_of_pos (inverse_harmonic_pos a ha ha₁ hd), inv_inv] at h
  exact h

/-- Every admissible finite exact heralded recovery of this actual channel
has weight at most the small Bell eigenvalue. The test vector is the
unnormalized Bell vector, so both sides of its quadratic-form inequality
carry the same factor d. -/
theorem sharp_family_recovery_upper_bound {J : Type*} [Fintype J]
    (a : ℝ) (ha : 0 < a) (ha₁ : a < 1) (hd : 2 ≤ Fintype.card A)
    (N : QuantumChannel A (A × A))
    (hN : ∀ X, act N X = filterAction (sharpFilter A a) X)
    (L : J → Matrix A (A × A) ℂ) (p : ℝ) (hp : 0 ≤ p)
    (heffect : (∑ j, (L j)ᴴ * L j) ≤ (1 : Matrix (A × A) (A × A) ℂ))
    (hrec : ∀ X : Matrix A A ℂ, MatrixMap.of_kraus L L (act N X) = (p : ℂ) • X) :
    p ≤ a := by
  classical
  by_cases hp0 : p = 0
  · simpa [hp0] using ha.le
  have hp' : 0 < p := lt_of_le_of_ne hp (Ne.symm hp0)
  let d : ℝ := Fintype.card A
  have hd' : 0 < d := by
    dsimp only [d]
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card A)
  let G := sharpFilter A a
  let S := CFC.sqrt G
  have hG : G.PosDef := sharpFilter_posDef a ha ha₁ hd
  have hS0 : 0 ≤ S := CFC.sqrt_nonneg G
  have hS : Sᴴ = S := (Matrix.nonneg_iff_posSemidef.mp hS0).isHermitian.eq
  have hSS : S * S = G := CFC.sqrt_mul_sqrt_self G hG.posSemidef.nonneg
  let K : A → Matrix (A × A) A ℂ := injection
  let T : J × A → Matrix A A ℂ := fun ji => L ji.1 * S * K ji.2
  -- The unscaled coordinate Kraus matrices give d times the filter action.
  have hsum (X : Matrix A A ℂ) :
      (∑ i : A, (S * K i) * X * (S * K i)ᴴ) = d • act N X := by
    calc
      _ = S * (∑ i : A, K i * X * (K i)ᴴ) * S := by
        simp only [Matrix.conjTranspose_mul, hS, Matrix.mul_sum, Matrix.sum_mul,
          Matrix.mul_assoc]
      _ = d • act N X := by
        dsimp only [K]
        rw [injection_expand, hN, filterAction]
        change S * (X ⊗ₖ (1 : Matrix A A ℂ)) * S =
          d • (S * (d⁻¹ • (X ⊗ₖ (1 : Matrix A A ℂ))) * S)
        rw [Matrix.mul_smul, Matrix.smul_mul, smul_smul, mul_inv_cancel₀ hd'.ne', one_smul]
  have hcomp (X : Matrix A A ℂ) :
      (∑ ji, T ji * X * (T ji)ᴴ) = (p * d) • X := by
    calc
      _ = ∑ j : J, L j * (∑ i : A, (S * K i) * X * (S * K i)ᴴ) *
          (L j)ᴴ := by
        simp only [T, Fintype.sum_prod_type, Matrix.conjTranspose_mul,
          Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_assoc]
      _ = d • MatrixMap.of_kraus L L (act N X) := by
        simp only [hsum, MatrixMap.of_kraus, LinearMap.sum_apply, LinearMap.coe_mk,
          AddHom.coe_mk, Matrix.mul_smul, Matrix.smul_mul, Finset.smul_sum]
      _ = (p * d) • X := by
        rw [hrec]
        ext u v
        simp only [Matrix.smul_apply, Complex.real_smul, smul_eq_mul, Complex.ofReal_mul]
        ring
  let r := (Real.sqrt (p * d))⁻¹
  have hpd : 0 < p * d := mul_pos hp' hd'
  have hr : 0 < r := inv_pos.mpr (Real.sqrt_pos.mpr hpd)
  have hrprod : r * r * (p * d) = 1 := by
    have hs := Real.sq_sqrt hpd.le
    have hs0 := (Real.sqrt_pos.mpr hpd).ne'
    dsimp only [r]
    field_simp [hs0]
    nlinarith
  let F : J × A → Matrix A A ℂ := fun ji => r • T ji
  have hF (X : Matrix A A ℂ) : (∑ ji, F ji * X * (F ji)ᴴ) = X := by
    simp only [F, Matrix.conjTranspose_smul, star_trivial, Matrix.smul_mul,
      Matrix.mul_smul, smul_smul, ← Finset.smul_sum, hcomp, hrprod, one_smul]
  let i₀ : A := Classical.choice inferInstance
  let c : J × A → ℂ := fun ji => T ji i₀ i₀
  have hc (ji : J × A) : T ji = c ji • (1 : Matrix A A ℂ) := by
    have hh := identity_kraus_scalar F hF i₀ ji
    ext x y
    have ht := congrArg (fun M : Matrix A A ℂ => M x y) hh
    simp only [F, Matrix.smul_apply, Complex.real_smul, smul_eq_mul] at ht
    change T ji x y = T ji i₀ i₀ * (1 : Matrix A A ℂ) x y
    apply mul_left_cancel₀ (show (r : ℂ) ≠ 0 by exact_mod_cast hr.ne')
    rw [ht, mul_assoc]
  have hweight : (∑ ji, star (c ji) * c ji) = ((p * d : ℝ) : ℂ) := by
    have ht (ji : J × A) :
        T ji * 1 * (T ji)ᴴ = (star (c ji) * c ji) • (1 : Matrix A A ℂ) := by
      rw [hc ji]
      simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_one, Matrix.mul_one,
        Matrix.mul_smul, smul_smul]
    have hm : (∑ ji, T ji * (1 : Matrix A A ℂ) * (T ji)ᴴ) =
        (p * d) • (1 : Matrix A A ℂ) := hcomp 1
    simp_rw [ht] at hm
    have hh := congrArg (fun M : Matrix A A ℂ => M i₀ i₀) hm
    simpa only [Matrix.sum_apply, Matrix.smul_apply, Matrix.one_apply_eq,
      Complex.real_smul, smul_eq_mul, mul_one] using hh
  let B : J → Matrix A (A × A) ℂ := fun j => L j * S
  let v := diagonalVector A
  have hinj (j : J) (i x y : A) :
      (B j * K i) x y = B j x (y,i) := by
    rw [Matrix.mul_apply, Finset.sum_eq_single (y,i)]
    · simp [K, injection]
    · intro z _ hz
      simp [K, injection, hz]
    · simp
  have hentry (j : J) (i x y : A) :
      B j x (y,i) = c (j,i) * (1 : Matrix A A ℂ) x y := by
    rw [← hinj j i x y]
    exact congrArg (fun M : Matrix A A ℂ => M x y) (hc (j,i))
  have hBv (j : J) : B j *ᵥ v = fun i => c (j,i) := by
    funext x
    change (∑ z : A × A, B j x z * diagonalVector A z) = _
    simp only [Fintype.sum_prod_type, diagonalVector, mul_ite, mul_one, mul_zero]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    simp [hentry, Matrix.one_apply, mul_ite, Finset.sum_ite_eq]
  -- Test the conjugated recovery-effect inequality on the Bell vector.
  have hmajor : (G - ∑ j, (B j)ᴴ * B j).PosSemidef := by
    have h := (Matrix.le_iff.mp heffect).conjTranspose_mul_mul_same S
    rw [hS, Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, hSS] at h
    convert h using 1
    simp only [B, Matrix.conjTranspose_mul, hS, Matrix.mul_sum, Matrix.sum_mul,
      Matrix.mul_assoc]
  have hvnorm : star v ⬝ᵥ v = (d : ℂ) := by
    simp [v, diagonalVector, dotProduct, Fintype.sum_prod_type, d]
  have hPv : bellProjector A *ᵥ v = v := by
    have hbell : bellProjector A *ᵥ bell A = bell A := by
      simp only [bellProjector, outer, Matrix.vecMulVec_mulVec, bell_norm,
        MulOpposite.op_one, one_smul]
    have hv : v = ((Real.sqrt d : ℝ) : ℂ) • bell A := by
      have hs : ((Real.sqrt d : ℝ) : ℂ) ≠ 0 := by
        exact_mod_cast (Real.sqrt_pos.mpr hd').ne'
      change v = ((Real.sqrt d : ℝ) : ℂ) •
        (((Real.sqrt d : ℝ) : ℂ)⁻¹ • v)
      rw [smul_smul, mul_inv_cancel₀ hs, one_smul]
    rw [hv, Matrix.mulVec_smul, hbell]
  have hGv : G *ᵥ v = a • v := by
    change (a • bellProjector A + complementaryParameter d a •
      (1 - bellProjector A)) *ᵥ v = _
    simp only [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec,
      hPv, sub_self, smul_zero, add_zero]
  have hgram (j : J) :
      star v ⬝ᵥ (((B j)ᴴ * B j) *ᵥ v) = ∑ i, star (c (j,i)) * c (j,i) := by
    rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec, hBv]
    rfl
  have htest := hmajor.dotProduct_mulVec_nonneg v
  rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.sum_mulVec, dotProduct_sum,
    hGv, dotProduct_smul, hvnorm] at htest
  simp_rw [hgram] at htest
  rw [Fintype.sum_prod_type] at hweight
  rw [hweight] at htest
  have hreal := (Complex.nonneg_iff.mp htest).1
  simp only [Complex.real_smul, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero] at hreal
  exact le_of_mul_le_mul_right (sub_nonneg.mp hreal) hd'

/-- Closed rational expression for the harmonic parameter. -/
theorem harmonicParameter_closed_form (d a : ℝ) (hd : 2 ≤ d)
    (ha : 0 < a) (ha₁ : a < 1) :
    harmonicParameter d a = a * (d ^ 2 - a) / (1 + (d ^ 2 - 2) * a) := by
  let D := d ^ 2
  have hD : 4 ≤ D := by
    dsimp only [D]
    nlinarith [sq_nonneg (d - 2)]
  have hD0 : D ≠ 0 := by linarith
  have hDa : D - a ≠ 0 := by linarith
  unfold harmonicParameter complementaryParameter
  change ((a⁻¹ + (D - 1) * ((D - a) / (D - 1))⁻¹) / D)⁻¹ = _
  have hs : a⁻¹ + (D - 1) * ((D - a) / (D - 1))⁻¹ =
      ((1 + (D - 2) * a) * D) / (a * (D - a)) := by
    rw [inv_div]
    field_simp [ha.ne', hDa]
    ring
  rw [hs]
  have hh : ((1 + (D - 2) * a) * D / (a * (D - a))) / D =
      (1 + (D - 2) * a) / (a * (D - a)) := by
    field_simp [ha.ne', hDa, hD0]
  rw [hh, inv_div]

/-- An algebraic choice of a small positive Bell eigenvalue defeats every
nonnegative proposed dimension-dependent constant strictly below d². -/
theorem exists_small_parameter (d C : ℝ) (hd : 2 ≤ d)
    (hC : 0 ≤ C) (hCD : C < d ^ 2) :
    ∃ a : ℝ, 0 < a ∧ a < 1 ∧ C * a < harmonicParameter d a := by
  let D := d ^ 2
  let M := 1 + C * (D - 2)
  have hD : 4 ≤ D := by
    dsimp only [D]
    nlinarith [sq_nonneg (d - 2)]
  have hM : 0 < M := by
    dsimp only [M]
    exact add_pos_of_pos_of_nonneg zero_lt_one
      (mul_nonneg hC (by linarith))
  let a := min (1 / 2 : ℝ) ((D - C) / (2 * M))
  have hsmall : 0 < (D - C) / (2 * M) :=
    div_pos (sub_pos.mpr hCD) (mul_pos (by norm_num) hM)
  have ha : 0 < a := lt_min (by norm_num) hsmall
  have ha₁ : a < 1 := (min_le_left _ _).trans_lt (by norm_num)
  have ham := (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hM)).mp
    (min_le_right (1 / 2 : ℝ) ((D - C) / (2 * M)))
  have ham' : a * M < D - C := by
    change a * (2 * M) ≤ D - C at ham
    linarith [show 0 < D - C from sub_pos.mpr hCD,
      show a * (2 * M) = 2 * (a * M) by ring]
  have hden : 0 < 1 + (D - 2) * a :=
    add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg (by linarith) ha.le)
  have hlt : C * (1 + (D - 2) * a) < D - a := by
    dsimp only [M] at ham'
    linarith [show a * (1 + C * (D - 2)) =
      a + C * a * (D - 2) by ring,
      show C * (1 + (D - 2) * a) =
      C + C * a * (D - 2) by ring]
  refine ⟨a, ha, ha₁, ?_⟩
  rw [harmonicParameter_closed_form d a hd ha ha₁]
  apply (lt_div_iff₀ hden).mpr
  change C * a * (1 + (D - 2) * a) < a * (D - a)
  calc
    _ = a * (C * (1 + (D - 2) * a)) := by ring
    _ < _ := mul_lt_mul_of_pos_left hlt ha

omit [Nonempty A] in
/-- There is an admissible trace-distance ratio for any channel on an
input of dimension at least two. Use the existing Bell-kernel ratio witness. -/
private theorem trace_ratios_nonempty (N : QuantumChannel A (A × A))
    (hd : 2 ≤ Fintype.card A) : (ratios N 1 true).Nonempty := by
  obtain ⟨ρ, σ, horth, hgap, _⟩ :=
    D5.S3.Quantum.Divergence.ConditionalExpansion.exists_bell_kernel_ratio_le
      N hd 1 zero_lt_one
  exact ⟨_, Option A, inferInstance, inferInstance, pairMatrix ρ, pairMatrix σ,
    density_posSemidef ρ, ρ.2.2, density_posSemidef σ, σ.2.2, fun _ => horth, hgap, rfl⟩

/-- A strict witness against any smaller factor, stated directly in terms
of the actual filtered channel and finite recovery representations.
The orthogonal trace-distance test and the full tests at every γ ≥ 1
have the same infimum by conditional hockey-stick orthogonal reduction.
The recovery bound applies after unpacking any feasible finite Kraus witness. -/
theorem sharp_factor_witness (C : ℝ)
    (hd : 2 ≤ Fintype.card A) (hCD : C < (Fintype.card A : ℝ) ^ 2) :
    ∃ a : ℝ, 0 < a ∧ a < 1 ∧
      ∃ N : QuantumChannel A (A × A),
        (∀ X, act N X = filterAction (sharpFilter A a) X) ∧
        (∀ (J : Type) (fJ : Fintype J), letI := fJ
          ∀ (L : J → Matrix A (A × A) ℂ) (p : ℝ), 0 ≤ p →
            (∑ j, (L j)ᴴ * L j) ≤ (1 : Matrix (A × A) (A × A) ℂ) →
            (∀ X : Matrix A A ℂ,
              MatrixMap.of_kraus L L (act N X) = (p : ℂ) • X) →
            p ≤ a) ∧
        (C * a < sInf (ratios N 1 true)) ∧
        (∀ γ : ℝ, 1 ≤ γ → C * a < sInf (ratios N γ false)) := by
  have hd' : (2 : ℝ) ≤ Fintype.card A := by exact_mod_cast hd
  have hd_pos : 0 < (Fintype.card A : ℝ) ^ 2 :=
    zero_lt_one.trans (dimension_square_gt_one hd)
  obtain ⟨a, ha, ha₁, hlt⟩ :=
    exists_small_parameter (Fintype.card A) (max C 0) hd'
      (le_max_right C 0) (max_lt hCD hd_pos)
  have hCa : C * a < harmonicParameter (Fintype.card A) a :=
    (mul_le_mul_of_nonneg_right (le_max_left C 0) ha.le).trans_lt hlt
  obtain ⟨N, hN⟩ := exists_filtered_channel (sharpFilter A a)
    (sharpFilter_posDef a ha ha₁ hd) (sharpFilter_normalized a hd)
  refine ⟨a, ha, ha₁, N, hN, ?_, ?_⟩
  · intro J fJ
    let _ := fJ
    intro L p hp heffect hrec
    exact sharp_family_recovery_upper_bound a ha ha₁ hd N hN L p hp heffect hrec
  · have htrace : C * a < sInf (ratios N 1 true) :=
      hCa.trans_le (le_csInf (trace_ratios_nonempty N hd)
        (fun _ hx => sharp_family_ratio_lower_bound a ha ha₁ hd N hN 1 true hx))
    refine ⟨htrace, fun γ hγ => ?_⟩
    have hratios :=
      D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction.result A (A × A) N
    rw [hratios.2 γ 1 hγ le_rfl, hratios.1 1 le_rfl]
    exact htrace

#print axioms sharpFilter_posDef

#print axioms sharpFilter_normalized

#print axioms sharpFilter_inverse_marginal

#print axioms sharp_family_ratio_lower_bound

#print axioms sharp_family_recovery_upper_bound

#print axioms harmonicParameter_closed_form

#print axioms exists_small_parameter

#print axioms sharp_factor_witness

end D5.S3.Quantum.Divergence.ConditionalExpansion.SharpFilteredRecoveryFactor
