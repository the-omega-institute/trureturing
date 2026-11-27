import D5.S3.Quantum.Semigroups.WuCubicOperatorNormalization
import D5.S3.Quantum.Information.PartialTraceMutualInformation
import D5.S3.Quantum.Divergence.TraceEntropyCalculus
import D5.S3.Quantum.Information.StrongSubadditivity.Physlib.ForMathlib.HermitianMat.LogExp
import OmegaBuild.Commands

/-! Gibbs-weighted reduction of the Wu cubic first variation at a one-mode base. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix Filter
open scoped Kronecker BigOperators Topology ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace D5.S3.Quantum.Semigroups.WuCubicHotInnerPartialTrace

open WuCubicOperatorBridge (Mat D G generator dissipator)
open WuCubicOperatorNormalization (operatorDeficit)
open WuRepeatedMiddleCubic (alpha)
open TwistedTwoModeOUComparison (modeJump)
open D5.S3.Quantum.Information.PartialTraceMutualInformation
  (partialTraceLeft partialTraceLeft_kronecker)
open private gibbsLow gibbsHigh gibbsOccupation jump_zero jump_one from
  D5.S3.Quantum.Semigroups.WuRepeatedMiddleCubic
open private rootValue rootScale rootRatio rootScale_pos rootRatio_sq from
  D5.S3.Quantum.Semigroups.WuCubicOperatorBridge

abbrev Local := Matrix (Fin 2) (Fin 2) ℂ

/-- One-mode Gibbs density in the physical occupation order. -/
def gibbs (r : ℝ) : Local := diagonal fun i => (gibbsOccupation r i : ℂ)

/-- Gibbs-weighted contraction over the spectator mode. -/
def reduce (r : ℝ) (X : Mat) : Local := partialTraceLeft ((gibbs r ⊗ₖ (1 : Local)) * X)

/-- The observable embedding for the active right mode. -/
def lift (Q : Local) : Mat := (1 : Local) ⊗ₖ Q

local notation "a" => (!![0,1;0,0] : Local)
local notation "Z" => diagonal (![-1,1] : Fin 2 → ℂ)

private theorem gibbs_entry_pos {r : ℝ} (hr : 1 ≤ r) (i : Fin 2) :
    0 < gibbsOccupation r i := by
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  fin_cases i <;> simp [gibbsOccupation, gibbsHigh, gibbsLow] <;> positivity

private theorem gibbs_trace {r : ℝ} (hr : 1 ≤ r) : (gibbs r).trace = 1 := by
  have hr0 : 0 ≤ r := zero_le_one.trans hr
  simp only [gibbs, trace_diagonal, Fin.sum_univ_two, gibbsOccupation,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [← Complex.ofReal_add, ← Complex.ofReal_one]
  congr 1
  unfold gibbsHigh gibbsLow
  have hden : 1 + r ^ 3 ≠ 0 := by positivity
  field_simp [hden]

private theorem reduce_apply (r : ℝ) (X : Mat) (j k : Fin 2) :
    reduce r X j k = ∑ i : Fin 2, (gibbsOccupation r i : ℂ) * X (i, j) (i, k) := by
  rw [reduce, gibbs, ← Matrix.diagonal_one, Matrix.diagonal_kronecker_diagonal]
  simp [partialTraceLeft, Matrix.diagonal_mul]

/-- The reduced observable generator uses the physical Wu raising and lowering rates. -/
def rightGenerator (r : ℝ) (Q : Local) : Local :=
  let term := fun J : Local =>
    (1 / 2 : ℂ) • ((Jᴴ * J) * Q + Q * (Jᴴ * J)) - Jᴴ * Q * J
  (2 * (gibbsLow r : ℂ)) • term a + (2 * (gibbsHigh r : ℂ)) • term aᴴ

private theorem reduce_lift {r : ℝ} (hr : 1 ≤ r) (Q : Local) :
    reduce r (lift Q) = Q := by
  rw [reduce, lift, ← mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]
  calc
    _ = (gibbs r).trace • Q := partialTraceLeft_kronecker _ _
    _ = Q := by rw [gibbs_trace hr, one_smul]

set_option maxHeartbeats 2000000 in
-- Evaluate the physical jump on the occupation blocks.
/-- The left-mode pair is stationary under the Gibbs-weighted partial trace. -/
theorem reduce_spectator (r : ℝ) (X : Mat) :
    reduce r ((2 * (gibbsLow r : ℂ)) • dissipator (modeJump 0) X +
      (2 * (gibbsHigh r : ℂ)) • dissipator (modeJump 0)ᴴ X) = 0 := by
  ext j k
  fin_cases j <;> fin_cases k <;>
    simp [reduce_apply, Fin.sum_univ_two, dissipator, jump_zero, Matrix.mul_apply,
      Matrix.conjTranspose_kronecker, Matrix.conjTranspose_apply, Matrix.kroneckerMap_apply,
      Fintype.sum_prod_type, Matrix.one_apply, gibbsOccupation, smul_eq_mul,
      Matrix.smul_apply] <;> ring

set_option maxHeartbeats 2000000 in
-- Evaluate both parity-twisted jumps on the occupation blocks.
private theorem reduce_active (r : ℝ) (X : Mat) :
    reduce r ((2 * (gibbsLow r : ℂ)) • dissipator (modeJump 1) X +
      (2 * (gibbsHigh r : ℂ)) • dissipator (modeJump 1)ᴴ X) =
      rightGenerator r (reduce r X) := by
  ext j k
  fin_cases j <;> fin_cases k <;>
    simp [reduce_apply, Fin.sum_univ_two, dissipator, rightGenerator, jump_one, Matrix.mul_apply,
      Matrix.conjTranspose_kronecker, Matrix.conjTranspose_apply, Matrix.kroneckerMap_apply,
      Fintype.sum_prod_type, Matrix.diagonal_apply, smul_eq_mul,
      Matrix.smul_apply, Matrix.vecMul, dotProduct] <;> ring

/-- The Gibbs contraction intertwines the genuine CAR generator for every complex matrix. -/
theorem reduce_generator (r : ℝ) (X : Mat) :
    reduce r (generator r X) = rightGenerator r (reduce r X) := by
  simp only [generator, Fin.sum_univ_two]
  rw [show ∀ A B : Mat, reduce r (A + B) = reduce r A + reduce r B from by
    intro A B
    ext j k
    simp [reduce_apply, mul_add, Finset.sum_add_distrib]]
  rw [reduce_spectator, reduce_active, zero_add]

private theorem kron_sub (A B C : Local) :
    A ⊗ₖ (B - C) = (A ⊗ₖ B) - (A ⊗ₖ C) := by
  ext i j
  exact mul_sub _ _ _

private theorem dissipator_lift (L J Q : Local) (hL : Lᴴ * L = 1) :
    dissipator (L ⊗ₖ J) (lift Q) =
      lift ((1 / 2 : ℂ) • ((Jᴴ * J) * Q + Q * (Jᴴ * J)) - Jᴴ * Q * J) := by
  simp only [dissipator, lift, Matrix.conjTranspose_kronecker, ← mul_kronecker_mul,
    Matrix.mul_one, hL, Matrix.kronecker_add, Matrix.kronecker_smul,
    kron_sub]

/-- The physical generator preserves the embedded active-mode algebra. -/
theorem generator_lift (r : ℝ) (Q : Local) :
    generator r (lift Q) = lift (rightGenerator r Q) := by
  have hz : (Z : Local)ᴴ = Z := by
    rw [Matrix.diagonal_conjTranspose]
    congr 1
    funext i
    fin_cases i <;> simp
  have hzz : (Z : Local)ᴴ * Z = 1 := by
    rw [hz, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    fin_cases i <;> simp
  have hleft (J : Local) : dissipator (J ⊗ₖ (1 : Local)) (lift Q) = 0 := by
    simp only [dissipator, lift, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
      ← mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one, ← add_kronecker,
      ← smul_kronecker]
    have h : (1 / 2 : ℂ) • (Jᴴ * J + Jᴴ * J) = Jᴴ * J := by
      rw [← two_smul ℂ, smul_smul]
      norm_num
    rw [h, sub_self]
  simp only [generator, Fin.sum_univ_two, jump_zero, jump_one, Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_one, hleft, smul_zero, add_zero, zero_add, hz,
    dissipator_lift Z _ Q hzz]
  simp only [rightGenerator, lift, Matrix.kronecker_add, Matrix.kronecker_smul]

private theorem gibbs_product (r : ℝ) : D r = gibbs r ⊗ₖ gibbs r := by
  simp [D, gibbs, Matrix.diagonal_kronecker_diagonal, Complex.ofReal_mul]

private def rootValues (r : ℝ) : Fin 2 → ℝ :=
  ![Real.sqrt (rootScale r), Real.sqrt (rootScale r) * rootRatio r]

private def root (r : ℝ) : Local := diagonal fun i => (rootValues r i : ℂ)

private theorem sqrt_rootScale_sq {r : ℝ} (hr : 1 ≤ r) :
    Real.sqrt (rootScale r) ^ 2 = rootScale r :=
  Real.sq_sqrt (rootScale_pos (zero_le_one.trans hr)).le

private theorem G_product {r : ℝ} (hr : 1 ≤ r) : G r = root r ⊗ₖ root r := by
  have hs := sqrt_rootScale_sq hr
  rw [G, root, Matrix.diagonal_kronecker_diagonal]
  congr 1
  funext ⟨i,j⟩
  rw [← Complex.ofReal_mul]
  apply congrArg Complex.ofReal
  fin_cases i <;> fin_cases j <;> simp [rootValues, rootValue, finProdFinEquiv]
  · exact hs.symm.trans (pow_two _)
  · calc
      _ = Real.sqrt (rootScale r) ^ 2 * rootRatio r := by rw [hs]
      _ = _ := by ring
  · calc
      _ = Real.sqrt (rootScale r) ^ 2 * rootRatio r := by rw [hs]
      _ = _ := by ring
  · calc
      _ = Real.sqrt (rootScale r) ^ 2 * rootRatio r ^ 2 := by
        rw [hs, rootRatio_sq (zero_le_one.trans hr)]
      _ = _ := by ring

private theorem root_posDef {r : ℝ} (hr : 1 ≤ r) : (root r).PosDef := by
  have hs := Real.sqrt_pos.2 (rootScale_pos (zero_le_one.trans hr))
  have ht : 0 < rootRatio r := Real.sqrt_pos.2 (zero_lt_one.trans_le hr)
  apply Matrix.PosDef.diagonal
  intro i
  rw [Complex.zero_lt_real]
  fin_cases i <;> simp [rootValues, hs, mul_pos hs ht]

private theorem root_pow_six {r : ℝ} (hr : 1 ≤ r) : root r ^ 6 = gibbs r := by
  have hl : 0 ≤ gibbsLow r := (gibbs_entry_pos hr 0).le
  have hs : rootScale r ^ 3 = gibbsLow r := by
    unfold rootScale
    rw [← Real.rpow_mul_natCast hl]
    norm_num
  have ht : rootRatio r ^ 6 = r ^ 3 := by
    rw [show (6 : ℕ) = 2 * 3 by decide, pow_mul, rootRatio_sq (zero_le_one.trans hr)]
  rw [root, gibbs, Matrix.diagonal_pow]
  congr 1
  funext i
  rw [Pi.pow_apply, ← Complex.ofReal_pow]
  apply congrArg Complex.ofReal
  have h : Real.sqrt (rootScale r) ^ 6 = gibbsLow r := by
    rw [show (6 : ℕ) = 2 * 3 by decide, pow_mul, sqrt_rootScale_sq hr, hs]
  fin_cases i <;> simp [rootValues, gibbsOccupation, gibbsHigh, mul_pow, h, ht, mul_comm]

private theorem kron_pow {A B : Local} (n : ℕ) :
    (A ⊗ₖ B) ^ n = (A ^ n) ⊗ₖ (B ^ n) := by
  induction n with
  | zero => simp
  | succ n hn => rw [pow_succ, hn, ← mul_kronecker_mul, ← pow_succ, ← pow_succ]

private theorem trace_pairing (r : ℝ) (X : Mat) (B : Local) :
    (X * (gibbs r ⊗ₖ B)).trace = (reduce r X * B).trace := by
  calc
    _ = (((gibbs r ⊗ₖ (1 : Local)) * X) * lift B).trace := by
      rw [Matrix.mul_assoc, Matrix.trace_mul_comm (gibbs r ⊗ₖ (1 : Local)),
        Matrix.mul_assoc, lift, ← mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one]
    _ = _ := Matrix.trace_mul_one_kron_right _ _

private theorem trace_sandwich_pairing {r : ℝ} (hr : 1 ≤ r) (H : Mat) (K : Local) :
    ((G r * H * G r) * ((root r ^ 4) ⊗ₖ K)).trace =
      ((root r * reduce r H * root r) * K).trace := by
  have hpow : root r * root r ^ 4 * root r = gibbs r := by
    rw [← pow_succ', ← pow_succ, root_pow_six hr]
  calc
    _ = ((G r * H) * (G r * ((root r ^ 4) ⊗ₖ K))).trace := by rw [Matrix.mul_assoc]
    _ = ((G r * ((root r ^ 4) ⊗ₖ K)) * (G r * H)).trace := Matrix.trace_mul_comm _ _
    _ = (H * (G r * ((root r ^ 4) ⊗ₖ K) * G r)).trace := by
      rw [← Matrix.mul_assoc, Matrix.trace_mul_comm]
    _ = (reduce r H * (root r * K * root r)).trace := by
      rw [G_product hr, ← mul_kronecker_mul, ← mul_kronecker_mul, hpow, trace_pairing]
    _ = (root r * (reduce r H * (root r * K))).trace := by
      rw [Matrix.trace_mul_comm (root r)]
      simp only [Matrix.mul_assoc]
    _ = _ := by simp only [Matrix.mul_assoc]

private theorem sandwich_lift {r : ℝ} (hr : 1 ≤ r) (P : Local) :
    G r * lift P * G r = (root r ^ 2) ⊗ₖ (root r * P * root r) := by
  rw [G_product hr, lift, ← mul_kronecker_mul, ← mul_kronecker_mul, Matrix.mul_one, pow_two]

/-- At an embedded one-mode observable the physical energy has exactly the
one-mode trace, including the normalization of the spectator Gibbs state. -/
theorem product_energy {r : ℝ} (hr : 1 ≤ r) (P : Local) :
    (((G r * lift P * G r) ^ 2) * (G r * generator r (lift P) * G r)).trace =
      (((root r * P * root r) ^ 2) *
        (root r * rightGenerator r P * root r)).trace := by
  rw [generator_lift, sandwich_lift hr, sandwich_lift hr, kron_pow,
    ← mul_kronecker_mul, ← pow_mul, ← pow_add, root_pow_six hr,
    trace_kronecker, gibbs_trace hr, one_mul]

private theorem positive_pow {A : Local} (hA : A.PosDef) (k : ℕ) : (A ^ k).PosDef :=
  ((hA.posSemidef.pow k).posDef_iff_isUnit).mpr (hA.isUnit.pow k)

private theorem log_product {A B : Local} (hA : A.PosDef) (hB : B.PosDef) :
    cfc Real.log (A ⊗ₖ B) =
      (cfc Real.log A ⊗ₖ (1 : Local)) + lift (cfc Real.log B) := by
  let HA : HermitianMat (Fin 2) ℂ := ⟨A, hA.isHermitian⟩
  let HB : HermitianMat (Fin 2) ℂ := ⟨B, hB.isHermitian⟩
  let _ : HermitianMat.NonSingular HA := HermitianMat.nonSingular_of_posDef hA
  let _ : HermitianMat.NonSingular HB := HermitianMat.nonSingular_of_posDef hB
  have h := congrArg HermitianMat.mat (HermitianMat.log_kron (A := HA) (B := HB))
  simp only [HermitianMat.log, HermitianMat.mat_cfc, HermitianMat.kronecker_mat,
    HermitianMat.mat_add, HermitianMat.mat_one] at h
  change cfc Real.log (HA.mat ⊗ₖ HB.mat) =
    (cfc Real.log HA.mat ⊗ₖ (1 : Local)) + lift (cfc Real.log HB.mat) at h
  have hAm : HA.mat = A := rfl
  have hBm : HB.mat = B := rfl
  rw [hAm, hBm] at h
  exact h

private theorem cubed_base {r : ℝ} (hr : 1 ≤ r) (B : Local) :
    ((root r ^ 2) ⊗ₖ B) ^ 3 = gibbs r ⊗ₖ (B ^ 3) := by
  rw [kron_pow, ← pow_mul, root_pow_six hr]

private theorem log_difference {r : ℝ} (hr : 1 ≤ r) {B : Local} (hB : B.PosDef) :
    cfc Real.log (((root r ^ 2) ⊗ₖ B) ^ 3) - cfc Real.log (D r) =
      lift (cfc Real.log (B ^ 3) - cfc Real.log (gibbs r)) := by
  have hg : (gibbs r).PosDef := by
    rw [← root_pow_six hr]
    exact positive_pow (root_posDef hr) 6
  rw [cubed_base hr, gibbs_product, log_product hg (positive_pow hB 3), log_product hg hg,
    lift, lift, lift, kron_sub]
  abel

private def cubeVariation {n : Type*} [Fintype n] [DecidableEq n]
    (B V : Matrix n n ℂ) : Matrix n n ℂ :=
  (V * B + B * V) * B + B ^ 2 * V

private theorem trace_cubeVariation {n : Type*} [Fintype n] [DecidableEq n]
    (B V L : Matrix n n ℂ) :
    (cubeVariation B V * L).trace = (V * (B ^ 2 * L + B * L * B + L * B ^ 2)).trace := by
  have h₁ : (B * V * B * L).trace = (V * (B * L * B)).trace := by
    rw [show B * V * B * L = B * (V * (B * L)) by simp only [Matrix.mul_assoc],
      Matrix.trace_mul_comm B]
    simp only [Matrix.mul_assoc]
  have h₂ : (B ^ 2 * V * L).trace = (V * (L * B ^ 2)).trace := by
    rw [Matrix.mul_assoc, Matrix.trace_mul_comm (B ^ 2)]
    simp only [Matrix.mul_assoc]
  simp only [cubeVariation, add_mul, mul_add, Matrix.trace_add, h₁, h₂]
  simp only [pow_two, Matrix.mul_assoc]

private theorem cubeVariation_pairing {r : ℝ} (hr : 1 ≤ r) (B L : Local) (H : Mat) :
    (cubeVariation ((root r ^ 2) ⊗ₖ B) (G r * H * G r) * lift L).trace =
      (cubeVariation B (root r * reduce r H * root r) * L).trace := by
  rw [trace_cubeVariation, trace_cubeVariation]
  have hp : (root r ^ 2) ^ 2 = root r ^ 4 := by rw [← pow_mul]
  have hp' : root r ^ 2 * root r ^ 2 = root r ^ 4 := by rw [← pow_add]
  simp only [lift, kron_pow, hp, ← mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul,
    hp', ← Matrix.kronecker_add]
  exact trace_sandwich_pairing hr H _

private theorem trace_energyVariation {n : Type*} [Fintype n] [DecidableEq n]
      (M N T U : Matrix n n ℂ) :
      ((T * M + M * T) * N + M ^ 2 * U).trace =
        (T * (M * N + N * M)).trace + (U * M ^ 2).trace := by
  have hc : (M * T * N).trace = (T * (N * M)).trace := by
    rw [Matrix.mul_assoc, Matrix.trace_mul_comm M, Matrix.mul_assoc]
  simp only [add_mul, mul_add, Matrix.trace_add, hc, Matrix.mul_assoc T,
    Matrix.trace_mul_comm (M ^ 2) U]

private theorem energyVariation_pairing {r : ℝ} (hr : 1 ≤ r) (P : Local) (H : Mat) :
    let B := root r * P * root r
    let C := root r * rightGenerator r P * root r
    let V := root r * reduce r H * root r
    let W := root r * rightGenerator r (reduce r H) * root r
    let M := G r * lift P * G r
    let N := G r * generator r (lift P) * G r
    let T := G r * H * G r
    let U := G r * generator r H * G r
    (((T * M + M * T) * N + M ^ 2 * U).trace) =
      (((V * B + B * V) * C + B ^ 2 * W).trace) := by
  dsimp only
  simp only [trace_energyVariation, generator_lift, sandwich_lift hr]
  have hp : (root r ^ 2) ^ 2 = root r ^ 4 := by rw [← pow_mul]
  have hp' : root r ^ 2 * root r ^ 2 = root r ^ 4 := by rw [← pow_add]
  simp only [kron_pow, ← mul_kronecker_mul, hp, hp', ← Matrix.kronecker_add,
    trace_sandwich_pairing hr, reduce_generator]

private theorem trace_mass_base {r : ℝ} (hr : 1 ≤ r) (B : Local) :
    (((root r ^ 2) ⊗ₖ B) ^ 3).trace.re = (B ^ 3).trace.re := by
  rw [cubed_base hr, Matrix.trace_kronecker, gibbs_trace hr, one_mul]

private theorem generator_affine (r : ℝ) (X H : Mat) (t : ℝ) :
    generator r (X + t • H) = generator r X + t • generator r H := by
  have hs (c : ℂ) (M : Mat) : c • (t • M) = t • (c • M) := smul_comm c t M
  have hd (J : Mat) : dissipator J (X + t • H) = dissipator J X + t • dissipator J H := by
    simp only [dissipator, mul_add, add_mul, Matrix.mul_smul, Matrix.smul_mul,
      smul_add, smul_sub, hs]
    abel
  simp only [generator, hd, Fin.sum_univ_two, smul_add, hs]
  abel

private theorem hasDerivAt_affine {n : Type*} [Fintype n] [DecidableEq n]
    (M V : Matrix n n ℂ) : HasDerivAt (fun t : ℝ => M + t • V) V 0 := by
  simpa using ((hasDerivAt_id (0 : ℝ)).smul_const V).const_add M

private theorem hasDerivAt_reTrace {n : Type*} [Fintype n] [DecidableEq n]
    {f : ℝ → Matrix n n ℂ} {V : Matrix n n ℂ} (hf : HasDerivAt f V 0) :
    HasDerivAt (fun t => (f t).trace.re) V.trace.re 0 := by
  let T : Matrix n n ℂ →L[ℝ] ℝ :=
    Complex.reCLM.comp (Matrix.traceLinearMap n ℝ ℂ).toContinuousLinearMap
  exact T.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hf

private theorem hasDerivAt_energy {r : ℝ} (P : Local) (H : Mat) :
    let M := G r * lift P * G r
    let N := G r * generator r (lift P) * G r
    let V := G r * H * G r
    let W := G r * generator r H * G r
    HasDerivAt (fun t : ℝ =>
      let X := lift P + t • H
      ((G r * X * G r) ^ 2 * (G r * generator r X * G r)).trace.re)
      (((V * M + M * V) * N + M ^ 2 * W).trace.re) 0 := by
  dsimp only
  let M := G r * lift P * G r
  let N := G r * generator r (lift P) * G r
  let V := G r * H * G r
  let W := G r * generator r H * G r
  have hM := hasDerivAt_affine M V
  have hN := hasDerivAt_affine N W
  have hE := hasDerivAt_reTrace ((hM.fun_mul hM).fun_mul hN)
  simpa only [M, N, V, W, zero_smul, add_zero, pow_two, generator_affine,
    Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul] using hE

set_option maxHeartbeats 1000000 in
-- Elaborate the trace chain rule and the normalization derivative in the operator norm.
private theorem hasDerivAt_entropy {r : ℝ} (hr : 1 ≤ r) (P : Local)
    (hP : P.PosDef) (H : Mat) (hH : H.IsHermitian) :
    let B := root r * P * root r
    let V := root r * reduce r H * root r
    let T := (B ^ 3).trace.re
    HasDerivAt (fun t : ℝ =>
      let M := G r * (lift P + t • H) * G r
      (M ^ 3 * (cfc Real.log (M ^ 3) - cfc Real.log (D r))).trace.re -
        (M ^ 3).trace.re * Real.log (M ^ 3).trace.re)
      (cubeVariation B V * (cfc Real.log (B ^ 3) - cfc Real.log (gibbs r) -
        Real.log T • (1 : Local))).trace.re 0 := by
  dsimp only
  let B := root r * P * root r
  let V := root r * reduce r H * root r
  let M := G r * lift P * G r
  let U := G r * H * G r
  let F := fun t : ℝ => M + t • U
  have hM : M = (root r ^ 2) ⊗ₖ B := sandwich_lift hr P
  have hroot := root_posDef hr
  have hB : B.PosDef := by
    simpa only [B, hroot.isHermitian.eq] using hP.conjTranspose_mul_mul_same hroot.mulVec_injective
  have hMpos : M.PosDef := by
    rw [hM]
    exact (positive_pow hroot 2).kronecker hB
  have hG : (G r).IsHermitian := by
    rw [G_product hr, Matrix.IsHermitian, Matrix.conjTranspose_kronecker, hroot.isHermitian.eq]
  have hU : U.IsHermitian := by
    simpa only [U, hG.eq] using Matrix.isHermitian_conjTranspose_mul_mul (G r) hH
  have hF := hasDerivAt_affine M U
  have hpow : HasDerivAt (fun t => F t ^ 3) (cubeVariation M U) 0 := by
    simpa only [F, zero_smul, add_zero, cubeVariation,
      show (3 : ℕ) = 2 + 1 by decide, pow_succ, pow_zero, one_mul] using (hF.fun_mul hF).fun_mul hF
  have hPD : (F 0 ^ 3).PosDef := by
    simpa only [F, zero_smul, add_zero, hM, cubed_base hr, ← root_pow_six hr] using
      (positive_pow hroot 6).kronecker (positive_pow hB 3)
  let Y := cubeVariation M U
  have hLog := D5.S3.Quantum.Divergence.TraceEntropyCalculus.hasDerivAt_trace_mul_log
    (fun t => F t ^ 3) Y 0 hpow
    (Eventually.of_forall fun t => (hMpos.isHermitian.add (hU.smul (star_trivial t))).pow 3) hPD
  have hGibbs := hasDerivAt_reTrace (hpow.mul_const (cfc Real.log (D r)))
  have hMass := hasDerivAt_reTrace hpow
  have hMassPos : 0 < (F 0 ^ 3).trace.re := (Complex.lt_def.mp hPD.trace_pos).1
  have hMassLog := hMass.fun_mul ((Real.hasDerivAt_log hMassPos.ne').comp 0 hMass)
  have hMassFactor : (F 0 ^ 3).trace.re = (B ^ 3).trace.re := by
    simpa only [F, zero_smul, add_zero, hM] using trace_mass_base hr B
  have hL : cfc Real.log (F 0 ^ 3) - cfc Real.log (D r) =
      lift (cfc Real.log (B ^ 3) - cfc Real.log (gibbs r)) := by
    simpa only [F, zero_smul, add_zero, hM] using log_difference hr hB
  have hMassPair : Y.trace = (cubeVariation B V).trace := by
    simpa only [Y, hM, V, U, lift, one_kronecker_one, Matrix.mul_one] using
      cubeVariation_pairing hr B (1 : Local) H
  have hLogPair :
      (Y * (cfc Real.log (F 0 ^ 3) - cfc Real.log (D r))).trace =
        (cubeVariation B V * (cfc Real.log (B ^ 3) - cfc Real.log (gibbs r))).trace := by
    rw [hL]
    simpa only [Y, hM, V, U] using cubeVariation_pairing hr B
      (cfc Real.log (B ^ 3) - cfc Real.log (gibbs r)) H
  have hd := (hLog.fun_sub hGibbs).fun_sub hMassLog
  simp only [Function.comp_apply] at hd
  have hcancel :
      (Y * (cfc Real.log (F 0 ^ 3) + 1)).trace.re -
          (Y * cfc Real.log (D r)).trace.re -
          (Y.trace.re * Real.log (F 0 ^ 3).trace.re +
            (F 0 ^ 3).trace.re * ((F 0 ^ 3).trace.re⁻¹ * Y.trace.re)) =
        (cubeVariation B V * (cfc Real.log (B ^ 3) - cfc Real.log (gibbs r) -
          Real.log (B ^ 3).trace.re • (1 : Local))).trace.re := by
    have hLogPairRe := congrArg Complex.re hLogPair
    have hMassPairRe := congrArg Complex.re hMassPair
    rw [← mul_assoc (F 0 ^ 3).trace.re, mul_inv_cancel₀ hMassPos.ne', one_mul, hMassFactor]
    simp only [mul_add, mul_sub, Matrix.trace_add, Matrix.trace_sub, Complex.add_re,
      Complex.sub_re, Matrix.mul_one, Matrix.mul_smul, Matrix.trace_smul,
      Complex.smul_re, smul_eq_mul] at hLogPairRe ⊢
    rw [← hMassPairRe]
    linarith only [hLogPairRe]
  rw [hcancel] at hd
  simpa only [Function.comp_apply, F, M, U, B, V, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_smul, Matrix.smul_mul, mul_sub, Matrix.trace_sub, Complex.sub_re] using hd

/-- The literal Wu deficit has this first variation at every positive-definite
one-mode observable and in every complex Hermitian direction. Both the energy
and entropy coefficients use only the Gibbs-weighted reduction of the direction. -/
theorem hasDerivAt_operatorDeficit {r : ℝ} (hr : 1 ≤ r) (P : Local)
    (hP : P.PosDef) (H : Mat) (hH : H.IsHermitian) :
    let B := root r * P * root r
    let C := root r * rightGenerator r P * root r
    let V := root r * reduce r H * root r
    let W := root r * rightGenerator r (reduce r H) * root r
    let T := (B ^ 3).trace.re
    HasDerivAt (fun t : ℝ => operatorDeficit r (lift P + t • H))
      ((9 / 8 : ℝ) * (((V * B + B * V) * C + B ^ 2 * W).trace.re) -
        alpha r * (cubeVariation B V * (cfc Real.log (B ^ 3) - cfc Real.log (gibbs r) -
          Real.log T • (1 : Local))).trace.re) 0 := by
  have hE := hasDerivAt_energy (r := r) P H
  have he := energyVariation_pairing hr P H
  dsimp only at hE he ⊢
  rw [he] at hE
  simpa only [operatorDeficit] using
    (hE.const_mul (9 / 8 : ℝ)).fun_sub ((hasDerivAt_entropy hr P hP H hH).const_mul (alpha r))

private theorem reduce_hermitian (r : ℝ) {H : Mat} (hH : H.IsHermitian) :
    (reduce r H).IsHermitian := by
  change (reduce r H)ᴴ = reduce r H
  ext i j
  have h (k : Fin 2) : star (H (k, j) (k, i)) = H (k, i) (k, j) :=
    congrFun (congrFun hH.eq (k, i)) (k, j)
  simp only [Matrix.conjTranspose_apply, reduce_apply, star_sum, star_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [h, show star (gibbsOccupation r k : ℂ) = (gibbsOccupation r k : ℂ) by simp, mul_comm]

/-- The directional derivative is preserved when the direction is replaced by
the embedding of its Gibbs-weighted partial trace. -/
theorem deriv_operatorDeficit_eq_lift_reduce {r : ℝ} (hr : 1 ≤ r) (P : Local)
    (hP : P.PosDef) (H : Mat) (hH : H.IsHermitian) :
    deriv (fun t : ℝ => operatorDeficit r (lift P + t • H)) 0 =
      deriv (fun t : ℝ => operatorDeficit r (lift P + t • lift (reduce r H))) 0 := by
  have hLift : (lift (reduce r H)).IsHermitian := by
    rw [lift, Matrix.IsHermitian, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
      (reduce_hermitian r hH).eq]
  rw [(hasDerivAt_operatorDeficit hr P hP H hH).deriv,
    (hasDerivAt_operatorDeficit hr P hP _ hLift).deriv, reduce_lift hr]

end D5.S3.Quantum.Semigroups.WuCubicHotInnerPartialTrace
