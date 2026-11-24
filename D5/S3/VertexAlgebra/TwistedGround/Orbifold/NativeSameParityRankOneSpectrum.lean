/- GID: D5/S3/VertexAlgebra/TwistedGround/Orbifold/NativeSameParityRankOneSpectrum
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/Orbifold/NativeSameParityRankOneSpectrum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The rank-one omega, Abe pair and quartic primary zero modes on the Leech even twisted top. -/

import D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeEvenGroundZhuCommutant
import D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeOddZhuTopBalance

/-!
Abe, arXiv:math/9907120v1, equation (2.11), Table 1 and §4.2.
The eigenvalues are obtained from the native normal-ordered field and its
finite pairing correction on the vacuum oscillator tensor.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1500000

open scoped BigOperators TensorProduct VertexOperator

namespace D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeSameParity

open LatticeGeneratingFieldLocality LatticeInvolution LatticePositiveEnergy
open LatticeFiniteNegativeGeneration LatticeAllStateField
open LatticeHalfFockChargedTensorCoefficients LatticeHalfFockCorrectedField
open LatticeHalfFockFiniteCorrection LatticeHalfFockGroundCompression MvPolynomial
open ActualLeechHyperbolic (leechData)
open Lattice.ActualZhuCurrentRelations (single_weighted_grade)
open NativeOddTwistedIntertwiner (twistedTop fixedAction fixedTopZero leechUnit
  leechAbeState leechAbeState_grade leechRankOneScale
  leechNeutralTransport leechOscillatorSubstitution leechOscillatorSubstitution_X
  evenTopGroundEquiv evenTopGroundEquiv_val evenTopGroundEquiv_symm_apply)
open private fixedAction_val from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeOddTopDetection
open private neutralLift neutralLift_apply neutralTransport_lift rankOne_abe_lift
    leechRankOneScale_contract from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeOddZhuTopBalance
open private theta_omega_fixed from D5.S3.VertexAlgebra.TwistedGround.MixedIntertwiner
open private x inverseGram from D5.S3.VertexAlgebra.Lattice.ActualZhuRankOneOdd

noncomputable section

local notation "ℒ" => leechData
local notation "R₁" => Lattice.ActualZhuRankOneOdd.datum
local notation "κ[" i "]" => (Complex.ofReal (leechRankOneScale i))
local notation "g[" i "]" => ((LatticeData.G leechData i i : ℤ) : ℂ)
local notation "E" => (evenTopGroundEquiv ℒ leechUnit)

local instance : AddCommGroup (twistedTop ℒ leechUnit false) :=
  @Submodule.addCommGroup ℂ (NativeOddTwistedIntertwiner.Twisted ℒ leechUnit false) _ _ _
    (twistedTop ℒ leechUnit false)

private theorem correctionWord_neutral_cons (D : LatticeData) (j : Index D)
    (word : List (Index D)) :
    correctionWord D 0 (j :: word) =
      X (some j) * correctionWord D 0 word +
        ((labelledRemainders D word).map (fun entry =>
          pairPolynomial D j entry.1 * correctionWord D 0 entry.2)).sum := by
  rw [correctionWord_matching]
  simp [singletonPolynomial, bilinear]

private theorem correctionWord_nil (D : LatticeData) :
    correctionWord D 0 [] = 1 := rfl

private theorem corrWord (D : LatticeData) (word : List (Index D)) :
    Corr D 0 (word.map (fun j => (X j : Oscillator D))).prod =
      shiftCoefficients D ((optionEquivLeft ℂ (Index D)) (correctionWord D 0 word)) := by
  classical
  let m := (word.map (fun j => Finsupp.single j 1)).sum
  have hm : monomial m (1 : ℂ) = (word.map (fun j => (X j : Oscillator D))).prod := by
    dsimp only [m]
    induction word with
    | nil => simp
    | cons j word ih =>
      simp only [List.map_cons, List.sum_cons, List.prod_cons, ← ih]
      rw [show (X j : Oscillator D) = monomial (Finsupp.single j 1) 1 from rfl,
        monomial_mul_monomial, one_mul]
  rw [← hm]
  apply Corr_monomial_enumeration
  rw [← Multiset.coe_eq_coe]
  simp only [LatticeAllStateField.occurrences, Multiset.coe_toList]
  change (word : Multiset (Index D)) = m.toMultiset
  clear hm
  dsimp only [m]
  induction word with
  | nil => simp
  | cons j word ih =>
    simp only [List.map_cons, List.sum_cons, Finsupp.toMultiset_add,
      Finsupp.toMultiset_single, one_nsmul, ← ih]
    change j ::ₘ (word : Multiset (Index D)) = _
    exact (Multiset.singleton_add _ _).symm

private theorem corr_pair (D : LatticeData) (j k : Index D) (d : ℕ)
    (hd : sourceWeight D j + sourceWeight D k = d) :
    Corr D 0 (X j * X k) d =
      C (pairScalar (sourceWeight D j) (sourceWeight D k) * (D.G j.1 k.1 : ℂ)) := by
  have h := congrArg (fun f : ℕ →₀ Oscillator D => f d) (corrWord D [j,k])
  let c : Oscillator D :=
    C (pairScalar (sourceWeight D j) (sourceWeight D k) * (D.G j.1 k.1 : ℂ))
  have hw : correctionWord D 0 [j,k] =
      X (some j) * X (some k) + C (pairScalar (sourceWeight D j)
        (sourceWeight D k) * (D.G j.1 k.1 : ℂ)) * X none ^ d := by
    simp [correctionWord_neutral_cons, correctionWord_nil, labelledRemainders, pairPolynomial, hd]
  have hp : (optionEquivLeft ℂ (Index D)) (correctionWord D 0 [j,k]) =
      Polynomial.C (X j * X k) + Polynomial.C c * Polynomial.X ^ d := by
    rw [hw]
    simp only [map_add, map_mul, map_pow, optionEquivLeft_X_some, optionEquivLeft_X_none,
      optionEquivLeft_C, c]
  rw [hp] at h
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at h
  change _ = _ at h
  rw [h]
  change (Polynomial.C (X j * X k) + Polynomial.C c * Polynomial.X ^ d).coeff d = c
  have hd0 : d ≠ 0 := by
    unfold sourceWeight at hd
    omega
  simp [Polynomial.coeff_C, hd0]

private theorem corr_four (D : LatticeData) (i : Fin D.rank) :
    Corr D 0 ((X (i, 0) : Oscillator D) ^ 4) 4 =
      C (3 * (((D.G i i : ℂ) / 8) ^ 2)) := by
  classical
  let j : Index D := (i, 0)
  let U : CorrectionPolynomial D := X (some j)
  let a : ℂ := (D.G i i : ℂ) / 8
  let P : CorrectionPolynomial D := C a * X none ^ 2
  have hp : pairPolynomial D j j = P := by
    dsimp [pairPolynomial, P, a, j, sourceWeight]
    congr 2
    norm_num [pairScalar, halfBinomial, Finset.prod_range_succ] <;> ring
  have hw : correctionWord D 0 [j,j,j,j] = U^4 + 6 * P * U^2 + 3 * P^2 := by
    simp only [correctionWord_neutral_cons, correctionWord_nil, labelledRemainders,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, hp, U]
    ring
  have hc := congrArg (fun f : ℕ →₀ Oscillator D => f 4) (corrWord D [j,j,j,j])
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, hw] at hc
  rw [show (X (i, 0) : Oscillator D)^4 = X j * (X j * (X j * X j)) by
    dsimp [j]; ring]
  rw [hc]
  have he :
      (optionEquivLeft ℂ (Index D)) (U^4 + 6 * P * U^2 + 3 * P^2) =
        Polynomial.C ((X j : Oscillator D)^4) +
        Polynomial.C (6 * C a * (X j : Oscillator D)^2) * Polynomial.X^2 +
        Polynomial.C (C (3 * a^2)) * Polynomial.X^4 := by
    simp only [U, P, map_add, map_mul, map_pow, map_ofNat, optionEquivLeft_X_some,
      optionEquivLeft_X_none, optionEquivLeft_C]
    <;> ring
  rw [he]
  change (Polynomial.C ((X j : Oscillator D)^4) +
        Polynomial.C (6 * C a * (X j : Oscillator D)^2) * Polynomial.X^2 +
        Polynomial.C (C (3 * a^2)) * Polynomial.X^4).coeff 4 = _
  rw [Polynomial.coeff_add, Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow,
    Polynomial.coeff_C_mul_X_pow]
  simp only [Polynomial.coeff_C, Nat.reduceEqDiff, ite_false, ite_true, zero_add, a]

private theorem compression_at_weight (p : Oscillator ℒ) (d : ℕ) :
    compression ℒ leechUnit ((correctedField ℒ leechUnit (Finsupp.single 0 p)).coeff
      (-2 * (d : ℤ))) = epsilon ℒ ((Corr ℒ 0 p) d) • LinearMap.id := by
  classical
  change (pi ℒ leechUnit).comp
    (((correctedField ℒ leechUnit (Finsupp.single 0 p)).coeff
      (-2 * (d : ℤ))).comp (iota ℒ leechUnit)) = _
  rw [correctedField_ground_compression]
  congr 1
  rw [Finset.sum_eq_single d]
  · simp
  · intro k hk hkd
    apply ite_eq_right
    intro he
    apply hkd
    omega
  · intro hd
    have hz := Finsupp.notMem_support_iff.mp hd
    simp [hz]

private def rankOneOmega : Carrier R₁ :=
  LatticeActualConformalState.omega R₁ inverseGram

private theorem rankOneOmega_polynomial :
    rankOneOmega = neutralLift R₁ ((1 / 4 : ℂ) • (x 0 * x 0)) := by
  let : NeZero (R₁).rank := ⟨by decide⟩
  let : Subsingleton (Fin (R₁).rank) := by change Subsingleton (Fin 1); infer_instance
  have singleSum (f : Fin (R₁).rank → Oscillator R₁) : (∑ j, f j) = f 0 :=
    Finset.sum_eq_single 0 (fun j _ hj => (hj (Subsingleton.elim j 0)).elim)
      (fun hn => (hn (Finset.mem_univ 0)).elim)
  norm_num [rankOneOmega, LatticeActualConformalState.omega,
    LatticeActualConformalState.conformalPolynomial, inverseGram, neutralLift_apply,
    x, singleSum, smul_smul]

private theorem rankOneOmega_fixed : theta R₁ rankOneOmega = rankOneOmega :=
  theta_omega_fixed R₁ inverseGram

/-- The transported rank-one conformal vector inside the actual fixed algebra. -/
def leechRankOneOmega (i : Fin (ℒ).rank) : FixedCarrier ℒ :=
  ⟨leechNeutralTransport i rankOneOmega, (mem_fixedSpace ℒ _).mpr (by
    calc
      _ = leechNeutralTransport i (theta R₁ rankOneOmega) := by
        rw [rankOneOmega_polynomial, neutralLift_apply]
        exact NativeOddTwistedIntertwiner.leechNeutralTransport_theta i _
      _ = _ := congrArg (leechNeutralTransport i) rankOneOmega_fixed)⟩

private theorem leechRankOneOmega_polynomial (i : Fin (ℒ).rank) :
    (leechRankOneOmega i).val =
      Finsupp.single 0 ((κ[i]^2 / 4) • (X (i, 0) * X (i, 0))) := by
  change leechNeutralTransport i rankOneOmega = _
  rw [rankOneOmega_polynomial, neutralTransport_lift, neutralLift_apply]
  simp only [x, map_smul, map_mul, leechOscillatorSubstitution_X,
    Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul]
  congr 2
  ring

private theorem leechAbe_polynomial (i : Fin (ℒ).rank) :
    (leechAbeState i).val =
      Finsupp.single 0 ((κ[i]^2 / 2) • (X (i, 2) * X (i, 0))) := by
  change leechNeutralTransport i Lattice.ActualZhuRankOneOdd.abeState = _
  rw [rankOne_abe_lift, neutralTransport_lift, neutralLift_apply]
  simp only [x, map_smul, map_mul, leechOscillatorSubstitution_X,
    Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul]
  congr 2
  ring

theorem leechRankOneOmega_grade (i : Fin (ℒ).rank) : (leechRankOneOmega i).val ∈ grade ℒ 2 := by
  rw [leechRankOneOmega_polynomial]
  have hw := (isWeightedHomogeneous_X ℂ (oscillatorWeight ℒ) (i, 0)).mul
    (isWeightedHomogeneous_X ℂ (oscillatorWeight ℒ) (i, 0))
  rw [MvPolynomial.smul_eq_C_mul]
  simpa only [chargeEnergy_zero, zero_add, Nat.cast_ofNat] using
    single_weighted_grade ℒ 0 _ 2 (hw.C_mul _)

/-- Abe's primary h(-1)^4 − 2 h(-3)h(-1) + (3/2)h(-2)^2, with unit h. -/
def leechRankOneQuartic (i : Fin (ℒ).rank) : FixedCarrier ℒ :=
  ⟨Finsupp.single 0
    ((κ[i]^4 / 4) • (X (i, 0))^4 -
      (κ[i]^2) • (X (i, 2) * X (i, 0)) +
      ((3 / 4 : ℂ) * κ[i]^2) • (X (i, 1) * X (i, 1))),
    (mem_fixedSpace ℒ _).mpr (by
      change thetaLinear ℒ (Finsupp.single 0 _) = _
      rw [theta_single, neg_zero]
      congr 1
      simp only [map_add, map_sub, sigma_smul, map_mul, map_pow, sigma_X, neg_mul_neg]
      rw [Even.neg_pow (by decide : Even (4 : ℕ))])⟩

theorem leechRankOneQuartic_grade (i : Fin (ℒ).rank) :
    (leechRankOneQuartic i).val ∈ grade ℒ 4 := by
  let p : Oscillator ℒ :=
    (κ[i]^4 / 4) • (X (i, 0))^4 -
      κ[i]^2 • (X (i, 2) * X (i, 0)) +
      ((3 / 4 : ℂ) * κ[i]^2) • (X (i, 1) * X (i, 1))
  change Finsupp.single 0 p ∈ _
  have h0 := isWeightedHomogeneous_X ℂ (oscillatorWeight ℒ) (i, 0)
  have h1 := isWeightedHomogeneous_X ℂ (oscillatorWeight ℒ) (i, 1)
  have h2 := isWeightedHomogeneous_X ℂ (oscillatorWeight ℒ) (i, 2)
  have hw : IsWeightedHomogeneous (oscillatorWeight ℒ) p 4 := by
    dsimp only [p]
    simp only [MvPolynomial.smul_eq_C_mul]
    exact (((h0.pow 4).C_mul _).sub ((h2.mul h0).C_mul _)).add ((h1.mul h1).C_mul _)
  simpa only [chargeEnergy_zero, zero_add, Nat.cast_ofNat] using single_weighted_grade ℒ 0 p 4 hw

private theorem evenZero_from_Corr (a : FixedCarrier ℒ) (d : ℕ)
    (ha : a.val ∈ grade ℒ (d : ℤ)) (p : Oscillator ℒ)
    (hp : a.val = Finsupp.single 0 p) (b : ℂ) (hb : (Corr ℒ 0 p) d = C b)
    (v : twistedTop ℒ leechUnit false) : fixedTopZero false a d ha v = b • v := by
  obtain ⟨y, rfl⟩ := (E).surjective v
  apply (E).symm.injective
  rw [map_smul, LinearEquiv.symm_apply_apply, evenTopGroundEquiv_symm_apply]
  change pi ℒ leechUnit ((fixedAction false a ((d : ℤ) - 1) (E y).val).val) = _
  rw [fixedAction_val, hp, show -2 * ((d : ℤ) - 1) - 2 = -2 * (d : ℤ) by ring]
  have h := LinearMap.congr_fun (compression_at_weight p d) y
  rw [hb] at h
  simpa [compression, iota, evenTopGroundEquiv_val,
    LatticeHalfFockGroundCompression.epsilon, MvPolynomial.lcoeff, MvPolynomial.coeff_C] using h

private theorem scale_gram (i : Fin (ℒ).rank) : κ[i]^2 * g[i] = 2 := by
  simpa only [pow_two, mul_assoc] using leechRankOneScale_contract i

/-- The actual rank-one L(0) on every even Leech ground tensor. -/
theorem leechRankOneOmega_even_zeroMode (i : Fin (ℒ).rank)
    (v : twistedTop ℒ leechUnit false) :
    fixedTopZero false (leechRankOneOmega i) 2 (leechRankOneOmega_grade i) v =
      (1 / 16 : ℂ) • v := by
  apply evenZero_from_Corr _ _ _ _ (leechRankOneOmega_polynomial i)
  rw [map_smul, Finsupp.smul_apply, corr_pair ℒ (i, 0) (i, 0) 2 rfl,
    MvPolynomial.smul_eq_C_mul, ← map_mul]
  congr 1
  have h := scale_gram i
  norm_num [sourceWeight, pairScalar, halfBinomial, Finset.prod_range_succ]
  linear_combination (1 / 32 : ℂ) * h

/-- The native o(h(-3)h(-1)1) on the even Leech top. -/
theorem leechAbeState_even_zeroMode (i : Fin (ℒ).rank)
    (v : twistedTop ℒ leechUnit false) :
    fixedTopZero false (leechAbeState i) 4 (leechAbeState_grade i) v =
      (15 / 128 : ℂ) • v := by
  apply evenZero_from_Corr _ _ _ _ (leechAbe_polynomial i)
  rw [map_smul, Finsupp.smul_apply, corr_pair ℒ (i, 2) (i, 0) 4 rfl,
    MvPolynomial.smul_eq_C_mul, ← map_mul]
  congr 1
  have h := scale_gram i
  norm_num [sourceWeight, pairScalar, halfBinomial, Finset.prod_range_succ]
  linear_combination (15 / 256 : ℂ) * h

/-- The weight-four primary's actual even-top eigenvalue, from all three oscillator terms. -/
theorem leechRankOneQuartic_even_zeroMode (i : Fin (ℒ).rank)
    (v : twistedTop ℒ leechUnit false) :
    fixedTopZero false (leechRankOneQuartic i) 4 (leechRankOneQuartic_grade i) v =
      (3 / 128 : ℂ) • v := by
  let p : Oscillator ℒ :=
    (κ[i]^4 / 4) • (X (i, 0))^4 -
      κ[i]^2 • (X (i, 2) * X (i, 0)) +
      ((3 / 4 : ℂ) * κ[i]^2) • (X (i, 1) * X (i, 1))
  apply evenZero_from_Corr _ _ _ p rfl
  let corr : Oscillator ℒ →ₗ[ℂ] Oscillator ℒ :=
    (Finsupp.lapply 4).comp (Corr ℒ 0)
  change corr p = _
  dsimp only [p]
  rw [map_add, map_sub, map_smul, map_smul, map_smul]
  change (κ[i]^4 / 4) • (Corr ℒ 0 (X (i, 0)^4)) 4 -
    κ[i]^2 • (Corr ℒ 0 (X (i, 2) * X (i, 0))) 4 +
    ((3 / 4 : ℂ) * κ[i]^2) • (Corr ℒ 0 (X (i, 1) * X (i, 1))) 4 = _
  rw [corr_four, corr_pair ℒ (i, 2) (i, 0) 4 rfl, corr_pair ℒ (i, 1) (i, 1) 4 rfl]
  simp only [MvPolynomial.smul_eq_C_mul, ← map_mul MvPolynomial.C,
    ← map_sub MvPolynomial.C, ← map_add MvPolynomial.C]
  congr 1
  have h := scale_gram i
  norm_num [sourceWeight, pairScalar, halfBinomial, Finset.prod_range_succ] at *
  have hh' : κ[i]^4 * g[i]^2 = 4 := by
    calc
      _ = (κ[i]^2 * g[i])^2 := by ring
      _ = _ := by rw [h]; norm_num
  linear_combination (3 / 256 : ℂ) * hh' - (3 / 256 : ℂ) * h

/-- The incompatible diagonal scalar in Abe (4.1) after evaluating (4.2)–(4.4). -/
theorem leechRankOne_even_spectral_obstruction (i : Fin (ℒ).rank)
    (v : twistedTop ℒ leechUnit false) :
    fixedTopZero false (leechRankOneQuartic i) 4 (leechRankOneQuartic_grade i) v -
      (4 : ℂ) • fixedTopZero false (leechRankOneOmega i) 2 (leechRankOneOmega_grade i)
        (fixedTopZero false (leechRankOneOmega i) 2 (leechRankOneOmega_grade i) v) +
      fixedTopZero false (leechRankOneOmega i) 2 (leechRankOneOmega_grade i) v =
      (9 / 128 : ℂ) • v := by
  simp only [leechRankOneQuartic_even_zeroMode, leechRankOneOmega_even_zeroMode]
  module

end
end D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeSameParity
