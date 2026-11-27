/- GID: D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2NeutralPower
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2NeutralPower
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Reduction of neutral charge-polynomial powers by oscillator length. -/

import D5.S3.VertexAlgebra.Lattice.FixedC2.ActualFixedC2NeutralMonomials
import D5.S3.VertexAlgebra.Lattice.FixedC2.ActualFixedC2Projection
import D5.S3.VertexAlgebra.Lattice.ActualLeechHyperbolic
import D5.S3.VertexAlgebra.Lattice.NormFourFixedPeirce

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.Lattice.ActualFixedC2

open LatticeGeneratingFieldLocality LatticeAllStateField LatticeAllStateReconstruction
open LatticeInvolution LatticeSugawaraConformal MvPolynomial
open scoped BigOperators

open private E ground orbit_coefficient creation_zero creation_negative chargePolynomial_neg
  from D5.S3.VertexAlgebra.Lattice.NormFourFixedPeirce
open private creation_derivation from D5.S3.VertexAlgebra.LatticeSugawaraConformal
open private higher_fixed_product_mem from D5.S3.VertexAlgebra.Lattice.FixedC2.ActualFixedC2NeutralMonomials

noncomputable section

local instance neutralPowerFixedCarrierGroup (D : LatticeData) : AddCommGroup (FixedCarrier D) :=
  (fixedSpace D).addCommGroup

/-- Oscillator polynomials spanned by words of length at most `n`. -/
def oscillatorLengthLE (D : LatticeData) (n : ℕ) : Submodule ℂ (Oscillator D) :=
  Submodule.span ℂ {p | ∃ w : List (Index D), w.length ≤ n ∧ p = neutralPolynomial D w}

private theorem word_mem_lengthLE (D : LatticeData) (w : List (Index D)) (n : ℕ)
    (hw : w.length ≤ n) : neutralPolynomial D w ∈ oscillatorLengthLE D n :=
  Submodule.subset_span ⟨w, hw, rfl⟩

private theorem oscillatorLengthLE_mono (D : LatticeData) {m n : ℕ} (h : m ≤ n) :
    oscillatorLengthLE D m ≤ oscillatorLengthLE D n := by
  apply Submodule.span_le.mpr
  rintro _ ⟨w, hw, rfl⟩
  exact word_mem_lengthLE D w n (hw.trans h)

private theorem variable_mul_mem (D : LatticeData) (x : Index D) {n : ℕ}
    {p : Oscillator D} (hp : p ∈ oscillatorLengthLE D n) :
    X x * p ∈ oscillatorLengthLE D (n + 1) := by
  change p ∈ (oscillatorLengthLE D (n + 1)).comap (LinearMap.mulLeft ℂ (X x))
  apply (Submodule.span_le.mpr ?_) hp
  rintro _ ⟨w, hw, rfl⟩
  exact word_mem_lengthLE D (x :: w) (n + 1) (by simpa using hw)

private theorem charge_mul_mem (D : LatticeData) (a : Charge D) {n : ℕ}
    {p : Oscillator D} (hp : p ∈ oscillatorLengthLE D n) :
    chargePolynomial D a * p ∈ oscillatorLengthLE D (n + 1) := by
  rw [chargePolynomial, Finset.sum_mul]
  apply Submodule.sum_mem
  intro i _
  rw [smul_mul_assoc]
  exact Submodule.smul_mem _ _ (variable_mul_mem D (i, 0) hp)

private theorem derivation_word_mem (D : LatticeData) (w : List (Index D)) :
    oscillatorDerivation D (neutralPolynomial D w) ∈ oscillatorLengthLE D w.length := by
  induction w with
  | nil => simp [neutralPolynomial]
  | cons x w ih =>
    change oscillatorDerivation D (X x * neutralPolynomial D w) ∈
      oscillatorLengthLE D (w.length + 1)
    rw [Derivation.leibniz]
    apply Submodule.add_mem
    · exact variable_mul_mem D x ih
    · rw [oscillatorDerivation, mkDerivation_X]
      change neutralPolynomial D w * ((x.2 + 1 : ℂ) • (X (x.1, x.2 + 1) : Oscillator D)) ∈ _
      rw [mul_comm (neutralPolynomial D w), smul_mul_assoc]
      exact Submodule.smul_mem _ _ (word_mem_lengthLE D ((x.1, x.2 + 1) :: w)
        (w.length + 1) (by simp))

private theorem derivation_mem_lengthLE (D : LatticeData) {n : ℕ} {p : Oscillator D}
    (hp : p ∈ oscillatorLengthLE D n) :
    oscillatorDerivation D p ∈ oscillatorLengthLE D n := by
  change p ∈ (oscillatorLengthLE D n).comap (oscillatorDerivation D).toLinearMap
  apply (Submodule.span_le.mpr ?_) hp
  rintro _ ⟨w, hw, rfl⟩
  exact oscillatorLengthLE_mono D hw (derivation_word_mem D w)

private theorem charge_pow_mem (D : LatticeData) (a : Charge D) (n : ℕ) :
    chargePolynomial D a ^ n ∈ oscillatorLengthLE D n := by
  induction n with
  | zero => simpa [neutralPolynomial] using word_mem_lengthLE D [] 0 (by simp)
  | succ n ih => rw [pow_succ']; exact charge_mul_mem D a ih

private theorem factorial_ne_zero (n : ℕ) : (n.factorial : ℂ) ≠ 0 :=
  Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)

private theorem factorial_creation_recurrence (D : LatticeData) (a : Charge D) (n : ℕ) :
    ((n + 1).factorial : ℂ) • creationCoeff D a ((n + 1 : ℕ) : ℤ) =
      (n.factorial : ℂ) • oscillatorDerivation D (creationCoeff D a n) +
        chargePolynomial D a * ((n.factorial : ℂ) • creationCoeff D a n) := by
  have h := creation_derivation D a (n : ℤ)
  rw [h, Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ, Nat.cast_succ, Int.cast_natCast,
    smul_sub, smul_smul, mul_smul_comm, mul_comm (n + 1 : ℂ)]
  abel

private theorem scaled_creation_length (D : LatticeData) (a : Charge D) (n : ℕ) :
    (n.factorial : ℂ) • creationCoeff D a n - chargePolynomial D a ^ n ∈
      oscillatorLengthLE D (n - 1) := by
  induction n with
  | zero => simp [creation_zero]
  | succ n ih =>
    let p := chargePolynomial D a
    let q := (n.factorial : ℂ) • creationCoeff D a n
    change _ • creationCoeff D a ((n + 1 : ℕ) : ℤ) - p ^ (n + 1) ∈
      oscillatorLengthLE D n
    have hq : q ∈ oscillatorLengthLE D n := by
      have h := (oscillatorLengthLE D n).add_mem
        (oscillatorLengthLE_mono D (Nat.sub_le n 1) ih) (charge_pow_mem D a n)
      simpa only [sub_add_cancel] using h
    have hderiv : oscillatorDerivation D q ∈ oscillatorLengthLE D n :=
      derivation_mem_lengthLE D hq
    have hmul : p * (q - p ^ n) ∈ oscillatorLengthLE D n := by
      cases n with
      | zero => simp [q, p, creation_zero]
      | succ n => exact charge_mul_mem D a ih
    rw [factorial_creation_recurrence, pow_succ', add_sub_assoc, ← mul_sub]
    exact (oscillatorLengthLE D n).add_mem
      (by simpa only [q, Derivation.map_smul] using hderiv) hmul

/-- The top oscillator length of the actual creation coefficient comes only
from the indicated power of the first creation coefficient. -/
theorem creationCoeff_sub_leading_mem (D : LatticeData) (a : Charge D) (n : ℕ) :
    creationCoeff D a n - (n.factorial : ℂ)⁻¹ • chargePolynomial D a ^ n ∈
      oscillatorLengthLE D (n - 1) := by
  simpa only [smul_sub, smul_smul, inv_mul_cancel₀ (factorial_ne_zero n), one_smul] using
    (oscillatorLengthLE D (n - 1)).smul_mem (n.factorial : ℂ)⁻¹
      (scaled_creation_length D a n)

/-- The literal invariant ground state `e^a + e^(-a)`. -/
def fixedEvenCharge (D : LatticeData) (a : Charge D) : FixedCarrier D :=
  ⟨E D a, by
    rw [mem_fixedSpace]
    simp only [E, ground, map_add]
    change thetaLinear D (Finsupp.single a 1) + thetaLinear D (Finsupp.single (-a) 1) = _
    simp only [theta_single, map_one, neg_neg, add_comm]⟩

/-- The signed sum of actual creation coefficients at vacuum charge. -/
def fixedNeutralCreation (D : LatticeData) (a : Charge D) (k : ℤ) : FixedCarrier D :=
  ⟨Finsupp.single 0 (creationCoeff D a k + creationCoeff D (-a) k), by
    rw [mem_fixedSpace]
    change thetaLinear D _ = _
    simp only [theta_single, neg_zero, map_add, sigma_creationCoeff, neg_neg, add_comm]⟩

/-- The diagonal fixed `(-3)` product has only the vacuum charge. -/
theorem fixed_ground_minus_three (D : LatticeData) (a : Charge D)
    (ha : 4 ≤ bilinear D a a) :
    fixedMode D (fixedEvenCharge D a) (-3) (fixedEvenCharge D a) =
      epsilon D a a • fixedNeutralCreation D a (bilinear D a a + 2) := by
  apply Subtype.ext
  change mu D (E D a) (-3) (E D a) = epsilon D a a • Finsupp.single 0 _
  rw [orbit_coefficient]
  have hneg : -(-3 : ℤ) - 1 - bilinear D a a < 0 := by omega
  simp only [creation_negative D _ _ hneg, Finsupp.single_zero, zero_add, sub_self,
    neg_zero, ← Finsupp.single_add, show -(-3 : ℤ) - 1 + bilinear D a a =
      bilinear D a a + 2 by omega]

/-- The signed actual creation coefficient is zero in the intrinsic fixed quotient. -/
theorem neutral_creation_class_zero (D : LatticeData) (a : Charge D)
    (ha : 4 ≤ bilinear D a a) :
    (fixedC2 D).mkQ (fixedNeutralCreation D a (bilinear D a a + 2)) = 0 := by
  have h : fixedMode D (fixedEvenCharge D a) (-3) (fixedEvenCharge D a) ∈ fixedC2 D :=
    higher_fixed_product_mem D 1 _ _
  rw [fixed_ground_minus_three D a ha] at h
  have he : epsilon D a a ≠ 0 := by
    unfold epsilon paritySign
    split_ifs <;> norm_num
  apply (Submodule.Quotient.mk_eq_zero (p := fixedC2 D)).mpr
  simpa only [smul_smul, inv_mul_cancel₀ he, one_smul] using
    (fixedC2 D).smul_mem (epsilon D a a)⁻¹ h

/-- The coefficient of the index-zero power in the signed actual sum at an even index. -/
theorem signed_creation_sub_leading_mem (D : LatticeData) (a : Charge D) (n : ℕ) (hn : Even n) :
    creationCoeff D a n + creationCoeff D (-a) n -
      (2 / (n.factorial : ℂ)) • chargePolynomial D a ^ n ∈ oscillatorLengthLE D (n - 1) := by
  have h := (oscillatorLengthLE D (n - 1)).add_mem
    (creationCoeff_sub_leading_mem D a n) (creationCoeff_sub_leading_mem D (-a) n)
  rw [chargePolynomial_neg, hn.neg_pow] at h
  convert h using 1
  rw [div_eq_mul_inv, two_mul, add_smul]
  abel

/-- The vacuum-charge state of an even power of the index-zero charge oscillator. -/
def fixedNeutralChargePower (D : LatticeData) (a : Charge D) (n : ℕ) (hn : Even n) :
    FixedCarrier D :=
  ⟨Finsupp.single 0 (chargePolynomial D a ^ n), by
    rw [mem_fixedSpace]
    change thetaLinear D _ = _
    have h : sigma D (chargePolynomial D a) = -chargePolynomial D a := by
      simp [chargePolynomial, Finset.sum_neg_distrib]
    rw [theta_single, neg_zero, map_pow, h, hn.neg_pow]⟩

/-- The span in intrinsic fixed C₂ of even neutral words of length strictly below `k`. -/
def neutralClassLengthLT (D : LatticeData) (k : ℕ) :
    Submodule ℂ (FixedCarrier D ⧸ fixedC2 D) :=
  Submodule.span ℂ {v | ∃ (w : List (Index D)) (hw : Even w.length),
    w.length < k ∧ v = neutralWordClass D w hw}

private theorem projected_short_polynomial (D : LatticeData) {n k : ℕ} (hn : n < k)
    {p : Oscillator D} (hp : p ∈ oscillatorLengthLE D n) :
    (fixedC2 D).mkQ (plusProjection D (Finsupp.single 0 p)) ∈ neutralClassLengthLT D k := by
  let f := (fixedC2 D).mkQ.comp ((plusProjection D).comp (Finsupp.lsingle 0))
  change p ∈ (neutralClassLengthLT D k).comap f
  apply (Submodule.span_le.mpr ?_) hp
  rintro _ ⟨w, hw, rfl⟩
  change (fixedC2 D).mkQ (plusProjection D (neutralWord D w)) ∈ neutralClassLengthLT D k
  rcases Nat.even_or_odd w.length with he | ho
  · change (fixedC2 D).mkQ (plusProjection D (fixedNeutralWord D w he).val) ∈ _
    rw [plusProjection_fixed]
    exact Submodule.subset_span ⟨w, he, lt_of_le_of_lt hw hn, rfl⟩
  · have h : theta D (neutralWord D w) = -neutralWord D w := by
      change thetaLinear D (Finsupp.single 0 (neutralPolynomial D w)) =
        -Finsupp.single 0 (neutralPolynomial D w)
      have hs : sigma D (neutralPolynomial D w) =
          (-1 : ℂ)^w.length • neutralPolynomial D w := sigma_word_product D w
      rw [theta_single, neg_zero, hs, ho.neg_one_pow, neg_one_smul, Finsupp.single_neg]
    rw [plusProjection_odd D _ h, map_zero]
    exact Submodule.zero_mem _

/-- The even index-zero charge power reduces to strictly shorter even neutral
words in the intrinsic fixed quotient. -/
theorem fixed_neutral_charge_power_length_reduction (D : LatticeData) (a : Charge D)
    (ha : 4 ≤ bilinear D a a) :
    let k := (bilinear D a a + 2).toNat
    ∃ hk : Even k, (fixedC2 D).mkQ (fixedNeutralChargePower D a k hk) ∈
      neutralClassLengthLT D k := by
  let k := (bilinear D a a + 2).toNat
  have hcast : (k : ℤ) = bilinear D a a + 2 := Int.toNat_of_nonneg (by omega)
  have hk : Even k := by
    have he := LatticePositiveEnergy.two_chargeEnergy D a
    rw [Nat.even_iff]
    omega
  refine ⟨hk, ?_⟩
  let c : ℂ := 2 / (k.factorial : ℂ)
  have hc : c ≠ 0 := div_ne_zero (by norm_num) (factorial_ne_zero k)
  let v := fixedNeutralCreation D a k - c • fixedNeutralChargePower D a k hk
  have hv : v.val = Finsupp.single 0
      (creationCoeff D a k + creationCoeff D (-a) k - c • chargePolynomial D a ^ k) := by
    change Finsupp.single 0 (creationCoeff D a k + creationCoeff D (-a) k) -
      c • Finsupp.single 0 (chargePolynomial D a ^ k) = _
    rw [Finsupp.smul_single, ← Finsupp.single_sub]
  have h := projected_short_polynomial D (n := k - 1) (k := k)
    (by omega) (signed_creation_sub_leading_mem D a k hk)
  rw [← hv, plusProjection_fixed] at h
  have hzero : (fixedC2 D).mkQ (fixedNeutralCreation D a k) = 0 := by
    rw [hcast]
    exact neutral_creation_class_zero D a ha
  dsimp only [v] at h
  rw [map_sub, map_smul, hzero, zero_sub] at h
  simpa only [neg_neg, smul_smul, inv_mul_cancel₀ hc, one_smul] using
    (neutralClassLengthLT D k).smul_mem c⁻¹ ((neutralClassLengthLT D k).neg_mem h)

open ActualLeechHyperbolic
open D5.S3.Arith.Lattices.Golay

/-- The minimum norm of the actual Golay-Leech lattice, in the same charge
coordinates used by its lattice fields. -/
theorem leech_charge_norm_ge_four (a : Charge leechData) (ha : a ≠ 0) :
    4 ≤ bilinear leechData a a := by
  obtain ⟨b, hb, hcoords⟩ :=
    (RealLeech.mem_lattice _).mp (leechCoordinates a).property
  have hb0 : b ≠ 0 := by
    intro h
    have hzero : leechCoordinates a = 0 := by
      apply Subtype.ext
      simpa [h] using hcoords.symm
    exact ha (leechCoordinates.injective (by simpa using hzero))
  have hmin := IntegerLeech.minimum_norm.1 b hb hb0
  have hsq : (32 : ℤ) ≤ IntegerLeech.squareSum b := by
    unfold IntegerLeech.scaledSquare at hmin
    exact_mod_cast (show (32 : ℚ) ≤ (IntegerLeech.squareSum b : ℚ) by linarith)
  have hform : (bilinear leechData a a : ℝ) =
      (IntegerLeech.squareSum b : ℝ) / 8 := by
    rw [leech_spec.2.2.2 a a, ← hcoords]
    simp [RealLeech.pairing, DirectLeechDuality.B, RealLeech.castLinear,
      IntegerLeech.squareSum, pow_two, dotProduct]
    ring
  have hsqr : (32 : ℝ) ≤ (IntegerLeech.squareSum b : ℝ) := by exact_mod_cast hsq
  exact_mod_cast (show (4 : ℝ) ≤ (bilinear leechData a a : ℝ) by linarith)

/-- Every nonzero charge of the actual Leech lattice has the indicated
index-zero power reduction in the intrinsic fixed C₂ quotient. -/
theorem leech_fixed_neutral_charge_power_length_reduction (a : Charge leechData) (ha : a ≠ 0) :
    let k := (bilinear leechData a a + 2).toNat
    ∃ hk : Even k,
      (fixedC2 leechData).mkQ (fixedNeutralChargePower leechData a k hk) ∈
        neutralClassLengthLT leechData k :=
  fixed_neutral_charge_power_length_reduction leechData a (leech_charge_norm_ge_four a ha)

end

end D5.S3.VertexAlgebra.Lattice.ActualFixedC2

#print axioms D5.S3.VertexAlgebra.Lattice.ActualFixedC2.creationCoeff_sub_leading_mem
#print axioms D5.S3.VertexAlgebra.Lattice.ActualFixedC2.fixed_ground_minus_three
#print axioms D5.S3.VertexAlgebra.Lattice.ActualFixedC2.neutral_creation_class_zero
#print axioms D5.S3.VertexAlgebra.Lattice.ActualFixedC2.signed_creation_sub_leading_mem
#print axioms D5.S3.VertexAlgebra.Lattice.ActualFixedC2.fixed_neutral_charge_power_length_reduction
#print axioms D5.S3.VertexAlgebra.Lattice.ActualFixedC2.leech_charge_norm_ge_four
#print axioms D5.S3.VertexAlgebra.Lattice.ActualFixedC2.leech_fixed_neutral_charge_power_length_reduction
