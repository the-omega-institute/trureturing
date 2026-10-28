/- GID: D5/S3/VertexAlgebra/Lattice/NormFourVirasoroVector
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/NormFourVirasoroVector
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual norm-four lattice self-products and integer Virasoro modes. -/

/-
The standard formula is Shimakura, arXiv:1202.6107, PDF p. 4, (1.3),
where the original Ising-vector assertion is attributed to Dong--Mason--Zhu,
Theorem 6.3.  The displayed formula, cocycle normalization and stated lattice
context were checked in that public PDF; DMZ94 itself was not retrieved.
Actual lattice-field attribution is Bakalov--Kac, math/0402315, section 4.1.
Imported normal-product/residue and Sugawara suppliers retain their existing
Carnahan and Kytola Apache 2.0 attribution in their owning source files.
The source below concerns the actual ungraded lattice carrier and operators.
It makes no simple-minimal-model, ambient-conformal-vector, rationality,
Miyamoto-involution, Monster, string-theory or AdS/CFT completion claim.

Live content: finite oscillator contractions and actual opposite/same-charge
cancellations, including the all-order tail.  Generic ground-series,
state/field reconstruction and state derivative suppliers are reused.
-/

import D5.S3.VertexAlgebra.LatticeActualConformalState
import D5.S3.VertexAlgebra.LatticeActualStateDerivative
import D5.S3.VertexAlgebra.LatticeActualOrderedProducts
import D5.S3.VertexAlgebra.LatticeTwistedGroundRealization
import Batteries.Tactic.OpenPrivate

/-! The actual norm-four lattice state and its central-charge-one-half mode action. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

-- These are existing proved suppliers, not new derivative/cocycle axioms.
open private creation_derivation partial_charge charge_pairing charge_transport
  from D5.S3.VertexAlgebra.LatticeSugawaraConformal

namespace D5.S3.VertexAlgebra.Lattice.NormFourVirasoroVector

open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration
open LatticeAllStateField LatticeAllStateReconstruction
open LatticeActualStateFieldCalculus LatticeActualStateDerivative
open LatticeActualConformalState LatticeSugawaraConformal LatticeSugawaraCurrents
open LatticeActualGeneratorLocality LatticeActualProductKernel
open LatticeActualOrderedProducts FieldNormalProduct MvPolynomial
open StateFieldResidueReconstruction (integerBinomial)
open scoped BigOperators VertexOperator

noncomputable section

private def osc (D : LatticeData) (a : Charge D) (r : ℕ) : Oscillator D :=
  ∑ i : Fin D.rank, (a i : ℂ) • X (i, r)

private abbrev ground (D : LatticeData) (a : Charge D) : Carrier D :=
  Finsupp.single a (1 : Oscillator D)

def quadraticState (D : LatticeData) (a : Charge D) : Carrier D :=
  Finsupp.single 0 ((chargePolynomial D a)^2)

def chargedState (D : LatticeData) (a : Charge D) : Carrier D :=
  ground D a + ground D (-a)

/-- The candidate is an actual state, with its scalar sign kept explicit. -/
def vector (D : LatticeData) (a : Charge D) (s : ℂ) : Carrier D :=
  (1 / 16 : ℂ) • quadraticState D a + (s / 4) • chargedState D a

def mode (D : LatticeData) (a : Charge D) (s : ℂ) (m : ℤ) :
    Module.End ℂ (Carrier D) := ((Y D (vector D a s))[[m + 1]])

private theorem osc_zero (D : LatticeData) (a : Charge D) :
    osc D a 0 = chargePolynomial D a := rfl

private theorem osc_neg (D : LatticeData) (a : Charge D) (r : ℕ) :
    osc D (-a) r = -osc D a r := by
  simp [osc, neg_smul, Finset.sum_neg_distrib]

private theorem charge_neg (D : LatticeData) (a : Charge D) :
    chargePolynomial D (-a) = -chargePolynomial D a := by
  simpa only [osc_zero] using osc_neg D a 0

private theorem deriv_osc (D : LatticeData) (a : Charge D) (r : ℕ) :
    oscillatorDerivation D (osc D a r) = (r + 1 : ℂ) • osc D a (r + 1) := by
  simp [osc, oscillatorDerivation, Finset.smul_sum, smul_smul, mul_comm]

private theorem deriv_charge (D : LatticeData) (a : Charge D) :
    oscillatorDerivation D (chargePolynomial D a) = osc D a 1 := by
  simpa only [osc_zero, Nat.cast_zero, zero_add, one_smul] using deriv_osc D a 0

private theorem creation_zero (D : LatticeData) (a : Charge D) :
    creationCoeff D a 0 = 1 := by
  simp [creationCoeff, exponential_constant]

private theorem creation_one (D : LatticeData) (a : Charge D) :
    creationCoeff D a 1 = chargePolynomial D a := by
  have h := creation_derivation D a 0
  simp only [creation_zero, Derivation.map_one_eq_zero, Int.cast_zero,
    zero_add, one_smul, mul_one] at h
  exact sub_eq_zero.mp h.symm

private theorem creation_two (D : LatticeData) (a : Charge D) :
    creationCoeff D a 2 = (1 / 2 : ℂ) •
      (osc D a 1 + (chargePolynomial D a)^2) := by
  have h := creation_derivation D a 1
  simp only [creation_one, deriv_charge, ← pow_two] at h
  norm_num only [Int.cast_one, one_add_one_eq_two] at h
  have h' : (2 : ℂ) • creationCoeff D a 2 =
      osc D a 1 + (chargePolynomial D a)^2 :=
    (eq_sub_iff_add_eq.mp h).symm
  calc
    creationCoeff D a 2 = (1 / 2 : ℂ) • ((2 : ℂ) • creationCoeff D a 2) := by
      norm_num [smul_smul]
    _ = _ := by rw [h']

private theorem creation_three (D : LatticeData) (a : Charge D) :
    creationCoeff D a 3 =
      (1 / 3 : ℂ) • osc D a 2 +
      (1 / 2 : ℂ) • (chargePolynomial D a * osc D a 1) +
      (1 / 6 : ℂ) • (chargePolynomial D a)^3 := by
  have h := creation_derivation D a 2
  simp only [creation_two] at h
  simp only [pow_two, mul_add, mul_smul_comm] at h
  norm_num at h
  simp only [deriv_charge, deriv_osc] at h
  norm_num at h
  have h' : (3 : ℂ) • creationCoeff D a 3 =
      (1 / 2 : ℂ) • ((2 : ℂ) • osc D a 2 +
        (chargePolynomial D a * osc D a 1 + chargePolynomial D a * osc D a 1)) +
      (1 / 2 : ℂ) • (chargePolynomial D a * osc D a 1 +
        chargePolynomial D a * (chargePolynomial D a * chargePolynomial D a)) := by
    convert (eq_sub_iff_add_eq.mp h).symm using 1
    module
  calc
    creationCoeff D a 3 = (1 / 3 : ℂ) • ((3 : ℂ) • creationCoeff D a 3) := by
      norm_num [smul_smul]
    _ = _ := by
      rw [h']
      rw [show (chargePolynomial D a)^3 =
        chargePolynomial D a * (chargePolynomial D a * chargePolynomial D a) by ring]
      module

private theorem opposite_phase (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) : epsilon D a (-a) = 1 := by
  have hneg : lowerCocycleExponent D a (-a) = -lowerCocycleExponent D a a := by
    unfold lowerCocycleExponent
    simp only [Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]
    abel
  rw [epsilon, hneg,
    LatticeTwistedGroundRealization.SignQuotient.integral_cocycle_square, ha]
  norm_num [paritySign]

private theorem neg_norm (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) : bilinear D (-a) (-a) = 4 := by
  rw [bilinear_neg_left, bilinear_neg_right, neg_neg, ha]

private theorem product_add_left (D : LatticeData) (a b c : Carrier D) (n : ℤ) :
    mu D (a + b) n c = mu D a n c + mu D b n c := by
  simp only [mu, map_add, VertexOperator.ncoeff, Pi.add_apply, LinearMap.add_apply]

private theorem product_add_right (D : LatticeData) (a b c : Carrier D) (n : ℤ) :
    mu D a n (b + c) = mu D a n b + mu D a n c := by
  exact map_add ((Y D a)[[n]]) b c

private theorem ground_product (D : LatticeData) (a b : Charge D) (n : ℤ) :
    mu D (ground D a) n (ground D b) =
      epsilon D a b • Finsupp.single (a + b)
        (creationCoeff D a (-n - 1 - bilinear D a b)) := by
  rw [mu, stateField_ground, actual_modes, raw_ground]

private theorem same_charge_vanish (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (n : ℤ) (hn : 0 ≤ n) :
    mu D (ground D a) n (ground D a) = 0 := by
  rw [ground_product, ha]
  simp [creationCoeff, show -n - 1 - (4 : ℤ) < 0 by omega]

private theorem opposite_charge (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (n : ℤ) :
    mu D (ground D a) n (ground D (-a)) =
      Finsupp.single 0 (creationCoeff D a (3 - n)) := by
  rw [ground_product, opposite_phase D a ha, bilinear_neg_right, ha,
    one_smul, add_neg_cancel,
    show -n - 1 - (-(4 : ℤ)) = 3 - n by omega]

private theorem charged_series (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (n : ℤ) (hn : 0 ≤ n) :
    mu D (chargedState D a) n (chargedState D a) =
      Finsupp.single 0 (creationCoeff D a (3 - n) + creationCoeff D (-a) (3 - n)) := by
  simp only [chargedState, product_add_left, product_add_right]
  rw [same_charge_vanish D a ha n hn,
    same_charge_vanish D (-a) (neg_norm D a ha) n hn,
    opposite_charge D a ha]
  have h := opposite_charge D (-a) (neg_norm D a ha) n
  simp only [neg_neg] at h
  rw [h]
  simp only [zero_add, add_zero, Finsupp.single_add]
  exact add_comm _ _

/-- Actual charged self-contractions: both charge directions, all singular
coefficients, and the entire nonnegative tail, without positivity hypotheses. -/
private theorem charged_self_products (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) :
    mu D (chargedState D a) 0 (chargedState D a) =
        Finsupp.single 0 (chargePolynomial D a * osc D a 1) ∧
    mu D (chargedState D a) 1 (chargedState D a) = quadraticState D a ∧
    mu D (chargedState D a) 2 (chargedState D a) = 0 ∧
    mu D (chargedState D a) 3 (chargedState D a) = (2 : ℂ) • vacuum D ∧
    ∀ n : ℤ, 4 ≤ n → mu D (chargedState D a) n (chargedState D a) = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [charged_series D a ha 0 (by omega)]
    norm_num only [sub_zero]
    rw [creation_three, creation_three]
    simp only [charge_neg, osc_neg, pow_succ, pow_zero, one_mul,
      neg_mul, mul_neg, neg_neg]
    congr 1
    module
  · rw [charged_series D a ha 1 (by omega)]
    norm_num only [show (3 : ℤ) - 1 = 2 by omega]
    rw [creation_two, creation_two]
    simp only [charge_neg, osc_neg, neg_sq]
    change Finsupp.single 0 _ = Finsupp.single 0 _
    congr 1
    module
  · rw [charged_series D a ha 2 (by omega)]
    norm_num only [show (3 : ℤ) - 2 = 1 by omega]
    rw [creation_one, creation_one, charge_neg, add_neg_cancel, Finsupp.single_zero]
  · rw [charged_series D a ha 3 (by omega)]
    norm_num only [sub_self]
    rw [creation_zero, creation_zero]
    simp [vacuum, two_smul]
  · intro n hn
    rw [charged_series D a ha n (by omega)]
    simp [creationCoeff, show (3 : ℤ) - n < 0 by omega]

private abbrev currentStateAlong (D : LatticeData) (a : Charge D) : Carrier D :=
  Finsupp.single 0 (chargePolynomial D a)

private def currentMode (D : LatticeData) (a : Charge D) (n : ℤ) :
    Module.End ℂ (Carrier D) := ((Y D (currentStateAlong D a))[[n]])

private theorem current_field (D : LatticeData) (a : Charge D) :
    Y D (currentStateAlong D a) = ∑ i : Fin D.rank, (a i : ℂ) • neutralField D i := by
  have hs : currentStateAlong D a =
      ∑ i : Fin D.rank, (a i : ℂ) • currentState D i := by
    simp only [currentStateAlong, chargePolynomial, currentState,
      Finsupp.single_finsetSum, ← Finsupp.smul_single]
  rw [hs, map_sum]
  simp only [map_smul, current_state_field]

private theorem currentMode_sum (D : LatticeData) (a : Charge D) (n : ℤ) :
    currentMode D a n = ∑ i : Fin D.rank, (a i : ℂ) • neutralMode D i n := by
  unfold currentMode
  rw [current_field]
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply,
    neutralField_ncoeff]

private theorem currentMode_single (D : LatticeData) (a b : Charge D)
    (n : ℤ) (p : Oscillator D) :
    currentMode D a n (Finsupp.single b p) =
      Finsupp.single b (∑ i : Fin D.rank,
        (a i : ℂ) • neutralPolynomialMode D i b n p) := by
  rw [currentMode_sum]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, neutralMode_single,
    Finsupp.smul_single]
  rw [Finsupp.single_finsetSum]

private theorem currentMode_negative (D : LatticeData) (a b : Charge D)
    (r : ℕ) (p : Oscillator D) :
    currentMode D a (-(r : ℤ) - 1) (Finsupp.single b p) =
      Finsupp.single b (osc D a r * p) := by
  rw [currentMode_single]
  simp only [osc, neutralPolynomialMode_negative, LinearMap.mulLeft_apply,
    smul_mul_assoc, Finset.sum_mul]

private theorem pairing_left (D : LatticeData) (a b : Charge D) :
    (∑ i : Fin D.rank, (a i : ℂ) * (bilinear D (unitCharge D i) b : ℂ)) =
      (bilinear D a b : ℂ) := by
  have h := charge_pairing D b a
  simp only [bilinear_symmetric D b] at h
  exact_mod_cast h

private theorem gram_smul (D : LatticeData) (a : Charge D) (p : Oscillator D) :
    (∑ i : Fin D.rank, (a i : ℂ) •
      ∑ j : Fin D.rank, (D.G i j : ℂ) • ((a j : ℂ) • p)) =
      (bilinear D a a : ℂ) • p := by
  have hc : (∑ i : Fin D.rank, ∑ j : Fin D.rank,
      (a i : ℂ) * (D.G i j : ℂ) * (a j : ℂ)) = (bilinear D a a : ℂ) := by
    simp only [bilinear, Int.cast_sum, Int.cast_mul]
  simp only [Finset.smul_sum, smul_smul, ← mul_assoc]
  simp_rw [← Finset.sum_smul]
  rw [hc]

private theorem currentMode_ground (D : LatticeData) (a b : Charge D)
    (n : ℤ) (hn : 0 ≤ n) :
    currentMode D a n (ground D b) =
      if n = 0 then (bilinear D a b : ℂ) • ground D b else 0 := by
  rw [currentMode_single]
  by_cases hz : n = 0
  · subst n
    simp only [neutralPolynomialMode, lt_self_iff_false, ite_false, ite_true,
      LinearMap.smul_apply, LinearMap.id_apply, smul_smul]
    rw [← Finset.sum_smul, pairing_left]
    simp only [Finsupp.smul_single]
  · simp [neutralPolynomialMode, not_lt.mpr hn, hz, Derivation.map_one_eq_zero]

private theorem currentMode_current (D : LatticeData) (a : Charge D)
    (n : ℤ) (hn : 0 ≤ n) :
    currentMode D a n (currentStateAlong D a) =
      if n = 1 then (bilinear D a a : ℂ) • vacuum D else 0 := by
  rw [currentMode_single]
  by_cases hz : n = 0
  · subst n
    simp [neutralPolynomialMode, bilinear]
  · by_cases ho : n = 1
    · subst n
      simp only [neutralPolynomialMode, show ¬ (1 : ℤ) < 0 by omega,
        show (1 : ℤ) ≠ 0 by omega, ite_false, Int.cast_one, one_smul, Int.reduceSub,
        Int.toNat_zero, LinearMap.sum_apply, LinearMap.smul_apply,
        Derivation.coeFn_coe, partial_charge, ite_true]
      simp_rw [MvPolynomial.C_eq_smul_one]
      rw [gram_smul]
      simp [vacuum, Finsupp.smul_single]
    · have hr : n.toNat - 1 ≠ 0 := by omega
      simp [neutralPolynomialMode, not_lt.mpr hn, hz, ho, partial_charge, hr]

private theorem partial_quadratic (D : LatticeData) (a : Charge D)
    (j : Fin D.rank) (r : ℕ) :
    pderiv (j, r) ((chargePolynomial D a)^2) =
      if r = 0 then (2 * (a j : ℂ)) • chargePolynomial D a else 0 := by
  rw [pow_two, pderiv_mul]
  simp only [partial_charge]
  by_cases hr : r = 0
  · simp only [hr, ite_true, MvPolynomial.C_eq_smul_one, smul_mul_assoc,
      one_mul, mul_smul_comm, mul_one]
    module
  · simp [hr]

private theorem currentMode_quadratic (D : LatticeData) (a : Charge D)
    (n : ℤ) (hn : 0 ≤ n) :
    currentMode D a n (quadraticState D a) =
      if n = 1 then (2 * (bilinear D a a : ℂ)) • currentStateAlong D a else 0 := by
  rw [quadraticState, currentMode_single]
  by_cases hz : n = 0
  · subst n
    simp [neutralPolynomialMode, bilinear]
  · by_cases ho : n = 1
    · subst n
      simp only [neutralPolynomialMode, show ¬ (1 : ℤ) < 0 by omega,
        show (1 : ℤ) ≠ 0 by omega, ite_false, Int.cast_one, one_smul, Int.reduceSub,
        Int.toNat_zero, LinearMap.sum_apply, LinearMap.smul_apply,
        Derivation.coeFn_coe, partial_quadratic, ite_true]
      have hs : (∑ i : Fin D.rank, (a i : ℂ) •
          ∑ j : Fin D.rank, (D.G i j : ℂ) •
            ((2 * (a j : ℂ)) • chargePolynomial D a)) =
          (2 : ℂ) • ((bilinear D a a : ℂ) • chargePolynomial D a) := by
        rw [← gram_smul]
        simp only [Finset.smul_sum, smul_smul]
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        congr 1
        ring
      rw [hs]
      simp only [Finsupp.smul_single, smul_smul]
    · have hr : (n - 1).toNat ≠ 0 := by omega
      simp only [neutralPolynomialMode, not_lt.mpr hn, hz, ite_false,
        LinearMap.smul_apply, LinearMap.sum_apply, Derivation.coeFn_coe]
      simp only [partial_quadratic, hr, ho, ite_false,
        smul_zero, Finset.sum_const_zero, Finsupp.single_zero]

private theorem quadratic_normal_field (D : LatticeData) (a : Charge D) :
    Y D (quadraticState D a) =
      (normalMinusOne (Y D (currentStateAlong D a))
        (Y D (currentStateAlong D a))).1 := by
  have hc : mu D (currentStateAlong D a) (-1) (currentStateAlong D a) =
      quadraticState D a := by
    change currentMode D a (-1) (currentStateAlong D a) = _
    simpa [currentStateAlong, quadraticState, osc_zero, pow_two] using
      currentMode_negative D a 0 0 (chargePolynomial D a)
  rw [← hc, minus_one_product_field]

-- This is the linear extension of the existing exact actual quadratic-state
-- identification, and is consumed when expanding the actual candidate field.
private theorem quadratic_field_expansion (D : LatticeData) (a : Charge D) :
    Y D (quadraticState D a) =
      ∑ i : Fin D.rank, ∑ j : Fin D.rank,
        ((a i : ℂ) * (a j : ℂ)) • quadraticSummand D i j := by
  have hp : (chargePolynomial D a)^2 =
      ∑ i : Fin D.rank, ∑ j : Fin D.rank,
        ((a i : ℂ) * (a j : ℂ)) • (X (i, 0) * X (j, 0) : Oscillator D) := by
    simp only [pow_two, chargePolynomial, Finset.sum_mul, Finset.mul_sum,
      smul_mul_assoc, mul_smul_comm, Finset.smul_sum, smul_smul]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [mul_comm (X (j, 0) : Oscillator D) (X (i, 0))]
  rw [quadraticState, hp, Finsupp.single_finsetSum, map_sum]
  simp_rw [Finsupp.single_finsetSum, map_sum, ← Finsupp.smul_single,
    map_smul, quadratic_state_field]

private theorem quadratic_product_formula (D : LatticeData) (a : Charge D)
    (n : ℤ) (b : Carrier D) :
    mu D (quadraticState D a) n b =
      (∑ᶠ j : ℕ, currentMode D a (-(j : ℤ) - 1)
        (currentMode D a (n + j) b)) +
      (∑ᶠ j : ℕ, currentMode D a (n - j - 1)
        (currentMode D a j b)) := by
  simpa only [mu, quadratic_normal_field, currentMode] using
    (normalMinusOne (Y D (currentStateAlong D a))
      (Y D (currentStateAlong D a))).2 n b

private theorem quadratic_ground_reduction (D : LatticeData) (a b : Charge D)
    (n : ℤ) (hn : 0 ≤ n) :
    mu D (quadraticState D a) n (ground D b) =
      currentMode D a (-1) (currentMode D a n (ground D b)) +
      currentMode D a (n - 1) (currentMode D a 0 (ground D b)) := by
  rw [quadratic_product_formula]
  have first : (∑ᶠ j : ℕ, currentMode D a (-(j : ℤ) - 1)
      (currentMode D a (n + j) (ground D b))) =
      currentMode D a (-1) (currentMode D a n (ground D b)) := by
    rw [finsum_eq_single _ 0]
    · simp only [Nat.cast_zero, neg_zero, zero_sub, add_zero]
    · intro j hj
      rw [currentMode_ground D a b (n + j) (by omega),
        ite_eq_right (by omega), map_zero]
  have second : (∑ᶠ j : ℕ, currentMode D a (n - j - 1)
      (currentMode D a j (ground D b))) =
      currentMode D a (n - 1) (currentMode D a 0 (ground D b)) := by
    rw [finsum_eq_single _ 0]
    · simp only [Nat.cast_zero, sub_zero]
    · intro j hj
      rw [currentMode_ground D a b j (by omega), ite_eq_right (by omega), map_zero]
  rw [first, second]

private theorem quadratic_quadratic_reduction (D : LatticeData) (a : Charge D)
    (n : ℤ) (hn : 0 ≤ n) :
    mu D (quadraticState D a) n (quadraticState D a) =
      (currentMode D a (-1) (currentMode D a n (quadraticState D a)) +
        currentMode D a (-2) (currentMode D a (n + 1) (quadraticState D a))) +
      (currentMode D a (n - 1) (currentMode D a 0 (quadraticState D a)) +
        currentMode D a (n - 2) (currentMode D a 1 (quadraticState D a))) := by
  rw [quadratic_product_formula]
  have first : (∑ᶠ j : ℕ, currentMode D a (-(j : ℤ) - 1)
      (currentMode D a (n + j) (quadraticState D a))) =
      ∑ j ∈ Finset.range 2, currentMode D a (-(j : ℤ) - 1)
        (currentMode D a (n + j) (quadraticState D a)) := by
    apply finsum_eq_sum_of_support_subset
    intro j hj
    apply Finset.mem_range.mpr
    by_contra h
    exact hj (by dsimp only; rw [currentMode_quadratic D a (n + j) (by omega),
      ite_eq_right (by omega), map_zero])
  have second : (∑ᶠ j : ℕ, currentMode D a (n - j - 1)
      (currentMode D a j (quadraticState D a))) =
      ∑ j ∈ Finset.range 2, currentMode D a (n - j - 1)
        (currentMode D a j (quadraticState D a)) := by
    apply finsum_eq_sum_of_support_subset
    intro j hj
    apply Finset.mem_range.mpr
    by_contra h
    exact hj (by dsimp only; rw [currentMode_quadratic D a j (by omega),
      ite_eq_right (by omega), map_zero])
  rw [first, second]
  norm_num [Finset.sum_range_succ, show n - 1 - 1 = n - 2 by omega]

private theorem translation_quadratic (D : LatticeData) (a : Charge D) :
    translation D (quadraticState D a) =
      (2 : ℂ) • Finsupp.single 0 (chargePolynomial D a * osc D a 1) := by
  rw [quadraticState, translation_single, pow_two, Derivation.leibniz]
  have hz : chargePolynomial D (0 : Charge D) = 0 := by simp [chargePolynomial]
  simp only [hz, zero_mul, add_zero, smul_eq_mul, deriv_charge,
    Finsupp.smul_single]
  congr 1
  module

private theorem quadratic_self_products (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) :
    mu D (quadraticState D a) 0 (quadraticState D a) =
        (8 : ℂ) • translation D (quadraticState D a) ∧
    mu D (quadraticState D a) 1 (quadraticState D a) =
        (16 : ℂ) • quadraticState D a ∧
    mu D (quadraticState D a) 2 (quadraticState D a) = 0 ∧
    mu D (quadraticState D a) 3 (quadraticState D a) = (32 : ℂ) • vacuum D ∧
    ∀ n : ℤ, 4 ≤ n → mu D (quadraticState D a) n (quadraticState D a) = 0 := by
  have inner (n : ℤ) (hn : 0 ≤ n) :
      currentMode D a n (quadraticState D a) =
        if n = 1 then (8 : ℂ) • currentStateAlong D a else 0 := by
    rw [currentMode_quadratic D a n hn, ha]
    norm_num
  have current (n : ℤ) (hn : 0 ≤ n) :
      currentMode D a n (currentStateAlong D a) =
        if n = 1 then (4 : ℂ) • vacuum D else 0 := by
    rw [currentMode_current D a n hn, ha]
    norm_num
  have neg_one : currentMode D a (-1) (currentStateAlong D a) = quadraticState D a := by
    simpa [currentStateAlong, quadraticState, osc_zero, pow_two] using
      currentMode_negative D a 0 0 (chargePolynomial D a)
  have neg_two : currentMode D a (-2) (currentStateAlong D a) =
      Finsupp.single 0 (chargePolynomial D a * osc D a 1) := by
    simpa [currentStateAlong, mul_comm] using
      currentMode_negative D a 0 1 (chargePolynomial D a)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [quadratic_quadratic_reduction D a 0 (by omega)]
    norm_num only [inner 0 (by omega), inner 1 (by omega), map_zero,
      ite_true, show (0 : ℤ) ≠ 1 by omega, ite_false, map_smul]
    simp only [neg_two, translation_quadratic]
    module
  · rw [quadratic_quadratic_reduction D a 1 (by omega)]
    norm_num only [inner 0 (by omega), inner 1 (by omega), inner 2 (by omega),
      map_zero, ite_true, show (0 : ℤ) ≠ 1 by omega,
      show (2 : ℤ) ≠ 1 by omega, ite_false, map_smul]
    simp only [neg_one]
    module
  · rw [quadratic_quadratic_reduction D a 2 (by omega)]
    norm_num only [inner, current, map_smul, map_zero, smul_zero, zero_add,
      add_zero, smul_smul, ite_true, ite_false]
  · rw [quadratic_quadratic_reduction D a 3 (by omega)]
    norm_num only [inner, current, map_smul, map_zero, smul_zero, zero_add,
      add_zero, smul_smul, ite_true, ite_false]
  · intro n hn
    rw [quadratic_quadratic_reduction D a n (by omega)]
    rw [inner n (by omega), inner (n + 1) (by omega),
      inner 0 (by omega), inner 1 (by omega)]
    simp only [ite_eq_right (show n ≠ 1 by omega),
      ite_eq_right (show n + 1 ≠ 1 by omega), ite_eq_right (show (0 : ℤ) ≠ 1 by omega),
      ite_true, map_zero, map_smul, zero_add]
    rw [current (n - 2) (by omega), ite_eq_right (by omega), smul_zero]

private theorem quadratic_ground_zero (D : LatticeData) (a b : Charge D) :
    mu D (quadraticState D a) 0 (ground D b) =
      (2 * (bilinear D a b : ℂ)) • Finsupp.single b (chargePolynomial D a) := by
  have hm : currentMode D a (-1) (ground D b) =
      Finsupp.single b (chargePolynomial D a) := by
    simpa [osc_zero] using currentMode_negative D a b 0 (1 : Oscillator D)
  rw [quadratic_ground_reduction D a b 0 (by omega),
    show (0 : ℤ) - 1 = -1 by omega]
  simp only [currentMode_ground D a b 0 (by omega), ite_true, map_smul]
  rw [hm]
  module

private theorem quadratic_ground_one (D : LatticeData) (a b : Charge D) :
    mu D (quadraticState D a) 1 (ground D b) =
      (bilinear D a b : ℂ)^2 • ground D b := by
  rw [quadratic_ground_reduction D a b 1 (by omega)]
  norm_num only [currentMode_ground, map_smul, map_zero, smul_zero, zero_add,
    add_zero, smul_smul, pow_two, ite_true, ite_false]

private theorem quadratic_ground_tail (D : LatticeData) (a b : Charge D)
    (n : ℤ) (hn : 2 ≤ n) : mu D (quadraticState D a) n (ground D b) = 0 := by
  rw [quadratic_ground_reduction D a b n (by omega),
    currentMode_ground D a b n (by omega), currentMode_ground D a b 0 (by omega)]
  simp only [ite_eq_right (show n ≠ 0 by omega), ite_true, map_zero, map_smul, zero_add]
  rw [currentMode_ground D a b (n - 1) (by omega), ite_eq_right (by omega), smul_zero]

private theorem quadratic_charged_products (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) :
    mu D (quadraticState D a) 0 (chargedState D a) =
        (8 : ℂ) • translation D (chargedState D a) ∧
    mu D (quadraticState D a) 1 (chargedState D a) = (16 : ℂ) • chargedState D a ∧
    ∀ n : ℤ, 2 ≤ n → mu D (quadraticState D a) n (chargedState D a) = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [chargedState, product_add_right]
    rw [quadratic_ground_zero, quadratic_ground_zero]
    simp only [bilinear_neg_right, ha]
    simp only [map_add, translation_single, Derivation.map_one_eq_zero,
      zero_add, mul_one, charge_neg, Finsupp.single_neg]
    norm_num only [Int.cast_neg, Int.cast_ofNat]
    module
  · simp only [chargedState, product_add_right]
    rw [quadratic_ground_one, quadratic_ground_one]
    simp only [bilinear_neg_right, ha]
    norm_num
  · intro n hn
    simp only [chargedState, product_add_right,
      quadratic_ground_tail D a a n hn, quadratic_ground_tail D a (-a) n hn,
      add_zero]

private theorem ground_quadratic_formula (D : LatticeData) (b a : Charge D) (n : ℤ) :
    mu D (ground D b) n (quadraticState D a) =
      Finsupp.single b
        ((chargePolynomial D a)^2 * creationCoeff D b (-n - 1) -
          (2 * (bilinear D b a : ℂ)) •
            (chargePolynomial D a * creationCoeff D b (-n)) +
          (bilinear D b a : ℂ)^2 • creationCoeff D b (1 - n)) := by
  rw [mu, stateField_ground, actual_modes, quadraticState, raw_single_convolution]
  have hb0 : bilinear D b (0 : Charge D) = 0 := by simp [bilinear]
  have he0 : epsilon D b (0 : Charge D) = 1 := by
    simp [epsilon, lowerCocycleExponent, paritySign]
  rw [hb0, he0, one_smul, add_zero, sub_zero]
  have hmap : translatedPolynomial D b ((chargePolynomial D a)^2) =
      (translatedPolynomial D b (chargePolynomial D a))^2 := by
    simp only [translatedPolynomial, map_pow]
  rw [hmap, charge_transport]
  have hp :
      (Polynomial.C (chargePolynomial D a) -
        Polynomial.C ((bilinear D b a : ℂ) • (1 : Oscillator D)) * Polynomial.X)^2 =
      Polynomial.monomial 0 ((chargePolynomial D a)^2) -
        Polynomial.monomial 1 ((2 * (bilinear D b a : ℂ)) • chargePolynomial D a) +
        Polynomial.monomial 2 ((bilinear D b a : ℂ)^2 • (1 : Oscillator D)) := by
    simp only [← Polynomial.C_mul_X_pow_eq_monomial, smul_eq_C_mul,
      map_mul, map_pow, map_ofNat, pow_zero, pow_one, mul_one]
    norm_num
    ring
  rw [hp, map_add, map_sub, convolution_monomial,
    convolution_monomial, convolution_monomial]
  rw [show -n - 1 + (0 : ℕ) = -n - 1 by omega,
    show -n - 1 + (1 : ℕ) = -n by omega,
    show -n - 1 + (2 : ℕ) = 1 - n by omega]
  simp only [smul_mul_assoc, one_mul]

private theorem ground_quadratic_zero (D : LatticeData) (b a : Charge D) :
    mu D (ground D b) 0 (quadraticState D a) =
      Finsupp.single b ((bilinear D b a : ℂ)^2 • chargePolynomial D b -
        (2 * (bilinear D b a : ℂ)) • chargePolynomial D a) := by
  rw [ground_quadratic_formula]
  norm_num only [neg_zero, zero_sub, sub_zero]
  rw [show creationCoeff D b (-1) = 0 by simp [creationCoeff],
    creation_zero, creation_one, mul_zero, mul_one, zero_sub]
  congr 1
  abel

private theorem ground_quadratic_one (D : LatticeData) (b a : Charge D) :
    mu D (ground D b) 1 (quadraticState D a) =
      (bilinear D b a : ℂ)^2 • ground D b := by
  rw [ground_quadratic_formula]
  norm_num only [neg_add_rev, neg_neg, neg_zero, zero_sub, sub_self,
    creation_zero, show (-1 : ℤ) - 1 = -2 by omega]
  simp [creationCoeff, Finsupp.smul_single]

private theorem ground_quadratic_tail (D : LatticeData) (b a : Charge D)
    (n : ℤ) (hn : 2 ≤ n) : mu D (ground D b) n (quadraticState D a) = 0 := by
  rw [ground_quadratic_formula]
  have h0 : creationCoeff D b (-n - 1) = 0 := by
    rw [creationCoeff, dite_eq_left (by omega)]
  have h1 : creationCoeff D b (-n) = 0 := by
    rw [creationCoeff, dite_eq_left (by omega)]
  have h2 : creationCoeff D b (1 - n) = 0 := by
    rw [creationCoeff, dite_eq_left (by omega)]
  rw [h0, h1, h2]
  simp only [mul_zero, smul_zero, sub_zero, add_zero, Finsupp.single_zero]

private theorem charged_quadratic_products (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) :
    mu D (chargedState D a) 0 (quadraticState D a) =
        (8 : ℂ) • translation D (chargedState D a) ∧
    mu D (chargedState D a) 1 (quadraticState D a) = (16 : ℂ) • chargedState D a ∧
    ∀ n : ℤ, 2 ≤ n → mu D (chargedState D a) n (quadraticState D a) = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [chargedState, product_add_left]
    rw [ground_quadratic_zero, ground_quadratic_zero]
    simp only [bilinear_neg_left, ha]
    simp only [map_add, translation_single, Derivation.map_one_eq_zero,
      zero_add, mul_one, charge_neg, Finsupp.single_neg]
    norm_num
    simp only [← Finsupp.smul_single]
    module
  · simp only [chargedState, product_add_left]
    rw [ground_quadratic_one, ground_quadratic_one]
    simp only [bilinear_neg_left, ha]
    norm_num
  · intro n hn
    simp only [chargedState, product_add_left,
      ground_quadratic_tail D a a n hn, ground_quadratic_tail D (-a) a n hn,
      add_zero]

private theorem vector_product_expansion (D : LatticeData) (a : Charge D)
    (s : ℂ) (hs : s ^ 2 = 1) (n : ℤ) :
    mu D (vector D a s) n (vector D a s) =
      (1 / 256 : ℂ) • mu D (quadraticState D a) n (quadraticState D a) +
      (s / 64) • mu D (quadraticState D a) n (chargedState D a) +
      (s / 64) • mu D (chargedState D a) n (quadraticState D a) +
      (1 / 16 : ℂ) • mu D (chargedState D a) n (chargedState D a) := by
  have hss : (s / 4) * (s / 4) = (1 / 16 : ℂ) := by
    calc
      (s / 4) * (s / 4) = s ^ 2 / 16 := by ring
      _ = 1 / 16 := by rw [hs]
  simp only [vector, mu, map_add, map_smul, quadratic_field_expansion,
    VertexOperator.ncoeff, Pi.add_apply, Pi.smul_apply,
    LinearMap.add_apply, LinearMap.smul_apply, smul_add, smul_smul, hss]
  module

/-- The five actual self-OPE parts.  The two signs are included by s ^ 2 = 1;
there is no assumed OPE, representation, positivity or positive-rank premise. -/
theorem self_products (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1) :
    mu D (vector D a s) 0 (vector D a s) = translation D (vector D a s) ∧
    mu D (vector D a s) 1 (vector D a s) = (2 : ℂ) • vector D a s ∧
    mu D (vector D a s) 2 (vector D a s) = 0 ∧
    mu D (vector D a s) 3 (vector D a s) = (1 / 4 : ℂ) • vacuum D ∧
    ∀ n : ℤ, 4 ≤ n → mu D (vector D a s) n (vector D a s) = 0 := by
  obtain ⟨q0, q1, q2, q3, qt⟩ := quadratic_self_products D a ha
  obtain ⟨b0, b1, b2, b3, bt⟩ := charged_self_products D a ha
  obtain ⟨qb0, qb1, qbt⟩ := quadratic_charged_products D a ha
  obtain ⟨bq0, bq1, bqt⟩ := charged_quadratic_products D a ha
  have b0' : mu D (chargedState D a) 0 (chargedState D a) =
      (1 / 2 : ℂ) • translation D (quadraticState D a) := by
    rw [b0, translation_quadratic]
    norm_num [smul_smul]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [vector_product_expansion D a s hs 0, q0, qb0, bq0, b0']
    simp only [vector, map_add, map_smul]
    module
  · rw [vector_product_expansion D a s hs 1, q1, qb1, bq1, b1]
    simp only [vector, smul_add, smul_smul]
    module
  · rw [vector_product_expansion D a s hs 2, q2,
      qbt 2 (by omega), bqt 2 (by omega), b2]
    simp
  · rw [vector_product_expansion D a s hs 3, q3,
      qbt 3 (by omega), bqt 3 (by omega), b3]
    module
  · intro n hn
    rw [vector_product_expansion D a s hs n, qt n hn,
      qbt n (by omega), bqt n (by omega), bt n hn]
    simp

-- Ring.choose, rather than Nat.choose or a nonnegative-upper-index shortcut,
-- is essential here: m + 1 is allowed to be negative.
private theorem central_binomial (m : ℤ) :
    (1 / 4 : ℂ) * integerBinomial (m + 1) 3 =
      ((m : ℂ)^3 - (m : ℂ)) / 24 := by
  have h := Ring.descPochhammer_eq_factorial_smul_choose (m + 1) 3
  norm_num [descPochhammer_succ_right, descPochhammer_zero,
    Polynomial.smeval_mul, Polynomial.smeval_sub, Polynomial.smeval_X,
    Polynomial.smeval_natCast, Polynomial.smeval_one, nsmul_eq_mul] at h
  rw [show (2 : Polynomial ℤ) = Polynomial.C 2 by norm_num, Polynomial.smeval_C] at h
  norm_num at h
  have hc := congrArg (fun z : ℤ => (z : ℂ)) h
  push_cast at hc
  unfold integerBinomial
  linear_combination -(1 / 24 : ℂ) * hc

/-- The supported all-integer Virasoro relation of the actual field of the
norm-four state.  This asserts an action of central charge 1/2; it asserts
neither simplicity of the generated vertex algebra nor an ambient grading. -/
theorem virasoro_commutator (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1) (m n : ℤ) :
    mode D a s m * mode D a s n - mode D a s n * mode D a s m =
      ((m : ℂ) - (n : ℂ)) • mode D a s (m + n) +
        (if m + n = 0 then
          (((m : ℂ)^3 - (m : ℂ)) / 24) • (1 : Module.End ℂ (Carrier D))
        else 0) := by
  classical
  obtain ⟨h0, h1, h2, h3, ht⟩ := self_products D a ha s hs
  have finite : (∑ᶠ j : ℕ,
      commutatorTerm D (vector D a s) (vector D a s) (m + 1) (n + 1) j) =
      ∑ j ∈ Finset.range 4,
        commutatorTerm D (vector D a s) (vector D a s) (m + 1) (n + 1) j := by
    apply finsum_eq_sum_of_support_subset
    intro j hj
    apply Finset.mem_range.mpr
    by_contra outside
    have high : 4 ≤ (j : ℤ) := by omega
    exact hj (by simp [commutatorTerm, ht j high])
  have term0 : commutatorTerm D (vector D a s) (vector D a s) (m + 1) (n + 1) 0 =
      -((m + n + 2 : ℤ) : ℂ) • mode D a s (m + n) := by
    unfold commutatorTerm
    simp only [Nat.cast_zero]
    rw [h0, show (m + 1) + (n + 1) - (0 : ℤ) = m + n + 2 by omega,
      state_derivative_modes, show m + n + 2 - 1 = m + n + 1 by omega]
    simp only [integerBinomial, Ring.choose_zero_right, Int.cast_one, one_smul] <;> rfl
  have term1 : commutatorTerm D (vector D a s) (vector D a s) (m + 1) (n + 1) 1 =
      (2 * ((m + 1 : ℤ) : ℂ)) • mode D a s (m + n) := by
    unfold commutatorTerm
    simp only [Nat.cast_one]
    rw [h1]
    simp only [map_smul, Pi.smul_apply, smul_smul, integerBinomial,
      Ring.choose_one_right]
    rw [show (m + 1) + (n + 1) - (1 : ℤ) = m + n + 1 by omega]
    change _ • mode D a s (m + n) = _
    congr 1
    ring
  have term2 : commutatorTerm D (vector D a s) (vector D a s) (m + 1) (n + 1) 2 = 0 := by
    simp [commutatorTerm, h2]
  have term3 : commutatorTerm D (vector D a s) (vector D a s) (m + 1) (n + 1) 3 =
      if m + n = 0 then
        (((m : ℂ)^3 - (m : ℂ)) / 24) • (1 : Module.End ℂ (Carrier D)) else 0 := by
    unfold commutatorTerm
    norm_num only [Nat.cast_ofNat]
    rw [h3]
    simp only [map_smul, Pi.smul_apply, stateField_vacuum, identity_modes, smul_smul]
    rw [show (m + 1) + (n + 1) - (3 : ℤ) = m + n - 1 by omega]
    by_cases hmn : m + n = 0
    · rw [ite_eq_left hmn, ite_eq_left (show m + n - 1 = -1 by omega)]
      change _ • (1 : Module.End ℂ (Carrier D)) = _
      congr 1
      simpa only [mul_comm] using central_binomial m
    · simp [hmn, show m + n - 1 ≠ -1 by omega]
  have h := mode_commutator D (vector D a s) (vector D a s) (m + 1) (n + 1)
  change mode D a s m * mode D a s n - mode D a s n * mode D a s m = _ at h
  rw [finite] at h
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, add_zero] at h
  rw [term0, term1, term2, term3] at h
  rw [h]
  push_cast
  module

end
end D5.S3.VertexAlgebra.Lattice.NormFourVirasoroVector
