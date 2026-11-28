/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/P48qChargedLocality
   generality: I
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Pairwise locality of native charged fields via finite Laurent coefficient shifts. -/

import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qChargedOrderedProduct
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qOrderedScalarExchange
import D5.S3.VertexAlgebra.Lattice.Orbifold.ThirdTwistedScalarLocality
import Batteries.Tactic.OpenPrivate
import Mathlib.Tactic.Abel
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

/-!
Pairwise locality of the native P48q charged fields in the cover coordinates.
Finite Laurent factors act by finite sums of coefficient shifts in either radial order.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48qThirdTwistedField

open HahnSeries (single)
open LatticeGeneratingFieldLocality (Charge bilinear)
open LatticeFiniteNegativeGeneration (bilinear_symmetric)
open P48qTwistedChargeAction (lattice g g_cube g_isometry Momentum)
open ThirdTwistedContraction (clearedContractionNumerator clearedContractionNumerator_eval
  contractionLocalityOrder contractionLocalityOrder_add_nonneg
  contractionOrbitExponent reciprocityPhase)
open scoped BigOperators

open private sum_orbitPairing from
  D5.S3.VertexAlgebra.Lattice.Orbifold.ThirdTwistedContractionReciprocity

noncomputable section

attribute [local instance 2000] HahnSeries.instAlgebra

local notation "ζ" => ThirdTwistedChargeCocycle.zeta
local notation "c₃" => ThirdTwistedChargeCocycle.c lattice g
local notation "shift" => ThirdTwistedChargeAction.shift lattice g

/-- The right cover variable is the outer Laurent variable. -/
abbrev CoverSeries (R : Type*) [Zero R] := LaurentSeries (LaurentSeries R)

/-- The monomial with inner degree `k`, outer degree `l`, and coefficient `c`. -/
def coverMonomial {R : Type*} [Zero R] (k l : ℤ) (c : R) : CoverSeries R :=
  single l (single k c)

private theorem coverMonomial_mul {R : Type*} [CommRing R] (k l r s : ℤ) (c d : R) :
    coverMonomial k l c * coverMonomial r s d = coverMonomial (k + r) (l + s) (c * d) := by
  simp only [coverMonomial, HahnSeries.single_mul_single]

private theorem coverMonomial_pow {R : Type*} [CommRing R] (k l : ℤ) (n : ℕ) :
    coverMonomial k l (1 : R) ^ n = coverMonomial ((n : ℤ) * k) ((n : ℤ) * l) 1 := by
  induction n with
  | zero => simp [coverMonomial]
  | succ n ih => rw [pow_succ, ih, coverMonomial_mul, Nat.cast_succ, add_mul, add_mul,
      one_mul, one_mul, one_mul]

private def coverUnit {R : Type*} [CommRing R] (k l : ℤ) : (CoverSeries R)ˣ where
  val := coverMonomial k l 1
  inv := coverMonomial (-k) (-l) 1
  val_inv := by rw [coverMonomial_mul]; simp [coverMonomial]
  inv_val := by rw [coverMonomial_mul]; simp [coverMonomial]

private theorem coverUnit_pow {R : Type*} [CommRing R] (k l : ℤ) (n : ℕ) :
    (coverUnit k l : (CoverSeries R)ˣ) ^ n = coverUnit ((n : ℤ) * k) ((n : ℤ) * l) := by
  apply Units.ext
  exact coverMonomial_pow k l n

private theorem coverUnit_zpow {R : Type*} [CommRing R] (k l n : ℤ) :
    (↑((coverUnit k l : (CoverSeries R)ˣ) ^ n) : CoverSeries R) =
      coverMonomial (n * k) (n * l) 1 := by
  cases n with
  | ofNat n =>
    rw [Int.ofNat_eq_natCast, zpow_natCast, coverUnit_pow]
    rfl
  | negSucc n =>
    rw [zpow_negSucc, coverUnit_pow]
    change coverMonomial (-((n.succ : ℤ) * k)) (-((n.succ : ℤ) * l)) 1 = _
    simp only [show Int.negSucc n = -(n.succ : ℤ) by omega, neg_mul]

private def coverC {R : Type*} [CommRing R] : R →+* CoverSeries R :=
  HahnSeries.C.comp HahnSeries.C

/-- Evaluate a finite polynomial at two Laurent monomials given by their degree pairs. -/
def coverEval {S R : Type*} [CommRing S] [CommRing R]
    (f : S →+* R) (v w : ℤ × ℤ) : MvPolynomial (Fin 2) S →+* CoverSeries R :=
  MvPolynomial.eval₂Hom (coverC.comp f)
    ![coverMonomial v.1 v.2 1, coverMonomial w.1 w.2 1]

private theorem coverEval_monomial {S R : Type*} [CommRing S] [CommRing R]
    (f : S →+* R) (v w : ℤ × ℤ) (d : Fin 2 →₀ ℕ) (c : S) :
    coverEval f v w (MvPolynomial.monomial d c) =
      coverMonomial ((d 0 : ℤ) * v.1 + (d 1 : ℤ) * w.1)
        ((d 0 : ℤ) * v.2 + (d 1 : ℤ) * w.2) (f c) := by
  rw [coverEval, MvPolynomial.eval₂Hom_monomial, Finsupp.prod_pow, Fin.prod_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, coverMonomial_pow, coverMonomial_mul]
  change coverMonomial 0 0 (f c) * coverMonomial _ _ (1 * 1) = _
  rw [coverMonomial_mul, zero_add, zero_add, one_mul, mul_one]

private theorem coverMonomial_mul_coeff {R : Type*} [CommRing R]
    (c : R) (A : CoverSeries R) (k l r s : ℤ) :
    ((coverMonomial r s c * A).coeff l).coeff k = c * ((A.coeff (l - s)).coeff (k - r)) := by
  rw [coverMonomial, HahnSeries.coeff_single_mul, HahnSeries.coeff_single_mul]

private theorem coverEval_mul_coeff {S R : Type*} [CommRing S] [CommRing R]
    (f : S →+* R) (v w : ℤ × ℤ) (Q : MvPolynomial (Fin 2) S)
    (A : CoverSeries R) (k l : ℤ) :
    ((coverEval f v w Q * A).coeff l).coeff k =
      ∑ d ∈ Q.support, f (Q.coeff d) *
        ((A.coeff (l - ((d 0 : ℤ) * v.2 + (d 1 : ℤ) * w.2))).coeff
          (k - ((d 0 : ℤ) * v.1 + (d 1 : ℤ) * w.1))) := by
  conv_lhs => rw [Q.as_sum]
  simp only [map_sum, Finset.sum_mul, HahnSeries.coeff_sum, coverEval_monomial,
    coverMonomial_mul_coeff]

private theorem coverEval_mul_coeff_swap {S R : Type*} [CommRing S] [CommRing R]
    (f : S →+* R) (v w : ℤ × ℤ) (Q : MvPolynomial (Fin 2) S) {A B : CoverSeries R}
    (h : ∀ k l : ℤ, (A.coeff l).coeff k = (B.coeff k).coeff l) (k l : ℤ) :
    ((coverEval f v w Q * A).coeff l).coeff k =
      ((coverEval f (v.2, v.1) (w.2, w.1) Q * B).coeff k).coeff l := by
  simp only [coverEval_mul_coeff, h]

private abbrev XY := CoverSeries Fock
private abbrev XSeries := LaurentSeries Fock

local notation "𝕏" => (coverMonomial 1 0 (1 : Fock))
local notation "𝕐" => (coverMonomial 0 1 (1 : Fock))
local notation "polyC" => (Polynomial.CAlgHom : Fock →ₐ[ℂ] Polynomial Fock)

private def inverseEval : Polynomial Fock →+* XSeries :=
  Polynomial.eval₂RingHom HahnSeries.C (single (-1 : ℤ) 1)

private theorem yExpansion_eq (A : PowerSeries (Polynomial Fock)) :
    yExpansion A = HahnSeries.ofPowerSeries ℤ XSeries (A.map inverseEval) := rfl

private theorem inverseEval_C (P : Fock) : inverseEval (Polynomial.C P) = HahnSeries.C P :=
  Polynomial.eval₂_C _ _

private theorem inverseEval_X : inverseEval Polynomial.X = single (-1 : ℤ) 1 :=
  Polynomial.eval₂_X _ _

/-- The two native creation exponentials in the right variable outermost order. -/
def creationProduct (B : FixedDualBases) (a b : Charge lattice) : CoverSeries Fock :=
  HahnSeries.C (HahnSeries.ofPowerSeries ℤ Fock (creationExponential B a)) *
    yExpansion (PowerSeries.mapAlgHom polyC (creationExponential B b))

private theorem creationProduct_coeff (B : FixedDualBases) (a b : Charge lattice) (k l : ℤ) :
    ((creationProduct B a b).coeff l).coeff k =
      creationCoeff B a k * creationCoeff B b l := by
  have hc (A : PowerSeries Fock) :
      PowerSeries.map inverseEval (PowerSeries.mapAlgHom polyC A) = A.map HahnSeries.C := by
    apply PowerSeries.ext
    intro n
    simp only [PowerSeries.mapAlgHom_apply, PowerSeries.coeff_map,
      AlgHom.coe_toRingHom, Polynomial.CAlgHom_apply, inverseEval_C]
  have hi (a : Charge lattice) (k : ℤ) :
      (HahnSeries.ofPowerSeries ℤ Fock (creationExponential B a)).coeff k =
        creationCoeff B a k := by
    rw [PowerSeries.coeff_coe, creationCoeff]
    cases k with
    | ofNat n =>
      simp only [Int.ofNat_eq_natCast, ite_eq_right (Int.natCast_nonneg n).not_gt,
        Int.natAbs_natCast, Int.toNat_natCast]
    | negSucc n => simp only [Int.negSucc_lt_zero, ite_true]
  have ho (A : PowerSeries Fock) (l : ℤ) :
      (HahnSeries.ofPowerSeries ℤ XSeries (A.map HahnSeries.C)).coeff l =
        HahnSeries.C ((HahnSeries.ofPowerSeries ℤ Fock A).coeff l) := by
    simp only [PowerSeries.coeff_coe]
    split_ifs <;> simp only [map_zero, PowerSeries.coeff_map]
  rw [creationProduct, yExpansion_eq, hc]
  change ((single 0 (HahnSeries.ofPowerSeries ℤ Fock (creationExponential B a)) *
    HahnSeries.ofPowerSeries ℤ XSeries ((creationExponential B b).map HahnSeries.C)).coeff l
    ).coeff k = _
  rw [HahnSeries.coeff_single_zero_mul, ho]
  change (HahnSeries.ofPowerSeries ℤ Fock (creationExponential B a) *
    single 0 ((HahnSeries.ofPowerSeries ℤ Fock (creationExponential B b)).coeff l)).coeff k = _
  rw [HahnSeries.coeff_mul_single_zero, hi, hi]

/-- The finite oscillator substitution in the inverse cover coordinates.
Coordinate 0 belongs to the first field and coordinate 1 to the second. -/
def finiteChargedTranslation (B : FixedDualBases) (a b : Charge lattice) :
    Fock →ₐ[ℂ] MvPolynomial (Fin 2) Fock :=
  MvPolynomial.aeval fun j =>
    MvPolynomial.C (MvPolynomial.X j) -
      MvPolynomial.C (annihilationPairing B a j • (1 : Fock)) *
        MvPolynomial.X 0 ^ frequency j -
      MvPolynomial.C (annihilationPairing B b j • (1 : Fock)) *
        MvPolynomial.X 1 ^ frequency j

private def inverseOuterEval : Polynomial XSeries →+* XY :=
  Polynomial.eval₂RingHom (HahnSeries.C : XSeries →+* XY) (single (-1 : ℤ) (1 : XSeries))

private theorem inverseOuterEval_C (s : XSeries) :
    inverseOuterEval (Polynomial.C s) = HahnSeries.C s := Polynomial.eval₂_C _ _

private theorem inverseOuterEval_X : inverseOuterEval Polynomial.X = single (-1 : ℤ) 1 :=
  Polynomial.eval₂_X _ _

private theorem inverseCover₂_eq (Q : Polynomial (Polynomial Fock)) :
    inverseCover₂ Q = inverseOuterEval (Q.map inverseEval) := rfl

private theorem translation_normalForm (B : FixedDualBases) (a b : Charge lattice) (P : Fock) :
    inverseCover₂ (translateOuter B b (translatedPolynomial B a P)) =
      coverEval (RingHom.id Fock) (-1, 0) (0, -1) (finiteChargedTranslation B a b P) := by
  have hcomm := DFunLike.congr_fun (translatedPolynomial_commute B a b) P
  change Polynomial.mapAlgHom (translatedPolynomial B a) (translatedPolynomial B b P) =
    translateOuter B b (translatedPolynomial B a P) at hcomm
  rw [← hcomm]
  let lhs := inverseCover₂.toRingHom.comp
    (((Polynomial.mapAlgHom (translatedPolynomial B a)).comp
      (translatedPolynomial B b)).toRingHom)
  let rhs := (coverEval (RingHom.id Fock) (-1, 0) (0, -1)).comp
    (finiteChargedTranslation B a b).toRingHom
  change lhs P = rhs P
  suffices h : lhs = rhs from DFunLike.congr_fun h P
  apply MvPolynomial.ringHom_ext
  · intro c
    change inverseCover₂ (Polynomial.mapAlgHom (translatedPolynomial B a)
      (translatedPolynomial B b (MvPolynomial.C c))) =
      coverEval (RingHom.id Fock) (-1, 0) (0, -1)
        (finiteChargedTranslation B a b (MvPolynomial.C c))
    rw [show finiteChargedTranslation B a b (MvPolynomial.C c) =
        MvPolynomial.C (MvPolynomial.C c) from MvPolynomial.aeval_C _ _]
    simp only [translatedPolynomial, MvPolynomial.algebraMap_eq, MvPolynomial.aeval_C,
      Polynomial.algebraMap_apply,
      Polynomial.coe_mapAlgHom, Polynomial.map_C, AlgHom.coe_toRingHom,
      inverseCover₂_eq, inverseEval_C, inverseOuterEval_C, coverEval,
      MvPolynomial.eval₂Hom_C, RingHom.comp_apply, RingHom.id_apply]
    rfl
  · intro j
    have hgen (a : Charge lattice) :
        translatedPolynomial B a (MvPolynomial.X j) = translationVariable B a j := by
      rw [translatedPolynomial, MvPolynomial.aeval_X]
    have hconst (c : ℂ) : translatedPolynomial B a (c • (1 : Fock)) =
        Polynomial.C (c • (1 : Fock)) := by
      simpa only [Algebra.smul_def, mul_one, Polynomial.algebraMap_apply] using
        (translatedPolynomial B a).commutes c
    change inverseCover₂ (Polynomial.mapAlgHom (translatedPolynomial B a)
      (translatedPolynomial B b (MvPolynomial.X j))) =
      coverEval (RingHom.id Fock) (-1, 0) (0, -1)
        (finiteChargedTranslation B a b (MvPolynomial.X j))
    rw [hgen b, translationVariable]
    simp only [Polynomial.coe_mapAlgHom, Polynomial.map_C, Polynomial.map_X,
      AlgHom.coe_toRingHom, hgen a,
      hconst, translationVariable, inverseCover₂_eq, inverseEval_C, inverseEval_X,
      inverseOuterEval_C, inverseOuterEval_X, map_sub, map_mul, map_pow]
    simp only [finiteChargedTranslation,
      MvPolynomial.aeval_X, coverEval, map_sub, map_mul, map_pow, MvPolynomial.eval₂Hom_C,
      MvPolynomial.eval₂Hom_X', Matrix.cons_val_zero, Matrix.cons_val_one]
    rfl

private theorem translation_normalForm_swap (B : FixedDualBases)
    (a b : Charge lattice) (P : Fock) :
    inverseCover₂ (translateOuter B a (translatedPolynomial B b P)) =
      coverEval (RingHom.id Fock) (0, -1) (-1, 0) (finiteChargedTranslation B a b P) := by
  rw [translation_normalForm]
  let lhs := (coverEval (RingHom.id Fock) (-1, 0) (0, -1)).comp
    (finiteChargedTranslation B b a).toRingHom
  let rhs := (coverEval (RingHom.id Fock) (0, -1) (-1, 0)).comp
    (finiteChargedTranslation B a b).toRingHom
  change lhs P = rhs P
  suffices h : lhs = rhs from DFunLike.congr_fun h P
  apply MvPolynomial.ringHom_ext
  · intro c
    change coverEval (RingHom.id Fock) (-1, 0) (0, -1)
        (finiteChargedTranslation B b a (MvPolynomial.C c)) =
      coverEval (RingHom.id Fock) (0, -1) (-1, 0)
        (finiteChargedTranslation B a b (MvPolynomial.C c))
    rw [show finiteChargedTranslation B b a (MvPolynomial.C c) =
        MvPolynomial.C (MvPolynomial.C c) from MvPolynomial.aeval_C _ _,
      show finiteChargedTranslation B a b (MvPolynomial.C c) =
        MvPolynomial.C (MvPolynomial.C c) from MvPolynomial.aeval_C _ _]
    simp only [coverEval, MvPolynomial.eval₂Hom_C]
  · intro j
    change coverEval (RingHom.id Fock) (-1, 0) (0, -1)
        (finiteChargedTranslation B b a (MvPolynomial.X j)) =
      coverEval (RingHom.id Fock) (0, -1) (-1, 0)
        (finiteChargedTranslation B a b (MvPolynomial.X j))
    simp only [finiteChargedTranslation,
      MvPolynomial.aeval_X, coverEval, map_sub, map_mul, map_pow, MvPolynomial.eval₂Hom_C,
      MvPolynomial.eval₂Hom_X', Matrix.cons_val_zero, Matrix.cons_val_one]
    abel

/-- The shared finite scalar and the two actual finite substitutions preserve
coefficient equality under exchange of the two nesting orders. -/
theorem normalOrdered_coeff_swap (B : FixedDualBases) (a b : Charge lattice) (P : Fock)
    (Q : MvPolynomial (Fin 2) ℂ) (r s k l : ℤ) :
    ((coverMonomial r s (1 : Fock) *
      coverEval (algebraMap ℂ Fock) (1, 0) (0, 1) Q *
      creationProduct B a b *
      inverseCover₂ (translateOuter B b (translatedPolynomial B a P))).coeff l).coeff k =
    ((coverMonomial s r (1 : Fock) *
      coverEval (algebraMap ℂ Fock) (0, 1) (1, 0) Q *
      creationProduct B b a *
      inverseCover₂ (translateOuter B a (translatedPolynomial B b P))).coeff k).coeff l := by
  rw [translation_normalForm, translation_normalForm_swap]
  have h (k l : ℤ) : ((creationProduct B a b).coeff l).coeff k =
      ((creationProduct B b a).coeff k).coeff l := by
    rw [creationProduct_coeff, creationProduct_coeff, mul_comm]
  simp only [mul_assoc, coverMonomial_mul_coeff, one_mul]
  apply coverEval_mul_coeff_swap
  intro i j
  simpa only [mul_comm (creationProduct B a b), mul_comm (creationProduct B b a)] using
    coverEval_mul_coeff_swap (RingHom.id Fock) (-1, 0) (0, -1)
      (finiteChargedTranslation B a b P) h i j

/-- The maximum of the three pole orders of the scalar contraction. -/
abbrev chargedLocalityOrder (a b : Charge lattice) : ℕ :=
  contractionLocalityOrder lattice g a b

private abbrev orbitExponent (a b : Charge lattice) (j : ℕ) : ℤ :=
  contractionOrbitExponent lattice g a b j

private theorem orbitExponent_zero_swap (a b : Charge lattice) :
    orbitExponent b a 0 = orbitExponent a b 0 :=
  bilinear_symmetric lattice b a

private theorem orbitExponent_one_swap (a b : Charge lattice) :
    orbitExponent b a 1 = orbitExponent a b 2 := by
  change bilinear lattice (g b) a = bilinear lattice (g (g a)) b
  rw [bilinear_symmetric lattice (g b) a]
  simpa only [g_cube a] using g_isometry (g (g a)) b

private theorem orbitExponent_two_swap (a b : Charge lattice) :
    orbitExponent b a 2 = orbitExponent a b 1 :=
  (orbitExponent_one_swap b a).symm

private theorem localityOrder_reverse_nonneg (a b : Charge lattice) (j : ℕ)
    (hj : j ∈ Finset.range 3) :
    0 ≤ (chargedLocalityOrder a b : ℤ) + orbitExponent b a j := by
  have hj' : j < 3 := Finset.mem_range.mp hj
  interval_cases j
  · rw [orbitExponent_zero_swap]
    exact contractionLocalityOrder_add_nonneg lattice g a b (by decide)
  · rw [orbitExponent_one_swap]
    exact contractionLocalityOrder_add_nonneg lattice g a b (by decide)
  · rw [orbitExponent_two_swap]
    exact contractionLocalityOrder_add_nonneg lattice g a b (by decide)

private def negUnit : ℂˣ := Units.mk0 (-1) (neg_ne_zero.mpr one_ne_zero)

private def flipUnit (j : ℕ) : ℂˣ := negUnit * ζ ^ j

private theorem prod_flipUnit : (∏ j ∈ Finset.range 3, flipUnit j) = negUnit := by
  have hsign : negUnit * negUnit = 1 := by
    apply Units.ext
    change (-1 : ℂ) * (-1) = 1
    ring
  simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul, flipUnit, pow_zero,
    pow_one, mul_one]
  calc
    _ = negUnit * (negUnit * negUnit) * ζ ^ 3 := by rw [pow_succ ζ 2]; ac_rfl
    _ = negUnit := by rw [hsign, ThirdTwistedChargeCocycle.zeta_primitive.pow_eq_one,
      mul_one, mul_one]

private theorem clearedNumerator_exchange {R : Type*} [CommRing R]
    (C : ℂ →+* R) (x y : R) (a b : Charge lattice) (N : ℕ)
    (hN : ∀ j ∈ Finset.range 3, 0 ≤ (N : ℤ) + orbitExponent a b j) :
    MvPolynomial.eval₂Hom C ![x, y] (clearedContractionNumerator lattice g ζ a b N) =
      ((-1 : R) ^ N * C (reciprocityPhase lattice g ζ a b : ℂ)) *
        MvPolynomial.eval₂Hom C ![y, x] (clearedContractionNumerator lattice g ζ b a N) := by
  let powIndex (j : ℕ) := ((N : ℤ) + orbitExponent a b j).toNat
  have hζ : ζ ^ (3 : ℕ) = 1 := ThirdTwistedChargeCocycle.zeta_primitive.pow_eq_one
  have hinv : ζ⁻¹ = ζ ^ (2 : ℕ) := by
    symm
    apply eq_inv_of_mul_eq_one_left
    rw [← pow_succ, hζ]
  have hinvSq : (ζ⁻¹) ^ (2 : ℕ) = ζ := by
    calc
      (ζ⁻¹) ^ (2 : ℕ) = (ζ ^ (2 : ℕ)) ^ (2 : ℕ) := by rw [← hinv]
      _ = ζ ^ (3 + 1 : ℕ) := by rw [← pow_mul]
      _ = ζ := by rw [pow_succ, hζ, one_mul]
  have hflip (j : ℕ) :
      x - C (↑(ζ ^ j) : ℂ) * y =
        C (flipUnit j : ℂ) * (y - C (↑(ζ⁻¹ ^ j) : ℂ) * x) := by
    have hunit : C (↑(ζ ^ j) : ℂ) * C (↑(ζ⁻¹ ^ j) : ℂ) = 1 := by
      rw [inv_pow ζ j, ← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one]
    have hcancel :
        C (↑(ζ ^ j) : ℂ) * (C (↑(ζ⁻¹ ^ j) : ℂ) * x) = x := by
      rw [← mul_assoc, hunit, one_mul]
    change _ = C ((-1 : ℂ) * (↑(ζ ^ j) : ℂ)) * _
    rw [neg_one_mul, map_neg, mul_sub, neg_mul, neg_mul, hcancel]
    ring
  have hpow (j : ℕ) (hj : j ∈ Finset.range 3) :
      flipUnit j ^ powIndex j = flipUnit j ^ N * flipUnit j ^ orbitExponent a b j := by
    calc
      _ = flipUnit j ^ ((N : ℤ) + orbitExponent a b j) := by
        rw [← zpow_natCast (flipUnit j) (powIndex j)]
        dsimp only [powIndex]
        rw [Int.toNat_of_nonneg (hN j hj)]
      _ = _ := by rw [zpow_add, zpow_natCast]
  have hphaseUnits :
      (∏ j ∈ Finset.range 3, flipUnit j ^ powIndex j) =
        negUnit ^ N * reciprocityPhase lattice g ζ a b := by
    calc
      _ = ∏ j ∈ Finset.range 3, (flipUnit j ^ N * flipUnit j ^ orbitExponent a b j) :=
        Finset.prod_congr rfl hpow
      _ = _ := by
        rw [Finset.prod_mul_distrib, Finset.prod_pow, prod_flipUnit]
        rfl
  have hphase :
      (∏ j ∈ Finset.range 3, C (flipUnit j : ℂ) ^ powIndex j) =
        (-1 : R) ^ N * C (reciprocityPhase lattice g ζ a b : ℂ) := by
    simpa only [Units.coe_prod, Units.val_pow_eq_pow_val, Units.val_mul,
      negUnit, Units.val_mk0, map_prod, map_pow, map_mul, map_neg, map_one]
      using congrArg (fun u : ℂˣ => C (u : ℂ)) hphaseUnits
  have hreverse :
      (∏ j ∈ Finset.range 3, (y - C (↑(ζ⁻¹ ^ j) : ℂ) * x) ^ powIndex j) =
        MvPolynomial.eval₂Hom C ![y, x] (clearedContractionNumerator lattice g ζ b a N) := by
    rw [clearedContractionNumerator_eval]
    simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul, powIndex, pow_zero,
      pow_one, orbitExponent_zero_swap a b, orbitExponent_one_swap a b,
      orbitExponent_two_swap a b]
    rw [hinvSq, hinv]
    ac_rfl
  calc
    _ = ∏ j ∈ Finset.range 3, (x - C (↑(ζ ^ j) : ℂ) * y) ^ powIndex j :=
      clearedContractionNumerator_eval lattice g C x y ζ a b N
    _ = _ := by
      simp only [hflip, mul_pow, Finset.prod_mul_distrib, hphase, hreverse]

private def coverRatio : PowerSeries ℂ →+* XY := yExpansion.comp atCoverRatio

private theorem coverRatio_C :
    coverRatio.comp PowerSeries.C = coverC.comp (algebraMap ℂ Fock) := by
  apply RingHom.ext
  intro c
  have h : atCoverRatio (PowerSeries.C c) =
      PowerSeries.C (Polynomial.C (algebraMap ℂ Fock c)) := by
    apply PowerSeries.ext
    intro n
    cases n with
    | zero => simp only [coeff_atCoverRatio, PowerSeries.coeff_C, ite_true, pow_zero, one_mul,
        Polynomial.algebraMap_apply]
    | succ n => simp [coeff_atCoverRatio]
  change yExpansion (atCoverRatio (PowerSeries.C c)) = _
  rw [h, yExpansion_eq, PowerSeries.map_C, inverseEval_C, HahnSeries.ofPowerSeries_C]
  rfl

private theorem coverRatio_X :
    coverRatio PowerSeries.X = coverMonomial (-1) 1 (1 : Fock) := by
  change yExpansion ((PowerSeries.rescale _)
    (PowerSeries.map (algebraMap ℂ (Polynomial Fock)) PowerSeries.X)) = _
  rw [PowerSeries.map_X, PowerSeries.rescale_X, map_mul, yExpansion_eq, yExpansion_eq,
    PowerSeries.map_C, PowerSeries.map_X, inverseEval_X, HahnSeries.ofPowerSeries_C,
    HahnSeries.ofPowerSeries_X, HahnSeries.C_apply, HahnSeries.single_mul_single,
    zero_add, mul_one]
  rfl

private theorem coverRatio_contraction (a b : Charge lattice) :
    coverRatio (↑(∏ j ∈ Finset.range 3, ThirdTwistedContraction.binomialUnit
      (↑(ζ ^ j) : ℂ) ^ orbitExponent a b j) : PowerSeries ℂ) = orderedContraction a b := by
  simp only [coverRatio, RingHom.comp_apply, Units.val_pow_eq_pow_val, orderedContraction]

/-- The locality multiplier as a finite polynomial in the physical cover variables. -/
def chargedLocalityPolynomial (N : ℕ) : MvPolynomial (Fin 2) ℂ :=
  (MvPolynomial.X 0 ^ 3 - MvPolynomial.X 1 ^ 3) ^ N

private theorem localityPolynomial_eval (v w : ℤ × ℤ) (N : ℕ) :
    coverEval (algebraMap ℂ Fock) v w (chargedLocalityPolynomial N) =
      (coverMonomial v.1 v.2 (1 : Fock) ^ 3 - coverMonomial w.1 w.2 1 ^ 3) ^ N := by
  simp only [chargedLocalityPolynomial, coverEval, map_pow, map_sub, MvPolynomial.eval₂Hom_X',
    Matrix.cons_val_zero, Matrix.cons_val_one]

private def groundScalar (a b : Charge lattice) (p : Momentum) : ℂ :=
  (c₃ a b : ℂ) * chargePhase (a + b) p

/-- The common finite numerator after removing the momentum monomial. -/
def chargedLocalityNumerator (a b : Charge lattice) (p : Momentum) (N : ℕ) :
    MvPolynomial (Fin 2) ℂ :=
  MvPolynomial.C (groundScalar a b p) * clearedContractionNumerator lattice g ζ a b N

private theorem groundScalar_exchange (a b : Charge lattice) (p : Momentum) :
    groundScalar a b p * (reciprocityPhase lattice g ζ a b : ℂ) = groundScalar b a p := by
  have h := congrArg (fun u : ℂˣ => (u : ℂ))
    (ThirdTwistedChargeCocycle.c_mul_reciprocityPhase lattice g g_cube g_isometry a b)
  change (c₃ a b : ℂ) * (reciprocityPhase lattice g ζ a b : ℂ) = (c₃ b a : ℂ) at h
  rw [groundScalar, groundScalar, add_comm b a, mul_right_comm, h]

private theorem chargedLocalityNumerator_eval_swap (a b : Charge lattice)
    (p : Momentum) (N : ℕ)
    (hN : ∀ j ∈ Finset.range 3, 0 ≤ (N : ℤ) + orbitExponent a b j) :
    coverEval (algebraMap ℂ Fock) (0, 1) (1, 0) (chargedLocalityNumerator a b p N) =
      (-1 : XY) ^ N *
        coverEval (algebraMap ℂ Fock) (1, 0) (0, 1) (chargedLocalityNumerator b a p N) := by
  let C : ℂ →+* XY := coverC.comp (algebraMap ℂ Fock)
  have phase := congrArg C (groundScalar_exchange a b p)
  rw [map_mul] at phase
  simp only [chargedLocalityNumerator, coverEval, map_mul, MvPolynomial.eval₂Hom_C]
  change C (groundScalar a b p) * MvPolynomial.eval₂Hom C ![𝕐, 𝕏]
      (clearedContractionNumerator lattice g ζ a b N) =
    (-1 : XY) ^ N * (C (groundScalar b a p) * MvPolynomial.eval₂Hom C ![𝕏, 𝕐]
      (clearedContractionNumerator lattice g ζ b a N))
  rw [clearedNumerator_exchange C 𝕐 𝕏 a b N hN, ← phase]
  simp only [← mul_assoc]
  rw [mul_comm (C (groundScalar a b p)) ((-1 : XY) ^ N)]

private theorem group_clearing_factors {R : Type*} [CommMonoid R]
    (multiplier momentum scalar orbit contraction first second translation : R) :
    multiplier * (momentum * scalar * orbit * contraction * first * second * translation) =
      momentum * (scalar * (multiplier * (orbit * contraction))) *
        (first * second) * translation := by
  ac_rfl

private theorem chargedLocalityNumerator_eval (a b : Charge lattice)
    (p : Momentum) (N : ℕ) :
    coverEval (algebraMap ℂ Fock) (1, 0) (0, 1) (chargedLocalityNumerator a b p N) =
      coverC (algebraMap ℂ Fock (groundScalar a b p)) *
        coverEval (algebraMap ℂ Fock) (1, 0) (0, 1)
          (clearedContractionNumerator lattice g ζ a b N) := by
  simp only [chargedLocalityNumerator, coverEval, map_mul, MvPolynomial.eval₂Hom_C,
    RingHom.comp_apply]

open Classical in
/-- On the shifted momentum line the forward radial expansion clears to the
finite numerator followed by the two creation series and the finite translation. -/
private theorem clearedOrderedProduct_single (B : FixedDualBases) (a b : Charge lattice)
    (p q : Momentum) (P : Fock) (N : ℕ)
    (hN : ∀ j ∈ Finset.range 3, 0 ≤ (N : ℤ) + orbitExponent a b j) :
    (𝕏 ^ 3 - 𝕐 ^ 3) ^ N * orderedChargedProduct B a b (Finsupp.single p P) q =
      if shift (a + b) p = q then
        coverMonomial (momentumExponent a p) (momentumExponent b p) (1 : Fock) *
          coverEval (algebraMap ℂ Fock) (1, 0) (0, 1) (chargedLocalityNumerator a b p N) *
          creationProduct B a b *
          inverseCover₂ (translateOuter B b (translatedPolynomial B a P))
      else 0 := by
  rw [orderedChargedProduct_single, Finsupp.single_apply]
  split_ifs with hq
  · let t := ∑ j ∈ Finset.range 3, orbitExponent a b j
    have ht : t = bilinear lattice (ThirdTwistedChargeAction.N lattice g a) b :=
      sum_orbitPairing lattice g a b
    have hd :
        momentumExponent (a + b) p + 3 * bilinear lattice a b - momentumExponent b p =
          momentumExponent a p + t := by
      rw [ht, ← momentumExponent_shift_eq_add_normPairing,
        momentumExponent_shift_eq_ordered_degree]
    let u : XYˣ := coverUnit 1 0
    have hu : (u : XY) * coverRatio PowerSeries.X = 𝕐 := by
      rw [coverRatio_X]
      change 𝕏 * coverMonomial (-1) 1 (1 : Fock) = _
      rw [coverMonomial_mul]
      norm_num
    have hclear := ThirdTwistedContraction.binomialContraction_clear_homogeneous
      lattice g coverRatio u 𝕐 hu ζ ThirdTwistedChargeCocycle.zeta_primitive a b N hN
    have hx : (u : XY) = 𝕏 := rfl
    rw [coverRatio_C, coverRatio_contraction, hx] at hclear
    have hm : (↑(u ^ t) : XY) = coverMonomial t 0 (1 : Fock) := by
      simp only [u, coverUnit_zpow, mul_one, mul_zero]
    have hmon :
        coverMonomial (momentumExponent a p) (momentumExponent b p) (1 : Fock) *
          coverC (algebraMap ℂ Fock (groundScalar a b p)) * (↑(u ^ t) : XY) =
        coverMonomial (momentumExponent a p + t) (momentumExponent b p)
          (algebraMap ℂ Fock (groundScalar a b p)) := by
      rw [hm]
      change _ * coverMonomial 0 0 (algebraMap ℂ Fock (groundScalar a b p)) * _ = _
      simp only [coverMonomial_mul, add_zero, one_mul, mul_one]
    rw [hd]
    change (𝕏 ^ 3 - 𝕐 ^ 3) ^ N *
        (coverMonomial (momentumExponent a p + t) (momentumExponent b p)
          (algebraMap ℂ Fock (groundScalar a b p)) * orderedContraction a b *
          HahnSeries.C (HahnSeries.ofPowerSeries ℤ Fock (creationExponential B a)) *
          yExpansion (PowerSeries.mapAlgHom polyC (creationExponential B b)) *
          inverseCover₂ (translateOuter B b (translatedPolynomial B a P))) = _
    rw [← hmon]
    calc
      _ = coverMonomial (momentumExponent a p) (momentumExponent b p) (1 : Fock) *
          (coverC (algebraMap ℂ Fock (groundScalar a b p)) *
            ((𝕏 ^ 3 - 𝕐 ^ 3) ^ N * ((↑(u ^ t) : XY) * orderedContraction a b))) *
          creationProduct B a b *
          inverseCover₂ (translateOuter B b (translatedPolynomial B a P)) := by
        exact group_clearing_factors (R := XY) _ _ _ _ _ _ _ _
      _ = _ := by
        rw [hclear, chargedLocalityNumerator_eval, coverEval]
  · rw [mul_zero]

/-- The same physical multiplier `(x³ - y³)^N` clears both ordered products.
After clearing, extraction of the two physical cover degrees commutes with
exchange of radial order on every input and output momentum line. -/
theorem clearedOrderedChargedProduct_coeff_swap (B : FixedDualBases)
    (a b : Charge lattice) (p q : Momentum) (P : Fock) (k l : ℤ) :
    (((𝕏 ^ 3 - 𝕐 ^ 3) ^ chargedLocalityOrder a b *
      orderedChargedProduct B a b (Finsupp.single p P) q).coeff l).coeff k =
    (((𝕐 ^ 3 - 𝕏 ^ 3) ^ chargedLocalityOrder a b *
      orderedChargedProduct B b a (Finsupp.single p P) q).coeff k).coeff l := by
  classical
  let N := chargedLocalityOrder a b
  have hN : ∀ j ∈ Finset.range 3, 0 ≤ (N : ℤ) + orbitExponent a b j :=
    fun _ hj => contractionLocalityOrder_add_nonneg lattice g a b hj
  have hf := clearedOrderedProduct_single B a b p q P N hN
  have hr := clearedOrderedProduct_single B b a p q P N (localityOrder_reverse_nonneg a b)
  have hsign : (𝕐 ^ 3 - 𝕏 ^ 3) ^ N = (-1 : XY) ^ N * (𝕏 ^ 3 - 𝕐 ^ 3) ^ N := by
    rw [show 𝕐 ^ 3 - 𝕏 ^ 3 = (-1 : XY) * (𝕏 ^ 3 - 𝕐 ^ 3) by ring]
    exact mul_pow (-1 : XY) (𝕏 ^ 3 - 𝕐 ^ 3) N
  change ((((𝕏 ^ 3 - 𝕐 ^ 3) ^ N *
    orderedChargedProduct B a b (Finsupp.single p P) q).coeff l).coeff k) = _
  by_cases hq : shift (a + b) p = q
  · have hq' : shift (b + a) p = q := by simpa only [add_comm b a] using hq
    rw [ite_eq_left hq] at hf
    rw [ite_eq_left hq'] at hr
    have hreversed :
        (𝕐 ^ 3 - 𝕏 ^ 3) ^ N * orderedChargedProduct B b a (Finsupp.single p P) q =
          coverMonomial (momentumExponent b p) (momentumExponent a p) (1 : Fock) *
            coverEval (algebraMap ℂ Fock) (0, 1) (1, 0) (chargedLocalityNumerator a b p N) *
            creationProduct B b a *
            inverseCover₂ (translateOuter B a (translatedPolynomial B b P)) := by
      rw [hsign, mul_assoc, hr, chargedLocalityNumerator_eval_swap a b p N hN]
      simp only [← mul_assoc]
      rw [mul_comm ((-1 : XY) ^ N)
        (coverMonomial (momentumExponent b p) (momentumExponent a p) (1 : Fock))]
    rw [hf, hreversed]
    exact normalOrdered_coeff_swap B a b P (chargedLocalityNumerator a b p N)
      (momentumExponent a p) (momentumExponent b p) k l
  · have hq' : shift (b + a) p ≠ q := by simpa only [add_comm b a] using hq
    rw [ite_eq_right hq] at hf
    rw [ite_eq_right hq'] at hr
    rw [hf, hsign, mul_assoc, hr, mul_zero]
    simp

private theorem orderedChargedProduct_coeff_apply (B : FixedDualBases)
    (a b : Charge lattice) (v : State) (q : Momentum) (k l : ℤ) :
    ((orderedChargedProduct B a b v q).coeff l).coeff k =
      (fieldCoeff B a k (fieldCoeff B b l v)) q := by
  have h := congrArg (fun T : State →ₗ[ℂ] State => T v q)
    (orderedChargedProduct_coeff B a b k l)
  simpa only [LinearMap.comp_apply, Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_apply,
    HahnSeries.coeff.linearMap_apply, AddMonoidHom.toFun_eq_coe,
    HahnSeries.coeff.addMonoidHom_apply] using h

/-- Pairwise locality of the two actual charged fields of charges `a` and `b`.
The displayed finite sum is the `(k,l)` coefficient of their commutator
multiplied by `(x³ - y³)^N`, with `N` the largest scalar pole order. -/
theorem fieldCoeff_pairwise_locality (B : FixedDualBases) (a b : Charge lattice) (k l : ℤ) :
    let Q := chargedLocalityPolynomial (chargedLocalityOrder a b)
    ∑ d ∈ Q.support, Q.coeff d •
      ((fieldCoeff B a (k - (d 0 : ℤ))).comp (fieldCoeff B b (l - (d 1 : ℤ))) -
       (fieldCoeff B b (l - (d 1 : ℤ))).comp (fieldCoeff B a (k - (d 0 : ℤ)))) =
      (0 : Module.End ℂ State) := by
  let Q := chargedLocalityPolynomial (chargedLocalityOrder a b)
  dsimp only
  apply Finsupp.lhom_ext
  intro p P
  apply Finsupp.ext
  intro q
  have h := clearedOrderedChargedProduct_coeff_swap B a b p q P k l
  have hx : coverEval (algebraMap ℂ Fock) (1, 0) (0, 1) Q =
      (𝕏 ^ 3 - 𝕐 ^ 3) ^ chargedLocalityOrder a b :=
    localityPolynomial_eval (1, 0) (0, 1) _
  have hy : coverEval (algebraMap ℂ Fock) (0, 1) (1, 0) Q =
      (𝕐 ^ 3 - 𝕏 ^ 3) ^ chargedLocalityOrder a b :=
    localityPolynomial_eval (0, 1) (1, 0) _
  rw [← hx, ← hy, coverEval_mul_coeff, coverEval_mul_coeff] at h
  simp only [mul_one, mul_zero, zero_add, add_zero, orderedChargedProduct_coeff_apply] at h
  simp only [LinearMap.sum_apply, LinearMap.zero_apply]
  change (Finsupp.lapply q : State →ₗ[ℂ] Fock) (∑ d ∈ Q.support, _) =
    (Finsupp.lapply q : State →ₗ[ℂ] Fock) 0
  rw [map_sum, map_zero]
  simp only [LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.comp_apply,
    Finsupp.lapply_apply, Finsupp.smul_apply, Finsupp.sub_apply]
  simp only [Algebra.smul_def, mul_sub, Finset.sum_sub_distrib]
  exact sub_eq_zero.mpr h

end

end D5.S3.VertexAlgebra.Lattice.Orbifold.P48qThirdTwistedField

#print axioms D5.S3.VertexAlgebra.Lattice.Orbifold.P48qThirdTwistedField.fieldCoeff_pairwise_locality
