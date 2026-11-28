/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/P48qChargedOrderedProduct
   generality: I
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The radial ordered product with the right cover variable outermost. -/

import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qChargedExponentialReordering
import Mathlib.RingTheory.LaurentSeries

/-!
The ordered product of the native charged fields, with the right cover coordinate
`y` outermost. The expansion of the contraction is in `y/x`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48qThirdTwistedField

open LatticeGeneratingFieldLocality (Charge bilinear)
open LatticeActualGeneratorLocality (bilinear_add_right)
open LatticeFiniteNegativeGeneration (bilinear_symmetric)
open P48qTwistedChargeAction (lattice g g_cube g_isometry Momentum U U_comp_single)
open HahnSeries (single)
open scoped BigOperators

noncomputable section

local notation "shift" => ThirdTwistedChargeAction.shift lattice g
local notation "N" => ThirdTwistedChargeAction.N lattice g
local notation "c₃" => ThirdTwistedChargeCocycle.c lattice g

private theorem U_single_mul (a : Charge lattice) (p : Momentum) (z : ℂ) :
    U a (Finsupp.single p z) = Finsupp.single (shift a p) (z * chargePhase a p) := by
  have hz : Finsupp.single p z = z • Finsupp.single p (1 : ℂ) := by
    simp only [Finsupp.smul_single, smul_eq_mul, mul_one]
  rw [hz, map_smul, U_ground, Finsupp.smul_single, smul_eq_mul]

/-- The scalar on the twice-shifted ground line is the native BK multiplier
times the scalar for the sum charge. -/
theorem chargePhase_ordered (a b : Charge lattice) (p : Momentum) :
    chargePhase a (shift b p) * chargePhase b p =
      (c₃ a b : ℂ) * chargePhase (a + b) p := by
  have h := U_comp_single a b p 1
  rw [U_ground b, U_single_mul, ThirdTwistedChargeAction.shift_add,
    U_ground (a + b), Finsupp.smul_single] at h
  simpa only [Finsupp.single_eq_same, smul_eq_mul,
    mul_comm (chargePhase b p) (chargePhase a (shift b p))] using
    congrArg (fun v : P48qTwistedChargeAction.Ground => v (shift (a + b) p)) h

/-- The right charge raises the left cover degree by the norm-orbit pairing. -/
theorem momentumExponent_shift (a b : Charge lattice) (p : Momentum) :
    momentumExponent a (shift b p) = momentumExponent a p + bilinear lattice (N a) b := by
  have hnorm : bilinear lattice a (N b) = bilinear lattice (N a) b :=
    (ThirdTwistedChargeAction.norm_pairing lattice g g_cube g_isometry a b).symm
  simp only [momentumExponent, shift_numerator, bilinear_add_right, hnorm, add_assoc]

/-- The total cover degree differs from the degree of the sum charge by
three times the integral pairing. -/
theorem momentumExponent_ordered (a b : Charge lattice) (p : Momentum) :
    momentumExponent a (shift b p) + momentumExponent b p =
      momentumExponent (a + b) p + 3 * bilinear lattice a b := by
  have hadd : bilinear lattice (a + b) p.1 =
      bilinear lattice a p.1 + bilinear lattice b p.1 := by
    rw [bilinear_symmetric lattice (a + b) p.1, bilinear_add_right,
      bilinear_symmetric lattice p.1 a, bilinear_symmetric lattice p.1 b]
  have hq := ThirdTwistedChargeAction.q_polarization lattice g g_cube g_isometry a b
  rw [momentumExponent_shift]
  simp only [momentumExponent, hadd]
  omega

local notation "polyC" => (Polynomial.CAlgHom : Fock →ₐ[ℂ] Polynomial Fock)

/-- Extend the `y` translation to polynomials in `x⁻¹`, keeping `x⁻¹` fixed.
The outer polynomial variable in the target is `y⁻¹`. -/
def translateOuter (B : FixedDualBases) (b : Charge lattice) :
    Polynomial Fock →ₐ[ℂ] Polynomial (Polynomial Fock) :=
  Polynomial.aevalTower ((Polynomial.mapAlgHom polyC).comp (translatedPolynomial B b))
    (Polynomial.C Polynomial.X)

private theorem translateOuter_C (B : FixedDualBases) (b : Charge lattice) (P : Fock) :
    translateOuter B b (Polynomial.C P) =
      Polynomial.mapAlgHom polyC (translatedPolynomial B b P) :=
  Polynomial.aevalTower_C _ _ _

private theorem translateOuter_X (B : FixedDualBases) (b : Charge lattice) :
    translateOuter B b Polynomial.X = Polynomial.C Polynomial.X :=
  Polynomial.aevalTower_X _ _

private theorem translatedPolynomial_generator
    (B : FixedDualBases) (a : Charge lattice) (j : Mode) :
    translatedPolynomial B a (MvPolynomial.X j) =
      Polynomial.C (MvPolynomial.X j) -
        Polynomial.C (algebraMap ℂ Fock (annihilationPairing B a j)) *
          Polynomial.X ^ frequency j := by
  rw [translatedPolynomial, MvPolynomial.aeval_X, translationVariable, Algebra.smul_def, mul_one]

/-- The two native finite substitutions commute in the two inverse cover
variables. The left side translates the coefficients of the `y⁻¹` polynomial. -/
theorem translatedPolynomial_commute (B : FixedDualBases) (a b : Charge lattice) :
    (Polynomial.mapAlgHom (translatedPolynomial B a)).comp (translatedPolynomial B b) =
      (translateOuter B b).comp (translatedPolynomial B a) := by
  apply MvPolynomial.algHom_ext
  intro j
  simp only [AlgHom.comp_apply, translatedPolynomial_generator, map_sub, map_mul, map_pow,
    translateOuter_C, translateOuter_X, Polynomial.coe_mapAlgHom, Polynomial.map_C,
    Polynomial.map_X, AlgHom.coe_toRingHom, Polynomial.CAlgHom_apply, AlgHom.commutes,
    Polynomial.algebraMap_apply]
  ring

private abbrev XSeries := LaurentSeries Fock
private abbrev XYSeries := LaurentSeries XSeries

-- Use the coefficientwise scalar action for both Laurent variables.
attribute [local instance 2000] HahnSeries.instAlgebra

/-- Multiplication in the two-variable Laurent ring is complex-linear. -/
local instance : SMulCommClass ℂ XYSeries XYSeries :=
  Algebra.to_smulCommClass (R := ℂ) (A := XYSeries)

/-- Evaluate a finite inverse-coordinate polynomial at the inverse Laurent monomial. -/
private def inverseCover (K : Type*) {R : Type*} [CommSemiring K] [CommRing R] [Algebra K R] :
    Polynomial R →ₐ[K] LaurentSeries R :=
  Polynomial.aevalTower
    ({ toRingHom := HahnSeries.C, commutes' := fun _ => rfl } : R →ₐ[K] LaurentSeries R)
    (single (-1 : ℤ) 1)

/-- Evaluate the inner polynomial variable at `x⁻¹` and the outer one at `y⁻¹`. -/
def inverseCover₂ : Polynomial (Polynomial Fock) →ₐ[ℂ] LaurentSeries (LaurentSeries Fock) :=
  (inverseCover ℂ (R := XSeries)).comp (Polynomial.mapAlgHom (inverseCover ℂ (R := Fock)))

/-- Embed a power series in `y` with polynomial coefficients in `x⁻¹`
into the ordered Laurent series ring. -/
def yExpansion : PowerSeries (Polynomial Fock) →+* LaurentSeries (LaurentSeries Fock) :=
  (HahnSeries.ofPowerSeries ℤ XSeries).comp
    (PowerSeries.map (inverseCover ℂ (R := Fock)).toRingHom)

private theorem coeff_mul_inverseCover (K : Type*) {R S : Type*}
    [CommSemiring K] [CommRing R] [CommRing S] [Algebra K S]
    (f : R →+* S) (A : LaurentSeries S) (P : Polynomial R) (k : ℤ) :
    (A * inverseCover K (P.map f)).coeff k =
      ∑ d ∈ P.support, A.coeff (k + (d : ℤ)) * f (P.coeff d) := by
  change (A * (P.map f).eval₂ HahnSeries.C (single (-1 : ℤ) 1)).coeff k = _
  rw [Polynomial.eval₂_map, Polynomial.eval₂_eq_sum, Polynomial.sum_def, Finset.mul_sum,
    HahnSeries.coeff_sum]
  apply Finset.sum_congr rfl
  intro d _
  have hpow : (single (-1 : ℤ) (1 : S)) ^ d = single (-(d : ℤ)) 1 := by
    rw [HahnSeries.single_pow, one_pow]
    congr 1
    simp
  rw [RingHom.comp_apply, HahnSeries.C_apply, hpow, HahnSeries.single_mul_single, zero_add,
    mul_one, HahnSeries.coeff_mul_single, sub_neg_eq_add]

private theorem coeff_ofPowerSeries_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (A : PowerSeries R) (k : ℤ) :
    (HahnSeries.ofPowerSeries ℤ S (A.map f)).coeff k =
      f ((HahnSeries.ofPowerSeries ℤ R A).coeff k) := by
  change ((A.map f : PowerSeries S) : LaurentSeries S).coeff k =
    f ((A : LaurentSeries R).coeff k)
  simp only [PowerSeries.coeff_coe]
  split_ifs <;> simp only [map_zero, PowerSeries.coeff_map]

private theorem coeff_creation_laurent (B : FixedDualBases) (a : Charge lattice) (k : ℤ) :
    (HahnSeries.ofPowerSeries ℤ Fock (creationExponential B a)).coeff k =
      creationCoeff B a k := by
  change ((creationExponential B a : PowerSeries Fock) : XSeries).coeff k = _
  rw [PowerSeries.coeff_coe, creationCoeff]
  cases k with
  | ofNat n =>
    simp only [Int.ofNat_eq_natCast, if_neg (Int.natCast_nonneg n).not_gt,
      Int.natAbs_natCast, Int.toNat_natCast]
  | negSucc n => simp only [Int.negSucc_lt_zero, if_true]

private theorem oscillatorCoeff_laurent
    (B : FixedDualBases) (a : Charge lattice) (P : Fock) (k : ℤ) :
    (HahnSeries.ofPowerSeries ℤ Fock (creationExponential B a) *
      inverseCover ℂ (translatedPolynomial B a P)).coeff k = oscillatorCoeff B a k P := by
  simpa only [Polynomial.map_id, RingHom.id_apply, coeff_creation_laurent, oscillatorCoeff_apply]
    using (coeff_mul_inverseCover ℂ (RingHom.id Fock)
      (HahnSeries.ofPowerSeries ℤ Fock (creationExponential B a))
      (translatedPolynomial B a P) k)

private theorem coeff_translated_right_field
    (B : FixedDualBases) (a b : Charge lattice) (P : Fock) (l : ℤ) :
    (yExpansion (PowerSeries.mapAlgHom (translatedPolynomial B a) (creationExponential B b)) *
      inverseCover₂ (Polynomial.mapAlgHom (translatedPolynomial B a)
        (translatedPolynomial B b P))).coeff l =
      inverseCover ℂ (translatedPolynomial B a (oscillatorCoeff B b l P)) := by
  let f : Fock →+* XSeries :=
    (inverseCover ℂ (R := Fock)).toRingHom.comp (translatedPolynomial B a).toRingHom
  change (HahnSeries.ofPowerSeries ℤ XSeries
      (((creationExponential B b).map (translatedPolynomial B a).toRingHom).map
        (inverseCover ℂ (R := Fock)).toRingHom) *
      inverseCover ℂ (((translatedPolynomial B b P).map (translatedPolynomial B a).toRingHom).map
        (inverseCover ℂ (R := Fock)).toRingHom)).coeff l = f (oscillatorCoeff B b l P)
  rw [Polynomial.map_map]
  change (HahnSeries.ofPowerSeries ℤ XSeries ((creationExponential B b).map f) *
    inverseCover ℂ ((translatedPolynomial B b P).map f)).coeff l = f (oscillatorCoeff B b l P)
  rw [coeff_mul_inverseCover ℂ, oscillatorCoeff_apply, map_sum]
  apply Finset.sum_congr rfl
  intro d _
  rw [coeff_ofPowerSeries_map, coeff_creation_laurent, map_mul]

private def orderedOscillator (B : FixedDualBases) (a b : Charge lattice) :
    Fock →ₗ[ℂ] XYSeries :=
  (LinearMap.mulLeft ℂ
    (HahnSeries.C (HahnSeries.ofPowerSeries ℤ Fock (creationExponential B a)) *
      yExpansion (PowerSeries.mapAlgHom (translatedPolynomial B a) (creationExponential B b)))).comp
    (inverseCover₂.comp ((Polynomial.mapAlgHom (translatedPolynomial B a)).comp
      (translatedPolynomial B b))).toLinearMap

private theorem orderedOscillator_coeff
    (B : FixedDualBases) (a b : Charge lattice) (P : Fock) (k l : ℤ) :
    ((orderedOscillator B a b P).coeff l).coeff k =
      oscillatorCoeff B a k (oscillatorCoeff B b l P) := by
  simp only [orderedOscillator, LinearMap.comp_apply, LinearMap.mulLeft_apply,
    AlgHom.toLinearMap_apply, AlgHom.comp_apply, mul_assoc, HahnSeries.C_apply,
    HahnSeries.coeff_single_zero_mul, coeff_translated_right_field, oscillatorCoeff_laurent]

/-- The ordered native field product on the finite state space, with a Laurent
expansion in `y` whose coefficients are Laurent series in `x`. -/
def orderedChargedProduct (B : FixedDualBases) (a b : Charge lattice) :
    State →ₗ[ℂ] (Momentum →₀ LaurentSeries (LaurentSeries Fock)) :=
  Finsupp.lsum ℂ fun p => (Finsupp.lsingle (shift a (shift b p))).comp
    ((LinearMap.mulLeft ℂ
      (single (momentumExponent b p)
        (single (momentumExponent a (shift b p))
          (algebraMap ℂ Fock (chargePhase a (shift b p) * chargePhase b p))))).comp
      (orderedOscillator B a b))

/-- Reading either cover degree recovers the corresponding composition
of the actual state-valued field modes. -/
theorem orderedChargedProduct_coeff
    (B : FixedDualBases) (a b : Charge lattice) (k l : ℤ) :
    (Finsupp.mapRange.linearMap
      ((HahnSeries.coeff.linearMap (R := ℂ) k).comp (HahnSeries.coeff.linearMap (R := ℂ) l))).comp
      (orderedChargedProduct B a b) = (fieldCoeff B a k).comp (fieldCoeff B b l) := by
  apply Finsupp.lhom_ext
  intro p P
  simp only [LinearMap.comp_apply, orderedChargedProduct, Finsupp.lsum_single,
    Finsupp.lsingle_apply, Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single,
    LinearMap.mulLeft_apply, HahnSeries.coeff.linearMap_apply, fieldCoeff_single,
    map_smul, smul_smul]
  simp only [AddMonoidHom.toFun_eq_coe, HahnSeries.coeff.addMonoidHom_apply]
  rw [HahnSeries.coeff_single_mul, HahnSeries.coeff_single_mul,
    orderedOscillator_coeff, Algebra.smul_def]

/-- The native BK contraction, expanded in the right cover variable divided by the left. -/
def orderedContraction (a b : Charge lattice) : LaurentSeries (LaurentSeries Fock) :=
  yExpansion (atCoverRatio
    (↑(∏ j ∈ Finset.range 3, ThirdTwistedContraction.binomialUnit
      ((ThirdTwistedChargeCocycle.zeta : ℂ) ^ j) ^ bilinear lattice ((g^[j]) a) b) :
      PowerSeries ℂ))

/-- Normal ordering on each input momentum summand. The inner and outer monomials
record the precise cover degrees of `x` and `y`, including the BK cross term.
The equality holds at the entire shifted momentum, with all other output summands
accounted for by the single. -/
theorem orderedChargedProduct_single
    (B : FixedDualBases) (a b : Charge lattice) (p : Momentum) (P : Fock) :
    orderedChargedProduct B a b (Finsupp.single p P) =
      Finsupp.single (shift (a + b) p)
        (single (momentumExponent b p)
            (single (momentumExponent (a + b) p + 3 * bilinear lattice a b -
                momentumExponent b p)
              (algebraMap ℂ Fock ((c₃ a b : ℂ) * chargePhase (a + b) p))) *
          orderedContraction a b *
          HahnSeries.C (HahnSeries.ofPowerSeries ℤ Fock (creationExponential B a)) *
          yExpansion (PowerSeries.mapAlgHom polyC (creationExponential B b)) *
          inverseCover₂ (translateOuter B b (translatedPolynomial B a P))) := by
  have he : momentumExponent a (shift b p) =
      momentumExponent (a + b) p + 3 * bilinear lattice a b - momentumExponent b p := by
    have h := momentumExponent_ordered a b p
    omega
  have ht := DFunLike.congr_fun (translatedPolynomial_commute B a b) P
  change Polynomial.mapAlgHom (translatedPolynomial B a) (translatedPolynomial B b P) =
    translateOuter B b (translatedPolynomial B a P) at ht
  have hc : yExpansion (PowerSeries.mapAlgHom (translatedPolynomial B a)
      (creationExponential B b)) =
      yExpansion (PowerSeries.mapAlgHom polyC (creationExponential B b)) *
        orderedContraction a b := by
    rw [translated_creationExponential_eq_contraction, P48qNativeContraction.scalar_contraction,
      map_mul, orderedContraction]
  simp only [orderedChargedProduct, Finsupp.lsum_single, LinearMap.comp_apply,
    Finsupp.lsingle_apply, LinearMap.mulLeft_apply, ThirdTwistedChargeAction.shift_add,
    chargePhase_ordered, he, orderedOscillator, AlgHom.toLinearMap_apply, AlgHom.comp_apply,
    ht, hc]
  apply congrArg (Finsupp.single (shift (a + b) p))
  ac_rfl

end

end D5.S3.VertexAlgebra.Lattice.Orbifold.P48qThirdTwistedField
