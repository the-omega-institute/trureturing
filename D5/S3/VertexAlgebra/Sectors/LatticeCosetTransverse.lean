/- GID: D5/S3/VertexAlgebra/Sectors/LatticeCosetTransverse
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Sectors/LatticeCosetTransverse
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Native polynomial translation of transverse oscillator descendants. -/

import D5.S3.VertexAlgebra.Sectors.LatticeCosetCompression
import D5.S3.VertexAlgebra.LatticeHalfFockChargedCoefficients

/-!
The creation and annihilation polynomials are those of the native lattice
field, Bakalov--Kac, math/0402315v1, section 4.1. The Schur complement is
computed by the original rational Gram inverse. No positive ambient lattice,
new vertex algebra, scalar cocycle replacement or contraction premise occurs.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.LatticeCosetTransverse

open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration
open LatticeCosetCompression LatticeDiscriminantTheta MvPolynomial
open scoped BigOperators

noncomputable section

open private gram_longitudinal from D5.S3.VertexAlgebra.Sectors.LatticeCosetCompression
open private bilinear_unit from D5.S3.VertexAlgebra.LatticeFiniteNegativeGeneration
open private derivative_map solution_unique from
  D5.S3.VertexAlgebra.LatticeHalfFockChargedCoefficients
open private exponential_derivative from D5.S3.VertexAlgebra.LatticeSugawaraConformal

variable (D : LatticeData) {e : ℕ}
variable (B : Matrix (Fin D.rank) (Fin e) ℤ) (C : Matrix (Fin e) (Fin e) ℤ)
variable (hC : ∀ i j, C i j = C j i) (hCe : ∀ i, Even (C i i))

/-- A transverse oscillator is an actual ambient polynomial, not a new state. -/
def transverse (j : Fin e) (k : ℕ) : Oscillator (ambient D e B C hC hCe) :=
  X (j.natAdd D.rank, k) -
    ∑ i : Fin D.rank, (longitudinal D B i j : ℂ) • X (i.castAdd e, k)

/-- Contraction of the external charge with one transverse direction. -/
def transversePair (a : Fin e → ℤ) (j : Fin e) : ℚ :=
  ∑ k, (a k : ℚ) * ((C k j : ℚ) - ∑ i, (B i k : ℚ) * longitudinal D B i j)

/-- The actual native annihilation translation, followed by longitudinal
projection coefficient by coefficient. -/
def translatedProjection (A : Charge (ambient D e B C hC hCe)) :
    Oscillator (ambient D e B C hC hCe) →ₐ[ℂ] Polynomial (Oscillator D) :=
  (Polynomial.mapAlgHom (polynomialProjection D B C hC hCe)).comp
    (aeval (fun x : Index (ambient D e B C hC hCe) =>
      translationVariable (ambient D e B C hC hCe) A x.1 x.2))

private theorem bilinear_old (a : Fin e → ℤ) (n : Charge D) (i : Fin D.rank) :
    bilinear (ambient D e B C hC hCe) (liftCharge D B C hC hCe a n)
        (unitCharge _ (i.castAdd e)) =
      (∑ k, n k * D.G k i) + ∑ k, a k * B i k := by
  classical
  rw [bilinear_symmetric, bilinear_unit]
  change (∑ k : Fin (D.rank+e), _) = _
  rw [Fin.sum_univ_add]
  simp [liftCharge, D.symmetric, mul_comm]

private theorem bilinear_external (a : Fin e → ℤ) (n : Charge D) (j : Fin e) :
    bilinear (ambient D e B C hC hCe) (liftCharge D B C hC hCe a n)
        (unitCharge _ (j.natAdd D.rank)) =
      (∑ k, n k * B k j) + ∑ k, a k * C k j := by
  classical
  rw [bilinear_symmetric, bilinear_unit]
  change (∑ k : Fin (D.rank+e), _) = _
  rw [Fin.sum_univ_add]
  simp [liftCharge, hC, mul_comm]

private theorem transverse_pairing (hD : (gramReal D).PosDef)
    (a : Fin e → ℤ) (n : Charge D) (j : Fin e) :
    (bilinear (ambient D e B C hC hCe) (liftCharge D B C hC hCe a n)
        (unitCharge _ (j.natAdd D.rank)) : ℚ) -
      ∑ i, longitudinal D B i j *
        (bilinear (ambient D e B C hC hCe) (liftCharge D B C hC hCe a n)
          (unitCharge _ (i.castAdd e)) : ℚ) = transversePair D B C a j := by
  rw [bilinear_external]
  simp_rw [bilinear_old, Int.cast_add, Int.cast_sum, Int.cast_mul]
  have old : (∑ i, longitudinal D B i j * ∑ k, (n k : ℚ) * (D.G k i : ℚ)) =
      ∑ k, (n k : ℚ) * (B k j : ℚ) := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k hk
    calc
      (∑ i, longitudinal D B i j * ((n k : ℚ) * (D.G k i : ℚ))) =
          (n k : ℚ) * ∑ i, (D.G k i : ℚ) * longitudinal D B i j := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intros
        ring
      _ = _ := by rw [gram_longitudinal D B hD]
  have ext : (∑ i, longitudinal D B i j * ∑ k, (a k : ℚ) * (B i k : ℚ)) =
      ∑ k, (a k : ℚ) * ∑ i, (B i k : ℚ) * longitudinal D B i j := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intros
    apply Finset.sum_congr rfl
    intros
    ring
  simp_rw [mul_add, Finset.sum_add_distrib]
  rw [old, ext]
  simp only [transversePair, mul_sub, Finset.sum_sub_distrib]
  ring

private theorem translatedProjection_variable
    (A : Charge (ambient D e B C hC hCe))
    (x : Fin (D.rank + e) × ℕ) :
    translatedProjection D B C hC hCe A (X x) =
      Polynomial.C (projectionVariable D B C hC hCe x) -
        Polynomial.C ((bilinear (ambient D e B C hC hCe) A (unitCharge _ x.1) : ℂ) •
          (1 : Oscillator D)) * Polynomial.X^(x.2+1) := by
  simp [translatedProjection, translationVariable, polynomialProjection]

/-- The old charge cancels out of the transverse contraction. The minus sign
comes from the native translationVariable, at every oscillator frequency. -/
theorem transverse_translation (hD : (gramReal D).PosDef)
    (a : Fin e → ℤ) (n : Charge D) (j : Fin e) (k : ℕ) :
    translatedProjection D B C hC hCe (liftCharge D B C hC hCe a n)
        (transverse D B C hC hCe j k) =
      -Polynomial.C ((transversePair D B C a j : ℂ) • (1 : Oscillator D)) *
        Polynomial.X^(k+1) := by
  classical
  have pair :
      (bilinear (ambient D e B C hC hCe) (liftCharge D B C hC hCe a n)
          (unitCharge _ (j.natAdd D.rank)) : ℂ) -
        ∑ i, (longitudinal D B i j : ℂ) *
          (bilinear (ambient D e B C hC hCe) (liftCharge D B C hC hCe a n)
            (unitCharge _ (i.castAdd e)) : ℂ) = (transversePair D B C a j : ℂ) := by
    exact_mod_cast transverse_pairing D B C hC hCe hD a n j
  have hCsmul (z : ℂ) (p : Oscillator D) :
      Polynomial.C (z • p) = z • (Polynomial.C p : Polynomial (Oscillator D)) :=
    map_smul (Polynomial.CAlgHom : Oscillator D →ₐ[ℂ] Polynomial (Oscillator D)) z p
  have hnew := translatedProjection_variable D B C hC hCe
    (liftCharge D B C hC hCe a n) (j.natAdd D.rank,k)
  have hold (i : Fin D.rank) := translatedProjection_variable D B C hC hCe
    (liftCharge D B C hC hCe a n) (i.castAdd e,k)
  simp only [projectionVariable, Fin.addCases_right] at hnew
  simp only [projectionVariable, Fin.addCases_left] at hold
  unfold transverse
  rw [map_sub, map_sum, hnew]
  simp_rw [map_smul, hold]
  simp only [smul_sub, Finset.sum_sub_distrib, ← hCsmul, ← smul_mul_assoc,
    smul_smul]
  rw [← map_sum, ← Finset.sum_mul, ← map_sum, ← Finset.sum_smul]
  have hscalar := congrArg (fun z : ℂ => Polynomial.C (z • (1 : Oscillator D))) pair
  simp only [sub_smul, map_sub] at hscalar
  linear_combination -Polynomial.X^(k+1) * hscalar

/-- Translate only after projecting the ambient polynomial. The old variable
shifts are still the actual ambient pairings, including the external charge. -/
def longitudinalTranslation (A : Charge (ambient D e B C hC hCe)) :
    Oscillator (ambient D e B C hC hCe) →ₐ[ℂ] Polynomial (Oscillator D) :=
  (aeval (fun x : Index D =>
    Polynomial.C (X x : Oscillator D) -
      Polynomial.C ((bilinear (ambient D e B C hC hCe) A
        (unitCharge _ (x.1.castAdd e)) : ℂ) • (1 : Oscillator D)) *
          Polynomial.X^(x.2+1))).comp (polynomialProjection D B C hC hCe)

private theorem translation_difference (hD : (gramReal D).PosDef)
    (a : Fin e → ℤ) (n : Charge D) (x : Fin (D.rank + e) × ℕ) :
    translatedProjection D B C hC hCe (liftCharge D B C hC hCe a n) (X x) -
      longitudinalTranslation D B C hC hCe (liftCharge D B C hC hCe a n) (X x) =
    Fin.addCases (fun _ => 0) (fun j =>
      -Polynomial.C ((transversePair D B C a j : ℂ) • (1 : Oscillator D)) *
        Polynomial.X^(x.2+1)) x.1 := by
  rcases x with ⟨j,k⟩
  induction j using Fin.addCases with
  | left i =>
    simp [translatedProjection_variable, longitudinalTranslation,
      polynomialProjection, projectionVariable]
  | right j =>
    have h : longitudinalTranslation D B C hC hCe (liftCharge D B C hC hCe a n)
          (X (j.natAdd D.rank,k)) =
        ∑ i : Fin D.rank, (longitudinal D B i j : ℂ) •
          translatedProjection D B C hC hCe (liftCharge D B C hC hCe a n)
            (X (i.castAdd e,k)) := by
      simp [longitudinalTranslation, polynomialProjection, projectionVariable,
        translatedProjection_variable, map_smul]
    rw [h]
    simpa only [transverse, map_sub, map_sum, map_smul, Fin.addCases_right] using
      transverse_translation D B C hC hCe hD a n j k

private theorem schur_eq_pair (a b : Fin e → ℤ) :
    schur D B C a b = ∑ j, (b j : ℚ) * transversePair D B C a j := by
  simp only [schur, transversePair, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- The exact logarithmic difference of the two native creation-series
translations. Both charges have arbitrary old and external components. -/
theorem creationSeries_difference (hD : (gramReal D).PosDef)
    (a b : Fin e → ℤ) (n m : Charge D) :
    PowerSeries.map (translatedProjection D B C hC hCe
        (liftCharge D B C hC hCe a n)).toRingHom
        (creationSeries (ambient D e B C hC hCe) (liftCharge D B C hC hCe b m)) -
      PowerSeries.map (longitudinalTranslation D B C hC hCe
        (liftCharge D B C hC hCe a n)).toRingHom
        (creationSeries (ambient D e B C hC hCe) (liftCharge D B C hC hCe b m)) =
      PowerSeries.mk (fun q : ℕ => if q = 0 then 0 else
        -(q : ℂ)⁻¹ • (Polynomial.C ((schur D B C a b : ℂ) • (1 : Oscillator D)) *
          Polynomial.X^q)) := by
  classical
  apply PowerSeries.ext
  intro q
  rw [map_sub, PowerSeries.coeff_map, PowerSeries.coeff_map, PowerSeries.coeff_mk]
  by_cases hq : q = 0
  · simp [creationSeries, hq]
  · simp only [creationSeries, PowerSeries.coeff_mk, dite_eq_right hq]
    change translatedProjection D B C hC hCe (liftCharge D B C hC hCe a n) _ -
      longitudinalTranslation D B C hC hCe (liftCharge D B C hC hCe a n) _ = _
    rw [map_smul, map_smul, ← smul_sub, map_sum, map_sum, ← Finset.sum_sub_distrib]
    simp only [map_smul, ← smul_sub, translation_difference D B C hC hCe hD]
    change (q : ℂ)⁻¹ • (∑ i : Fin (D.rank+e), _) = _
    rw [Fin.sum_univ_add]
    simp only [Fin.addCases_left, Fin.addCases_right, smul_zero, Finset.sum_const_zero,
      zero_add, liftCharge]
    have hcast : ∑ j, (b j : ℂ) * (transversePair D B C a j : ℂ) =
        (schur D B C a b : ℂ) := by exact_mod_cast (schur_eq_pair D B C a b).symm
    have hCsmul (z : ℂ) (p : Oscillator D) :
        Polynomial.C (z • p) = z • (Polynomial.C p : Polynomial (Oscillator D)) :=
      map_smul (Polynomial.CAlgHom : Oscillator D →ₐ[ℂ] Polynomial (Oscillator D)) z p
    rw [ite_eq_right hq, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hq)]
    simp only [← smul_mul_assoc, smul_neg, ← hCsmul, smul_smul,
      ← Finset.sum_mul]
    rw [Finset.sum_neg_distrib, ← map_sum, ← Finset.sum_smul, hcast]
    simp only [neg_mul, smul_neg, neg_smul]
    simp only [← hCsmul, smul_smul, map_neg, neg_mul]


/-- Projecting between the two native annihilation translations removes exactly
one Schur binomial factor from the full creation exponential. -/
theorem creationExponential_factorization (hD : (gramReal D).PosDef)
    (a b : Fin e → ℤ) (n m : Charge D) :
    PowerSeries.map (translatedProjection D B C hC hCe
        (liftCharge D B C hC hCe a n)).toRingHom
        (creationExponential (ambient D e B C hC hCe) (liftCharge D B C hC hCe b m)) =
      PowerSeries.map (longitudinalTranslation D B C hC hCe
        (liftCharge D B C hC hCe a n)).toRingHom
        (creationExponential (ambient D e B C hC hCe) (liftCharge D B C hC hCe b m)) *
      PowerSeries.rescale (-Polynomial.X)
        (PowerSeries.binomialSeries (R := ℚ) (Polynomial (Oscillator D)) (schur D B C a b)) := by
  classical
  let F := ambient D e B C hC hCe
  let α := liftCharge D B C hC hCe a n
  let β := liftCharge D B C hC hCe b m
  let T := translatedProjection D B C hC hCe α
  let L := longitudinalTranslation D B C hC hCe α
  let A := (creationSeries F β).map T.toRingHom
  let A₀ := (creationSeries F β).map L.toRingHom
  let f := (creationExponential F β).map T.toRingHom
  let f₀ := (creationExponential F β).map L.toRingHom
  let s := schur D B C a b
  let U : Polynomial (Oscillator D) := Polynomial.X
  let K := PowerSeries.rescale (-U)
    (PowerSeries.binomialSeries (R := ℚ) (Polynomial (Oscillator D)) s)
  let E : PowerSeries (Polynomial (Oscillator D)) := 1 - PowerSeries.C U * PowerSeries.X
  have hsource := exponential_derivative F β
  have hconstant := LatticeSugawaraConformal.exponential_constant F β
  have hdiff (k : ℕ) : PowerSeries.coeff k
      (PowerSeries.derivative (R := Polynomial (Oscillator D)) A -
       PowerSeries.derivative (R := Polynomial (Oscillator D)) A₀) =
      -Polynomial.C ((s : ℂ) • (1 : Oscillator D)) * U^(k+1) := by
    rw [← map_sub, PowerSeries.coeff_derivative]
    have h := creationSeries_difference D B C hC hCe hD a b n m
    change A - A₀ = _ at h
    rw [h, PowerSeries.coeff_mk, ite_eq_right (Nat.succ_ne_zero k)]
    rw [mul_comm, show (k+1 : Polynomial (Oscillator D)) =
      algebraMap ℂ (Polynomial (Oscillator D)) (k+1 : ℂ) by simp,
      ← Algebra.smul_def, smul_smul]
    have hk : (k+1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
    simp only [Nat.cast_add, Nat.cast_one, mul_neg, mul_inv_cancel₀ hk,
      neg_one_smul, neg_mul, U, s]
  have hDiffE : (PowerSeries.derivative (R := Polynomial (Oscillator D)) A -
      PowerSeries.derivative (R := Polynomial (Oscillator D)) A₀) * E =
      -PowerSeries.C (Polynomial.C ((s : ℂ) • (1 : Oscillator D)) * U) := by
    apply PowerSeries.ext
    intro k
    cases k with
    | zero =>
      simp only [E, mul_sub, mul_one, ← mul_assoc, map_sub,
        PowerSeries.coeff_zero_mul_X, sub_zero, hdiff,
        map_neg, PowerSeries.coeff_zero_C]
      ring
    | succ k =>
      simp only [E, mul_sub, mul_one, ← mul_assoc, map_sub,
        PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_mul_C,
        hdiff, map_neg, PowerSeries.coeff_C, Nat.succ_ne_zero, ite_false]
      simp only [pow_succ]
      ring
  have hChoose (k : ℕ) : (k+1 : ℚ) * Ring.choose s (k+1) =
      (s-k) * Ring.choose s k := by
    simpa [Nat.choose_succ_self_right, Nat.add_sub_cancel_left,
      Ring.choose_one_right, nsmul_eq_mul, mul_comm] using
      (Ring.choose_smul_choose s (n := k+1) (k := k) (by omega))
  have hKcoeff (k : ℕ) : PowerSeries.coeff k K =
      (-U)^k * algebraMap ℚ (Polynomial (Oscillator D)) (Ring.choose s k) := by
    simp only [K, PowerSeries.coeff_rescale, PowerSeries.binomialSeries_coeff,
      Algebra.smul_def, mul_one]
  have hs : Polynomial.C ((s : ℂ) • (1 : Oscillator D)) =
      algebraMap ℚ (Polynomial (Oscillator D)) s := by
    simp [Algebra.smul_def, Polynomial.algebraMap_apply, MvPolynomial.algebraMap_apply]
  have hKE : PowerSeries.derivative (R := Polynomial (Oscillator D)) K * E =
      -PowerSeries.C (Polynomial.C ((s : ℂ) • (1 : Oscillator D)) * U) * K := by
    rw [hs]
    apply PowerSeries.ext
    intro k
    cases k with
    | zero =>
      dsimp only [E]
      rw [mul_sub, mul_one, ← mul_assoc, map_sub,
        PowerSeries.coeff_zero_mul_X, sub_zero, PowerSeries.coeff_derivative,
        neg_mul, map_neg, PowerSeries.coeff_C_mul, hKcoeff, hKcoeff]
      simp
      ring
    | succ k =>
      dsimp only [E]
      rw [mul_sub, mul_one, ← mul_assoc, map_sub,
        PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_mul_C,
        PowerSeries.coeff_derivative, PowerSeries.coeff_derivative,
        neg_mul, map_neg, PowerSeries.coeff_C_mul]
      simp only [hKcoeff]
      have hr : (k+2 : Polynomial (Oscillator D)) *
          algebraMap ℚ (Polynomial (Oscillator D)) (Ring.choose s (k+2)) =
          (algebraMap ℚ (Polynomial (Oscillator D)) s - (k+1 : Polynomial (Oscillator D))) *
            algebraMap ℚ (Polynomial (Oscillator D)) (Ring.choose s (k+1)) := by
        simpa only [map_mul, map_sub, map_add, map_natCast, map_one, map_ofNat,
          Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, add_assoc, one_add_one_eq_two] using
          congrArg (algebraMap ℚ (Polynomial (Oscillator D))) (hChoose (k+1))
      simp only [pow_succ, Nat.cast_add, Nat.cast_one]
      linear_combination (-U)^(k+1) * (-U) * hr
  have hu : IsUnit E := PowerSeries.isUnit_iff_constantCoeff.mpr (by simp [E])
  have hDK : PowerSeries.derivative (R := Polynomial (Oscillator D)) K =
      K * (PowerSeries.derivative (R := Polynomial (Oscillator D)) A -
        PowerSeries.derivative (R := Polynomial (Oscillator D)) A₀) := by
    apply hu.mul_right_cancel
    rw [hKE, mul_assoc, hDiffE]
    ring
  have hf : PowerSeries.derivative (R := Polynomial (Oscillator D)) f =
      f * PowerSeries.derivative (R := Polynomial (Oscillator D)) A := by
    dsimp only [f, A]
    rw [derivative_map, hsource, map_mul, derivative_map]
  have hf₀ : PowerSeries.derivative (R := Polynomial (Oscillator D)) f₀ =
      f₀ * PowerSeries.derivative (R := Polynomial (Oscillator D)) A₀ := by
    dsimp only [f₀, A₀]
    rw [derivative_map, hsource, map_mul, derivative_map]
  have hg : PowerSeries.derivative (R := Polynomial (Oscillator D)) (f₀*K) =
      (f₀*K) * PowerSeries.derivative (R := Polynomial (Oscillator D)) A := by
    letI : Algebra (Polynomial (Oscillator D))
        (PowerSeries (Polynomial (Oscillator D))) := MvPowerSeries.instAlgebra
    have h := (PowerSeries.derivative (R := Polynomial (Oscillator D))).leibniz' f₀ K
    change PowerSeries.derivative (R := Polynomial (Oscillator D)) (f₀*K) =
      f₀ * PowerSeries.derivative (R := Polynomial (Oscillator D)) K +
        K * PowerSeries.derivative (R := Polynomial (Oscillator D)) f₀ at h
    rw [h, hf₀, hDK]
    ring
  apply solution_unique f (f₀*K) _ hf hg
  have hT : PowerSeries.coeff 0 f = 1 := by
    dsimp only [f]
    rw [PowerSeries.coeff_map, hconstant, map_one]
  have hL : PowerSeries.coeff 0 f₀ = 1 := by
    dsimp only [f₀]
    rw [PowerSeries.coeff_map, hconstant, map_one]
  rw [hT, PowerSeries.coeff_mul, Finset.Nat.antidiagonal_zero]
  simp only [Finset.sum_singleton, hL, hKcoeff, pow_zero, one_mul,
    Ring.choose_zero_right, map_one]

end
end D5.S3.VertexAlgebra.LatticeCosetTransverse
