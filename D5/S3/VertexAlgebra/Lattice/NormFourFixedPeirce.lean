/- GID: D5/S3/VertexAlgebra/Lattice/NormFourFixedPeirce
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/NormFourFixedPeirce
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual norm-four Peirce quartic on the complete theta-fixed energy-two space. -/

import D5.S3.VertexAlgebra.LatticeActualConformalState
import D5.S3.VertexAlgebra.LatticeActualStateDerivative
import D5.S3.VertexAlgebra.StateField.SkewSymmetry
import D5.S3.VertexAlgebra.Sectors.LatticeSectorGround
import D5.S3.VertexAlgebra.LatticeInvolution
import D5.S3.VertexAlgebra.Lattice.RootlessLowGrades
import D5.S3.VertexAlgebra.Lattice.NormFourVirasoroVector
import D5.S3.VertexAlgebra.Lattice.InvolutionRootlessLowGrades
import Batteries.Tactic.OpenPrivate

/-!
The norm-four vector is the production state of Shimakura, arXiv:1202.6107,
(1.3), attributed there to Dong--Mason--Zhu, Theorem 6.3. The contractions
reuse the production ordinary lattice construction of Bakalov--Kac,
math/0402315v1, section 4.1, and Frenkel--Lepowsky--Meurman. Imported
normal-product/residue suppliers retain their Carnahan, Matsuo--Nagatomo
and Kytölä attribution and Apache 2.0 licenses.
The quartic is proved on the complete actual theta-fixed energy-two space.
No Ising simplicity, fusion, Monster, string or AdS/CFT assertion is made.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.Lattice.NormFourFixedPeirce
open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration
open LatticeAllStateField LatticeAllStateReconstruction
open LatticeActualConformalState LatticeSugawaraCurrents
open LatticeSugawaraConformal LatticeActualStateDerivative
open LatticeActualVertexAlgebra LatticePositiveEnergy
open RootlessLowGrades MvPolynomial
open NormFourVirasoroVector InvolutionRootlessLowGrades LatticeInvolution
open LatticeActualProductKernel LatticeActualGeneratorLocality
open scoped BigOperators VertexOperator Classical
noncomputable section

open private bilinear_unit norm_sub from D5.S3.VertexAlgebra.LatticeFiniteNegativeGeneration

/-- Literal neutral quadratic oscillator state. -/
private def Q (D : LatticeData) (i j : Fin D.rank) : Carrier D :=
  Finsupp.single 0 (X (i, 0) * X (j, 0))

/-- Actual charged ground state. -/
private def ground (D : LatticeData) (a : Charge D) : Carrier D := Finsupp.single a 1

/-- The actual plus orbit; no choice of representatives is required. -/
private def E (D : LatticeData) (a : Charge D) : Carrier D := ground D a + ground D (-a)

/-- Gram pairing with a colour, in precisely the requested coordinates. -/
private def Gi (D : LatticeData) (i : Fin D.rank) (a : Charge D) : ℂ :=
  ∑ j : Fin D.rank, (D.G i j : ℂ) * (a j : ℂ)

/-- The square of the existing actual charge oscillator polynomial. -/
private def Qcharge (D : LatticeData) (a : Charge D) : Carrier D :=
  Finsupp.single 0 ((chargePolynomial D a) ^ 2)

private theorem mu_add_left (D : LatticeData) (a b c : Carrier D) (n : ℤ) :
    mu D (a + b) n c = mu D a n c + mu D b n c := by
  simp only [mu, map_add, Pi.add_apply, LinearMap.add_apply]

private theorem mu_add_right (D : LatticeData) (a b c : Carrier D) (n : ℤ) :
    mu D a n (b + c) = mu D a n b + mu D a n c := by
  simp [mu]

@[simp] private theorem E_neg (D : LatticeData) (a : Charge D) : E D (-a) = E D a := by
  simp [E, add_comm]

@[simp] private theorem Gi_neg (D : LatticeData) (i : Fin D.rank) (a : Charge D) :
    Gi D i (-a) = -Gi D i a := by
  simp [Gi, Finset.sum_neg_distrib]

@[simp] private theorem chargePolynomial_neg (D : LatticeData) (a : Charge D) :
    chargePolynomial D (-a) = -chargePolynomial D a := by
  simp [chargePolynomial, Finset.sum_neg_distrib]

@[simp] private theorem epsilon_zero_right (D : LatticeData) (a : Charge D) :
    epsilon D a 0 = 1 := by
  simp [epsilon, lowerCocycleExponent, paritySign]

@[simp] private theorem creation_negative (D : LatticeData) (a : Charge D)
    (t : ℤ) (ht : t < 0) : creationCoeff D a t = 0 := by
  simp [creationCoeff, ht]

@[simp] private theorem creation_zero (D : LatticeData) (a : Charge D) :
    creationCoeff D a 0 = 1 := by
  simp [creationCoeff, exponential_constant]

/-- Reuse the complete actual ground series, restoring its actual charge support
with inclusion_canonical rather than assuming any coefficient identity. -/
private theorem ground_product (D : LatticeData) (a b : Charge D) (n : ℤ) :
    mu D (ground D a) n (ground D b) =
      epsilon D a b • Finsupp.single (a + b)
        (creationCoeff D a (-n - 1 - bilinear D a b)) := by
  change ((Y D (LatticeSectorIntertwiner.inclusion D a 1))[[n]])
    (LatticeSectorIntertwiner.inclusion D b 1) = _
  rw [← LatticeSectorIntertwiner.inclusion_canonical D a b 1 1 n,
    LatticeSectorIntertwiner.canonical_ground_series]
  simp only [map_smul, LatticeSectorIntertwiner.inclusion, Finsupp.lsingle_apply]

/-- The derivative-state theorem computes the genuine second creation coefficient.
Its derivative term is retained, so it can be cancelled rather than discarded. -/
private theorem creation_two (D : LatticeData) (a : Charge D) :
    creationCoeff D a 2 = (2 : ℂ)⁻¹ •
      (oscillatorDerivation D (chargePolynomial D a) + (chargePolynomial D a)^2) := by
  have hraw := LinearMap.congr_fun
    (state_derivative_modes D (ground D a) (-2)) (vacuum D)
  have h : ((Y D (translation D (ground D a)))[[-2]]) (vacuum D) =
      (2 : ℂ) • ((Y D (ground D a))[[-3]]) (vacuum D) := by
    simpa using hraw
  rw [← translation_as_mode D (translation D (ground D a))] at h
  change translation D (translation D (ground D a)) =
    (2 : ℂ) • mu D (ground D a) (-3) (ground D 0) at h
  rw [ground_product, epsilon_zero_right, one_smul, add_zero] at h
  have he := congrArg (fun v : Carrier D => v a) h
  have hc : oscillatorDerivation D (chargePolynomial D a) + (chargePolynomial D a)^2 =
      (2 : ℂ) • creationCoeff D a 2 := by
    simpa [ground, translation_single, pow_two, bilinear] using he
  calc
    creationCoeff D a 2 = (2 : ℂ)⁻¹ • ((2 : ℂ) • creationCoeff D a 2) := by
      rw [smul_smul, inv_mul_cancel₀ (by norm_num : (2 : ℂ) ≠ 0), one_smul]
    _ = _ := by rw [← hc]

/-- Opposite charges cancel the mode-two derivative; they leave the square
of the actual mode-one charge oscillator. -/
private theorem creation_two_opposite (D : LatticeData) (a : Charge D) :
    creationCoeff D a 2 + creationCoeff D (-a) 2 = (chargePolynomial D a)^2 := by
  rw [creation_two, creation_two, chargePolynomial_neg, map_neg, neg_sq]
  rw [← smul_add]
  have h :
      (oscillatorDerivation D (chargePolynomial D a) + (chargePolynomial D a)^2) +
        (-oscillatorDerivation D (chargePolynomial D a) + (chargePolynomial D a)^2) =
      (2 : ℂ) • (chargePolynomial D a)^2 := by module
  rw [h, smul_smul]
  norm_num

/-- Negating either charge leaves this literal lower-cocycle sign unchanged. -/
private theorem epsilon_neg_right (D : LatticeData) (a b : Charge D) :
    epsilon D a (-b) = epsilon D a b := by
  have h : lowerCocycleExponent D a (-b) = -lowerCocycleExponent D a b := by
    simp [lowerCocycleExponent, Finset.sum_neg_distrib, add_comm]
  simp only [epsilon, h, paritySign, even_neg]

private theorem epsilon_neg_left (D : LatticeData) (a b : Charge D) :
    epsilon D (-a) b = epsilon D a b := by
  have h := LatticeInvolution.epsilon_neg_neg D a (-b)
  simpa only [neg_neg, epsilon_neg_right] using h

/-- Diagonal norm-four sign checked against the actual section square. -/
private theorem epsilon_norm_four (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) : epsilon D a a = 1 := by
  unfold epsilon
  rw [LatticeTwistedGroundRealization.SignQuotient.integral_cocycle_square, ha]
  norm_num [paritySign]

/-- Two genuine charge channels in the actual product, at every integer mode. -/
private theorem orbit_coefficient (D : LatticeData) (a b : Charge D) (n : ℤ) :
    mu D (E D a) n (E D b) = epsilon D a b •
      ((Finsupp.single (a + b) (creationCoeff D a (-n-1-bilinear D a b)) +
        Finsupp.single (-(a + b)) (creationCoeff D (-a) (-n-1-bilinear D a b))) +
       (Finsupp.single (a - b) (creationCoeff D a (-n-1+bilinear D a b)) +
        Finsupp.single (-(a - b)) (creationCoeff D (-a) (-n-1+bilinear D a b)))) := by
  simp only [E, mu_add_left, mu_add_right, ground_product,
    epsilon_neg_left, epsilon_neg_right, bilinear_neg_left, bilinear_neg_right,
    neg_neg, sub_neg_eq_add]
  have h1 : -a + b = -(a - b) := by abel
  have h2 : a + -b = a - b := by abel
  have h3 : -a + -b = -(a + b) := by abel
  rw [h1, h2, h3]
  simp only [smul_add]
  abel

/-- Rootlessness bounds pairings of distinct sign orbits. The existing energy
gap is used on both the sum and the difference; no Cauchy hypothesis is added. -/
private theorem norm_four_inner_bounds (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (hroot : ∀ c : Charge D, bilinear D c c ≠ 2)
    (a b : Charge D) (ha : bilinear D a a = 4) (hb : bilinear D b b = 4)
    (hne : b ≠ a) (hopp : b ≠ -a) :
    -2 ≤ bilinear D a b ∧ bilinear D a b ≤ 2 := by
  have hd : a - b ≠ 0 := by
    intro h
    exact hne (sub_eq_zero.mp h).symm
  have hs : a - (-b) ≠ 0 := by
    intro h
    have he : a = -b := sub_eq_zero.mp h
    exact hopp (by simpa using congrArg Neg.neg he.symm)
  have hgd := chargeEnergy_gap D hD hroot (a-b) hd
  have hgs := chargeEnergy_gap D hD hroot (a-(-b)) hs
  have htd := two_chargeEnergy D (a-b)
  have hts := two_chargeEnergy D (a-(-b))
  rw [norm_sub, ha, hb, bilinear_symmetric D b a] at htd
  rw [norm_sub, ha, LatticeInvolution.bilinear_neg_neg, hb,
    bilinear_neg_left, bilinear_symmetric D b a] at hts
  constructor <;> omega

/-- Actual nonnegative neutral action on a charged ground. The coordinate
conversion consumes the visibility-only bilinear_unit supplier. -/
private theorem neutral_ground (D : LatticeData) (i : Fin D.rank)
    (a : Charge D) (m : ℤ) (hm : 0 ≤ m) :
    neutralMode D i m (ground D a) =
      if m = 0 then Gi D i a • ground D a else 0 := by
  classical
  by_cases hz : m = 0
  · subst m
    simp [ground, neutralMode_single, neutralPolynomialMode, bilinear_unit, Gi,
      Int.cast_sum, Int.cast_mul, Finsupp.smul_single]
  · simp [ground, neutralMode_single, neutralPolynomialMode, not_lt.mpr hm, hz]

/-- The complete nonnegative quadratic action on a ground state: the only
surviving normal-sum index is zero, with its genuine charge-sensitive action. -/
private theorem quadratic_ground (D : LatticeData) (i j : Fin D.rank)
    (a : Charge D) (m : ℤ) (hm : 0 ≤ m) :
    ((quadraticSummand D i j)[[m+1]]) (ground D a) =
      if m = 0 then (Gi D i a * Gi D j a) • ground D a else 0 := by
  rw [quadraticSummand_coefficient, finsum_eq_single _ 0]
  · simp only [normalSummand, lt_irrefl, ite_false, Module.End.mul_apply, sub_zero]
    rw [neutral_ground D i a 0 (by omega)]
    simp only [ite_true, map_smul]
    rw [neutral_ground D j a m hm]
    by_cases hz : m = 0 <;> simp [hz, smul_smul]
  · intro k hk
    by_cases hn : k < 0
    · simp only [normalSummand, ite_eq_left hn, Module.End.mul_apply]
      rw [neutral_ground D j a (m-k) (by omega), ite_eq_right (by omega), map_zero]
    · simp only [normalSummand, ite_eq_right hn, Module.End.mul_apply]
      rw [neutral_ground D i a k (by omega), ite_eq_right hk, map_zero]

/-- Quadratic/charge mode one, computed on actual fields. No norm assumption
is needed for this mixed contraction. -/
private theorem quadratic_orbit_one (D : LatticeData) (i j : Fin D.rank) (a : Charge D) :
    mu D (Q D i j) 1 (E D a) = (Gi D i a * Gi D j a) • E D a := by
  unfold E
  rw [mu_add_right]
  have hg (b : Charge D) : mu D (Q D i j) 1 (ground D b) =
      (Gi D i b * Gi D j b) • ground D b := by
    change ((Y D (Finsupp.single 0 (X (i,0) * X (j,0))))[[1]]) (ground D b) = _
    rw [quadratic_state_field]
    simpa using quadratic_ground D i j b 0 (by omega)
  rw [hg, hg, Gi_neg, Gi_neg, neg_mul_neg, smul_add]

/-- All higher mixed coefficients vanish in this direction. -/
private theorem quadratic_orbit_high (D : LatticeData) (i j : Fin D.rank)
    (a : Charge D) (n : ℤ) (hn : 2 ≤ n) : mu D (Q D i j) n (E D a) = 0 := by
  rw [E, mu_add_right]
  have hg (b : Charge D) : mu D (Q D i j) n (ground D b) = 0 := by
    change ((Y D (Finsupp.single 0 (X (i,0) * X (j,0))))[[n]]) (ground D b) = 0
    rw [quadratic_state_field]
    have h := quadratic_ground D i j b (n-1) (by omega)
    simpa [show n-1+1 = n by omega, show n-1 ≠ 0 by omega] using h
  rw [hg, hg, add_zero]

/-- Reversed mixed mode one from the existing all-state skew theorem. Its
entire positive-translation tail vanishes by actual mixed contractions. -/
private theorem orbit_quadratic_one (D : LatticeData) (a : Charge D) (i j : Fin D.rank) :
    mu D (E D a) 1 (Q D i j) = (Gi D i a * Gi D j a) • E D a := by
  have h := ((StateField.SkewSymmetry.skew_symmetry (actualVertexAlgebra D)
    (E D a) (Q D i j)).1 1).2
  change mu D (E D a) 1 (Q D i j) = ∑ᶠ k : ℕ,
    (((-1 : ℂ) ^ ((1 : ℤ)+(k : ℤ)+1)) / (k.factorial : ℂ)) •
      (translation D ^ k) (mu D (Q D i j) (1+k) (E D a)) at h
  rw [h, finsum_eq_single _ 0]
  · simpa using quadratic_orbit_one D i j a
  · intro k hk
    rw [quadratic_orbit_high D i j a (1+k) (by omega), map_zero, smul_zero]

private theorem Q_as_creation (D : LatticeData) (i j : Fin D.rank) :
    Q D i j = neutralMode D i (-1) (neutralMode D j (-1) (vacuum D)) := by
  change Finsupp.single 0 (X (i,0) * X (j,0)) = _
  rw [← current_minus_one_current, mu, current_state_field, neutralField_ncoeff]
  congr 1
  simpa only [neutralField_ncoeff] using (current_state_creation D j).symm

private theorem Q_comm (D : LatticeData) (i j : Fin D.rank) : Q D i j = Q D j i := by
  simp [Q, mul_comm]

private theorem quadratic_vacuum (D : LatticeData) (i j : Fin D.rank)
    (n : ℤ) (hn : 0 ≤ n) : ((quadraticSummand D i j)[[n]]) (vacuum D) = 0 := by
  rw [← quadratic_state_field]
  exact stateField_creativity D _ n hn

/-- Reuse the actual quadratic/current commutator at q=-1, evaluated at the
specified actual vector. This helper has consumers in both neutral table entries. -/
private theorem quadratic_creation_commute (D : LatticeData) (i j k : Fin D.rank)
    (m : ℤ) (v : Carrier D) :
    ((quadraticSummand D i j)[[m+1]]) (neutralMode D k (-1) v) =
      neutralMode D k (-1) (((quadraticSummand D i j)[[m+1]]) v) +
        (D.G j k : ℂ) • neutralMode D i (m-1) v +
        (D.G i k : ℂ) • neutralMode D j (m-1) v := by
  have h := LinearMap.congr_fun
    (quadraticSummand_current_commutator D i j k m (-1)) v
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply,
    LinearMap.add_apply, Int.cast_neg, Int.cast_one, neg_neg, one_smul,
    show m + (-1 : ℤ) = m-1 by omega] at h
  have hh := sub_eq_iff_eq_add.mp h
  rw [hh]
  abel

/-- Four nontrivial actual neutral quadratic contractions, including repeated
colours and all matrix entries; no inverse Gram or rank restriction is needed. -/
private theorem quadratic_quadratic_one (D : LatticeData) (i j k l : Fin D.rank) :
    mu D (Q D i j) 1 (Q D k l) =
      (D.G i k : ℂ) • Q D j l + (D.G i l : ℂ) • Q D j k +
      (D.G j k : ℂ) • Q D i l + (D.G j l : ℂ) • Q D i k := by
  change ((Y D (Finsupp.single 0 (X (i,0) * X (j,0))))[[1]]) (Q D k l) = _
  rw [quadratic_state_field, Q_as_creation D k l]
  change ((quadraticSummand D i j)[[(0 : ℤ)+1]])
    (neutralMode D k (-1) (neutralMode D l (-1) (vacuum D))) = _
  rw [quadratic_creation_commute D i j k 0,
    quadratic_creation_commute D i j l 0]
  simp only [show (0 : ℤ)+1 = 1 by omega, show (0 : ℤ)-1 = -1 by omega,
    quadratic_vacuum D i j 1 (by omega), map_zero, zero_add,
    map_add, map_smul]
  rw [← Q_as_creation D k i, ← Q_as_creation D k j,
    ← Q_as_creation D i l, ← Q_as_creation D j l,
    Q_comm D k i, Q_comm D k j]
  abel

/-- Equal sign-orbits: the opposite-charge degree-two derivative cancels
inside the actual product, and the diagonal section phase is +1. -/
private theorem orbit_diagonal_one (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) : mu D (E D a) 1 (E D a) = Qcharge D a := by
  rw [orbit_coefficient, ha, epsilon_norm_four D a ha]
  simp only [show -(1 : ℤ)-1-4 = -6 by norm_num,
    show -(1 : ℤ)-1+4 = 2 by norm_num,
    creation_negative D a (-6) (by norm_num),
    creation_negative D (-a) (-6) (by norm_num),
    Finsupp.single_zero, zero_add, one_smul, sub_self, neg_zero]
  rw [← Finsupp.single_add, creation_two_opposite]
  rfl

private theorem orbit_add_one (D : LatticeData) (a b : Charge D)
    (hp : bilinear D a b = -2) :
    mu D (E D a) 1 (E D b) = epsilon D a b • E D (a+b) := by
  rw [orbit_coefficient, hp]
  simp only [show -(1 : ℤ)-1-(-2) = 0 by norm_num,
    show -(1 : ℤ)-1+(-2) = -4 by norm_num, creation_zero,
    creation_negative D a (-4) (by norm_num),
    creation_negative D (-a) (-4) (by norm_num),
    Finsupp.single_zero, add_zero]
  rfl

private theorem orbit_sub_one (D : LatticeData) (a b : Charge D)
    (hp : bilinear D a b = 2) :
    mu D (E D a) 1 (E D b) = epsilon D a (-b) • E D (a-b) := by
  rw [orbit_coefficient, epsilon_neg_right, hp]
  simp only [show -(1 : ℤ)-1-2 = -4 by norm_num,
    show -(1 : ℤ)-1+2 = 0 by norm_num, creation_zero,
    creation_negative D a (-4) (by norm_num),
    creation_negative D (-a) (-4) (by norm_num),
    Finsupp.single_zero, zero_add]
  rfl

private theorem orbit_middle_one (D : LatticeData) (a b : Charge D)
    (hlo : -2 < bilinear D a b) (hhi : bilinear D a b < 2) :
    mu D (E D a) 1 (E D b) = 0 := by
  rw [orbit_coefficient,
    creation_negative D a (-1-1-bilinear D a b) (by omega),
    creation_negative D (-a) (-1-1-bilinear D a b) (by omega),
    creation_negative D a (-1-1+bilinear D a b) (by omega),
    creation_negative D (-a) (-1-1+bilinear D a b) (by omega)]
  simp

open private quadratic_field_expansion quadratic_self_products
  quadratic_charged_products charged_quadratic_products
  quadratic_ground_one from D5.S3.VertexAlgebra.Lattice.NormFourVirasoroVector

private def R (D : LatticeData) (a : Charge D) (i : Fin D.rank) : Carrier D :=
  ∑ k : Fin D.rank, (a k : ℂ) • Q D k i

private theorem gram_contract (D : LatticeData) (a : Charge D) (i : Fin D.rank) :
    (∑ k : Fin D.rank, (a k : ℂ) * (D.G k i : ℂ)) = Gi D i a := by
  unfold Gi
  apply Finset.sum_congr rfl
  intro k hk
  rw [D.symmetric k i, mul_comm]

private theorem charge_contract (D : LatticeData) (a b : Charge D) :
    (∑ i : Fin D.rank, (a i : ℂ) * Gi D i b) = (bilinear D a b : ℂ) := by
  simp only [Gi, bilinear, Int.cast_sum, Int.cast_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

private theorem quadratic_sum (D : LatticeData) (a : Charge D) :
    quadraticState D a = ∑ i : Fin D.rank, (a i : ℂ) • R D a i := by
  simp only [R, Q, quadraticState, chargePolynomial, pow_two,
    Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm,
    Finset.smul_sum, smul_smul, Finsupp.single_finsetSum, Finsupp.smul_single]

private theorem contraction_left (D : LatticeData) (a : Charge D)
    (i j : Fin D.rank) :
    (∑ k : Fin D.rank, ∑ l : Fin D.rank,
      ((a k : ℂ) * (a l : ℂ)) • ((D.G k i : ℂ) • Q D l j)) =
      Gi D i a • R D a j := by
  rw [← gram_contract D a i]
  simp only [R, Finset.sum_smul, Finset.smul_sum, smul_smul, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro l hl
  congr 1
  ring

private theorem contraction_right (D : LatticeData) (a : Charge D)
    (i j : Fin D.rank) :
    (∑ k : Fin D.rank, ∑ l : Fin D.rank,
      ((a k : ℂ) * (a l : ℂ)) • ((D.G l i : ℂ) • Q D k j)) =
      Gi D i a • R D a j := by
  rw [Finset.sum_comm]
  convert contraction_left D a i j using 1
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro l hl
  rw [mul_comm (a k : ℂ) (a l : ℂ)]

private theorem quadratic_on_Q (D : LatticeData) (a : Charge D)
    (i j : Fin D.rank) :
    mu D (quadraticState D a) 1 (Q D i j) =
      (2 * Gi D i a) • R D a j + (2 * Gi D j a) • R D a i := by
  change ((Y D (quadraticState D a))[[1]]) (Q D i j) = _
  rw [quadratic_field_expansion]
  simp_rw [← quadratic_state_field]
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply,
    LinearMap.sum_apply, LinearMap.smul_apply]
  change (∑ k : Fin D.rank, ∑ l : Fin D.rank,
    ((a k : ℂ) * (a l : ℂ)) • mu D (Q D k l) 1 (Q D i j)) = _
  simp_rw [quadratic_quadratic_one, smul_add, Finset.sum_add_distrib]
  rw [contraction_left, contraction_left, contraction_right, contraction_right]
  module

private theorem zero_mode_action (D : LatticeData) (a : Charge D) (s : ℂ)
    (v : Carrier D) :
    mode D a s 0 v = (1 / 16 : ℂ) • mu D (quadraticState D a) 1 v +
      (s/4) • mu D (E D a) 1 v := by
  simp only [mode, vector, map_add, map_smul, VertexOperator.ncoeff,
    Pi.add_apply, Pi.smul_apply, LinearMap.add_apply, LinearMap.smul_apply]
  rfl

private theorem zero_mode_Q (D : LatticeData) (a : Charge D) (s : ℂ)
    (i j : Fin D.rank) :
    mode D a s 0 (Q D i j) =
      (Gi D i a / 8) • R D a j + (Gi D j a / 8) • R D a i +
        (s * Gi D i a * Gi D j a / 4) • E D a := by
  rw [zero_mode_action, quadratic_on_Q, orbit_quadratic_one]
  module

private theorem zero_mode_A (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) :
    mode D a s 0 (quadraticState D a) = quadraticState D a + (4*s) • E D a := by
  rw [zero_mode_action, (quadratic_self_products D a ha).2.1]
  have h := (charged_quadratic_products D a ha).2.1
  change mu D (E D a) 1 (quadraticState D a) = (16 : ℂ) • E D a at h
  rw [h]
  module

private theorem zero_mode_E (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) :
    mode D a s 0 (E D a) = (s/4) • quadraticState D a + E D a := by
  rw [zero_mode_action]
  have h := (quadratic_charged_products D a ha).2.1
  change mu D (quadraticState D a) 1 (E D a) = (16 : ℂ) • E D a at h
  rw [h, orbit_diagonal_one D a ha]
  change (1 / 16 : ℂ) • ((16 : ℂ) • E D a) +
    (s/4) • quadraticState D a = _
  module

private theorem zero_mode_R (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (i : Fin D.rank) :
    mode D a s 0 (R D a i) = (1 / 2 : ℂ) • R D a i +
      (Gi D i a / 8) • quadraticState D a + (s * Gi D i a) • E D a := by
  rw [R, map_sum]
  simp_rw [map_smul, zero_mode_Q, smul_add, smul_smul, Finset.sum_add_distrib]
  have h1 : (∑ k : Fin D.rank, ((a k : ℂ) * (Gi D k a / 8)) • R D a i) =
      (1 / 2 : ℂ) • R D a i := by
    rw [← Finset.sum_smul]
    congr 1
    simp_rw [div_eq_mul_inv, ← mul_assoc]
    rw [← Finset.sum_mul, charge_contract, ha]
    norm_num
  have h2 : (∑ k : Fin D.rank, ((a k : ℂ) * (Gi D i a / 8)) • R D a k) =
      (Gi D i a / 8) • quadraticState D a := by
    rw [quadratic_sum]
    simp only [Finset.smul_sum, smul_smul, mul_comm]
  have h3 : (∑ k : Fin D.rank,
      ((a k : ℂ) * (s * Gi D k a * Gi D i a / 4)) • E D a) =
      (s * Gi D i a) • E D a := by
    rw [← Finset.sum_smul]
    congr 1
    calc
      (∑ k : Fin D.rank, (a k : ℂ) * (s * Gi D k a * Gi D i a / 4)) =
          (∑ k : Fin D.rank, (a k : ℂ) * Gi D k a) * (s * Gi D i a / 4) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro k hk
        ring
      _ = s * Gi D i a := by rw [charge_contract, ha]; push_cast; ring
  rw [h1, h2, h3]
  rfl

private def peirce (D : LatticeData) (a : Charge D) (s : ℂ) :
    Module.End ℂ (Carrier D) :=
  let L := mode D a s 0
  L * (L - (1 / 16 : ℂ) • 1) * (L - (1 / 2 : ℂ) • 1) * (L - (2 : ℂ) • 1)

private theorem peirce_of_cubic (D : LatticeData) (a : Charge D) (s : ℂ)
    (v : Carrier D)
    (h : (mode D a s 0 * (mode D a s 0 - (1 / 2 : ℂ) • 1) *
      (mode D a s 0 - (2 : ℂ) • 1)) v = 0) : peirce D a s v = 0 := by
  let L := mode D a s 0
  have hc : L * (L - (1 / 16 : ℂ) • 1) = (L - (1 / 16 : ℂ) • 1) * L := by
    simp only [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, mul_one, one_mul]
  have he : peirce D a s = (L - (1 / 16 : ℂ) • 1) *
      (L * (L - (1 / 2 : ℂ) • 1) * (L - (2 : ℂ) • 1)) := by
    unfold peirce
    change L * (L - (1 / 16 : ℂ) • 1) * _ * _ = _
    rw [hc]
    simp only [mul_assoc]
    rfl
  rw [he, Module.End.mul_apply, h, map_zero]

private theorem peirce_Q (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1)
    (i j : Fin D.rank) : peirce D a s (Q D i j) = 0 := by
  apply peirce_of_cubic
  simp only [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    Module.End.one_apply, map_sub, map_smul]
  simp only [zero_mode_Q, map_add, map_smul,
    zero_mode_R D a ha, zero_mode_A D a ha, zero_mode_E D a ha]
  have hs3 : s ^ 3 = s := by
    calc
      s ^ 3 = s ^ 2 * s := by ring
      _ = s := by rw [hs, one_mul]
  match_scalars <;> ring_nf <;> simp only [hs, hs3] <;> ring

private theorem quadratic_on_orbit (D : LatticeData) (a b : Charge D) :
    mu D (quadraticState D a) 1 (E D b) =
      (bilinear D a b : ℂ)^2 • E D b := by
  change mu D (quadraticState D a) 1 (ground D b + ground D (-b)) = _
  have hg (b : Charge D) : mu D (quadraticState D a) 1 (ground D b) =
      (bilinear D a b : ℂ)^2 • ground D b := by
    exact quadratic_ground_one D a b
  rw [mu_add_right, hg, hg]
  simp only [bilinear_neg_right, Int.cast_neg, neg_sq, E, smul_add]

private theorem zero_mode_orbit_middle (D : LatticeData) (a b : Charge D) (s : ℂ)
    (hlo : -2 < bilinear D a b) (hhi : bilinear D a b < 2) :
    mode D a s 0 (E D b) = ((bilinear D a b : ℂ)^2 / 16) • E D b := by
  rw [zero_mode_action, quadratic_on_orbit, orbit_middle_one D a b hlo hhi]
  module

private theorem zero_mode_orbit_add (D : LatticeData) (a b : Charge D) (s : ℂ)
    (hp : bilinear D a b = -2) :
    mode D a s 0 (E D b) = (1 / 4 : ℂ) • E D b +
      (s * epsilon D a b / 4) • E D (a+b) := by
  rw [zero_mode_action, quadratic_on_orbit, orbit_add_one D a b hp, hp]
  push_cast
  module

private theorem zero_mode_orbit_sub (D : LatticeData) (a b : Charge D) (s : ℂ)
    (hp : bilinear D a b = 2) :
    mode D a s 0 (E D b) = (1 / 4 : ℂ) • E D b +
      (s * epsilon D a b / 4) • E D (a-b) := by
  rw [zero_mode_action, quadratic_on_orbit, orbit_sub_one D a b hp,
    epsilon_neg_right, hp]
  push_cast
  module

private theorem peirce_of_half_square (D : LatticeData) (a : Charge D) (s : ℂ)
    (v : Carrier D) (h : mode D a s 0 (mode D a s 0 v) =
      (1 / 2 : ℂ) • mode D a s 0 v) : peirce D a s v = 0 := by
  apply peirce_of_cubic
  simp only [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    Module.End.one_apply, map_sub, map_smul]
  rw [h, map_smul, h]
  module

private theorem peirce_matching (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1) :
    peirce D a s (E D a) = 0 := by
  apply peirce_of_cubic
  simp only [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    Module.End.one_apply, map_sub, map_smul]
  simp only [zero_mode_E D a ha, zero_mode_A D a ha, map_add, map_smul]
  have hs3 : s ^ 3 = s := by
    calc
      s ^ 3 = s ^ 2 * s := by ring
      _ = s := by rw [hs, one_mul]
  match_scalars <;> ring_nf <;> simp only [hs, hs3] <;> ring

private theorem peirce_two_block (D : LatticeData) (a : Charge D) (s c : ℂ)
    (u w : Carrier D) (hc : c * c = (1 / 16 : ℂ))
    (hu : mode D a s 0 u = (1 / 4 : ℂ) • u + c • w)
    (hw : mode D a s 0 w = (1 / 4 : ℂ) • w + c • u) :
    peirce D a s u = 0 := by
  apply peirce_of_half_square
  calc
    mode D a s 0 (mode D a s 0 u) =
        (1 / 16 + c * c : ℂ) • u + (c/2) • w := by
      rw [hu, map_add, map_smul, map_smul, hu, hw]
      module
    _ = (1 / 2 : ℂ) • mode D a s 0 u := by rw [hc, hu]; module

private theorem phase_square (D : LatticeData) (a b : Charge D)
    (s : ℂ) (hs : s ^ 2 = 1) :
    (s * epsilon D a b / 4) * (s * epsilon D a b / 4) = (1 / 16 : ℂ) := by
  calc
    _ = s ^ 2 * (epsilon D a b * epsilon D a b) / 16 := by ring
    _ = _ := by rw [hs, epsilon, paritySign_square]; norm_num

private theorem peirce_pairing_neg_two (D : LatticeData) (a b : Charge D)
    (ha : bilinear D a a = 4) (hb : bilinear D b b = 4)
    (s : ℂ) (hs : s ^ 2 = 1) (hp : bilinear D a b = -2) :
    peirce D a s (E D b) = 0 := by
  have hgamma : bilinear D (a+b) (a+b) = 4 := by
    rw [bilinear_add_right, bilinear_symmetric D (a+b) a, bilinear_add_right,
      bilinear_symmetric D (a+b) b, bilinear_add_right,
      ha, hb, bilinear_symmetric D b a, hp]
    norm_num
  have hagamma : bilinear D a (a+b) = 2 := by rw [bilinear_add_right, ha, hp]; norm_num
  have he : epsilon D a (a+b) = epsilon D a b := by
    rw [epsilon_add_right, epsilon_norm_four D a ha, one_mul]
  have hret : mode D a s 0 (E D (a+b)) = (1 / 4 : ℂ) • E D (a+b) +
      (s * epsilon D a b / 4) • E D b := by
    rw [zero_mode_orbit_sub D a (a+b) s hagamma, he,
      show a-(a+b) = -b by abel, E_neg]
  exact peirce_two_block D a s (s * epsilon D a b / 4) (E D b) (E D (a+b))
    (phase_square D a b s hs) (zero_mode_orbit_add D a b s hp) hret

private theorem peirce_pairing_two (D : LatticeData) (a b : Charge D)
    (ha : bilinear D a a = 4) (hb : bilinear D b b = 4)
    (s : ℂ) (hs : s ^ 2 = 1) (hp : bilinear D a b = 2) :
    peirce D a s (E D b) = 0 := by
  have hpneg : bilinear D a (-b) = -2 := by rw [bilinear_neg_right, hp]
  have hbneg : bilinear D (-b) (-b) = 4 := by rw [bilinear_neg_neg, hb]
  simpa only [E_neg] using peirce_pairing_neg_two D a (-b) ha hbneg s hs hpneg

private theorem peirce_orbit (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (hroot : ∀ c : Charge D, bilinear D c c ≠ 2)
    (a b : Charge D) (ha : bilinear D a a = 4) (hb : bilinear D b b = 4)
    (s : ℂ) (hs : s ^ 2 = 1) : peirce D a s (E D b) = 0 := by
  by_cases he : b = a
  · subst b
    exact peirce_matching D a ha s hs
  by_cases ho : b = -a
  · subst b
    rw [E_neg]
    exact peirce_matching D a ha s hs
  have hbnd := norm_four_inner_bounds D hD hroot a b ha hb he ho
  by_cases hm : bilinear D a b = -2
  · exact peirce_pairing_neg_two D a b ha hb s hs hm
  by_cases hp : bilinear D a b = 2
  · exact peirce_pairing_two D a b ha hb s hs hp
  have hm' : -2 < bilinear D a b := by omega
  have hp' : bilinear D a b < 2 := by omega
  have hmid := zero_mode_orbit_middle D a b s hm' hp'
  have hc : bilinear D a b = -1 ∨ bilinear D a b = 0 ∨ bilinear D a b = 1 := by omega
  rcases hc with hc | hc | hc
  · have heigen : mode D a s 0 (E D b) = (1 / 16 : ℂ) • E D b := by
      rw [hmid, hc]; norm_num
    unfold peirce
    simp only [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply,
      Module.End.one_apply, map_sub, map_smul, heigen]
    module
  · have hz : mode D a s 0 (E D b) = 0 := by rw [hmid, hc]; norm_num
    unfold peirce
    simp only [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply,
      Module.End.one_apply, map_sub, map_smul, hz, map_zero]
    module
  · have heigen : mode D a s 0 (E D b) = (1 / 16 : ℂ) • E D b := by
      rw [hmid, hc]; norm_num
    unfold peirce
    simp only [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply,
      Module.End.one_apply, map_sub, map_smul, heigen]
    module

open private FixedGrade theta_gradeTwoBasis_even
  fixedGradeTwoEquiv gradeTwoCoordinateEquiv_basis fixedGradeTwoBasis
  fixedGradeTwoBasis_coordinates gradeTwoBasis_even_coe
  from D5.S3.VertexAlgebra.Lattice.InvolutionRootlessLowGrades
open private pairOccupation_pair from D5.S3.VertexAlgebra.Lattice.RootlessLowGrades

private def neutralPairFixedVector (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (hroot : ∀ a : Charge D, bilinear D a a ≠ 2)
    (s : Sym (Fin D.rank) 2) : FixedGrade D 2 :=
  ⟨(gradeTwoBasis D hD hroot (Sum.inl (Sum.inr s)) : Carrier D),
    (mem_fixedSpace D _).mpr (theta_gradeTwoBasis_even D hD hroot s),
    (gradeTwoBasis D hD hroot (Sum.inl (Sum.inr s))).2⟩

private theorem fixedGradeTwoEquiv_neutralPairFixedVector (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (hroot : ∀ a : Charge D, bilinear D a a ≠ 2) (s : Sym (Fin D.rank) 2) :
    fixedGradeTwoEquiv D hD hroot (neutralPairFixedVector D hD hroot s) =
      Pi.single (Sum.inl s) 1 := by
  classical
  funext j
  rcases j with t | q
  · change gradeTwoCoordinateEquiv D hD hroot
      (gradeTwoBasis D hD hroot (Sum.inl (Sum.inr s))) (Sum.inl (Sum.inr t)) = _
    rw [gradeTwoCoordinateEquiv_basis]
    simp [Pi.single_apply]
  · change gradeTwoCoordinateEquiv D hD hroot
      (gradeTwoBasis D hD hroot (Sum.inl (Sum.inr s)))
        (Sum.inr (normFourOrbitRep D q)) = _
    rw [gradeTwoCoordinateEquiv_basis]
    simp [Pi.single_apply]

private theorem fixedGradeTwoBasis_neutral_coe (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (hroot : ∀ a : Charge D, bilinear D a a ≠ 2) (s : Sym (Fin D.rank) 2) :
    (fixedGradeTwoBasis D hD hroot (Sum.inl s) : Carrier D) =
      Finsupp.single 0 (monomial (pairOccupation D s) 1) := by
  have h : fixedGradeTwoBasis D hD hroot (Sum.inl s) =
      neutralPairFixedVector D hD hroot s := by
    apply (fixedGradeTwoEquiv D hD hroot).injective
    rw [fixedGradeTwoBasis_coordinates, fixedGradeTwoEquiv_neutralPairFixedVector]
  rw [h]
  exact gradeTwoBasis_even_coe D hD hroot s


private theorem actual_basis_neutral_coe (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (hroot : ∀ c : Charge D, bilinear D c c ≠ 2) (p : Sym (Fin D.rank) 2) :
    (actualFixedEnergyTwoBasis D hD hroot (Sum.inl p) : Carrier D) =
      Finsupp.single 0 (monomial (pairOccupation D p) 1) := by
  exact fixedGradeTwoBasis_neutral_coe D hD hroot p

/-- The production norm-four zero mode obeys the Peirce quartic on the WHOLE
literal theta-fixed canonical Sugawara energy-two space. -/
theorem actual_fixed_energy_two_peirce (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (hroot : ∀ c : Charge D, bilinear D c c ≠ 2)
    (a : Charge D) (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1)
    (v : ↥(fixedSpace D ⊓
      (sugawaraMode D (gramComplex D)⁻¹ 0).eigenspace (2 : ℂ))) :
    (mode D a s 0 * (mode D a s 0 - (1 / 16 : ℂ) • 1) *
      (mode D a s 0 - (1 / 2 : ℂ) • 1) * (mode D a s 0 - (2 : ℂ) • 1))
        (v : Carrier D) = 0 := by
  let S := fixedSpace D ⊓ (sugawaraMode D (gramComplex D)⁻¹ 0).eigenspace (2 : ℂ)
  let F : S →ₗ[ℂ] Carrier D := (peirce D a s).comp S.subtype
  have he : F = 0 := by
    apply (actualFixedEnergyTwoBasis D hD hroot).ext
    intro j
    rcases j with p | q
    · change peirce D a s (actualFixedEnergyTwoBasis D hD hroot (Sum.inl p) : Carrier D) = 0
      rw [actual_basis_neutral_coe]
      rcases p with ⟨p, hp⟩
      obtain ⟨i, j, rfl⟩ := Multiset.card_eq_two.mp hp
      rw [pairOccupation_pair]
      simpa only [Q, monomial_add_single, ← X_pow_eq_monomial, pow_one] using
        peirce_Q D a ha s hs i j
    · change peirce D a s (actualFixedEnergyTwoBasis D hD hroot (Sum.inr q) : Carrier D) = 0
      rw [actualFixedEnergyTwoBasis_charge_coe]
      exact peirce_orbit D hD hroot a (normFourOrbitRep D q).1 ha
        (normFourOrbitRep D q).2 s hs
  exact LinearMap.congr_fun he v

#print axioms actual_fixed_energy_two_peirce

end
end D5.S3.VertexAlgebra.Lattice.NormFourFixedPeirce
