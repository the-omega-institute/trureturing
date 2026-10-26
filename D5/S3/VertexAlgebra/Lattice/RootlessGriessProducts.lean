/- GID: D5/S3/VertexAlgebra/Lattice/RootlessGriessProducts
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/RootlessGriessProducts
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual quadratic and norm-four charge-orbit lattice products. -/

import D5.S3.VertexAlgebra.LatticeActualConformalState
import D5.S3.VertexAlgebra.LatticeActualStateDerivative
import D5.S3.VertexAlgebra.StateField.SkewSymmetry
import D5.S3.VertexAlgebra.Sectors.LatticeSectorGround
import D5.S3.VertexAlgebra.LatticeInvolution
import D5.S3.VertexAlgebra.Lattice.RootlessLowGrades
import Batteries.Tactic.OpenPrivate

/-!
The carrier, Y, normalized mu, translation,
quadratic field and charge cocycle are the production ordinary lattice ones.
No product identity, representation, shell count or abstract Griess algebra is
assumed. The clean charge table requires positive definiteness and rootlessness.
No positive-rank premise is used: at rank zero Fin D.rank is empty and there
are no norm-four charges. This does not construct the Monster, an Ising model,
a CFT or a string-theory/AdS-CFT bridge.

Read-only suppliers: e30c151ba97e8290d5969cb9e29b6adc29090582, except
LatticeRootlessLowGrades at b1a99af2fd3869ce20268ead0ae5d450226ae91b
(SHA256 8ac6afd9d307a40bfa52272c7e788d9fae8863fc73f102a8ac20d18925338afb).
The existing private bilinear_unit and norm_sub suppliers in
LatticeFiniteNegativeGeneration are reused through Batteries.Tactic.OpenPrivate;
the proofs below consume both without changing their owning module.
Classical construction: Bakalov--Kac, math/0402315v1, section 4.1.
The actual normal/residue suppliers retain Carnahan, Matsuo--Nagatomo and
Kytölä attribution and Apache 2.0 licenses as recorded in their source files.
All supplier specializations and normalization helpers below are reuse;
no literature novelty or accepted new-content classification is asserted.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.Lattice.RootlessGriessProducts
open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration
open LatticeAllStateField LatticeAllStateReconstruction
open LatticeActualConformalState LatticeSugawaraCurrents
open LatticeSugawaraConformal LatticeActualStateDerivative
open LatticeActualVertexAlgebra LatticePositiveEnergy
open RootlessLowGrades MvPolynomial
open scoped BigOperators VertexOperator
noncomputable section

open private bilinear_unit norm_sub from D5.S3.VertexAlgebra.LatticeFiniteNegativeGeneration

/-- Literal neutral quadratic oscillator state. -/
def Q (D : LatticeData) (i j : Fin D.rank) : Carrier D :=
  Finsupp.single 0 (X (i, 0) * X (j, 0))

/-- Actual charged ground state. -/
def ground (D : LatticeData) (a : Charge D) : Carrier D := Finsupp.single a 1

/-- The actual plus orbit; no choice of representatives is required. -/
def E (D : LatticeData) (a : Charge D) : Carrier D := ground D a + ground D (-a)

/-- Gram pairing with a colour, in precisely the requested coordinates. -/
def Gi (D : LatticeData) (i : Fin D.rank) (a : Charge D) : ℂ :=
  ∑ j : Fin D.rank, (D.G i j : ℂ) * (a j : ℂ)

/-- The square of the existing actual charge oscillator polynomial. -/
def Qcharge (D : LatticeData) (a : Charge D) : Carrier D :=
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
theorem quadratic_orbit_one (D : LatticeData) (i j : Fin D.rank) (a : Charge D) :
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
theorem orbit_quadratic_one (D : LatticeData) (a : Charge D) (i j : Fin D.rank) :
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

/-- The two mixed vacuum pairings are zero on the actual carrier. -/
theorem mixed_three (D : LatticeData) (i j : Fin D.rank) (a : Charge D) :
    mu D (Q D i j) 3 (E D a) = 0 ∧ mu D (E D a) 3 (Q D i j) = 0 := by
  refine ⟨quadratic_orbit_high D i j a 3 (by omega), ?_⟩
  have h := ((StateField.SkewSymmetry.skew_symmetry (actualVertexAlgebra D)
    (E D a) (Q D i j)).1 3).2
  change mu D (E D a) 3 (Q D i j) = ∑ᶠ k : ℕ,
    (((-1 : ℂ) ^ ((3 : ℤ)+(k : ℤ)+1)) / (k.factorial : ℂ)) •
      (translation D ^ k) (mu D (Q D i j) (3+k) (E D a)) at h
  rw [h]
  apply finsum_eq_zero_of_forall_eq_zero
  intro k
  rw [quadratic_orbit_high D i j a (3+k) (by omega), map_zero, smul_zero]

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

/-- The actual Heisenberg contraction on one creation, with the vacuum term
and its sign computed in normalized integer modes. -/
private theorem neutral_one_creation (D : LatticeData) (i j : Fin D.rank) :
    neutralMode D i 1 (neutralMode D j (-1) (vacuum D)) =
      (D.G i j : ℂ) • vacuum D := by
  have h := LinearMap.congr_fun (neutralMode_heisenberg D i j 1 (-1)) (vacuum D)
  have hv : neutralMode D i 1 (vacuum D) = 0 := by
    change neutralMode D i 1 (ground D 0) = 0
    simp [neutral_ground D i 0 1 (by omega)]
  simpa [hv, Module.End.mul_apply] using h

/-- Four nontrivial actual neutral quadratic contractions, including repeated
colours and all matrix entries; no inverse Gram or rank restriction is needed. -/
theorem quadratic_quadratic_one (D : LatticeData) (i j k l : Fin D.rank) :
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

/-- The vacuum pairing of the two literal quadratic oscillator states. -/
theorem quadratic_quadratic_three (D : LatticeData) (i j k l : Fin D.rank) :
    mu D (Q D i j) 3 (Q D k l) =
      ((D.G i k : ℂ)*(D.G j l : ℂ) + (D.G i l : ℂ)*(D.G j k : ℂ)) • vacuum D := by
  change ((Y D (Finsupp.single 0 (X (i,0) * X (j,0))))[[3]]) (Q D k l) = _
  rw [quadratic_state_field, Q_as_creation D k l]
  change ((quadraticSummand D i j)[[(2 : ℤ)+1]])
    (neutralMode D k (-1) (neutralMode D l (-1) (vacuum D))) = _
  rw [quadratic_creation_commute D i j k 2,
    quadratic_creation_commute D i j l 2]
  have hv (a : Fin D.rank) : neutralMode D a 1 (vacuum D) = 0 := by
    change neutralMode D a 1 (ground D 0) = 0
    simp [neutral_ground D a 0 1 (by omega)]
  simp only [show (2 : ℤ)+1 = 3 by omega, show (2 : ℤ)-1 = 1 by omega,
    quadratic_vacuum D i j 3 (by omega), hv, map_zero, smul_zero,
    add_zero, zero_add, neutral_one_creation, smul_smul, ← add_smul]
  congr 1
  ring

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

private theorem orbit_diagonal_three (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) :
    mu D (E D a) 3 (E D a) = (2 : ℂ) • vacuum D := by
  rw [orbit_coefficient, ha, epsilon_norm_four D a ha]
  simp only [show -(3 : ℤ)-1-4 = -8 by norm_num,
    show -(3 : ℤ)-1+4 = 0 by norm_num,
    creation_negative D a (-8) (by norm_num),
    creation_negative D (-a) (-8) (by norm_num), creation_zero,
    Finsupp.single_zero, zero_add, one_smul, sub_self, neg_zero]
  change Finsupp.single (0 : Charge D) (1 : Oscillator D) +
    Finsupp.single 0 1 = (2 : ℂ) • Finsupp.single 0 1
  rw [two_smul]

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

/-- Complete clean mode-one charge table for positive rootless even lattices.
Both signs of a repeated orbit are handled before the inner-product cases.
The lower-cocycle phases are the actual epsilon, including in the +2 case. -/
theorem orbit_orbit_one (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (hroot : ∀ c : Charge D, bilinear D c c ≠ 2)
    (a b : Charge D) (ha : bilinear D a a = 4) (hb : bilinear D b b = 4) :
    mu D (E D a) 1 (E D b) =
      if b = a ∨ b = -a then Qcharge D a
      else if bilinear D a b = -2 then epsilon D a b • E D (a+b)
      else if bilinear D a b = 2 then epsilon D a (-b) • E D (a-b)
      else 0 := by
  classical
  by_cases hs : b = a ∨ b = -a
  · rw [ite_eq_left hs]
    rcases hs with h | h
    · subst b
      exact orbit_diagonal_one D a ha
    · subst b
      rw [E_neg]
      exact orbit_diagonal_one D a ha
  · rw [ite_eq_right hs]
    have hbounds := norm_four_inner_bounds D hD hroot a b ha hb
      (fun h => hs (Or.inl h)) (fun h => hs (Or.inr h))
    by_cases hm : bilinear D a b = -2
    · rw [ite_eq_left hm]
      exact orbit_add_one D a b hm
    · rw [ite_eq_right hm]
      by_cases hp : bilinear D a b = 2
      · rw [ite_eq_left hp]
        exact orbit_sub_one D a b hp
      · rw [ite_eq_right hp]
        exact orbit_middle_one D a b (by omega) (by omega)

/-- Complete vacuum-pairing table for actual norm-four plus orbits.
Positivity/rootlessness enter in proving the noncoincident terms vanish. -/
theorem orbit_orbit_three (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (hroot : ∀ c : Charge D, bilinear D c c ≠ 2)
    (a b : Charge D) (ha : bilinear D a a = 4) (hb : bilinear D b b = 4) :
    mu D (E D a) 3 (E D b) =
      if b = a ∨ b = -a then (2 : ℂ) • vacuum D else 0 := by
  classical
  by_cases hs : b = a ∨ b = -a
  · rw [ite_eq_left hs]
    rcases hs with h | h
    · subst b
      exact orbit_diagonal_three D a ha
    · subst b
      rw [E_neg]
      exact orbit_diagonal_three D a ha
  · rw [ite_eq_right hs]
    have hbounds := norm_four_inner_bounds D hD hroot a b ha hb
      (fun h => hs (Or.inl h)) (fun h => hs (Or.inr h))
    rw [orbit_coefficient,
      creation_negative D a (-3-1-bilinear D a b) (by omega),
      creation_negative D (-a) (-3-1-bilinear D a b) (by omega),
      creation_negative D a (-3-1+bilinear D a b) (by omega),
      creation_negative D (-a) (-3-1+bilinear D a b) (by omega)]
    simp

end
end D5.S3.VertexAlgebra.Lattice.RootlessGriessProducts
