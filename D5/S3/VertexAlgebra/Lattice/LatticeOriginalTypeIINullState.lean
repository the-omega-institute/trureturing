/- GID: D5/S3/VertexAlgebra/Lattice/LatticeOriginalTypeIINullState
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/LatticeOriginalTypeIINullState
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Original Type II null obstruction and explicit relative BRST primitive. -/


import D5.S3.VertexAlgebra.LatticeSugawaraConformal
import D5.S3.VertexAlgebra.SourceBPZ.OriginalMatterHermitian
import Mathlib.Tactic.Module
import D5.S3.VertexAlgebra.Lattice.LatticeRelativeMassShell
import Batteries.Tactic.OpenPrivate

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-!
The Type II formula is classical; the new formal endpoint concerns the literal
original carrier and its finite oscillator coefficients. No novelty in physics
or completion of the full string-theory goal is claimed.

admission_basis: escape-witness
The endpoint itself is produced by the actual coefficient calculation: ell(S)
is -5, whereas ell(Tu) is the constant coefficient of the original L(1)u.
Polynomial induction proves these coefficient identities on all oscillator
polynomials, followed by finite-charge linear induction. No desired-result
premise or substituted Fock form is used.

Coefficient proof shapes after inlining and their consumers:
coeff_linear_mul_X: bind-only; coeff_derivation_two, ell_translation_single,
  coeff_mode_one.
coeff_zero_derivation: content; coeff_derivation_two.
coeff_derivation_two: content; ell_translation_single.
charge_scalar: bind-only; ell_translation_single, charge_norm.
ell_translation_single: content; ell_translation, ell_translation_squared.
mode_mul_X: bind-only; coeff_mode_one.
coeff_mode_one: content; ell_translation.
ell_translation: content; original_typeII_null_obstruction.
current_two_constant: bind-only; current_two_extracts_ell.
current_two_extracts_ell: bind-only; ell_minus_two.
charge_norm: bind-only; ell_minus_two, ell_translation_squared.
ell_minus_two: bind-only; ell_typeII.
ell_translation_squared: content; ell_typeII.
ell_typeII: content; original_typeII_null_obstruction.
typeII_primary: bind-only; original_typeII_null_obstruction.
original_typeII_null_obstruction: content; public coefficient-obstruction
  endpoint, not an auxiliary binding wrapper.
ell and typeII are consumed private functional and literal-state definitions.
The relative extension computes the original charge on a literal primitive,
using exact finite support and Ward identities. ghost_R_one_vacuum is consumed
by ghost_Q_down, which is consumed by charge_on_primary_down. The latter is
consumed by primitive_charge and the public boundary endpoint.
ghost_L_minus_two_down and charge_on_vacuum are consumed by primitive_charge;
ground_translation_modes is consumed by primitive_charge and primitive_relative;
single_tensor_fixed is consumed by primitive_relative; both primitive_charge
and primitive_relative are consumed by original_typeII_relative_boundary.
The finite-support and coefficient computations provide the content; Ward,
Virasoro, grading and relative-subspace applications are consumed bindings.
The boundary endpoint constructs and verifies the original explicit primitive;
it assumes no exactness or cohomology comparison.
Utility is none: these are algebraic laws for arbitrary original lattice data,
charges, inverse matrices and finite oscillator polynomials, not a certified
finite instance or bounded enumeration.
-/


namespace D5.S3.VertexAlgebra.LatticeOriginalTypeIINullState

open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration
open LatticeSugawaraCurrents LatticeSugawaraVirasoro LatticeSugawaraConformal
open SourceBPZ.OriginalMatterHermitian MvPolynomial
open scoped BigOperators

noncomputable section

private theorem coeff_linear_mul_X (D : LatticeData) (x y : Index D)
    (P : Oscillator D) :
    (P * X y).coeff (Finsupp.single x 1) = if x = y then P.coeff 0 else 0 := by
  classical
  by_cases h : x = y
  · subst y; simp [coeff_mul_X']
  · simp [coeff_mul_X', h, Ne.symm h]

private theorem coeff_zero_derivation (D : LatticeData) (P : Oscillator D) :
    (oscillatorDerivation D P).coeff 0 = 0 := by
  classical
  induction P using MvPolynomial.induction_on with
  | C c => simp [C_eq_smul_one]
  | add P Q hP hQ => simp [hP, hQ]
  | mul_X P x hP =>
    simp [Derivation.leibniz, oscillatorDerivation, MvPolynomial.mkDerivation_X,
      ← constantCoeff_eq, hP]

private theorem coeff_derivation_two (D : LatticeData) (i : Fin D.rank)
    (P : Oscillator D) :
    (oscillatorDerivation D P).coeff (Finsupp.single (i, 1) 1) =
      P.coeff (Finsupp.single (i, 0) 1) := by
  classical
  induction P using MvPolynomial.induction_on with
  | C c =>
    have he : (0 : Index D →₀ ℕ) ≠ Finsupp.single (i,0) 1 :=
      Ne.symm (Finsupp.single_ne_zero.mpr one_ne_zero)
    simp [C_eq_smul_one, MvPolynomial.coeff_one, he]
  | add P Q hP hQ => simp [hP, hQ]
  | mul_X P x hP =>
    rcases x with ⟨j,k⟩
    rw [Derivation.leibniz]
    have hx : oscillatorDerivation D (X (j,k)) =
        (k+1 : ℂ) • (X (j,k+1) : Oscillator D) := by
      simp [oscillatorDerivation]
    rw [hx]
    simp only [smul_eq_mul]
    rw [mul_comm (X (j,k))]
    simp only [MvPolynomial.coeff_add, mul_smul_comm, coeff_smul, coeff_linear_mul_X,
      coeff_zero_derivation]
    by_cases h : k = 0
    · subst k; simp
    · simp [h, Ne.symm h, show k + 1 ≠ 1 by omega]

private def ell (D : LatticeData) (p : Charge D) (x : Carrier D) : ℂ :=
  ∑ i : Fin D.rank, (∑ j : Fin D.rank, (D.G i j : ℂ) * (p j : ℂ)) *
    (x p).coeff (Finsupp.single (i, 1) 1)

private theorem charge_scalar (D : LatticeData) (p : Charge D) (i : Fin D.rank) :
    chargeScalar D p i = ∑ j : Fin D.rank, (D.G i j : ℂ) * (p j : ℂ) := by
  simp [chargeScalar, bilinear, unitCharge, Int.cast_sum]

private theorem ell_translation_single (D : LatticeData) (p q : Charge D)
    (P : Oscillator D) :
    ell D p (translation D (Finsupp.single q P)) =
      if q = p then ∑ i : Fin D.rank, chargeScalar D p i *
        P.coeff (Finsupp.single (i,0) 1) else 0 := by
  classical
  rw [translation_single]
  by_cases h : q = p
  · subst q
    simp only [ell, Finsupp.single_eq_same, if_true]
    have hc (i : Fin D.rank) : (chargePolynomial D p * P).coeff
        (Finsupp.single (i,1) 1) = 0 := by
      rw [chargePolynomial, Finset.sum_mul]
      simp only [smul_mul_assoc, MvPolynomial.coeff_sum, coeff_smul]
      apply Finset.sum_eq_zero
      intro j hj
      rw [mul_comm (X (j,0)) P, coeff_linear_mul_X]
      simp
    simp_rw [MvPolynomial.coeff_add, hc, add_zero, coeff_derivation_two]
    apply Finset.sum_congr rfl
    intro i hi
    rw [charge_scalar D p i]
  · simp [ell, h]

private theorem mode_mul_X (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (p : Charge D) (m : ℤ) (i : Fin D.rank) (k : ℕ) (P : Oscillator D) :
    sectorSugawaraMode D H p m (P * X (i,k)) =
      X (i,k) * sectorSugawaraMode D H p m P +
        ((k+1 : ℕ) : ℂ) • neutralPolynomialMode D i p (m - (k+1 : ℕ)) P := by
  have h := congrArg (fun A : Module.End ℂ (Carrier D) =>
      (A (Finsupp.single p P)) p)
    (sugawaraMode_current_commutator D H hHG hGH i m (-((k+1 : ℕ) : ℤ)))
  have hn : neutralPolynomialMode D i p (-((k+1 : ℕ) : ℤ)) =
      LinearMap.mulLeft ℂ (X (i,k)) := by
    rw [show -((k+1 : ℕ) : ℤ) = -(k : ℤ)-1 by omega]
    exact neutralPolynomialMode_negative D i p k
  simp only [LinearMap.sub_apply, Module.End.mul_apply, neutralMode_single,
    sugawaraMode_single_sector, LinearMap.smul_apply, Finsupp.sub_apply,
    Finsupp.single_eq_same, Finsupp.smul_apply, hn, LinearMap.mulLeft_apply] at h
  simp only [Int.cast_neg, neg_neg, Int.cast_natCast,
    show m + -((k+1 : ℕ) : ℤ) = m - ((k+1 : ℕ) : ℤ) by omega] at h
  rw [mul_comm P]
  exact (sub_eq_iff_eq_add.mp h).trans (by abel)

private theorem coeff_mode_one (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (p : Charge D) (P : Oscillator D) :
    (sectorSugawaraMode D H p 1 P).coeff 0 =
      ∑ i : Fin D.rank, chargeScalar D p i * P.coeff (Finsupp.single (i,0) 1) := by
  classical
  induction P using MvPolynomial.induction_on with
  | C c =>
    have hg := sugawaraMode_ground_positive D H p 1 (by omega)
    have hc : Finsupp.single p (C c : Oscillator D) =
        c • Finsupp.single p (1 : Oscillator D) := by simp [← C_mul']
    have hz := congrArg (fun x : Carrier D => x p) (show
        sugawaraMode D H 1 (Finsupp.single p (C c)) = 0 by rw [hc, map_smul, hg, smul_zero])
    have hx := congrArg (fun P : Oscillator D => P.coeff 0) hz
    have he (i : Fin D.rank) : (0 : Index D →₀ ℕ) ≠ Finsupp.single (i,0) 1 :=
      Ne.symm (Finsupp.single_ne_zero.mpr one_ne_zero)
    simpa [sugawaraMode_single_sector, he] using hx
  | add P Q hP hQ =>
    simp [hP, hQ, Finset.sum_add_distrib, mul_add]
  | mul_X P x hP =>
    rcases x with ⟨j,k⟩
    rw [mode_mul_X D H hHG hGH]
    simp only [MvPolynomial.coeff_add, coeff_smul]
    have hc : (X (j,k) * sectorSugawaraMode D H p 1 P).coeff 0 = 0 := by
      rw [← constantCoeff_eq]
      simp
    rw [hc, zero_add]
    cases k with
    | zero =>
      simp [neutralPolynomialMode, chargeScalar, coeff_linear_mul_X,
        constantCoeff_eq, eq_comm]
    | succ k =>
      have hn : (1 : ℤ) - ((k+1+1 : ℕ) : ℤ) = -(k : ℤ)-1 := by omega
      rw [hn, neutralPolynomialMode_negative]
      simp [LinearMap.mulLeft_apply, coeff_linear_mul_X, ← constantCoeff_eq]


private theorem ell_translation (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (p : Charge D) (u : Carrier D) :
    ell D p (translation D u) = ((sugawaraMode D H 1 u) p).coeff 0 := by
  classical
  induction u using Finsupp.induction_linear with
  | zero => simp [ell]
  | add x y hx hy =>
    simpa [ell, mul_add, Finset.sum_add_distrib] using congrArg₂ (· + ·) hx hy
  | single q P =>
    rw [ell_translation_single, sugawaraMode_single_sector]
    by_cases h : q = p
    · subst q; simp [coeff_mode_one D H hHG hGH]
    · simp [h, Finsupp.single_eq_of_ne h]

private theorem current_two_constant (D : LatticeData) (p : Charge D)
    (i : Fin D.rank) (P : Oscillator D) :
    (neutralPolynomialMode D i p 2 P).coeff 0 =
      2 * ∑ j : Fin D.rank, (D.G i j : ℂ) * P.coeff (Finsupp.single (j,1) 1) := by
  simp [neutralPolynomialMode, coeff_pderiv]

private theorem current_two_extracts_ell (D : LatticeData) (p : Charge D)
    (P : Oscillator D) :
    ∑ i : Fin D.rank, (p i : ℂ) * (neutralPolynomialMode D i p 2 P).coeff 0 =
      2 * ell D p (Finsupp.single p P) := by
  classical
  simp only [current_two_constant, ell, Finsupp.single_eq_same, Finset.sum_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [D.symmetric j i]
  ring

private theorem charge_norm (D : LatticeData) (p : Charge D) :
    ∑ i : Fin D.rank, (p i : ℂ) * chargeScalar D p i = (bilinear D p p : ℂ) := by
  simp only [charge_scalar, bilinear, Int.cast_sum, Int.cast_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

private theorem ell_minus_two (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (p : Charge D) :
    ell D p (sugawaraMode D H (-2) (Finsupp.single p 1)) = (bilinear D p p : ℂ) := by
  classical
  have hc (i : Fin D.rank) :
      (neutralPolynomialMode D i p 2 (sectorSugawaraMode D H p (-2) 1)).coeff 0 =
        2 * chargeScalar D p i := by
    have h := congrArg (fun A : Module.End ℂ (Carrier D) =>
      ((A (Finsupp.single p 1)) p).coeff 0)
      (sugawaraMode_current_commutator D H hHG hGH i (-2) 2)
    have hz : neutralMode D i 2 (Finsupp.single p (1 : Oscillator D)) = 0 := by
      simp [neutralPolynomialMode]
    simp only [LinearMap.sub_apply, Module.End.mul_apply, hz, map_zero,
      sugawaraMode_single_sector, neutralMode_single, Finsupp.sub_apply,
      Finsupp.zero_apply, Finsupp.single_eq_same, coeff_sub, MvPolynomial.coeff_zero,
      LinearMap.smul_apply, Finsupp.smul_apply, coeff_smul] at h
    norm_num [neutralPolynomialMode, chargeScalar] at h ⊢
    exact h
  rw [sugawaraMode_single_sector]
  have he := current_two_extracts_ell D p (sectorSugawaraMode D H p (-2) 1)
  simp_rw [hc] at he
  have hs : (∑ i : Fin D.rank, (p i : ℂ) * (2 * chargeScalar D p i)) =
      2 * (bilinear D p p : ℂ) := by
    rw [← charge_norm D p, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hs] at he
  linear_combination -he / 2

private theorem ell_translation_squared (D : LatticeData) (p : Charge D) :
    ell D p (translation D (translation D (Finsupp.single p 1))) =
      (bilinear D p p : ℂ) := by
  classical
  have tv : translation D (Finsupp.single p (1 : Oscillator D)) =
      Finsupp.single p (chargePolynomial D p) := by simp
  rw [tv, ell_translation_single]
  simp only [ite_true]
  have hc (i : Fin D.rank) : (chargePolynomial D p).coeff (Finsupp.single (i,0) 1) =
      (p i : ℂ) := by
    simp [chargePolynomial, MvPolynomial.coeff_sum, coeff_X,
      Finsupp.single_left_inj (by norm_num : (1 : ℕ) ≠ 0), eq_comm]
  simp_rw [hc, mul_comm (chargeScalar D p _) (p _ : ℂ)]
  exact charge_norm D p

/-- The literal original Type II vector, with its original charge and oscillator carrier. -/
def typeII (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (p : Charge D) : Carrier D :=
  sugawaraMode D H (-2) (Finsupp.single p 1) +
    (3/2 : ℂ) • translation D (translation D (Finsupp.single p 1))

private theorem ell_typeII (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (p : Charge D) (hp : bilinear D p p = -2) :
    ell D p (typeII D H p) = -5 := by
  have ha (x y : Carrier D) : ell D p (x+y) = ell D p x + ell D p y := by
    simp [ell, mul_add, Finset.sum_add_distrib]
  have hs (c : ℂ) (x : Carrier D) : ell D p (c • x) = c * ell D p x := by
    simp [ell, Finset.mul_sum, mul_left_comm, mul_assoc]
  rw [typeII, ha, hs, ell_minus_two D H hHG hGH, ell_translation_squared, hp]
  norm_num


private theorem typeII_primary (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (hr : D.rank = 26) (p : Charge D) (hp : bilinear D p p = -2) :
    sugawaraMode D H 0 (typeII D H p) = typeII D H p ∧
      ∀ n : ℤ, 0 < n → sugawaraMode D H n (typeII D H p) = 0 := by
  let L := sugawaraMode D H
  let v : Carrier D := Finsupp.single p 1
  have ground (m : ℤ) (hm : 0 < m) : L m v = 0 :=
    sugawaraMode_ground_positive D H p m hm
  have weight : L 0 v = (-1 : ℂ) • v := by
    dsimp [L,v]
    rw [sugawaraMode_ground_zero, chargeQuadratic_eq D H hHG hGH, hp]
    norm_num
  have comm (m n : ℤ) (x : Carrier D) :
      L m (L n x) = L n (L m x) + ((m-n : ℤ) : ℂ) • L (m+n) x +
        (if m+n = 0 then (D.rank : ℂ)/12*((m : ℂ)^3-m) else 0) • x := by
    have h := congrArg (fun A : Module.End ℂ (Carrier D) => A x)
      (sugawaraMode_virasoro D H hHG hGH m n)
    simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.add_apply,
      LinearMap.smul_apply, Module.End.one_apply] at h
    dsimp [L]
    rw [sub_eq_iff_eq_add] at h
    exact h.trans (by abel)
  have zero_one : L 0 (L (-1) v) = 0 := by
    rw [comm, weight]
    norm_num <;> module
  have zero_two : L 0 (L (-2) v) = L (-2) v := by
    rw [comm, weight]
    norm_num <;> module
  have zero_one_one : L 0 (L (-1) (L (-1) v)) = L (-1) (L (-1) v) := by
    rw [comm, zero_one]
    norm_num
  have one_one : L 1 (L (-1) v) = (-2 : ℂ) • v := by
    rw [comm, ground 1 (by omega)]
    norm_num [weight]
  have one_two : L 1 (L (-2) v) = (3 : ℂ) • L (-1) v := by
    rw [comm, ground 1 (by omega)]
    norm_num
  have one_one_one : L 1 (L (-1) (L (-1) v)) = (-2 : ℂ) • L (-1) v := by
    rw [comm, one_one]
    norm_num [zero_one]
  have higher_one (n : ℤ) (hn : 1 < n) : L n (L (-1) v) = 0 := by
    rw [comm, ground n (by omega), ground (n + -1) (by omega)]
    simp [show n + -1 ≠ 0 by omega]
  have two_two : L 2 (L (-2) v) = (9 : ℂ) • v := by
    rw [comm, ground 2 (by omega)]
    norm_num [hr, weight] <;> module
  have two_one_one : L 2 (L (-1) (L (-1) v)) = (-6 : ℂ) • v := by
    rw [comm, higher_one 2 (by omega)]
    norm_num [one_one, smul_smul]
  have high_two (n : ℤ) (hn : 2 < n) : L n (L (-2) v) = 0 := by
    rw [comm, ground n (by omega), ground (n + -2) (by omega)]
    simp [show n + -2 ≠ 0 by omega]
  have high_one_one (n : ℤ) (hn : 2 < n) : L n (L (-1) (L (-1) v)) = 0 := by
    rw [comm, higher_one n (by omega), higher_one (n + -1) (by omega)]
    simp [show n + -1 ≠ 0 by omega]
  have hT := sugawaraMode_minus_one_eq_translation D H hHG hGH
  rw [typeII, ← hT]
  change L 0 (L (-2) v + (3/2 : ℂ) • L (-1) (L (-1) v)) =
      L (-2) v + (3/2 : ℂ) • L (-1) (L (-1) v) ∧
    ∀ n : ℤ, 0 < n → L n (L (-2) v + (3/2 : ℂ) • L (-1) (L (-1) v)) = 0
  constructor
  · simp [zero_two, zero_one_one]
  · intro n hn
    by_cases h1 : n = 1
    · subst n
      simp only [map_add, map_smul, one_two, one_one_one, smul_smul]
      rw [← add_smul]
      norm_num
    · by_cases h2 : n = 2
      · subst n
        simp only [map_add, map_smul, two_two, two_one_one, smul_smul]
        rw [← add_smul]
        norm_num
      · simp [high_two n (by omega), high_one_one n (by omega)]

/-- At rank 26 and norm -2, the original Type II state is a nonzero physical
null state outside the translation of even the kernel of L(1).
The image in the last clause is the literal original positive-primary weight-zero space. -/
theorem original_typeII_null_obstruction (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (hr : D.rank = 26) (p : Charge D) (hp : bilinear D p p = -2) :
    sugawaraMode D H 0 (typeII D H p) = typeII D H p ∧
    (∀ n : ℤ, 0 < n → sugawaraMode D H n (typeII D H p) = 0) ∧
    (∀ w : Carrier D, (∀ n : ℤ, 0 < n → sugawaraMode D H n w = 0) →
      Hm (typeII D H p) w = 0) ∧
    typeII D H p ≠ 0 ∧
    (∀ u : Carrier D, sugawaraMode D H 1 u = 0 → translation D u ≠ typeII D H p) ∧
    typeII D H p ∉ (translation D) ''
      {u : Carrier D | sugawaraMode D H 0 u = 0 ∧
        ∀ n : ℤ, 0 < n → sugawaraMode D H n u = 0} := by
  have hprimary := typeII_primary D H hHG hGH hr p hp
  have hcoeff := ell_typeII D H hHG hGH p hp
  have hnonzero : typeII D H p ≠ 0 := by
    intro h
    rw [h] at hcoeff
    norm_num [ell] at hcoeff
  have hnot (u : Carrier D) (hu : sugawaraMode D H 1 u = 0) :
      translation D u ≠ typeII D H p := by
    intro h
    have hzero := ell_translation D H hHG hGH p u
    rw [hu, Finsupp.zero_apply, h, hcoeff] at hzero
    simp only [MvPolynomial.coeff_zero, Pi.zero_apply] at hzero
    norm_num at hzero
  refine ⟨hprimary.1, hprimary.2, ?_, hnonzero, hnot, ?_⟩
  · intro w hw
    rw [typeII, Hm_add_left, Hm_smul_left]
    have hT := sugawaraMode_minus_one_eq_translation D H hHG hGH
    rw [← hT, Hm_sugawaraMode H hHG hGH,
      Hm_sugawaraMode H hHG hGH, Hm_sugawaraMode H hHG hGH]
    norm_num [hw 2 (by omega), hw 1 (by omega)]
  · rintro ⟨u,hu,htu⟩
    exact hnot u (hu.2 1 (by omega)) htu

open scoped TensorProduct
open LatticeMatterGhostCoupling LatticeBRST LatticeRelativeMassShell
open D5.S3.Quantum.Fermionic
open CountableOccupationFock
open BcGhostFock
open private c_swap from D5.S3.Quantum.Fermionic.BcGhostCubic
open private coeff_zero from D5.S3.VertexAlgebra.Lattice.LatticeRelativeMassShell
open private number_ket from D5.S3.Quantum.Fermionic.BcGhostCharge
open private L_vacuum from D5.S3.Quantum.Fermionic.BcGhostVirasoro

private theorem ghost_R_one_vacuum : BcGhostBRST.R 1 vacuum = ket {1,3} := by
  classical
  change (∑ᶠ j : ℤ, BcGhostBRST.rTerm 1 j vacuum) = _
  have ht (j : ℤ) (hj : j ∉ ({0,1} : Finset ℤ)) :
      BcGhostBRST.rTerm 1 j vacuum = 0 := by
    have hj01 : j ≠ 0 ∧ j ≠ 1 := by simpa using hj
    obtain ⟨hj0,hj1⟩ := hj01
    by_cases hjp : 2 ≤ j
    · rw [BcGhostBRST.rTerm, c_swap j (1-j)]
      simp [Module.End.mul_apply, ghost_vacuum.2.1 j hjp]
    · have hq : 2 ≤ 1-j := by omega
      simp [BcGhostBRST.rTerm, Module.End.mul_apply, ghost_vacuum.2.1 (1-j) hq]
  rw [finsum_eq_sum_of_support_subset _ (s := ({0,1} : Finset ℤ)) (by
    intro j hj
    by_contra hn
    exact hj (ht j hn))]
  norm_num [BcGhostBRST.rTerm, Module.End.mul_apply, c, vacuum, create_ket,
    phase, lowerCount, Finset.filter_insert, Finset.filter_singleton,
    Finset.insert_comm, Finset.pair_comm, smul_smul]
  module

private theorem ghost_Q_down : BcGhostBRST.Qg (ket {1}) = ket {1,3} := by
  have h := LinearMap.congr_fun (BcGhostBRST.ward_c 1) vacuum
  simpa only [LinearMap.add_apply, Module.End.mul_apply, ghost_vacuum.2.2.1,
    BcGhostBRST.Qg_vacuum, map_zero, add_zero, ghost_R_one_vacuum] using h

private theorem ghost_L_minus_two_down :
    BcGhostVirasoro.L (-2) (ket {1}) =
      (2 : ℂ) • ket {0,1,3} + (3 : ℂ) • ket {5} := by
  have h := LinearMap.congr_fun (BcGhostVirasoro.ward_c (-2) 1) vacuum
  have hv : BcGhostVirasoro.L (-2) vacuum =
      (-2 : ℂ) • ket {0,3} + ket {1,2} := by
    rw [L_vacuum]
    have hi : Finset.Icc (0 : ℤ) 1 = {0,1} := by decide
    norm_num [hi, b, c, vacuum, create_ket,
      phase, lowerCount, Finset.filter_insert, Finset.filter_singleton,
      Finset.insert_comm, Finset.pair_comm, map_smul, smul_smul]
    module
  simp only [LinearMap.sub_apply, Module.End.mul_apply, ghost_vacuum.2.2.1,
    LinearMap.smul_apply] at h
  rw [hv] at h
  norm_num [b, c, vacuum, create_ket, phase, lowerCount, Finset.filter_insert,
    Finset.filter_singleton, Finset.insert_comm, Finset.pair_comm, map_sub, map_smul,
    smul_smul] at h
  rw [show ({1,3,0} : Finset ℕ) = {0,1,3} by decide] at h
  have h' : BcGhostVirasoro.L (-2) (ket {1}) -
      (2 : ℂ) • ket {0,1,3} = (3 : ℂ) • ket {5} := h
  exact (sub_eq_iff_eq_add.mp h').trans (by module)

private theorem charge_on_vacuum (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (x : Carrier D)
    (hx : ∀ n : ℤ, 1 < n → sugawaraMode D H n x = 0) :
    totalCharge D H (x ⊗ₜ[ℂ] vacuum) =
      sugawaraMode D H (-1) x ⊗ₜ[ℂ] ket {1} +
      sugawaraMode D H 0 x ⊗ₜ[ℂ] ket {3} +
      sugawaraMode D H 1 x ⊗ₜ[ℂ] ket {5} := by
  classical
  have hs : Function.support (fun m : ℤ =>
      summand D H m (x ⊗ₜ[ℂ] vacuum)) ⊆ (({-1,0,1} : Finset ℤ) : Set ℤ) := by
    intro m hm
    by_contra hn
    have hmneq : m ≠ -1 ∧ m ≠ 0 ∧ m ≠ 1 := by simpa using hn
    obtain ⟨hm1,hm0,hmone⟩ := hmneq
    by_cases hlo : m < -1
    · exact hm (by simp [summand, ghost_vacuum.2.1 (-m) (by omega)])
    · exact hm (by simp [summand, hx m (by omega)])
  rw [totalCharge, LinearMap.add_apply, finite_capture D H _ _ hs]
  simp only [ghostCharge, TensorProduct.map_tmul, LinearMap.id_apply,
    BcGhostBRST.Qg_vacuum, TensorProduct.tmul_zero, add_zero]
  norm_num [summand, c, vacuum, create_ket, phase, lowerCount, add_assoc]

private theorem charge_on_primary_down (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (x : Carrier D) (h : ℂ)
    (h0 : sugawaraMode D H 0 x = h • x)
    (hx : ∀ n : ℤ, 0 < n → sugawaraMode D H n x = 0) :
    totalCharge D H (x ⊗ₜ[ℂ] ket {1}) =
      (1-h) • (x ⊗ₜ[ℂ] ket {1,3}) := by
  classical
  have hs : Function.support (fun m : ℤ =>
      summand D H m (x ⊗ₜ[ℂ] ket {1})) ⊆ (({0} : Finset ℤ) : Set ℤ) := by
    intro m hm
    by_contra hn
    have hm0 : m ≠ 0 := by simpa using hn
    by_cases hp : 0 < m
    · exact hm (by simp [summand, hx m hp])
    · have hmle : m ≤ -1 := by omega
      by_cases he : m = -1
      · subst m
        exact hm (by norm_num [summand, c, create_ket])
      · have hc : ¬ -m ≤ 1 := by omega
        have hj : 2 * (-m-2).toNat ≠ 1 := by omega
        exact hm (by simp [summand, c, hc, annihilate_ket, hj])
  rw [totalCharge, LinearMap.add_apply, finite_capture D H _ _ hs]
  simp only [Finset.sum_singleton, summand, TensorProduct.map_tmul, neg_zero,
    h0, ghostCharge, LinearMap.id_apply, ghost_Q_down]
  norm_num [c, create_ket, phase, lowerCount, Finset.filter_singleton,
    Finset.pair_comm]
  simp only [← TensorProduct.smul_tmul', TensorProduct.tmul_smul,
    TensorProduct.tmul_neg, TensorProduct.neg_tmul]
  module

/-- The literal relative ghost-number-zero primitive for the same Type II state. -/
def typeIIPrimitive (D : LatticeData) (p : Charge D) : State D :=
  (3/2 : ℂ) • (translation D (Finsupp.single p 1) ⊗ₜ[ℂ] vacuum) +
    Finsupp.single p 1 ⊗ₜ[ℂ] ket {0,1}

private theorem ground_translation_modes (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (p : Charge D) (hp : bilinear D p p = -2) :
    let v : Carrier D := Finsupp.single p 1
    sugawaraMode D H 0 v = (-1 : ℂ) • v ∧
    sugawaraMode D H 0 (translation D v) = 0 ∧
    sugawaraMode D H 1 (translation D v) = (-2 : ℂ) • v ∧
    ∀ n : ℤ, 1 < n → sugawaraMode D H n (translation D v) = 0 := by
  let v : Carrier D := Finsupp.single p 1
  have hv : sugawaraMode D H 0 v = (-1 : ℂ) • v := by
    dsimp [v]
    rw [sugawaraMode_ground_zero, chargeQuadratic_eq D H hHG hGH, hp]
    norm_num
  have hc (m : ℤ) :
      sugawaraMode D H m (sugawaraMode D H (-1) v) =
        sugawaraMode D H (-1) (sugawaraMode D H m v) +
        ((m+1 : ℤ) : ℂ) • sugawaraMode D H (m-1) v +
        (if m-1 = 0 then (D.rank : ℂ)/12*((m : ℂ)^3-m) else 0) • v := by
    have h := LinearMap.congr_fun (sugawaraMode_virasoro D H hHG hGH m (-1)) v
    simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.add_apply,
      LinearMap.smul_apply, Module.End.one_apply, sub_neg_eq_add] at h
    rw [show m + -1 = m - 1 by omega] at h
    exact (sub_eq_iff_eq_add.mp h).trans (by module)
  have ht := sugawaraMode_minus_one_eq_translation D H hHG hGH
  refine ⟨hv, ?_, ?_, ?_⟩
  · rw [← ht, hc, hv]
    norm_num
  · rw [← ht, hc, sugawaraMode_ground_positive D H p 1 (by omega)]
    norm_num [hv, v]
  · intro n hn
    rw [← ht, hc, sugawaraMode_ground_positive D H p n (by omega),
      sugawaraMode_ground_positive D H p (n-1) (by omega)]
    simp [show n-1 ≠ 0 by omega]

private theorem primitive_charge (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (p : Charge D) (hp : bilinear D p p = -2) :
    totalCharge D H (typeIIPrimitive D p) = typeII D H p ⊗ₜ[ℂ] ket {1} := by
  let v : Carrier D := Finsupp.single p 1
  obtain ⟨hv, ht0, ht1, hthigh⟩ := ground_translation_modes D H hHG hGH p hp
  have hqv := charge_on_primary_down D H v (-1) hv
    (fun n hn => sugawaraMode_ground_positive D H p n hn)
  have hqt : totalCharge D H (translation D v ⊗ₜ[ℂ] vacuum) =
      translation D (translation D v) ⊗ₜ[ℂ] ket {1} -
        (2 : ℂ) • (v ⊗ₜ[ℂ] ket {5}) := by
    rw [charge_on_vacuum D H _ hthigh, ht0, ht1,
      sugawaraMode_minus_one_eq_translation D H hHG hGH]
    simp only [TensorProduct.zero_tmul, add_zero, ← TensorProduct.smul_tmul']
    module
  have hb1 : b (-2) (ket {1}) = ket {0,1} := by
    norm_num [b, create_ket, phase, lowerCount]
  have hb13 : b (-2) (ket {1,3}) = ket {0,1,3} := by
    norm_num [b, create_ket, phase, lowerCount]
  have hw := LinearMap.congr_fun (total_ward_b D H (-2)) (v ⊗ₜ[ℂ] ket {1})
  simp only [LinearMap.add_apply, Module.End.mul_apply, ghostB, matterMode,
    ghostVirasoro, TensorProduct.map_tmul, LinearMap.id_apply, hb1,
    ghost_L_minus_two_down] at hw
  rw [hqv] at hw
  norm_num only [sub_neg_eq_add, one_add_one_eq_two] at hw
  simp only [map_smul, TensorProduct.map_tmul, LinearMap.id_apply, hb13,
    TensorProduct.tmul_add, TensorProduct.tmul_smul] at hw
  have hqb : totalCharge D H (v ⊗ₜ[ℂ] ket {0,1}) =
      sugawaraMode D H (-2) v ⊗ₜ[ℂ] ket {1} +
        (3 : ℂ) • (v ⊗ₜ[ℂ] ket {5}) := by
    calc
      _ = (totalCharge D H (v ⊗ₜ[ℂ] ket {0,1}) +
          (2 : ℂ) • (v ⊗ₜ[ℂ] ket {0,1,3})) -
          (2 : ℂ) • (v ⊗ₜ[ℂ] ket {0,1,3}) := by abel
      _ = _ := by rw [hw]; module
  rw [typeIIPrimitive, map_add, map_smul, hqt, hqb, typeII]
  simp only [TensorProduct.add_tmul, ← TensorProduct.smul_tmul']
  module

private theorem single_tensor_fixed (D : LatticeData) (p : Charge D)
    (P : Oscillator D) (g : Fock) :
    Finsupp.single p P ⊗ₜ[ℂ] g ∈ fixedMomentum D p := by
  apply (mem_fixedMomentum_iff D p _).mpr
  rintro ⟨⟨q,e⟩,S⟩ hq
  rw [coeff_tmul_original]
  simp [Ne.symm hq]

private theorem primitive_relative (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (p : Charge D) (hp : bilinear D p p = -2) :
    typeIIPrimitive D p ∈ relativeMassShell D H p ∧
    TensorProduct.map (LinearMap.id : Module.End ℂ (Carrier D))
      BcGhostCharge.ghostNumber (typeIIPrimitive D p) = 0 := by
  obtain ⟨hv, ht0, ht1, hthigh⟩ := ground_translation_modes D H hHG hGH p hp
  have hfix : typeIIPrimitive D p ∈ fixedMomentum D p := by
    apply (fixedMomentum D p).add_mem
    · apply (fixedMomentum D p).smul_mem
      rw [translation_single]
      exact single_tensor_fixed D p _ _
    · exact single_tensor_fixed D p _ _
  have hb : ghostB D 0 (typeIIPrimitive D p) = 0 := by
    norm_num [typeIIPrimitive, ghostB, TensorProduct.map_tmul, b, vacuum,
      annihilate_ket, map_add, map_smul]
  have hg0 : BcGhostVirasoro.L 0 vacuum = 0 := by
    rw [vacuum, BcGhostRelativeEnergy.L_zero_ket]
    simp [BcGhostRelativeEnergy.energy]
  have hg01 : BcGhostVirasoro.L 0 (ket {0,1}) = ket {0,1} := by
    rw [BcGhostRelativeEnergy.L_zero_ket]
    norm_num [BcGhostRelativeEnergy.energy, BcGhostRelativeEnergy.siteEnergy,
      BcGhostCharge.siteMode, BcGhostCharge.siteSign]
  have hl : totalL0 D H (typeIIPrimitive D p) = 0 := by
    simp only [typeIIPrimitive, map_add, map_smul, totalL0, LinearMap.add_apply,
      matterMode, ghostVirasoro, TensorProduct.map_tmul, LinearMap.id_apply,
      hv, ht0, hg0, hg01, TensorProduct.zero_tmul, TensorProduct.tmul_zero,
      ← TensorProduct.smul_tmul']
    module
  refine ⟨⟨⟨hfix,hb⟩,hl⟩, ?_⟩
  norm_num [typeIIPrimitive, TensorProduct.map_tmul, number_ket,
    BcGhostCharge.charge, vacuum, map_add, map_smul, Finset.filter_insert,
    Finset.filter_singleton]

/-- An explicit relative primitive for the literal nontranslation Type II state,
with the original, unshifted ghost numbers and zero mode on both sides. -/
theorem original_typeII_relative_boundary (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (hr : D.rank = 26) (p : Charge D) (hp : bilinear D p p = -2) :
    totalCharge D H (typeIIPrimitive D p) = typeII D H p ⊗ₜ[ℂ] ket {1} ∧
    typeIIPrimitive D p ∈ relativeMassShell D H p ∧
    TensorProduct.map (LinearMap.id : Module.End ℂ (Carrier D))
      BcGhostCharge.ghostNumber (typeIIPrimitive D p) = 0 ∧
    typeII D H p ⊗ₜ[ℂ] ket {1} ∈ relativeMassShell D H p ∧
    TensorProduct.map (LinearMap.id : Module.End ℂ (Carrier D))
      BcGhostCharge.ghostNumber (typeII D H p ⊗ₜ[ℂ] ket {1}) =
      typeII D H p ⊗ₜ[ℂ] ket {1} ∧
    totalCharge D H (typeII D H p ⊗ₜ[ℂ] ket {1}) = 0 ∧
    typeII D H p ⊗ₜ[ℂ] ket {1} ≠ 0 := by
  classical
  obtain ⟨h0,hpos,horth,hne,hnot,hnotP0⟩ :=
    original_typeII_null_obstruction D H hHG hGH hr p hp
  obtain ⟨hu,hnum⟩ := primitive_relative D H hHG hGH p hp
  have hfix : typeII D H p ⊗ₜ[ℂ] ket {1} ∈ fixedMomentum D p := by
    apply (mem_fixedMomentum_iff D p _).mpr
    rintro ⟨⟨q,e⟩,S⟩ hq
    rw [coeff_tmul_original]
    simp [typeII, sugawaraMode_single_sector, translation_single, Ne.symm hq]
  have hb : ghostB D 0 (typeII D H p ⊗ₜ[ℂ] ket {1}) = 0 := by
    simp [ghostB, TensorProduct.map_tmul, BcGhostRelativeEnergy.b_zero_down]
  have hg : BcGhostVirasoro.L 0 (ket {1}) = -(ket {1}) := by
    simpa only [ghost_vacuum.2.2.1] using BcGhostRelativeEnergy.L_zero_down
  have hl : totalL0 D H (typeII D H p ⊗ₜ[ℂ] ket {1}) = 0 := by
    simp [totalL0, matterMode, ghostVirasoro, TensorProduct.map_tmul, h0, hg,
      TensorProduct.tmul_neg]
  have hnumout : TensorProduct.map (LinearMap.id : Module.End ℂ (Carrier D))
      BcGhostCharge.ghostNumber (typeII D H p ⊗ₜ[ℂ] ket {1}) =
      typeII D H p ⊗ₜ[ℂ] ket {1} := by
    norm_num [TensorProduct.map_tmul, number_ket, BcGhostCharge.charge,
      Finset.filter_singleton]
  have hcycle : totalCharge D H (typeII D H p ⊗ₜ[ℂ] ket {1}) = 0 := by
    rw [charge_on_primary_down D H _ 1 (by simpa using h0) hpos]
    simp
  have hnonzero : typeII D H p ⊗ₜ[ℂ] ket {1} ≠ 0 := by
    intro hz
    apply hne
    apply Finsupp.ext
    intro q
    apply MvPolynomial.ext
    intro e
    have hc := congrArg (fun x : State D =>
      LatticeRelativeMassShell.coeff D x ((q,e),{1})) hz
    rw [coeff_tmul_original, coeff_zero] at hc
    simpa only [ket, Finsupp.single_eq_same, mul_one, Finsupp.zero_apply,
      MvPolynomial.coeff_zero] using hc
  exact ⟨primitive_charge D H hHG hGH p hp, hu, hnum, ⟨⟨hfix,hb⟩,hl⟩,
    hnumout, hcycle, hnonzero⟩

end
end D5.S3.VertexAlgebra.LatticeOriginalTypeIINullState
