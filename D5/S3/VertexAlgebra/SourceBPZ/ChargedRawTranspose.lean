/- GID: D5/S3/VertexAlgebra/SourceBPZ/ChargedRawTranspose
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/SourceBPZ/ChargedRawTranspose
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Algebra.MvPolynomial.PDeriv]
   utility: none
   digest: Finite integer Wick induction for the original charged raw transpose. -/

import D5.S3.VertexAlgebra.SourceBPZ.OriginalSourcePairing

/-!
The standard lattice-VOA invariant bilinear form calculation is performed on
the original integer oscillator and finite-charge carrier. The finite Wick
induction adapts SignedOscillatorWick.creation_translation_adjoint, with the
actual integer creation and translation suppliers. The lattice field formulas
are those of Bakalov--Kac, arXiv math/0402315v1, section 4.1.
All declarations concern universally quantified algebraic identities proved
by polynomial induction and finite-support linearity. None is a bounded
enumeration, checker, numeric reduction or certified finite instance; hence
the computational utility classification is none.
No claim of literature novelty or all-state BPZ is made.
-/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators

namespace D5.S3.VertexAlgebra.SourceBPZ.ChargedRawTranspose

open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration
open LatticeActualGeneratorLocality LatticeActualProductKernel
open LatticeActualAnnihilation OriginalSourcePairing MvPolynomial
open private wick_constant_right from
  D5.S3.VertexAlgebra.TwistedGround.SignedOscillatorWick

private theorem epsilon_reflection (D : LatticeData) (a d : Charge D) :
    epsilon D a d = paritySign (bilinear D a a / 2) * epsilon D a (-a-d) := by
  have hn (b : Charge D) : epsilon D a (-b) = epsilon D a b := by
    have he : lowerCocycleExponent D a (-b) = -lowerCocycleExponent D a b := by
      simp [lowerCocycleExponent, Finset.sum_neg_distrib, add_comm]
    simp only [epsilon, he, paritySign, even_neg]
  rw [show -a-d = -(a+d) by abel, hn, epsilon_add_right]
  simp only [epsilon,
    LatticeTwistedGroundRealization.SignQuotient.integral_cocycle_square]
  rw [← mul_assoc, paritySign_square, one_mul]

private def translatedCoeff (D : LatticeData) (a : Charge D) (n : ℤ)
    (p : Oscillator D) : Oscillator D :=
  if n < 0 then 0 else (translatedPolynomial D a p).coeff n.toNat

private theorem creation_constant (D : LatticeData) (a : Charge D) (n : ℤ) :
    (creationCoeff D a n).coeff 0 = if n = 0 then 1 else 0 := by
  classical
  by_cases negative : n < 0
  · simp [creationCoeff, negative, show n ≠ 0 by omega]
  by_cases zero : n = 0
  · subst n
    simp [creationCoeff, LatticeSugawaraConformal.exponential_constant]
  · rw [ite_eq_right zero]
    by_contra nonzero
    have degree := ((actual_creation_coefficient_transport D a a).1 n) nonzero
    have : n.toNat = 0 := by simpa using degree.symm
    omega

private theorem translated_variable (D : LatticeData) (a : Charge D) (n : ℤ)
    (i : Fin D.rank) (k : ℕ) (p : Oscillator D) :
    translatedCoeff D a n (X (i,k) * p) =
      X (i,k) * translatedCoeff D a n p -
        (bilinear D a (unitCharge D i) : ℂ) •
          translatedCoeff D a (n - (k+1 : ℕ)) p := by
  classical
  by_cases negative : n < 0
  · have shifted : n - (k+1 : ℕ) < 0 := by omega
    simp only [translatedCoeff, ite_eq_left negative, ite_eq_left shifted,
      mul_zero, smul_zero, sub_zero]
  · have translated : translatedPolynomial D a (X (i,k) * p) =
        Polynomial.C (X (i,k) : Oscillator D) * translatedPolynomial D a p -
        Polynomial.C ((bilinear D a (unitCharge D i) : ℂ) • (1 : Oscillator D)) *
          (Polynomial.X ^ (k+1) * translatedPolynomial D a p) := by
      simp only [translatedPolynomial, map_mul, MvPolynomial.eval₂Hom_X',
        translationVariable]
      ring
    rw [translatedCoeff, ite_eq_right negative, translated, Polynomial.coeff_sub,
      Polynomial.coeff_C_mul, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_mul']
    by_cases bound : k+1 ≤ n.toNat
    · have shifted : ¬ n - (k+1 : ℕ) < 0 := by omega
      have hn : (n - (k+1 : ℕ)).toNat = n.toNat - (k+1) := by omega
      simp only [bound, ite_true, translatedCoeff, negative, shifted, ite_false, hn,
        smul_mul_assoc, one_mul]
    · have shifted : n - (k+1 : ℕ) < 0 := by omega
      simp only [bound, ite_false, translatedCoeff, negative, shifted, ite_true,
        smul_zero, mul_zero, sub_zero]

private theorem lowering_creation_product (D : LatticeData) (a : Charge D) (n : ℤ)
    (i : Fin D.rank) (k : ℕ) (p : Oscillator D) :
    -((k : ℂ)+1) • annihilate D i k (creationCoeff D a n * p) =
      creationCoeff D a n * (-((k : ℂ)+1) • annihilate D i k p) -
        (bilinear D a (unitCharge D i) : ℂ) •
          (creationCoeff D a (n - (k+1 : ℕ)) * p) := by
  have hn : (k+1 : ℂ) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero k)
  rw [annihilate_mul, annihilation_creation,
    bilinear_symmetric D (unitCharge D i) a]
  simp only [smul_add, smul_mul_assoc, smul_smul]
  simp only [Nat.cast_add, Nat.cast_one]
  rw [show -((k : ℂ)+1) * (((k : ℂ)+1)⁻¹ *
      (bilinear D a (unitCharge D i) : ℂ)) =
      -(bilinear D a (unitCharge D i) : ℂ) by field_simp]
  simp only [Algebra.smul_def, map_neg]
  ring

private theorem integer_constant_right (D : LatticeData) (c : ℂ) (p : Oscillator D) :
    integerWick D p (C c) = c * p.coeff 0 := by
  rw [integerWick_apply, wick_constant_right, retune_constant]

private theorem creation_translation_adjoint (D : LatticeData) (a : Charge D)
    (n : ℤ) (p q : Oscillator D) :
    integerWick D (creationCoeff D a n * p) q =
      integerWick D p (translatedCoeff D a n q) := by
  classical
  induction q using MvPolynomial.induction_on generalizing p n with
  | C c =>
    rw [integer_constant_right]
    change c * MvPolynomial.constantCoeff (creationCoeff D a n * p) = _
    rw [map_mul]
    change c * ((creationCoeff D a n).coeff 0 * p.coeff 0) = _
    rw [creation_constant]
    by_cases negative : n < 0
    · simp [translatedCoeff, negative, show n ≠ 0 by omega]
    · by_cases zero : n = 0
      · subst n
        simp only [translatedCoeff, show ¬ (0 : ℤ) < 0 by omega, ite_false, ite_true,
          one_mul, Int.toNat_zero,
          translatedPolynomial, MvPolynomial.eval₂Hom_C, RingHom.comp_apply,
          Polynomial.coeff_C_zero]
        exact (integer_constant_right D c p).symm
      · have nat_zero : n.toNat ≠ 0 := by omega
        simp [translatedCoeff, negative, translatedPolynomial, Polynomial.coeff_C,
          zero, nat_zero]
  | add q r hq hr =>
    simp only [map_add, hq, hr]
    by_cases negative : n < 0
    · simp [translatedCoeff, negative]
    · simp only [translatedCoeff, ite_eq_right negative, translatedPolynomial,
        map_add, Polynomial.coeff_add]
  | mul_X q x ih =>
    rcases x with ⟨i,k⟩
    rw [mul_comm q, ← integerWick_lowering, lowering_creation_product]
    simp only [map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply]
    rw [ih, ih, integerWick_lowering, ← map_smul, ← map_sub,
      ← translated_variable]

private theorem translated_as_supported_sum (D : LatticeData) (a : Charge D)
    (n : ℤ) (p : Oscillator D) :
    translatedCoeff D a n p =
      ∑ c ∈ (translatedPolynomial D a p).support,
        if (c : ℤ) = n then (translatedPolynomial D a p).coeff c else 0 := by
  classical
  by_cases negative : n < 0
  · rw [translatedCoeff, ite_eq_left negative]
    symm
    apply Finset.sum_eq_zero
    intro c hc
    rw [ite_eq_right (by omega)]
  · rw [translatedCoeff, ite_eq_right negative]
    symm
    calc
      _ = if (n.toNat : ℤ) = n then
          (translatedPolynomial D a p).coeff n.toNat else 0 := by
        apply Finset.sum_eq_single n.toNat
        · intro c hc different
          rw [ite_eq_right (by omega)]
        · intro outside
          rw [Polynomial.notMem_support_iff.mp outside]
          simp
      _ = _ := by simp [Int.toNat_of_nonneg (le_of_not_gt negative)]

private def rectangle (D : LatticeData) (a : Charge D) (s : ℤ)
    (p q : Oscillator D) : ℂ :=
  ∑ d ∈ (translatedPolynomial D a p).support,
    ∑ c ∈ (translatedPolynomial D a q).support,
      if (c : ℤ) - (d : ℤ) = s then
        integerWick D ((translatedPolynomial D a p).coeff d)
          ((translatedPolynomial D a q).coeff c) else 0

private theorem convolution_rectangle (D : LatticeData) (a : Charge D) (s : ℤ)
    (p q : Oscillator D) :
    integerWick D (convolution D a s (translatedPolynomial D a p)) q =
      rectangle D a s p q := by
  classical
  change integerWick D (∑ d ∈ (translatedPolynomial D a p).support,
    (translatedPolynomial D a p).coeff d * creationCoeff D a (s+d)) q = _
  simp only [map_sum, LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro d hd
  rw [mul_comm, creation_translation_adjoint, translated_as_supported_sum]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro c hc
  by_cases equation : (c : ℤ) - (d : ℤ) = s
  · have equal : (c : ℤ) = s+d := by omega
    simp [equal]
  · have unequal : ¬ (c : ℤ) = s+d := by omega
    simp only [equation, unequal, ite_false, map_zero]

private theorem convolution_transpose (D : LatticeData) (a : Charge D) (s : ℤ)
    (p q : Oscillator D) :
    integerWick D (convolution D a s (translatedPolynomial D a p)) q =
      integerWick D p (convolution D a (-s) (translatedPolynomial D a q)) := by
  classical
  rw [integerWick_symmetric D p, convolution_rectangle, convolution_rectangle]
  unfold rectangle
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro c hc
  split_ifs with h₁ h₂
  · exact integerWick_symmetric D _ _
  · exfalso; omega
  · exfalso; omega
  · rfl

/-
proof_shape: sourcePairing_rawCoeff: content
admission_basis: escape-witness
escape_witness: The consumed creation_translation_adjoint proves the integer
creation/translation pairing by polynomial induction and the actual
annihilation-creation recurrence. convolution_rectangle then derives the
transpose by swapping two finite supports, before the original charge lift.
All other private helpers are consumed proof organization.
-/
/-- Charged raw BPZ transpose on the original carrier, for every signed index. -/
theorem sourcePairing_rawCoeff (D : LatticeData) (a : Charge D) (k : ℤ)
    (u v : Carrier D) :
    sourcePairing D (rawCoeff D a k u) v =
      paritySign (bilinear D a a / 2) *
        sourcePairing D u (rawCoeff D a (-k-bilinear D a a) v) := by
  classical
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add u w hu hw => simp only [map_add, LinearMap.add_apply, hu, hw, mul_add]
  | single d p =>
    induction v using Finsupp.induction_linear with
    | zero => simp
    | add v w hv hw => simp only [map_add, hv, hw, mul_add]
    | single e q =>
      rw [raw_single_convolution, raw_single_convolution]
      simp only [map_smul, LinearMap.smul_apply, smul_eq_mul,
        sourcePairing_single_single]
      by_cases he : e = -(a+d)
      · subst e
        have hd : a + -(a+d) = -d := by abel
        have hb : -k-bilinear D a a-bilinear D a (-(a+d)) =
            -(k-bilinear D a d) := by
          rw [bilinear_neg_right, bilinear_add_right]
          ring
        simp only [hd, ite_true]
        rw [hb, convolution_transpose, epsilon_reflection D a d]
        rw [show -a-d = -(a+d) by abel]
        ring
      · have hd : a+e ≠ -d := by
          intro h
          apply he
          calc e = (a+e)-a := by abel
               _ = -(a+d) := by rw [h]; abel
        rw [ite_eq_right he, ite_eq_right hd]
        ring

#print axioms sourcePairing_rawCoeff
end D5.S3.VertexAlgebra.SourceBPZ.ChargedRawTranspose
