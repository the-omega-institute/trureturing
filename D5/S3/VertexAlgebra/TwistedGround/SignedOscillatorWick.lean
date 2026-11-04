/- GID: D5/S3/VertexAlgebra/TwistedGround/SignedOscillatorWick
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/SignedOscillatorWick
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.BilinearForm.Basic]
   utility: none
   digest: The negative Gram Wick form transposes actual half-creation and translation and reflects every signed charged oscillator coefficient. -/



import D5.S3.VertexAlgebra.OriginalCurrentMetric
import D5.S3.VertexAlgebra.LatticeHalfFockChargedTensorCoefficients
import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
Complex bilinear signed Wick pairing on the original polynomial oscillator.
Reuse: FactorialFockMetric supplies occupation factorials and its proved
creation/derivative pairing; OriginalCurrentMetric supplies finite-colour
substitution and its derived inverse. No positive-definiteness premise.
The creation/translation induction and finite double-support rectangle prove
the coefficient reflection e -> -e-2*bilinear D a a, for the same charge a.
Integer IsUnit D.G.det is used only for both-sided nondegeneracy.
Indefinite forms, rank zero and empty polynomial supports remain in scope.
This is the classical bilinear Wick normalization, with no novelty claim.
No ground symmetry, Jacobi, intertwiner or full string theory is asserted.
Admission witness: the native signed creation/translation transpose, derived
from the polynomial chain rule and actual half_annihilation_creation, is
consumed by oscillator_coefficient_adjoint through a finite rectangle.
-/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped BigOperators TensorProduct
open ComplexConjugate

namespace D5.S3.VertexAlgebra.SignedOscillatorWick

open LatticeGeneratingFieldLocality LatticeHalfFock
open LatticeHalfFockChargedTensorCoefficients
open LatticeHalfFockChargedCoefficients MvPolynomial
open LatticeTwistedGroundRealization

namespace FactorialBilinear

universe u
variable {σ : Type u}

abbrev P (σ : Type u) := MvPolynomial σ ℂ

/-- Same existing occupation factorial; a complex BILINEAR form. -/
def form (σ : Type u) : LinearMap.BilinForm ℂ (P σ) :=
  (MvPolynomial.basisMonomials σ ℂ).constr ℂ
    (fun d => (FactorialFockMetric.weight d : ℂ) • MvPolynomial.lcoeff ℂ d)

private theorem basis_left (d : σ →₀ ℕ) (q : P σ) :
    form σ ((MvPolynomial.basisMonomials σ ℂ) d) q =
      (FactorialFockMetric.weight d : ℂ) * q.coeff d := by
  unfold form
  rw [Module.Basis.constr_basis]
  rfl

theorem monomial_left (d : σ →₀ ℕ) (a : ℂ) (q : P σ) :
    form σ (MvPolynomial.monomial d a) q =
      (FactorialFockMetric.weight d : ℂ) * a * q.coeff d := by
  have hm : MvPolynomial.monomial d a =
      a • (MvPolynomial.basisMonomials σ ℂ) d := by
    simp [MvPolynomial.coe_basisMonomials, MvPolynomial.smul_monomial]
  rw [hm, map_smul, LinearMap.smul_apply, basis_left]
  simp only [smul_eq_mul]
  ring

private theorem symmetric (p q : P σ) : form σ p q = form σ q p := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial d a =>
    induction q using MvPolynomial.induction_on' with
    | monomial e b =>
      rw [monomial_left, monomial_left]
      by_cases equal : d = e
      · subst e
        simp only [MvPolynomial.coeff_monomial, ite_true]
        ring
      · simp [MvPolynomial.coeff_monomial, equal, Ne.symm equal]
    | add q r hq hr =>
      simp only [map_add, LinearMap.add_apply, hq, hr]
  | add p r hp hr =>
    simp only [map_add, LinearMap.add_apply, hp, hr]

/-- This equality is used to REUSE the existing creation/pderiv proof. -/
private theorem eq_existing_inner (p q : P σ) :
    form σ p q = FactorialFockMetric.inner (MvPolynomial.map (starRingEnd ℂ) p) q := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial d a =>
    rw [monomial_left, MvPolynomial.map_monomial,
      FactorialFockMetric.inner_monomial_left]
    simp
  | add p r hp hr =>
    rw [map_add, LinearMap.add_apply, map_add,
      FactorialFockMetric.inner_add_first, hp, hr]

private theorem creation (i : σ) (p q : P σ) :
    form σ (MvPolynomial.X i * p) q = form σ p (MvPolynomial.pderiv i q) := by
  rw [eq_existing_inner, map_mul, MvPolynomial.map_X,
    FactorialFockMetric.mul_X_pderiv_pairing, ← eq_existing_inner]

private theorem derivative (i : σ) (p q : P σ) :
    form σ (MvPolynomial.pderiv i p) q = form σ p (MvPolynomial.X i * q) := by
  rw [symmetric, ← creation, symmetric]

private theorem nondegenerate : (form σ).Nondegenerate := by
  classical
  have left (p : P σ) (hp : ∀ q : P σ, form σ p q = 0) : p = 0 := by
    apply MvPolynomial.ext
    intro d
    change p.coeff d = 0
    have hz := hp (MvPolynomial.monomial d 1)
    rw [symmetric, monomial_left, mul_one] at hz
    have weight_ne : (FactorialFockMetric.weight d : ℂ) ≠ 0 := by
      exact_mod_cast (ne_of_gt (FactorialFockMetric.weight_pos d))
    exact (mul_eq_zero.mp hz).resolve_left weight_ne
  exact ⟨left, fun q hq => left q (fun p => by rw [symmetric]; exact hq p)⟩

end FactorialBilinear

/-- No positive-definiteness premise: the invariant bilinear sign is negative. -/
def modeMatrix (D : LatticeData) (k : ℕ) :
    Matrix (Fin D.rank) (Fin D.rank) ℂ :=
  (-frequency (k : ℤ)) • gramComplex D

private def modeInverse (D : LatticeData) (k : ℕ) :
    Matrix (Fin D.rank) (Fin D.rank) ℂ :=
  (-frequency (k : ℤ))⁻¹ • (gramComplex D)⁻¹

private theorem mode_scalar_ne_zero (k : ℕ) : -frequency (k : ℤ) ≠ 0 := by
  apply neg_ne_zero.mpr
  change (k : ℂ) + 1 / 2 ≠ 0
  have h := Complex.ofReal_ne_zero.mpr (show (k : ℝ) + 1 / 2 ≠ 0 by positivity)
  simpa using h

theorem complex_det_unit (D : LatticeData) (hu : IsUnit D.G.det) :
    IsUnit (gramComplex D).det := by
  change IsUnit (D.G.map (Int.castRingHom ℂ)).det
  change IsUnit ((Int.castRingHom ℂ).mapMatrix D.G).det
  rw [← (Int.castRingHom ℂ).map_det]
  exact hu.map (Int.castRingHom ℂ)

private theorem mode_mul_inverse (D : LatticeData) (hu : IsUnit D.G.det) (k : ℕ) :
    modeMatrix D k * modeInverse D k = 1 := by
  rw [modeMatrix, modeInverse, smul_mul_assoc, mul_smul_comm, smul_smul,
    mul_inv_cancel₀ (mode_scalar_ne_zero k), one_smul,
    Matrix.mul_nonsing_inv _ (complex_det_unit D hu)]

private theorem inverse_mul_mode (D : LatticeData) (hu : IsUnit D.G.det) (k : ℕ) :
    modeInverse D k * modeMatrix D k = 1 := by
  rw [modeMatrix, modeInverse, smul_mul_assoc, mul_smul_comm, smul_smul,
    inv_mul_cancel₀ (mode_scalar_ne_zero k), one_smul,
    Matrix.nonsing_inv_mul _ (complex_det_unit D hu)]

private def gramEquiv (D : LatticeData) (hu : IsUnit D.G.det) :
    Oscillator D ≃ₐ[ℂ] Oscillator D :=
  OriginalCurrentMetric.substitutionEquiv (modeMatrix D) (modeInverse D)
    (mode_mul_inverse D hu) (inverse_mul_mode D hu)

/-- On the same original oscillator, not on a replacement Fock model. -/
def wick (D : LatticeData) : LinearMap.BilinForm ℂ (Oscillator D) :=
  (FactorialBilinear.form (Index D)).compLeft
    (OriginalCurrentMetric.substitution (modeMatrix D)).toLinearMap

private theorem lowering_eq (D : LatticeData) (i : Fin D.rank) (k : ℕ)
    (p : Oscillator D) :
    OriginalCurrentMetric.lowering (modeMatrix D) i k p =
      -frequency (k : ℤ) • LatticeActualAnnihilation.annihilate D i k p := by
  rw [OriginalCurrentMetric.lowering_apply]
  change (∑ a : Fin D.rank,
      ((-frequency (k : ℤ)) * (D.G a i : ℂ)) • MvPolynomial.pderiv (a,k) p) = _
  simp_rw [D.symmetric _ i, mul_smul]
  rw [← Finset.smul_sum]
  congr 1
  rw [← LatticeActualAnnihilation.annihilation_apply]
  unfold LatticeActualAnnihilation.annihilationDerivation
  change (∑ j, (D.G i j : ℂ) • MvPolynomial.pderiv (j,k) p) =
    (Derivation.coeFnAddMonoidHom (∑ j, (D.G i j : ℂ) • MvPolynomial.pderiv (j,k))) p
  rw [map_sum]
  simp only [Finset.sum_apply, Derivation.coeFnAddMonoidHom_apply,
    Derivation.coe_smul, Pi.smul_apply]

private theorem factorial_variable_pairing (D : LatticeData) (i : Fin D.rank)
    (k : ℕ) (p q : Oscillator D) :
    FactorialBilinear.form (Index D)
        (OriginalCurrentMetric.variableImage (modeMatrix D) (i,k) * p) q =
      FactorialBilinear.form (Index D) p
        (OriginalCurrentMetric.lowering (modeMatrix D) i k q) := by
  classical
  rw [OriginalCurrentMetric.variableImage, Finset.sum_mul,
    OriginalCurrentMetric.lowering_apply]
  simp only [smul_mul_assoc, map_sum, LinearMap.sum_apply, map_smul,
    LinearMap.smul_apply, FactorialBilinear.creation]

theorem wick_creation (D : LatticeData) (i : Fin D.rank) (k : ℕ)
    (p q : Oscillator D) :
    wick D (MvPolynomial.X (i,k) * p) q =
      wick D p (-frequency (k : ℤ) • LatticeActualAnnihilation.annihilate D i k q) := by
  change FactorialBilinear.form (Index D)
    (OriginalCurrentMetric.substitution (modeMatrix D) (MvPolynomial.X (i,k) * p)) q = _
  rw [map_mul, OriginalCurrentMetric.substitution_X, factorial_variable_pairing,
    lowering_eq]
  rfl

private theorem derivative_substitution (D : LatticeData) (i : Fin D.rank)
    (k : ℕ) (p : Oscillator D) :
    MvPolynomial.pderiv (i,k) (OriginalCurrentMetric.substitution (modeMatrix D) p) =
      OriginalCurrentMetric.substitution (modeMatrix D)
        (OriginalCurrentMetric.lowering (modeMatrix D) i k p) := by
  classical
  have generator (x : Index D) :
      MvPolynomial.pderiv (i,k)
          (OriginalCurrentMetric.substitution (modeMatrix D) (MvPolynomial.X x)) =
        OriginalCurrentMetric.substitution (modeMatrix D)
          (OriginalCurrentMetric.lowering (modeMatrix D) i k (MvPolynomial.X x)) := by
    rcases x with ⟨l,m⟩
    rw [OriginalCurrentMetric.substitution_X, OriginalCurrentMetric.lowering_X]
    by_cases same : k = m
    · subst m
      simp [OriginalCurrentMetric.variableImage, MvPolynomial.pderiv_X,
        Pi.single_apply, Prod.mk.injEq, modeMatrix, gramComplex, D.symmetric,
        smul_ite, eq_comm]
    · simp [OriginalCurrentMetric.variableImage, MvPolynomial.pderiv_X,
        Prod.mk.injEq, same, Ne.symm same]
  induction p using MvPolynomial.induction_on with
  | C c => simp [OriginalCurrentMetric.substitution, MvPolynomial.derivation_C]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p x hp =>
    rw [map_mul, (MvPolynomial.pderiv (i,k)).leibniz,
      (OriginalCurrentMetric.lowering (modeMatrix D) i k).leibniz]
    simp only [smul_eq_mul, map_add, map_mul, hp, generator]

theorem wick_lowering (D : LatticeData) (i : Fin D.rank) (k : ℕ)
    (p q : Oscillator D) :
    wick D (-frequency (k : ℤ) • LatticeActualAnnihilation.annihilate D i k p) q =
      wick D p (MvPolynomial.X (i,k) * q) := by
  rw [← lowering_eq]
  change FactorialBilinear.form (Index D)
    (OriginalCurrentMetric.substitution (modeMatrix D)
      (OriginalCurrentMetric.lowering (modeMatrix D) i k p)) q = _
  rw [← derivative_substitution, FactorialBilinear.derivative]
  rfl

theorem wick_nondegenerate (D : LatticeData) (hu : IsUnit D.G.det) :
    (wick D).Nondegenerate := by
  constructor
  · intro p hp
    have h : gramEquiv D hu p = 0 :=
      FactorialBilinear.nondegenerate.1 _ hp
    exact (gramEquiv D hu).injective (by simpa using h)
  · intro q hq
    apply FactorialBilinear.nondegenerate.2 q
    intro p
    obtain ⟨r, hr⟩ := (gramEquiv D hu).surjective p
    subst p
    exact hq r

private theorem substitution_constant (D : LatticeData) (p : Oscillator D) :
    (OriginalCurrentMetric.substitution (modeMatrix D) p).coeff 0 = p.coeff 0 := by
  classical
  change MvPolynomial.constantCoeff
    (OriginalCurrentMetric.substitution (modeMatrix D) p) = MvPolynomial.constantCoeff p
  induction p using MvPolynomial.induction_on with
  | C c => simp [OriginalCurrentMetric.substitution]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p x hp =>
    rw [map_mul, map_mul, map_mul, hp, OriginalCurrentMetric.substitution_X]
    simp [OriginalCurrentMetric.variableImage, map_sum]

private theorem wick_constant_left (D : LatticeData) (c : ℂ) (q : Oscillator D) :
    wick D (MvPolynomial.C c) q = c * q.coeff 0 := by
  change FactorialBilinear.form (Index D)
    (OriginalCurrentMetric.substitution (modeMatrix D) (MvPolynomial.C c)) q = _
  rw [show OriginalCurrentMetric.substitution (modeMatrix D) (MvPolynomial.C c) =
    MvPolynomial.C c from (OriginalCurrentMetric.substitution (modeMatrix D)).commutes c]
  change FactorialBilinear.form (Index D) (MvPolynomial.monomial 0 c) q = _
  rw [FactorialBilinear.monomial_left]
  simp [FactorialFockMetric.weight]

private theorem wick_constant_right (D : LatticeData) (c : ℂ) (p : Oscillator D) :
    wick D p (MvPolynomial.C c) = c * p.coeff 0 := by
  change FactorialBilinear.form (Index D)
    (OriginalCurrentMetric.substitution (modeMatrix D) p) (MvPolynomial.monomial 0 c) = _
  rw [FactorialBilinear.symmetric, FactorialBilinear.monomial_left,
    substitution_constant]
  simp [FactorialFockMetric.weight]

private theorem wick_symmetric (D : LatticeData) (p q : Oscillator D) :
    wick D p q = wick D q p := by
  induction p using MvPolynomial.induction_on generalizing q with
  | C c => rw [wick_constant_left, wick_constant_right]
  | add p r hp hr => simp only [map_add, LinearMap.add_apply, hp, hr]
  | mul_X p x hp =>
    rcases x with ⟨i,k⟩
    rw [mul_comm p, wick_creation, hp, wick_lowering]

/-- Signed polynomial coefficient; retains negative indices as zero. -/
def translatedCoeff (D : LatticeData) (a : Charge D) (n : ℤ)
    (p : Oscillator D) : Oscillator D :=
  if n < 0 then 0 else (halfTranslatedPolynomial D a p).coeff n.toNat

private theorem creation_constant (D : LatticeData) (a : Charge D) (n : ℤ) :
    (halfCreationCoeff D a n).coeff 0 = if n = 0 then 1 else 0 := by
  classical
  by_cases negative : n < 0
  · simp [halfCreationCoeff, negative, show n ≠ 0 by omega]
  by_cases zero : n = 0
  · subst n
    simp only [halfCreationCoeff, show ¬ (0 : ℤ) < 0 by omega, ite_false,
      Int.toNat_zero, exponential_constant, MvPolynomial.coeff_one, ite_true]
  · rw [ite_eq_right zero]
    by_contra nonzero
    have degree := (half_creation_coefficient_grading D a n) nonzero
    have : n.toNat = 0 := by simpa using degree.symm
    omega

private theorem translated_variable (D : LatticeData) (a : Charge D) (n : ℤ)
    (i : Fin D.rank) (k : ℕ) (p : Oscillator D) :
    translatedCoeff D a n (MvPolynomial.X (i,k) * p) =
      MvPolynomial.X (i,k) * translatedCoeff D a n p -
        (bilinear D a (unitCharge D i) : ℂ) •
          translatedCoeff D a (n - (omega D (i,k) : ℤ)) p := by
  classical
  by_cases negative : n < 0
  · have shifted : n - (omega D (i,k) : ℤ) < 0 := by simp only [omega] at *; omega
    simp [translatedCoeff, negative, shifted]
  · have translated : halfTranslatedPolynomial D a (MvPolynomial.X (i,k) * p) =
        Polynomial.C (MvPolynomial.X (i,k) : Oscillator D) * halfTranslatedPolynomial D a p -
        Polynomial.C ((bilinear D a (unitCharge D i) : ℂ) • (1 : Oscillator D)) *
          (Polynomial.X ^ omega D (i,k) * halfTranslatedPolynomial D a p) := by
      simp only [halfTranslatedPolynomial, map_mul, MvPolynomial.eval₂AlgHom_X,
        halfTranslationVariable]
      ring
    rw [translatedCoeff, ite_eq_right negative, translated, Polynomial.coeff_sub,
      Polynomial.coeff_C_mul, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_mul']
    by_cases bound : omega D (i,k) ≤ n.toNat
    · have shifted : ¬ n - (omega D (i,k) : ℤ) < 0 := by omega
      have hn : (n - (omega D (i,k) : ℤ)).toNat = n.toNat - omega D (i,k) := by omega
      simp only [bound, ite_true, translatedCoeff, negative, shifted, ite_false, hn,
        smul_mul_assoc, one_mul]
    · have shifted : n - (omega D (i,k) : ℤ) < 0 := by omega
      simp only [bound, ite_false, translatedCoeff, negative, shifted, ite_true, smul_zero,
        mul_zero, sub_zero]

private theorem lowering_creation_product (D : LatticeData) (a : Charge D) (n : ℤ)
    (i : Fin D.rank) (k : ℕ) (p : Oscillator D) :
    OriginalCurrentMetric.lowering (modeMatrix D) i k (halfCreationCoeff D a n * p) =
      halfCreationCoeff D a n * OriginalCurrentMetric.lowering (modeMatrix D) i k p -
        (bilinear D a (unitCharge D i) : ℂ) •
          (halfCreationCoeff D a (n - (omega D (i,k) : ℤ)) * p) := by
  have scalar : -frequency (k : ℤ) * (2 / (2*k+1 : ℂ)) = -1 := by
    have nonzero : (2*k+1 : ℂ) ≠ 0 := by exact_mod_cast (show 2*k+1 ≠ 0 by omega)
    rw [← mul_div_assoc, div_eq_iff nonzero]
    simp only [frequency, Int.cast_natCast]
    ring
  rw [lowering_eq, lowering_eq, LatticeActualAnnihilation.annihilate_mul,
    half_annihilation_creation]
  rw [LatticeFiniteNegativeGeneration.bilinear_symmetric D (unitCharge D i) a]
  simp only [smul_add, smul_mul_assoc, smul_smul]
  rw [← mul_assoc, scalar]
  simp only [omega, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
    Algebra.smul_def, map_neg, map_mul, map_one, one_mul]
  ring

/-- The first charged transpose calculation. No desired field adjoint is a premise. -/
theorem creation_translation_adjoint (D : LatticeData) (a : Charge D)
    (n : ℤ) (p q : Oscillator D) :
    wick D (halfCreationCoeff D a n * p) q = wick D p (translatedCoeff D a n q) := by
  classical
  induction q using MvPolynomial.induction_on generalizing p n with
  | C c =>
    rw [wick_constant_right]
    change c * MvPolynomial.constantCoeff (halfCreationCoeff D a n * p) = _
    rw [map_mul]
    change c * ((halfCreationCoeff D a n).coeff 0 * p.coeff 0) = _
    rw [creation_constant]
    by_cases negative : n < 0
    · simp [translatedCoeff, negative, show n ≠ 0 by omega]
    · by_cases zero : n = 0
      · subst n
        simp [translatedCoeff, halfTranslatedPolynomial, wick_constant_right]
      · have nat_zero : n.toNat ≠ 0 := by omega
        simp [translatedCoeff, negative, halfTranslatedPolynomial, Polynomial.coeff_C,
          zero, nat_zero]
  | add q r hq hr =>
    simp only [map_add, hq, hr]
    by_cases negative : n < 0
    · simp [translatedCoeff, negative]
    · simp only [translatedCoeff, ite_eq_right negative, halfTranslatedPolynomial,
        map_add, Polynomial.coeff_add]
  | mul_X q x ih =>
    rcases x with ⟨i,k⟩
    rw [mul_comm q, ← wick_lowering, ← lowering_eq, lowering_creation_product]
    simp only [map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply]
    rw [ih, ih, lowering_eq, wick_lowering, ← map_smul, ← map_sub,
      ← translated_variable]

/-- Both input translation supports are finite; the creation series need not be. -/
private def rectangularPairing (D : LatticeData) (a : Charge D) (e : ℤ)
    (p q : Oscillator D) : ℂ :=
  ∑ d ∈ (halfTranslatedPolynomial D a p).support,
    ∑ c ∈ (halfTranslatedPolynomial D a q).support,
      if (c : ℤ) - (d : ℤ) = e + chargeNorm D a then
        wick D ((halfTranslatedPolynomial D a p).coeff d)
          ((halfTranslatedPolynomial D a q).coeff c) else 0

private theorem translated_as_supported_sum (D : LatticeData) (a : Charge D)
    (n : ℤ) (p : Oscillator D) :
    translatedCoeff D a n p =
      ∑ c ∈ (halfTranslatedPolynomial D a p).support,
        if (c : ℤ) = n then (halfTranslatedPolynomial D a p).coeff c else 0 := by
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
          (halfTranslatedPolynomial D a p).coeff n.toNat else 0 := by
        apply Finset.sum_eq_single n.toNat
        · intro c hc different
          rw [ite_eq_right (by omega)]
        · intro outside
          rw [Polynomial.notMem_support_iff.mp outside]
          simp
      _ = _ := by simp [Int.toNat_of_nonneg (le_of_not_gt negative)]

private theorem oscillator_rectangular_pairing (D : LatticeData) (a : Charge D)
    (e : ℤ) (p q : Oscillator D) :
    wick D (oscillatorCoefficient D a e p) q = rectangularPairing D a e p q := by
  classical
  change wick D (∑ᶠ d : ℕ, oscillatorTerm D a e p d) q = _
  rw [finsum_eq_sum_of_support_subset _ (term_support D a e p)]
  simp only [map_sum, LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro d hd
  rw [oscillatorTerm, mul_comm, creation_translation_adjoint, translated_as_supported_sum]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro c hc
  by_cases equation : (c : ℤ) - (d : ℤ) = e + chargeNorm D a
  · have equal : (c : ℤ) = e + chargeNorm D a + d := by omega
    simp [equal]
  · have unequal : ¬ (c : ℤ) = e + chargeNorm D a + d := by omega
    simp only [equation, unequal, ite_false, map_zero]

theorem oscillator_coefficient_adjoint (D : LatticeData) (a : Charge D)
    (e : ℤ) (p q : Oscillator D) :
    wick D (oscillatorCoefficient D a e p) q =
      wick D p (oscillatorCoefficient D a (-e-2*chargeNorm D a) q) := by
  classical
  rw [wick_symmetric D p, oscillator_rectangular_pairing,
    oscillator_rectangular_pairing]
  unfold rectangularPairing
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro c hc
  split_ifs with h₁ h₂
  · exact wick_symmetric D _ _
  · exfalso; omega
  · exfalso; omega
  · rfl


#print axioms wick_nondegenerate
#print axioms oscillator_coefficient_adjoint
end D5.S3.VertexAlgebra.SignedOscillatorWick
