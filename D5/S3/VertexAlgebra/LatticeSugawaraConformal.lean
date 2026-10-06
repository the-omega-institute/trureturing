/- GID: D5/S3/VertexAlgebra/LatticeSugawaraConformal
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeSugawaraConformal
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual Sugawara minus-one and zero modes give translation and charged weighted grading. -/

/-
Copyright (c) 2025 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the repository root LICENSE.
Authors of the upstream Sugawara architecture: Kalle Kytölä
Modified source: the statewise normal-ordering and commutator architecture of
VirasoroProject revision 5ff4245383b2cdd4eea7a0524bc1274c32041eb4 is adapted
here to the actual matrix lattice currents and every integral charge sector.
The charged-ground cancellation, inverse-Gram trace and actual translation
identification concern the existing lattice carrier, without a Fock transfer.
Classical source: Bakalov--Kac, Twisted Modules over Lattice Vertex Algebras,
arXiv math/0402315v1, section 4.1, equations (4.12)--(4.16).

proof_shape: sugawaraMode_minus_one_eq_translation: content
proof_shape: sugawaraMode_zero_single: content
proof_shape: actual_conformal_generators: content
admission_basis: escape-witness
escape_witness: The actual normal-product coefficient L(-1) is identified
with charge-sensitive translation on every oscillator polynomial; the
actual zero coefficient is identified with Euler plus half the lattice norm.
proof_shape: translation_single: bind-only; consumed by rawCoeff_translation,
neutral_translation_covariance and actual_translation_generators
proof_shape: translation_vacuum: bind-only; consumed by actual_translation_generators
proof_shape: rawCoeff_translation: bind-only; consumed by actual_lattice_translation_covariance
proof_shape: actual_lattice_translation_covariance: bind-only; consumed by actual_translation_generators
proof_shape: neutral_translation_covariance: bind-only; consumed by
sugawaraMode_minus_one_eq_translation and actual_translation_generators
proof_shape: actual_translation_generators: bind-only; consumed by actual_conformal_generators
The translation auxiliaries supply no independent admission basis.
Utility is none: all assertions are general operator identities, not
bounded enumeration, checkers, numerical reductions or certified instances.
No all-state vertex algebra, Jacobi, positivity or finite-dimensional
weight-space conclusion is asserted.
-/

import D5.S3.VertexAlgebra.LatticeSugawaraVirasoro
import Mathlib.RingTheory.Derivation.MapCoeffs
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.LatticeSugawaraConformal

open D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open D5.S3.VertexAlgebra.LatticeFiniteNegativeGeneration
open D5.S3.VertexAlgebra.FieldNormalProduct
open D5.S3.VertexAlgebra.LatticeSugawaraCurrents
open D5.S3.VertexAlgebra.LatticeSugawaraVirasoro
open MvPolynomial
open scoped BigOperators VertexOperator

noncomputable section

/-- Translation of the actual oscillator variables, without divided powers. -/
def oscillatorDerivation (D : LatticeData) :
    Derivation ℂ (Oscillator D) (Oscillator D) :=
  MvPolynomial.mkDerivation ℂ (fun x : Index D =>
    (x.2 + 1 : ℂ) • (X (x.1, x.2 + 1) : Oscillator D))

/-- The charge contribution on a sector. -/
def chargePolynomial (D : LatticeData) (β : Charge D) : Oscillator D :=
  ∑ i : Fin D.rank, (β i : ℂ) • X (i, 0)

def sectorTranslation (D : LatticeData) (β : Charge D) :
    Module.End ℂ (Oscillator D) :=
  (oscillatorDerivation D).toLinearMap + LinearMap.mulLeft ℂ (chargePolynomial D β)

/-- The operator preserves each charge and extends over finite charge support. -/
def translation (D : LatticeData) : Module.End ℂ (Carrier D) :=
  Finsupp.lsum ℂ (fun β => (Finsupp.lsingle β).comp (sectorTranslation D β))

@[simp] theorem translation_single (D : LatticeData) (β : Charge D)
    (p : Oscillator D) :
    translation D (Finsupp.single β p) =
      Finsupp.single β (oscillatorDerivation D p + chargePolynomial D β * p) := by
  simp [translation, sectorTranslation]

@[simp] theorem translation_vacuum (D : LatticeData) :
    translation D (Finsupp.single (0 : Charge D) (1 : Oscillator D)) = 0 := by
  simp [chargePolynomial]

private theorem charge_add (D : LatticeData) (α β : Charge D) :
    chargePolynomial D (α + β) = chargePolynomial D α + chargePolynomial D β := by
  simp [chargePolynomial, Int.cast_add, add_smul, Finset.sum_add_distrib]

/-- Coefficientwise oscillator derivation, fixing the polynomial variable. -/
private def polynomialDerivation (D : LatticeData) :
    Derivation ℂ (Polynomial (Oscillator D)) (Polynomial (Oscillator D)) :=
  PolynomialModule.equivPolynomialSelf.toLinearMap.compDer
    (oscillatorDerivation D).mapCoeffs

private theorem polynomialDerivation_coeff (D : LatticeData)
    (q : Polynomial (Oscillator D)) (d : ℕ) :
    (polynomialDerivation D q).coeff d = oscillatorDerivation D (q.coeff d) := rfl

private theorem polynomialDerivation_monomial (D : LatticeData) (d : ℕ)
    (p : Oscillator D) :
    polynomialDerivation D (Polynomial.monomial d p) =
      Polynomial.monomial d (oscillatorDerivation D p) := by
  ext j
  rw [polynomialDerivation_coeff]
  by_cases h : d = j <;> simp [Polynomial.coeff_monomial, h]

private theorem partial_translation_zero (D : LatticeData) (j : Fin D.rank)
    (p : Oscillator D) :
    oscillatorDerivation D (pderiv (j, 0) p) -
      pderiv (j, 0) (oscillatorDerivation D p) = 0 := by
  have h : ⁅oscillatorDerivation D, pderiv (j, 0)⁆ =
      (0 : Derivation ℂ (Oscillator D) (Oscillator D)) := by
    apply MvPolynomial.derivation_ext
    intro x
    simp [Derivation.commutator_apply, oscillatorDerivation, pderiv_X,
      Pi.single_apply, apply_ite]
  exact congrArg (fun d : Derivation ℂ (Oscillator D) (Oscillator D) => d p) h

private theorem partial_translation_succ (D : LatticeData) (j : Fin D.rank)
    (r : ℕ) (p : Oscillator D) :
    oscillatorDerivation D (pderiv (j, r + 1) p) -
      pderiv (j, r + 1) (oscillatorDerivation D p) =
        -(r + 1 : ℂ) • pderiv (j, r) p := by
  have h : ⁅oscillatorDerivation D, pderiv (j, r + 1)⁆ =
      (-(r + 1 : ℂ) • pderiv (j, r) : Derivation ℂ (Oscillator D) (Oscillator D)) := by
    apply MvPolynomial.derivation_ext
    intro x
    simp only [Derivation.commutator_apply, pderiv_X, Pi.single_apply,
      oscillatorDerivation, MvPolynomial.mkDerivation_X,
      Derivation.smul_apply]
    rw [show (MvPolynomial.mkDerivation ℂ
      (fun x : Index D => (x.2 + 1 : ℂ) • (X (x.1, x.2 + 1) : Oscillator D)))
      (if x = (j, r + 1) then 1 else 0) = 0 by split_ifs <;> simp]
    have hx : (x.1, x.2 + 1) = (j, r + 1) ↔ x = (j, r) := by
      simp only [Nat.add_right_cancel_iff, Prod.ext_iff]
    rw [Derivation.map_smul, pderiv_X]
    simp only [Pi.single_apply]
    simp only [hx]
    by_cases h : x = (j, r)
    · subst x; simp [smul_eq_C_mul]
    · simp [h]
  exact congrArg (fun d : Derivation ℂ (Oscillator D) (Oscillator D) => d p) h

private theorem partial_charge (D : LatticeData) (β : Charge D)
    (j : Fin D.rank) (r : ℕ) :
    pderiv (j, r) (chargePolynomial D β) =
      if r = 0 then C (β j : ℂ) else 0 := by
  classical
  by_cases hr : r = 0
  · subst r
    simp [chargePolynomial, pderiv_X, Pi.single_apply, Prod.mk.injEq,
      smul_eq_C_mul]
  · simp [chargePolynomial, pderiv_X, Prod.mk.injEq,
      smul_eq_C_mul, hr, Ne.symm hr]

/-- Coefficientwise oscillator derivation on a formal power series. -/
private def seriesDerivation (D : LatticeData) :
    Derivation ℂ (PowerSeries (Oscillator D)) (PowerSeries (Oscillator D)) where
  toFun f := PowerSeries.mk (fun n => oscillatorDerivation D (PowerSeries.coeff n f))
  map_add' f g := by apply PowerSeries.ext; intro n; simp
  map_smul' c f := by apply PowerSeries.ext; intro n; simp
  map_one_eq_zero' := by
    apply PowerSeries.ext
    intro n
    simp [PowerSeries.coeff_one, apply_ite]
  leibniz' f g := by
    apply PowerSeries.ext
    intro n
    change PowerSeries.coeff n (PowerSeries.mk (fun n =>
      oscillatorDerivation D (PowerSeries.coeff n (f * g)))) =
      PowerSeries.coeff n (f * PowerSeries.mk (fun n =>
        oscillatorDerivation D (PowerSeries.coeff n g)) +
        g * PowerSeries.mk (fun n => oscillatorDerivation D (PowerSeries.coeff n f)))
    rw [mul_comm g (PowerSeries.mk (fun n => oscillatorDerivation D (PowerSeries.coeff n f)))]
    simp only [PowerSeries.coeff_mk, map_add, PowerSeries.coeff_mul, map_sum,
      Derivation.leibniz, smul_eq_mul, Finset.sum_add_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro x hx
    ring

private theorem seriesDerivation_coeff (D : LatticeData)
    (f : PowerSeries (Oscillator D)) (n : ℕ) :
    PowerSeries.coeff n (seriesDerivation D f) =
      oscillatorDerivation D (PowerSeries.coeff n f) := by
  change PowerSeries.coeff n (PowerSeries.mk
    (fun n => oscillatorDerivation D (PowerSeries.coeff n f))) = _
  rw [PowerSeries.coeff_mk]

private theorem seriesDerivation_derivative (D : LatticeData)
    (f : PowerSeries (Oscillator D)) :
    seriesDerivation D (PowerSeries.derivative (Oscillator D) f) =
      PowerSeries.derivative (Oscillator D) (seriesDerivation D f) := by
  apply PowerSeries.ext
  intro n
  simp only [seriesDerivation_coeff, PowerSeries.coeff_derivative,
    Derivation.leibniz, Derivation.map_add, Derivation.map_natCast, Derivation.map_one_eq_zero,
    add_zero, smul_eq_mul]
  ring

private theorem logarithm_derivative_coeff (D : LatticeData) (α : Charge D)
    (n : ℕ) :
    PowerSeries.coeff n (PowerSeries.derivative (Oscillator D) (creationSeries D α)) =
      ∑ i : Fin D.rank, (α i : ℂ) • (X (i,n) : Oscillator D) := by
  rw [PowerSeries.coeff_derivative]
  simp only [creationSeries, PowerSeries.coeff_mk, Nat.succ_ne_zero, ↓reduceDIte,
    Nat.add_sub_cancel]
  rw [mul_comm, show (n + 1 : Oscillator D) =
    algebraMap ℂ (Oscillator D) (n + 1 : ℂ) by simp,
    ← Algebra.smul_def, smul_smul]
  rw [Nat.cast_add, Nat.cast_one,
    mul_inv_cancel₀ (by exact_mod_cast Nat.succ_ne_zero n), one_smul]

private theorem exponential_constant (D : LatticeData) (α : Charge D) :
    PowerSeries.coeff 0 (creationExponential D α) = 1 := by
  have hA : PowerSeries.constantCoeff (creationSeries D α) = 0 := by
    simp [creationSeries, ← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  rw [creationExponential, PowerSeries.coeff_subst'
    (PowerSeries.HasSubst.of_constantCoeff_zero' hA), finsum_eq_single _ 0]
  · simp
  · intro j hj
    rw [PowerSeries.coeff_zero_eq_constantCoeff, map_pow, hA]
    simp [hj]

private theorem exponential_derivative (D : LatticeData) (α : Charge D) :
    PowerSeries.derivative (Oscillator D) (creationExponential D α) =
      creationExponential D α *
        PowerSeries.derivative (Oscillator D) (creationSeries D α) := by
  have hA : PowerSeries.constantCoeff (creationSeries D α) = 0 := by
    simp [creationSeries, ← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  rw [creationExponential,
    PowerSeries.derivative_subst (PowerSeries.HasSubst.of_constantCoeff_zero' hA),
    PowerSeries.derivative_exp]

/-- The oscillator derivative of the actual exponential, proved from its ODE. -/
private theorem creation_derivation_series (D : LatticeData) (α : Charge D) :
    seriesDerivation D (creationExponential D α) =
      PowerSeries.derivative (Oscillator D) (creationExponential D α) -
        PowerSeries.C (chargePolynomial D α) * creationExponential D α := by
  let E := creationExponential D α
  let A := PowerSeries.derivative (Oscillator D) (creationSeries D α)
  let H := seriesDerivation D E - PowerSeries.derivative (Oscillator D) E +
    PowerSeries.C (chargePolynomial D α) * E
  have hE : PowerSeries.derivative (Oscillator D) E = E * A :=
    exponential_derivative D α
  have hA : seriesDerivation D A = PowerSeries.derivative (Oscillator D) A := by
    apply PowerSeries.ext
    intro n
    rw [seriesDerivation_coeff]
    conv_rhs => rw [PowerSeries.coeff_derivative]
    rw [show PowerSeries.coeff n A =
      ∑ i : Fin D.rank, (α i : ℂ) • (X (i,n) : Oscillator D) from
      logarithm_derivative_coeff D α n]
    rw [show PowerSeries.coeff (n+1) A =
      ∑ i : Fin D.rank, (α i : ℂ) • (X (i,n+1) : Oscillator D) from
      logarithm_derivative_coeff D α (n+1)]
    simp only [map_sum, Derivation.map_smul,
      oscillatorDerivation, MvPolynomial.mkDerivation_X]
    simp only [Finset.sum_mul, smul_eq_C_mul, C_add, C_1]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [map_natCast]
    ring
  have hH : PowerSeries.derivative (Oscillator D) H = H * A := by
    dsimp only [H]
    rw [map_add, map_sub, ← seriesDerivation_derivative, hE,
      (seriesDerivation D).leibniz, (PowerSeries.derivative (Oscillator D)).leibniz,
      (PowerSeries.derivative (Oscillator D)).leibniz,
      PowerSeries.derivative_C, hA, hE]
    simp only [smul_eq_mul, mul_zero, add_zero]
    ring
  have h0 : PowerSeries.coeff 0 H = 0 := by
    dsimp only [H]
    rw [map_add, map_sub, seriesDerivation_coeff, exponential_constant,
      Derivation.map_one_eq_zero, hE]
    simp [PowerSeries.coeff_mul, E, A, exponential_constant,
      logarithm_derivative_coeff, chargePolynomial]
  have hzero : H = 0 := by
    apply PowerSeries.ext
    intro n
    rw [map_zero]
    induction n using Nat.strong_induction_on with
    | h n ih =>
      cases n with
      | zero => exact h0
      | succ n =>
        have hr := congrArg (PowerSeries.coeff n) hH
        rw [PowerSeries.coeff_derivative, PowerSeries.coeff_mul] at hr
        have hz : (∑ x ∈ Finset.HasAntidiagonal.antidiagonal n,
            PowerSeries.coeff x.1 H * PowerSeries.coeff x.2 A) = 0 := by
          apply Finset.sum_eq_zero
          intro x hx
          rw [ih x.1 (by have := Finset.HasAntidiagonal.mem_antidiagonal.mp hx; omega),
            zero_mul]
        rw [hz] at hr
        have hr' : (n + 1) • PowerSeries.coeff (n + 1) H =
            (n + 1) • (0 : Oscillator D) := by
          simpa only [nsmul_eq_mul, Nat.cast_add, Nat.cast_one, mul_comm,
            mul_zero, zero_mul] using hr
        exact (smul_right_inj (Nat.succ_ne_zero n)).mp hr'
  dsimp only [H] at hzero
  change seriesDerivation D E = PowerSeries.derivative (Oscillator D) E -
    PowerSeries.C (chargePolynomial D α) * E
  linear_combination hzero

private theorem creation_derivation (D : LatticeData) (α : Charge D) (t : ℤ) :
    oscillatorDerivation D (creationCoeff D α t) =
      (t + 1 : ℂ) • creationCoeff D α (t + 1) -
        chargePolynomial D α * creationCoeff D α t := by
  by_cases ht : t < 0
  · by_cases h : t = -1
    · subst t; simp [creationCoeff]
    · simp [creationCoeff, ht, show t + 1 < 0 by omega]
  · have ht0 : 0 ≤ t := by omega
    have hn : ((t.toNat : ℕ) : ℤ) = t := Int.toNat_of_nonneg ht0
    have hs : (t + 1).toNat = t.toNat + 1 := by omega
    have h := congrArg (PowerSeries.coeff t.toNat) (creation_derivation_series D α)
    rw [map_sub, seriesDerivation_coeff, PowerSeries.coeff_derivative,
      PowerSeries.coeff_C_mul] at h
    have hscale : (t.toNat + 1 : Oscillator D) =
        algebraMap ℂ (Oscillator D) (t + 1 : ℂ) := by
      simp only [map_add, map_one, map_intCast]
      have htP : (t.toNat : Oscillator D) = (t : Oscillator D) := by exact_mod_cast hn
      rw [htP]
    rw [hscale] at h
    rw [creationCoeff, dif_neg ht, creationCoeff, dif_neg (by omega), hs]
    simpa only [creationCoeff, dif_neg ht, Algebra.smul_def, mul_comm] using h

private theorem translated_sum (D : LatticeData) (α : Charge D)
    {ι : Type*} (s : Finset ι) (p : ι → Oscillator D) :
    translatedPolynomial D α (∑ i ∈ s, p i) =
      ∑ i ∈ s, translatedPolynomial D α (p i) := by
  simp [translatedPolynomial]

private theorem translated_add (D : LatticeData) (α : Charge D)
    (p q : Oscillator D) :
    translatedPolynomial D α (p + q) =
      translatedPolynomial D α p + translatedPolynomial D α q := by
  simp [translatedPolynomial]

private theorem translated_mul (D : LatticeData) (α : Charge D)
    (p q : Oscillator D) :
    translatedPolynomial D α (p * q) =
      translatedPolynomial D α p * translatedPolynomial D α q := by
  simp [translatedPolynomial]

private theorem translated_X (D : LatticeData) (α : Charge D) (x : Index D) :
    translatedPolynomial D α (X x) = translationVariable D α x.1 x.2 := by
  simp [translatedPolynomial]

private theorem translated_smul (D : LatticeData) (α : Charge D) (c : ℂ)
    (p : Oscillator D) :
    translatedPolynomial D α (c • p) = c • translatedPolynomial D α p := by
  have h : translatedPolynomial D α (C c) =
      algebraMap ℂ (Polynomial (Oscillator D)) c := by simp [translatedPolynomial]
  rw [smul_eq_C_mul, translated_mul, h, ← Algebra.smul_def]


private theorem polynomialDerivation_C (D : LatticeData) (p : Oscillator D) :
    polynomialDerivation D (Polynomial.C p) =
      Polynomial.C (oscillatorDerivation D p) :=
  polynomialDerivation_monomial D 0 p

private theorem polynomialDerivation_X (D : LatticeData) :
    polynomialDerivation D (Polynomial.X : Polynomial (Oscillator D)) = 0 := by
  rw [← Polynomial.monomial_one_one_eq_X, polynomialDerivation_monomial]
  simp

/-- All-polynomial annihilation transport; the indeterminate is the inverse field variable. -/
private theorem annihilation_transport (D : LatticeData) (α : Charge D)
    (p : Oscillator D) :
    translatedPolynomial D α (oscillatorDerivation D p) =
      polynomialDerivation D (translatedPolynomial D α p) +
        Polynomial.X ^ 2 * (translatedPolynomial D α p).derivative := by
  classical
  have hgen (x : Index D) :
      translatedPolynomial D α (oscillatorDerivation D (X x)) =
        polynomialDerivation D (translatedPolynomial D α (X x)) +
          Polynomial.X ^ 2 * (translatedPolynomial D α (X x)).derivative := by
    rw [show oscillatorDerivation D (X x) =
      (x.2 + 1 : ℂ) • (X (x.1, x.2 + 1) : Oscillator D) from
        MvPolynomial.mkDerivation_X ℂ _ x]
    rw [translated_smul]
    simp only [translated_X]
    simp only [translationVariable, map_sub, Derivation.leibniz,
      polynomialDerivation_C, polynomialDerivation_X, Derivation.leibniz_pow,
      smul_zero, zero_add, mul_zero, smul_eq_mul,
      oscillatorDerivation, MvPolynomial.mkDerivation_X,
      Derivation.map_smul, Derivation.map_one_eq_zero,
      Polynomial.derivative_C,
      Polynomial.derivative_mul, Polynomial.derivative_pow,
      Polynomial.derivative_X, mul_one, zero_mul]
    simp only [Nat.add_sub_cancel, smul_eq_C_mul, map_mul, map_add, map_natCast, map_one]
    rw [show x.2 + 1 + 1 = x.2 + 2 by omega]
    simp only [Algebra.smul_def, map_add, map_natCast, map_one, map_zero,
      Nat.cast_add, Nat.cast_one]
    ring
  induction p using MvPolynomial.induction_on with
  | C c =>
    simp [translatedPolynomial, polynomialDerivation_C]
  | add p q hp hq =>
    simp only [map_add, translated_add, hp, hq, mul_add]
    abel
  | mul_X p x hp =>
    rw [(oscillatorDerivation D).leibniz]
    simp only [smul_eq_mul, translated_add, translated_mul]
    rw [hp, hgen, (polynomialDerivation D).leibniz, Polynomial.derivative_mul]
    simp only [smul_eq_mul]
    ring

private theorem charge_pairing (D : LatticeData) (α β : Charge D) :
    (∑ i, β i * bilinear D α (unitCharge D i)) = bilinear D α β := by
  classical
  simp only [bilinear, unitCharge, Finset.mul_sum]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    if_true]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- The actual input charge supplies precisely the missing inverse-variable term. -/
private theorem charge_transport (D : LatticeData) (α β : Charge D) :
    translatedPolynomial D α (chargePolynomial D β) =
      Polynomial.C (chargePolynomial D β) -
        Polynomial.C ((bilinear D α β : ℂ) • (1 : Oscillator D)) * Polynomial.X := by
  classical
  rw [chargePolynomial, translated_sum]
  simp only [translated_smul, translated_X, translationVariable,
    Nat.zero_add, pow_one, smul_sub, Finset.sum_sub_distrib]
  have hb : (∑ i : Fin D.rank, (β i : ℂ) *
      (bilinear D α (unitCharge D i) : ℂ)) = (bilinear D α β : ℂ) := by
    exact_mod_cast charge_pairing D α β
  simp only [← smul_mul_assoc, Polynomial.smul_C, smul_smul,
    ← Finset.sum_mul, ← map_sum]
  rw [show (∑ i : Fin D.rank,
      ((β i : ℂ) * (bilinear D α (unitCharge D i) : ℂ)) • (1 : Oscillator D)) =
      (bilinear D α β : ℂ) • (1 : Oscillator D) by
        rw [← Finset.sum_smul, hb] ]

/-- A finite coefficient convolution. Its linearity includes the full support of each input. -/
private def convolution (D : LatticeData) (α : Charge D) (b k : ℤ) :
    Polynomial (Oscillator D) →ₗ[Oscillator D] Oscillator D :=
  (Finsupp.lsum (Oscillator D) (fun d : ℕ =>
    LinearMap.mulRight (Oscillator D) (creationCoeff D α (k - b + d)))).comp
      ((AddMonoidAlgebra.coeffLinearEquiv (Oscillator D)).toLinearMap.comp
        (Polynomial.toFinsuppIsoLinear (Oscillator D)).toLinearMap)

private theorem convolution_monomial (D : LatticeData) (α : Charge D) (b k : ℤ)
    (d : ℕ) (a : Oscillator D) :
    convolution D α b k (Polynomial.monomial d a) =
      a * creationCoeff D α (k - b + d) := by
  simp [convolution, Polynomial.toFinsupp_monomial]

private theorem convolution_C_mul (D : LatticeData) (α : Charge D) (b k : ℤ)
    (a : Oscillator D) (q : Polynomial (Oscillator D)) :
    convolution D α b k (Polynomial.C a * q) = a * convolution D α b k q := by
  rw [← Polynomial.smul_eq_C_mul]
  exact map_smul _ _ _

/-- The escaping cancellation combines creation, annihilation and the changed charge. -/
private theorem convolution_cancellation (D : LatticeData) (α : Charge D)
    (b k : ℤ) (q : Polynomial (Oscillator D)) :
    oscillatorDerivation D (convolution D α b k q) -
        convolution D α b k (polynomialDerivation D q) +
        chargePolynomial D α * convolution D α b k q +
        (b : ℂ) • convolution D α b k (Polynomial.X * q) -
        convolution D α b k (Polynomial.X ^ 2 * q.derivative) =
      (k + 1 : ℂ) • convolution D α b (k + 1) q := by
  classical
  induction q using Polynomial.induction_on' with
  | add q r hq hr =>
    simp only [map_add, mul_add, smul_add]
    linear_combination hq + hr
  | monomial d a =>
    rw [convolution_monomial, (oscillatorDerivation D).leibniz,
      polynomialDerivation_monomial, convolution_monomial, creation_derivation]
    have hx : (Polynomial.X : Polynomial (Oscillator D)) * Polynomial.monomial d a =
        Polynomial.monomial (d + 1) a := by
      simp [← Polynomial.monomial_one_one_eq_X, Polynomial.monomial_mul_monomial,
        Nat.add_comm]
    have hd : (Polynomial.X : Polynomial (Oscillator D)) ^ 2 *
        (Polynomial.monomial d a).derivative =
        Polynomial.monomial (d + 1) ((d : Oscillator D) * a) := by
      cases d with
      | zero => simp
      | succ d =>
        simp [← Polynomial.monomial_one_one_eq_X,
          Polynomial.monomial_mul_monomial, Polynomial.monomial_pow, mul_comm,
          Nat.add_comm, Nat.add_left_comm]
    rw [hx, hd, convolution_monomial, convolution_monomial, convolution_monomial]
    rw [show k - b + (d + 1 : ℕ) = k - b + d + 1 by omega,
      show k + 1 - b + d = k - b + d + 1 by omega]
    simp only [smul_eq_mul, smul_eq_C_mul, C_add, C_sub, C_1,
      Int.cast_add, Int.cast_sub, Int.cast_natCast,
      map_natCast, map_intCast]
    ring

private theorem sector_apply (D : LatticeData) (β : Charge D) (p : Oscillator D) :
    sectorTranslation D β p = oscillatorDerivation D p + chargePolynomial D β * p := rfl

private theorem sector_convolution (D : LatticeData) (α β : Charge D)
    (k : ℤ) (p : Oscillator D) :
    sectorTranslation D (α + β)
        (convolution D α (bilinear D α β) k (translatedPolynomial D α p)) -
      convolution D α (bilinear D α β) k
        (translatedPolynomial D α (sectorTranslation D β p)) =
      (k + 1 : ℂ) • convolution D α (bilinear D α β) (k + 1)
        (translatedPolynomial D α p) := by
  have hQ : translatedPolynomial D α (sectorTranslation D β p) =
      polynomialDerivation D (translatedPolynomial D α p) +
        Polynomial.X ^ 2 * (translatedPolynomial D α p).derivative +
        Polynomial.C (chargePolynomial D β) * translatedPolynomial D α p -
        Polynomial.C ((bilinear D α β : ℂ) • (1 : Oscillator D)) *
          (Polynomial.X * translatedPolynomial D α p) := by
    rw [sector_apply, translated_add, translated_mul, annihilation_transport, charge_transport]
    ring
  rw [sector_apply, charge_add, hQ, map_sub, map_add, map_add,
    convolution_C_mul, convolution_C_mul]
  have h := convolution_cancellation D α (bilinear D α β) k
    (translatedPolynomial D α p)
  simp only [smul_eq_C_mul, mul_one] at h ⊢
  linear_combination h

/-- Exponent coefficient covariance on the full, finitely supported charge direct sum. -/
theorem rawCoeff_translation (D : LatticeData) (α : Charge D) (k : ℤ) :
    translation D * rawCoeff D α k - rawCoeff D α k * translation D =
      (k + 1 : ℂ) • rawCoeff D α (k + 1) := by
  apply Finsupp.lhom_ext
  intro β p
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply,
    translation_single]
  rw [(actual_creation_coefficient_transport D α α).2.2.1,
    (actual_creation_coefficient_transport D α α).2.2.1,
    (actual_creation_coefficient_transport D α α).2.2.1]
  simp only [rawSingle, map_smul, translation_single]
  change epsilon D α β • Finsupp.single (α + β)
      (sectorTranslation D (α + β)
        (convolution D α (bilinear D α β) k (translatedPolynomial D α p))) -
    epsilon D α β • Finsupp.single (α + β)
      (convolution D α (bilinear D α β) k
        (translatedPolynomial D α (sectorTranslation D β p))) = _
  rw [← smul_sub, ← Finsupp.single_sub, sector_convolution, ← Finsupp.smul_single,
    smul_comm]
  rfl

/-- Ordinary lattice modes, with the mode shift obtained from the actual field constructor. -/
theorem actual_lattice_translation_covariance (D : LatticeData) (α : Charge D)
    (n : ℤ) :
    translation D * ((actualField D α)[[n]]) -
        ((actualField D α)[[n]]) * translation D =
      -(n : ℂ) • ((actualField D α)[[n - 1]]) := by
  rw [actualField, VertexOperator.ncoeff_of_coeff, VertexOperator.ncoeff_of_coeff]
  have h := rawCoeff_translation D α (-n - 1)
  rw [show -n - 1 + 1 = -(n - 1) - 1 by omega] at h
  simpa only [Int.cast_sub, Int.cast_neg, Int.cast_one, sub_add_cancel] using h

private theorem sector_partial (D : LatticeData) (β : Charge D)
    (j : Fin D.rank) (r : ℕ) (p : Oscillator D) :
    sectorTranslation D β (pderiv (j,r) p) -
      pderiv (j,r) (sectorTranslation D β p) =
        (oscillatorDerivation D (pderiv (j,r) p) -
          pderiv (j,r) (oscillatorDerivation D p)) -
        pderiv (j,r) (chargePolynomial D β) * p := by
  simp only [sector_apply, map_add, Derivation.leibniz, smul_eq_mul]
  ring

private theorem positive_current_commutator (D : LatticeData) (β : Charge D)
    (i : Fin D.rank) (m : ℤ) (p : Oscillator D) :
    sectorTranslation D β
        ((m : ℂ) • ∑ j : Fin D.rank, (D.G i j : ℂ) • pderiv (j,(m-1).toNat) p) -
      (m : ℂ) • ∑ j : Fin D.rank, (D.G i j : ℂ) •
        pderiv (j,(m-1).toNat) (sectorTranslation D β p) =
      (m : ℂ) • ∑ j : Fin D.rank, (D.G i j : ℂ) •
        (sectorTranslation D β (pderiv (j,(m-1).toNat) p) -
          pderiv (j,(m-1).toNat) (sectorTranslation D β p)) := by
  simp only [map_smul, map_sum, smul_sub, Finset.sum_sub_distrib]

private theorem neutral_sector_translation (D : LatticeData) (β : Charge D)
    (i : Fin D.rank) (m : ℤ) (p : Oscillator D) :
    sectorTranslation D β (neutralPolynomialMode D i β m p) -
      neutralPolynomialMode D i β m (sectorTranslation D β p) =
        -(m : ℂ) • neutralPolynomialMode D i β (m - 1) p := by
  classical
  by_cases hm : m < 0
  · have hm1 : m - 1 < 0 := by omega
    have hn : ((-m-1).toNat : ℤ) = -m-1 := Int.toNat_of_nonneg (by omega)
    have hs : (-(m-1)-1).toNat = (-m-1).toNat + 1 := by omega
    simp only [neutralPolynomialMode, if_pos hm, if_pos hm1,
      LinearMap.mulLeft_apply, sector_apply, Derivation.leibniz,
      oscillatorDerivation, MvPolynomial.mkDerivation_X, hs, smul_eq_mul]
    rw [show ((-m-1).toNat + 1 : ℂ) = -(m : ℂ) by
      have h : ((-m-1).toNat : ℂ) = - (m : ℂ) - 1 := by exact_mod_cast hn
      linear_combination h]
    simp only [smul_eq_C_mul]
    ring
  · by_cases hz : m = 0
    · subst m
      simp [neutralPolynomialMode, map_smul]
    · have hp : 0 < m := by omega
      simp only [neutralPolynomialMode, if_neg hm, if_neg hz,
        LinearMap.smul_apply, LinearMap.sum_apply, Derivation.coeFn_coe]
      rw [positive_current_commutator]
      by_cases h1 : m = 1
      · subst m
        simp only [Int.reduceSub, Int.toNat_zero, Int.cast_one,
          one_smul, sector_partial, partial_translation_zero, partial_charge,
          if_true, zero_sub]
        have hb : bilinear D (unitCharge D i) β = ∑ j, D.G i j * β j := by
          simp [bilinear, unitCharge]
        simp only [lt_self_iff_false, if_false,
          LinearMap.smul_apply, LinearMap.id_apply]
        rw [hb]
        simp only [smul_eq_C_mul, C_mul,
          Int.cast_sum, Int.cast_mul, map_sum, Finset.sum_mul]
        simp [mul_comm, mul_assoc]
      · have hm1 : 0 < m - 1 := by omega
        let r := (m - 2).toNat
        have hr : (r : ℤ) = m - 2 := Int.toNat_of_nonneg (by omega)
        have hs : (m - 1).toNat = r + 1 := by omega
        have hrC : (r + 1 : ℂ) = (m - 1 : ℂ) := by
          have h : (r : ℂ) = (m : ℂ) - 2 := by exact_mod_cast hr
          linear_combination h
        simp only [hs, sector_partial, partial_translation_succ, partial_charge,
          Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, if_false,
          zero_mul, sub_zero, hrC]
        simp only [if_neg (by omega : ¬ m - 1 < 0),
          if_neg (by omega : m - 1 ≠ 0), LinearMap.smul_apply,
          LinearMap.sum_apply, Derivation.coeFn_coe, Int.cast_sub, Int.cast_one,
          Finset.smul_sum, smul_smul]
        apply Finset.sum_congr rfl
        intro j hj
        dsimp only [r]
        rw [show m - 1 - 1 = m - 2 by omega]
        congr 1
        ring

/-- All neutral current modes, including the separate positive-mode-one boundary. -/
theorem neutral_translation_covariance (D : LatticeData) (i : Fin D.rank)
    (m : ℤ) :
    translation D * neutralMode D i m - neutralMode D i m * translation D =
      -(m : ℂ) • neutralMode D i (m - 1) := by
  apply Finsupp.lhom_ext
  intro β p
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply,
    neutralMode, Finsupp.lsum_single, LinearMap.comp_apply, Finsupp.lsingle_apply,
    translation_single]
  change Finsupp.single β (sectorTranslation D β (neutralPolynomialMode D i β m p)) -
    Finsupp.single β (neutralPolynomialMode D i β m (sectorTranslation D β p)) = _
  rw [← Finsupp.single_sub, neutral_sector_translation, ← Finsupp.smul_single]

/-- The constructed operator, vacuum and both actual generating families in one contract. -/
theorem actual_translation_generators (D : LatticeData) :
    (∀ (β : Charge D) (p : Oscillator D),
      translation D (Finsupp.single β p) =
        Finsupp.single β (oscillatorDerivation D p + chargePolynomial D β * p)) ∧
    translation D (Finsupp.single (0 : Charge D) (1 : Oscillator D)) = 0 ∧
    (∀ (α : Charge D) (n : ℤ),
      translation D * ((actualField D α)[[n]]) -
          ((actualField D α)[[n]]) * translation D =
        -(n : ℂ) • ((actualField D α)[[n - 1]])) ∧
    (∀ (i : Fin D.rank) (m : ℤ),
      translation D * neutralMode D i m - neutralMode D i m * translation D =
        -(m : ℂ) • neutralMode D i (m - 1)) := by
  exact ⟨translation_single D, translation_vacuum D,
    actual_lattice_translation_covariance D, neutral_translation_covariance D⟩


private theorem inverse_charge_contractions (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) (β : Charge D) :
    (∀ i, ∑ j : Fin D.rank, H i j * chargeScalar D β j = (β i : ℂ)) ∧
    (∀ j, ∑ i : Fin D.rank, H i j * chargeScalar D β i = (β j : ℂ)) := by
  classical
  have hcharge (i : Fin D.rank) : chargeScalar D β i =
      ∑ a : Fin D.rank, (D.G i a : ℂ) * (β a : ℂ) := by
    simp [chargeScalar, bilinear, unitCharge, Int.cast_sum]
  have row (i a : Fin D.rank) : ∑ j, H i j * (D.G j a : ℂ) = if i = a then 1 else 0 := by
    simpa [Matrix.mul_apply, gramComplex, Matrix.one_apply] using
      congrArg (fun M : Matrix (Fin D.rank) (Fin D.rank) ℂ => M i a) hHG
  have col (j a : Fin D.rank) : ∑ i, H i j * (D.G i a : ℂ) = if j = a then 1 else 0 := by
    simpa [Matrix.mul_apply, gramComplex, Matrix.one_apply, D.symmetric a,
      mul_comm, eq_comm] using
      congrArg (fun M : Matrix (Fin D.rank) (Fin D.rank) ℂ => M a j) hGH
  constructor
  · intro i
    calc
      _ = ∑ a : Fin D.rank, (∑ j, H i j * (D.G j a : ℂ)) * (β a : ℂ) := by
        simp only [hcharge, Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro a ha
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = _ := by simp [row]
  · intro j
    calc
      _ = ∑ a : Fin D.rank, (∑ i, H i j * (D.G i a : ℂ)) * (β a : ℂ) := by
        simp only [hcharge, Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro a ha
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = _ := by simp [col]

/-- The actual minus-one coefficient has precisely the charged ground translation term. -/
theorem sugawaraMode_ground_minus_one (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) (β : Charge D) :
    sugawaraMode D H (-1) (Finsupp.single β (1 : Oscillator D)) =
      Finsupp.single β (chargePolynomial D β) := by
  classical
  have inv := inverse_charge_contractions D H hHG hGH β
  have negative (i : Fin D.rank) (p : Oscillator D) :
      neutralMode D i (-1) (Finsupp.single β p) = Finsupp.single β (X (i,0)*p) := by
    simp [neutralPolynomialMode]
  have term (i j : Fin D.rank) :
      normalSummand D i j (-1) 0 (Finsupp.single β 1) +
        normalSummand D i j 0 (-1) (Finsupp.single β 1) =
      chargeScalar D β j • Finsupp.single β (X (i,0)) +
        chargeScalar D β i • Finsupp.single β (X (j,0)) := by
    simp only [normalSummand, show (-1 : ℤ) < 0 by omega, if_true,
      show ¬(0 : ℤ) < 0 by omega, if_false, Module.End.mul_apply,
      neutralMode_zero_single, map_smul, negative, mul_one]
  rw [sugawaraMode_interval_sum, ground_frequency_bound]
  have hI : Finset.Icc (-1 : ℤ) 0 = {-1,0} := by decide
  simp only [Nat.cast_zero, sub_zero, min_eq_right (by omega : (-1 : ℤ) ≤ 0), hI,
    Finset.sum_insert (by decide : (-1 : ℤ) ∉ ({0} : Finset ℤ)), Finset.sum_singleton,
    show (-1 : ℤ)-(-1) = 0 by omega, sub_zero]
  simp_rw [term, smul_add, smul_smul]
  simp only [Finset.sum_add_distrib]
  have first : (∑ i : Fin D.rank, ∑ j : Fin D.rank,
      (H i j * chargeScalar D β j) • Finsupp.single β (X (i,0))) =
      Finsupp.single β (chargePolynomial D β) := by
    simp_rw [← Finset.sum_smul, inv.1]
    simp [chargePolynomial, Finsupp.smul_single, Finsupp.single_finsetSum]
  have second : (∑ i : Fin D.rank, ∑ j : Fin D.rank,
      (H i j * chargeScalar D β i) • Finsupp.single β (X (j,0))) =
      Finsupp.single β (chargePolynomial D β) := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_smul, inv.2]
    simp [chargePolynomial, Finsupp.smul_single, Finsupp.single_finsetSum]
  rw [first, second, ← two_smul ℂ, smul_smul]
  norm_num

/-- The actual normal-product coefficient L(-1) is the constructed charge-sensitive translation. -/
theorem sugawaraMode_minus_one_eq_translation (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) :
    sugawaraMode D H (-1) = translation D := by
  apply Finsupp.lhom_ext'
  intro β
  let A : Module.End ℂ (Oscillator D) := sectorSugawaraMode D H β (-1) - sectorTranslation D β
  have hA (i : Fin D.rank) (q : ℤ) :
      A * neutralPolynomialMode D i β q - neutralPolynomialMode D i β q * A = 0 := by
    apply LinearMap.ext
    intro p
    have hL := congrArg (fun F : Module.End ℂ (Carrier D) => (F (Finsupp.single β p)) β)
      (sugawaraMode_current_commutator D H hHG hGH i (-1) q)
    have hT := congrArg (fun F : Module.End ℂ (Carrier D) => (F (Finsupp.single β p)) β)
      (neutral_translation_covariance D i q)
    simp only [LinearMap.sub_apply, Module.End.mul_apply, neutralMode_single,
      sugawaraMode_single_sector, translation_single, Finsupp.sub_apply,
      Finsupp.single_eq_same, LinearMap.smul_apply, Finsupp.smul_apply] at hL hT
    calc
      _ = (sectorSugawaraMode D H β (-1) (neutralPolynomialMode D i β q p) -
      neutralPolynomialMode D i β q (sectorSugawaraMode D H β (-1) p)) -
      (sectorTranslation D β (neutralPolynomialMode D i β q p) -
      neutralPolynomialMode D i β q (sectorTranslation D β p)) := by
        simp only [A, LinearMap.sub_apply, Module.End.mul_apply, map_sub,
          LinearMap.zero_apply]
        abel
      _ = 0 := by
        change _ - (oscillatorDerivation D (neutralPolynomialMode D i β q p) +
          chargePolynomial D β * neutralPolynomialMode D i β q p -
          neutralPolynomialMode D i β q
            (oscillatorDerivation D p + chargePolynomial D β * p)) = 0
        rw [hL, hT, show (-1 : ℤ)+q = q-1 by omega, sub_self]
  have hs := polynomial_current_commutant_scalar D H hHG β A hA
  have hg := congrArg (fun v : Carrier D => v β)
    (sugawaraMode_ground_minus_one D H hHG hGH β)
  simp only [sugawaraMode_single_sector, Finsupp.single_eq_same] at hg
  have hz : A 1 = 0 := by simp [A, hg, sectorTranslation]
  rw [hz, map_zero, zero_smul] at hs
  apply LinearMap.ext
  intro p
  have hp := congrArg (fun F : Module.End ℂ (Oscillator D) => F p) hs
  have he : sectorSugawaraMode D H β (-1) p = sectorTranslation D β p := by
    exact sub_eq_zero.mp hp
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, sugawaraMode_single_sector,
    translation_single, he]
  rfl


/-- The inverse-Gram charge quadratic is the original lattice norm divided by two. -/
theorem chargeQuadratic_eq (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) (β : Charge D) :
    chargeQuadratic D H β = (bilinear D β β : ℂ)/2 := by
  classical
  have inv := (inverse_charge_contractions D H hHG hGH β).1
  have hcharge (i : Fin D.rank) : chargeScalar D β i =
      ∑ a : Fin D.rank, (D.G i a : ℂ) * (β a : ℂ) := by
    simp [chargeScalar, bilinear, unitCharge, Int.cast_sum]
  have hsum : (∑ i : Fin D.rank, ∑ j : Fin D.rank,
      H i j * chargeScalar D β i * chargeScalar D β j) = (bilinear D β β : ℂ) := by
    calc
      _ = ∑ i : Fin D.rank, chargeScalar D β i * (∑ j, H i j * chargeScalar D β j) := by
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = ∑ i : Fin D.rank, chargeScalar D β i * (β i : ℂ) := by simp_rw [inv]
      _ = _ := by
        simp only [hcharge, bilinear, Int.cast_sum, Int.cast_mul, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        ring
  rw [chargeQuadratic, hsum]
  ring

/-- The actual zero mode is frequency Euler plus the charged lattice norm. -/
theorem sugawaraMode_zero_single (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (β : Charge D) (p : Oscillator D) :
    sugawaraMode D H 0 (Finsupp.single β p) =
      Finsupp.single β
        (oscillatorEuler D p + ((bilinear D β β : ℂ)/2) • p) := by
  let A : Module.End ℂ (Oscillator D) := sectorSugawaraMode D H β 0 - (oscillatorEuler D).toLinearMap
  have hA (i : Fin D.rank) (q : ℤ) :
      A * neutralPolynomialMode D i β q - neutralPolynomialMode D i β q * A = 0 := by
    have hL : sectorSugawaraMode D H β 0 * neutralPolynomialMode D i β q -
        neutralPolynomialMode D i β q * sectorSugawaraMode D H β 0 =
          -(q : ℂ) • neutralPolynomialMode D i β q := by
      apply LinearMap.ext
      intro p
      have h := congrArg (fun F : Module.End ℂ (Carrier D) => (F (Finsupp.single β p)) β)
        (sugawaraMode_current_commutator D H hHG hGH i 0 q)
      simpa only [LinearMap.sub_apply, Module.End.mul_apply, neutralMode_single,
        sugawaraMode_single_sector, Finsupp.sub_apply, Finsupp.single_eq_same,
        LinearMap.smul_apply, Finsupp.smul_apply, zero_add] using h
    calc
      _ = (sectorSugawaraMode D H β 0 * neutralPolynomialMode D i β q -
          neutralPolynomialMode D i β q * sectorSugawaraMode D H β 0) -
        ((oscillatorEuler D).toLinearMap * neutralPolynomialMode D i β q -
          neutralPolynomialMode D i β q * (oscillatorEuler D).toLinearMap) := by
        dsimp only [A]
        noncomm_ring
      _ = 0 := by rw [hL, oscillatorEuler_current, sub_self]
  have hs := polynomial_current_commutant_scalar D H hHG β A hA
  have hg := congrArg (fun v : Carrier D => v β) (sugawaraMode_ground_zero D H β)
  simp only [sugawaraMode_single_sector, Finsupp.smul_single, Finsupp.single_eq_same] at hg
  have hz : constantCoeff (A 1) = chargeQuadratic D H β := by simp [A, hg]
  rw [hz, chargeQuadratic_eq D H hHG hGH] at hs
  have hp := congrArg (fun F : Module.End ℂ (Oscillator D) => F p) hs
  have he : sectorSugawaraMode D H β 0 p =
      oscillatorEuler D p + ((bilinear D β β : ℂ)/2) • p := by
    simpa only [LinearMap.smul_apply, Module.End.one_apply, Derivation.coeFn_coe] using
      sub_eq_iff_eq_add'.mp hp
  rw [sugawaraMode_single_sector, he]


private theorem oscillatorEuler_monomial (D : LatticeData) (d : Index D →₀ ℕ) (c : ℂ) :
    oscillatorEuler D (monomial d c) =
      ((Finsupp.weight (fun x : Index D => x.2+1) d : ℕ) : ℂ) • monomial d c := by
  classical
  rw [oscillatorEuler, mkDerivation_monomial]
  have term (x : Index D) :
      monomial (d-Finsupp.single x 1) (d x : ℂ) • ((x.2+1 : ℂ) • X x) =
        ((x.2+1 : ℂ)*(d x : ℂ)) • (monomial d (1 : ℂ) : Oscillator D) := by
    have h := X_mul_pderiv_monomial (i := x) (m := d) (r := (1 : ℂ))
    simp only [pderiv_monomial, one_mul] at h
    change monomial (d-Finsupp.single x 1) (d x : ℂ) * ((x.2+1 : ℂ) • X x) = _
    rw [mul_smul_comm, mul_comm _ (X x), h]
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  simp_rw [Finsupp.sum, term, ← Finset.sum_smul]
  have weight : (∑ x ∈ d.support, (x.2+1 : ℂ)*(d x : ℂ)) =
      ((Finsupp.weight (fun x : Index D => x.2+1) d : ℕ) : ℂ) := by
    simp only [Finsupp.weight_apply, Finsupp.sum, smul_eq_mul, Nat.cast_sum,
      Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    apply Finset.sum_congr rfl
    intro x hx
    ring
  rw [weight, smul_comm c]
  simp [smul_monomial]

/-- Weighted homogeneous oscillators have the frequency degree plus their charged norm. -/
theorem sugawaraMode_weighted_homogeneous (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (β : Charge D) (p : Oscillator D) (r : ℕ)
    (hp : IsWeightedHomogeneous (fun x : Index D => x.2+1) p r) :
    sugawaraMode D H 0 (Finsupp.single β p) =
      ((r : ℂ)+(bilinear D β β : ℂ)/2) • Finsupp.single β p := by
  classical
  have hEuler : oscillatorEuler D p = (r : ℂ) • p := by
    conv_lhs => rw [p.as_sum]
    rw [map_sum]
    calc
      _ = ∑ d ∈ p.support, (r : ℂ) • monomial d (coeff d p) := by
        apply Finset.sum_congr rfl
        intro d hd
        rw [oscillatorEuler_monomial, hp (mem_support_iff.mp hd)]
      _ = _ := by rw [← Finset.smul_sum, ← p.as_sum]
  rw [sugawaraMode_zero_single D H hHG hGH, hEuler, ← add_smul, Finsupp.smul_single]

/-- The actual Virasoro modes act as conformal translation on both genuine generating families. -/
theorem actual_conformal_generators (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) :
    (∀ m n : ℤ, sugawaraMode D H m * sugawaraMode D H n -
      sugawaraMode D H n * sugawaraMode D H m =
      ((m-n : ℤ) : ℂ) • sugawaraMode D H (m+n) +
        (if m+n = 0 then (D.rank : ℂ)/12*((m : ℂ)^3-m) else 0) •
          (1 : Module.End ℂ (Carrier D))) ∧
    (∀ (β : Charge D) (p : Oscillator D),
      sugawaraMode D H 0 (Finsupp.single β p) =
        Finsupp.single β
        (oscillatorEuler D p + ((bilinear D β β : ℂ)/2) • p)) ∧
    (∀ (β : Charge D) (p : Oscillator D),
      sugawaraMode D H (-1) (Finsupp.single β p) =
        Finsupp.single β (oscillatorDerivation D p + chargePolynomial D β * p)) ∧
    sugawaraMode D H (-1) (Finsupp.single (0 : Charge D) (1 : Oscillator D)) = 0 ∧
    (∀ (α : Charge D) (n : ℤ),
      sugawaraMode D H (-1) * ((actualField D α)[[n]]) -
        ((actualField D α)[[n]]) * sugawaraMode D H (-1) =
        -(n : ℂ) • ((actualField D α)[[n-1]])) ∧
    (∀ (i : Fin D.rank) (q : ℤ),
      sugawaraMode D H (-1) * neutralMode D i q -
        neutralMode D i q * sugawaraMode D H (-1) =
        -(q : ℂ) • neutralMode D i (q-1)) ∧
    (∀ (β : Charge D) (p : Oscillator D) (r : ℕ),
      IsWeightedHomogeneous (fun x : Index D => x.2+1) p r →
      sugawaraMode D H 0 (Finsupp.single β p) =
        ((r : ℂ)+(bilinear D β β : ℂ)/2) • Finsupp.single β p) := by
  constructor
  · exact sugawaraMode_virasoro D H hHG hGH
  · constructor
    · exact sugawaraMode_zero_single D H hHG hGH
    · rw [sugawaraMode_minus_one_eq_translation D H hHG hGH]
      have g := actual_translation_generators D
      exact ⟨g.1, g.2.1, g.2.2.1, g.2.2.2,
        sugawaraMode_weighted_homogeneous D H hHG hGH⟩

end
end D5.S3.VertexAlgebra.LatticeSugawaraConformal
