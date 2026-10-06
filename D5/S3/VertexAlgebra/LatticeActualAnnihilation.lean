/- GID: D5/S3/VertexAlgebra/LatticeActualAnnihilation
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeActualAnnihilation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Current derivations act on actual creation exponentials and translated polynomials. -/

import D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
import D5.S3.VertexAlgebra.LatticeActualCurrentAlgebra
import D5.S3.VertexAlgebra.LatticeActualProductKernel
import Mathlib.Algebra.Polynomial.Derivation

/- Coefficientwise derivation of the actual creation exponential.
   Adapted transparently from the terminal sealed LatticeSugawaraConformal
   seriesDerivation and creation_derivation_series ODE proof. The derivation
   is now a parameter; the actual exponential and scalar hypotheses are unchanged. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.ActualSeriesDerivation
open LatticeGeneratingFieldLocality
open scoped BigOperators
noncomputable section

def seriesDerivation (D : LatticeData) (d : Derivation ℂ (Oscillator D) (Oscillator D)) :
    Derivation ℂ (PowerSeries (Oscillator D)) (PowerSeries (Oscillator D)) where
  toFun f := PowerSeries.mk (fun n => d (PowerSeries.coeff n f))
  map_add' f g := by apply PowerSeries.ext; intro n; simp
  map_smul' c f := by apply PowerSeries.ext; intro n; simp
  map_one_eq_zero' := by
    apply PowerSeries.ext
    intro n
    simp [PowerSeries.coeff_one, apply_ite]
  leibniz' f g := by
    apply PowerSeries.ext
    intro n
    change PowerSeries.coeff n (PowerSeries.mk (fun n => d (PowerSeries.coeff n (f*g)))) =
      PowerSeries.coeff n (f * PowerSeries.mk (fun n => d (PowerSeries.coeff n g)) +
        g * PowerSeries.mk (fun n => d (PowerSeries.coeff n f)))
    rw [mul_comm g (PowerSeries.mk (fun n => d (PowerSeries.coeff n f)))]
    simp only [PowerSeries.coeff_mk, map_add, PowerSeries.coeff_mul, map_sum,
      Derivation.leibniz, smul_eq_mul, Finset.sum_add_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro x hx
    ring

@[simp] theorem series_coeff (D : LatticeData)
    (d : Derivation ℂ (Oscillator D) (Oscillator D))
    (f : PowerSeries (Oscillator D)) (n : ℕ) :
    PowerSeries.coeff n (seriesDerivation D d f) = d (PowerSeries.coeff n f) := by
  change PowerSeries.coeff n (PowerSeries.mk (fun n => d (PowerSeries.coeff n f))) = _
  rw [PowerSeries.coeff_mk]

theorem derivative_commute (D : LatticeData)
    (d : Derivation ℂ (Oscillator D) (Oscillator D)) (f : PowerSeries (Oscillator D)) :
    seriesDerivation D d (PowerSeries.derivative (Oscillator D) f) =
      PowerSeries.derivative (Oscillator D) (seriesDerivation D d f) := by
  apply PowerSeries.ext
  intro n
  simp only [series_coeff, PowerSeries.coeff_derivative, Derivation.leibniz,
    Derivation.map_add, Derivation.map_natCast, Derivation.map_one_eq_zero,
    add_zero, smul_eq_mul]
  ring

theorem exponential_constant (D : LatticeData) (α : Charge D) :
    PowerSeries.coeff 0 (creationExponential D α) = 1 := by
  have hA : PowerSeries.constantCoeff (creationSeries D α) = 0 := by
    simp [creationSeries, ← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  rw [creationExponential, PowerSeries.coeff_subst'
    (PowerSeries.HasSubst.of_constantCoeff_zero' hA), finsum_eq_single _ 0]
  · simp
  · intro j hj
    rw [PowerSeries.coeff_zero_eq_constantCoeff, map_pow, hA]
    simp [hj]

/-- Any coefficientwise polynomial derivation obeys the exponential chain rule. -/
theorem actual_exponential_derivation (D : LatticeData)
    (d : Derivation ℂ (Oscillator D) (Oscillator D)) (α : Charge D) :
    seriesDerivation D d (creationExponential D α) =
      creationExponential D α * seriesDerivation D d (creationSeries D α) := by
  let E := creationExponential D α
  let S := creationSeries D α
  let A := PowerSeries.derivative (Oscillator D) S
  let H := seriesDerivation D d E - E * seriesDerivation D d S
  have hS : PowerSeries.constantCoeff S = 0 := by
    simp [S, creationSeries, ← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  have hE : PowerSeries.derivative (Oscillator D) E = E*A := by
    dsimp [E,creationExponential,A,S]
    rw [PowerSeries.derivative_subst (PowerSeries.HasSubst.of_constantCoeff_zero' hS),
      PowerSeries.derivative_exp]
  have hH : PowerSeries.derivative (Oscillator D) H = H*A := by
    dsimp only [H]
    rw [map_sub, ← derivative_commute, hE, (seriesDerivation D d).leibniz,
      (PowerSeries.derivative (Oscillator D)).leibniz, hE,
      ← derivative_commute]
    change _ = (seriesDerivation D d E - E * seriesDerivation D d S)*A
    simp only [smul_eq_mul]
    ring
  have h0 : PowerSeries.coeff 0 H = 0 := by
    dsimp only [H]
    rw [map_sub, series_coeff, exponential_constant, Derivation.map_one_eq_zero]
    rw [PowerSeries.coeff_mul]
    simp only [Finset.Nat.antidiagonal_zero,Finset.sum_singleton,series_coeff]
    simp [S,creationSeries]
  have hz : H = 0 := by
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
        have hs : (∑ x ∈ Finset.HasAntidiagonal.antidiagonal n,
            PowerSeries.coeff x.1 H * PowerSeries.coeff x.2 A) = 0 := by
          apply Finset.sum_eq_zero
          intro x hx
          rw [ih x.1 (by have := Finset.HasAntidiagonal.mem_antidiagonal.mp hx; omega),zero_mul]
        rw [hs] at hr
        have hr' : (n+1) • PowerSeries.coeff (n+1) H = (n+1) • (0 : Oscillator D) := by
          simpa only [nsmul_eq_mul, Nat.cast_add, Nat.cast_one, mul_comm,
            mul_zero, zero_mul] using hr
        exact (smul_right_inj (Nat.succ_ne_zero n)).mp hr'
  exact sub_eq_zero.mp hz

end
end D5.S3.VertexAlgebra.ActualSeriesDerivation

/- Actual current annihilation on the lattice exponential and polynomial shifts.
   Coefficientwise ODE and polynomial induction adapt the terminal sealed
   LatticeSugawaraConformal proof mechanisms, with exact source attribution.
   Bakalov--Kac math/0402315v1, section 4.1. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace D5.S3.VertexAlgebra.LatticeActualAnnihilation
open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration
open LatticeActualCurrentAlgebra LatticeActualProductKernel ActualSeriesDerivation MvPolynomial
open scoped BigOperators
noncomputable section

def annihilationDerivation (D : LatticeData) (i : Fin D.rank) (k : ℕ) :
    Derivation ℂ (Oscillator D) (Oscillator D) :=
  ∑ j : Fin D.rank, (D.G i j : ℂ) • pderiv (j,k)

@[simp] theorem annihilation_apply (D : LatticeData) (i : Fin D.rank) (k : ℕ)
    (p : Oscillator D) : annihilationDerivation D i k p = annihilate D i k p := by
  unfold annihilationDerivation
  change (Derivation.coeFnAddMonoidHom (∑ j : Fin D.rank,
      (D.G i j : ℂ) • pderiv (j,k))) p = _
  rw [map_sum]
  simp only [Finset.sum_apply,Derivation.coeFnAddMonoidHom_apply,
    Derivation.coe_smul,Pi.smul_apply,annihilate,LinearMap.sum_apply,
    LinearMap.smul_apply,Derivation.coeFn_coe]

theorem pairing_sum (D : LatticeData) (i : Fin D.rank) (α : Charge D) :
    (∑ j : Fin D.rank, (α j : ℂ)*(D.G i j : ℂ)) = (bilinear D (unitCharge D i) α : ℂ) := by
  have h : bilinear D (unitCharge D i) α = ∑ j, D.G i j * α j := by
    simp [bilinear,unitCharge]
  rw [h]
  push_cast
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem annihilation_linear_creation (D : LatticeData) (i : Fin D.rank)
    (k n : ℕ) (α : Charge D) :
    annihilationDerivation D i k (∑ j : Fin D.rank, (α j : ℂ) • X (j,n)) =
      if k = n then (bilinear D (unitCharge D i) α : ℂ) • (1 : Oscillator D) else 0 := by
  rw [annihilation_apply,map_sum]
  simp_rw [map_smul,annihilate_X]
  by_cases h : k = n
  · simp only [if_pos h,smul_smul]
    rw [← Finset.sum_smul,pairing_sum]
  · simp [h]

theorem annihilation_logarithm (D : LatticeData) (i : Fin D.rank)
    (k : ℕ) (α : Charge D) :
    seriesDerivation D (annihilationDerivation D i k) (creationSeries D α) =
      PowerSeries.C (((k+1 : ℂ)⁻¹ * (bilinear D (unitCharge D i) α : ℂ)) •
        (1 : Oscillator D)) * PowerSeries.X^(k+1) := by
  apply PowerSeries.ext
  intro n
  rw [series_coeff]
  cases n with
  | zero => simp [creationSeries]
  | succ n =>
    simp only [creationSeries,PowerSeries.coeff_mk,dif_neg (Nat.succ_ne_zero n),
      Nat.add_sub_cancel,
      PowerSeries.coeff_C_mul,PowerSeries.coeff_X_pow]
    rw [annihilation_apply,map_smul,←annihilation_apply,annihilation_linear_creation]
    by_cases h : k = n
    · subst n
      simp only [if_true,smul_smul,mul_one,Nat.cast_add,Nat.cast_one]
    · simp [h,Ne.symm h]

theorem annihilation_creation_nat (D : LatticeData) (i : Fin D.rank)
    (k n : ℕ) (α : Charge D) :
    annihilate D i k (PowerSeries.coeff n (creationExponential D α)) =
      if k+1 ≤ n then
        ((k+1 : ℂ)⁻¹ * (bilinear D (unitCharge D i) α : ℂ)) •
          PowerSeries.coeff (n-(k+1)) (creationExponential D α) else 0 := by
  have h := congrArg (PowerSeries.coeff n)
    (actual_exponential_derivation D (annihilationDerivation D i k) α)
  rw [series_coeff,annihilation_apply,annihilation_logarithm,←mul_assoc,
    PowerSeries.coeff_mul_X_pow'] at h
  rw [h]
  split_ifs
  · rw [PowerSeries.coeff_mul_C,mul_smul_comm,mul_one]
  · rfl

/-- Actual creation coefficients have the exact annihilation commutator factor. -/
theorem annihilation_creation (D : LatticeData) (i : Fin D.rank) (k : ℕ)
    (α : Charge D) (t : ℤ) :
    annihilate D i k (creationCoeff D α t) =
      ((k+1 : ℂ)⁻¹ * (bilinear D (unitCharge D i) α : ℂ)) •
        creationCoeff D α (t-(k+1 : ℕ)) := by
  by_cases ht : t < 0
  · rw [creationCoeff,dif_pos ht,map_zero,creationCoeff,
      dif_pos (show t-(k+1 : ℕ) < 0 by omega),smul_zero]
  · rw [creationCoeff,dif_neg ht,annihilation_creation_nat]
    by_cases h : (k+1 : ℕ) ≤ t.toNat
    · rw [if_pos h,creationCoeff,dif_neg (by omega),
        show (t-(k+1 : ℕ)).toNat = t.toNat-(k+1) by omega]
    · rw [if_neg h,creationCoeff,dif_pos (by omega),smul_zero]

def polynomialDerivation (D : LatticeData) (i : Fin D.rank) (k : ℕ) :
    Derivation ℂ (Polynomial (Oscillator D)) (Polynomial (Oscillator D)) :=
  PolynomialModule.equivPolynomialSelf.toLinearMap.compDer
    (annihilationDerivation D i k).mapCoeffs

theorem polynomialDerivation_monomial (D : LatticeData) (i : Fin D.rank)
    (k d : ℕ) (p : Oscillator D) :
    polynomialDerivation D i k (Polynomial.monomial d p) =
      Polynomial.monomial d (annihilate D i k p) := by
  apply Polynomial.ext
  intro j
  change annihilationDerivation D i k ((Polynomial.monomial d p).coeff j) = _
  by_cases h : d = j <;> simp [Polynomial.coeff_monomial,h]

theorem polynomialDerivation_C (D : LatticeData) (i : Fin D.rank)
    (k : ℕ) (p : Oscillator D) :
    polynomialDerivation D i k (Polynomial.C p) = Polynomial.C (annihilate D i k p) :=
  polynomialDerivation_monomial D i k 0 p

theorem polynomialDerivation_X (D : LatticeData) (i : Fin D.rank) (k : ℕ) :
    polynomialDerivation D i k Polynomial.X = 0 := by
  rw [←Polynomial.monomial_one_one_eq_X,polynomialDerivation_monomial]
  simp [annihilate]

/-- Actual translations commute with every positive current derivation. -/
theorem annihilation_transport (D : LatticeData) (i : Fin D.rank) (k : ℕ)
    (α : Charge D) (p : Oscillator D) :
    translatedPolynomial D α (annihilate D i k p) =
      polynomialDerivation D i k (translatedPolynomial D α p) := by
  have hX (x : Index D) : translatedPolynomial D α (annihilate D i k (X x)) =
      polynomialDerivation D i k (translatedPolynomial D α (X x)) := by
    rcases x with ⟨j,l⟩
    have hc (z : ℂ) : annihilate D i k (z • (1 : Oscillator D)) = 0 := by
      simp [annihilate]
    have ht (z : ℂ) : translatedPolynomial D α (z • (1 : Oscillator D)) =
        Polynomial.C (z • (1 : Oscillator D)) := by
      simp [translatedPolynomial,Algebra.smul_def]
    rw [show translatedPolynomial D α (X (j,l)) = translationVariable D α j l by
      simp [translatedPolynomial]]
    simp only [translationVariable,map_sub,Derivation.leibniz,polynomialDerivation_C,
      hc,polynomialDerivation_X,Derivation.leibniz_pow,smul_zero,zero_smul,
      add_zero,zero_add,map_zero,sub_zero]
    rw [annihilate_X]
    by_cases h : k = l
    · simp only [if_pos h]
      exact ht _
    · simp [h,translatedPolynomial]
  induction p using MvPolynomial.induction_on with
  | C c => simp [translatedPolynomial,polynomialDerivation_C,annihilate]
  | add p q hp hq => simp only [map_add,translatedPolynomial,map_add] at hp hq ⊢; rw [hp,hq]
  | mul_X p x hp =>
    rw [annihilate_mul]
    simp only [translatedPolynomial,map_add,map_mul] at hp hX ⊢
    rw [hp,hX,(polynomialDerivation D i k).leibniz]
    simp only [smul_eq_mul]
    ring

theorem annihilation_convolution (D : LatticeData) (i : Fin D.rank) (k : ℕ)
    (α : Charge D) (s : ℤ) (q : Polynomial (Oscillator D)) :
    annihilate D i k (convolution D α s q) =
      convolution D α s (polynomialDerivation D i k q) +
        ((k+1 : ℂ)⁻¹ * (bilinear D (unitCharge D i) α : ℂ)) •
          convolution D α (s-(k+1 : ℕ)) q := by
  induction q using Polynomial.induction_on' with
  | add q q' h h' => simp only [map_add,h,h',smul_add]; abel
  | monomial n a =>
    rw [convolution_monomial,annihilate_mul,annihilation_creation,
      polynomialDerivation_monomial,convolution_monomial,convolution_monomial]
    rw [show s+(n : ℤ)-(k+1 : ℕ) = s-(k+1 : ℕ)+n by omega]
    rw [mul_smul_comm]

end
end D5.S3.VertexAlgebra.LatticeActualAnnihilation
