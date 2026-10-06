/- GID: D5/S3/VertexAlgebra/LatticeActualProductKernel
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeActualProductKernel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Polynomial convolutions give finite intermediate-vector bounds for the actual common kernel. -/

import D5.S3.VertexAlgebra.LatticeActualGeneratorLocality

/- Actual coefficient convolution and common-kernel recurrences.
   The linear convolution presentation adapts the explicit polynomial functional
   inside actual_creation_coefficient_transport and the terminal sealed
   LatticeSugawaraConformal convolution proof. No theorem is transported
   between carriers. Bakalov--Kac math/0402315v1, section 4.1. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.LatticeActualProductKernel
open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration
open LatticeActualGeneratorLocality MvPolynomial
open scoped BigOperators VertexOperator
noncomputable section

def convolution (D : LatticeData) (α : Charge D) (s : ℤ) :
    Polynomial (Oscillator D) →ₗ[Oscillator D] Oscillator D :=
  (Finsupp.lsum (Oscillator D) (fun d : ℕ =>
    LinearMap.mulRight (Oscillator D) (creationCoeff D α (s + d)))).comp
      ((AddMonoidAlgebra.coeffLinearEquiv (Oscillator D)).toLinearMap.comp
        (Polynomial.toFinsuppIsoLinear (Oscillator D)).toLinearMap)

theorem convolution_monomial (D : LatticeData) (α : Charge D) (s : ℤ)
    (d : ℕ) (a : Oscillator D) :
    convolution D α s (Polynomial.monomial d a) = a * creationCoeff D α (s+d) := by
  simp [convolution, Polynomial.toFinsupp_monomial]

theorem convolution_C_mul (D : LatticeData) (α : Charge D) (s : ℤ)
    (a : Oscillator D) (q : Polynomial (Oscillator D)) :
    convolution D α s (Polynomial.C a * q) = a * convolution D α s q := by
  rw [← Polynomial.smul_eq_C_mul]
  exact map_smul _ _ _

theorem convolution_X_pow (D : LatticeData) (α : Charge D) (s : ℤ)
    (r : ℕ) (q : Polynomial (Oscillator D)) :
    convolution D α s (Polynomial.X^r * q) = convolution D α (s+r) q := by
  induction q using Polynomial.induction_on' with
  | add q q' h h' => simp only [mul_add, map_add, h, h']
  | monomial d a =>
    rw [Polynomial.X_pow_mul_monomial, convolution_monomial, convolution_monomial]
    congr 2
    push_cast
    omega

theorem raw_single_convolution (D : LatticeData) (α : Charge D) (k : ℤ)
    (δ : Charge D) (p : Oscillator D) :
    rawCoeff D α k (Finsupp.single δ p) = epsilon D α δ •
      Finsupp.single (α+δ) (convolution D α (k-bilinear D α δ)
        (translatedPolynomial D α p)) := by
  rw [(actual_creation_coefficient_transport D α α).2.2.1]
  rfl

def pairConvolution (D : LatticeData) (α β : Charge D) (s t : ℤ) :
    PairPolynomial D →ₗ[Oscillator D] Oscillator D :=
  (Finsupp.lsum (Oscillator D) (fun e : Fin 2 →₀ ℕ =>
    LinearMap.mulRight (Oscillator D)
      (creationCoeff D α (s+e 0) * creationCoeff D β (t+e 1)))).comp
        (AddMonoidAlgebra.coeffLinearEquiv (Oscillator D)).toLinearMap

theorem pairConvolution_monomial (D : LatticeData) (α β : Charge D) (s t : ℤ)
    (e : Fin 2 →₀ ℕ) (a : Oscillator D) :
    pairConvolution D α β s t (MvPolynomial.monomial e a) =
      a * (creationCoeff D α (s+e 0) * creationCoeff D β (t+e 1)) := by
  simp [pairConvolution, MvPolynomial.monomial, mul_assoc]

theorem pairConvolution_C_mul (D : LatticeData) (α β : Charge D) (s t : ℤ)
    (a : Oscillator D) (q : PairPolynomial D) :
    pairConvolution D α β s t (MvPolynomial.C a * q) =
      a * pairConvolution D α β s t q := by
  rw [MvPolynomial.C_mul']
  exact map_smul _ _ _

theorem pairConvolution_X_zero_pow (D : LatticeData) (α β : Charge D) (s t : ℤ)
    (r : ℕ) (q : PairPolynomial D) :
    pairConvolution D α β s t (MvPolynomial.X 0^r * q) =
      pairConvolution D α β (s+r) t q := by
  classical
  induction q using MvPolynomial.induction_on' with
  | add q q' h h' => simp only [mul_add, map_add, h, h']
  | monomial e a =>
    rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.monomial_mul,
      pairConvolution_monomial, pairConvolution_monomial]
    simp only [one_mul, Finsupp.add_apply, Finsupp.single_eq_same,
      Finsupp.single_eq_of_ne (by decide : (1 : Fin 2) ≠ 0), zero_add]
    congr 3
    push_cast
    omega

theorem pairConvolution_X_one_pow (D : LatticeData) (α β : Charge D) (s t : ℤ)
    (r : ℕ) (q : PairPolynomial D) :
    pairConvolution D α β s t (MvPolynomial.X 1^r * q) =
      pairConvolution D α β s (t+r) q := by
  classical
  induction q using MvPolynomial.induction_on' with
  | add q q' h h' => simp only [mul_add, map_add, h, h']
  | monomial e a =>
    rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.monomial_mul,
      pairConvolution_monomial, pairConvolution_monomial]
    simp only [one_mul, Finsupp.add_apply, Finsupp.single_eq_same,
      Finsupp.single_eq_of_ne (by decide : (0 : Fin 2) ≠ 1), zero_add]
    congr 3
    push_cast
    omega

theorem kernel_single_convolution (D : LatticeData) (α β : Charge D) (u v : ℤ)
    (δ : Charge D) (p : Oscillator D) :
    commonKernel D α β u v (Finsupp.single δ p) =
      epsilon D (α+β) δ • Finsupp.single (α+β+δ)
        (pairConvolution D α β (u-bilinear D α δ) (v-bilinear D β δ)
          (translatedPairPolynomial D α β p)) := by
  rw [(actual_creation_coefficient_transport D α β).2.2.2]
  unfold commonKernelSingle
  congr 2
  simp only [pairConvolution, LinearMap.comp_apply, Finsupp.lsum_apply,
    Finsupp.sum, LinearMap.mulRight_apply]
  apply Finset.sum_congr rfl
  intro e he
  change MvPolynomial.coeff e (translatedPairPolynomial D α β p) *
    creationCoeff D α (u-bilinear D α δ+e 0) *
    creationCoeff D β (v-bilinear D β δ+e 1) =
    MvPolynomial.coeff e (translatedPairPolynomial D α β p) *
      (creationCoeff D α (u-bilinear D α δ+e 0) *
        creationCoeff D β (v-bilinear D β δ+e 1))
  ring

def creator (D : LatticeData) (x : Index D) : Module.End ℂ (Carrier D) :=
  neutralMode D x.1 (-(x.2 : ℤ)-1)

@[simp] theorem creator_single (D : LatticeData) (x : Index D)
    (δ : Charge D) (p : Oscillator D) :
    creator D x (Finsupp.single δ p) = Finsupp.single δ (X x * p) := by
  simp [creator, neutralMode, neutralPolynomialMode,
    show -(x.2 : ℤ)-1 < 0 by omega,
    show (-(-(x.2 : ℤ)-1)-1).toNat = x.2 by omega]

/-- Actual charge-changing coefficients satisfy the oscillator creation recurrence. -/
theorem raw_creator (D : LatticeData) (α : Charge D) (k : ℤ)
    (δ : Charge D) (x : Index D) (p : Oscillator D) :
    rawCoeff D α k (Finsupp.single δ (X x*p)) =
      creator D x (rawCoeff D α k (Finsupp.single δ p)) -
      (bilinear D α (unitCharge D x.1) : ℂ) •
        rawCoeff D α (k+(x.2+1 : ℕ)) (Finsupp.single δ p) := by
  rw [raw_single_convolution, raw_single_convolution, raw_single_convolution]
  have ht : translatedPolynomial D α (X x*p) =
      (Polynomial.C (X x) -
        Polynomial.C ((bilinear D α (unitCharge D x.1) : ℂ) • (1 : Oscillator D)) *
          Polynomial.X^(x.2+1)) * translatedPolynomial D α p := by
    simp [translatedPolynomial, translationVariable]
  rw [ht, sub_mul, map_sub, convolution_C_mul, mul_assoc,
    convolution_C_mul, convolution_X_pow]
  rw [show k - bilinear D α δ + (x.2+1 : ℕ) =
      k+(x.2+1 : ℕ)-bilinear D α δ by omega]
  simp only [map_smul, creator_single, Finsupp.single_sub, smul_sub,
    smul_mul_assoc, one_mul, ← Finsupp.smul_single]
  module

/-- The actual common kernel has the two required independent oscillator shifts. -/
theorem kernel_creator (D : LatticeData) (α β : Charge D) (u v : ℤ)
    (δ : Charge D) (x : Index D) (p : Oscillator D) :
    commonKernel D α β u v (Finsupp.single δ (X x*p)) =
      creator D x (commonKernel D α β u v (Finsupp.single δ p)) -
      (bilinear D α (unitCharge D x.1) : ℂ) •
        commonKernel D α β (u+(x.2+1 : ℕ)) v (Finsupp.single δ p) -
      (bilinear D β (unitCharge D x.1) : ℂ) •
        commonKernel D α β u (v+(x.2+1 : ℕ)) (Finsupp.single δ p) := by
  rw [kernel_single_convolution, kernel_single_convolution,
    kernel_single_convolution, kernel_single_convolution]
  have ht : translatedPairPolynomial D α β (X x*p) =
      (MvPolynomial.C (X x) -
        MvPolynomial.C ((bilinear D α (unitCharge D x.1) : ℂ) • (1 : Oscillator D)) *
          MvPolynomial.X 0^(x.2+1) -
        MvPolynomial.C ((bilinear D β (unitCharge D x.1) : ℂ) • (1 : Oscillator D)) *
          MvPolynomial.X 1^(x.2+1)) * translatedPairPolynomial D α β p := by
    simp [translatedPairPolynomial]
  rw [ht, sub_mul, sub_mul, map_sub, map_sub, pairConvolution_C_mul,
    mul_assoc, pairConvolution_C_mul, pairConvolution_X_zero_pow,
    mul_assoc, pairConvolution_C_mul, pairConvolution_X_one_pow]
  rw [show u - bilinear D α δ + (x.2+1 : ℕ) =
      u+(x.2+1 : ℕ)-bilinear D α δ by omega,
    show v - bilinear D β δ + (x.2+1 : ℕ) =
      v+(x.2+1 : ℕ)-bilinear D β δ by omega]
  simp only [map_smul, creator_single, Finsupp.single_sub, smul_sub,
    smul_mul_assoc, one_mul, ← Finsupp.smul_single]
  module

/-- Finite input support supplies separate lower bounds for both kernel indices. -/
theorem kernel_lower_bounds (D : LatticeData) (α β : Charge D)
    (δ : Charge D) (p : Oscillator D) :
    ∃ a b : ℤ, ∀ u v : ℤ, u < a ∨ v < b →
      commonKernel D α β u v (Finsupp.single δ p) = 0 := by
  classical
  let q := translatedPairPolynomial D α β p
  refine ⟨bilinear D α δ - q.support.sup (fun e => e 0),
    bilinear D β δ - q.support.sup (fun e => e 1), ?_⟩
  intro u v huv
  rw [(actual_creation_coefficient_transport D α β).2.2.2]
  have hz : ∑ e ∈ q.support,
      q.coeff e * creationCoeff D α (u-bilinear D α δ+e 0) *
        creationCoeff D β (v-bilinear D β δ+e 1) = 0 := by
    apply Finset.sum_eq_zero
    intro e he
    rcases huv with hu | hv
    · have he' := Finset.le_sup (f := fun e : Fin 2 →₀ ℕ => e 0) he
      simp [creationCoeff, show u-bilinear D α δ+e 0 < 0 by omega]
    · have he' := Finset.le_sup (f := fun e : Fin 2 →₀ ℕ => e 1) he
      simp [creationCoeff, show v-bilinear D β δ+e 1 < 0 by omega]
  simp only [commonKernelSingle, ← show q = translatedPairPolynomial D α β p from rfl,
    hz, Finsupp.single_zero, smul_zero]

theorem ordered_kernel_finite (D : LatticeData) (α β : Charge D)
    (k l : ℤ) (δ : Charge D) (p : Oscillator D) :
    Function.HasFiniteSupport (fun j : ℕ =>
      commonKernel D α β (k-bilinear D α β+j) (l-j) (Finsupp.single δ p)) ∧
    Function.HasFiniteSupport (fun j : ℕ =>
      commonKernel D α β (k-j) (l-bilinear D α β+j) (Finsupp.single δ p)) := by
  obtain ⟨a,b,h⟩ := kernel_lower_bounds D α β δ p
  constructor
  · apply BddAbove.finite
    refine bddAbove_def.mpr ⟨(l-b).toNat, ?_⟩
    intro j hj
    by_contra hn
    exact hj (h _ _ (Or.inr (by omega)))
  · apply BddAbove.finite
    refine bddAbove_def.mpr ⟨(k-a).toNat, ?_⟩
    intro j hj
    by_contra hn
    exact hj (h _ _ (Or.inl (by omega)))

end
end D5.S3.VertexAlgebra.LatticeActualProductKernel
