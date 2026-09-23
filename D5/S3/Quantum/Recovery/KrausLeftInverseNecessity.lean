/- GID: D5/S3/Quantum/Recovery/KrausLeftInverseNecessity
   generality: G
   mirror-B: D5/B/S3/Quantum/Recovery/KrausLeftInverseNecessity
   mirror-E: none(waiver:finite-algebraic-proof)
   anchors: []
   utility: none
   digest: Finite Kraus left inversion forces scalar error products. -/

import D5.S3.Quantum.Reduction.IsometricCompression

/-!
# Necessity of the exact error-product condition

The input is the actual composite sandwich sum on every matrix. Scalarity of
composite Kraus operators is derived, not assumed. A positive commutator defect
avoids importing an unproved rank-one Choi assertion. The existing Gram-zero
owner is reused. The final conclusion concerns every finite Kraus left inverse;
a separate Kraus-representation theorem is needed to transfer a quantified
abstract completely-positive map to this representation.

The correction criterion is classical: Knill--Laflamme (1997), Nayak--Sen
(2007). The commutator proof is an elementary multiplicative-domain argument.
-/

noncomputable section
open scoped Matrix BigOperators ComplexOrder MatrixOrder

namespace D5.S3.Quantum.Recovery.KrausLeftInverseNecessity

set_option autoImplicit false
set_option relaxedAutoImplicit false

open D5.S3.Quantum.Reduction.IsometricCompression

variable {d n s t : Type*} [Fintype d] [DecidableEq d]
  [Fintype n] [DecidableEq n] [Fintype s] [Fintype t]

/-- The identity sandwich map has no noncentral Kraus operator. -/
theorem identity_kraus_commute (F : s → Matrix d d ℂ)
    (hF : ∀ X : Matrix d d ℂ, (∑ a, F a * X * (F a)ᴴ) = X)
    (a : s) (X : Matrix d d ℂ) : F a * X = X * F a := by
  have hsum : (∑ b, (F b * X - X * F b) * (F b * X - X * F b)ᴴ) = 0 := by
    calc
      _ = (∑ b, F b * (X * Xᴴ) * (F b)ᴴ) -
          (∑ b, F b * X * (F b)ᴴ) * Xᴴ -
          X * (∑ b, F b * Xᴴ * (F b)ᴴ) +
          X * (∑ b, F b * 1 * (F b)ᴴ) * Xᴴ := by
        simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul,
          Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_add, Matrix.add_mul,
          Matrix.mul_sum, Matrix.sum_mul, Finset.sum_sub_distrib,
          Finset.sum_add_distrib, Matrix.mul_one, Matrix.mul_assoc]
        abel
      _ = 0 := by simp_rw [hF]; simp
  have hz : ∀ b, (F b * X - X * F b)ᴴ = 0 := by
    apply (sum_gram_eq_zero_iff (fun b => (F b * X - X * F b)ᴴ)).mp
    simpa only [Matrix.conjTranspose_conjTranspose] using hsum
  exact sub_eq_zero.mp (Matrix.conjTranspose_eq_zero.mp (hz a))

/-- Scalar coefficients are explicitly the chosen diagonal entries. -/
theorem identity_kraus_scalar (F : s → Matrix d d ℂ)
    (hF : ∀ X : Matrix d d ℂ, (∑ a, F a * X * (F a)ᴴ) = X)
    (j₀ : d) (a : s) : F a = F a j₀ j₀ • (1 : Matrix d d ℂ) := by
  have hdiag (i j : d) : F a i i = F a j j := by
    have h := congrArg (fun M : Matrix d d ℂ => M i j)
      (identity_kraus_commute F hF a (Matrix.single i j 1))
    simpa [Matrix.mul_apply, Matrix.single] using h
  have hoff (i j : d) (hij : i ≠ j) : F a i j = 0 := by
    have h := congrArg (fun M : Matrix d d ℂ => M i j)
      (identity_kraus_commute F hF a (Matrix.single j j 1))
    simpa [Matrix.mul_apply, Matrix.single, hij] using h
  ext i j
  by_cases hij : i = j
  · subst j
    simpa using hdiag i j₀
  · simp [Matrix.one_apply, hij, hoff i j hij]

/-- A represented left inverse computes a positive Gram scalar for every error product. -/
theorem left_inverse_error_products (E : s → Matrix n d ℂ)
    (A : t → Matrix d n ℂ)
    (hA : (∑ b, (A b)ᴴ * A b) = 1)
    (hleft : ∀ X : Matrix d d ℂ,
      (∑ b, A b * (∑ a, E a * X * (E a)ᴴ) * (A b)ᴴ) = X)
    (j₀ : d) (a c : s) :
    (E a)ᴴ * E c =
      (∑ b, star ((A b * E a) j₀ j₀) * ((A b * E c) j₀ j₀)) •
        (1 : Matrix d d ℂ) := by
  let F : t × s → Matrix d d ℂ := fun b => A b.1 * E b.2
  have hF : ∀ X : Matrix d d ℂ, (∑ b, F b * X * (F b)ᴴ) = X := by
    intro X
    simpa only [F, Fintype.sum_prod_type, Matrix.conjTranspose_mul,
      Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_assoc] using hleft X
  have hscalar (b : t) (k : s) :
      A b * E k = (A b * E k) j₀ j₀ • (1 : Matrix d d ℂ) :=
    identity_kraus_scalar F hF j₀ (b, k)
  calc
    (E a)ᴴ * E c = (E a)ᴴ * (∑ b, (A b)ᴴ * A b) * E c := by
      rw [hA, Matrix.mul_one]
    _ = ∑ b, (A b * E a)ᴴ * (A b * E c) := by
      simp only [Matrix.conjTranspose_mul, Matrix.mul_sum, Matrix.sum_mul,
        Matrix.mul_assoc]
    _ = (∑ b, star ((A b * E a) j₀ j₀) * ((A b * E c) j₀ j₀)) •
        (1 : Matrix d d ℂ) := by
      rw [Finset.sum_smul]
      apply Finset.sum_congr rfl
      intro b hb
      calc
        _ = (((A b * E a) j₀ j₀) • (1 : Matrix d d ℂ))ᴴ *
            (((A b * E c) j₀ j₀) • (1 : Matrix d d ℂ)) :=
          congrArg₂ (fun M N : Matrix d d ℂ => Mᴴ * N)
            (hscalar b a) (hscalar b c)
        _ = _ := by
          simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_one,
            Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul]

/-- The scalar is forced to be the normalized trace, so the error defect is determined by E alone. -/
theorem left_inverse_normalized_trace_condition (E : s → Matrix n d ℂ)
    (A : t → Matrix d n ℂ)
    (hA : (∑ b, (A b)ᴴ * A b) = 1)
    (hleft : ∀ X : Matrix d d ℂ,
      (∑ b, A b * (∑ a, E a * X * (E a)ᴴ) * (A b)ᴴ) = X)
    (j₀ : d) (a c : s) :
    (E a)ᴴ * E c =
      (Matrix.trace ((E a)ᴴ * E c) / (Fintype.card d : ℂ)) • (1 : Matrix d d ℂ) := by
  letI : Nonempty d := ⟨j₀⟩
  have hn : (Fintype.card d : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  let z := ∑ b, star ((A b * E a) j₀ j₀) * ((A b * E c) j₀ j₀)
  have hz : (E a)ᴴ * E c = z • (1 : Matrix d d ℂ) :=
    left_inverse_error_products E A hA hleft j₀ a c
  have hc : Matrix.trace ((E a)ᴴ * E c) / (Fintype.card d : ℂ) = z := by
    rw [hz, Matrix.trace_smul]
    simp [hn, smul_eq_mul]
  rw [hc]
  exact hz

/-- A single nonzero normalized-trace defect excludes every finite Kraus left inverse. -/
theorem nonzero_defect_excludes_left_inverse (E : s → Matrix n d ℂ)
    (j₀ : d) (a c : s)
    (hbad : (E a)ᴴ * E c ≠
      (Matrix.trace ((E a)ᴴ * E c) / (Fintype.card d : ℂ)) • (1 : Matrix d d ℂ)) :
    ¬ ∃ A : t → Matrix d n ℂ,
      (∑ b, (A b)ᴴ * A b) = 1 ∧
      ∀ X : Matrix d d ℂ,
        (∑ b, A b * (∑ k, E k * X * (E k)ᴴ) * (A b)ᴴ) = X := by
  rintro ⟨A, hA, hleft⟩
  exact hbad (left_inverse_normalized_trace_condition E A hA hleft j₀ a c)

#print axioms identity_kraus_commute
#print axioms identity_kraus_scalar
#print axioms left_inverse_error_products
#print axioms left_inverse_normalized_trace_condition
#print axioms nonzero_defect_excludes_left_inverse

end D5.S3.Quantum.Recovery.KrausLeftInverseNecessity
