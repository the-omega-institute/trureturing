/- GID: D5/S3/Combinatorics/GaussianQuotient/CoefficientListInvariance
   generality: G
   mirror-B: D5/B/S3/Combinatorics/GaussianQuotient/CoefficientListInvariance
   mirror-E: none(waiver:structural-proof)
   anchors: [lake/module/D5.S3.Combinatorics.GaussianQuotient.OkadaPreMergedNonPalindromic]
   utility: none
   digest: Multiplying a polynomial by q^s or substituting q -> q^k (k >= 1) preserves its ordered list of nonzero coefficients and hence almost palindromicity. -/

import D5.S3.Combinatorics.GaussianQuotient.OkadaPreMergedNonPalindromic

/-! Invariance of the ordered nonzero-coefficient list under shifts and substitutions. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.GaussianQuotient.CoefficientListInvariance

/-
proof_shape:
  supportCoeffList: definition
  support_X_pow_mul: bind-only (consumer: supportCoeffList_X_pow_mul)
  mulEmb: definition
  mulEmb_apply: bind-only (consumers: support_expand, supportCoeffList_expand)
  support_expand: content (consumer: supportCoeffList_expand)
  supportCoeffList_X_pow_mul: bind-only (consumer: result)
  supportCoeffList_expand: content (consumer: result)
  result: content
escape_witness: the substitution identity supp(f(q^k)) = k supp(f) (no univariate Mathlib
  counterpart), through which the strictly monotone relabeling n -> k n commutes with sorting
  (StrictMonoOn.map_finsetSort) and carries each coefficient to itself.
admission_basis: escape-witness
-/

open Polynomial
open D5.S3.Combinatorics.GaussianQuotient.OkadaPreMergedNonPalindromic (IsAlmostPalindromic)

/-- The coefficients of `f` at its support, in increasing order of exponent. -/
noncomputable def supportCoeffList {R : Type*} [Semiring R] (f : R[X]) : List R :=
  (f.support.sort (· ≤ ·)).map f.coeff

/-- `supp(q^s f) = s + supp(f)`, transported from `AddMonoidAlgebra.support_coeff_single_mul`. -/
private theorem support_X_pow_mul {R : Type*} [Semiring R] (f : R[X]) (s : ℕ) :
    (X ^ s * f).support = f.support.map (addLeftEmbedding s) := by
  rw [← support_toFinsupp, toFinsupp_mul, toFinsupp_X_pow,
    AddMonoidAlgebra.support_coeff_single_mul _ _ (by simp), support_toFinsupp]

/-- Multiplication by `k ≥ 1` as an embedding of `ℕ`. -/
private def mulEmb (k : ℕ) (hk : 1 ≤ k) : ℕ ↪ ℕ :=
  ⟨fun a => a * k, fun a b (h : a * k = b * k) => Nat.eq_of_mul_eq_mul_right (by omega) h⟩

private theorem mulEmb_apply (k : ℕ) (hk : 1 ≤ k) (a : ℕ) : mulEmb k hk a = a * k := rfl

/-- `supp(f(q^k)) = k · supp(f)` for `k ≥ 1`. -/
private theorem support_expand {R : Type*} [CommSemiring R] (f : R[X]) (k : ℕ) (hk : 1 ≤ k) :
    (expand R k f).support = f.support.map (mulEmb k hk) := by
  ext n
  simp only [mem_support_iff, coeff_expand (by omega : 0 < k), Finset.mem_map, mulEmb_apply]
  constructor
  · intro h
    split_ifs at h with hd
    · exact ⟨n / k, h, Nat.div_mul_cancel hd⟩
    · exact absurd rfl h
  · rintro ⟨a, ha, rfl⟩
    have hd : k ∣ a * k := Dvd.intro_left a rfl
    simp only [hd, ↓reduceIte, Nat.mul_div_cancel a (by omega : 0 < k)]
    exact ha

private theorem supportCoeffList_X_pow_mul {R : Type*} [Semiring R] (f : R[X]) (s : ℕ) :
    supportCoeffList (X ^ s * f) = supportCoeffList f := by
  unfold supportCoeffList
  rw [support_X_pow_mul]
  have hmono : StrictMonoOn (addLeftEmbedding s) (f.support : Set ℕ) :=
    fun a _ b _ hab => by simp only [addLeftEmbedding_apply]; omega
  rw [← hmono.map_finsetSort, List.map_map]
  congr 1
  funext a
  simp only [Function.comp_apply, addLeftEmbedding_apply]
  rw [add_comm, coeff_X_pow_mul]

private theorem supportCoeffList_expand {R : Type*} [CommSemiring R] (f : R[X]) (k : ℕ) (hk : 1 ≤ k) :
    supportCoeffList (expand R k f) = supportCoeffList f := by
  unfold supportCoeffList
  rw [support_expand f k hk]
  have hmono : StrictMonoOn (mulEmb k hk) (f.support : Set ℕ) :=
    fun a _ b _ hab => by
      rw [mulEmb_apply, mulEmb_apply]
      exact Nat.mul_lt_mul_of_pos_right hab (by omega)
  rw [← hmono.map_finsetSort, List.map_map]
  congr 1
  funext a
  simp [mulEmb_apply, coeff_expand_mul (by omega : 0 < k)]

universe u

/-- Multiplying by `q^s` (`s ≥ 0`, over any semiring) or substituting `q ↦ q^k` (`k ≥ 1`, over any
commutative semiring) preserves the ordered list of nonzero coefficients of every polynomial,
and hence, over `ℤ`, almost palindromicity. -/
theorem result :
    (∀ (R : Type u) [Semiring R] (f : R[X]) (s : ℕ), supportCoeffList (X ^ s * f) = supportCoeffList f) ∧
    (∀ (R : Type u) [CommSemiring R] (f : R[X]) (k : ℕ), 1 ≤ k →
      supportCoeffList (expand R k f) = supportCoeffList f) ∧
    (∀ (f : ℤ[X]) (s k : ℕ), 1 ≤ k →
      (IsAlmostPalindromic (X ^ s * f) ↔ IsAlmostPalindromic f) ∧
        (IsAlmostPalindromic (expand ℤ k f) ↔ IsAlmostPalindromic f)) :=
  ⟨fun _ _ f s => supportCoeffList_X_pow_mul f s, fun _ _ f k hk => supportCoeffList_expand f k hk,
    fun f s k hk => by
      have h1 := supportCoeffList_X_pow_mul f s
      have h2 := supportCoeffList_expand f k hk
      unfold supportCoeffList at h1 h2
      unfold IsAlmostPalindromic
      rw [h1, h2]
      exact ⟨Iff.rfl, Iff.rfl⟩⟩

#print axioms result

end D5.S3.Combinatorics.GaussianQuotient.CoefficientListInvariance
