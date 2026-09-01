/- GID: D5/S3/Factorization/Embeddings/RationalPadicProductFormula
   generality: G
   mirror-B: D5/B/S3/Factorization/Embeddings/RationalPadicProductFormula
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The archimedean norm times all rational p-adic norms equals one. -/

/- Library-search audit trail (2026-08-31):
   * The target atom remains in `residual-open` with empty `coverage_gids`; no formalization receipt
     contains its hash. Repository searches for rational product-formula, `padicNorm`, and
     `padicValRat` statements found no theorem expressing the p-indexed norm product below.
   * The same-section atoms have no `primary_gid`. The adjacent
     `RationalValuationRecovery.lean` supplies a finite `padicValRat` profile, but no product
     identity. `HilbertReciprocityParity.lean` treats a product formula only as an external
     hypothesis and is not an anchor for this statement.
   * The generality-side neighbor `prime_exponent_product_formula` reconstructs a natural number
     from finitely supported exponents; it is not a formula for archimedean and p-adic norms.
   * Pinned Mathlib has the more general `NumberField.prod_abs_eq_one`, indexed by number-field
     infinite and finite places. No equivalence from `NumberField.FinitePlace ℚ` to `Nat.Primes`
     or theorem identifying that finprod with `padicNorm` was found, so its exact rational
     specialization is exposed separately rather than claimed as the p-indexed result.
   * Pinned Mathlib searches found `padicNorm` in nine files and `padicValRat` in five files. The
     proof uses `padicNorm.eq_zpow_of_nonzero`, `padicNorm.div`, `padicNorm.neg`,
     `Nat.factorization_def`, `Nat.prod_factorization_pow_eq_self`, and the standard `finprod`
     support and division lemmas directly. No new definition or abbreviation is introduced. -/

import D5.S3.Factorization.Embeddings.RationalValuationRecovery
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.NumberTheory.NumberField.ProductFormula
import Mathlib.NumberTheory.Padics.PadicNorm

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Factorization.Embeddings.RationalPadicProductFormula

open D5.S3.Factorization.Embeddings.RationalValuationRecovery

local instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

/-- Only finitely many prime-indexed p-adic norms of a nonzero rational differ from one. -/
theorem rational_padic_norm_hasFiniteMulSupport (x : ℚ) (hx : x ≠ 0) :
    Function.HasFiniteMulSupport (fun p : Nat.Primes => padicNorm p.1 x) := by
  rw [Function.HasFiniteMulSupport]
  apply (rationalFiniteValuationProfile x).support.finite_toSet.subset
  intro p hp
  change padicNorm p.1 x ≠ 1 at hp
  simp only [Finset.mem_coe, Finsupp.mem_support_iff, rationalFiniteValuationProfile_apply]
  intro hvaluation
  exact hp (by rw [padicNorm.eq_zpow_of_nonzero hx, hvaluation]; simp)
#print axioms rational_padic_norm_hasFiniteMulSupport

/-- The pinned number-field product formula specialized exactly to the rational number field. -/
theorem rational_number_field_product_formula {x : ℚ} (hx : x ≠ 0) :
    (∏ w : NumberField.InfinitePlace ℚ, w x ^ w.mult) *
      ∏ᶠ w : NumberField.FinitePlace ℚ, w x = 1 :=
  NumberField.prod_abs_eq_one hx
#print axioms rational_number_field_product_formula

private theorem nat_padic_norm_finprod (n : ℕ) (hn : n ≠ 0) :
    ∏ᶠ p : Nat.Primes, padicNorm p.1 n = (n : ℚ)⁻¹ := by
  change (∏ᶠ p : {p : ℕ // p.Prime}, padicNorm p.1 n) = (n : ℚ)⁻¹
  calc
    (∏ᶠ p : {p : ℕ // p.Prime}, padicNorm p.1 n) =
        ∏ᶠ (p : ℕ) (_ : p.Prime), padicNorm p n := by
      exact finprod_subtype_eq_finprod_cond
        (f := fun p : ℕ => padicNorm p n) Nat.Prime
    _ = ∏ p ∈ n.primeFactors, padicNorm p n := by
      apply finprod_cond_eq_prod_of_cond_iff
      intro p hpNorm
      constructor
      · intro hpPrime
        by_contra hpFactors
        apply hpNorm
        rw [padicNorm.eq_zpow_of_nonzero (by exact_mod_cast hn)]
        have hfactorization : n.factorization p = 0 := by
          rw [← Finsupp.notMem_support_iff, Nat.support_factorization]
          exact hpFactors
        simp only [padicValRat.of_nat, ← Nat.factorization_def n hpPrime, hfactorization]
        simp
      · exact Nat.prime_of_mem_primeFactors
    _ = ∏ p ∈ n.primeFactors, ((p : ℚ) ^ n.factorization p)⁻¹ := by
      apply Finset.prod_congr rfl
      intro p hp
      have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hp
      rw [padicNorm.eq_zpow_of_nonzero (by exact_mod_cast hn)]
      simp only [padicValRat.of_nat, ← Nat.factorization_def n hpPrime]
      simp
    _ = (∏ p ∈ n.primeFactors, (p : ℚ) ^ n.factorization p)⁻¹ := by
      rw [Finset.prod_inv_distrib]
    _ = (n : ℚ)⁻¹ := by
      congr 1
      norm_cast
      rw [← Nat.prod_factorization_eq_prod_primeFactors]
      exact Nat.prod_factorization_pow_eq_self hn

private theorem int_padic_norm_finprod (z : ℤ) (hz : z ≠ 0) :
    ∏ᶠ p : Nat.Primes, padicNorm p.1 z = (z.natAbs : ℚ)⁻¹ := by
  cases z with
  | ofNat n =>
      simpa using nat_padic_norm_finprod n (by simpa using hz)
  | negSucc n =>
      change ∏ᶠ p : Nat.Primes, padicNorm p.1 (-((n + 1 : ℕ) : ℚ)) =
        ((n + 1 : ℕ) : ℚ)⁻¹
      simp_rw [padicNorm.neg]
      exact nat_padic_norm_finprod (n + 1) (Nat.succ_ne_zero n)

/-- For a nonzero rational, its usual absolute value times all prime-indexed p-adic norms is one.

The `finprod` is an algebraic finite product: the preceding support theorem proves that all but
finitely many factors equal one.
-/
theorem rational_padic_product_formula (x : ℚ) (hx : x ≠ 0) :
    |x| * ∏ᶠ p : Nat.Primes, padicNorm p.1 x = 1 := by
  have hnumInt : x.num ≠ 0 := Rat.num_ne_zero.mpr hx
  have hnumRat : (x.num : ℚ) ≠ 0 := by exact_mod_cast hnumInt
  have hdenRat : (x.den : ℚ) ≠ 0 := by exact_mod_cast x.den_ne_zero
  have hxDiv : x = (x.num : ℚ) / (x.den : ℚ) := (Rat.num_div_den x).symm
  have hpadic :
      (fun p : Nat.Primes => padicNorm p.1 x) =
        fun p : Nat.Primes => padicNorm p.1 (x.num : ℚ) /
          padicNorm p.1 (x.den : ℚ) := by
    funext p
    calc
      padicNorm p.1 x = padicNorm p.1 ((x.num : ℚ) / (x.den : ℚ)) :=
        congrArg (padicNorm p.1) hxDiv
      _ = padicNorm p.1 (x.num : ℚ) / padicNorm p.1 (x.den : ℚ) :=
        padicNorm.div _ _
  rw [Rat.abs_def, Rat.divInt_eq_div, hpadic]
  rw [finprod_div_distrib
    (rational_padic_norm_hasFiniteMulSupport (x.num : ℚ) hnumRat)
    (rational_padic_norm_hasFiniteMulSupport (x.den : ℚ) hdenRat)]
  rw [int_padic_norm_finprod x.num hnumInt,
    nat_padic_norm_finprod x.den x.den_ne_zero]
  have hnumAbs : (x.num.natAbs : ℚ) ≠ 0 := by
    exact_mod_cast Int.natAbs_ne_zero.mpr hnumInt
  field_simp
  norm_num [mul_comm]
#print axioms rational_padic_product_formula

end D5.S3.Factorization.Embeddings.RationalPadicProductFormula
