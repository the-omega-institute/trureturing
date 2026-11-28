/- GID: D5/S3/LinearAlgebra/Matrix/RationalGraph/Rational
   generality: G
   mirror-B: none(waiver:existing-library-proof-without-a-dedicated-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The integral graph domain of a rational matrix -/

import OmegaBuild.Commands
import D5.S3.LinearAlgebra.Matrix.RationalGraph.Padic

/-! Omega original.

# The integral graph domain of a rational matrix

The graph domain consists of the integer vectors whose rational matrix product
is integral. Its index is the product of the indices of the analogous graph
domains in the p-adic integer vectors at the primes dividing a common denominator.
-/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Matrix
open scoped BigOperators Padic

namespace Omega.RationalMatrixGraph.Rational

noncomputable section

/-- The product of the entry denominators, a common denominator for the matrix. -/
def denominator {n : Type*} [Fintype n] (E : Matrix n n ℚ) : ℕ :=
  ∏ ij : n × n, (E ij.1 ij.2).den

theorem denominator_ne_zero {n : Type*} [Fintype n] (E : Matrix n n ℚ) :
    denominator E ≠ 0 := by
  unfold denominator
  exact Finset.prod_ne_zero_iff.mpr (fun ij _ => (E ij.1 ij.2).den_nz)

/-- The integer matrix obtained by multiplying by the common denominator. -/
def cleared {n : Type*} [Fintype n] (E : Matrix n n ℚ) : Matrix n n ℤ :=
  fun i j => ((denominator E / (E i j).den : ℕ) : ℤ) * (E i j).num

theorem cleared_coe {n : Type*} [Fintype n] (E : Matrix n n ℚ) (i j : n) :
    (cleared E i j : ℚ) = (denominator E : ℚ) * E i j := by
  have hd : (E i j).den ∣ denominator E := by
    unfold denominator
    exact Finset.dvd_prod_of_mem _ (Finset.mem_univ (i, j))
  have hh : ((denominator E / (E i j).den : ℕ) : ℚ) * ((E i j).den : ℚ) = denominator E := by
    exact_mod_cast Nat.div_mul_cancel hd
  change ((((denominator E / (E i j).den : ℕ) : ℤ) * (E i j).num : ℤ) : ℚ) = _
  simp only [Int.cast_mul, Int.cast_natCast]
  rw [← hh, ← Rat.mul_den_eq_num (E i j)]
  ac_rfl

/-- The integral graph domain, represented by congruences modulo the common denominator. -/
def graphDomain {n : Type*} [Fintype n] (E : Matrix n n ℚ) : AddSubgroup (n → ℤ) :=
  CRT.graphKernel (denominator E) (cleared E)

theorem graphDomain_mem {n : Type*} [Fintype n] (E : Matrix n n ℚ) (v : n → ℤ) :
    v ∈ graphDomain E ↔ ∀ i, ∃ a : ℤ, (a : ℚ) = (E *ᵥ fun j => (v j : ℚ)) i := by
  rw [graphDomain, CRT.graphKernel_mem]
  apply forall_congr'
  intro i
  have hm : ((cleared E *ᵥ v) i : ℚ) =
      (denominator E : ℚ) * (E *ᵥ fun j => (v j : ℚ)) i := by
    simp only [Matrix.mulVec, dotProduct, Int.cast_sum, Int.cast_mul, cleared_coe, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [mul_assoc]
  have hD : (denominator E : ℚ) ≠ 0 := by
    exact_mod_cast denominator_ne_zero E
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a, mul_left_cancel₀ hD ?_⟩
    rw [ha, Int.cast_mul, Int.cast_natCast] at hm
    exact hm
  · rintro ⟨a, ha⟩
    refine ⟨a, ?_⟩
    rw [← ha, ← Int.cast_natCast, ← Int.cast_mul] at hm
    exact_mod_cast hm

/-- The graph domain over the p-adic integers at a prime dividing the common denominator. -/
def localizedDomain {n : Type*} [Fintype n] (E : Matrix n n ℚ)
    (q : (denominator E).primeFactors) :
    letI : Fact q.val.Prime := ⟨Nat.prime_of_mem_primeFactors q.property⟩
    AddSubgroup (n → ℤ_[q.val]) :=
  @Padic.localKernel q.val ⟨Nat.prime_of_mem_primeFactors q.property⟩
    n _ ((denominator E).factorization q.val) (cleared E)

/-- The integral graph index is the product of the p-adic graph indices. -/
theorem global_index {n : Type*} [Fintype n] (E : Matrix n n ℚ) :
    (graphDomain E).index = ∏ q : (denominator E).primeFactors, (localizedDomain E q).index :=
  Padic.global_index (denominator E) (denominator_ne_zero E) (cleared E)

/-- Membership means that the unscaled matrix product has p-adically integral coordinates. -/
theorem localized_mem {n : Type*} [Fintype n] (E : Matrix n n ℚ)
    (q : (denominator E).primeFactors) :
    letI : Fact q.val.Prime := ⟨Nat.prime_of_mem_primeFactors q.property⟩
    ∀ v : n → ℤ_[q.val],
      v ∈ localizedDomain E q ↔ ∀ i, ∃ a : ℤ_[q.val], (a : ℚ_[q.val]) =
        ((E.map (algebraMap ℚ ℚ_[q.val])) *ᵥ fun j => (v j : ℚ_[q.val])) i := by
  let : Fact q.val.Prime := ⟨Nat.prime_of_mem_primeFactors q.property⟩
  intro v
  let D := denominator E
  let p := q.val
  exact Padic.localKernel_unscaled p D (D / p ^ (D.factorization p))
    (D.factorization p) (Nat.not_dvd_ordCompl (Fact.out : Nat.Prime p) (denominator_ne_zero E))
    (Nat.ordProj_mul_ordCompl_eq_self D p).symm (cleared E) E (cleared_coe E) v

end

end Omega.RationalMatrixGraph.Rational
