/- GID: D5/S3/Arith/Lattices/PureCubicPrimeSaturation
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/PureCubicPrimeSaturation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A simple prime divisor of the radicand saturates the pure cubic order. -/

import D5.S3.Arith.Lattices.PureCubicThreeSaturation
import Mathlib.RingTheory.Polynomial.Eisenstein.IsIntegral
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.Lattices.PureCubicPrimeSaturation

open Polynomial Algebra

/-- At a prime occurring exactly once in the radicand, the displayed cubic order
contains every integral element whose multiple by that prime lies in the order. -/
theorem pure_cubic_prime_saturation
    {K : Type*} [Field K] [CharZero K] [Algebra ℚ K]
    (pb : PowerBasis ℚ K) (h3 : pb.dim = 3) (a : ℤ)
    (hroot : pb.gen ^ 3 = ((1 + 9 * a : ℤ) : K))
    (p : ℕ) (hp : p.Prime)
    (hpdvd : (p : ℤ) ∣ 1 + 9 * a)
    (hpsq : ¬(p : ℤ) ^ 2 ∣ 1 + 9 * a)
    (z : K) (hzint : IsIntegral ℤ z)
    (hpz : ∃ u v w : ℤ,
      (p : K) * z = (u : K) + (v : K) * pb.gen +
        (w : K) * ((1 + pb.gen + pb.gen ^ 2) / 3)) :
    ∃ u v w : ℤ,
      z = (u : K) + (v : K) * pb.gen +
        (w : K) * ((1 + pb.gen + pb.gen ^ 2) / 3) := by
  letI : Module.Finite ℚ K := pb.finite
  let B : ℤ := 1 + 9 * a
  let beta : K := (1 + pb.gen + pb.gen ^ 2) / 3
  have hpdvdB : (p : ℤ) ∣ B := hpdvd
  have hnotSq : ¬(p : ℤ) ^ 2 ∣ B := hpsq
  obtain ⟨_, _, _, A, hA, hAint, _⟩ :=
    D5.S3.Arith.Lattices.PureCubicSuborder.pure_cubic_suborder pb h3 a hroot
  have htheta : IsIntegral ℤ pb.gen := by
    apply hAint
    apply (hA pb.gen).mpr
    refine ⟨0, 1, 0, ?_⟩
    simp
  have hminQ : minpoly ℚ pb.gen =
      (Polynomial.X : Polynomial ℚ) ^ 3 - Polynomial.C (B : ℚ) := by
    have heval : Polynomial.aeval pb.gen
        ((Polynomial.X : Polynomial ℚ) ^ 3 - Polynomial.C (B : ℚ)) = 0 := by
      simpa [B] using sub_eq_zero.mpr hroot
    have hdegree :
        (((Polynomial.X : Polynomial ℚ) ^ 3 - Polynomial.C (B : ℚ))).degree ≤
          (minpoly ℚ pb.gen).degree := by
      rw [Polynomial.degree_X_pow_sub_C (by norm_num : 0 < 3),
        Polynomial.degree_eq_natDegree (minpoly.ne_zero pb.isIntegral_gen),
        pb.natDegree_minpoly, h3]
    exact (minpoly.unique_of_degree_le_degree_minpoly ℚ pb.gen
      (Polynomial.monic_X_pow_sub_C _ (by norm_num : 3 ≠ 0))
      heval hdegree).symm
  have hminZ : minpoly ℤ pb.gen =
      (Polynomial.X : Polynomial ℤ) ^ 3 - Polynomial.C B := by
    apply Polynomial.map_injective (algebraMap ℤ ℚ) (algebraMap ℤ ℚ).injective_int
    rw [← minpoly.isIntegrallyClosed_eq_field_fractions' ℚ htheta, hminQ]
    simp
  have hthree {y : K} (hyint : IsIntegral ℤ y)
      (h3y : (3 : K) * y ∈ A) : y ∈ A := by
    apply (hA y).mpr
    exact D5.S3.Arith.Lattices.PureCubicThreeSaturation.pure_cubic_three_saturation
      pb h3 a hroot y hyint ((hA _).mp h3y)
  have hadjoin : adjoin ℤ ({pb.gen} : Set K) ≤ subalgebraOfSubring A := by
    apply adjoin_le
    intro x hx
    simp only [Set.mem_singleton_iff] at hx
    subst x
    change pb.gen ∈ A
    apply (hA pb.gen).mpr
    refine ⟨0, 1, 0, ?_⟩
    simp
  have h3adjoin (y : K) (hy : y ∈ A) :
      (3 : K) * y ∈ adjoin ℤ ({pb.gen} : Set K) := by
    obtain ⟨u, v, w, rfl⟩ := (hA y).mp hy
    have ht : pb.gen ∈ adjoin ℤ ({pb.gen} : Set K) :=
      subset_adjoin (Set.mem_singleton _)
    have hb : (3 : K) * beta ∈ adjoin ℤ ({pb.gen} : Set K) := by
      have heq : (3 : K) * beta = 1 + pb.gen + pb.gen ^ 2 := by
        dsimp [beta]
        field_simp
      rw [heq]
      exact (Subalgebra.add_mem _ (Subalgebra.add_mem _
        (Subalgebra.one_mem _) ht) (Subalgebra.pow_mem _ ht 2))
    have hsum : ((3 * u : ℤ) : K) + ((3 * v : ℤ) : K) * pb.gen +
        (w : K) * ((3 : K) * beta) ∈ adjoin ℤ ({pb.gen} : Set K) := by
      exact Subalgebra.add_mem _
        (Subalgebra.add_mem _ (Subalgebra.algebraMap_mem _ (3 * u))
          (Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ (3 * v)) ht))
        (Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ w) hb)
    convert hsum using 1 <;> push_cast <;> ring
  have heisenstein :
      (minpoly ℤ pb.gen).IsEisensteinAt (Submodule.span ℤ {(p : ℤ)}) := by
    have hpI : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
    rw [hminZ]
    apply (Polynomial.monic_X_pow_sub_C B (by norm_num : 3 ≠ 0)).isEisensteinAt_of_mem_of_notMem
    · exact Ideal.IsPrime.ne_top ((Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).2 hpI)
    · intro i hi
      rw [Ideal.submodule_span_eq, Ideal.mem_span_singleton]
      have hi3 : i < 3 := by
        simpa only [Polynomial.natDegree_X_pow_sub_C] using hi
      interval_cases i <;>
        simp [Polynomial.coeff_sub, Polynomial.coeff_X_pow, hpdvdB]
      all_goals simp only [← Polynomial.C_eq_intCast B, Polynomial.coeff_C]
      all_goals simp
    · rw [Ideal.submodule_span_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
      simpa [Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_C] using
        (show ¬(p : ℤ) ^ 2 ∣ -B by simpa using hnotSq)
  have hpzA : (p : K) * z ∈ A := (hA _).mpr hpz
  have h3pz := h3adjoin ((p : K) * z) hpzA
  have hp3z : (p : ℤ) • ((3 : K) * z) ∈ adjoin ℤ ({pb.gen} : Set K) := by
    convert h3pz using 1 <;> simp [Algebra.smul_def] <;> ring
  have h3zint : IsIntegral ℤ ((3 : K) * z) :=
    (show IsIntegral ℤ (3 : K) from by
      simpa using (isIntegral_algebraMap : IsIntegral ℤ (((3 : ℤ) : K)))).mul hzint
  have h3z := mem_adjoin_of_smul_prime_smul_of_minpoly_isEisensteinAt
    (Nat.prime_iff_prime_int.mp hp) htheta h3zint hp3z heisenstein
  exact (hA z).mp (hthree hzint (hadjoin h3z))

#print axioms pure_cubic_prime_saturation

end D5.S3.Arith.Lattices.PureCubicPrimeSaturation
