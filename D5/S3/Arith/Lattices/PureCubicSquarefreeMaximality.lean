/- GID: D5/S3/Arith/Lattices/PureCubicSquarefreeMaximality
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/PureCubicSquarefreeMaximality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Squarefree pure cubic radicands give the full ring of integers. -/

import D5.S3.Arith.Lattices.PureCubicThreeSaturation
import Mathlib.RingTheory.Polynomial.Eisenstein.IsIntegral
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.Lattices.PureCubicSquarefreeMaximality

open Polynomial Algebra

/-- For a squarefree radicand congruent to one modulo nine, the cubic
suborder with its extra third is the full ring of integers. -/
theorem pure_cubic_squarefree_maximality
    {K : Type*} [Field K] [CharZero K] [Algebra ℚ K]
    (pb : PowerBasis ℚ K) (h3 : pb.dim = 3) (a : ℤ)
    (hroot : pb.gen ^ 3 = ((1 + 9 * a : ℤ) : K))
    (hsq : Squarefree (1 + 9 * a : ℤ))
    (z : K) (hzint : IsIntegral ℤ z) :
    ∃ u v w : ℤ,
      z = (u : K) + (v : K) * pb.gen +
        (w : K) * ((1 + pb.gen + pb.gen ^ 2) / 3) := by
  letI : Module.Finite ℚ K := pb.finite
  let B : ℤ := 1 + 9 * a
  let beta : K := (1 + pb.gen + pb.gen ^ 2) / 3
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
  have hdisc : Algebra.discr ℚ pb.basis = -27 * (B : ℚ) ^ 2 := by
    have hnorm : Algebra.norm ℚ pb.gen = (B : ℚ) := by
      rw [Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly, hminQ, h3]
      simp <;> norm_num
    have hderiv :
        ((Polynomial.X : Polynomial ℚ) ^ 3 - Polynomial.C (B : ℚ)).derivative =
          Polynomial.C 3 * Polynomial.X ^ 2 := by
      rw [derivative_sub, derivative_C, sub_zero, derivative_X_pow]
      norm_num
    rw [Algebra.discr_powerBasis_eq_norm, hminQ, hderiv]
    simp only [map_mul, map_pow, aeval_C, aeval_X]
    rw [Algebra.norm_algebraMap, hnorm, pb.finrank, h3]
    norm_num
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
  have heisenstein (p : ℕ) (hp : p.Prime) (hpdvdB : (p : ℤ) ∣ B) :
      (minpoly ℤ pb.gen).IsEisensteinAt (Submodule.span ℤ {(p : ℤ)}) := by
    have hpI : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
    have hnotSq : ¬(p : ℤ) ^ 2 ∣ B := by
      intro h
      have hu := hsq (p : ℤ) (by simpa [pow_two] using h)
      have hpge : (2 : ℤ) ≤ p := by exact_mod_cast hp.two_le
      simp only [Int.isUnit_iff] at hu
      omega
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
  have hprimeSat (p : ℕ) (hp : p.Prime) (hpdvdB : (p : ℤ) ∣ B)
      (y : K) (hyint : IsIntegral ℤ y) (hpy : (p : K) * y ∈ A) : y ∈ A := by
    have h3py := h3adjoin ((p : K) * y) hpy
    have hp3y : (p : ℤ) • ((3 : K) * y) ∈ adjoin ℤ ({pb.gen} : Set K) := by
      convert h3py using 1 <;> simp [Algebra.smul_def] <;> ring
    have h3yint : IsIntegral ℤ ((3 : K) * y) :=
      (show IsIntegral ℤ (3 : K) from by
        simpa using (isIntegral_algebraMap : IsIntegral ℤ (((3 : ℤ) : K)))).mul hyint
    have h3y := mem_adjoin_of_smul_prime_smul_of_minpoly_isEisensteinAt
      (Nat.prime_iff_prime_int.mp hp) htheta h3yint hp3y (heisenstein p hp hpdvdB)
    exact hthree hyint (hadjoin h3y)
  let N : ℕ := (27 * B ^ 2).toNat
  have hNInt : (N : ℤ) = 27 * B ^ 2 := by
    exact Int.toNat_of_nonneg (by positivity : 0 ≤ 27 * B ^ 2)
  have hBne : B ≠ 0 := hsq.ne_zero
  have hNne : N ≠ 0 := by
    intro h
    have hzero : (27 : ℤ) * B ^ 2 = 0 := by simpa [h] using hNInt.symm
    nlinarith [sq_pos_of_ne_zero hBne]
  have hprimeCase (p : ℕ) (hp : p.Prime) (hpdvdN : p ∣ N) :
      p = 3 ∨ (p : ℤ) ∣ B := by
    have hpi : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
    have hdiv : (p : ℤ) ∣ 27 * B ^ 2 := by
      have hi : (p : ℤ) ∣ (N : ℤ) := by exact_mod_cast hpdvdN
      simpa [hNInt] using hi
    rcases hpi.dvd_mul.mp hdiv with h27 | hB2
    · left
      have h27' : (p : ℤ) ∣ (3 : ℤ) ^ 3 := by simpa using h27
      have h3 : p ∣ 3 := by exact_mod_cast hpi.dvd_of_dvd_pow h27'
      exact (Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 3)).mp h3
    · right
      exact hpi.dvd_of_dvd_pow hB2
  have hremove : ∀ n : ℕ, n ∣ N → ∀ y : K,
      IsIntegral ℤ y → (n : K) * y ∈ A → y ∈ A := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hnN y hyint hny
      by_cases hn1 : n = 1
      · simpa [hn1] using hny
      have hn0 : n ≠ 0 := by
        intro h
        apply hNne
        simpa [h] using hnN
      obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd hn1
      obtain ⟨m, hm⟩ := hpn
      have hm0 : m ≠ 0 := by
        intro h
        apply hn0
        simpa [h] using hm
      have hmlt : m < n := by
        rw [hm]
        have hp2 : 2 ≤ p := hp.two_le
        exact lt_mul_of_one_lt_left (Nat.pos_of_ne_zero hm0) (by omega)
      have hmN : m ∣ N := by
        apply dvd_trans (b := n)
        · exact ⟨p, by simpa [mul_comm] using hm⟩
        · exact hnN
      have hpN : p ∣ N := dvd_trans ⟨m, hm⟩ hnN
      have hmyint : IsIntegral ℤ ((m : K) * y) := by
        exact (show IsIntegral ℤ (m : K) from by
          simpa using (isIntegral_algebraMap : IsIntegral ℤ (((m : ℤ) : K)))).mul hyint
      have hpmy : (p : K) * ((m : K) * y) ∈ A := by
        convert hny using 1
        rw [hm]
        push_cast
        ring
      have hmy : (m : K) * y ∈ A := by
        rcases hprimeCase p hp hpN with hp3 | hpB
        · subst p
          exact hthree hmyint (by simpa using hpmy)
        · exact hprimeSat p hp hpB _ hmyint hpmy
      exact ih m hmlt hmN y hyint hmy
  have hcleared := Algebra.discr_mul_isIntegral_mem_adjoin ℚ htheta hzint
  have hclearedA : ((-27 * B ^ 2 : ℤ) : K) * z ∈ A := by
    apply hadjoin
    have heq : ((-27 * B ^ 2 : ℤ) : K) * z =
        Algebra.discr ℚ pb.basis • z := by
      rw [hdisc]
      simp [Algebra.smul_def, map_mul, map_pow]
    rw [heq]
    exact hcleared
  have hNz : (N : K) * z ∈ A := by
    have h := A.neg_mem hclearedA
    have hNK : (N : K) = ((27 * B ^ 2 : ℤ) : K) := by
      exact_mod_cast hNInt
    convert h using 1
    rw [hNK]
    push_cast
    ring
  exact (hA z).mp (hremove N dvd_rfl z hzint hNz)

#print axioms pure_cubic_squarefree_maximality

end D5.S3.Arith.Lattices.PureCubicSquarefreeMaximality
