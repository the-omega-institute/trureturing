/- GID: D5/S3/Arith/TernaryTraceSupport
   generality: I
   mirror-B: D5/B/S3/Arith/TernaryTraceSupport
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Ternary trace identities for the exact mod-three support of A396808. -/

import D5.S3.Arith.ArtinSchreierTracePowersOfTwo

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped PowerSeries
open Finset Polynomial

namespace D5.S3.Arith.TernaryTraceSupport
noncomputable section
open D5.S3.Arith.ArtinSchreierTracePowersOfTwo
private abbrev F3 := ZMod 3

private theorem coeff_pow_add_monomial
    {R : Type*} [CommRing R] (p : R[X]) (n m : ℕ) (c : R)
    (hn : 0 < n) (hm : 0 < m) (hp0 : p.coeff 0 = 1) :
    ((p + Polynomial.monomial n c) ^ m).coeff n =
      (p ^ m).coeff n + (m : R) * c := by
  classical
  rw [add_comm, (Commute.all (Polynomial.monomial n c) p).add_pow,
    Polynomial.finsetSum_coeff]
  let f : ℕ → R := fun k =>
    ((Polynomial.monomial n c) ^ k * p ^ (m - k) *
      Polynomial.C (m.choose k : R)).coeff n
  have hf0 : f 0 = (p ^ m).coeff n := by
    simp [f]
  have hf1 : f 1 = (m : R) * c := by
    have hconst : ∀ k : ℕ, (p ^ k).coeff 0 = 1 := by
      intro k
      induction k with
      | zero => simp
      | succ k ih => simp [pow_succ, Polynomial.mul_coeff_zero, ih, hp0]
    have hcoef : ((Polynomial.monomial n c) * p ^ (m - 1)).coeff n = c := by
      simpa [hconst] using
        (Polynomial.coeff_monomial_mul (p ^ (m - 1)) n 0 c)
    have hcoef' : (p ^ (m - 1) * Polynomial.monomial n c).coeff n = c := by
      rw [mul_comm]
      exact hcoef
    simp [f, hcoef', mul_comm]
  have hfk : ∀ k ∈ Finset.range (m + 1), k ≠ 0 → k ≠ 1 → f k = 0 := by
    intro k hk hk0 hk1
    have hk2 : 2 ≤ k := by omega
    have hlarge : n < k * n := by nlinarith
    have hnle : ¬n * k ≤ n := by nlinarith
    simp only [f, Polynomial.monomial_pow]
    rw [Polynomial.coeff_mul_C, ← Polynomial.C_mul_X_pow_eq_monomial,
      mul_assoc, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_mul']
    simp [hnle]
  change (∑ k ∈ Finset.range (m + 1), f k) = _
  let s := Finset.range (m + 1)
  have h0 : 0 ∈ s := by simp [s]
  have h1 : 1 ∈ s.erase 0 := by simp [s, hm]
  calc
    (∑ k ∈ s, f k) = f 0 + ∑ k ∈ s.erase 0, f k :=
      (Finset.add_sum_erase s f h0).symm
    _ = f 0 + f 1 := by
      rw [Finset.sum_eq_single 1]
      · intro k hk hk1'
        exact hfk k (Finset.mem_of_mem_erase hk) (Finset.ne_of_mem_erase hk) hk1'
      · exact fun hnot => False.elim (hnot h1)
    _ = (p ^ m).coeff n + (m : R) * c := by rw [hf0, hf1]

private theorem coeff_pow_eq_coeff_trunc_pow
    {R : Type*} [CommRing R] (f : R⟦X⟧) (n m : ℕ) :
    PowerSeries.coeff n (f ^ m) = ((PowerSeries.trunc (n + 1) f) ^ m).coeff n := by
  have h := congrArg (fun p : R[X] => p.coeff n)
    (PowerSeries.trunc_trunc_pow f (n + 1) m)
  calc
    PowerSeries.coeff n (f ^ m) =
        PowerSeries.coeff n ((PowerSeries.trunc (n + 1) f : R⟦X⟧) ^ m) := by
      simpa only [PowerSeries.coeff_trunc, Nat.lt_succ_iff, le_rfl, if_true,
        Polynomial.coeff_coe] using h.symm
    _ = PowerSeries.coeff n ((↑((PowerSeries.trunc (n + 1) f) ^ m)) : R⟦X⟧) := by
      rw [Polynomial.coe_pow]
    _ = ((PowerSeries.trunc (n + 1) f) ^ m).coeff n :=
      Polynomial.coeff_coe _ _

private theorem coeff_pow_eq_strict_trunc_add
    {R : Type*} [CommRing R] (f : R⟦X⟧) (n m : ℕ)
    (hn : 0 < n) (hm : 0 < m) (hf0 : PowerSeries.coeff 0 f = 1) :
    PowerSeries.coeff n (f ^ m) =
      ((PowerSeries.trunc n f) ^ m).coeff n + (m : R) * PowerSeries.coeff n f := by
  rw [coeff_pow_eq_coeff_trunc_pow, PowerSeries.trunc_succ]
  exact coeff_pow_add_monomial (PowerSeries.trunc n f) n m
    (PowerSeries.coeff n f) hn hm (by simpa [PowerSeries.coeff_trunc, hn] using hf0)


private theorem recursion_of_source {K : Type*} [CommRing K] (f : K⟦X⟧)
    (hf0 : PowerSeries.coeff 0 f = 1)
    (n : ℕ) (hn : 1 < n)
    (hs : (n + 1 : K) * PowerSeries.coeff n (f ^ (n + 1)) =
      (n : K) * PowerSeries.coeff n (f ^ (n + 2))) :
    PowerSeries.coeff n f =
      (n : K) * ((PowerSeries.trunc n f) ^ (n + 2)).coeff n -
      (n + 1 : K) * ((PowerSeries.trunc n f) ^ (n + 1)).coeff n := by
  have h1 := coeff_pow_eq_strict_trunc_add f n (n + 1) (by omega) (by omega) hf0
  have h2 := coeff_pow_eq_strict_trunc_add f n (n + 2) (by omega) (by omega) hf0
  rw [h1, h2] at hs
  push_cast at hs ⊢
  linear_combination hs

private theorem source_unique {K : Type*} [CommRing K] (f g : K⟦X⟧)
    (hf0 : PowerSeries.coeff 0 f = 1) (hg0 : PowerSeries.coeff 0 g = 1)
    (hf1 : PowerSeries.coeff 1 f = 1) (hg1 : PowerSeries.coeff 1 g = 1)
    (hsf : ∀ n : ℕ, 1 < n →
      (n + 1 : K) * PowerSeries.coeff n (f ^ (n + 1)) =
        (n : K) * PowerSeries.coeff n (f ^ (n + 2)))
    (hsg : ∀ n : ℕ, 1 < n →
      (n + 1 : K) * PowerSeries.coeff n (g ^ (n + 1)) =
        (n : K) * PowerSeries.coeff n (g ^ (n + 2))) : f = g := by
  ext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn0 : n = 0
      · subst n
        exact hf0.trans hg0.symm
      by_cases hn1 : n = 1
      · subst n
        exact hf1.trans hg1.symm
      have hn : 1 < n := by omega
      have ht : PowerSeries.trunc n f = PowerSeries.trunc n g := by
        ext j
        simp only [PowerSeries.coeff_trunc]
        split_ifs with hj
        · exact ih j hj
        · rfl
      rw [recursion_of_source f hf0 n hn (hsf n hn),
        recursion_of_source g hg0 n hn (hsg n hn), ht]

private def reducedSeries : F3⟦X⟧ :=
  PowerSeries.map (Int.castRingHom F3) (PowerSeries.mk a)

@[simp] private theorem coeff_reducedSeries (n : ℕ) :
    PowerSeries.coeff n reducedSeries = (a n : F3) := by
  simp [reducedSeries]

private theorem reduced_source_equation (n : ℕ) (hn : 1 < n) :
    (n + 1 : F3) * PowerSeries.coeff n (reducedSeries ^ (n + 1)) =
      (n : F3) * PowerSeries.coeff n (reducedSeries ^ (n + 2)) := by
  simp only [reducedSeries, ← map_pow, PowerSeries.coeff_map]
  simpa using congrArg (Int.castRingHom F3) (source_equation n hn)

private theorem reduced_zero : PowerSeries.coeff 0 reducedSeries = 1 := by
  rw [coeff_reducedSeries]
  have h : a 0 = 1 := rfl
  rw [h]
  rfl

private theorem reduced_one : PowerSeries.coeff 1 reducedSeries = 1 := by
  rw [coeff_reducedSeries]
  have h : a 1 = 1 := rfl
  rw [h]
  rfl

#print axioms source_unique
#print axioms reduced_source_equation
end
end D5.S3.Arith.TernaryTraceSupport
