/- GID: D5/S1/Dynamics/Symbolic/KhetanBinomialIrreducibility
   generality: G
   mirror-B: none(waiver:no mirrored proof)
   mirror-E: none(waiver:no external mirror)
   anchors: []
   utility: none
   digest: Coprime rational-function degree forces binomial irreducibility. -/

import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.FieldTheory.RatFunc.Degree
import Mathlib.RingTheory.Norm.Basic
import Mathlib.Tactic

/-! The irreducible-factor and root-norm calculation is adapted from
`X_pow_sub_C_irreducible_of_prime` in Mathlib's `FieldTheory/KummerPolynomial.lean`
(Andrew Yang and Patrick Lutz, Apache 2.0). Integer degree replaces its
prime-degree argument, so even and composite exponents are included. -/

set_option autoImplicit false

namespace D5.S1.Dynamics.Symbolic.KhetanBinomialIrreducibility

open Polynomial AdjoinRoot

universe u
variable {k : Type u} [Field k]

private theorem int_degree_pow (a : RatFunc k) (ha : a ≠ 0) (n : ℕ) :
    (a ^ n).intDegree = (n : ℤ) * a.intDegree := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, RatFunc.intDegree_mul (pow_ne_zero n ha) ha, ih]
      push_cast
      ring

/-- A rational-function binomial is irreducible when its exponent and the signed
integer degree of its nonzero constant term are coprime. -/
theorem X_pow_sub_C_irreducible_of_intDegree_coprime
    (a : RatFunc k) (ha : a ≠ 0) (m : ℕ) (hm : 0 < m)
    (hcoprime : Int.gcd (m : ℤ) a.intDegree = 1) :
    Irreducible ((X : Polynomial (RatFunc k)) ^ m - C a) := by
  have hf : (X : Polynomial (RatFunc k)) ^ m - C a ≠ 0 :=
    X_pow_sub_C_ne_zero hm a
  have hunit : ¬ IsUnit ((X : Polynomial (RatFunc k)) ^ m - C a) := by
    rw [Polynomial.isUnit_iff_degree_eq_zero, degree_X_pow_sub_C hm, Nat.cast_eq_zero]
    exact Nat.ne_of_gt hm
  obtain ⟨g, hg, hgf⟩ := WfDvdMonoid.exists_irreducible_factor hunit hf
  have : Fact (Irreducible g) := ⟨hg⟩
  have hroot : (AdjoinRoot.root g) ^ m = algebraMap (RatFunc k) (AdjoinRoot g) a := by
    have h := eval₂_eq_zero_of_dvd_of_eval₂_eq_zero _ _ hgf (AdjoinRoot.eval₂_root g)
    rw [eval₂_sub, eval₂_pow, eval₂_C, eval₂_X, sub_eq_zero] at h
    simpa only [AdjoinRoot.algebraMap_eq] using h
  have hroot_ne : AdjoinRoot.root g ≠ 0 := by
    intro hz
    rw [hz, zero_pow (Nat.ne_of_gt hm)] at hroot
    apply ha
    apply (algebraMap (RatFunc k) (AdjoinRoot g)).injective
    simpa only [map_zero] using hroot.symm
  have hnorm : (Algebra.norm (RatFunc k) (AdjoinRoot.root g)) ^ m = a ^ g.natDegree := by
    rw [← map_pow, hroot, Algebra.norm_algebraMap,
      (powerBasis hg.ne_zero).finrank, powerBasis_dim hg.ne_zero]
  have hnorm_ne : Algebra.norm (RatFunc k) (AdjoinRoot.root g) ≠ 0 := by
    exact (Algebra.norm_ne_zero_iff_of_basis (powerBasis hg.ne_zero).basis).mpr hroot_ne
  have hdegree : (m : ℤ) * (Algebra.norm (RatFunc k) (AdjoinRoot.root g)).intDegree =
      a.intDegree * (g.natDegree : ℤ) := by
    have h := congrArg RatFunc.intDegree hnorm
    rw [int_degree_pow _ hnorm_ne, int_degree_pow _ ha] at h
    simpa only [mul_comm a.intDegree] using h
  have hbezout : (m : ℤ) * Int.gcdA (m : ℤ) a.intDegree +
      a.intDegree * Int.gcdB (m : ℤ) a.intDegree = 1 := by
    simpa only [hcoprime, Nat.cast_one] using
      (Int.gcd_eq_gcd_ab (m : ℤ) a.intDegree).symm
  have hdvd_int : (m : ℤ) ∣ (g.natDegree : ℤ) := by
    refine ⟨Int.gcdA (m : ℤ) a.intDegree * (g.natDegree : ℤ) +
      Int.gcdB (m : ℤ) a.intDegree *
        (Algebra.norm (RatFunc k) (AdjoinRoot.root g)).intDegree, ?_⟩
    calc
      (g.natDegree : ℤ) =
          ((m : ℤ) * Int.gcdA (m : ℤ) a.intDegree +
            a.intDegree * Int.gcdB (m : ℤ) a.intDegree) * (g.natDegree : ℤ) := by
              rw [hbezout, one_mul]
      _ = (m : ℤ) * (Int.gcdA (m : ℤ) a.intDegree * (g.natDegree : ℤ) +
          Int.gcdB (m : ℤ) a.intDegree *
            (Algebra.norm (RatFunc k) (AdjoinRoot.root g)).intDegree) := by
              linear_combination -Int.gcdB (m : ℤ) a.intDegree * hdegree
  have hdvd : m ∣ g.natDegree := Int.natCast_dvd_natCast.mp hdvd_int
  have hdpos : 0 < g.natDegree :=
    natDegree_pos_iff_degree_pos.mpr (Polynomial.degree_pos_of_irreducible hg)
  have hdle : g.natDegree ≤ m := by
    simpa only [natDegree_X_pow_sub_C] using natDegree_le_of_dvd hgf hf
  have hdeq : g.natDegree = m := hdle.antisymm (Nat.le_of_dvd hdpos hdvd)
  exact (associated_of_dvd_of_natDegree_le hgf hf
    (hdeq.trans natDegree_X_pow_sub_C.symm).ge).irreducible hg

end D5.S1.Dynamics.Symbolic.KhetanBinomialIrreducibility
