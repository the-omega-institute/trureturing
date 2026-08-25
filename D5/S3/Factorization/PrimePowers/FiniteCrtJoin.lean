/- GID: D5/S3/Factorization/PrimePowers/FiniteCrtJoin
   generality: G
   mirror-B: D5/B/S3/Factorization/PrimePowers/FiniteCrtJoin
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite prime-power CRT covers empty sets, zero exponents, and composite failure. -/

/- Library-search audit trail (2026-08-25):
   * Exact pinned-Mathlib hit `ZMod.prodEquivPi` gives the finite dependent CRT
     equivalence and is applied directly in `finite_crt_join`.
   * `Nat.coprime_pow_primes` gives coprimality of powers of distinct primes.
   * `ZMod.equivPi` instead fixes its index type to the prime factors of a nonzero
     modulus, so it omits the zero-exponent labels retained by this statement.
   * Current-tree `RetainedResidueRecoveryCriterion` uses `ZMod.prodEquivPi`
     inside a bounded-state injectivity criterion; the two-factor CRT and matrix
     tensor modules also address different statements. No current module states
     this supplied finite prime set decomposition with zero-exponent factors. -/

import Mathlib.Data.ZMod.QuotientRing

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Factorization.PrimePowers.FiniteCrtJoin

open scoped Function

/-- The modulus assembled from a finite set of prime labels and their exponents. -/
def primePowerProduct (S : Finset Nat) (kappa : Nat -> Nat) : Nat :=
  S.prod fun p => p ^ kappa p

/-- A finite set of prime-power moduli has the canonical dependent CRT decomposition.
Zero exponents remain as labeled `ZMod 1` factors, rather than disappearing from the index. -/
theorem finite_crt_join (S : Finset Nat) (kappa : Nat -> Nat)
    (hS : forall p, p ∈ S -> Nat.Prime p) :
    Nonempty
      (ZMod (primePowerProduct S kappa) ≃+*
        forall p : S, ZMod ((p : Nat) ^ kappa p)) := by
  have hcoprime :
      Pairwise (Nat.Coprime on fun p : S => (p : Nat) ^ kappa p) := by
    intro p q hpq
    exact Nat.coprime_pow_primes (kappa p) (kappa q)
      (hS p p.property) (hS q q.property) (Subtype.coe_ne_coe.mpr hpq)
  have hproduct :
      primePowerProduct S kappa = ∏ p : S, (p : Nat) ^ kappa p := by
    exact Finset.prod_subtype S (fun _ => Iff.rfl) (fun p => p ^ kappa p)
  rw [hproduct]
  exact ⟨ZMod.prodEquivPi (fun p : S => (p : Nat) ^ kappa p) hcoprime⟩

#print axioms finite_crt_join

/-- Empty prime support gives modulus one and an empty dependent product. -/
theorem finite_crt_join_empty (kappa : Nat -> Nat) :
    Nonempty
      (ZMod 1 ≃+*
        forall p : (∅ : Finset Nat), ZMod ((p : Nat) ^ kappa p)) := by
  have hproduct : primePowerProduct (∅ : Finset Nat) kappa = 1 := by
    simp [primePowerProduct]
  rcases finite_crt_join (∅ : Finset Nat) kappa (by simp) with ⟨crt⟩
  exact ⟨(ZMod.ringEquivCongr hproduct).symm.trans crt⟩

#print axioms finite_crt_join_empty

/-- A zero exponent contributes a subsingleton `ZMod 1` coordinate without changing CRT. -/
theorem finite_crt_join_zero_exponent
    (S : Finset Nat) (kappa : Nat -> Nat) (p : S)
    (hS : forall q, q ∈ S -> Nat.Prime q) (hzero : kappa p = 0) :
    Nonempty
        (ZMod (primePowerProduct S kappa) ≃+*
          forall q : S, ZMod ((q : Nat) ^ kappa q)) ∧
      Subsingleton (ZMod ((p : Nat) ^ kappa p)) := by
  refine ⟨finite_crt_join S kappa hS, ?_⟩
  rw [hzero, pow_zero]
  infer_instance

#print axioms finite_crt_join_zero_exponent

/-- A singleton family needs no primality assumption: pairwise coprimality is vacuous. -/
theorem finite_crt_join_singleton (p exponent : Nat) :
    Nonempty
      (ZMod (p ^ exponent) ≃+*
        forall q : ({p} : Finset Nat), ZMod ((q : Nat) ^ exponent)) := by
  let a : ({p} : Finset Nat) -> Nat := fun q => (q : Nat) ^ exponent
  have hcoprime : Pairwise (Nat.Coprime on a) := by
    intro i j hij
    exact (hij (Subsingleton.elim i j)).elim
  have hproduct : (∏ q, a q) = p ^ exponent := by
    rw [← Finset.prod_subtype {p} (fun _ => Iff.rfl)
      (fun q => q ^ exponent)]
    simp
  rw [← hproduct]
  exact ⟨ZMod.prodEquivPi a hcoprime⟩

#print axioms finite_crt_join_singleton

/-- A nonempty family with every exponent zero still decomposes `ZMod 1` into trivial factors. -/
theorem finite_crt_join_all_zero_exponents :
    Nonempty
      (ZMod 1 ≃+* forall _p : ({2, 3} : Finset Nat), ZMod 1) := by
  have hproduct : primePowerProduct {2, 3} (fun _ => 0) = 1 := by
    norm_num [primePowerProduct]
  rcases finite_crt_join ({2, 3} : Finset Nat) (fun _ => 0) (by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_three) with ⟨crt⟩
  exact ⟨(ZMod.ringEquivCongr hproduct).symm.trans crt⟩

#print axioms finite_crt_join_all_zero_exponents

/-- Without the prime-set hypothesis, overlapping composite labels can make the result false. -/
theorem prime_hypothesis_is_necessary :
    ¬Nonempty
      (ZMod (primePowerProduct {2, 4} (fun _ => 1)) ≃+*
        forall p : ({2, 4} : Finset Nat), ZMod ((p : Nat) ^ 1)) := by
  rintro ⟨equiv⟩
  have hfour_maps_to_zero :
      equiv (4 : ZMod (primePowerProduct {2, 4} (fun _ => 1))) = 0 := by
    funext p
    rw [map_ofNat]
    change (4 : ZMod ((p : Nat) ^ 1)) = 0
    have hp : (p : Nat) = 2 ∨ (p : Nat) = 4 := by
      simpa only [Finset.mem_insert, Finset.mem_singleton] using p.property
    rcases hp with hp | hp
    · rw [hp, pow_one]
      decide
    · rw [hp, pow_one]
      decide
  have hfour_eq_zero :
      (4 : ZMod (primePowerProduct {2, 4} (fun _ => 1))) = 0 := by
    apply equiv.injective
    simpa using hfour_maps_to_zero
  have hproduct : primePowerProduct {2, 4} (fun _ => 1) = 8 := by
    norm_num [primePowerProduct]
  rw [hproduct] at hfour_eq_zero
  exact (by decide : (4 : ZMod 8) ≠ 0) hfour_eq_zero

#print axioms prime_hypothesis_is_necessary

end D5.S3.Factorization.PrimePowers.FiniteCrtJoin
