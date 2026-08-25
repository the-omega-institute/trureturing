/- GID: D5/S3/Arith/Congruence/HorizontalJointKernel
   generality: G
   mirror-B: D5/B/S3/Arith/Congruence/HorizontalJointKernel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Joint prime-power readings have the product modulus as their integer kernel. -/

import D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Coprime.Lemmas

/- Library-search audit trail (2026-08-25):
   * Current-tree searches for joint readouts, joint kernels, residue equality,
     prime-power products, and divisibility found no declaration with this
     integer-carrier equivalence. `ResidueCodeDynamicRange.agree_on_iff_prod_dvd`
     is restricted to ordered natural messages and arbitrary coprime moduli.
   * The body-shape search for `fun x i => q i x` found the canonical
     `JointFaithfulnessLeibnizCriterion.jointReadout`, which is imported and
     instantiated here. No new readout definition is introduced.
   * Exact pinned-library hits `ZMod.intCast_eq_intCast_iff_dvd_sub`,
     `Fintype.prod_dvd_of_coprime`, and `Nat.coprime_primes` supply the local
     kernels and their finite coprime product. No library theorem states the
     complete joint-kernel equivalence below.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.Congruence.HorizontalJointKernel

open D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion

/-- Equality of all selected positive prime-power reductions is exactly
divisibility of the integer difference by their product modulus. -/
theorem horizontal_joint_kernel
    (S : Finset Nat) (hprime : forall p, p ∈ S -> Nat.Prime p)
    (kappa : S -> ℕ+) (x y : Int) :
    jointReadout
        (fun p : S => fun z : Int => (z : ZMod (p.1 ^ (kappa p).1))) x =
      jointReadout
        (fun p : S => fun z : Int => (z : ZMod (p.1 ^ (kappa p).1))) y <->
      (∏ p : S, (p.1 : Int) ^ (kappa p).1) ∣ x - y := by
  constructor
  · intro sameReadout
    apply Fintype.prod_dvd_of_coprime
    · intro p q hpq
      have hpNeq : p.1 ≠ q.1 := by
        intro samePrime
        exact hpq (Subtype.ext samePrime)
      have coprimePrimes : Nat.Coprime p.1 q.1 :=
        (Nat.coprime_primes (hprime p.1 p.2) (hprime q.1 q.2)).2 hpNeq
      exact coprimePrimes.isCoprime.pow
    · intro p
      have sameComponent := congrFun sameReadout p
      have componentDivides :
          ((p.1 : Int) ^ (kappa p).1) ∣ y - x := by
        simpa only [Nat.cast_pow] using
          (ZMod.intCast_eq_intCast_iff_dvd_sub x y
            (p.1 ^ (kappa p).1)).mp sameComponent
      rw [show x - y = -(y - x) by ring, Int.dvd_neg]
      exact componentDivides
  · intro productDivides
    funext p
    apply (ZMod.intCast_eq_intCast_iff_dvd_sub x y
      (p.1 ^ (kappa p).1)).2
    rw [show y - x = -(x - y) by ring, Int.dvd_neg]
    have componentDividesProduct :
        ((p.1 : Int) ^ (kappa p).1) ∣
          ∏ q : S, (q.1 : Int) ^ (kappa q).1 :=
      Finset.dvd_prod_of_mem
        (fun q : S => (q.1 : Int) ^ (kappa q).1) (Finset.mem_univ p)
    simpa only [Nat.cast_pow] using componentDividesProduct.trans productDivides

#print axioms horizontal_joint_kernel

end D5.S3.Arith.Congruence.HorizontalJointKernel
