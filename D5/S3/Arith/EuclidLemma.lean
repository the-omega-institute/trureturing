/- GID: D5/S3/Arith/EuclidLemma
   generality: G
   mirror-B: D5/B/S3/Arith/EuclidLemma
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A prime dividing a product of two naturals divides one of the factors. -/

module
prelude
public import OmegaMathlib.Data.Nat.Prime.Defs
public import OmegaMath.Arithmetic.Euclidean.GCD

/-! Euclid's lemma from the prime divisor characterization and Bézout's identity. -/

namespace D5.S3.Arith.EuclidLemma

open Omega Omega.Arithmetic

/-- Euclid's lemma: if a prime `p` divides the product `a * b` of two natural
numbers, then `p` divides `a` or `p` divides `b`. -/
public theorem euclid_prime_dvd_mul {p a b : Nat} (hp : Nat.Prime p)
    (h : Exists (fun k => Eq (a.mul b) (p.mul k))) :
    Or (Exists (fun k => Eq a (p.mul k))) (Exists (fun k => Eq b (p.mul k))) :=
  (hp.eq_one_or_self_of_dvd (gcd p a) (gcd_dvd_left p a)).elim
    (fun hg => Or.inr (dvd_of_dvd_mul_of_gcd_eq_one hg h))
    (fun hg => Or.inl (Eq.subst (motive := fun d => Dvd d a) hg (gcd_dvd_right p a)))

end D5.S3.Arith.EuclidLemma
