/- GID: D5/S3/PrimeForms/Crossing/ResonanceFactors
   generality: G
   mirror-B: D5/B/S3/PrimeForms/Crossing/ResonanceFactors
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The two explicit resonance factors vanish identically exactly at alphabet value three. -/

module
prelude
public import OmegaMath.Data.Int

/-! The two explicitly given polynomial factors and their common zero parameter. -/

namespace D5.S3.PrimeForms.Crossing.ResonanceFactors

open Omega

/-- The two exceptional deficit factors from residual E.67 are identically zero as
polynomials in `p` and `r` exactly when the alphabet parameter `m` equals three. -/
public theorem resonance_factors_identically_zero_iff (m : Int) :
    Iff (∀ p r : Int,
      And (Eq (((Int.two.mul r).mul (m.sub (Int.ofNat Nat.one.succ.succ))).mul
        ((Int.two.mul p).add r)) Int.zero)
        (Eq (((Int.two.neg.mul r).mul (m.sub (Int.ofNat Nat.one.succ.succ))).mul (p.add r)) Int.zero))
      (Eq m (Int.ofNat Nat.one.succ.succ)) :=
  let three := Int.ofNat Nat.one.succ.succ
  Iff.intro
    (fun h =>
      have arg : Eq ((Int.two.mul Int.zero).add Int.one) Int.one :=
        (congrArg (fun x : Int => x.add Int.one) (Int.mul_zero Int.two)).trans (Int.zero_add Int.one)
      have product : Eq (((Int.two.mul Int.one).mul (m.sub three)).mul
          ((Int.two.mul Int.zero).add Int.one)) (Int.two.mul (m.sub three)) :=
        (congrArg (fun x : Int => x.mul ((Int.two.mul Int.zero).add Int.one))
          (congrArg (fun x : Int => x.mul (m.sub three)) (Int.mul_one Int.two))).trans
          ((congrArg (Int.two.mul (m.sub three)).mul arg).trans (Int.mul_one _))
      have zero := product.symm.trans (h Int.zero Int.one).left
      Int.sub_eq_zero.mp ((Int.mul_eq_zero.mp zero).elim
        (fun e => False.elim (Int.ofNat_succ_ne_zero Nat.one e)) (fun e => e)))
    (fun h p r =>
      have diffZero : Eq (m.sub three) Int.zero := Int.sub_eq_zero.mpr h
      have vanish (a b : Int) : Eq ((a.mul (m.sub three)).mul b) Int.zero :=
        (congrArg (fun t : Int => (a.mul t).mul b) diffZero).trans
          ((congrArg (fun t : Int => t.mul b) (Int.mul_zero a)).trans (Int.zero_mul b))
      And.intro (vanish (Int.two.mul r) ((Int.two.mul p).add r))
        (vanish (Int.two.neg.mul r) (p.add r)))

end D5.S3.PrimeForms.Crossing.ResonanceFactors
