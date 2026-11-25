/- GID: D5/S3/PrimeForms/Crossing/ResonanceFactors
   generality: G
   mirror-B: D5/B/S3/PrimeForms/Crossing/ResonanceFactors
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The two explicit resonance factors vanish identically exactly at alphabet value three. -/

module
prelude
public import OmegaInit.Data.Int

/-! The two explicitly given polynomial factors and their common zero parameter. -/

namespace D5.S3.PrimeForms.Crossing.ResonanceFactors

open Omega

/-- The two exceptional deficit factors from residual E.67 are identically zero as
polynomials in `p` and `r` exactly when the alphabet parameter `m` equals three. -/
public theorem resonance_factors_identically_zero_iff (m : Int) :
    let two := Int.ofNat Nat.zero.succ.succ
    let three := Int.ofNat Nat.zero.succ.succ.succ
    Iff (∀ p r : Int,
      And (Eq (((two.mul r).mul (m.sub three)).mul
        ((two.mul p).add r)) (Int.ofNat Nat.zero))
        (Eq (((two.neg.mul r).mul (m.sub three)).mul (p.add r)) (Int.ofNat Nat.zero)))
      (Eq m three) :=
  let zero := Int.ofNat Nat.zero
  let one := Int.ofNat Nat.zero.succ
  let two := Int.ofNat Nat.zero.succ.succ
  let three := Int.ofNat Nat.zero.succ.succ.succ
  Iff.intro
    (fun h =>
      have arg : Eq ((two.mul zero).add one) one :=
        (congrArg (fun x : Int => x.add one) (Int.mul_zero two)).trans (Int.zero_add one)
      have product : Eq (((two.mul one).mul (m.sub three)).mul
          ((two.mul zero).add one)) (two.mul (m.sub three)) :=
        (congrArg (fun x : Int => x.mul ((two.mul zero).add one))
          (congrArg (fun x : Int => x.mul (m.sub three)) (Int.mul_one two))).trans
          ((congrArg (two.mul (m.sub three)).mul arg).trans (Int.mul_one _))
      have vanishes := product.symm.trans (h zero one).left
      Int.sub_eq_zero.mp ((Int.mul_eq_zero.mp vanishes).elim
        (fun e => False.elim (Nat.succ_ne_zero _ (Int.ofNat_inj.mp e))) (fun e => e)))
    (fun h p r =>
      have diffZero : Eq (m.sub three) zero := Int.sub_eq_zero.mpr h
      have vanish (a b : Int) : Eq ((a.mul (m.sub three)).mul b) zero :=
        (congrArg (fun t : Int => (a.mul t).mul b) diffZero).trans
          ((congrArg (fun t : Int => t.mul b) (Int.mul_zero a)).trans (Int.zero_mul b))
      And.intro (vanish (two.mul r) ((two.mul p).add r))
        (vanish (two.neg.mul r) (p.add r)))

end D5.S3.PrimeForms.Crossing.ResonanceFactors
