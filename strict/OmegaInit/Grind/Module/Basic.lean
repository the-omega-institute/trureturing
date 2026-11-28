/-
Copyright (c) 2025 Lean FRO, LLC. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
prelude
public import OmegaInit.Data.Int.DivMod.Basic
public import OmegaInit.Data.Zero
import OmegaInit.Data.Int.Lemmas

port_prop_record Lean.Grind.AddRightCancel
port_native_records Lean.Grind.AddCommMonoid, Lean.Grind.AddCommGroup, Lean.Grind.NatModule, Lean.Grind.IntModule
port_prop_record Lean.Grind.NoNatZeroDivisors

public section
namespace Omega.Lean.Grind
export NoNatZeroDivisors (no_nat_zero_divisors)
end Omega.Lean.Grind
end

port_definition Lean.Grind.AddCommMonoid.ctorIdx with_native_code
port_definition Lean.Grind.AddCommMonoid.noConfusionType
port_definition Lean.Grind.AddCommMonoid.noConfusion
port_definition Lean.Grind.AddCommMonoid.mk.noConfusion
port_definition Lean.Grind.AddCommGroup.ctorIdx with_native_code
port_definition Lean.Grind.AddCommGroup.noConfusionType
port_definition Lean.Grind.AddCommGroup.noConfusion
port_definition Lean.Grind.AddCommGroup.mk.noConfusion
port_definition Lean.Grind.NatModule.ctorIdx with_native_code
port_definition Lean.Grind.NatModule.noConfusionType
port_definition Lean.Grind.NatModule.noConfusion
port_definition Lean.Grind.NatModule.mk.noConfusion
port_definition Lean.Grind.IntModule.ctorIdx with_native_code
port_definition Lean.Grind.IntModule.noConfusionType
port_definition Lean.Grind.IntModule.noConfusion
port_definition Lean.Grind.IntModule.mk.noConfusion

attribute [instance] Omega.Lean.Grind.AddCommMonoid.toZero Omega.Lean.Grind.AddCommMonoid.toAdd
attribute [instance] Omega.Lean.Grind.AddCommGroup.toAddCommMonoid
attribute [instance] Omega.Lean.Grind.AddCommGroup.toNeg Omega.Lean.Grind.AddCommGroup.toSub
attribute [instance] Omega.Lean.Grind.NatModule.toAddCommMonoid Omega.Lean.Grind.IntModule.toAddCommGroup
attribute [instance 100] Omega.Lean.Grind.AddCommMonoid.toZero Omega.Lean.Grind.AddCommMonoid.toAdd
attribute [instance 100] Omega.Lean.Grind.AddCommGroup.toAddCommMonoid Omega.Lean.Grind.AddCommGroup.toNeg Omega.Lean.Grind.AddCommGroup.toSub
attribute [instance 100] Omega.Lean.Grind.NatModule.toAddCommMonoid Omega.Lean.Grind.NatModule.nsmul
attribute [instance 100] Omega.Lean.Grind.IntModule.toAddCommGroup Omega.Lean.Grind.IntModule.zsmul

port_proof Lean.Grind.IntModule.toNatModule._proof_1
port_proof Lean.Grind.IntModule.toNatModule._proof_2
port_definition Lean.Grind.IntModule.toNatModule with_native_code
attribute [instance 100] Omega.Lean.Grind.IntModule.toNatModule
port_proof Lean.Grind.AddCommMonoid.zero_add
port_proof Lean.Grind.AddCommMonoid.add_left_comm
port_proof Lean.Grind.AddCommGroup.add_neg_cancel
port_proof Lean.Grind.AddCommGroup.add_left_inj
namespace Omega.Lean.Grind.AddCommGroup
open AddCommMonoid
variable {M : Type u} [AddCommGroup M]

public theorem add_right_inj (a b c : M) : Iff (Eq (Add.add a b) (Add.add a c)) (Eq b c) :=
  Iff.intro (fun h => (add_left_inj a).mp ((add_comm b a).trans (h.trans (add_comm a c))))
    (fun h => congrArg (Add.add a) h)

public theorem neg_zero : Eq (Neg.neg (Zero.zero : M)) Zero.zero :=
  (add_left_inj (Zero.zero : M)).mp ((neg_add_cancel _).trans (add_zero _).symm)

public theorem neg_neg (a : M) : Eq (Neg.neg (Neg.neg a)) a :=
  (add_left_inj (Neg.neg a)).mp ((neg_add_cancel _).trans (add_neg_cancel a).symm)

end Omega.Lean.Grind.AddCommGroup
port_proof Lean.Grind.AddCommGroup.neg_eq_zero
namespace Omega.Lean.Grind.AddCommGroup
open AddCommMonoid
variable {M : Type u} [AddCommGroup M]

public theorem neg_add (a b : M) : Eq (Neg.neg (Add.add a b)) (Add.add (Neg.neg a) (Neg.neg b)) :=
  let rotate := add_assoc (Neg.neg a) (Neg.neg b) (Add.add a b)
  let swap := congrArg (fun t => Add.add (Neg.neg a) (Add.add (Neg.neg b) t)) (add_comm a b)
  let reassoc := congrArg (Add.add (Neg.neg a)) (add_assoc (Neg.neg b) b a).symm
  let cancel := congrArg (fun t => Add.add (Neg.neg a) (Add.add t a)) (neg_add_cancel b)
  let finish := (congrArg (Add.add (Neg.neg a)) (zero_add a)).trans (neg_add_cancel a)
  (add_left_inj (Add.add a b)).mp ((neg_add_cancel _).trans
    (rotate.trans (swap.trans (reassoc.trans (cancel.trans finish)))).symm)

end Omega.Lean.Grind.AddCommGroup
port_proof Lean.Grind.AddCommGroup.neg_sub
port_proof Lean.Grind.AddCommGroup.sub_self
port_proof Lean.Grind.AddCommGroup.sub_eq_iff
namespace Omega.Lean.Grind.AddCommGroup
public theorem sub_eq_zero_iff {M : Type u} [AddCommGroup M] {a b : M} :
    Iff (Eq (Sub.sub a b) Zero.zero) (Eq a b) :=
  sub_eq_iff.trans (Iff.intro (fun h => h.trans (AddCommMonoid.zero_add b))
    (fun h => h.trans (AddCommMonoid.zero_add b).symm))
end Omega.Lean.Grind.AddCommGroup
port_proof Lean.Grind.AddCommGroup.add_sub_cancel
port_proof Lean.Grind.AddCommGroup.sub_add_cancel
port_proof Lean.Grind.AddCommGroup.neg_eq_iff
port_proof Lean.Grind.NatModule.one_nsmul
port_proof Lean.Grind.NatModule.add_nsmul
port_proof Lean.Grind.NatModule.nsmul_zero
port_proof Lean.Grind.NatModule.nsmul_add
namespace Omega.Lean.Grind.NatModule
public theorem mul_nsmul {M : Type u} [NatModule M] (n m : Nat) (a : M) :
    Eq (SMul.smul (Nat.mul n m) a) (SMul.smul n (SMul.smul m a)) :=
  Nat.rec (motive := fun i => Eq (SMul.smul (Nat.mul i m) a) (SMul.smul i (SMul.smul m a)))
    ((congrArg (fun k => SMul.smul k a) (Nat.zero_mul m)).trans
      ((zero_nsmul a).trans (zero_nsmul (SMul.smul m a)).symm))
    (fun i ih =>
      let step := congrArg (fun k => SMul.smul k a) (Nat.succ_mul i m)
      let combine := congrArg (fun x => Add.add x (SMul.smul m a)) ih
      step.trans ((add_nsmul _ _ a).trans (combine.trans (add_one_nsmul i (SMul.smul m a)).symm))) n
end Omega.Lean.Grind.NatModule
port_proof Lean.Grind.IntModule.neg_zsmul
port_proof Lean.Grind.IntModule.zsmul_zero
port_proof Lean.Grind.IntModule.zsmul_add
port_proof Lean.Grind.IntModule.zsmul_neg
port_proof Lean.Grind.IntModule.zsmul_sub
port_proof Lean.Grind.IntModule.sub_zsmul
namespace Omega.Lean.Grind.IntModule
variable {M : Type u} [IntModule M]

private theorem natMul (n : Nat) (m : Int) (a : M) :
    Eq (SMul.smul (Int.mul (Int.ofNat n) m) a) (SMul.smul (Int.ofNat n) (SMul.smul m a)) :=
  Nat.rec (motive := fun i => Eq (SMul.smul (Int.mul (Int.ofNat i) m) a) (SMul.smul (Int.ofNat i) (SMul.smul m a)))
    ((congrArg (fun z => SMul.smul z a) (Int.zero_mul m)).trans
      ((zero_zsmul a).trans (zero_zsmul (SMul.smul m a)).symm))
    (fun i ih =>
      let one := Int.ofNat (Nat.succ Nat.zero)
      let dist := Int.add_mul (Int.ofNat i) one m
      let left := congrArg (fun z => SMul.smul z a) (dist.trans (congrArg (Int.add (Int.mul (Int.ofNat i) m)) (Int.one_mul m)))
      let right := (add_zsmul (Int.ofNat i) one (SMul.smul m a)).trans
        (congrArg (Add.add (SMul.smul (Int.ofNat i) (SMul.smul m a))) (one_zsmul (SMul.smul m a)))
      left.trans ((add_zsmul (Int.mul (Int.ofNat i) m) m a).trans
        ((congrArg (fun x => Add.add x (SMul.smul m a)) ih).trans right.symm))) n

public theorem mul_zsmul (n m : Int) (a : M) : Eq (SMul.smul (Int.mul n m) a) (SMul.smul n (SMul.smul m a)) :=
  Int.rec (motive := fun k => Eq (SMul.smul (Int.mul k m) a) (SMul.smul k (SMul.smul m a)))
    (fun i => natMul i m a)
    (fun i =>
      let z := Int.ofNat (Nat.succ i)
      let moveNeg := congrArg (fun k => SMul.smul k a) (Int.neg_mul z m)
      moveNeg.trans ((neg_zsmul (Int.mul z m) a).trans
        ((congrArg Neg.neg (natMul (Nat.succ i) m a)).trans (neg_zsmul z (SMul.smul m a)).symm))) n

end Omega.Lean.Grind.IntModule

namespace Omega.Lean.Grind.NoNatZeroDivisors
set_option linter.defProp false in
@[instance_reducible] public def mk' {M : Type u} [IntModule M]
    (cancel : ∀ (k : Nat) (a : M), Ne k Nat.zero → Eq (SMul.smul k a) Zero.zero → Eq a Zero.zero) :
    NoNatZeroDivisors M :=
  NoNatZeroDivisors.mk fun k a b nz hab =>
    let castA := IntModule.zsmul_natCast_eq_nsmul k a
    let castB := IntModule.zsmul_natCast_eq_nsmul k b
    let eqInt := castA.trans (hab.trans castB.symm)
    let subZero := AddCommGroup.sub_eq_zero_iff.mpr eqInt
    let dist := IntModule.zsmul_sub (Int.ofNat k) a b
    let castSub := IntModule.zsmul_natCast_eq_nsmul k (Sub.sub a b)
    AddCommGroup.sub_eq_zero_iff.mp (cancel k (Sub.sub a b) nz (castSub.symm.trans (dist.trans subZero)))
end Omega.Lean.Grind.NoNatZeroDivisors
namespace Omega.Lean.Grind.NoNatZeroDivisors
public theorem eq_zero_of_mul_eq_zero {M : Type u} [NatModule M] [NoNatZeroDivisors M] {k : Nat} {a : M}
    (nonzero : Ne k Nat.zero) (cancel : Eq (SMul.smul k a) Zero.zero) : Eq a Zero.zero :=
  no_nat_zero_divisors k a Zero.zero nonzero (cancel.trans (NatModule.nsmul_zero k).symm)
end Omega.Lean.Grind.NoNatZeroDivisors
