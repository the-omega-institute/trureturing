/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
prelude
public import OmegaInit.Grind.Ordered.Module

port_proof Quot.lift.congr_simp
port_proof Lean.Grind.IntModule.OfNatModule.instAssociativeHAdd
port_proof Lean.Grind.IntModule.OfNatModule.instCommutativeHAdd
port_definition Lean.Grind.IntModule.OfNatModule.r
port_definition Lean.Grind.IntModule.OfNatModule.Q
namespace Omega.Lean.Grind.IntModule.OfNatModule
open AddCommMonoid
variable {α : Type u} [NatModule α]

public theorem r_rfl (a : Prod α α) : r α a a :=
  Exists.intro Zero.zero (congrArg (fun s => Add.add s Zero.zero) (add_comm a.fst a.snd))

public theorem r_sym {a b : Prod α α} : r α a b → r α b a := fun h =>
  Exists.elim h (fun k eq => Exists.intro k
    ((congrArg (fun s => Add.add s k) (add_comm b.fst a.snd)).trans
      (eq.symm.trans (congrArg (fun s => Add.add s k) (add_comm a.fst b.snd)))))

private theorem exchange (a b c d : α) :
    Eq (Add.add (Add.add a b) (Add.add c d)) (Add.add (Add.add a c) (Add.add b d)) :=
  (add_assoc a b (Add.add c d)).trans
    ((congrArg (Add.add a) (add_left_comm b c d)).trans (add_assoc a c (Add.add b d)).symm)

private theorem collectWitness (a b c d k l : α) :
    Eq (Add.add (Add.add (Add.add a b) k) (Add.add (Add.add c d) l))
       (Add.add (Add.add a d) (Add.add (Add.add b c) (Add.add k l))) :=
  let regroup := (congrArg (Add.add (Add.add a b)) (add_comm c d)).trans (exchange a b d c)
  (exchange (Add.add a b) k (Add.add c d) l).trans
    ((congrArg (fun s => Add.add s (Add.add k l)) regroup).trans
      (add_assoc (Add.add a d) (Add.add b c) (Add.add k l)))

public theorem r_trans {a b c : Prod α α} : r α a b → r α b c → r α a c := fun hab hbc =>
  Exists.elim hab (fun k h₁ => Exists.elim hbc (fun l h₂ =>
    let swap := congrArg (fun s => Add.add (Add.add a.fst c.snd) (Add.add s (Add.add k l))) (add_comm b.fst b.snd)
    let lhs := collectWitness a.fst b.snd b.fst c.snd k l
    let rhs := collectWitness a.snd b.fst b.snd c.fst k l
    Exists.intro (Add.add (Add.add b.fst b.snd) (Add.add k l))
      (swap.trans (lhs.symm.trans ((congr (congrArg Add.add h₁) h₂).trans rhs)))))
end Omega.Lean.Grind.IntModule.OfNatModule

port_definition Lean.Grind.IntModule.OfNatModule.Q.mk with_native_code
port_definition Lean.Grind.IntModule.OfNatModule.Q.liftOn₂ with_native_code
port_proof Lean.Grind.IntModule.OfNatModule.Q.ind
port_definition Lean.Grind.IntModule.OfNatModule.zero with_native_code
port_definition Lean.Grind.IntModule.OfNatModule.toQ with_native_code
port_definition Lean.Grind.IntModule.OfNatModule.instLEQOfOrderedAdd.match_1 with_native_code

namespace Omega.Lean.Grind.IntModule.OfNatModule
open Std AddCommMonoid
variable {α : Type u} [NatModule α]

/- These representative computations expose the operations on pairs.
The public quotient operations also require identifying related representatives. -/
public theorem toQ_zero : Eq (toQ (Zero.zero : α)) zero := Omega.rfl

public theorem toQ_add (a b : α) :
    Eq (toQ (Add.add a b)) (Q.mk (Prod.mk (Add.add a b) (Add.add (Zero.zero : α) Zero.zero))) :=
  congrArg (fun x => Q.mk (Prod.mk (Add.add a b) x)) (add_zero (Zero.zero : α)).symm

public theorem toQ_smul (n : Nat) (a : α) :
    Eq (toQ (SMul.smul n a)) (Q.mk (Prod.mk (SMul.smul n a) (SMul.smul n (Zero.zero : α)))) :=
  congrArg (fun x => Q.mk (Prod.mk (SMul.smul n a) x)) (NatModule.nsmul_zero n).symm

/- The public quotient comparisons retain the full representative coherence.
At universe zero it implies propositional extensionality by
OmegaChecks.InitBoundaries.EnvelopeOrder.propextFromModuleLift.
Conversely moduleLiftFromPropext derives that coherence at every universe, and
moduleOrderFromPropext reconstructs the entire pinned LE instance with its binary
quotient lift. The bare LE type also admits the constant-false comparison.
The public types of instIsPreorderQ and instOrderedAddQ also fix that comparison
at arbitrary quotient inputs. -/
/- instLTQOfOrderedAdd reduces on arbitrary x and y to x ≤ y ∧ ¬ y ≤ x.
Both operands retain the full canonical quotient lift. With propext,
moduleStrictOrderFromPropext reconstructs the pinned definition. -/
/- instIsLinearPreorderQ additionally assumes a linear preorder on the base.
LinearEnvelopeOrder.propextFromLinearLift uses a total relation on Nat whose
comparisons at (1,0) and (2,1) reduce to any two equivalent propositions.
Its converse linearLiftFromPropext constructs precisely the restricted coherence. -/
/- The lifts nsmul, zsmul, add, sub and neg require related pairs to have equal
classes. Their equations and the IntModule and ordered instances depend on
those lifts. Q.exact and toQ_inj remain open under the zero-axiom requirement. -/
public theorem mk_le_mk [LE α] [IsPreorder α] [OrderedAdd α] {a₁ a₂ b₁ b₂ : α} :
    Iff (LE.le (Add.add a₁ b₂) (Add.add a₂ b₁)) (LE.le (Add.add a₁ b₂) (Add.add a₂ b₁)) :=
  Iff.refl _

public theorem toQ_le [LE α] [IsPreorder α] [OrderedAdd α] {a b : α} :
    Iff (LE.le (Add.add a Zero.zero) (Add.add Zero.zero b)) (LE.le a b) :=
  Iff.of_eq (congr (congrArg LE.le (add_zero a)) (zero_add b))

public theorem toQ_lt [LE α] [LT α] [LawfulOrderLT α] [IsPreorder α] [OrderedAdd α] {a b : α} :
    Iff (And (LE.le (Add.add a Zero.zero) (Add.add Zero.zero b))
      (Not (LE.le (Add.add b Zero.zero) (Add.add Zero.zero a)))) (LT.lt a b) :=
  (Iff.intro (fun h => And.intro (toQ_le.mp h.left) (fun rev => h.right (toQ_le.mpr rev)))
    (fun h => And.intro (toQ_le.mpr h.left) (fun rev => h.right (toQ_le.mp rev)))).trans
    (LawfulOrderLT.lt_iff a b).symm
end Omega.Lean.Grind.IntModule.OfNatModule
