/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dany Fabian, Sebastian Ullrich
-/
module
prelude
public import OmegaInit.Core
public import OmegaInit.Data.Nat.Bitwise.Basic
import all OmegaInit.Data.Nat.Bitwise.Basic
import all OmegaInit.Prelude

noncomputable section

@[expose] public section

port_inductive Ordering

port_definition Ordering.ctorIdx
port_definition Ordering.then._sparseCasesOn_1
port_definition Ordering.then.match_1
port_definition Ordering.isLE._sparseCasesOn_1
port_definition Ordering.isLE.match_1
port_definition Ordering.isLT._sparseCasesOn_1
port_definition Ordering.isLT.match_1
port_definition Ordering.then
port_definition Ordering.isEq
port_definition Ordering.isNe
port_definition Ordering.isLE
port_definition Ordering.isLT
port_definition Ordering.isGT
port_definition Ordering.isGE

namespace Omega

namespace Ordering

def swap : Ordering → Ordering := Ordering.rec gt «eq» lt

def then' (a b : Ordering) : Ordering := Ordering.rec a b a a

protected theorem «forall» {p : Ordering → Prop} :
    Iff (∀ o, p o) (And (p lt) (And (p «eq») (p gt))) :=
  Iff.intro (fun h => And.intro (h lt) (And.intro (h «eq») (h gt)))
    (fun h => Ordering.rec h.left h.right.left h.right.right)

protected theorem «exists» {p : Ordering → Prop} :
    Iff (Exists p) (Or (p lt) (Or (p «eq») (p gt))) :=
  Iff.intro
    (fun h => h.elim (Ordering.rec
      (motive := fun o => p o → Or (p lt) (Or (p «eq») (p gt)))
      Or.inl (fun heq => Or.inr (Or.inl heq)) (fun hgt => Or.inr (Or.inr hgt))))
    (fun h => h.elim (Exists.intro lt)
      (fun tail => tail.elim (Exists.intro «eq») (Exists.intro gt)))


private theorem falseTrue : Ne Bool.false Bool.true := Bool.ne_true_of_eq_false Omega.rfl
private theorem trueFalse : Ne Bool.true Bool.false := Bool.ne_false_of_eq_true Omega.rfl

private theorem ltNeEq : Ne lt «eq» :=
  fun h => falseTrue (congrArg isEq h)

private theorem ltNeGt : Ne lt gt :=
  fun h => falseTrue (congrArg isGT h)

private theorem eqNeLt : Ne «eq» lt :=
  fun h => falseTrue (congrArg isLT h)

private theorem eqNeGt : Ne «eq» gt :=
  fun h => falseTrue (congrArg isGT h)

private theorem gtNeLt : Ne gt lt :=
  fun h => falseTrue (congrArg isLT h)

private theorem gtNeEq : Ne gt «eq» :=
  fun h => falseTrue (congrArg isEq h)


theorem isLT_lt : Eq (isLT lt) Bool.true :=
  Omega.rfl

theorem isLE_lt : Eq (isLE lt) Bool.true :=
  Omega.rfl

theorem isEq_lt : Eq (isEq lt) Bool.false :=
  Omega.rfl

theorem isNe_lt : Eq (isNe lt) Bool.true :=
  Omega.rfl

theorem isGE_lt : Eq (isGE lt) Bool.false :=
  Omega.rfl

theorem isGT_lt : Eq (isGT lt) Bool.false :=
  Omega.rfl

theorem isLT_eq : Eq (isLT «eq») Bool.false :=
  Omega.rfl

theorem isLE_eq : Eq (isLE «eq») Bool.true :=
  Omega.rfl

theorem isEq_eq : Eq (isEq «eq») Bool.true :=
  Omega.rfl

theorem isNe_eq : Eq (isNe «eq») Bool.false :=
  Omega.rfl

theorem isGE_eq : Eq (isGE «eq») Bool.true :=
  Omega.rfl

theorem isGT_eq : Eq (isGT «eq») Bool.false :=
  Omega.rfl

theorem isLT_gt : Eq (isLT gt) Bool.false :=
  Omega.rfl

theorem isLE_gt : Eq (isLE gt) Bool.false :=
  Omega.rfl

theorem isEq_gt : Eq (isEq gt) Bool.false :=
  Omega.rfl

theorem isNe_gt : Eq (isNe gt) Bool.true :=
  Omega.rfl

theorem isGE_gt : Eq (isGE gt) Bool.true :=
  Omega.rfl

theorem isGT_gt : Eq (isGT gt) Bool.true :=
  Omega.rfl

theorem swap_lt : Eq (swap lt) gt :=
  Omega.rfl

theorem swap_eq : Eq (swap «eq») «eq» :=
  Omega.rfl

theorem swap_gt : Eq (swap gt) lt :=
  Omega.rfl

theorem eq_eq_of_isLE_of_isLE_swap : ∀ {o : Ordering}, Eq (isLE o) Bool.true → Eq (isLE (swap o)) Bool.true → Eq o «eq» :=
  @Ordering.rec _
    (fun _ h => False.elim (falseTrue h))
    (fun _ _ => Omega.rfl)
    (fun h => False.elim (falseTrue h))

theorem eq_eq_of_isGE_of_isGE_swap : ∀ {o : Ordering}, Eq (isGE o) Bool.true → Eq (isGE (swap o)) Bool.true → Eq o «eq» :=
  @Ordering.rec _
    (fun h => False.elim (falseTrue h))
    (fun _ _ => Omega.rfl)
    (fun _ h => False.elim (falseTrue h))

theorem eq_eq_of_isLE_of_isGE : ∀ {o : Ordering}, Eq (isLE o) Bool.true → Eq (isGE o) Bool.true → Eq o «eq» :=
  @Ordering.rec _
    (fun _ h => False.elim (falseTrue h))
    (fun _ _ => Omega.rfl)
    (fun h => False.elim (falseTrue h))

theorem eq_eq_iff_isLE_and_isGE : ∀ {o : Ordering}, Iff (Eq o «eq») (And (Eq (isLE o) Bool.true) (Eq (isGE o) Bool.true)) :=
  @Ordering.rec _
    (iff_of_false ltNeEq (fun h => falseTrue h.right))
    (iff_of_true Omega.rfl (And.intro Omega.rfl Omega.rfl))
    (iff_of_false gtNeEq (fun h => falseTrue h.left))

theorem eq_swap_iff_eq_eq : ∀ {o : Ordering}, Iff (Eq o (swap o)) (Eq o «eq») :=
  @Ordering.rec _
    (iff_of_false ltNeGt ltNeEq)
    (iff_of_true Omega.rfl Omega.rfl)
    (iff_of_false gtNeLt gtNeEq)

theorem eq_eq_of_eq_swap : ∀ {o : Ordering}, Eq o (swap o) → Eq o «eq» :=
  fun h => eq_swap_iff_eq_eq.mp h

theorem isLE_eq_false : ∀ {o : Ordering}, Iff (Eq (isLE o) Bool.false) (Eq o gt) :=
  @Ordering.rec _
    (iff_of_false trueFalse ltNeGt)
    (iff_of_false trueFalse eqNeGt)
    (iff_of_true Omega.rfl Omega.rfl)

theorem isGE_eq_false : ∀ {o : Ordering}, Iff (Eq (isGE o) Bool.false) (Eq o lt) :=
  @Ordering.rec _
    (iff_of_true Omega.rfl Omega.rfl)
    (iff_of_false trueFalse eqNeLt)
    (iff_of_false trueFalse gtNeLt)

theorem isNe_eq_false : ∀ {o : Ordering}, Iff (Eq (isNe o) Bool.false) (Eq o «eq») :=
  @Ordering.rec _
    (iff_of_false trueFalse ltNeEq)
    (iff_of_true Omega.rfl Omega.rfl)
    (iff_of_false trueFalse gtNeEq)

theorem isEq_eq_false : ∀ {o : Ordering}, Iff (Eq (isEq o) Bool.false) (Not (Eq o «eq»)) :=
  @Ordering.rec _
    (iff_of_true Omega.rfl ltNeEq)
    (iff_of_false trueFalse (fun h => h Omega.rfl))
    (iff_of_true Omega.rfl gtNeEq)

theorem swap_eq_gt : ∀ {o : Ordering}, Iff (Eq (swap o) gt) (Eq o lt) :=
  @Ordering.rec _
    (iff_of_true Omega.rfl Omega.rfl)
    (iff_of_false eqNeGt eqNeLt)
    (iff_of_false ltNeGt gtNeLt)

theorem swap_eq_lt : ∀ {o : Ordering}, Iff (Eq (swap o) lt) (Eq o gt) :=
  @Ordering.rec _
    (iff_of_false gtNeLt ltNeGt)
    (iff_of_false eqNeLt eqNeGt)
    (iff_of_true Omega.rfl Omega.rfl)

theorem swap_eq_eq : ∀ {o : Ordering}, Iff (Eq (swap o) «eq») (Eq o «eq») :=
  @Ordering.rec _
    (iff_of_false gtNeEq ltNeEq)
    (iff_of_true Omega.rfl Omega.rfl)
    (iff_of_false ltNeEq gtNeEq)

theorem isLT_swap : ∀ {o : Ordering}, Eq (isLT (swap o)) (isGT o) :=
  @Ordering.rec _ Omega.rfl Omega.rfl Omega.rfl

theorem isLE_swap : ∀ {o : Ordering}, Eq (isLE (swap o)) (isGE o) :=
  @Ordering.rec _ Omega.rfl Omega.rfl Omega.rfl

theorem isEq_swap : ∀ {o : Ordering}, Eq (isEq (swap o)) (isEq o) :=
  @Ordering.rec _ Omega.rfl Omega.rfl Omega.rfl

theorem isNe_swap : ∀ {o : Ordering}, Eq (isNe (swap o)) (isNe o) :=
  @Ordering.rec _ Omega.rfl Omega.rfl Omega.rfl

theorem isGE_swap : ∀ {o : Ordering}, Eq (isGE (swap o)) (isLE o) :=
  @Ordering.rec _ Omega.rfl Omega.rfl Omega.rfl

theorem isGT_swap : ∀ {o : Ordering}, Eq (isGT (swap o)) (isLT o) :=
  @Ordering.rec _ Omega.rfl Omega.rfl Omega.rfl

theorem isLE_of_eq_lt : ∀ {o : Ordering}, Eq o lt → Eq (isLE o) Bool.true :=
  fun h => congrArg isLE h

theorem isLE_of_eq_eq : ∀ {o : Ordering}, Eq o «eq» → Eq (isLE o) Bool.true :=
  fun h => congrArg isLE h

theorem isGE_of_eq_gt : ∀ {o : Ordering}, Eq o gt → Eq (isGE o) Bool.true :=
  fun h => congrArg isGE h

theorem isGE_of_eq_eq : ∀ {o : Ordering}, Eq o «eq» → Eq (isGE o) Bool.true :=
  fun h => congrArg isGE h

theorem ne_eq_of_eq_lt : ∀ {o : Ordering}, Eq o lt → Ne o «eq» :=
  fun h he => ltNeEq (h.symm.trans he)

theorem ne_eq_of_eq_gt : ∀ {o : Ordering}, Eq o gt → Ne o «eq» :=
  fun h he => gtNeEq (h.symm.trans he)

theorem isLT_iff_eq_lt : ∀ {o : Ordering}, Iff (Eq (isLT o) Bool.true) (Eq o lt) :=
  @Ordering.rec _
    (iff_of_true Omega.rfl Omega.rfl)
    (iff_of_false falseTrue eqNeLt)
    (iff_of_false falseTrue gtNeLt)

theorem isGT_iff_eq_gt : ∀ {o : Ordering}, Iff (Eq (isGT o) Bool.true) (Eq o gt) :=
  @Ordering.rec _
    (iff_of_false falseTrue ltNeGt)
    (iff_of_false falseTrue eqNeGt)
    (iff_of_true Omega.rfl Omega.rfl)

theorem isEq_iff_eq_eq : ∀ {o : Ordering}, Iff (Eq (isEq o) Bool.true) (Eq o «eq») :=
  @Ordering.rec _
    (iff_of_false falseTrue ltNeEq)
    (iff_of_true Omega.rfl Omega.rfl)
    (iff_of_false falseTrue gtNeEq)

theorem isNe_iff_ne_eq : ∀ {o : Ordering}, Iff (Eq (isNe o) Bool.true) (Not (Eq o «eq»)) :=
  @Ordering.rec _
    (iff_of_true Omega.rfl ltNeEq)
    (iff_of_false falseTrue (fun h => h Omega.rfl))
    (iff_of_true Omega.rfl gtNeEq)

theorem isLE_iff_ne_gt : ∀ {o : Ordering}, Iff (Eq (isLE o) Bool.true) (Not (Eq o gt)) :=
  @Ordering.rec _
    (iff_of_true Omega.rfl ltNeGt)
    (iff_of_true Omega.rfl eqNeGt)
    (iff_of_false falseTrue (fun h => h Omega.rfl))

theorem isGE_iff_ne_lt : ∀ {o : Ordering}, Iff (Eq (isGE o) Bool.true) (Not (Eq o lt)) :=
  @Ordering.rec _
    (iff_of_false falseTrue (fun h => h Omega.rfl))
    (iff_of_true Omega.rfl eqNeLt)
    (iff_of_true Omega.rfl gtNeLt)

theorem isLE_iff_eq_lt_or_eq_eq : ∀ {o : Ordering}, Iff (Eq (isLE o) Bool.true) (Or (Eq o lt) (Eq o «eq»)) :=
  @Ordering.rec _
    (iff_of_true Omega.rfl (Or.inl Omega.rfl))
    (iff_of_true Omega.rfl (Or.inr Omega.rfl))
    (iff_of_false falseTrue (fun h => h.elim gtNeLt gtNeEq))

theorem isGE_iff_eq_gt_or_eq_eq : ∀ {o : Ordering}, Iff (Eq (isGE o) Bool.true) (Or (Eq o gt) (Eq o «eq»)) :=
  @Ordering.rec _
    (iff_of_false falseTrue (fun h => h.elim ltNeGt ltNeEq))
    (iff_of_true Omega.rfl (Or.inr Omega.rfl))
    (iff_of_true Omega.rfl (Or.inl Omega.rfl))

theorem isLE_eq_isLT_or_isEq : ∀ {o : Ordering}, Eq (isLE o) (Bool.or (isLT o) (isEq o)) :=
  @Ordering.rec _ Omega.rfl Omega.rfl Omega.rfl

theorem isGE_eq_isGT_or_isEq : ∀ {o : Ordering}, Eq (isGE o) (Bool.or (isGT o) (isEq o)) :=
  @Ordering.rec _ Omega.rfl Omega.rfl Omega.rfl

theorem isNe_eq_isLT_or_isGT : ∀ {o : Ordering}, Eq (isNe o) (Bool.or (isLT o) (isGT o)) :=
  @Ordering.rec _ Omega.rfl Omega.rfl Omega.rfl

theorem not_isLT_eq_isGE : ∀ {o : Ordering}, Eq (Bool.not (isLT o)) (isGE o) :=
  @Ordering.rec _ Omega.rfl Omega.rfl Omega.rfl

theorem not_isLE_eq_isGT : ∀ {o : Ordering}, Eq (Bool.not (isLE o)) (isGT o) :=
  @Ordering.rec _ Omega.rfl Omega.rfl Omega.rfl

theorem not_isGT_eq_isLE : ∀ {o : Ordering}, Eq (Bool.not (isGT o)) (isLE o) :=
  @Ordering.rec _ Omega.rfl Omega.rfl Omega.rfl

theorem not_isGE_eq_isLT : ∀ {o : Ordering}, Eq (Bool.not (isGE o)) (isLT o) :=
  @Ordering.rec _ Omega.rfl Omega.rfl Omega.rfl

theorem not_isNe_eq_isEq : ∀ {o : Ordering}, Eq (Bool.not (isNe o)) (isEq o) :=
  @Ordering.rec _ Omega.rfl Omega.rfl Omega.rfl

theorem not_isEq_eq_isNe : ∀ {o : Ordering}, Eq (Bool.not (isEq o)) (isNe o) :=
  @Ordering.rec _ Omega.rfl Omega.rfl Omega.rfl

theorem ne_lt_iff_isGE : ∀ {o : Ordering}, Iff (Not (Eq o lt)) (Eq (isGE o) Bool.true) :=
  isGE_iff_ne_lt.symm

theorem ne_gt_iff_isLE : ∀ {o : Ordering}, Iff (Not (Eq o gt)) (Eq (isLE o) Bool.true) :=
  isLE_iff_ne_gt.symm

theorem swap_swap : ∀ {o : Ordering}, Eq (swap (swap o)) o :=
  @Ordering.rec _ Omega.rfl Omega.rfl Omega.rfl

theorem swap_inj : ∀ {o₁ o₂ : Ordering}, Iff (Eq (swap o₁) (swap o₂)) (Eq o₁ o₂) :=
  fun {a b} => Iff.intro
    (fun h => (swap_swap (o := a)).symm.trans ((congrArg swap h).trans (swap_swap (o := b))))
    (congrArg swap)

theorem swap_then : ∀ (o₁ o₂ : Ordering), Eq (swap («then» o₁ o₂)) («then» (swap o₁) (swap o₂)) :=
  @Ordering.rec _ (fun _ => Omega.rfl) (fun _ => Omega.rfl) (fun _ => Omega.rfl)

theorem then_eq_lt : ∀ {o₁ o₂ : Ordering},
  Iff (Eq («then» o₁ o₂) lt) (Or (Eq o₁ lt) (And (Eq o₁ «eq») (Eq o₂ lt))) :=
  @Ordering.rec _
    (fun {_} => iff_of_true Omega.rfl (Or.inl Omega.rfl))
    (fun {_} => Iff.intro (fun h => Or.inr (And.intro Omega.rfl h))
      (fun h => h.elim (fun hl => False.elim (eqNeLt hl)) And.right))
    (fun {_} => iff_of_false gtNeLt (fun h => h.elim gtNeLt (fun he => gtNeEq he.left)))

theorem then_eq_gt : ∀ {o₁ o₂ : Ordering},
  Iff (Eq («then» o₁ o₂) gt) (Or (Eq o₁ gt) (And (Eq o₁ «eq») (Eq o₂ gt))) :=
  @Ordering.rec _
    (fun {_} => iff_of_false ltNeGt (fun h => h.elim ltNeGt (fun he => ltNeEq he.left)))
    (fun {_} => Iff.intro (fun h => Or.inr (And.intro Omega.rfl h))
      (fun h => h.elim (fun hg => False.elim (eqNeGt hg)) And.right))
    (fun {_} => iff_of_true Omega.rfl (Or.inl Omega.rfl))

theorem then_eq_eq : ∀ {o₁ o₂ : Ordering}, Iff (Eq («then» o₁ o₂) «eq») (And (Eq o₁ «eq») (Eq o₂ «eq»)) :=
  @Ordering.rec _
    (fun {_} => iff_of_false ltNeEq (fun h => ltNeEq h.left))
    (fun {_} => Iff.intro (And.intro Omega.rfl) And.right)
    (fun {_} => iff_of_false gtNeEq (fun h => gtNeEq h.left))

theorem isLT_then : ∀ {o₁ o₂ : Ordering},
  Eq (isLT («then» o₁ o₂)) (Bool.or (isLT o₁) (Bool.and (isEq o₁) (isLT o₂))) :=
  @Ordering.rec _ (fun {_} => Omega.rfl) (fun {_} => Omega.rfl) (fun {_} => Omega.rfl)

theorem isEq_then : ∀ {o₁ o₂ : Ordering}, Eq (isEq («then» o₁ o₂)) (Bool.and (isEq o₁) (isEq o₂)) :=
  @Ordering.rec _ (fun {_} => Omega.rfl) (fun {_} => Omega.rfl) (fun {_} => Omega.rfl)

theorem isNe_then : ∀ {o₁ o₂ : Ordering}, Eq (isNe («then» o₁ o₂)) (Bool.or (isNe o₁) (isNe o₂)) :=
  @Ordering.rec _ (fun {_} => Omega.rfl) (fun {_} => Omega.rfl) (fun {_} => Omega.rfl)

theorem isGT_then : ∀ {o₁ o₂ : Ordering},
  Eq (isGT («then» o₁ o₂)) (Bool.or (isGT o₁) (Bool.and (isEq o₁) (isGT o₂))) :=
  @Ordering.rec _ (fun {_} => Omega.rfl) (fun {_} => Omega.rfl) (fun {_} => Omega.rfl)

theorem lt_then : ∀ {o : Ordering}, Eq («then» lt o) lt :=
  fun {_} => Omega.rfl

theorem gt_then : ∀ {o : Ordering}, Eq («then» gt o) gt :=
  fun {_} => Omega.rfl

theorem eq_then : ∀ {o : Ordering}, Eq («then» «eq» o) o :=
  fun {_} => Omega.rfl

theorem then_eq : ∀ {o : Ordering}, Eq («then» o «eq») o :=
  @Ordering.rec _ Omega.rfl Omega.rfl Omega.rfl

theorem then_self : ∀ {o : Ordering}, Eq («then» o o) o :=
  @Ordering.rec _ Omega.rfl Omega.rfl Omega.rfl

theorem then_assoc : ∀ (o₁ o₂ o₃ : Ordering), Eq («then» («then» o₁ o₂) o₃) («then» o₁ («then» o₂ o₃)) :=
  @Ordering.rec _ (fun _ _ => Omega.rfl) (fun _ _ => Omega.rfl) (fun _ _ => Omega.rfl)

theorem isLE_then_iff_or : ∀ {o₁ o₂ : Ordering},
  Iff (Eq (isLE («then» o₁ o₂)) Bool.true)
    (Or (Eq o₁ lt) (And (Eq o₁ «eq») (Eq (isLE o₂) Bool.true))) :=
  @Ordering.rec _
    (fun {_} => iff_of_true Omega.rfl (Or.inl Omega.rfl))
    (fun {_} => Iff.intro (fun h => Or.inr (And.intro Omega.rfl h))
      (fun h => h.elim (fun hl => False.elim (eqNeLt hl)) And.right))
    (fun {_} => iff_of_false falseTrue (fun h => h.elim gtNeLt (fun he => gtNeEq he.left)))

theorem isLE_then_iff_and : ∀ {o₁ o₂ : Ordering},
  Iff (Eq (isLE («then» o₁ o₂)) Bool.true)
    (And (Eq (isLE o₁) Bool.true) (Or (Eq o₁ lt) (Eq (isLE o₂) Bool.true))) :=
  @Ordering.rec _
    (fun {_} => iff_of_true Omega.rfl (And.intro Omega.rfl (Or.inl Omega.rfl)))
    (fun {_} => Iff.intro (fun h => And.intro Omega.rfl (Or.inr h))
      (fun h => h.right.resolve_left eqNeLt))
    (fun {_} => iff_of_false falseTrue (fun h => falseTrue h.left))

theorem isLE_left_of_isLE_then : ∀ {o₁ o₂ : Ordering}, Eq (isLE («then» o₁ o₂)) Bool.true → Eq (isLE o₁) Bool.true :=
  fun h => (isLE_then_iff_and.mp h).left

theorem isGE_left_of_isGE_then : ∀ {o₁ o₂ : Ordering}, Eq (isGE («then» o₁ o₂)) Bool.true → Eq (isGE o₁) Bool.true :=
  @Ordering.rec _ (fun {_} => id) (fun {_} _ => Omega.rfl) (fun {_} _ => Omega.rfl)

theorem isLE_and_isGE_eq : ∀ {o : Ordering}, Eq (Bool.and (isLE o) (isGE o)) (isEq o) :=
  @Ordering.rec _ Omega.rfl Omega.rfl Omega.rfl

theorem then'_eq_then : ∀ (a b : Ordering), Eq (then' a b) («then» a b) :=
  fun a => Ordering.rec (motive := fun o => ∀ b, Eq (then' o b) («then» o b))
    (fun _ => Omega.rfl) (fun _ => Omega.rfl) (fun _ => Omega.rfl) a

end Ordering

def compareLex {α : Sort u} {β : Sort v} (cmp₁ cmp₂ : α → β → Ordering) (a : α) (b : β) : Ordering :=
  (cmp₁ a b).then (cmp₂ a b)

theorem compareLex_eq_eq {α : Sort u} {cmp₁ cmp₂ : α → α → Ordering} {a b : α} :
    Iff (Eq (compareLex cmp₁ cmp₂ a b) Ordering.eq)
      (And (Eq (cmp₁ a b) Ordering.eq) (Eq (cmp₂ a b) Ordering.eq)) :=
  Ordering.then_eq_eq

attribute [irreducible] Ordering.then Ordering.isEq Ordering.isNe Ordering.isLE Ordering.isLT Ordering.isGT Ordering.isGE

end Omega

port_proof compareLex.eq_1 by_reflexivity
port_proof Ordering.then.eq_1 by_reflexivity
port_proof Ordering.then'.eq_1 by_reflexivity
