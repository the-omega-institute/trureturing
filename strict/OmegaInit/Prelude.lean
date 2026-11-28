/-
Copyright (c) 2026 The Omega Institute. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
prelude

noncomputable section

@[expose] public section

set_option linter.unusedVariables.funArgs false in
@[reducible] def optParam (α : Sort u) (default : α) : Sort u := α

@[reducible] def outParam (α : Sort u) : Sort u := α

@[reducible] def semiOutParam (α : Sort u) : Sort u := α

port_compiler_markers
port_kernel_naturals

set_option genCtorIdx false

port_inductive Option
port_inductive List
port_inductive Prod
port_definition Prod.fst with_native_code
port_definition Prod.snd with_native_code

namespace Omega

theorem congrArg {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β) (h : Eq a₁ a₂) : Eq (f a₁) (f a₂) :=
  Eq.rec (motive := fun a₂ _ => Eq (f a₁) (f a₂)) rfl h

inductive True : Prop where
  | intro


end Omega


namespace Omega

def False.elim {C : Sort u} (h : False) : C := False.casesOn (fun _ => C) h


end Omega

port_prop_record And

namespace Omega

inductive Or (a b : Prop) : Prop where
  | inl (h : a) : Or a b
  | inr (h : b) : Or a b


theorem Or.elim {a b c : Prop} (h : Or a b) (left : a → c) (right : b → c) : c :=
  Or.rec (motive := fun _ => c) left right h


end Omega

port_inductive Nat.le

namespace Omega
namespace Nat

protected def lt (n m : Nat) : Prop := Nat.le (succ n) m

theorem zero_le (n : Nat) : Nat.le zero n :=
  Nat.rec (motive := fun k => Nat.le zero k) Nat.le.refl (fun _ h => Nat.le.step h) n

theorem succ_le_succ {n m : Nat} : Nat.le n m → Nat.le (succ n) (succ m) := fun h =>
  Nat.le.rec (motive := fun k _ => Nat.le (succ n) (succ k)) Nat.le.refl
    (fun _ ih => Nat.le.step ih) h

private theorem weakenLeft {n m : Nat} (h : Nat.le (succ n) m) : Nat.le n m :=
  Nat.le.rec (motive := fun k _ => Nat.le n k) (Nat.le.step Nat.le.refl)
    (fun _ ih => Nat.le.step ih) h

theorem le_of_succ_le_succ {n m : Nat} : Nat.le (succ n) (succ m) → Nat.le n m := fun h =>
  Nat.le.rec (n := succ n) (motive := fun k _ => Nat.le n (pred k)) Nat.le.refl (fun evidence _ => weakenLeft evidence) h

theorem not_succ_le_zero (n : Nat) : Not (Nat.le (succ n) zero) := fun h =>
  Nat.le.rec (n := succ n) (motive := fun k _ => Nat.casesOn (motive := fun _ => Prop) k False (fun _ => True))
    True.intro (fun _ _ => True.intro) h

protected theorem le_refl (n : Nat) : Nat.le n n := Nat.le.refl

protected theorem le_trans {n m k : Nat} : Nat.le n m → Nat.le m k → Nat.le n k := fun h g =>
  Nat.le.rec (motive := fun k _ => Nat.le n k) h (fun _ ih => Nat.le.step ih) g

protected theorem le_antisymm {n m : Nat} (h₁ : Nat.le n m) (h₂ : Nat.le m n) : Eq n m :=
  (Nat.rec (motive := fun n => ∀ m, Nat.le n m → Nat.le m n → Eq n m)
    (fun m => Nat.rec (motive := fun m => Nat.le zero m → Nat.le m zero → Eq zero m)
      (fun _ _ => rfl) (fun k _ _ h => False.elim (not_succ_le_zero k h)) m)
    (fun n smaller m => Nat.rec (motive := fun m => Nat.le (succ n) m → Nat.le m (succ n) → Eq (succ n) m)
      (fun h _ => False.elim (not_succ_le_zero n h))
      (fun m _ h g => congrArg succ (smaller m (le_of_succ_le_succ h) (le_of_succ_le_succ g))) m) n) m h₁ h₂

theorem succ_sub_succ_eq_sub (n m : Nat) : Eq (Nat.sub (succ n) (succ m)) (Nat.sub n m) :=
  Nat.rec (motive := fun i => Eq (pred (Nat.sub (succ n) i)) (Nat.sub n i))
    rfl (fun _ h => congrArg pred h) m

end Nat

inductive Empty : Type

set_option bootstrap.inductiveCheckResultingUniverse false in
inductive PEmpty : Sort u where

set_option linter.defProp false in
@[match_pattern] protected def HEq.rfl {α : Sort u} {a : α} : HEq a a := HEq.refl a


theorem id_eq (a : α) : Eq (id a) a := Omega.rfl

def Function.comp {α : Sort u} {β : Sort v} {δ : Sort w}
    (f : β → δ) (g : α → β) : α → δ := fun x => f (g x)

def Function.const {α : Sort u} (β : Sort v) (a : α) : β → α := fun _ => a

end Omega


namespace Omega

theorem congrFun {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}
    (h : Eq f g) (a : α) : Eq (f a) (g a) := congrArg (fun f : (x : α) → β x => f a) h

theorem congrFun' {α : Sort u} {β : Sort v} {f g : α → β}
    (h : Eq f g) (a : α) : Eq (f a) (g a) := congrFun h a

theorem congr {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}
    (h₁ : Eq f₁ f₂) (h₂ : Eq a₁ a₂) : Eq (f₁ a₁) (f₂ a₂) :=
  (congrFun h₁ a₁).trans (congrArg f₂ h₂)

theorem Or.intro_left (b : Prop) (h : a) : Or a b := Or.inl h

theorem Or.intro_right (a : Prop) (h : b) : Or a b := Or.inr h

theorem Or.resolve_left (h : Or a b) (na : Not a) : b := h.elim (fun ha => absurd ha na) id

theorem Or.resolve_right (h : Or a b) (nb : Not b) : a := h.elim id (fun hb => absurd hb nb)

theorem Or.neg_resolve_left (h : Or (Not a) b) (ha : a) : b := h.elim (absurd ha) id

theorem Or.neg_resolve_right (h : Or a (Not b)) (nb : b) : a := h.elim id (absurd nb)

class inductive Nonempty (α : Sort u) : Prop where
  | intro (val : α) : Nonempty α


protected theorem Nonempty.elim {α : Sort u} {p : Prop} (h₁ : Nonempty α) (h₂ : α → p) : p :=
  Nonempty.rec (motive := fun _ => p) h₂ h₁

set_option checkBinderAnnotations false in
abbrev inferInstance {α : Sort u} [i : α] : α := i

set_option checkBinderAnnotations false in
abbrev «inferInstanceAs» (α : Sort u) [i : α] : α := i

set_option linter.unusedVariables.funArgs false in
@[reducible] def namedPattern {α : Sort u} (x a : α) (h : Eq x a) : α := a


end Omega


namespace Omega




end Omega


namespace Omega


protected def Bool.dcond {α : Sort u} (c : Bool)
    (x : Eq c true → α) (y : Eq c false → α) : α :=
  Bool.rec (motive := fun b => (Eq b true → α) → (Eq b false → α) → α)
    (fun _ no => no Omega.rfl) (fun yes _ => yes Omega.rfl) c x y

def Bool.or (x y : Bool) : Bool := Bool.casesOn x y true

def Bool.and (x y : Bool) : Bool := Bool.casesOn x false y

def Bool.not (x : Bool) : Bool := Bool.casesOn x true false

def Bool.Internal.or (x y : Bool) : Bool := Bool.or x y

def Bool.Internal.and (x y : Bool) : Bool := Bool.and x y

def Bool.Internal.not : Bool → Bool := Bool.not

theorem Bool.and_eq_internalAnd : Eq Bool.and Bool.Internal.and := Omega.rfl

theorem Bool.or_eq_internalOr : Eq Bool.or Bool.Internal.or := Omega.rfl

theorem Bool.not_eq_internalNot : Eq Bool.not Bool.Internal.not := Omega.rfl

open Bool (or and not)

def Bool.beq (a b : Bool) : Bool := Bool.casesOn b (Bool.not a) a

theorem Bool.eq_false_of_ne_true : {b : Bool} → Not (Eq b true) → Eq b false :=
  fun {b} => Bool.rec (motive := fun b => Not (Eq b true) → Eq b false)
    (fun _ => Omega.rfl) (fun h => False.elim (h Omega.rfl)) b

theorem Bool.eq_true_of_ne_false : {b : Bool} → Not (Eq b false) → Eq b true :=
  fun {b} => Bool.rec (motive := fun b => Not (Eq b false) → Eq b true)
    (fun h => False.elim (h Omega.rfl)) (fun _ => Omega.rfl) b

theorem Bool.ne_false_of_eq_true : {b : Bool} → Eq b true → Not (Eq b false) :=
  fun h g => Eq.subst (motive := Bool.rec (motive := fun _ => Prop) True False) (g.symm.trans h) True.intro

theorem Bool.ne_true_of_eq_false : {b : Bool} → Eq b false → Not (Eq b true) :=
  fun h g => Bool.ne_false_of_eq_true g h

end Omega

namespace Omega

/-- A computation with access to a read-only environment. -/
def ReaderT (ρ : Type u) (m : Type u → Type v) (α : Type u) : Type (max u v) := ρ → m α

def ReaderT.mk {ρ : Type u} {m : Type u → Type v} {α : Type u} (x : ρ → m α) : ReaderT ρ m α := x

def ReaderT.run {ρ : Type u} {m : Type u → Type v} {α : Type u} (x : ReaderT ρ m α) (r : ρ) : m α :=
  x r

protected def ReaderT.adapt {ρ : Type u} {m : Type u → Type v} {ρ' α : Type u}
    (f : ρ' → ρ) : ReaderT ρ m α → ReaderT ρ' m α := fun x r => x (f r)

end Omega

namespace Omega.Option

protected def map {α : Type u} {β : Type v} (f : α → β) : Option α → Option β :=
  fun x => Option.casesOn (motive := fun _ => Option β) x none (fun a => some (f a))

def getD {α : Type u} (opt : Option α) (dflt : α) : α :=
  Option.casesOn (motive := fun _ => α) opt dflt (fun a => a)

end Omega.Option

namespace Omega.Nat

protected theorem lt_irrefl (n : Nat) : Not (Nat.lt n n) :=
  Nat.rec (motive := fun k => Not (Nat.lt k k)) (not_succ_le_zero zero)
    (fun _ ih h => ih (le_of_succ_le_succ h)) n

theorem le_of_ble_eq_true {n m : Nat} (h : Eq (Nat.ble n m) Bool.true) : Nat.le n m :=
  Nat.rec (motive := fun n => ∀ m, Eq (Nat.ble n m) Bool.true → Nat.le n m)
    (fun m _ => zero_le m)
    (fun n ih m => Nat.rec (motive := fun m => Eq (Nat.ble (succ n) m) Bool.true → Nat.le (succ n) m)
      (fun e => False.elim (Bool.ne_true_of_eq_false Omega.rfl e))
      (fun k _ e => succ_le_succ (ih k e)) m) n m h

theorem ble_eq_true_of_le {n m : Nat} (h : Nat.le n m) : Eq (Nat.ble n m) Bool.true :=
  Nat.rec (motive := fun n => ∀ m, Nat.le n m → Eq (Nat.ble n m) Bool.true)
    (fun _ _ => Omega.rfl)
    (fun n ih m => Nat.rec (motive := fun m => Nat.le (succ n) m → Eq (Nat.ble (succ n) m) Bool.true)
      (fun e => False.elim (not_succ_le_zero n e)) (fun k _ e => ih k (le_of_succ_le_succ e)) m) n m h

/-- Subtract a positive divisor at most once per remaining fuel unit. -/
@[extern "lean_nat_div", no_expose] protected def _root_.Nat.div (x y : @& Nat) : Nat :=
  Nat.rec zero (fun d _ =>
    Nat.rec (motive := fun _ => Nat → Nat) (fun _ => zero)
      (fun _ previous n => Bool.rec zero (succ (previous (Nat.sub n (succ d)))) (Nat.ble (succ d) n))
      (succ x) x) y

@[extern "lean_nat_mod", no_expose] protected def _root_.Nat.mod : @& Nat → @& Nat → Nat :=
  fun x y => Nat.rec zero (fun k _ =>
    Nat.rec (succ k) (fun d _ =>
      Nat.rec (motive := fun _ => Nat → Nat) (fun _ => zero)
        (fun _ previous n => Bool.rec n (previous (Nat.sub n (succ d))) (Nat.ble (succ d) n))
        (succ (succ k)) (succ k)) y) x

export _root_.Nat (div mod)

private theorem lt_of_ble_false (a : Nat) : ∀ b, Eq (Nat.ble b a) Bool.false → Nat.lt a b :=
  Nat.rec (motive := fun a => ∀ b, Eq (Nat.ble b a) Bool.false → Nat.lt a b)
    (fun b => Nat.rec (motive := fun b => Eq (Nat.ble b zero) Bool.false → Nat.lt zero b)
      (fun h => False.elim (Bool.ne_false_of_eq_true Omega.rfl h))
      (fun k _ _ => Nat.succ_le_succ (Nat.zero_le k)) b)
    (fun a smaller b => Nat.rec (motive := fun b => Eq (Nat.ble b (succ a)) Bool.false → Nat.lt (succ a) b)
      (fun h => False.elim (Bool.ne_false_of_eq_true Omega.rfl h))
      (fun k _ h => Nat.succ_le_succ (smaller k h)) b) a

private def remainder (d fuel n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun _ => zero)
    (fun _ previous n => Bool.rec n (previous (Nat.sub n (succ d))) (Nat.ble (succ d) n)) fuel n

private theorem remainder_lt (d fuel : Nat) : ∀ x, Nat.lt (remainder d fuel x) (succ d) :=
  Nat.rec (motive := fun fuel => ∀ x, Nat.lt (remainder d fuel x) (succ d))
    (fun _ => Nat.succ_le_succ (Nat.zero_le d))
    (fun fuel smaller x =>
      let next := remainder d fuel (Nat.sub x (succ d))
      let branch : ∀ bit : Bool, Eq (Nat.ble (succ d) x) bit →
          Nat.lt (@Bool.rec (fun _ => Nat) x next bit) (succ d) :=
        Bool.rec (motive := fun bit => Eq (Nat.ble (succ d) x) bit → Nat.lt (@Bool.rec (fun _ => Nat) x next bit) (succ d))
          (lt_of_ble_false x (succ d)) (fun _ => smaller _)
      branch (Nat.ble (succ d) x) Omega.rfl) fuel

theorem mod_lt (x : Nat) {y : Nat} (hy : Nat.lt zero y) : Nat.lt (Nat.mod x y) y :=
  (Nat.rec (motive := fun x => ∀ y, Nat.lt zero y → Nat.lt (Nat.mod x y) y)
    (fun _ h => h)
    (fun k _ y => Nat.rec (motive := fun y => Nat.lt zero y → Nat.lt (Nat.mod (succ k) y) y)
      (fun h => False.elim (Nat.not_succ_le_zero zero h))
      (fun d _ _ => remainder_lt d (succ (succ k)) (succ k)) y) x) y hy

attribute [irreducible] Nat.div Nat.mod

end Omega.Nat


port_definition List.below
port_definition List.brecOn.go
port_definition List.brecOn

namespace Omega.List

@[instance_reducible] def length {α : Type u} : List α → Nat := fun xs =>
  List.brecOn (motive := fun _ : List α => Nat) xs (fun ys below =>
    List.casesOn (motive := fun ys => List.below (motive := fun _ : List α => Nat) ys → Nat)
      ys (fun _ => Nat.zero) (fun _ _ prior => Nat.succ prior.fst) below)

@[implicit_reducible] protected def append {α : Type u} : (xs ys : List α) → List α := fun xs ys =>
  List.brecOn (motive := fun _ : List α => List α → List α) xs (fun l prior ys =>
    List.casesOn (motive := fun l =>
        List.below (motive := fun _ : List α => List α → List α) l → List α)
      l (fun _ => ys) (fun a _ prev => cons a (prev.fst ys)) prior) ys

@[implicit_reducible] def concat {α : Type u} : List α → α → List α := fun l b =>
  List.brecOn (motive := fun _ : List α => α → List α) l (fun xs below b =>
    List.casesOn (motive := fun xs => List.below (motive := fun _ : List α => α → List α) xs → List α)
      xs (fun _ => cons b nil) (fun a _ prior => cons a (prior.fst b)) below) b

@[implicit_reducible] def map {α : Type u} {β : Type v} (f : α → β) (l : List α) : List β :=
  List.brecOn (motive := fun _ : List α => List β) l (fun xs below =>
    List.casesOn (motive := fun xs => List.below (motive := fun _ : List α => List β) xs → List β)
      xs (fun _ => nil) (fun a _ prior => cons (f a) prior.fst) below)

def foldl {α : Type u} {β : Type v} (f : α → β → α) : (init : α) → List β → α := fun init l =>
  List.brecOn (motive := fun _ : List β => α → α) l (fun xs below acc =>
    List.casesOn (motive := fun xs => List.below (motive := fun _ : List β => α → α) xs → α)
      xs (fun _ => acc) (fun b _ prior => prior.fst (f acc b)) below) init

def lengthTRAux {α : Type u} : List α → Nat → Nat := fun xs n =>
  List.brecOn (motive := fun _ : List α => Nat → Nat) xs (fun ys below acc =>
    List.casesOn (motive := fun ys => List.below (motive := fun _ : List α => Nat → Nat) ys → Nat)
      ys (fun _ => acc) (fun _ _ prior => prior.fst (Nat.succ acc)) below) n

@[no_expose] def lengthTR {α : Type u} (as : List α) : Nat := length as
attribute [irreducible] lengthTR

@[implicit_reducible] def flatten {α : Type u} : List (List α) → List α := fun l =>
  List.brecOn (motive := fun _ : List (List α) => List α) l (fun xs below =>
    List.casesOn (motive := fun xs => List.below (motive := fun _ : List (List α) => List α) xs → List α)
      xs (fun _ => nil) (fun head _ prior => List.append head prior.fst) below)

end Omega.List

port_definition List.concat.match_1 with_native_code
port_structural_code List.concat on_arg 2

port_definition List.flatMap

port_inductive LE
port_definition LE.le
port_inductive LT
port_definition LT.lt

port_definition Decidable.isFalse
port_definition Decidable.isTrue
port_definition ite


namespace Omega

theorem instDecidableAnd._proof_1 {p q : Prop} [dp : Decidable p] [dq : Decidable q] :
    Bool.Reflects (Bool.and (@Decidable.decide p dp) (@Decidable.decide q dq)) (And p q) :=
  have reflect : ∀ a b : Bool, Bool.Reflects a p → Bool.Reflects b q → Bool.Reflects (Bool.and a b) (And p q) :=
    fun a => Bool.casesOn (motive := fun a => ∀ b : Bool, Bool.Reflects a p → Bool.Reflects b q →
        Bool.Reflects (Bool.and a b) (And p q)) a
      (fun _ hp _ both => hp (And.left both))
      (fun b => Bool.casesOn (motive := fun b => p → Bool.Reflects b q → Bool.Reflects b (And p q))
        b (fun _ hq both => hq (And.right both)) And.intro)
  reflect _ _ (@Decidable.reflects_decide p dp) (@Decidable.reflects_decide q dq)

instance instDecidableAnd {p q : Prop} [dp : Decidable p] [dq : Decidable q] : Decidable (And p q) :=
  Decidable.intro (Bool.and (@Decidable.decide p dp) (@Decidable.decide q dq)) instDecidableAnd._proof_1

attribute [instance] _root_.instOfNatNat _root_.instHAdd _root_.instAddNat

instance instLENat : LE Nat := LE.mk Nat.le
instance instLTNat : LT Nat := LT.mk Nat.lt

instance Nat.decLe (n m : Nat) : Decidable (@LE.le Nat instLENat n m) :=
  Decidable.intro (Nat.ble n m)
    (Bool.casesOn (motive := fun b => Eq (Nat.ble n m) b → Bool.Reflects b (Nat.le n m)) (Nat.ble n m)
      (fun e h => Bool.ne_false_of_eq_true (Nat.ble_eq_true_of_le h) e) Nat.le_of_ble_eq_true Omega.rfl)

instance Nat.decLt (n m : Nat) : Decidable (@LT.lt Nat instLTNat n m) := Nat.decLe (Nat.succ n) m

end Omega

port_inductive Array
port_definition Array.toList
port_definition List.toArray
port_definition Array.push with_native_code
port_definition Array.emptyWithCapacity with_native_code
port_definition Array.mkEmpty

namespace Omega
def Array.empty {α : Type u} : Array α := Array.emptyWithCapacity Nat.zero
end Omega

port_inductive Append
port_definition Append.append
port_inductive HAppend
port_definition HAppend.hAppend
port_definition instHAppendOfAppend

port_inductive Sub
port_definition Sub.sub
port_inductive HSub
port_definition HSub.hSub
port_definition instHSub
port_definition instSubNat

end
end

-- Lean's pattern elaborator uses these root names for patterns, cases and argument-free branches.

port_native_records Mul, Div, Mod, Pow, NatPow, HomogeneousPow, SMul
port_native_records HMul, HDiv, HMod, HPow, HSMul
port_native_records OrElse, AndThen, AndOp, XorOp, OrOp, Complement, ShiftLeft, ShiftRight
port_native_records HOrElse, HAndThen, HAnd, HXor, HOr, HShiftLeft, HShiftRight

port_definition instHMul with_native_code
port_definition instHDiv with_native_code
port_definition instHMod with_native_code
port_definition instHPow with_native_code
port_definition instHSMul with_native_code
port_definition instPowNat with_native_code
port_definition instHOrElseOfOrElse with_native_code
port_definition instHAndThenOfAndThen with_native_code
port_definition instHAndOfAndOp with_native_code
port_definition instHXorOfXorOp with_native_code
port_definition instHOrOfOrOp with_native_code
port_definition instHShiftLeftOfShiftLeft with_native_code
port_definition instHShiftRightOfShiftRight with_native_code

port_native_records Inhabited, PLift, ULift, MProd
port_native_records Bind, Pure, Functor, Seq, SeqLeft, SeqRight
port_native_records MonadLift, MonadLiftT, MonadEval, MonadEvalT, MonadFunctor, MonadFunctorT
port_native_records MonadReader, MonadReaderOf, MonadWithReader, MonadWithReaderOf
port_native_records MonadState, MonadStateOf, MonadExcept, MonadExceptOf
port_inductive Except
port_inductive EStateM.Result
port_definition EStateM
port_native_records EStateM.Backtrackable
port_definition instInhabitedSort with_native_code
port_definition instInhabitedForall with_native_code
port_definition instInhabitedBool.default with_native_code
port_definition instInhabitedBool with_native_code
port_definition instInhabitedNat with_native_code
port_definition instInhabitedOption with_native_code
port_definition instInhabitedList with_native_code
port_definition instInhabitedULift with_native_code
port_definition instInhabitedReaderT with_native_code
port_definition instInhabitedExcept with_native_code
port_definition instMonadLiftT with_native_code
port_definition instMonadLiftTOfMonadLift with_native_code
port_definition instMonadEvalOfMonadLift with_native_code
port_definition instMonadEvalT with_native_code
port_definition instMonadEvalTOfMonadEval with_native_code
port_definition instMonadFunctorTOfMonadFunctor with_native_code
port_definition monadFunctorRefl with_native_code
port_definition throwThe with_native_code
port_definition tryCatchThe with_native_code
port_definition instMonadExceptOfMonadExceptOf with_native_code
port_definition readThe with_native_code
port_definition instMonadReaderOfMonadReaderOf with_native_code
port_definition liftM with_native_code
port_definition instMonadReaderOfOfMonadLift with_native_code
port_definition withTheReader with_native_code
port_definition instMonadWithReaderOfMonadWithReaderOf with_native_code
port_definition instMonadWithReaderOfOfMonadFunctor with_native_code
port_definition instMonadWithReaderOfReaderT with_native_code
port_definition getThe with_native_code
port_definition instMonadStateOfMonadStateOf with_native_code
port_definition instMonadStateOfOfMonadLift with_native_code
port_definition ReaderT.instMonadLift with_native_code
port_definition ReaderT.instMonadExceptOf with_native_code
port_definition ReaderT.instMonadFunctor with_native_code
port_definition EStateM.pure with_native_code
port_definition EStateM.set with_native_code
port_definition EStateM.get with_native_code
port_definition EStateM.modifyGet.match_1 with_native_code
port_definition EStateM.modifyGet with_native_code
port_definition EStateM.throw with_native_code
port_definition EStateM.run with_native_code
port_definition EStateM.dummyRestore with_native_code
port_definition EStateM.dummySave with_native_code
port_definition EStateM.nonBacktrackable with_native_code
port_definition EStateM.instInhabitedResult with_native_code
port_definition EStateM.instInhabited with_native_code
port_definition EStateM.instMonadStateOf with_native_code

port_native_records Applicative, Monad

port_definition instInhabitedForallOfMonad with_native_code
port_definition instInhabitedOfMonad with_native_code
port_definition ReaderT.read with_native_code
port_definition ReaderT.pure with_native_code
port_definition ReaderT.bind with_native_code
port_definition ReaderT.instFunctorOfMonad with_native_code
port_definition ReaderT.instApplicativeOfMonad with_native_code
port_definition ReaderT.instMonad with_native_code
port_definition instMonadReaderOfReaderTOfMonad with_native_code
port_definition EStateM.adaptExcept.match_1 with_native_code
port_definition EStateM.adaptExcept with_native_code
port_definition EStateM.bind.match_1 with_native_code
port_definition EStateM.bind with_native_code
port_definition EStateM.map with_native_code
port_definition EStateM.tryCatch.match_1 with_native_code
port_definition EStateM.tryCatch with_native_code
port_definition EStateM.orElse with_native_code
port_definition EStateM.seqRight with_native_code
port_definition EStateM.run' with_native_code
port_definition EStateM.instMonad with_native_code
port_definition EStateM.instMonadExceptOfOfBacktrackable with_native_code
port_definition EStateM.instOrElseOfBacktrackable with_native_code
port_definition MonadExcept.ofExcept.match_1 with_native_code
port_definition MonadExcept.ofExcept with_native_code
port_definition MonadExcept.orElse with_native_code
port_definition MonadExcept.instOrElse with_native_code

port_native_records BEq, Membership

port_inductive Subtype
port_definition Subtype.val with_native_code
port_proof Subtype.property
port_definition DecidableEq

port_constructor_eliminators Bool, Nat, Option, List, Except, EStateM.Result

port_native_records Min, Max
port_definition getModify with_native_code
port_definition modify with_native_code
port_definition modifyThe with_native_code
port_definition modifyGetThe with_native_code
port_definition Pi.instInhabited with_native_code
port_definition instSMulOfMul with_native_code
port_definition instPowOfHomogeneousPow with_native_code
port_definition instBEqOfDecidableEq with_native_code

port_definition NonemptyType with_native_code
port_definition instInhabitedNonemptyType with_native_code

namespace Omega

public theorem Bool.decEq._proof_1 (a b : Bool) : Bool.Reflects (Bool.beq a b) (Eq a b) :=
  Bool.casesOn (motive := fun a => Bool.Reflects (Bool.beq a b) (Eq a b)) a
    (Bool.casesOn (motive := fun b => Bool.Reflects (Bool.beq Bool.false b) (Eq Bool.false b)) b
      Omega.rfl (Bool.ne_true_of_eq_false Omega.rfl))
    (Bool.casesOn (motive := fun b => Bool.Reflects (Bool.beq Bool.true b) (Eq Bool.true b)) b
      (Bool.ne_false_of_eq_true Omega.rfl) Omega.rfl)

end Omega

port_definition Bool.decEq with_native_code
port_definition instDecidableEqBool with_native_code

port_definition DecidableRel
port_definition Option.noConfusionType
port_definition Option.noConfusion

port_definition List.append.match_1 with_native_code
port_structural_code List.append on_arg 2
port_definition instDecidableEqList.match_1 with_native_code
port_structural_code List.map on_arg 4
port_definition List.foldl.match_1 with_native_code
port_structural_code List.foldl on_arg 5
port_definition List.lengthTRAux.match_1 with_native_code
port_structural_code List.lengthTRAux on_arg 2
port_structural_code List.length on_arg 2

port_definition instMulNat with_native_code
port_definition instNatPowNat with_native_code
port_definition minOfLe with_native_code
port_definition maxOfLe with_native_code
port_definition instMinNat with_native_code
port_definition Decidable.falseTrueCases with_native_code
namespace Omega

end Omega

port_definition instDecidableEqNat with_native_code

port_definition Array.size with_native_code
port_definition Array.mkArray0 with_native_code
port_definition Array.mkArray1 with_native_code
port_definition Array.mkArray2 with_native_code
port_definition Array.mkArray3 with_native_code
port_definition Array.mkArray4 with_native_code
port_definition Array.mkArray5 with_native_code
port_definition Array.mkArray6 with_native_code
port_definition Array.mkArray7 with_native_code
port_definition Array.mkArray8 with_native_code

port_inductive Fin
port_definition Fin.val with_native_code
port_proof Fin.isLt
port_definition instLTFin with_native_code
port_definition instLEFin with_native_code
port_definition Fin.decLt with_native_code
port_definition Fin.decLe with_native_code
port_native_records BitVec
port_definition BitVec.toNat with_native_code
port_definition BitVec.ofNatLT with_native_code
port_definition instLTBitVec with_native_code
port_definition instLEBitVec with_native_code
port_proof instDecidableLtBitVec._proof_1
port_definition instDecidableLtBitVec with_native_code
port_proof instDecidableLeBitVec._proof_1
port_definition instDecidableLeBitVec with_native_code

port_proof Fin.eq_of_val_eq
port_proof Fin.val_eq_of_eq
port_definition instDecidableEqFin.match_1
port_proof instDecidableEqFin._proof_1
port_definition instDecidableEqFin with_native_code
port_definition BitVec.decEq.match_1
port_definition BitVec.noConfusionType
port_definition BitVec.noConfusion
port_proof BitVec.decEq._proof_1
port_definition BitVec.decEq with_native_code
port_definition instDecidableEqBitVec with_native_code

port_native_records UInt8
port_definition UInt8.decEq.match_1
port_definition UInt8.noConfusionType
port_definition UInt8.noConfusion
port_proof UInt8.decEq._proof_1
port_definition UInt8.decEq with_native_code
port_definition instDecidableEqUInt8 with_native_code
port_definition UInt8.lt
port_definition UInt8.le
port_definition instLTUInt8 with_native_code
port_proof UInt8.decLt._proof_1
port_definition UInt8.decLt with_native_code
port_definition instLEUInt8 with_native_code
port_proof UInt8.decLe._proof_1
port_definition UInt8.decLe with_native_code

port_native_records UInt16
port_definition UInt16.decEq.match_1
port_definition UInt16.noConfusionType
port_definition UInt16.noConfusion
port_proof UInt16.decEq._proof_1
port_definition UInt16.decEq with_native_code
port_definition instDecidableEqUInt16 with_native_code

port_native_records UInt32
port_definition UInt32.decEq.match_1
port_definition UInt32.noConfusionType
port_definition UInt32.noConfusion
port_proof UInt32.decEq._proof_1
port_definition UInt32.decEq with_native_code
port_definition instDecidableEqUInt32 with_native_code
port_definition UInt32.toNat with_native_code
port_definition instLTUInt32 with_native_code
port_proof UInt32.decLt._proof_1
port_definition UInt32.decLt with_native_code
port_definition instLEUInt32 with_native_code
port_proof UInt32.decLe._proof_1
port_definition UInt32.decLe with_native_code

port_native_records UInt64
port_definition UInt64.decEq.match_1
port_definition UInt64.noConfusionType
port_definition UInt64.noConfusion
port_proof UInt64.decEq._proof_1
port_definition UInt64.decEq with_native_code
port_definition instDecidableEqUInt64 with_native_code

port_definition instMinUInt32 with_native_code
port_definition instMaxUInt32 with_native_code
port_native_records ByteArray
port_definition ByteArray.emptyWithCapacity with_native_code
port_definition ByteArray.empty with_native_code
port_definition ByteArray.push.match_1 with_native_code
port_definition ByteArray.push with_native_code
port_definition ByteArray.size.match_1 with_native_code
port_definition ByteArray.size with_native_code
port_definition List.toByteArray.match_1 with_native_code
port_definition List.toByteArray.loop._f
port_definition List.toByteArray.loop
port_structural_code List.toByteArray.loop on_arg 1
port_definition List.toByteArray with_native_code

port_proof noConfusion_of_Nat
port_definition List.get.match_1 with_native_code
port_definition List.get._f
port_definition List.get
port_structural_code List.get on_arg 2
port_definition Array.getInternal with_native_code
port_definition Array.getD with_native_code
port_definition List.set.match_1 with_native_code
port_definition List.set._f
port_definition List.set
port_structural_code List.set on_arg 2
port_definition Array.appendCore.loop.match_1 with_native_code
port_definition Array.appendCore.loop._f
port_definition Array.appendCore.loop
port_structural_code Array.appendCore.loop on_arg 3
port_definition Array.appendCore with_native_code
port_definition Array.extract.loop._f
port_definition Array.extract.loop
port_structural_code Array.extract.loop on_arg 3
port_definition Array.extract with_native_code

port_definition List.beq.match_1 with_native_code
port_definition List.beq._f
port_definition List.beq
port_structural_code List.beq on_arg 3
port_definition List.hasDecEq.go.match_3
port_definition PLift.noConfusionType
port_definition PLift.noConfusion
port_definition PLift.up.noConfusion
port_definition ULift.noConfusionType
port_definition ULift.noConfusion
port_definition ULift.up.noConfusion
port_definition List.noConfusionType
port_definition List.noConfusion
port_definition List.hasDecEq.go.match_1
port_proof List.hasDecEq._proof_1
port_definition List.hasDecEq.go._f
port_proof List.hasDecEq.go
port_definition List.hasDecEq with_native_code
port_proof instDecidableEqList._proof_1
port_proof instDecidableEqList._proof_2
port_proof instDecidableEqList._proof_3
port_definition instDecidableEqList.match_5 with_native_code
port_definition decEq with_native_code
port_definition instDecidableEqList.match_3 with_native_code
port_proof instDecidableEqList._proof_4
port_proof instDecidableEqList._proof_5
port_proof instDecidableEqList._proof_6
port_definition instDecidableEqList with_native_code
port_definition List.instDecidableEqNil with_native_code
port_definition List.instDecidableNilEq with_native_code

port_definition Prod.noConfusionType
port_definition Prod.noConfusion
port_definition Subtype.noConfusionType
port_definition Subtype.noConfusion
port_definition instDecidableOr.match_3 with_native_code
port_definition instDecidableOr.match_1 with_native_code
port_proof instDecidableOr._proof_1

port_native_records Trans

port_proof Nat.lt_add_one
port_proof Nat.lt_succ_self
port_proof Nat.le_succ
port_proof Nat.pred_le
port_proof Nat.sub_le
port_proof Nat.lt_succ_of_le
port_proof Nat.sub_lt
port_proof Nat.lt_of_lt_of_le
port_proof Nat.div_rec_lemma
port_proof Nat.le_of_lt_succ
port_proof Nat.div_rec_fuel_lemma
port_definition Nat.div.go.match_1
port_definition Nat.modCore.go._f
port_definition Nat.modCore.go

namespace Omega.Nat

private def modCoreGoImpl (y : Nat) (_ : LT.lt 0 y) (fuel x : Nat) (_ : LT.lt x fuel) : Nat := Nat.mod x y

attribute [implemented_by modCoreGoImpl] Nat.modCore.go

@[expose, irreducible] public protected def modCore (x y : @& Nat) : Nat :=
  dite (LT.lt zero y) (fun hy => Nat.modCore.go y hy (succ x) x (Nat.lt_succ_self x)) (fun _ => x)

end Omega.Nat

port_definition GE.ge
port_definition Nat.eq_or_lt_of_le._f
port_proof Nat.eq_or_lt_of_le
port_proof Nat.le_succ_of_le
port_definition Nat.lt_or_ge._f
port_proof Nat.lt_or_ge
port_proof Nat.lt_of_not_le
port_proof Nat.not_lt_zero
port_proof Nat.modCoreGo_lt
port_proof Nat.modCore_lt

public section
namespace Bool
export _root_.Omega.Bool (and and_eq_internalAnd beq ctorElim ctorElimType ctorIdx dcond decEq eq_false_of_ne_true eq_true_of_ne_false ne_false_of_eq_true ne_true_of_eq_false not not_eq_internalNot or or_eq_internalOr)
end Bool
namespace Bool.false
export _root_.Omega.Bool.false (elim)
end Bool.false
namespace Bool.true
export _root_.Omega.Bool.true (elim)
end Bool.true
namespace Decidable
export _root_.Omega.Decidable (falseTrueCases isFalse isTrue)
end Decidable
namespace False
export _root_.Omega.False (elim)
end False
namespace HEq
export _root_.Omega.HEq (rfl)
end HEq
namespace Nat
export _root_.Omega.Nat (ble_eq_true_of_le ctorElim ctorElimType ctorIdx decLe decLt le le_antisymm le_of_ble_eq_true le_of_succ_le_succ le_refl le_trans lt lt_irrefl modCore modCore_lt mod_lt not_succ_le_zero succ_le_succ succ_sub_succ_eq_sub zero_le)
end Nat
namespace Nat.succ
export _root_.Omega.Nat.succ (elim)
end Nat.succ
namespace Nat.zero
export _root_.Omega.Nat.zero (elim)
end Nat.zero


port_definition GT.gt
port_proof Nat.lt_trans
port_proof decide_eq_false
port_proof of_decide_eq_true
port_proof Nat.brecOn.eq

public section
namespace Nat
export _root_.Omega.Nat (div_rec_fuel_lemma div_rec_lemma eq_or_lt_of_le le_of_lt_succ le_succ le_succ_of_le lt_add_one lt_of_lt_of_le lt_of_not_le lt_or_ge lt_succ_of_le lt_succ_self lt_trans modCoreGo_lt not_lt_zero pred_le sub_le sub_lt)
end Nat
namespace Nat.brecOn
export _root_.Omega.Nat.brecOn (eq)
end Nat.brecOn
