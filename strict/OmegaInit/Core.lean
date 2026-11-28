/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Copyright (c) 2026 The Omega Institute. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
prelude
import all OmegaInit.Prelude

public import OmegaInit.Prelude

noncomputable section

@[expose] public section

port_inductive Sum

namespace Omega

end Omega

port_prop_record Iff
port_prop_record Std.Associative
port_prop_record Std.Commutative
port_prop_record Subsingleton
port_proof Subsingleton.elim

namespace Omega

inductive Exists {α : Sort u} (p : α → Prop) : Prop where
  | intro (w : α) (h : p w) : Exists p

theorem Exists.elim {α : Sort u} {p : α → Prop} {b : Prop}
    (h₁ : Exists p) (h₂ : ∀ a, p a → b) : b :=
  Exists.rec (motive := fun _ => b) h₂ h₁

namespace Nat


theorem succ.inj {m n : Nat} : Eq (succ m) (succ n) → Eq m n := fun h =>
  congrArg pred h

protected theorem add_zero (n : Nat) : Eq (Nat.add n zero) n := Omega.rfl

end Nat

/-! ## Functions and elimination -/

def inline.{u} {α : Sort u} (a : α) : α := a

theorem id_def.{u} {α : Sort u} (a : α) : Eq (id a) a := Omega.rfl

def eagerReduce.{u} {α : Sort u} (a : α) : α := a

def flip.{u, v, w} {α : Sort u} {β : Sort v} {φ : Sort w} (f : α → β → φ) : β → α → φ :=
  fun b a => f a b

theorem Function.const_apply.{u, v} {β : Sort u} {α : Sort v} {y : β} {x : α} :
  Eq (Function.const α y x) y :=
  Omega.rfl

theorem Function.comp_apply.{u, v, w} {β : Sort u} {δ : Sort v} {α : Sort w} {f : β → δ}
  {g : α → β} {x : α} : Eq (Function.comp f g x) (f (g x)) :=
  Omega.rfl

theorem Function.comp_def.{u, v, w} {α : Sort u} {β : Sort v} {δ : Sort w} (f : β → δ)
  (g : α → β) : Eq (Function.comp f g) fun x => f (g x) :=
  Omega.rfl

theorem Function.const_comp.{u, v, w} {α : Sort u} {β : Sort v} {γ : Sort w} {f : α → β}
  {c : γ} : Eq (Function.comp (Function.const β c) f) (Function.const α c) :=
  Omega.rfl

theorem Function.comp_const.{u, v, w} {β : Sort u} {γ : Sort v} {α : Sort w} {f : β → γ}
  {b : β} : Eq (Function.comp f (Function.const α b)) (Function.const α (f b)) :=
  Omega.rfl

theorem Function.true_comp.{u, v} {α : Sort u} {β : Sort v} {f : α → β} :
  Eq (Function.comp (fun _ => Bool.true) f) fun _ => Bool.true :=
  Omega.rfl

theorem Function.false_comp.{u, v} {α : Sort u} {β : Sort v} {f : α → β} :
  Eq (Function.comp (fun _ => Bool.false) f) fun _ => Bool.false :=
  Omega.rfl

theorem Function.comp_id.{u, v} {α : Sort u} {β : Sort v} (f : α → β) :
  Eq (Function.comp f id) f :=
  Omega.rfl

theorem Function.id_comp.{u, v} {α : Sort u} {β : Sort v} (f : α → β) :
  Eq (Function.comp id f) f :=
  Omega.rfl

def Empty.elim.{u} {C : Sort u} : Empty → C := fun x => Empty.casesOn (fun _ => C) x

def PEmpty.elim.{u, v} {C : Sort u} : PEmpty.{v} → C :=
  let motive : PEmpty → Prop := fun _ => False; fun a => False.elim (PEmpty.rec (motive := motive) a)

abbrev Eq.ndrecOn.{u1, u2} {α : Sort u2} {a : α} {motive : α → Sort u1} {b : α} (h : Eq a b)
  (m : motive a) : motive b :=
  Eq.ndrec m h

/-! ## Negation and equality -/

theorem trivial : True := True.intro

theorem mt {a b : Prop} (h₁ : a → b) (h₂ : Not b) : Not a := fun ha => h₂ (h₁ ha)

theorem not_false : Not False := id

theorem not_not_intro {p : Prop} (h : p) : Not (Not p) := fun hn => hn h

theorem proof_irrel {a : Prop} (h₁ h₂ : a) : Eq h₁ h₂ := Omega.rfl

def Eq.mp.{u} {α β : Sort u} (h : Eq α β) (a : α) : β := cast h a

def Eq.mpr.{u} {α β : Sort u} (h : Eq α β) (b : β) : α := cast h.symm b

theorem Eq.substr.{u} {α : Sort u} {p : α → Prop} {a b : α} (h₁ : Eq b a) (h₂ : p a) : p b :=
  Eq.subst h₁.symm h₂

theorem cast_eq.{u} {α : Sort u} (h : Eq α α) (a : α) : Eq (cast h a) a := Omega.rfl

@[reducible] def Ne.{u} {α : Sort u} (a b : α) : Prop := Not (Eq a b)

theorem Ne.intro.{u} {α : Sort u} {a b : α} (h : Eq a b → False) : Ne a b := h

theorem Ne.irrefl.{u} {α : Sort u} {a : α} (h : Ne a a) : False := h Omega.rfl

theorem Ne.symm.{u} {α : Sort u} {a b : α} (h : Ne a b) : Ne b a := fun h₁ => h h₁.symm

theorem ne_comm.{u} {α : Sort u} {a b : α} : Iff (Ne a b) (Ne b a) := Iff.intro Ne.symm Ne.symm

theorem false_of_ne.{u} {α : Sort u} {a : α} : Ne a a → False := Ne.irrefl

theorem ne_false_of_self {p : Prop} : p → Ne p False := fun hp h => Eq.mp h hp

theorem ne_true_of_not {p : Prop} : Not p → Ne p True := fun hn h => hn (Eq.mpr h trivial)

theorem true_ne_false : Not (Eq True False) := ne_false_of_self trivial

theorem false_ne_true : Ne False True := Ne.symm true_ne_false

theorem Bool.of_not_eq_true {b : Bool} : Not (Eq b Bool.true) → Eq b Bool.false :=
  Bool.rec (motive := fun b => Not (Eq b Bool.true) → Eq b Bool.false)
    (fun _ => Omega.rfl) (fun h => False.elim (h Omega.rfl)) b

theorem Bool.of_not_eq_false {b : Bool} : Not (Eq b Bool.false) → Eq b Bool.true :=
  Bool.rec (motive := fun b => Not (Eq b Bool.false) → Eq b Bool.true)
    (fun h => False.elim (h Omega.rfl)) (fun _ => Omega.rfl) b

/-! ## Heterogeneous equality -/

def HEq.ndrec.{u1, u2} {α : Sort u2} {a : α} {motive : {β : Sort u2} → β → Sort u1} (m : motive a)
  {β : Sort u2} {b : β} (h : HEq a b) : motive b :=
  HEq.rec (motive := fun {_} b _ => motive b) m h

def HEq.ndrecOn.{u1, u2} {α : Sort u2} {a : α} {motive : {β : Sort u2} → β → Sort u1} {β : Sort u2}
  {b : β} (h : HEq a b) (m : motive a) : motive b :=
  HEq.ndrec m h

theorem HEq.subst.{u} {α β : Sort u} {a : α} {b : β} {p : (T : Sort u) → T → Prop} (h₁ : HEq a b)
  (h₂ : p α a) : p β b :=
  HEq.ndrec (motive := fun {T} x => p T x) h₂ h₁

theorem HEq.symm.{u} {α β : Sort u} {a : α} {b : β} (h : HEq a b) : HEq b a :=
  HEq.ndrec (motive := fun b => HEq b a) (HEq.refl a) h

theorem HEq.trans.{u} {α β φ : Sort u} {a : α} {b : β} {c : φ} (h₁ : HEq a b) (h₂ : HEq b c) : HEq a c :=
  HEq.ndrec (motive := fun c => HEq a c) h₁ h₂

theorem heq_of_heq_of_eq.{u} {α β : Sort u} {a : α} {b b' : β} (h₁ : HEq a b) (h₂ : Eq b b') : HEq a b' :=
  HEq.trans h₁ (heq_of_eq h₂)

theorem heq_of_eq_of_heq.{u} {α β : Sort u} {a a' : α} {b : β} (h₁ : Eq a a') (h₂ : HEq a' b) : HEq a b :=
  HEq.trans (heq_of_eq h₁) h₂

theorem type_eq_of_heq.{u} {α β : Sort u} {a : α} {b : β} (h : HEq a b) : Eq α β :=
  HEq.ndrec (motive := fun {β} _ => Eq α β) (Eq.refl α) h

theorem eqRec_heq.{u, v} {α : Sort u} {φ : α → Sort v} {a a' : α} (h : Eq a a') (p : φ a) :
  HEq (Eq.recOn (motive := fun x _ => φ x) h p) p :=
  Eq.rec (motive := fun _ h => HEq (Eq.rec (motive := fun x _ => φ x) p h) p)
    (HEq.refl p) h

theorem eqRec_heq_iff.{u, v} {β : Sort v} {α : Sort u} {a : α} {motive : (b : α) → Eq a b → Sort v}
  {b : α} {refl : motive a Omega.rfl} {h : Eq a b} {c : β} : Iff (HEq (Eq.rec (motive := motive) refl h) c) (HEq refl c) :=
  Eq.rec (motive := fun _ h => Iff (HEq (Eq.rec (motive := motive) refl h) c) (HEq refl c))
    (Iff.intro id id) h

theorem heq_eqRec_iff.{u, v} {β : Sort v} {α : Sort u} {a : α} {motive : (b : α) → Eq a b → Sort v}
  {b : α} {refl : motive a Omega.rfl} {h : Eq a b} {c : β} : Iff (HEq c (Eq.rec (motive := motive) refl h)) (HEq c refl) :=
  Eq.rec (motive := fun _ h => Iff (HEq c (Eq.rec (motive := motive) refl h)) (HEq c refl))
    (Iff.intro id id) h

theorem cast_heq.{u} {α β : Sort u} (h : Eq α β) (a : α) : HEq (cast h a) a :=
  Eq.rec (motive := fun _ h => HEq (cast h a) a) (HEq.refl a) h

theorem heq_of_eqRec_eq.{u} {α β : Sort u} {a : α} {b : β} (h₁ : Eq α β) (h₂ : Eq (Eq.rec (motive := fun α _ => α) a h₁) b) :
  HEq a b :=
  HEq.trans (HEq.symm (cast_heq h₁ a)) (heq_of_eq h₂)

/-! ## Logical equivalence -/

theorem iff_iff_implies_and_implies {a b : Prop} : Iff (Iff a b) (And (a → b) (b → a)) :=
  Iff.intro (fun h => And.intro h.mp h.mpr) (fun h => Iff.intro h.left h.right)

theorem Iff.refl (a : Prop) : Iff a a := Iff.intro id id

protected theorem Iff.rfl {a : Prop} : Iff a a := Iff.refl a

theorem Iff.of_eq {a b : Prop} (h : Eq a b) : Iff a b :=
  Eq.subst (motive := fun b => Iff a b) h (Iff.refl a)

theorem Iff.trans {a b c : Prop} (h₁ : Iff a b) (h₂ : Iff b c) : Iff a c :=
  Iff.intro (fun ha => h₂.mp (h₁.mp ha)) (fun hc => h₁.mpr (h₂.mpr hc))

theorem Eq.comm.{u} {α : Sort u} {a b : α} : Iff (Eq a b) (Eq b a) := Iff.intro Eq.symm Eq.symm

theorem eq_comm.{u} {α : Sort u} {a b : α} : Iff (Eq a b) (Eq b a) := Eq.comm

theorem HEq.comm.{u} {α β : Sort u} {a : α} {b : β} : Iff (HEq a b) (HEq b a) :=
  Iff.intro HEq.symm HEq.symm

theorem heq_comm.{u} {α β : Sort u} {a : α} {b : β} : Iff (HEq a b) (HEq b a) := HEq.comm

theorem Iff.symm {a b : Prop} (h : Iff a b) : Iff b a := Iff.intro h.mpr h.mp

theorem Iff.comm {a b : Prop} : Iff (Iff a b) (Iff b a) := Iff.intro Iff.symm Iff.symm

theorem iff_comm {a b : Prop} : Iff (Iff a b) (Iff b a) := Iff.comm

theorem And.symm {a b : Prop} : And a b → And b a := fun h => And.intro h.right h.left

theorem And.comm {a b : Prop} : Iff (And a b) (And b a) := Iff.intro And.symm And.symm

theorem and_comm {a b : Prop} : Iff (And a b) (And b a) := And.comm

theorem Or.symm {a b : Prop} : Or a b → Or b a := fun h => h.elim Or.inr Or.inl

theorem Or.comm {a b : Prop} : Iff (Or a b) (Or b a) := Iff.intro Or.symm Or.symm

theorem or_comm {a b : Prop} : Iff (Or a b) (Or b a) := Or.comm

theorem PUnit.eq_punit.{u} (a : PUnit.{u}) : Eq a PUnit.unit :=
  PUnit.rec (motive := fun a => Eq a PUnit.unit) Omega.rfl a

/-! ## Elimination and propositional laws -/

def Not.elim.{u} {a : Prop} {α : Sort u} (H1 : Not a) (H2 : a) : α := absurd H2 H1

abbrev And.elim.{u} {a b : Prop} {α : Sort u} (f : a → b → α) (h : And a b) : α :=
  f h.left h.right

def Iff.elim.{u} {a b : Prop} {α : Sort u} (f : (a → b) → (b → a) → α) (h : Iff a b) : α :=
  f h.mp h.mpr

theorem Not.intro {a : Prop} (h : a → False) : Not a := h

theorem Not.imp {a b : Prop} (H2 : Not b) (H1 : a → b) : Not a := mt H1 H2

theorem not_congr {a b : Prop} (h : Iff a b) : Iff (Not a) (Not b) :=
  Iff.intro (mt h.mpr) (mt h.mp)

theorem not_not_not {a : Prop} : Iff (Not (Not (Not a))) (Not a) :=
  Iff.intro (mt not_not_intro) not_not_intro

theorem iff_of_true {a b : Prop} (ha : a) (hb : b) : Iff a b :=
  Iff.intro (fun _ => hb) (fun _ => ha)

theorem iff_of_false {a b : Prop} (ha : Not a) (hb : Not b) : Iff a b :=
  Iff.intro (Not.elim ha) (Not.elim hb)

theorem iff_true_left {a b : Prop} (ha : a) : Iff (Iff a b) b :=
  Iff.intro (fun h => h.mp ha) (iff_of_true ha)

theorem iff_true_right {a b : Prop} (ha : a) : Iff (Iff b a) b :=
  Iff.comm.trans (iff_true_left ha)

theorem iff_false_left {a b : Prop} (ha : Not a) : Iff (Iff a b) (Not b) :=
  Iff.intro (fun h => mt h.mpr ha) (iff_of_false ha)

theorem iff_false_right {a b : Prop} (ha : Not a) : Iff (Iff b a) (Not b) :=
  Iff.comm.trans (iff_false_left ha)

theorem of_iff_true {a : Prop} (h : Iff a True) : a := h.mpr trivial

theorem iff_true_intro {a : Prop} (h : a) : Iff a True := iff_of_true h trivial

theorem not_of_iff_false {p : Prop} : Iff p False → Not p := Iff.mp

theorem iff_false_intro {a : Prop} (h : Not a) : Iff a False := iff_of_false h id

theorem not_iff_false_intro {a : Prop} (h : a) : Iff (Not a) False :=
  iff_false_intro (not_not_intro h)

theorem not_true : Iff (Not True) False := iff_false_intro (not_not_intro trivial)

theorem not_false_iff : Iff (Not False) True := iff_true_intro not_false

theorem Eq.to_iff {a b : Prop} : Eq a b → Iff a b := Iff.of_eq

theorem iff_of_eq {a b : Prop} : Eq a b → Iff a b := Iff.of_eq

theorem neq_of_not_iff {a b : Prop} : Not (Iff a b) → Ne a b := mt Iff.of_eq

theorem eq_self_iff_true.{u} {α : Sort u} (a : α) : Iff (Eq a a) True := iff_true_intro Omega.rfl

theorem ne_self_iff_false.{u} {α : Sort u} (a : α) : Iff (Ne a a) False :=
  not_iff_false_intro Omega.rfl

theorem false_of_true_iff_false (h : Iff True False) : False := h.mp trivial

theorem false_of_true_eq_false (h : Eq True False) : False :=
  false_of_true_iff_false (Iff.of_eq h)

theorem true_eq_false_of_false : False → Eq True False := False.elim

theorem iff_def {a b : Prop} : Iff (Iff a b) (And (a → b) (b → a)) := iff_iff_implies_and_implies

theorem iff_def' {a b : Prop} : Iff (Iff a b) (And (b → a) (a → b)) := Iff.trans iff_def And.comm

theorem true_iff_false : Iff (Iff True False) False := iff_false_intro (fun h => h.mp trivial)

theorem false_iff_true : Iff (Iff False True) False := iff_false_intro (fun h => h.mpr trivial)

theorem iff_not_self {a : Prop} : Not (Iff a (Not a)) :=
  fun h =>
    let hn : Not a := fun ha => h.mp ha ha
    hn (h.mpr hn)

theorem heq_self_iff_true.{u} {α : Sort u} (a : α) : Iff (HEq a a) True := iff_true_intro HEq.rfl

/-! ## Implication -/

theorem not_not_of_not_imp {a b : Prop} : Not (a → b) → Not (Not a) := mt Not.elim

theorem not_of_not_imp {b a : Prop} : Not (a → b) → Not b := mt (fun hb _ => hb)

theorem imp_not_self {a : Prop} : Iff (a → Not a) (Not a) :=
  Iff.intro (fun h ha => h ha ha) (fun h _ => h)

theorem imp_intro {α β : Prop} (h : α) : β → α := fun _ => h

theorem imp_imp_imp {a b c d : Prop} (h₀ : c → a) (h₁ : b → d) : (a → b) → c → d :=
  fun f hc => h₁ (f (h₀ hc))

theorem imp_iff_right {b a : Prop} (ha : a) : Iff (a → b) b :=
  Iff.intro (fun f => f ha) (fun hb _ => hb)

theorem imp_true_iff.{u} (α : Sort u) : Iff (α → True) True := iff_true_intro (fun _ => trivial)

theorem false_imp_iff (a : Prop) : Iff (False → a) True := iff_true_intro False.elim

theorem true_imp_iff {α : Prop} : Iff (True → α) α := imp_iff_right trivial

theorem imp_self {a : Prop} : Iff (a → a) True := iff_true_intro id

theorem imp_false {a : Prop} : Iff (a → False) (Not a) := Iff.rfl

theorem imp.swap {a b c : Prop} : Iff (a → b → c) (b → a → c) := Iff.intro flip flip

theorem imp_not_comm {a b : Prop} : Iff (a → Not b) (b → Not a) := imp.swap

theorem imp_congr_left {a b c : Prop} (h : Iff a b) : Iff (a → c) (b → c) :=
  Iff.intro (fun f hb => f (h.mpr hb)) (fun f ha => f (h.mp ha))

theorem imp_congr_right {a b c : Prop} (h : a → Iff b c) : Iff (a → b) (a → c) :=
  Iff.intro (fun hab ha => (h ha).mp (hab ha)) (fun hac ha => (h ha).mpr (hac ha))

theorem imp_congr_ctx {a b c d : Prop} (h₁ : Iff a c) (h₂ : c → Iff b d) : Iff (a → b) (c → d) :=
  Iff.trans (imp_congr_left h₁) (imp_congr_right h₂)

theorem imp_congr {a b c d : Prop} (h₁ : Iff a c) (h₂ : Iff b d) : Iff (a → b) (c → d) :=
  imp_congr_ctx h₁ (fun _ => h₂)

theorem imp_iff_not {a b : Prop} (hb : Not b) : Iff (a → b) (Not a) :=
  imp_congr_right (fun _ => iff_false_intro hb)

theorem flip_flip.{u, v, w} {α : Sort u} {β : Sort v} {φ : Sort w} {f : α → β → φ} :
  Eq (flip (flip f)) f :=
  Omega.rfl

end Omega

port_proof apply_eqRec
port_proof optParam_eq by_reflexivity
port_proof Lean.injEq_helper
port_proof PUnit.ext by_reflexivity
port_proof PUnit.subsingleton by_reflexivity
port_proof Sum.nonemptyLeft
port_proof Sum.nonemptyRight
port_proof flip.eq_1 by_reflexivity
port_proof id.eq_1 by_reflexivity
port_proof inline.eq_1 by_reflexivity

namespace Omega

theorem ite_eq_left {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : Eq (@ite α c h t e) t :=
  Decidable.rec (motive := fun d => Eq (@ite α c d t e) t) (fun bit =>
    Bool.casesOn (motive := fun bit => ∀ reflected : Bool.Reflects bit c,
        Eq (@ite α c (Decidable.intro bit reflected) t e) t) bit
      (fun no => False.elim (no hc)) (fun _ => Omega.rfl)) h

theorem ite_eq_right {c : Prop} {h : Decidable c} (hnc : Not c) {α : Sort u} {t e : α} : Eq (@ite α c h t e) e :=
  Decidable.rec (motive := fun d => Eq (@ite α c d t e) e) (fun bit =>
    Bool.casesOn (motive := fun bit => ∀ reflected : Bool.Reflects bit c,
        Eq (@ite α c (Decidable.intro bit reflected) t e) e) bit
      (fun _ => Omega.rfl) (fun yes => False.elim (hnc yes))) h

end Omega

port_proof if_pos
port_proof if_neg

port_inductive ForInStep
port_native_records ForIn, ForIn'

port_inductive PSum
port_inductive DoResultPRBC
port_inductive DoResultPR
port_inductive DoResultBC
port_inductive DoResultSBC
port_inductive PNonScalar
port_native_records NonScalar
port_definition instDecidableEqProd.match_3 with_native_code
port_definition Prod.map with_native_code
port_definition PSum.inhabitedLeft with_native_code
port_definition PSum.inhabitedRight with_native_code
port_definition Sum.inhabitedLeft with_native_code
port_definition Sum.inhabitedRight with_native_code
port_definition Subtype.instBEq with_native_code
port_definition instBEqOption.beq with_native_code
port_definition instBEqOption with_native_code
port_definition instBEqProd with_native_code
port_definition instDecidableEqPUnit with_native_code
port_definition instDecidableFalse with_native_code
port_definition instDecidableTrue with_native_code
port_definition instInhabitedForInStep.default with_native_code
port_definition instInhabitedForInStep with_native_code
port_definition instInhabitedMProd with_native_code
port_definition instInhabitedNonScalar.default with_native_code
port_definition instInhabitedNonScalar with_native_code
port_definition instInhabitedPNonScalar.default with_native_code
port_definition instInhabitedPNonScalar with_native_code
port_definition instInhabitedPProd with_native_code
port_definition instInhabitedPUnit with_native_code
port_definition instInhabitedProd with_native_code
port_definition instInhabitedProp with_native_code
port_proof instInhabitedTrue.default
port_definition instInhabitedTrue with_native_code
port_definition strictAnd with_native_code
port_definition strictOr with_native_code
port_definition toBoolUsing with_native_code
port_definition bne with_native_code

port_constructor_eliminators PSum, Sum, ForInStep, DoResultBC, DoResultPR, DoResultPRBC, DoResultSBC

port_definition decidable_of_decidable_of_iff.match_1
port_proof decidable_of_decidable_of_iff._proof_1
port_definition decidable_of_decidable_of_iff with_native_code
port_proof decidable_of_decidable_of_eq._proof_1
port_definition decidable_of_decidable_of_eq with_native_code

port_definition instDecidableEqProd.match_1 with_native_code
port_proof instDecidableEqProd._proof_1
port_definition instDecidableEqProd with_native_code
port_definition instDecidableEqSum.decEq.match_1 with_native_code
port_proof instDecidableEqSum.decEq._proof_1
port_definition Sum.noConfusionType
port_definition Sum.noConfusion
port_definition Sum.inl.noConfusion
port_proof instDecidableEqSum.decEq._proof_3
port_proof instDecidableEqSum.decEq._proof_4
port_proof instDecidableEqSum.decEq._proof_5
port_proof instDecidableEqSum.decEq._proof_2
port_definition Sum.inr.noConfusion
port_proof instDecidableEqSum.decEq._proof_6
port_definition instDecidableEqSum.decEq with_native_code
port_definition instDecidableEqSum with_native_code
port_definition instDecidableEqPEmpty with_native_code
port_definition instDecidableEqEmpty with_native_code
port_definition Subtype.instDecidableEq.match_1 with_native_code
port_proof Subtype.instDecidableEq._proof_3
port_proof Subtype.instDecidableEq._proof_1
port_definition Subtype.instDecidableEq with_native_code
port_definition Prod.lexLt
port_proof Prod.lexLtDec._proof_1
port_definition Prod.lexLtDec with_native_code
port_native_records Equivalence, Setoid
port_proof equivalence_true
port_definition Setoid.trivial with_native_code
port_inductive ReflBEq
port_inductive LawfulBEq
port_definition instDecidableEqOfLawfulBEq.match_1 with_native_code
port_proof ReflBEq.rfl
port_proof BEq.rfl
port_proof not_eq_of_beq_eq_false
port_proof LawfulBEq.toReflBEq
port_proof LawfulBEq.eq_of_beq
port_proof instDecidableEqOfLawfulBEq._proof_1
port_definition instDecidableEqOfLawfulBEq with_native_code
port_definition instDecidableIff.match_1 with_native_code
port_proof instDecidableIff._proof_1
port_definition instDecidableIff with_native_code

port_native_records Thunk
port_definition Thunk.pure with_native_code
port_definition Thunk.get with_native_code
port_definition Thunk.fnImpl with_native_code
port_proof Thunk.fn_eq_fnImpl
port_thunk_field_code
port_definition Thunk.map with_native_code
port_definition Thunk.bind with_native_code
port_definition instInhabitedThunk with_native_code
attribute [instance] Omega.instInhabitedThunk Omega.LawfulBEq.toReflBEq Omega.instBEqProd

namespace Omega
export _root_ (Thunk)
end Omega

namespace Omega.Thunk
export _root_.Thunk (mk get fn pure rec recOn casesOn)
end Omega.Thunk

namespace Thunk
export _root_.Omega.Thunk (fnImpl fn_eq_fnImpl map bind)
end Thunk

port_native_records Sigma
port_definition instDecidableEqSigma.match_5 with_native_code
port_definition instDecidableEqSigma.match_3 with_native_code
port_definition instDecidableEqSigma.match_1 with_native_code
port_proof instDecidableEqSigma._proof_1
port_definition Sigma.noConfusionType
port_definition Sigma.noConfusion
port_proof instDecidableEqSigma._proof_2
port_proof instDecidableEqSigma._proof_3
port_definition instDecidableEqSigma with_native_code
port_native_records PSigma
port_definition instDecidableEqPSigma.match_5 with_native_code
port_definition instDecidableEqPSigma.match_3 with_native_code
port_definition instDecidableEqPSigma.match_1 with_native_code
port_proof instDecidableEqPSigma._proof_1
port_definition PSigma.noConfusionType
port_definition PSigma.noConfusion
port_proof instDecidableEqPSigma._proof_2
port_proof instDecidableEqPSigma._proof_3
port_definition instDecidableEqPSigma with_native_code

port_definition Decidable.byCases.match_1 with_native_code
port_definition iteInduction with_native_code
port_definition instDecidableDite with_native_code
port_native_records HasEquiv
port_definition instHasEquivOfSetoid with_native_code

port_proof Quot.liftBeta
port_proof Quot.indBeta
port_proof Quot.inductionOn
port_proof Quot.exists_rep
port_definition Quot.indep

/- Quot.indepCoherent, Quot.liftIndepPr1, Quot.rec and Quot.recOn transport a
branch along Quot.sound. Their pinned coherence premise requires that path even
when the motive has a constant result. The unit-motive specialization in
HeterogeneousQuotient.soundFromUnitCoherence recovers Quot.sound from coherence. -/
port_definition Quotient
port_definition Quotient.mk with_native_code
port_definition Quotient.mk' with_native_code
port_definition Quotient.lift with_native_code
port_proof Quotient.ind
port_definition Quotient.liftOn with_native_code
port_proof Quotient.inductionOn
port_proof Quotient.exists_rep
port_proof Setoid.refl
port_proof Setoid.symm
port_proof Setoid.trans
port_proof Quotient.lift₂._proof_1
port_proof Quotient.lift₂._proof_2
port_definition Quotient.lift₂ with_native_code
port_definition Quotient.liftOn₂ with_native_code
port_proof Quotient.ind₂
port_proof Quotient.inductionOn₂
port_proof Quotient.inductionOn₃
port_alternative_definition Quot.hrecOn from OmegaChecks.InitPort.Alternatives.Logic.Quotient
port_definition Quotient.hrecOn with_native_code
/- Quotient.sound identifies false and true for Setoid.trivial Bool.
RepresentativeQuotient.refuteSound separates those representatives while preserving
the four quotient primitives and both computation rules. Quotient.rec and
Quotient.recOn require this equality in the type of the branch coherence proof.
Quotient.decidableEq also returns a positive decision on these two representatives
with the pinned always-true relation test (RepresentativeQuotient.refutePositiveDecision). -/

port_definition Squash
port_definition Squash.mk with_native_code
port_proof Squash.ind
port_proof Squash.lift._proof_1
port_definition Squash.lift with_native_code
/- instSubsingletonSquash would identify Squash.mk false with Squash.mk true.
RepresentativeQuotient.refuteSquash checks these two distinct representatives. -/
port_definition instTransIff with_native_code
port_definition noConfusionTypeEnum
port_proof noConfusionEnum._proof_1
port_proof noConfusionEnum._proof_2
port_definition noConfusionEnum with_native_code

namespace Omega
export _root_ (noConfusionTypeEnum noConfusionEnum)
end Omega

namespace Omega.Lean
public opaque opaqueId {α : Sort u} (x : α) : α := x
end Omega.Lean

public section
namespace Bool
export _root_.Omega.Bool (of_not_eq_false of_not_eq_true)
end Bool
namespace Eq
export _root_.Omega.Eq (comm mp mpr ndrecOn substr to_iff)
end Eq
namespace HEq
export _root_.Omega.HEq (comm ndrec ndrecOn subst symm trans)
end HEq
namespace Nat
export _root_.Omega.Nat (add_zero)
end Nat
namespace Nat.succ
export _root_.Omega.Nat.succ (inj)
end Nat.succ
namespace Not
export _root_.Omega.Not (elim imp intro)
end Not
namespace Omega.id
export _root_.id (eq_1)
end Omega.id
namespace PUnit
export _root_.Omega.PUnit (eq_punit ext subsingleton)
end PUnit

port_definition InvImage

port_proof dite_eq_left
port_proof dite_eq_right
port_definition Decidable.byCases
port_proof Decidable.em

public section
namespace Decidable
export _root_.Omega.Decidable (byCases em)
end Decidable

port_proof instSubsingletonPUnit
attribute [instance] Omega.instSubsingletonPUnit
