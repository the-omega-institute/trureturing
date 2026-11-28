/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Floris van Doorn, Mario Carneiro
-/
module
prelude
public import OmegaInit.Core

/-! Constructive proofs of the propositional and quantifier laws from Lean Init. -/

public section
namespace Omega

/-! ## Negation -/

theorem not_not_em (a : Prop) : Not (Not (Or a (Not a))) :=
  fun h => h (Or.inr fun ha => h (Or.inl ha))

/-! ## Conjunction -/

theorem and_self_iff {a : Prop} : Iff (And a a) a :=
  Iff.intro And.left (fun ha => And.intro ha ha)

theorem and_not_self_iff (a : Prop) : Iff (And a (Not a)) False :=
  Iff.intro (fun h => h.right h.left) False.elim

theorem not_and_self_iff (a : Prop) : Iff (And (Not a) a) False :=
  Iff.intro (fun h => h.left h.right) False.elim

theorem And.imp {a c b d : Prop} (f : a → c) (g : b → d) (h : And a b) : And c d :=
  And.intro (f h.left) (g h.right)

theorem And.imp_left {a b c : Prop} (h : a → b) : And a c → And b c :=
  And.imp h (fun x => x)

theorem And.imp_right {a b c : Prop} (h : a → b) : And c a → And c b :=
  And.imp (fun x => x) h

theorem and_congr {a c b d : Prop} (h₁ : Iff a c) (h₂ : Iff b d) : Iff (And a b) (And c d) :=
  Iff.intro (And.imp h₁.mp h₂.mp) (And.imp h₁.mpr h₂.mpr)

theorem and_congr_left' {a b c : Prop} (h : Iff a b) : Iff (And a c) (And b c) :=
  and_congr h (Iff.intro (fun x => x) (fun x => x))

theorem and_congr_right' {b c a : Prop} (h : Iff b c) : Iff (And a b) (And a c) :=
  and_congr (Iff.intro (fun x => x) (fun x => x)) h

theorem not_and_of_not_left {a : Prop} (b : Prop) : Not a → Not (And a b) :=
  fun ha h => ha h.left

theorem not_and_of_not_right (a : Prop) {b : Prop} : Not b → Not (And a b) :=
  fun hb h => hb h.right

theorem and_left_comm {a b c : Prop} : Iff (And a (And b c)) (And b (And a c)) :=
  Iff.intro (fun h => And.intro h.right.left (And.intro h.left h.right.right))
    (fun h => And.intro h.right.left (And.intro h.left h.right.right))

theorem and_right_comm {a b c : Prop} : Iff (And (And a b) c) (And (And a c) b) :=
  Iff.intro (fun h => And.intro (And.intro h.left.left h.right) h.left.right)
    (fun h => And.intro (And.intro h.left.left h.right) h.left.right)

theorem and_rotate {a b c : Prop} : Iff (And a (And b c)) (And b (And c a)) :=
  Iff.intro (fun h => And.intro h.right.left (And.intro h.right.right h.left))
    (fun h => And.intro h.right.right (And.intro h.left h.right.left))

theorem and_and_and_comm {a b c d : Prop} : Iff (And (And a b) (And c d)) (And (And a c) (And b d)) :=
  Iff.intro
    (fun h => And.intro (And.intro h.left.left h.right.left) (And.intro h.left.right h.right.right))
    (fun h => And.intro (And.intro h.left.left h.right.left) (And.intro h.left.right h.right.right))

theorem and_and_left {a b c : Prop} : Iff (And a (And b c)) (And (And a b) (And a c)) :=
  Iff.intro (fun h => And.intro (And.intro h.left h.right.left) (And.intro h.left h.right.right))
    (fun h => And.intro h.left.left (And.intro h.left.right h.right.right))

theorem and_and_right {a b c : Prop} : Iff (And (And a b) c) (And (And a c) (And b c)) :=
  Iff.intro (fun h => And.intro (And.intro h.left.left h.right) (And.intro h.left.right h.right))
    (fun h => And.intro (And.intro h.left.left h.right.left) h.left.right)

theorem and_iff_left {b a : Prop} (hb : b) : Iff (And a b) a :=
  Iff.intro And.left (fun ha => And.intro ha hb)

theorem and_iff_right {a b : Prop} (ha : a) : Iff (And a b) b :=
  Iff.intro And.right (And.intro ha)

theorem and_imp_left_iff_true {P Q : Prop} : Iff (And P Q → P) True :=
  Iff.intro (fun _ => True.intro) (fun _ => And.left)

theorem and_imp_right_iff_true {P Q : Prop} : Iff (And P Q → Q) True :=
  Iff.intro (fun _ => True.intro) (fun _ => And.right)

/-! ## Disjunction -/

theorem or_self_iff {a : Prop} : Iff (Or a a) a :=
  Iff.intro (fun h => h.elim (fun ha => ha) (fun ha => ha)) Or.inl

theorem not_or_intro {a b : Prop} (ha : Not a) (hb : Not b) : Not (Or a b) :=
  fun h => h.elim ha hb

theorem or_congr {a c b d : Prop} (h₁ : Iff a c) (h₂ : Iff b d) : Iff (Or a b) (Or c d) :=
  Iff.intro (fun h => h.elim (fun ha => Or.inl (h₁.mp ha)) (fun hb => Or.inr (h₂.mp hb)))
    (fun h => h.elim (fun hc => Or.inl (h₁.mpr hc)) (fun hd => Or.inr (h₂.mpr hd)))

theorem or_congr_left {a b c : Prop} (h : Iff a b) : Iff (Or a c) (Or b c) :=
  or_congr h (Iff.intro (fun x => x) (fun x => x))

theorem or_congr_right {b c a : Prop} (h : Iff b c) : Iff (Or a b) (Or a c) :=
  or_congr (Iff.intro (fun x => x) (fun x => x)) h

theorem or_left_comm {a b c : Prop} : Iff (Or a (Or b c)) (Or b (Or a c)) :=
  Iff.intro
    (fun h => h.elim (fun ha => Or.inr (Or.inl ha))
      (fun hbc => hbc.elim Or.inl (fun hc => Or.inr (Or.inr hc))))
    (fun h => h.elim (fun hb => Or.inr (Or.inl hb))
      (fun hac => hac.elim Or.inl (fun hc => Or.inr (Or.inr hc))))

theorem or_right_comm {a b c : Prop} : Iff (Or (Or a b) c) (Or (Or a c) b) :=
  Iff.intro
    (fun h => h.elim (fun hab => hab.elim (fun ha => Or.inl (Or.inl ha)) Or.inr)
      (fun hc => Or.inl (Or.inr hc)))
    (fun h => h.elim (fun hac => hac.elim (fun ha => Or.inl (Or.inl ha)) Or.inr)
      (fun hb => Or.inl (Or.inr hb)))

theorem or_or_or_comm {a b c d : Prop} : Iff (Or (Or a b) (Or c d)) (Or (Or a c) (Or b d)) :=
  Iff.intro
    (fun h => h.elim
      (fun hab => hab.elim (fun ha => Or.inl (Or.inl ha)) (fun hb => Or.inr (Or.inl hb)))
      (fun hcd => hcd.elim (fun hc => Or.inl (Or.inr hc)) (fun hd => Or.inr (Or.inr hd))))
    (fun h => h.elim
      (fun hac => hac.elim (fun ha => Or.inl (Or.inl ha)) (fun hc => Or.inr (Or.inl hc)))
      (fun hbd => hbd.elim (fun hb => Or.inl (Or.inr hb)) (fun hd => Or.inr (Or.inr hd))))

theorem or_or_distrib_left {a b c : Prop} : Iff (Or a (Or b c)) (Or (Or a b) (Or a c)) :=
  Iff.intro (fun h => or_or_or_comm.mp ((or_congr_left or_self_iff).mpr h))
    (fun h => (or_congr_left or_self_iff).mp (or_or_or_comm.mpr h))

theorem or_or_distrib_right {a b c : Prop} : Iff (Or (Or a b) c) (Or (Or a c) (Or b c)) :=
  Iff.intro (fun h => or_or_or_comm.mp ((or_congr_right or_self_iff).mpr h))
    (fun h => (or_congr_right or_self_iff).mp (or_or_or_comm.mpr h))

theorem or_rotate {a b c : Prop} : Iff (Or a (Or b c)) (Or b (Or c a)) :=
  Iff.intro
    (fun h => h.elim (fun ha => Or.inr (Or.inr ha))
      (fun hbc => hbc.elim Or.inl (fun hc => Or.inr (Or.inl hc))))
    (fun h => h.elim (fun hb => Or.inr (Or.inl hb))
      (fun hca => hca.elim (fun hc => Or.inr (Or.inr hc)) Or.inl))

theorem or_iff_left {b a : Prop} (hb : Not b) : Iff (Or a b) a :=
  Iff.intro (fun h => h.elim (fun ha => ha) (fun b => False.elim (hb b))) Or.inl

theorem or_iff_right {a b : Prop} (ha : Not a) : Iff (Or a b) b :=
  Iff.intro (fun h => h.elim (fun a => False.elim (ha a)) (fun hb => hb)) Or.inr

theorem imp_or_left_iff_true {P Q : Prop} : Iff (P → Or P Q) True :=
  Iff.intro (fun _ => True.intro) (fun _ => Or.inl)

theorem imp_or_right_iff_true {P Q : Prop} : Iff (Q → Or P Q) True :=
  Iff.intro (fun _ => True.intro) (fun _ => Or.inr)

/-! ## Distribution -/

theorem not_imp_of_and_not {a b : Prop} : And a (Not b) → Not (a → b) :=
  fun h f => h.right (f h.left)

theorem imp_and {b c : Prop} {α : Sort u} :
  Iff (α → And b c) (And (α → b) (α → c)) :=
  Iff.intro (fun f => And.intro (fun a => (f a).left) (fun a => (f a).right))
    (fun h a => And.intro (h.left a) (h.right a))

theorem not_and' {a b : Prop} : Iff (Not (And a b)) (b → Not a) :=
  Iff.intro (fun h hb ha => h (And.intro ha hb)) (fun h hab => h hab.right hab.left)

theorem and_or_left {a b c : Prop} : Iff (And a (Or b c)) (Or (And a b) (And a c)) :=
  Iff.intro (fun h => h.right.elim
      (fun hb => Or.inl (And.intro h.left hb)) (fun hc => Or.inr (And.intro h.left hc)))
    (fun h => h.elim (And.imp_right Or.inl) (And.imp_right Or.inr))

theorem or_and_right {a b c : Prop} : Iff (And (Or a b) c) (Or (And a c) (And b c)) :=
  Iff.intro (fun h => h.left.elim
      (fun ha => Or.inl (And.intro ha h.right)) (fun hb => Or.inr (And.intro hb h.right)))
    (fun h => h.elim (And.imp_left Or.inl) (And.imp_left Or.inr))

theorem or_and_left {a b c : Prop} : Iff (Or a (And b c)) (And (Or a b) (Or a c)) :=
  Iff.intro (fun h => h.elim (fun ha => And.intro (Or.inl ha) (Or.inl ha)) (And.imp Or.inr Or.inr))
    (fun h => h.left.elim Or.inl
      (fun hb => h.right.elim Or.inl (fun hc => Or.inr (And.intro hb hc))))

theorem and_or_right {a b c : Prop} : Iff (Or (And a b) c) (And (Or a c) (Or b c)) :=
  Iff.intro (fun h => h.elim (And.imp Or.inl Or.inl) (fun hc => And.intro (Or.inr hc) (Or.inr hc)))
    (fun h => h.left.elim
      (fun ha => h.right.elim (fun hb => Or.inl (And.intro ha hb)) Or.inr) Or.inr)

theorem or_imp {a b c : Prop} : Iff (Or a b → c) (And (a → c) (b → c)) :=
  Iff.intro (fun f => And.intro (fun ha => f (Or.inl ha)) (fun hb => f (Or.inr hb)))
    (fun h hab => hab.elim h.left h.right)

theorem not_or {p q : Prop} : Iff (Not (Or p q)) (And (Not p) (Not q)) :=
  or_imp

theorem not_and_of_not_or_not {a b : Prop} (h : Or (Not a) (Not b)) : Not (And a b) :=
  fun hab => h.elim (fun ha => ha hab.left) (fun hb => hb hab.right)

/-! ## Quantifiers -/

theorem forall_imp {α : Sort u} {p q : α → Prop} (h : ∀ (a : α), p a → q a) :
  (∀ (a : α), p a) → ∀ (a : α), q a :=
  fun hp a => h a (hp a)

theorem forall_exists_index {α : Sort u} {p : α → Prop} {q : (Exists p) → Prop} :
  Iff (∀ (h : Exists p), q h) (∀ (x : α) (h : p x), q (Exists.intro x h)) :=
  Iff.intro (fun f x h => f (Exists.intro x h)) (fun f ex => ex.elim f)

theorem Exists.imp {α : Sort u} {p q : α → Prop} (h : ∀ (a : α), p a → q a) :
  (Exists p) → Exists fun a => q a :=
  fun ex => ex.elim (fun a ha => Exists.intro a (h a ha))

theorem Exists.imp'.{u, v} {α : Sort v} {p : α → Prop} {β : Sort u} {q : β → Prop} (f : α → β)
  (hpq : ∀ (a : α), p a → q (f a)) : (Exists p) → Exists q :=
  fun ex => ex.elim (fun a ha => Exists.intro (f a) (hpq a ha))

theorem exists_imp {α : Sort u} {p : α → Prop} {b : Prop} :
  Iff ((Exists p) → b) (∀ (x : α), p x → b) :=
  Iff.intro (fun f x hx => f (Exists.intro x hx)) (fun f ex => ex.elim f)

theorem exists₂_imp {α : Sort u} {p : α → Prop} {b : Prop} {P : (x : α) → p x → Prop} :
  Iff ((Exists fun x => Exists fun h => P x h) → b) (∀ (x : α) (h : p x), P x h → b) :=
  Iff.intro (fun f x h hx => f (Exists.intro x (Exists.intro h hx)))
    (fun f ex => ex.elim (fun x inner => inner.elim (f x)))

theorem exists_prop_congr {p p' : Prop} {q q' : p → Prop} (hq : ∀ (h : p), Iff (q h) (q' h))
  (hp : Iff p p') : Iff (Exists q) (Exists fun h => q' (hp.mpr h)) :=
  Iff.intro
    (fun ex => ex.elim (fun h hq' => Exists.intro (hp.mp h) ((hq h).mp hq')))
    (fun ex => ex.elim (fun h hq' => Exists.intro (hp.mpr h) ((hq _).mpr hq')))

theorem exists_prop_of_true {p : Prop} {q : p → Prop} (h : p) : Iff (Exists fun h' => q h') (q h) :=
  Iff.intro (fun ex => ex.elim (fun _ hq => hq)) (fun hq => Exists.intro h hq)

theorem exists_true_left {p : True → Prop} : Iff (Exists p) (p True.intro) :=
  exists_prop_of_true True.intro

theorem forall_congr' {α : Sort u} {p q : α → Prop} (h : ∀ (a : α), Iff (p a) (q a)) :
  Iff (∀ (a : α), p a) (∀ (a : α), q a) :=
  Iff.intro (forall_imp (fun a => (h a).mp)) (forall_imp (fun a => (h a).mpr))

theorem exists_congr {α : Sort u} {p q : α → Prop} (h : ∀ (a : α), Iff (p a) (q a)) :
  Iff (Exists p) (Exists q) :=
  Iff.intro (Exists.imp fun a => (h a).mp) (Exists.imp fun a => (h a).mpr)

theorem forall₂_congr.{u, v} {α : Sort u} {β : α → Sort v} {p q : (a : α) → β a → Prop}
  (h : ∀ (a : α) (b : β a), Iff (p a b) (q a b)) :
  Iff (∀ (a : α) (b : β a), p a b) (∀ (a : α) (b : β a), q a b) :=
  forall_congr' fun a => forall_congr' (h a)

theorem exists₂_congr.{u, v} {α : Sort u} {β : α → Sort v} {p q : (a : α) → β a → Prop}
  (h : ∀ (a : α) (b : β a), Iff (p a b) (q a b)) :
  Iff (Exists fun a => Exists fun b => p a b) (Exists fun a => Exists fun b => q a b) :=
  exists_congr fun a => exists_congr (h a)

theorem forall₃_congr.{u, v, w} {α : Sort u} {β : α → Sort v} {γ : (a : α) → β a → Sort w}
  {p q : (a : α) → (b : β a) → γ a b → Prop}
  (h : ∀ (a : α) (b : β a) (c : γ a b), Iff (p a b c) (q a b c)) :
  Iff (∀ (a : α) (b : β a) (c : γ a b), p a b c) (∀ (a : α) (b : β a) (c : γ a b), q a b c) :=
  forall_congr' fun a => forall₂_congr (h a)

theorem exists₃_congr.{u, v, w} {α : Sort u} {β : α → Sort v} {γ : (a : α) → β a → Sort w}
  {p q : (a : α) → (b : β a) → γ a b → Prop}
  (h : ∀ (a : α) (b : β a) (c : γ a b), Iff (p a b c) (q a b c)) :
  Iff (Exists fun a => Exists fun b => Exists fun c => p a b c)
    (Exists fun a => Exists fun b => Exists fun c => q a b c) :=
  exists_congr fun a => exists₂_congr (h a)

theorem forall₄_congr.{u, v, w, s} {α : Sort u} {β : α → Sort v}
  {γ : (a : α) → β a → Sort w} {δ : (a : α) → (b : β a) → γ a b → Sort s}
  {p q : (a : α) → (b : β a) → (c : γ a b) → δ a b c → Prop}
  (h : ∀ (a : α) (b : β a) (c : γ a b) (d : δ a b c), Iff (p a b c d) (q a b c d)) :
  Iff (∀ (a : α) (b : β a) (c : γ a b) (d : δ a b c), p a b c d)
    (∀ (a : α) (b : β a) (c : γ a b) (d : δ a b c), q a b c d) :=
  forall_congr' fun a => forall₃_congr (h a)

theorem exists₄_congr.{u, v, w, s} {α : Sort u} {β : α → Sort v}
  {γ : (a : α) → β a → Sort w} {δ : (a : α) → (b : β a) → γ a b → Sort s}
  {p q : (a : α) → (b : β a) → (c : γ a b) → δ a b c → Prop}
  (h : ∀ (a : α) (b : β a) (c : γ a b) (d : δ a b c), Iff (p a b c d) (q a b c d)) :
  Iff (Exists fun a => Exists fun b => Exists fun c => Exists fun d => p a b c d)
    (Exists fun a => Exists fun b => Exists fun c => Exists fun d => q a b c d) :=
  exists_congr fun a => exists₃_congr (h a)

theorem forall₅_congr.{u, v, w, s, t} {α : Sort u} {β : α → Sort v}
  {γ : (a : α) → β a → Sort w} {δ : (a : α) → (b : β a) → γ a b → Sort s}
  {ε : (a : α) → (b : β a) → (c : γ a b) → δ a b c → Sort t}
  {p q : (a : α) → (b : β a) → (c : γ a b) → (d : δ a b c) → ε a b c d → Prop}
  (h :
    ∀ (a : α) (b : β a) (c : γ a b) (d : δ a b c) (e : ε a b c d),
      Iff (p a b c d e) (q a b c d e)) :
  Iff (∀ (a : α) (b : β a) (c : γ a b) (d : δ a b c) (e : ε a b c d), p a b c d e)
    (∀ (a : α) (b : β a) (c : γ a b) (d : δ a b c) (e : ε a b c d), q a b c d e) :=
  forall_congr' fun a => forall₄_congr (h a)

theorem exists₅_congr.{u, v, w, s, t} {α : Sort u} {β : α → Sort v}
  {γ : (a : α) → β a → Sort w} {δ : (a : α) → (b : β a) → γ a b → Sort s}
  {ε : (a : α) → (b : β a) → (c : γ a b) → δ a b c → Sort t}
  {p q : (a : α) → (b : β a) → (c : γ a b) → (d : δ a b c) → ε a b c d → Prop}
  (h :
    ∀ (a : α) (b : β a) (c : γ a b) (d : δ a b c) (e : ε a b c d),
      Iff (p a b c d e) (q a b c d e)) :
  Iff
    (Exists fun a =>
      Exists fun b => Exists fun c => Exists fun d => Exists fun e => p a b c d e)
    (Exists fun a =>
      Exists fun b => Exists fun c => Exists fun d => Exists fun e => q a b c d e) :=
  exists_congr fun a => exists₄_congr (h a)

theorem not_exists {α : Sort u} {p : α → Prop} :
  Iff (Not (Exists p)) (∀ (x : α), Not (p x)) :=
  exists_imp

theorem forall_not_of_not_exists {α : Sort u} {p : α → Prop} (h : Not (Exists p))
  (x : α) : Not (p x) :=
  not_exists.mp h x

theorem not_exists_of_forall_not {α : Sort u} {p : α → Prop} (h : ∀ (x : α), Not (p x)) :
  Not (Exists p) :=
  not_exists.mpr h

theorem forall_and {α : Sort u} {p q : α → Prop} :
  Iff (∀ (x : α), And (p x) (q x)) (And (∀ (x : α), p x) (∀ (x : α), q x)) :=
  Iff.intro (fun h => And.intro (fun x => (h x).left) (fun x => (h x).right))
    (fun h x => And.intro (h.left x) (h.right x))

theorem exists_or {α : Sort u} {p q : α → Prop} :
  Iff (Exists fun x => Or (p x) (q x)) (Or (Exists p) (Exists q)) :=
  Iff.intro (fun ex => ex.elim (fun x hx => hx.elim
        (fun hp => Or.inl (Exists.intro x hp)) (fun hq => Or.inr (Exists.intro x hq))))
    (fun h => h.elim (Exists.imp fun _ hp => Or.inl hp) (Exists.imp fun _ hq => Or.inr hq))

theorem exists_false {α : Sort u} : Not (Exists fun _a : α => False) :=
  fun ex => ex.elim (fun _ h => h)

theorem not_forall_of_exists_not {α : Sort u} {p : α → Prop} :
  (Exists fun x => Not (p x)) → Not (∀ (x : α), p x) :=
  fun ex h => ex.elim (fun x hn => hn (h x))

theorem forall_eq {α : Sort u} {p : α → Prop} {a' : α} : Iff (∀ (a : α), Eq a a' → p a) (p a') :=
  Iff.intro (fun f => f a' rfl) (fun hp _ e => Eq.subst e.symm hp)

theorem forall_eq' {α : Sort u} {p : α → Prop} {a' : α} : Iff (∀ (a : α), Eq a' a → p a) (p a') :=
  Iff.intro (fun f => f a' rfl) (fun hp _ e => Eq.subst e hp)

theorem exists_eq : Exists fun a => Eq a a' :=
  Exists.intro a' rfl

theorem exists_eq' : Exists fun a => Eq a' a :=
  Exists.intro a' rfl

theorem exists_eq_left {α : Sort u} {p : α → Prop} {a' : α} :
  Iff (Exists fun a => And (Eq a a') (p a)) (p a') :=
  Iff.intro (fun ex => ex.elim (fun _ h => Eq.subst h.left h.right))
    (fun hp => Exists.intro a' (And.intro rfl hp))

theorem exists_eq_right {α : Sort u} {p : α → Prop} {a' : α} :
  Iff (Exists fun a => And (p a) (Eq a a')) (p a') :=
  Iff.intro (fun ex => ex.elim (fun _ h => Eq.subst h.right h.left))
    (fun hp => Exists.intro a' (And.intro hp rfl))

theorem exists_and_left {α : Sort u} {p : α → Prop} {b : Prop} :
  Iff (Exists fun x => And b (p x)) (And b (Exists p)) :=
  Iff.intro (fun ex => ex.elim (fun x h => And.intro h.left (Exists.intro x h.right)))
    (fun h => h.right.elim (fun x hp => Exists.intro x (And.intro h.left hp)))

theorem exists_and_right {α : Sort u} {p : α → Prop} {b : Prop} :
  Iff (Exists fun x => And (p x) b) (And (Exists p) b) :=
  Iff.intro (fun ex => ex.elim (fun x h => And.intro (Exists.intro x h.left) h.right))
    (fun h => h.left.elim (fun x hp => Exists.intro x (And.intro hp h.right)))

theorem exists_eq_left' {α : Sort u} {p : α → Prop} {a' : α} :
  Iff (Exists fun a => And (Eq a' a) (p a)) (p a') :=
  Iff.intro (fun ex => ex.elim (fun _ h => Eq.subst h.left.symm h.right))
    (fun hp => Exists.intro a' (And.intro rfl hp))

theorem exists_eq_right' {α : Sort u} {p : α → Prop} {a' : α} :
  Iff (Exists fun a => And (p a) (Eq a' a)) (p a') :=
  Iff.intro (fun ex => ex.elim (fun _ h => Eq.subst h.right.symm h.left))
    (fun hp => Exists.intro a' (And.intro hp rfl))

theorem exists_prop_eq {α : Sort u} {a' : α} {p : (a : α) → Eq a a' → Prop} :
  Iff (Exists fun a => Exists fun h => p a h) (p a' rfl) :=
  Iff.intro
    (fun ex => ex.elim (fun _ e => e.elim (fun h hp =>
      Eq.rec (motive := fun x eq => p x eq.symm → p a' rfl) (fun v => v) h.symm hp)))
    (fun h => Exists.intro a' (Exists.intro rfl h))

theorem exists_prop_eq' {α : Sort u} {a' : α} {p : (a : α) → Eq a' a → Prop} :
  Iff (Exists fun a => Exists fun h => p a h) (p a' rfl) :=
  Iff.intro
    (fun ex => ex.elim (fun _ e => e.elim (fun h hp =>
      Eq.rec (motive := fun x eq => p x eq → p a' rfl) (fun v => v) h hp)))
    (fun h => Exists.intro a' (Exists.intro rfl h))

theorem forall_eq_or_imp {α : Sort u} {a' : α} {P Q : α → Prop} :
  Iff (∀ (a : α), Or (Eq a a') (Q a) → P a) (And (P a') (∀ (a : α), Q a → P a)) :=
  Iff.intro (fun f => And.intro (f a' (Or.inl rfl)) (fun a hq => f a (Or.inr hq)))
    (fun h a e => e.elim (fun eq => Eq.subst eq.symm h.left) (h.right a))

theorem forall_eq_or_imp' {α : Sort u} {P Q : α → Prop} {a' : α} :
  Iff (∀ (a : α), Or (Eq a' a) (Q a) → P a) (And (P a') (∀ (a : α), Q a → P a)) :=
  Iff.intro (fun f => And.intro (f a' (Or.inl rfl)) (fun a hq => f a (Or.inr hq)))
    (fun h a e => e.elim (fun eq => Eq.subst eq h.left) (h.right a))

theorem forall_or_eq_imp {α : Sort u} {a' : α} {P Q : α → Prop} :
  Iff (∀ (a : α), Or (Q a) (Eq a a') → P a) (And (∀ (a : α), Q a → P a) (P a')) :=
  Iff.intro (fun f => And.intro (fun a hq => f a (Or.inl hq)) (f a' (Or.inr rfl)))
    (fun h a e => e.elim (h.left a) (fun eq => Eq.subst eq.symm h.right))

theorem forall_or_eq_imp' {α : Sort u} {a' : α} {P Q : α → Prop} :
  Iff (∀ (a : α), Or (Q a) (Eq a' a) → P a) (And (∀ (a : α), Q a → P a) (P a')) :=
  Iff.intro (fun f => And.intro (fun a hq => f a (Or.inl hq)) (f a' (Or.inr rfl)))
    (fun h a e => e.elim (h.left a) (fun eq => Eq.subst eq h.right))

theorem exists_eq_or_imp {α : Sort u} {p q : α → Prop} {a' : α} :
  Iff (Exists fun a => And (Or (Eq a a') (q a)) (p a))
    (Or (p a') (Exists fun a => And (q a) (p a))) :=
  Iff.intro
    (fun ex => ex.elim (fun a h => h.left.elim (fun e => Or.inl (Eq.subst e h.right))
      (fun hq => Or.inr (Exists.intro a (And.intro hq h.right)))))
    (fun h => h.elim (fun hp => Exists.intro a' (And.intro (Or.inl rfl) hp))
      (Exists.imp fun _ h' => And.intro (Or.inr h'.left) h'.right))

theorem exists_eq_or_imp' {α : Sort u} {p q : α → Prop} {a' : α} :
  Iff (Exists fun a => And (Or (Eq a' a) (q a)) (p a))
    (Or (p a') (Exists fun a => And (q a) (p a))) :=
  Iff.intro
    (fun ex => ex.elim (fun a h => h.left.elim (fun e => Or.inl (Eq.subst e.symm h.right))
      (fun hq => Or.inr (Exists.intro a (And.intro hq h.right)))))
    (fun h => h.elim (fun hp => Exists.intro a' (And.intro (Or.inl rfl) hp))
      (Exists.imp fun _ h' => And.intro (Or.inr h'.left) h'.right))

theorem exists_or_eq_imp {α : Sort u} {p q : α → Prop} {a' : α} :
  Iff (Exists fun a => And (Or (q a) (Eq a a')) (p a))
    (Or (Exists fun a => And (q a) (p a)) (p a')) :=
  Iff.intro
    (fun ex => ex.elim (fun a h => h.left.elim
      (fun hq => Or.inl (Exists.intro a (And.intro hq h.right))) (fun e => Or.inr (Eq.subst e h.right))))
    (fun h => h.elim (Exists.imp fun _ h' => And.intro (Or.inl h'.left) h'.right)
      (fun hp => Exists.intro a' (And.intro (Or.inr rfl) hp)))

theorem exists_or_eq_imp' {α : Sort u} {p q : α → Prop} {a' : α} :
  Iff (Exists fun a => And (Or (q a) (Eq a' a)) (p a))
    (Or (Exists fun a => And (q a) (p a)) (p a')) :=
  Iff.intro
    (fun ex => ex.elim (fun a h => h.left.elim
      (fun hq => Or.inl (Exists.intro a (And.intro hq h.right))) (fun e => Or.inr (Eq.subst e.symm h.right))))
    (fun h => h.elim (Exists.imp fun _ h' => And.intro (Or.inl h'.left) h'.right)
      (fun hp => Exists.intro a' (And.intro (Or.inr rfl) hp)))

theorem exists_eq_right_right {α : Sort u} {p q : α → Prop} {a' : α} :
  Iff (Exists fun a => And (p a) (And (q a) (Eq a a'))) (And (p a') (q a')) :=
  Iff.intro (fun ex => ex.elim (fun _ h => And.intro
      (Eq.subst h.right.right h.left) (Eq.subst h.right.right h.right.left)))
    (fun h => Exists.intro a' (And.intro h.left (And.intro h.right rfl)))

theorem exists_eq_right_right' {α : Sort u} {p q : α → Prop} {a' : α} :
  Iff (Exists fun a => And (p a) (And (q a) (Eq a' a))) (And (p a') (q a')) :=
  Iff.intro (fun ex => ex.elim (fun _ h => And.intro
      (Eq.subst h.right.right.symm h.left) (Eq.subst h.right.right.symm h.right.left)))
    (fun h => Exists.intro a' (And.intro h.left (And.intro h.right rfl)))

theorem exists_or_eq_left {α : Sort u} (y : α) (p : α → Prop) :
  Exists fun x => Or (Eq x y) (p x) :=
  Exists.intro y (Or.inl rfl)

theorem exists_or_eq_right {α : Sort u} (y : α) (p : α → Prop) :
  Exists fun x => Or (p x) (Eq x y) :=
  Exists.intro y (Or.inr rfl)

theorem exists_or_eq_left' {α : Sort u} (y : α) (p : α → Prop) :
  Exists fun x => Or (Eq y x) (p x) :=
  Exists.intro y (Or.inl rfl)

theorem exists_or_eq_right' {α : Sort u} (y : α) (p : α → Prop) :
  Exists fun x => Or (p x) (Eq y x) :=
  Exists.intro y (Or.inr rfl)

theorem exists_prop {b a : Prop} : Iff (Exists fun _h : a => b) (And a b) :=
  Iff.intro (fun ex => ex.elim (fun ha hb => And.intro ha hb))
    (fun h => Exists.intro h.left h.right)

theorem exists_idem {P : Prop} (f : P → P → Prop) :
  Iff (Exists fun p₁ => Exists fun p₂ => f p₁ p₂) (Exists fun p => f p p) :=
  Iff.intro (fun ex => ex.elim (fun p outer => outer.elim (fun _ hx => Exists.intro p hx)))
    (fun ex => ex.elim (fun p hx => Exists.intro p (Exists.intro p hx)))

theorem exists_apply_eq_apply.{u, v} {α : Sort v} {β : Sort u} (f : α → β) (a' : α) :
  Exists fun a => Eq (f a) (f a') :=
  Exists.intro a' rfl

theorem forall_prop_of_true {p : Prop} {q : p → Prop} (h : p) : Iff (∀ (h' : p), q h') (q h) :=
  Iff.intro (fun f => f h) (fun hq _ => hq)

theorem forall_comm.{u, v} {α : Sort v} {β : Sort u} {p : α → β → Prop} :
  Iff (∀ (a : α) (b : β), p a b) (∀ (b : β) (a : α), p a b) :=
  Iff.intro (fun f b a => f a b) (fun f a b => f b a)

theorem exists_comm.{u, v} {α : Sort v} {β : Sort u} {p : α → β → Prop} :
  Iff (Exists fun a => Exists fun b => p a b) (Exists fun b => Exists fun a => p a b) :=
  Iff.intro (fun ex => ex.elim (fun a e => e.elim (fun b h => Exists.intro b (Exists.intro a h))))
    (fun ex => ex.elim (fun b e => e.elim (fun a h => Exists.intro a (Exists.intro b h))))

theorem forall_apply_eq_imp_iff.{u, v} {α : Sort v} {β : Sort u} {f : α → β} {p : β → Prop} :
  Iff (∀ (b : β) (a : α), Eq (f a) b → p b) (∀ (a : α), p (f a)) :=
  Iff.intro (fun h a => h (f a) a rfl) (fun h _ a e => Eq.subst e (h a))

theorem forall_eq_apply_imp_iff.{u, v} {α : Sort v} {β : Sort u} {f : α → β} {p : β → Prop} :
  Iff (∀ (b : β) (a : α), Eq b (f a) → p b) (∀ (a : α), p (f a)) :=
  Iff.intro (fun h a => h (f a) a rfl) (fun h _ a e => Eq.subst e.symm (h a))

theorem forall_apply_eq_imp_iff₂.{u, v} {α : Sort v} {β : Sort u} {f : α → β} {p : α → Prop}
  {q : β → Prop} : Iff (∀ (b : β) (a : α), p a → Eq (f a) b → q b) (∀ (a : α), p a → q (f a)) :=
  Iff.intro (fun h a ha => h (f a) a ha rfl) (fun h _ a ha e => Eq.subst e (h a ha))

theorem forall_prop_of_false {p : Prop} {q : p → Prop} (hn : Not p) : Iff (∀ (h' : p), q h') True :=
  Iff.intro (fun _ => True.intro) (fun _ hp => False.elim (hn hp))

theorem and_exists_self (P : Prop) (Q : P → Prop) :
  Iff (And P (Exists fun p => Q p)) (Exists fun p => Q p) :=
  Iff.intro And.right (fun ex => ex.elim (fun p h => And.intro p (Exists.intro p h)))

theorem exists_and_self (P : Prop) (Q : P → Prop) :
  Iff (And (Exists fun p => Q p) P) (Exists fun p => Q p) :=
  Iff.intro And.left (fun ex => ex.elim (fun p h => And.intro (Exists.intro p h) p))

theorem forall_self_imp (P : Prop) (Q : P → Prop) : Iff (∀ (p : P), P → Q p) (∀ (p : P), Q p) :=
  Iff.intro (fun h p => h p p) (fun h p _ => h p)

theorem forall_or_imp_or_self_right_right {α : Sort u} {P Q R : α → Prop} :
  Iff (∀ (a : α), Or (P a) (Q a) → Or (R a) (Q a)) (∀ (a : α), P a → Or (R a) (Q a)) :=
  Iff.intro (fun f a hp => f a (Or.inl hp)) (fun f a h => h.elim (f a) Or.inr)

theorem forall_or_imp_or_self_right_left {α : Sort u} {P Q R : α → Prop} :
  Iff (∀ (a : α), Or (P a) (Q a) → Or (Q a) (R a)) (∀ (a : α), P a → Or (Q a) (R a)) :=
  Iff.intro (fun f a hp => f a (Or.inl hp)) (fun f a h => h.elim (f a) Or.inl)

theorem forall_or_imp_or_self_left_right {α : Sort u} {P Q R : α → Prop} :
  Iff (∀ (a : α), Or (Q a) (P a) → Or (R a) (Q a)) (∀ (a : α), P a → Or (R a) (Q a)) :=
  Iff.intro (fun f a hp => f a (Or.inr hp)) (fun f a h => h.elim Or.inr (f a))

theorem forall_or_imp_or_self_left_left {α : Sort u} {P Q R : α → Prop} :
  Iff (∀ (a : α), Or (Q a) (P a) → Or (Q a) (R a)) (∀ (a : α), P a → Or (Q a) (R a)) :=
  Iff.intro (fun f a hp => f a (Or.inr hp)) (fun f a h => h.elim Or.inl (f a))

theorem peirce' {a : Prop} (H : ∀ (b : Prop), (a → b) → a) : a :=
  H a (fun ha => ha)

end Omega

port_proof cast_cast
port_proof eq_mp_eq_cast by_reflexivity
port_proof eq_mpr_eq_cast by_reflexivity
port_proof exists_const
port_proof exists_prop'
port_proof forall_const
port_proof ne_of_apply_ne
port_proof nonempty_prop
port_proof Exists.nonempty

port_definition decidable_of_iff with_native_code
port_definition decidable_of_iff' with_native_code
