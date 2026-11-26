module
public import Lean
import Lean.Replay
import all Lean.Util.CollectAxioms
import all Init.Data.Array.Basic
import all Init.Prelude
import all Init.Data.Slice.Operations
import all Init.Data.Iterators.Basic
import all Init.Grind.Ring.Envelope

public section

/-!
Inventory of named public declarations in every installed module of the pinned `Init` library,
including modules importable separately from its umbrella. Constructors, recursors and other
named generated declarations are included. Each defining module has its own row for a shared name. The inventory omits syntax,
aliases and private or internal names. Each row gives the original implementation's transitive
axioms and the defining module, if any, of its strict `Omega.` counterpart. The strict library
audit checks the corresponding types, implementations and strict axiom closures.

Run from the project root after building the strict basis.
`lean --run src/OmegaChecks/InitInventory.lean .lake/build/omega-strict/lib/lean output.json`.
-/

open Lean

/- Each reduction accepts an implementation of precisely the pinned public type.
Its result implements the named axiom. Both types are elaborated without
referring to the values of the upstream constants. -/
namespace OmegaChecks.InitBoundaries
universe u

/-- The official option selector returns a value on every inhabited input.
Lifting a sort into a type also covers propositional inputs to choice. -/
def choiceFromOptionPresence (select : type_of% (@Option.choice.{u}))
    (present : ∀ (α : Type u), Nonempty α → (select α).isSome) :
    type_of% (@Classical.choice.{u}) := by
  intro α h
  have nonempty : Nonempty (PLift α) := h.elim fun a => ⟨⟨a⟩⟩
  exact ((select (PLift α)).get (present _ nonempty)).down

def choiceFromChoose (select : type_of% (@Classical.choose.{u})) : type_of% (@Classical.choice.{u}) :=
  fun {α} inhabited => @select α (fun _ => True) (inhabited.elim fun x => ⟨x, trivial⟩)

def choiceFromExistsChoose (select : type_of% (@Exists.choose.{u})) : type_of% (@Classical.choice.{u}) :=
  choiceFromChoose (@select)

def choiceFromEpsilon (select : type_of% (@Classical.epsilon.{u})) : type_of% (@Classical.choice.{u}) :=
  fun {α} inhabited => @select α inhabited (fun _ => True)

def choiceFromDescription (select : type_of% (@Classical.indefiniteDescription.{u})) :
    type_of% (@Classical.choice.{u}) :=
  fun {α} inhabited => (@select α (fun _ => True) (inhabited.elim fun x => ⟨x, trivial⟩)).val

def choiceFromInhabited (select : type_of% (@Classical.inhabited_of_nonempty.{u})) :
    type_of% (@Classical.choice.{u}) :=
  fun {α} inhabited => (@select α inhabited).default

theorem propextFromIffIffEq (equiv : type_of% (@iff_iff_eq)) : type_of% (@propext) :=
  fun {a b} h => (@equiv a b).mp h

theorem propextFromEqIffIff (equiv : type_of% (@eq_iff_iff)) : type_of% (@propext) :=
  fun {a b} h => (@equiv a b).mpr h

theorem propextFromPropIntro (intro : type_of% (@Eq.propIntro)) : type_of% (@propext) :=
  fun {a b} h => @intro a b h.mp h.mpr

def choiceFromOfNonempty (select : type_of% (@Classical.ofNonempty.{u})) :
    type_of% (@Classical.choice.{u}) :=
  fun {α} inhabited => @select α inhabited

def choiceFromInhabitedOfExists (select : type_of% (@Classical.inhabited_of_exists.{u})) :
    type_of% (@Classical.choice.{u}) :=
  fun {α} inhabited => (@select α (fun _ => True) (inhabited.elim fun x => ⟨x, trivial⟩)).default

def choiceFromStrongDescription (select : type_of% (@Classical.strongIndefiniteDescription.{u})) :
    type_of% (@Classical.choice.{u}) :=
  fun {α} inhabited => (@select α (fun _ => True) inhabited).val

def choiceFromTypeDecidable (decideType : type_of% (@Classical.typeDecidable.{u})) :
    type_of% (@Classical.choice.{u}) :=
  fun {α} inhabited => match decideType α with
    | .inl value => value
    | .inr empty => False.elim (inhabited.elim empty)

theorem propextFromIffSubst (subst : type_of% (@Iff.subst)) : type_of% (@propext) :=
  fun {a b} eqv => @subst a b (Eq a) eqv rfl

theorem propextFromPropextIff (equiv : type_of% (@propext_iff)) : type_of% (@propext) :=
  fun {a b} h => (@equiv a b).mpr h

theorem propextFromPropComplete (complete : type_of% (@Classical.propComplete)) : type_of% (@propext) := by
  intro a b hab
  rcases complete a with ha | ha <;> rcases complete b with hb | hb
  · exact ha.trans hb.symm
  · exact False.elim (hb.mp (hab.mp (ha.mpr trivial)))
  · exact False.elim (ha.mp (hab.mpr (hb.mpr trivial)))
  · exact ha.trans hb.symm

theorem propextFromIteIffLeft (h : type_of% (@ite_iff_left_iff)) : type_of% (@propext) :=
  fun {a b} eqv => (@h False (.isFalse id) b a).mp eqv id

theorem propextFromIteIffRight (h : type_of% (@ite_iff_right_iff)) : type_of% (@propext) :=
  fun {a b} eqv => (@h True (.isTrue trivial) a b).mp eqv trivial

theorem propextFromLeftIffIte (h : type_of% (@left_iff_ite_iff)) : type_of% (@propext) :=
  fun {a b} eqv => (@h False (.isFalse id) a b).mp eqv id

theorem propextFromRightIffIte (h : type_of% (@right_iff_ite_iff)) : type_of% (@propext) :=
  fun {a b} eqv => (@h True (.isTrue trivial) b a).mp eqv trivial

theorem propextFromGrindIffEq (h : type_of% (@Lean.Grind.iff_eq)) : type_of% (@propext) :=
  fun {a b} eqv => (h a b).mp eqv

universe v w z

def choiceFromFix (fix : type_of% (@WellFounded.extrinsicFix.{u,v})) : type_of% (@Classical.choice.{v}) :=
  fun {α} inhabited => @fix PUnit.{u} (fun _ => α) (fun _ => inhabited) (fun _ _ => True)
    (fun x next => next x trivial) PUnit.unit

def choiceFromFix₂ (fix : type_of% (@WellFounded.extrinsicFix₂.{u,v,w})) : type_of% (@Classical.choice.{w}) :=
  fun {α} inhabited => @fix PUnit.{u} (fun _ => PUnit.{v}) (fun _ _ => α) (fun _ _ => inhabited)
    (fun _ _ => True) (fun x y next => next x y trivial) PUnit.unit PUnit.unit

def choiceFromFix₃ (fix : type_of% (@WellFounded.extrinsicFix₃.{u,v,w,z})) : type_of% (@Classical.choice.{z}) :=
  fun {α} inhabited => @fix PUnit.{u} (fun _ => PUnit.{v}) (fun _ _ => PUnit.{w}) (fun _ _ _ => α)
    (fun _ _ _ => inhabited) (fun _ _ => True) (fun x y z next => next x y z trivial)
    PUnit.unit PUnit.unit PUnit.unit

def sorryAxFromUnsafeCast (castAny : type_of% (@unsafeCast.{u,v})) : type_of% (@sorryAx.{v}) :=
  fun α _ => @castAny PUnit.{u} α PUnit.unit

def choiceFromLeftInv (leftInv : type_of% (@Lean.Grind.leftInv.{u,u+1})) : type_of% (@Classical.choice.{u}) :=
  fun {α} inhabited => @leftInv α (Option (PLift α)) (fun a => some ⟨a⟩)
    (fun _ _ h => congrArg PLift.down (Option.some.inj h)) inhabited none

def choiceFromRepeatM (loop : type_of% (@repeatM.{u,u})) : type_of% (@Classical.choice.{u}) :=
  fun {α} inhabited =>
    let wrapped : Nonempty (PLift α) := inhabited.elim (fun a => ⟨⟨a⟩⟩)
    (@loop (PLift (PUnit.{u})) Id inferInstance (PLift α) wrapped (fun x => Sum.inl x) ⟨PUnit.unit⟩).down

/- Specialize each range interface to a singleton. Its comparison expresses any proposition
and its size is one. Double negation is exactly what the zero-size law needs. -/
namespace FiniteMembership

/-- Any two elements of a type have either equal or unequal values. -/
def EqualityCases : Prop := ∀ {α : Type u} (a b : α), a = b ∨ a ≠ b

theorem ofListMember (branch : type_of% (@List.eq_or_ne_mem_of_mem.{u})) : EqualityCases.{u} := by
  intro α a b
  exact (branch (a := a) (b := b) (l := [a]) (.tail _ (.head _))).imp_right And.left

theorem ofArrayMember (branch : type_of% (@Array.eq_or_ne_mem_of_mem.{u})) : EqualityCases.{u} := by
  intro α a b
  have mem : a ∈ (#[a].push b) := ⟨.head _⟩
  exact (branch mem).imp_right And.left

theorem ofFirstListMember (split : type_of% (@List.eq_append_cons_of_mem.{u})) : EqualityCases.{u} := by
  intro α a b
  obtain ⟨before, after, eq, absent⟩ := split (a := a) (xs := [b,a]) (.tail _ (.head _))
  cases before with
  | nil => exact .inl (List.cons.inj eq).1.symm
  | cons c cs =>
    have same := (List.cons.inj eq).1
    exact .inr fun e => absent ((e.trans same) ▸ List.Mem.head _)

/-- Appending cannot change the first entry of a nonempty array. -/
private theorem pushKeepsHead {α : Type u} {acc : Array α} {a v : α}
    (h : acc.toList.head? = some v) : (acc.push a).toList.head? = some v := by
  cases acc with
  | mk l => cases l with
    | nil => cases h
    | cons c cs => exact h

private theorem appendKeepsHead {α : Type u} {xs ys : Array α} {v : α}
    (h : xs.toList.head? = some v) : (xs ++ ys).toList.head? = some v := by
  have loop (fuel j : Nat) (acc : Array α) (head : acc.toList.head? = some v) :
      (Array.foldlM.loop (m := Id) (fun a x => pure (a.push x)) ys ys.size
        (Nat.le_refl _) fuel j acc).run.toList.head? = some v := by
    induction fuel generalizing j acc with
    | zero =>
      unfold Array.foldlM.loop
      split <;> exact head
    | succ fuel ih =>
      unfold Array.foldlM.loop
      split
      · exact ih (j+1) _ (pushKeepsHead head)
      · exact head
  change (Array.foldl (fun a x => a.push x) xs ys).toList.head? = some v
  unfold Array.foldl Array.foldlM
  rw [dite_eq_left (Nat.le_refl _)]
  exact loop ys.size 0 xs h

theorem ofFirstArrayMember (split : type_of% (@Array.eq_push_append_of_mem.{u})) : EqualityCases.{u} := by
  intro α a b
  have mem : a ∈ #[b,a] := ⟨.tail _ (.head _)⟩
  obtain ⟨⟨before⟩, after, eq, absent⟩ := split mem
  have eqHead := congrArg (fun xs => xs.toList.head?) eq
  cases before with
  | nil => exact .inl (Option.some.inj (eqHead.trans (appendKeepsHead rfl))).symm
  | cons c cs =>
    have same : b = c := Option.some.inj (eqHead.trans (appendKeepsHead (pushKeepsHead rfl)))
    exact .inr fun e => absent ⟨(e.trans same) ▸ List.Mem.head _⟩

theorem ofRunDecomposition (split : type_of% (@List.eq_replicate_or_eq_replicate_append_cons.{u})) :
    EqualityCases.{u} := by
  intro α a b
  rcases split [a, b] with emp | ⟨n, c, eq, positive⟩ | ⟨n, c, d, rest, eq, positive, apart⟩
  · cases emp
  · cases n with
    | zero => cases positive
    | succ n => cases n with
      | zero => cases eq
      | succ n =>
        have heads := List.cons.inj eq
        exact .inl (heads.1.trans (List.cons.inj heads.2).1.symm)
  · cases n with
    | zero => cases positive
    | succ n => cases n with
      | zero =>
        have heads := List.cons.inj eq
        exact .inr fun h => apart (heads.1.symm.trans (h.trans (List.cons.inj heads.2).1))
      | succ n =>
        have heads := List.cons.inj eq
        exact .inl (heads.1.trans (List.cons.inj heads.2).1.symm)

theorem ofRunInduction (rec : type_of% (@List.replicateRecOn.{u})) : EqualityCases.{u} := by
  apply ofRunDecomposition
  intro α l
  apply rec l
  · exact .inl rfl
  · intro a n h
    exact .inr (.inl ⟨n, a, rfl, h⟩)
  · intro a b n l ne pos _
    exact .inr (.inr ⟨n, a, b, l, rfl, pos, ne⟩)

end FiniteMembership

namespace VectorExistence

private theorem appendOne (l : List α) (x : α) : (l.concat x).length = l.length + 1 := by
  induction l with
  | nil => rfl
  | cons a tail ih => exact congrArg Nat.succ ih
private def push (xs : Vector α n) (x : α) : Vector α (n+1) :=
  ⟨xs.toArray.push x, (appendOne xs.toArray.toList x).trans (congrArg Nat.succ xs.size_toArray)⟩
/-- The size proof in the official push operation is irrelevant to definitional equality. -/
def DecideSucc : Type 1 := ∀ {α : Type} {n : Nat} (P : Vector α (n+1) → Prop),
  [Decidable (∀ (x : α) (xs : Vector α n), ¬ P (push xs x))] → Decidable (∃ xs, P xs)
example : (type_of% (@Vector.instDecidableExistsVectorSucc.{0})) = DecideSucc := rfl
theorem emOfVectorSucc (existsDec : DecideSucc) (p : Prop) : p ∨ ¬p := by
  let goal := p ∨ ¬p
  have nn : ¬¬goal := fun ng => ng (.inr fun hp => ng (.inl hp))
  let reject : Decidable (∀ (_ : Unit) (_ : Vector Unit 0), ¬goal) :=
    .isFalse fun h => nn (h () ⟨#[], rfl⟩)
  cases @existsDec Unit 0 (fun _ => goal) reject with
  | isTrue yes => exact yes.elim fun _ hp => hp
  | isFalse no => exact (nn (fun hp => no ⟨⟨#[()], rfl⟩, hp⟩)).elim

end VectorExistence

theorem dneFromClosedRange (range : type_of% (@Std.Rxc.size_pos_iff_le.{0}))
    (p : Prop) (nn : ¬¬p) : p := by
  letI : LE Unit := ⟨fun _ _ => p⟩
  letI : Std.PRange.UpwardEnumerable Unit := ⟨fun _ => none, fun _ _ => none⟩
  letI : Std.Rxc.HasSize Unit := ⟨fun _ _ => 1⟩
  letI : Std.Rxc.LawfulHasSize Unit :=
    ⟨fun _ _ denied => (nn denied).elim, fun _ _ _ _ => rfl,
      fun _ _ _ _ impossible => nomatch impossible⟩
  exact (@range Unit _ _ _ _ () ()).mp (Nat.lt_succ_self 0)

theorem dneFromOpenRange (range : type_of% (@Std.Rxo.size_pos_iff_lt.{0}))
    (p : Prop) (nn : ¬¬p) : p := by
  letI : LT Unit := ⟨fun _ _ => p⟩
  letI : Std.PRange.UpwardEnumerable Unit := ⟨fun _ => none, fun _ _ => none⟩
  letI : Std.Rxo.HasSize Unit := ⟨fun _ _ => 1⟩
  letI : Std.Rxo.LawfulHasSize Unit :=
    ⟨fun _ _ denied => (nn denied).elim, fun _ _ _ _ => rfl,
      fun _ _ _ _ impossible => nomatch impossible⟩
  exact (@range Unit _ _ _ _ () ()).mp (Nat.lt_succ_self 0)

theorem excludedMiddleFromDNE (dne : ∀ p : Prop, ¬¬p → p) (p : Prop) : p ∨ ¬p :=
  dne _ fun neither => neither (.inr fun hp => neither (.inl hp))

namespace LexicographicOrder

/-- Lexicographic comparison of one-element sequences can represent any proposition. -/
private theorem singletonMiddle (caseSplit : ∀ p : Prop,
    letI : LT Unit := ⟨fun _ _ => p⟩
    ¬ ¬ (([()] : List Unit) < [()]) → ([()] : List Unit) < [()]) (p : Prop) : p ∨ ¬p := by
  apply excludedMiddleFromDNE _ p
  intro q nn
  letI : LT Unit := ⟨fun _ _ => q⟩
  have lt := caseSplit q (fun absent => nn (fun h => absent (List.Lex.rel h)))
  cases lt with
  | rel h => exact h
  | cons h => cases h

theorem ofListNotLE (law : type_of% (@List.not_le.{0})) : type_of% @Classical.em :=
  singletonMiddle fun p => @law Unit ⟨fun _ _ => p⟩ [()] [()] |>.mp

theorem ofArrayNotLE (law : type_of% (@Array.not_le.{0})) : type_of% @Classical.em :=
  singletonMiddle fun p => @law Unit ⟨fun _ _ => p⟩ #[()] #[()] |>.mp

theorem ofVectorNotLE (law : type_of% (@Vector.not_le.{0})) : type_of% @Classical.em :=
  singletonMiddle fun p => @law Unit 1 ⟨fun _ _ => p⟩ #v[()] #v[()] |>.mp

end LexicographicOrder

/-- The comparison from the upper Boolean point back to the lower point can encode any proposition. -/
theorem dneOfNotLT (notLT : type_of% (@Std.not_lt.{0})) (p : Prop) (nn : ¬¬p) : p := by
  let le (a b : Bool) : Prop := Bool.rec (motive := fun _ => Prop) True (Bool.rec (motive := fun _ => Prop) p True b) a
  letI : LE Bool := ⟨le⟩
  letI : LT Bool := ⟨fun a b => le a b ∧ ¬le b a⟩
  letI : Std.Total (α := Bool) (· ≤ ·) := ⟨fun a =>
    Bool.rec (motive := fun a => ∀ b, le a b ∨ le b a)
      (fun _ => Or.inl True.intro)
      (Bool.rec (motive := fun b => le true b ∨ le b true) (Or.inr True.intro) (Or.inl True.intro)) a⟩
  letI : Std.LawfulOrderLT Bool := ⟨fun _ _ => Iff.rfl⟩
  exact (@notLT Bool _ _ _ _ false true).mp (fun h => nn h.2)

theorem excludedMiddleOfNotLT (notLT : type_of% (@Std.not_lt.{0})) (p : Prop) : p ∨ ¬p :=
  excludedMiddleFromDNE (dneOfNotLT (@notLT)) p

/-- On a singleton both comparisons can express the same arbitrary proposition. -/
theorem excludedMiddleOfNotLTIff (notLT : type_of% (@Std.not_lt_iff_not_le_or_ge.{0}))
    (p : Prop) : p ∨ ¬p := by
  letI : LE Unit := ⟨fun _ _ => p⟩
  letI : LT Unit := ⟨fun _ _ => p ∧ ¬p⟩
  letI : Std.LawfulOrderLT Unit := ⟨fun _ _ => Iff.rfl⟩
  exact ((@notLT Unit _ _ _ () ()).mp (fun h => h.2 h.1)).elim Or.inr Or.inl

namespace GrindOrder

private def relation (p : Prop) (a b : Bool) : Prop :=
  Bool.rec (motive := fun _ => Prop) True (Bool.rec (motive := fun _ => Prop) p True b) a

/-- A linear preorder can encode an arbitrary proposition in its reverse comparison. -/
theorem excludedMiddleFromComparison
    (compare : type_of% (@Lean.Grind.Order.le_of_not_lt.{0})) (p : Prop) : p ∨ ¬p := by
  apply excludedMiddleFromDNE _ p
  intro q nn
  letI : LE Bool := ⟨relation q⟩
  letI : LT Bool := ⟨fun a b => relation q a b ∧ ¬ relation q b a⟩
  letI : Std.LawfulOrderLT Bool := ⟨fun _ _ => Iff.rfl⟩
  letI : Std.IsLinearPreorder Bool := {
    le_refl := by intro a; cases a <;> exact True.intro
    le_trans := by
      intro a b c ab bc
      cases a <;> cases b <;> cases c <;> first | exact True.intro | exact ab | exact bc
    le_total := by
      intro a b
      cases a <;> cases b <;> first | exact Or.inl True.intro | exact Or.inr True.intro
  }
  exact @compare Bool _ _ _ _ false true (fun lt => nn lt.2)

theorem excludedMiddleFromImplication (imp : type_of% @Lean.Grind.imp_eq) (p : Prop) : p ∨ ¬p :=
  ((imp p p).mp id).elim Or.inr Or.inl

theorem excludedMiddleFromNotNot (nn : type_of% @Lean.Grind.not_not) (p : Prop) : p ∨ ¬p :=
  (nn (p ∨ ¬p)).mp fun neither => neither (.inr fun hp => neither (.inl hp))

theorem excludedMiddleFromLookahead (look : type_of% @Lean.Grind.of_lookahead) (p : Prop) : p ∨ ¬p :=
  (look (p ∨ ¬p) fun neither => neither (.inr fun hp => neither (.inl hp))).mpr True.intro

end GrindOrder

/-- Every inhabited proposition is equal to True. -/
def InhabitedPropExt := ∀ p : Prop, p → p = True

/-- Every refuted proposition is equal to False. -/
def RefutedPropExt := ∀ p : Prop, (¬p) → p = False

theorem inhabitedPropExtOfDecision (rule : type_of% @Lean.Grind.of_decide_eq_true) :
    InhabitedPropExt :=
  fun p hp => @rule p (.isTrue hp) rfl

theorem refutedPropExtOfDecision (rule : type_of% @Lean.Grind.of_decide_eq_false) :
    RefutedPropExt :=
  fun p hn => @rule p (.isFalse hn) rfl

theorem inhabitedPropExtOfEqTrueRule (rule : type_of% @eq_true) : InhabitedPropExt :=
  fun _ hp => rule hp

theorem refutedPropExtOfEqFalseRule (rule : type_of% @eq_false) : RefutedPropExt :=
  fun _ hn => rule hn

theorem inhabitedPropExtOfProofHEq (proofHEq : type_of% @proof_irrel_heq) :
    InhabitedPropExt :=
  fun _ hp => type_eq_of_heq (proofHEq hp True.intro)

theorem inhabitedPropExtOfEqTrue (eqTrue : type_of% @eq_true_eq_id) :
    InhabitedPropExt :=
  fun p hp => ((congrFun eqTrue p).mpr hp).symm

namespace OptionalIndex

/-- Equivalent decidable propositions are equal. -/
def DecidablePropExt : Prop :=
  ∀ {p q : Prop}, [Decidable p] → [Decidable q] → (p ↔ q) → p = q

theorem decidablePropExtOfIte (rule : type_of% @Lean.Grind.ite_true_false) : DecidablePropExt := by
  intro p q dp dq iff
  cases dp with
  | isTrue hp =>
    exact (@rule p (.isTrue hp)).symm.trans (@rule q (.isTrue (iff.mp hp)))
  | isFalse hn =>
    exact (@rule p (.isFalse hn)).symm.trans (@rule q (.isFalse (fun hq => hn (iff.mpr hq))))

private theorem represented (read : type_of% (@isSome_getElem?.{0,0,0}))
    (p : Prop) (d : Decidable p) : (@decide p d = true) = p := by
  let dom (_ _ : Unit) := p
  let answer := @ite (Option Unit) p d (some ()) none
  letI : GetElem? Unit Unit Unit dom := {
    getElem := fun _ _ _ => ()
    getElem? := fun _ _ => answer
    getElem! := fun {_} _ _ => answer.getD default }
  letI : LawfulGetElem Unit Unit Unit dom := {
    getElem?_def := by
      intro c i other
      cases d <;> cases other <;> first | rfl | contradiction
    getElem!_def := by intro inhabited c i; cases d <;> rfl }
  have h := @read Unit Unit Unit dom inferInstance inferInstance () () d
  cases d <;> exact h

theorem decidablePropExtOfIsSome (read : type_of% (@isSome_getElem?.{0,0,0})) :
    DecidablePropExt := by
  intro p q dp dq eqv
  refine (represented read p dp).symm.trans ((congrArg (fun b : Bool => b = true) ?_).trans (represented read q dq))
  cases dp with
  | isTrue hp => exact (decide_eq_true (eqv.mp hp)).symm
  | isFalse hp => exact (decide_eq_false (fun hq => hp (eqv.mpr hq))).symm

end OptionalIndex

namespace NaturalCancellation

open Nat.Internal.Linear

/-- Two slots in the official linear expression evaluator. -/
private abbrev pairCtx (a b : Nat) : Context := .branch 1 (.leaf a) (.leaf b)
private abbrev plusOne (i : Nat) : Nat.Internal.Linear.Expr := .add (.var i) (.num 1)

/-- Removing one successor from each side preserves the proposition itself. -/
def SuccLeEq := ∀ a b : Nat, (a.succ ≤ b.succ) = (a ≤ b)

theorem exprEq (rule : type_of% @Expr.of_cancel_eq) : type_of% @Nat.succ.injEq := by
  intro a b
  exact rule (pairCtx a b) (plusOne 0) (plusOne 1) (.var 0) (.var 1) rfl

theorem exprLe (rule : type_of% @Expr.of_cancel_le) : SuccLeEq := by
  intro a b
  exact rule (pairCtx a b) (plusOne 0) (plusOne 1) (.var 0) (.var 1) rfl

theorem exprNormEq (rule : type_of% @ExprCnstr.eq_of_toNormPoly_eq) : type_of% @Nat.succ.injEq := by
  intro a b
  exact rule (pairCtx a b) ⟨true, plusOne 0, plusOne 1⟩ ⟨true, .var 0, .var 1⟩ rfl

theorem exprNorm (rule : type_of% @ExprCnstr.denote_toNormPoly) : type_of% @Nat.succ.injEq := by
  intro a b
  have h := (rule (pairCtx a b) ⟨true, plusOne 0, plusOne 1⟩).symm
  change (a.succ = b.succ) = (1 * a = 1 * b) at h
  rwa [Nat.one_mul, Nat.one_mul] at h

private abbrev polyPlus (i : Nat) : Poly := [(1, i), (1, fixedVar)]

theorem polyEq (rule : type_of% @Poly.denote_eq_cancel_eq) : type_of% @Nat.succ.injEq := by
  intro a b
  have h := (rule (pairCtx a b) (polyPlus 0) (polyPlus 1)).symm
  change ((1 * a) + 1 = (1 * b) + 1) = (1 * a = 1 * b) at h
  rwa [Nat.one_mul, Nat.one_mul] at h

theorem polyLe (rule : type_of% @Poly.denote_le_cancel_eq) : SuccLeEq := by
  intro a b
  have h := (rule (pairCtx a b) (polyPlus 0) (polyPlus 1)).symm
  change ((1 * a) + 1 ≤ (1 * b) + 1) = (1 * a ≤ 1 * b) at h
  rwa [Nat.one_mul, Nat.one_mul] at h


/-- Strict comparison reflects the same successor cancellation. -/
def SuccLtEq := ∀ a b : Nat, (a.succ < b.succ) = (a < b)

theorem exprLt (rule : type_of% @Expr.of_cancel_lt) : SuccLtEq := by
  intro a b
  exact rule (pairCtx a b) (plusOne 0) (plusOne 1) (.var 0) (.var 1) rfl

end NaturalCancellation

namespace IntegerCancellation

open Int.Internal.Linear

private abbrev pairCtx (a b : Int) : Context := .branch 1 (.leaf a) (.leaf b)
private abbrev plusOne (i : Nat) : Int.Internal.Linear.Expr := .add (.var i) (.num 1)
def AddOneEq := ∀ a b : Int, (a + 1 = b + 1) = (a = b)
def AddOneLE := ∀ a b : Int, (a + 1 ≤ b + 1) = (a ≤ b)
private abbrev difference : Poly := .add (-1) 1 (.add 1 0 (.num 0))


theorem eqVar (rule : type_of% @norm_eq_var) : AddOneEq := by
  intro a b
  exact rule (pairCtx b a) (plusOne 1) (plusOne 0) 1 0 rfl

theorem eqNorm (rule : type_of% @norm_eq) : AddOneEq := by
  intro a b
  exact (rule (pairCtx a b) (plusOne 0) (plusOne 1) difference rfl).trans
    (rule (pairCtx a b) (.var 0) (.var 1) difference rfl).symm

theorem leNorm (rule : type_of% @norm_le) : AddOneLE := by
  intro a b
  exact (rule (pairCtx a b) (plusOne 0) (plusOne 1) difference rfl).trans
    (rule (pairCtx a b) (.var 0) (.var 1) difference rfl).symm

theorem eqCoeff (rule : type_of% @norm_eq_coeff) : AddOneEq := by
  intro a b
  exact (rule (pairCtx a b) (plusOne 0) (plusOne 1) difference 1 rfl).trans
    (rule (pairCtx a b) (.var 0) (.var 1) difference 1 rfl).symm

theorem leCoeff (rule : type_of% @norm_le_coeff) : AddOneLE := by
  intro a b
  exact (rule (pairCtx a b) (plusOne 0) (plusOne 1) difference 1 rfl).trans
    (rule (pairCtx a b) (.var 0) (.var 1) difference 1 rfl).symm

end IntegerCancellation

namespace AbstractOrder

private theorem notNotEM (p : Prop) : ¬ ¬ (p ∨ ¬p) :=
  fun neither => neither (.inr fun hp => neither (.inl hp))

/-- The off-diagonal comparison is excluded middle, in both directions. -/
private def offDiagonal (p : Prop) (a b : Bool) : Prop :=
  if a = b then True else p ∨ ¬p

private theorem offRefl (p : Prop) : Std.Refl (offDiagonal p) := by
  refine ⟨fun a => ?_⟩
  unfold offDiagonal
  rw [ite_eq_left rfl]
  trivial

private theorem offTri (p : Prop) : Std.Trichotomous (offDiagonal p) := by
  refine ⟨fun a b denied _ => ?_⟩
  by_cases eq : a = b
  · exact eq
  · rw [offDiagonal, ite_eq_right eq] at denied
    exact (notNotEM p denied).elim

theorem excludedMiddleOfTrichotomy
    (tri : type_of% (@Std.Trichotomous.rel_or_eq_or_rel_swap.{1})) (p : Prop) : p ∨ ¬p :=
  (@tri Bool (offDiagonal p) (offTri p) false true).elim id
    (fun h => h.elim Bool.noConfusion id)

theorem excludedMiddleOfLTTrichotomy
    (tri : type_of% (@Std.lt_trichotomy.{0})) (p : Prop) : p ∨ ¬p :=
  (@tri Bool ⟨offDiagonal p⟩ (offTri p) false true).elim id
    (fun h => h.elim Bool.noConfusion id)

theorem excludedMiddleOfTrichotomousTotal
    (total : type_of% (@Std.total_of_refl_of_trichotomous.{1})) (p : Prop) : p ∨ ¬p :=
  ((@total Bool (offDiagonal p) (offRefl p) (offTri p)).total false true).elim id id

theorem excludedMiddleOfNegationTotal
    (total : type_of% (@Std.total_of_not_rel_swap_imp_rel.{1})) (p : Prop) : p ∨ ¬p :=
  ((@total Unit (fun _ _ => p ∨ ¬p) (fun {_ _} denied => (notNotEM p denied).elim)).total () ()).elim id id

theorem excludedMiddleOfLawfulLT
    (order : type_of% (@Std.LawfulOrderLT.of_lt.{0})) (p : Prop) : p ∨ ¬p := by
  apply excludedMiddleFromDNE _ p
  intro q nn
  letI : LT Bool := ⟨fun a b => a = false ∧ b = true ∧ q⟩
  letI : Std.Asymm (α := Bool) (· < ·) :=
    ⟨fun _ _ h r => Bool.noConfusion (r.1.symm.trans h.2.1)⟩
  have law := (@order Bool _ _).lt_iff false true
  exact (law.mpr ⟨fun h => Bool.noConfusion h.1,
    fun denied => nn fun hq => denied ⟨rfl,rfl,hq⟩⟩).2.2

/-- Opposite comparisons of distinct Boolean values test a proposition and its negation. -/
private def signed (p : Prop) (a b : Bool) : Prop :=
  Bool.rec (motive := fun _ => Prop)
    (Bool.rec (motive := fun _ => Prop) False p b)
    (Bool.rec (motive := fun _ => Prop) (¬p) False b) a

private theorem signedAsymm (p : Prop) : Std.Asymm (signed p) := by
  refine ⟨fun a b f r => ?_⟩
  cases a <;> cases b <;> first | exact (f : False) | exact (r : ¬p) f | exact (f : ¬p) r

@[instance_reducible] private def signedNegTrans (p : Prop) :
    Trans (fun a b => ¬signed p a b) (fun a b => ¬signed p a b) (fun a b => ¬signed p a b) := by
  constructor
  intro a b c ab bc
  cases a <;> cases b <;> cases c <;> first | exact ab | exact bc | exact id

private theorem signedTri (p : Prop) : Std.Trichotomous (signed p) := by
  refine ⟨fun a b f r => ?_⟩
  cases a <;> cases b <;> first | rfl | exact (r f).elim | exact (f r).elim

theorem weakMiddleOfTotalNot (total : type_of% (@Std.Asymm.total_not.{1})) (p : Prop) :
    ¬p ∨ ¬¬p :=
  (@total Bool (signed p) (signedAsymm p)).total false true

theorem weakMiddleOfLinearPreorder (order : type_of% (@Std.IsLinearPreorder.of_lt.{0})) (p : Prop) :
    ¬p ∨ ¬¬p := by
  letI : LT Bool := ⟨signed p⟩
  exact ((@order Bool _ (signedAsymm p) (signedNegTrans p)).le_total false true).symm

theorem weakMiddleOfLinearOrder (order : type_of% (@Std.IsLinearOrder.of_lt.{0})) (p : Prop) :
    ¬p ∨ ¬¬p := by
  letI : LT Bool := ⟨signed p⟩
  exact ((@order Bool _ (signedAsymm p) (signedNegTrans p) (signedTri p)).le_total false true).symm

end AbstractOrder

namespace InternalOrder

open Lean.Order

theorem excludedMiddleOfFlatSuprema
    (complete : ∀ {α : Type} {c : Option α → Prop}, chain c → ∃ top, is_sup c top)
    (p : Prop) : p ∨ ¬p := by
  let c : Option (Decidable p) → Prop := fun x => ∃ d, x = some d
  have ordered : chain c := by
    rintro _ _ ⟨d, rfl⟩ ⟨d', rfl⟩
    have eq : d = d' := Subsingleton.elim _ _
    cases eq
    exact Or.inl PartialOrder.rel_refl
  obtain ⟨top, hup⟩ := complete ordered
  cases top with
  | some d =>
    cases d with
    | isTrue hp => exact .inl hp
    | isFalse hn => exact .inr hn
  | none =>
    have impossible (d : Decidable p) : False := by
      have h := (hup none).mp PartialOrder.rel_refl (some d) ⟨d, rfl⟩
      change FlatOrder.rel (b := (none : Option (Decidable p))) (some d) none at h
      cases h
    exact .inr fun hp => impossible (.isTrue hp)


private theorem completeFlatOrder {α : Type} (order : CCPO (Option α))
    (agree : ∀ x y : Option α, order.rel x y ↔ x ⊑ y)
    {c : Option α → Prop} (hc : chain c) : ∃ top, is_sup c top := by
  have hc' : @chain _ order.toPartialOrder c := fun x y hx hy =>
    (hc x y hx hy).elim (fun h => .inl ((agree x y).mpr h)) (fun h => .inr ((agree y x).mpr h))
  obtain ⟨top, upper⟩ := @CCPO.has_csup _ order c hc'
  refine ⟨top, fun x => ⟨?_, ?_⟩⟩
  · intro bound y hy
    exact (agree y x).mp ((upper x).mp ((agree top x).mpr bound) y hy)
  · intro bounds
    exact (agree top x).mp ((upper x).mpr fun y hy => (agree y x).mpr (bounds y hy))


theorem excludedMiddleOfOptionCCPO (order : type_of% @Lean.Order.instCCPOOption.{0})
    (agree : ∀ {α : Type} (x y : Option α), (@order α).rel x y ↔ x ⊑ y)
    (p : Prop) : p ∨ ¬p :=
  excludedMiddleOfFlatSuprema (fun {α _} hc => completeFlatOrder (@order α) agree hc) p

theorem excludedMiddleOfFlatCCPO (order : type_of% @FlatOrder.instCCPO.{1})
    (agree : ∀ {α : Type} (x y : Option α), (@order (Option α) none).rel x y ↔ x ⊑ y)
    (p : Prop) : p ∨ ¬p :=
  excludedMiddleOfFlatSuprema (fun {α _} hc => completeFlatOrder (@order (Option α) none) agree hc) p

theorem excludedMiddleOfFlatCSup (pick : type_of% @flat_csup.{1})
    (valid : ∀ {α : Type} (c : Option α → Prop), chain c → is_sup c (@pick (Option α) none c))
    (p : Prop) : p ∨ ¬p :=
  excludedMiddleOfFlatSuprema (fun {_ c} hc => ⟨_, valid c hc⟩) p

theorem funextOfPointwiseOrder
    (order : type_of% @Lean.Order.instOrderPi.{u,v})
    (pointwise : ∀ {α : Sort u} {β : α → Sort v} [inst : ∀ a, PartialOrder (β a)]
      (f g : ∀ a, β a), (∀ a, f a ⊑ g a) → (@order α β inst).rel f g) :
    type_of% @funext.{u,v} := by
  intro α β f g same
  letI component (a : α) : PartialOrder (β a) :=
    ⟨Eq, rfl, Eq.trans, fun h _ => h⟩
  exact (@order α β component).rel_antisymm (pointwise f g same)
    (pointwise g f fun a => (same a).symm)

theorem propextOfImplicationOrder (order : PartialOrder Prop)
    (rel : ∀ p q : Prop, (p → q) → order.rel p q) : type_of% @propext :=
  fun {p q} iff => order.rel_antisymm (rel p q iff.mp) (rel q p iff.mpr)

theorem propextOfReverseImplicationOrder (order : PartialOrder Prop)
    (rel : ∀ p q : Prop, (q → p) → order.rel p q) : type_of% @propext :=
  fun {p q} iff => order.rel_antisymm (rel p q iff.mpr) (rel q p iff.mp)

@[instance_reducible] private def singletonOrder (α : Sort u) [Subsingleton α] : PartialOrder α :=
  ⟨fun _ _ => True, trivial, fun _ _ => trivial, fun {_ _} _ _ => Subsingleton.elim _ _⟩

@[instance_reducible] private def singletonLattice (α : Sort u) [Subsingleton α]
    (inh : Nonempty α) : CompleteLattice α where
  toPartialOrder := singletonOrder α
  has_sup _ := inh.elim fun a => ⟨a, fun _ => ⟨fun _ _ _ => trivial, fun _ => trivial⟩⟩

@[instance_reducible] private def singletonCCPO (α : Sort u) [Subsingleton α] (inh : Nonempty α) : CCPO α where
  toPartialOrder := singletonOrder α
  has_csup {c} _ := (singletonLattice α inh).has_sup c

private abbrev SingletonFunctionsEq :=
  ∀ {α : Sort u} {β : α → Sort (max 1 v)} [∀ a, Subsingleton (β a)],
    (∀ a, Nonempty (β a)) → ∀ (f g : ∀ a, β a), f = g

private theorem funextOfSingletonFunctions (eq : SingletonFunctionsEq.{u,v}) :
    type_of% @funext.{u,v} := by
  intro α β f g same
  let F (a : α) := {x : β a // x = f a}
  letI fiber (a : α) : Subsingleton (F a) := ⟨fun x y => Subtype.ext (x.2.trans y.2.symm)⟩
  have eq := @eq α F fiber (fun a => ⟨⟨f a, rfl⟩⟩)
    (fun a => ⟨f a, rfl⟩) (fun a => ⟨g a, (same a).symm⟩)
  exact congrArg (fun z : ∀ a, F a => fun a => (z a).val) eq

theorem funextOfCompletePointwiseOrder
    (order : type_of% @Lean.Order.instCompleteLatticePi.{u,max 1 v})
    (pointwise : ∀ {α : Sort u} {β : α → Sort (max 1 v)} [inst : ∀ a, CompleteLattice (β a)]
      (f g : ∀ a, β a), (∀ a, f a ⊑ g a) → (@order α β inst).rel f g) :
    type_of% @funext.{u,v} := by
  apply funextOfSingletonFunctions
  intro α β fibers inhabited f g
  letI components (a : α) := singletonLattice (β a) (inhabited a)
  exact (@order α β components).rel_antisymm (pointwise f g (fun _ => trivial))
    (pointwise g f (fun _ => trivial))

theorem funextOfChainCompletePointwiseOrder
    (order : type_of% @Lean.Order.instCCPOPi.{u,max 1 v})
    (pointwise : ∀ {α : Sort u} {β : α → Sort (max 1 v)} [inst : ∀ a, CCPO (β a)]
      (f g : ∀ a, β a), (∀ a, f a ⊑ g a) → (@order α β inst).rel f g) :
    type_of% @funext.{u,v} := by
  apply funextOfSingletonFunctions
  intro α β fibers inhabited f g
  letI components (a : α) := singletonCCPO (β a) (inhabited a)
  exact (@order α β components).rel_antisymm (pointwise f g (fun _ => trivial))
    (pointwise g f (fun _ => trivial))

abbrev UniqueChoice := ∀ {α : Sort u} [Subsingleton α], Nonempty α → α

def uniqueChoiceOfSup (select : type_of% @CompleteLattice.sup.{u}) : UniqueChoice.{u} :=
  fun {α} _ inh => @select α (singletonLattice α inh) (fun _ => False)

def uniqueChoiceOfChainSup (select : type_of% @CCPO.csup.{u}) : UniqueChoice.{u} := by
  intro α _ inh
  letI : CCPO α := singletonCCPO α inh
  exact select (chain_empty α)

def uniqueChoiceOfBot (select : type_of% @Lean.Order.bot.{u}) : UniqueChoice.{u} := by
  intro α _ inh
  letI : CCPO α := singletonCCPO α inh
  exact select

def uniqueChoiceOfLfp (select : type_of% @lfp.{u}) : UniqueChoice.{u} :=
  fun {α} _ inh => @select α (singletonLattice α inh) id

def uniqueChoiceOfMonotoneLfp (select : type_of% @lfp_monotone.{u}) : UniqueChoice.{u} :=
  fun {α} _ inh => @select α (singletonLattice α inh) id (fun _ _ h => h)

def uniqueChoiceOfFix (select : type_of% @fix.{u}) : UniqueChoice.{u} :=
  fun {α} _ inh => @select α (singletonCCPO α inh) id (fun _ _ h => h)

def uniqueChoiceOfProdSup (select : type_of% @prod_sup.{u,u}) : UniqueChoice.{u} :=
  fun {α} _ inh =>
    let lattice := singletonLattice α inh
    (@select α α lattice lattice (fun _ => False)).1

def uniqueChoiceOfProdCSup (select : type_of% @prod_csup.{u,u}) : UniqueChoice.{u} :=
  fun {α} _ inh =>
    let order := singletonCCPO α inh
    (@select α α order order (fun _ => False) (fun _ _ denied => denied.elim)).1

def uniqueChoiceOfFunSup (select : type_of% @fun_sup.{1,u}) : UniqueChoice.{u} :=
  fun {α} _ inh => @select Unit (fun _ => α) (fun _ => singletonLattice α inh) (fun _ => False) ()

def limitedOmniscienceOfSearch (search : type_of% @Example.find)
    (step : ∀ f n, search f n = if f n then some n else search f (n+1))
    (valid : ∀ f n m, search f n = some m → f m = true) (f : Nat → Bool) :
    Decidable (∃ n, f n = true) := by
  cases found : search f 0 with
  | some n => exact .isTrue ⟨n, valid f 0 n found⟩
  | none =>
    have absent (n : Nat) : search f n = none := by
      induction n with
      | zero => exact found
      | succ n ih =>
        have eq := (step f n).symm.trans ih
        cases hit : f n with
        | true =>
          rw [hit] at eq
          cases eq
        | false =>
          rw [hit] at eq
          exact eq
    exact .isFalse fun ⟨n, hit⟩ => by
      have eq := (step f n).symm.trans (absent n)
      rw [hit] at eq
      cases eq

abbrev FamilyChoice := ∀ {α : Sort u} {β : α → Type}, (∀ x, Nonempty (β x)) → Nonempty (∀ x, β x)

theorem familyChoiceOfStateBottom (bot : type_of% @Lean.Order.EST.bot) : FamilyChoice.{u} :=
  fun {_} {β} inh =>
    (Void.instNonempty (σ := Unit)).elim fun token => ⟨fun x =>
      match @bot (β x) Unit Empty (inh x) token with
      | .ok impossible _ => impossible.elim
      | .error element _ => element⟩

end InternalOrder

namespace TwoWorlds

/-- Kripke implication on the chain `false ≤ true`. -/
def imp (p q : Bool → Prop) (w : Bool) : Prop := ∀ v, w ≤ v → p v → q v

def neg (p : Bool → Prop) : Bool → Prop := imp p (fun _ => False)

/-- The atom holds only at the leaf. Its valuation is persistent, and both double-negation
elimination and excluded middle fail at the root of this propositional Kripke model. -/
theorem countermodel :
    let p := fun w : Bool => w = true
    (∀ u v : Bool, u ≤ v → p u → p v) ∧
    ¬ imp (neg (neg p)) p false ∧ ¬ (p false ∨ neg p false) := by
  let p := fun w : Bool => w = true
  have reachesLeaf (w : Bool) : w ≤ true := fun _ => rfl
  have absent : ¬p false := fun h => nomatch h
  have nn : neg (neg p) false := fun v _ hn => hn true (reachesLeaf v) rfl
  exact ⟨fun _ _ le => le, fun h => absent (h false id nn),
    fun h => h.elim absent (fun hn => hn true (reachesLeaf false) rfl)⟩

end TwoWorlds

/-- Physical public definition sites with a checked reduction from the original type.
The target universe parameters are a suffix of the witness parameters. -/
def reductions : List (Name × Name × Name × Name) := [
  (`Init.Classical, `Classical.choose, `Classical.choice, ``choiceFromChoose),
  (`Init.Classical, `Exists.choose, `Classical.choice, ``choiceFromExistsChoose),
  (`Init.Classical, `Classical.epsilon, `Classical.choice, ``choiceFromEpsilon),
  (`Init.Classical, `Classical.indefiniteDescription, `Classical.choice, ``choiceFromDescription),
  (`Init.Classical, `Classical.inhabited_of_nonempty, `Classical.choice, ``choiceFromInhabited),
  (`Init.Classical, `Classical.inhabited_of_exists, `Classical.choice, ``choiceFromInhabitedOfExists),
  (`Init.Classical, `Classical.strongIndefiniteDescription, `Classical.choice, ``choiceFromStrongDescription),
  (`Init.Classical, `Classical.typeDecidable, `Classical.choice, ``choiceFromTypeDecidable),
  (`Init.Prelude, `Classical.ofNonempty, `Classical.choice, ``choiceFromOfNonempty),
  (`Init.Core, `iff_iff_eq, `propext, ``propextFromIffIffEq),
  (`Init.Core, `eq_iff_iff, `propext, ``propextFromEqIffIff),
  (`Init.Core, `Iff.subst, `propext, ``propextFromIffSubst),
  (`Init.Core, `Eq.propIntro, `propext, ``propextFromPropIntro),
  (`Init.Ext, `propext_iff, `propext, ``propextFromPropextIff),
  (`Init.Classical, `Classical.propComplete, `propext, ``propextFromPropComplete),
  (`Init.PropLemmas, `ite_iff_left_iff, `propext, ``propextFromIteIffLeft),
  (`Init.PropLemmas, `ite_iff_right_iff, `propext, ``propextFromIteIffRight),
  (`Init.PropLemmas, `left_iff_ite_iff, `propext, ``propextFromLeftIffIte),
  (`Init.PropLemmas, `right_iff_ite_iff, `propext, ``propextFromRightIffIte),
  (`Init.Grind.Norm, `Lean.Grind.iff_eq, `propext, ``propextFromGrindIffEq),
  (`Init.WFExtrinsicFix, `WellFounded.extrinsicFix, `Classical.choice, ``choiceFromFix),
  (`Init.WFExtrinsicFix, `WellFounded.partialExtrinsicFix, `Classical.choice, ``choiceFromFix),
  (`Init.WFExtrinsicFix, `WellFounded.extrinsicFix₂, `Classical.choice, ``choiceFromFix₂),
  (`Init.WFExtrinsicFix, `WellFounded.partialExtrinsicFix₂, `Classical.choice, ``choiceFromFix₂),
  (`Init.WFExtrinsicFix, `WellFounded.extrinsicFix₃, `Classical.choice, ``choiceFromFix₃),
  (`Init.WFExtrinsicFix, `WellFounded.partialExtrinsicFix₃, `Classical.choice, ``choiceFromFix₃),
  -- Even the logically opaque loop must return an element when its three inputs are units.
  (`Init.WFExtrinsicFix, `WellFounded.opaqueFix₃, `Classical.choice, ``choiceFromFix₃),
  (`Init.Grind.Injective, `Lean.Grind.leftInv, `Classical.choice, ``choiceFromLeftInv),
  (`Init.While, `repeatM, `Classical.choice, ``choiceFromRepeatM),
  (`Init.Prelude, `unsafeCast, `sorryAx, ``sorryAxFromUnsafeCast)]

/-- Recheck the transitive kernel terms of each witness with all forbidden declarations absent.
Include complete inductive families so that replay can regenerate their primitive rules. -/
private def replayWitnesses (env : Environment) : IO Unit := do
  let official ← importModules #[{module := `Lean}] {} (level := .private)
  let mut terms : Std.HashMap Name ConstantInfo := {}
  let mut todo := (reductions.map fun (_, _, _, witness) => witness) ++
    [``LexicographicOrder.ofListNotLE, ``LexicographicOrder.ofArrayNotLE, ``LexicographicOrder.ofVectorNotLE,
      ``FiniteMembership.ofRunDecomposition, ``FiniteMembership.ofRunInduction,
      ``FiniteMembership.ofListMember, ``FiniteMembership.ofArrayMember,
      ``FiniteMembership.ofFirstListMember, ``FiniteMembership.ofFirstArrayMember,
      ``choiceFromOptionPresence, ``VectorExistence.emOfVectorSucc, ``dneFromClosedRange, ``dneFromOpenRange, ``excludedMiddleFromDNE, ``excludedMiddleOfNotLT,
      ``excludedMiddleOfNotLTIff, ``GrindOrder.excludedMiddleFromComparison, ``GrindOrder.excludedMiddleFromImplication,
      ``GrindOrder.excludedMiddleFromNotNot, ``GrindOrder.excludedMiddleFromLookahead,
      ``AbstractOrder.excludedMiddleOfTrichotomy, ``AbstractOrder.excludedMiddleOfLTTrichotomy,
      ``AbstractOrder.excludedMiddleOfTrichotomousTotal, ``AbstractOrder.excludedMiddleOfNegationTotal,
      ``InternalOrder.familyChoiceOfStateBottom, ``InternalOrder.limitedOmniscienceOfSearch,
      ``InternalOrder.funextOfCompletePointwiseOrder, ``InternalOrder.funextOfChainCompletePointwiseOrder,
      ``InternalOrder.funextOfPointwiseOrder, ``InternalOrder.propextOfImplicationOrder,
      ``InternalOrder.propextOfReverseImplicationOrder, ``InternalOrder.excludedMiddleOfFlatSuprema,
      ``InternalOrder.excludedMiddleOfOptionCCPO, ``InternalOrder.excludedMiddleOfFlatCCPO,
      ``InternalOrder.excludedMiddleOfFlatCSup,
      ``InternalOrder.uniqueChoiceOfLfp, ``InternalOrder.uniqueChoiceOfMonotoneLfp,
      ``InternalOrder.uniqueChoiceOfFix, ``InternalOrder.uniqueChoiceOfProdSup,
      ``InternalOrder.uniqueChoiceOfProdCSup, ``InternalOrder.uniqueChoiceOfFunSup,
      ``InternalOrder.uniqueChoiceOfBot, ``InternalOrder.uniqueChoiceOfChainSup, ``InternalOrder.uniqueChoiceOfSup,
      ``AbstractOrder.excludedMiddleOfLawfulLT, ``AbstractOrder.weakMiddleOfTotalNot,
      ``AbstractOrder.weakMiddleOfLinearPreorder, ``AbstractOrder.weakMiddleOfLinearOrder,
      ``inhabitedPropExtOfProofHEq, ``inhabitedPropExtOfEqTrue,
      ``inhabitedPropExtOfDecision, ``refutedPropExtOfDecision, ``inhabitedPropExtOfEqTrueRule,
      ``refutedPropExtOfEqFalseRule, ``OptionalIndex.decidablePropExtOfIte,
      ``IntegerCancellation.eqVar, ``IntegerCancellation.eqNorm, ``IntegerCancellation.leNorm,
      ``IntegerCancellation.eqCoeff, ``IntegerCancellation.leCoeff,
      ``NaturalCancellation.exprEq, ``NaturalCancellation.exprLe, ``NaturalCancellation.exprLt,
      ``NaturalCancellation.exprNormEq, ``NaturalCancellation.exprNorm, ``NaturalCancellation.polyEq,
      ``NaturalCancellation.polyLe,
      ``OptionalIndex.decidablePropExtOfIsSome, ``TwoWorlds.countermodel]
  while let n :: more := todo do
    todo := more
    if terms.contains n then continue
    let some ci := (official.find? n).orElse fun _ => env.find? n
      | throw <| IO.userError s!"missing witness dependency {n}"
    if ci.isAxiom || ci.isUnsafe || ci.isPartial || ci matches .quotInfo _ then
      throw <| IO.userError s!"forbidden dependency in a boundary witness: {n}"
    terms := terms.insert n ci
    todo := ci.getUsedConstantsAsSet.toList ++ todo
    if let .inductInfo ind := ci then todo := ind.all ++ todo
    if let .ctorInfo ctor := ci then todo := ctor.induct :: todo
  discard <| (← mkEmptyEnvironment).toKernelEnv.replay terms

run_cmd
  let env ← getEnv
  let mut seen := Std.HashSet.emptyWithCapacity
  for (owner, name, axiomName, witness) in reductions do
    unless !seen.contains (owner, name) do throwError "duplicate axiom reduction for {owner}/{name}"
    seen := seen.insert (owner, name)
    let some idx := env.getModuleIdx? owner | throwError "missing module {owner}"
    let some source := env.header.moduleData[idx]!.constants.find? (·.name == name)
      | throwError "missing definition site {owner}/{name}"
    -- Several compiler axioms have constructively inhabited types (e.g. lcAny : Type).
    -- A reduction to one of those cannot exclude a source declaration.
    unless [`Classical.choice, `propext, `sorryAx].contains axiomName do
      throwError "unsupported impossibility target {axiomName} for {owner}/{name}"
    let proof ← getConstInfo witness
    let target ← getConstInfo axiomName
    let levels := proof.levelParams.map Level.param
    -- The source may be specialized to a particular universe tuple when constructing the axiom.
    let .forallE _ input _ _ := proof.type | throwError "missing argument of {witness}"
    let sourceLevels ← Elab.Command.liftCoreM <| Meta.MetaM.run' do
      let fresh ← Meta.mkFreshLevelMVarsFor source
      unless ← Meta.isDefEq input (source.type.instantiateLevelParams source.levelParams fresh) do
        throwError "incorrect source type in {witness}"
      let found ← fresh.mapM instantiateLevelMVars
      if found.any Level.hasMVar then throwError "unresolved source universe in {witness}"
      return found
    let targetLevels := levels.drop (levels.length - target.numLevelParams)
    let expected := Expr.forallE .anonymous (source.type.instantiateLevelParams source.levelParams sourceLevels)
      (target.type.instantiateLevelParams target.levelParams targetLevels) .default
    unless target.isAxiom && target.numLevelParams == targetLevels.length &&
        !proof.isUnsafe && !proof.isPartial && (proof.value? (allowOpaque := true)).isSome &&
        Kernel.isDefEqGuarded env {} proof.type expected && (← collectAxioms witness).isEmpty do
      throwError "invalid axiom reduction for {owner}/{name}"
  replayWitnesses env

/-- Evaluation factors through the setoid of pointwise-equal functions. -/
theorem funextFromQuotientSound (sound : type_of% (@Quotient.sound.{imax u v})) :
    type_of% (@funext.{u,v}) := by
  intro α β f g h
  let s : Setoid ((a : α) → β a) := ⟨fun f g => ∀ a, f a = g a,
    ⟨fun _ _ => rfl, fun h a => (h a).symm, fun h₁ h₂ a => (h₁ a).trans (h₂ a)⟩⟩
  let app (q : Quotient s) (a : α) : β a :=
    Quot.lift (r := s.r) (fun t => t a) (fun _ _ eq => eq a) q
  exact congrArg app (@sound _ s f g h)

/-- Each fiber of values equal to a fixed value is a subsingleton. -/
theorem funextFromPiSubsingleton (ss : type_of% (@Pi.instSubsingleton.{u, max 1 v})) :
    type_of% (@funext.{u,v}) := by
  intro α β f g h
  let F (a : α) := {x : β a // x = f a}
  let fibers (a : α) : Subsingleton (F a) := ⟨fun x y => Subtype.ext (x.2.trans y.2.symm)⟩
  have eq := (@ss α F fibers).elim (fun a => ⟨f a, rfl⟩) (fun a => ⟨g a, (h a).symm⟩)
  exact congrArg (fun z : ∀ a, F a => fun a => (z a).val) eq

/-- Evaluate a squashed function by restricting to a single pointwise equality class. -/
theorem funextFromSquashSubsingleton (ss : type_of% (@instSubsingletonSquash.{max 1 (imax u v)})) :
    type_of% (@funext.{u,v}) := by
  intro α β f g h
  let F := {t : (a : α) → β a // ∀ a, t a = f a}
  let app (s : Squash F) (a : α) : β a :=
    Quot.lift (fun t : F => t.val a) (fun t t' _ => (t.2 a).trans (t'.2 a).symm) s
  have eq := (@ss F).elim (Squash.mk (⟨f, fun _ => rfl⟩ : F))
    (Squash.mk (⟨g, fun a => (h a).symm⟩ : F))
  exact congrArg app eq

run_cmd
  for n in [``funextFromQuotientSound, ``funextFromPiSubsingleton, ``funextFromSquashSubsingleton] do
    unless (← collectAxioms n).isEmpty do throwError "function extensionality witness {n} uses axioms"

namespace Envelope

open _root_.Lean.Grind _root_.Lean.Grind.Ring.OfSemiring

/-- Equal quotient representatives distinguished by a Boolean observation imply function extensionality. -/
private theorem quotientPointsGiveFunext {A : Sort w} {r : A → A → Prop} (pick : A → Bool)
    {p q : A} (hp : pick p = false) (hq : pick q = true) (same : Quot.mk r p = Quot.mk r q) :
    type_of% (@funext.{u,v}) := by
  intro α β f g h
  let F (x : A) (i : α) : β i := bif pick x then g i else f i
  have stable (i : α) (x y : A) (_ : r x y) : F x i = F y i := by
    dsimp only [F]
    cases pick x <;> cases pick y <;> first | rfl | exact h i | exact (h i).symm
  let app (z : Quot r) (i : α) : β i := Quot.lift (fun x => F x i) (stable i) z
  have sides := congrArg app same
  change (fun i => bif pick p then g i else f i) = (fun i => bif pick q then g i else f i) at sides
  rw [hp, hq] at sides
  exact sides

@[expose] def natPositive : Nat → Bool
  | 0 => false
  | _ + 1 => true

local instance boolSemiring : Semiring Bool where
  add := Bool.or
  mul := Bool.and
  natCast := ⟨natPositive⟩
  ofNat n := ⟨natPositive n⟩
  nsmul := ⟨fun k a => natPositive k && a⟩
  npow := ⟨fun a k => if natPositive k then a else true⟩
  add_zero a := by cases a <;> rfl
  add_comm a b := by cases a <;> cases b <;> rfl
  add_assoc a b c := by cases a <;> cases b <;> cases c <;> rfl
  mul_assoc a b c := by cases a <;> cases b <;> cases c <;> rfl
  mul_one a := by cases a <;> rfl
  one_mul a := by cases a <;> rfl
  left_distrib a b c := by cases a <;> cases b <;> cases c <;> rfl
  right_distrib a b c := by cases a <;> cases b <;> cases c <;> rfl
  zero_mul a := rfl
  mul_zero a := by cases a <;> rfl
  pow_zero a := rfl
  pow_succ a k := by cases a <;> cases k <;> rfl
  ofNat_succ n := by cases n <;> rfl
  ofNat_eq_natCast _ := rfl
  nsmul_eq_natCast_mul _ _ := rfl

/-- The Boolean semiring gives two related pairs with different first coordinates. -/
private theorem envelopeFunext
    (same : Q.mk (α := Bool) (false, false) = Q.mk (α := Bool) (true, true)) :
    type_of% (@funext.{u,v}) :=
  quotientPointsGiveFunext (fun p : Bool × Bool => p.1) (p := (false,false)) (q := (true,true)) rfl rfl same

theorem funextFromNegRespect (respect : type_of% (@neg._proof_1.{0})) : type_of% (@funext.{u,v}) :=
  envelopeFunext (@respect Bool _ (false,false) (true,true) ⟨false,rfl⟩)

theorem funextFromAddRespect (respect : type_of% (@add._proof_1.{0})) : type_of% (@funext.{u,v}) :=
  envelopeFunext (@respect Bool _ (false,false) (false,false) (true,true) (false,false) ⟨false,rfl⟩ ⟨false,rfl⟩)

theorem funextFromSubRespect (respect : type_of% (@sub._proof_5.{0})) : type_of% (@funext.{u,v}) :=
  envelopeFunext (@respect Bool _ (false,false) (false,false) (true,true) (false,false) ⟨false,rfl⟩ ⟨false,rfl⟩)

theorem funextFromMulRespect (respect : type_of% (@mul._proof_1.{0})) : type_of% (@funext.{u,v}) :=
  envelopeFunext (@respect Bool _ (false,false) (true,false) (true,true) (true,false) ⟨false,rfl⟩ ⟨false,rfl⟩)

/-- Cancellation together with the representative computation rules at a single input suffices. -/
theorem funextFromCancellation
    (plus : Q Bool → Q Bool → Q Bool) (minus : Q Bool → Q Bool)
    (negValue : minus (Q.mk (true, false)) = Q.mk (false, true))
    (sumValue : plus (Q.mk (false, true)) (Q.mk (true, false)) = Q.mk (true, true))
    (cancel : ∀ z, plus (minus z) z = Q.mk (false, false)) :
    type_of% (@funext.{u,v}) := by
  have eq := cancel (Q.mk (true, false))
  rw [negValue, sumValue] at eq
  intro α β f g h
  exact envelopeFunext eq.symm h

run_cmd
  for n in [``funextFromNegRespect, ``funextFromAddRespect, ``funextFromSubRespect,
      ``funextFromMulRespect, ``funextFromCancellation] do
    unless (← collectAxioms n).isEmpty do throwError "ring envelope witness {n} uses axioms"

end Envelope

/-- Reader binding exposes the entire continuation as its result. -/
theorem funextFromBindCongr
    (combine : type_of% (@bind_congr.{u,u})) {α β : Type u} {f g : α → β}
    (pointwise : ∀ x, f x = g x) : f = g := by
  let read (γ : Type u) := α → γ
  letI : Bind read := ⟨fun x k a => k (x a) a⟩
  have eq := @combine read α β _ (fun a => a)
    (fun a _ => f a) (fun a _ => g a)
    (fun a => congrArg (fun y _ => y) (pointwise a))
  exact eq

/-- Mapping over the identity reader exposes the mapped function itself. -/
theorem funextFromMapCongr
    (combine : type_of% (@map_congr.{u,u})) {α β : Type u} {f g : α → β}
    (pointwise : ∀ x, f x = g x) : f = g := by
  let read (γ : Type u) := α → γ
  letI : Functor read := ⟨fun h x a => h (x a), fun c _ _ => c⟩
  exact @combine read α β _ (fun a => a) f g pointwise

private def graphStep {α : Sort u} {β : α → Sort v} (f : (x : α) → β x)
    (x : PLift (PSum α (PSigma β))) : PLift (PSum α (PSigma β)) :=
  PSum.casesOn x.down (fun a => ⟨.inr ⟨a, f a⟩⟩) (fun _ => x)

/-- Equal endomorphisms identify dependent sections by their graphs. -/
private theorem funextFromEndomorphisms
    (ext : ∀ {T : Type (max 1 u v)} {f g : T → T}, (∀ x, f x = g x) → f = g) :
    type_of% @funext.{u,v} := by
  intro α β f g agree
  have stepEq : graphStep f = graphStep g := ext
    (T := PLift (PSum α (PSigma β))) (f := graphStep f) (g := graphStep g) (by
    rintro ⟨x⟩
    cases x with
    | inl a => exact congrArg (fun y => PLift.up (.inr ⟨a, y⟩ : PSum α (PSigma β))) (agree a)
    | inr => rfl)
  let graph (h : (a : α) → β a) (a : α) : PSigma β := ⟨a, h a⟩
  let observe (k : PLift (PSum α (PSigma β)) → PLift (PSum α (PSigma β))) (a : α) : PSigma β :=
    PSum.casesOn (k ⟨.inl a⟩).down (fun _ => ⟨a, f a⟩) id
  have graphEq : graph f = graph g := congrArg observe stepEq
  let unpack (t : {t : α → PSigma β // ∀ x, (t x).1 = x}) (a : α) : β a :=
    (t.property a) ▸ (t.val a).2
  exact congrArg unpack (Subtype.ext (a1 := ⟨graph f, fun _ => rfl⟩)
    (a2 := ⟨graph g, fun _ => rfl⟩) graphEq)

/-- Congruence under binding in the identity reader entails dependent function extensionality. -/
theorem dependentFunextFromBindCongr (combine : type_of% @bind_congr.{max 1 u v,max 1 u v}) :
    type_of% @funext.{u,v} :=
  funextFromEndomorphisms (fun {_ _ _} h => funextFromBindCongr combine h)

/-- Congruence of mapping over a reader entails dependent function extensionality. -/
theorem dependentFunextFromMapCongr (combine : type_of% @map_congr.{max 1 u v,max 1 u v}) :
    type_of% @funext.{u,v} :=
  funextFromEndomorphisms (fun {_ _ _} h => funextFromMapCongr combine h)

theorem funextFromReaderExt (ext : type_of% @ReaderT.ext.{max 1 u v,max 1 u v}) :
    type_of% @funext.{u,v} :=
  funextFromEndomorphisms fun {T f g} h => @ext T (fun _ => T) T f g h

theorem funextFromReaderExtIff (ext : type_of% @ReaderT.ext_iff.{max 1 u v,max 1 u v}) :
    type_of% @funext.{u,v} :=
  funextFromReaderExt fun {_ _ _ _ _} => ext.mpr

theorem funextFromStateExt (ext : type_of% @StateT.ext.{max 1 u v,max 1 u v}) :
    type_of% @funext.{u,v} :=
  funextFromEndomorphisms fun {T f g} h => @ext T (fun _ => T) T f g h

theorem funextFromStateExtIff (ext : type_of% @StateT.ext_iff.{max 1 u v,max 1 u v}) :
    type_of% @funext.{u,v} :=
  funextFromStateExt fun {_ _ _ _ _} => ext.mpr

/-- On the graph of f, replacing each value by its pointwise equal g gives an identity map. -/
private theorem endomorphismsOfPointwiseId
    (fixes : ∀ {S : Type w} (k : S → S), (∀ s, k s = s) → k = id)
    {T : Type w} {f g : T → T} (h : ∀ x, f x = g x) : f = g := by
  let graph := {p : T × T // p.2 = f p.1}
  let k (p : graph) : graph := ⟨(p.val.1, g p.val.1), (h p.val.1).symm⟩
  have eq := fixes k fun p => Subtype.ext (Prod.ext rfl ((h p.val.1).symm.trans p.property.symm))
  exact (congrArg (fun (j : graph → graph) x => (j ⟨(x, f x), rfl⟩).val.2) eq).symm

theorem funextFromLeftInverseId
    (inv : type_of% @Function.LeftInverse.id.{(max 1 u v)+1,(max 1 u v)+1}) :
    type_of% @funext.{u,v} :=
  funextFromEndomorphisms fun {_ _ _} h =>
    endomorphismsOfPointwiseId (fun {S} k hk => @inv S S k id hk) h

theorem funextFromRightInverseId
    (inv : type_of% @Function.RightInverse.id.{(max 1 u v)+1,(max 1 u v)+1}) :
    type_of% @funext.{u,v} :=
  funextFromEndomorphisms fun {_ _ _} h =>
    endomorphismsOfPointwiseId (fun {S} k hk => @inv S S id k hk) h

/-- A reader iterator returns the callback's value at the supplied element. -/
theorem funextFromForInEq
    (loop : type_of% @forIn'_eq_forIn.{max 1 u v,0,max 1 u v,max 1 u v}) :
    type_of% @funext.{u,v} := by
  apply funextFromEndomorphisms
  intro T f g h
  let read (α : Type (max 1 u v)) := T → α
  letI : Membership T Unit := ⟨fun _ _ => True⟩
  letI : ForIn' read Unit T inferInstance := ⟨fun _ b visit x => (visit x True.intro b x).value⟩
  let body (k : T → T) (a : T) (_ : T → T) : read (ForInStep (T → T)) :=
    fun _ => .yield fun _ => k a
  have eq := @loop T Unit read _ _ (T → T) () id (fun a _ => body f a) (body g)
    (fun a _ _ => congrArg (fun (y : T) (_ : T) => ForInStep.yield fun _ : T => y) (h a))
  have diagonal := congrArg (fun (k : T → T → T) x => k x x) eq
  exact diagonal

open Lean in
run_cmd
  for n in [``dependentFunextFromBindCongr, ``dependentFunextFromMapCongr,
      ``funextFromReaderExt, ``funextFromReaderExtIff, ``funextFromStateExt, ``funextFromStateExtIff,
      ``funextFromLeftInverseId, ``funextFromRightInverseId, ``funextFromForInEq] do
    unless (← collectAxioms n).isEmpty do throwError "reader congruence witness {n} uses axioms"

namespace TransformerLaws

/-- A pointwise identity can be applied in the error branch of both mapping and binding. -/
@[instance_reducible] private def exceptionMonad {ε : Type u} (reset : ε → ε) : Monad (fun α : Type u => Except ε α) where
  pure := Except.ok
  bind x k := match x with | .ok a => k a | .error e => .error (reset e)
  map f x := match x with | .ok a => .ok (f a) | .error e => .error (reset e)

private theorem lawful {ε : Type u} (reset : ε → ε) (fixed : ∀ e, reset e = e) :
    letI := exceptionMonad reset; LawfulMonad (fun α : Type u => Except ε α) := by
  letI := exceptionMonad reset
  exact {
    map_const := rfl
    id_map := by intro _ x; cases x <;> first | rfl | exact congrArg Except.error (fixed _) | exact congrArg Except.error (fixed _).symm
    comp_map := by intro _ _ _ g h x; cases x <;> first | rfl | exact congrArg Except.error (fixed _) | exact congrArg Except.error (fixed _).symm
    pure_seq := by intro _ _ f x; cases x <;> first | rfl | exact congrArg Except.error (fixed _) | exact congrArg Except.error (fixed _).symm
    map_pure := by intros; rfl
    seq_pure := by intro _ _ g x; cases g <;> first | rfl | exact congrArg Except.error (fixed _) | exact congrArg Except.error (fixed _).symm
    seqLeft_eq := by intro _ _ x y; cases x <;> cases y <;> first | rfl | exact congrArg Except.error (fixed _) | exact congrArg Except.error (fixed _).symm
    seqRight_eq := by intro _ _ x y; cases x <;> cases y <;> first | rfl | exact congrArg Except.error (fixed _) | exact congrArg Except.error (fixed _).symm
    seq_assoc := by intro _ _ _ x g h; cases x <;> cases g <;> cases h <;> first | rfl | exact congrArg Except.error (fixed _) | exact congrArg Except.error (fixed _).symm
    bind_pure_comp := by intro _ _ f x; cases x <;> first | rfl | exact congrArg Except.error (fixed _) | exact congrArg Except.error (fixed _).symm
    bind_map := by intro _ _ f x; cases f <;> cases x <;> first | rfl | exact congrArg Except.error (fixed _) | exact congrArg Except.error (fixed _).symm
    pure_bind := by intros; rfl
    bind_assoc := by intro _ _ _ x f g; cases x <;> first | rfl | exact congrArg Except.error (fixed _)
  }

private def Graph {T : Type u} (f : T → T) := (x : T) × {y : T // f x = y}
private def resetGraph {T : Type u} (f : T → T) (p : Graph f) : Graph f := ⟨p.1, f p.1, rfl⟩
private theorem resetGraph_eq {T : Type u} (f : T → T) (p : Graph f) : resetGraph f p = p := by
  rcases p with ⟨x,y,hy⟩
  cases hy
  rfl

private abbrev ErrorM {T : Type u} (f : T → T) (α : Type u) := Except (Graph f) α

private theorem readerIdentity {T : Type u} {f g : T → T} (agree : ∀ x, f x = g x)
    (identityLaw : letI := exceptionMonad (resetGraph f); LawfulFunctor (ReaderT T (ErrorM f))) :
    f = g := by
  letI := exceptionMonad (resetGraph f)
  letI : LawfulFunctor (ReaderT T (ErrorM f)) := identityLaw
  let input : ReaderT T (ErrorM f) PUnit := fun t => .error ⟨t, g t, agree t⟩
  let output (a : ReaderT T (ErrorM f) PUnit) (t : T) :=
    match a t with | .error s => s.2.val | .ok _ => t
  exact congrArg output (id_map input)

private theorem viaFunctor (law : type_of% @ReaderT.instLawfulFunctor.{u,u})
    {T : Type u} {f g : T → T} (agree : ∀ x, f x = g x) : f = g := by
  letI := exceptionMonad (resetGraph f)
  letI : LawfulMonad (ErrorM f) := lawful (resetGraph f) (resetGraph_eq f)
  exact readerIdentity agree ((law (ρ := T) (m := ErrorM f)))

private theorem viaApplicative (law : type_of% @ReaderT.instLawfulApplicative.{u,u})
    {T : Type u} {f g : T → T} (agree : ∀ x, f x = g x) : f = g := by
  letI := exceptionMonad (resetGraph f)
  letI : LawfulMonad (ErrorM f) := lawful (resetGraph f) (resetGraph_eq f)
  exact readerIdentity agree ((law (ρ := T) (m := ErrorM f)).toLawfulFunctor)

private theorem viaMonad (law : type_of% @ReaderT.instLawfulMonad.{u,u})
    {T : Type u} {f g : T → T} (agree : ∀ x, f x = g x) : f = g := by
  letI := exceptionMonad (resetGraph f)
  letI : LawfulMonad (ErrorM f) := lawful (resetGraph f) (resetGraph_eq f)
  exact readerIdentity agree ((law (ρ := T) (m := ErrorM f)).toLawfulApplicative.toLawfulFunctor)

private theorem viaState (law : type_of% @StateT.instLawfulMonad.{u,u})
    {T : Type u} {f g : T → T} (agree : ∀ x, f x = g x) : f = g := by
  letI := exceptionMonad (resetGraph f)
  letI : LawfulMonad (ErrorM f) := lawful (resetGraph f) (resetGraph_eq f)
  letI : LawfulFunctor (StateT T (ErrorM f)) := (law (σ := T) (m := ErrorM f)).toLawfulApplicative.toLawfulFunctor
  let input : StateT T (ErrorM f) PUnit := fun t => .error ⟨t, g t, agree t⟩
  let output (a : StateT T (ErrorM f) PUnit) (t : T) :=
    match a t with | .error s => s.2.val | .ok _ => t
  exact congrArg output (id_map input)

public theorem fromReaderTFunctor
    (law : type_of% @ReaderT.instLawfulFunctor.{max 1 u v, max 1 u v}) : type_of% @funext.{u,v} :=
  funextFromEndomorphisms (viaFunctor law)

public theorem fromReaderTApplicative
    (law : type_of% @ReaderT.instLawfulApplicative.{max 1 u v, max 1 u v}) : type_of% @funext.{u,v} :=
  funextFromEndomorphisms (viaApplicative law)

public theorem fromReaderTMonad
    (law : type_of% @ReaderT.instLawfulMonad.{max 1 u v, max 1 u v}) : type_of% @funext.{u,v} :=
  funextFromEndomorphisms (viaMonad law)

public theorem fromStateTMonad
    (law : type_of% @StateT.instLawfulMonad.{max 1 u v, max 1 u v}) : type_of% @funext.{u,v} :=
  funextFromEndomorphisms (viaState law)

@[instance_reducible] private def attached {T : Type u} (f : T → T) : MonadAttach (ErrorM f) where
  CanReturn {α} x a := match x with | .ok b => b = a | .error _ => False
  attach x := match x with | .ok b => .ok ⟨b, rfl⟩ | .error e => .error e

private theorem attachedLaw {T : Type u} (f : T → T) :
    letI := exceptionMonad (resetGraph f); letI := attached f; LawfulMonadAttach (ErrorM f) := by
  letI := exceptionMonad (resetGraph f)
  letI := attached f
  exact {
    map_attach := by
      intro _ x
      cases x with
      | error e => exact congrArg Except.error (resetGraph_eq f e)
      | ok _ => rfl
    canReturn_map_imp := by
      intro α P x a h
      cases x with
      | error e => exact False.elim h
      | ok b => exact h ▸ b.property
  }
private theorem ReaderTAttach {T : Type u} {f g : T → T} (agree : ∀ x, f x = g x)
    (law : letI := exceptionMonad (resetGraph f); letI := attached f;
      WeaklyLawfulMonadAttach (ReaderT T (ErrorM f))) : f = g := by
  letI := exceptionMonad (resetGraph f)
  letI := attached f
  letI : WeaklyLawfulMonadAttach (ReaderT T (ErrorM f)) := law
  let input : ReaderT T (ErrorM f) PUnit := fun t => .error ⟨t, g t, agree t⟩
  let output (a : ReaderT T (ErrorM f) PUnit) (t : T) :=
    match a t with | .error e => e.2.val | .ok _ => t
  exact congrArg output (WeaklyLawfulMonadAttach.map_attach (x := input))

public theorem fromReaderTWeakAttach (law : type_of% @instWeaklyLawfulMonadAttachReaderTOfLawfulMonad.{max 1 u v, max 1 u v}) :
    type_of% @funext.{u,v} := by
  apply funextFromEndomorphisms
  intro T f g agree
  letI := exceptionMonad (resetGraph f)
  letI : LawfulMonad (ErrorM f) := lawful (resetGraph f) (resetGraph_eq f)
  letI := attached f
  letI : LawfulMonadAttach (ErrorM f) := attachedLaw f
  exact ReaderTAttach agree ((law (ρ := T) (m := ErrorM f)))

public theorem fromReaderTAttach (law : type_of% @instLawfulMonadAttachReaderTOfLawfulMonad.{max 1 u v, max 1 u v}) :
    type_of% @funext.{u,v} := by
  apply funextFromEndomorphisms
  intro T f g agree
  letI := exceptionMonad (resetGraph f)
  letI : LawfulMonad (ErrorM f) := lawful (resetGraph f) (resetGraph_eq f)
  letI := attached f
  letI : LawfulMonadAttach (ErrorM f) := attachedLaw f
  exact ReaderTAttach agree ((law (ρ := T) (m := ErrorM f)).toWeaklyLawfulMonadAttach)

private theorem StateTAttach {T : Type u} {f g : T → T} (agree : ∀ x, f x = g x)
    (law : letI := exceptionMonad (resetGraph f); letI := attached f;
      WeaklyLawfulMonadAttach (StateT T (ErrorM f))) : f = g := by
  letI := exceptionMonad (resetGraph f)
  letI := attached f
  letI : WeaklyLawfulMonadAttach (StateT T (ErrorM f)) := law
  let input : StateT T (ErrorM f) PUnit := fun t => .error ⟨t, g t, agree t⟩
  let output (a : StateT T (ErrorM f) PUnit) (t : T) :=
    match a t with | .error e => e.2.val | .ok _ => t
  exact congrArg output (WeaklyLawfulMonadAttach.map_attach (x := input))

public theorem fromStateTWeakAttach (law : type_of% @instWeaklyLawfulMonadAttachStateTOfLawfulMonad.{max 1 u v, max 1 u v}) :
    type_of% @funext.{u,v} := by
  apply funextFromEndomorphisms
  intro T f g agree
  letI := exceptionMonad (resetGraph f)
  letI : LawfulMonad (ErrorM f) := lawful (resetGraph f) (resetGraph_eq f)
  letI := attached f
  letI : LawfulMonadAttach (ErrorM f) := attachedLaw f
  exact StateTAttach agree ((law (σ := T) (m := ErrorM f)))

public theorem fromStateTAttach (law : type_of% @instLawfulMonadAttachStateTOfLawfulMonad.{max 1 u v, max 1 u v}) :
    type_of% @funext.{u,v} := by
  apply funextFromEndomorphisms
  intro T f g agree
  letI := exceptionMonad (resetGraph f)
  letI : LawfulMonad (ErrorM f) := lawful (resetGraph f) (resetGraph_eq f)
  letI := attached f
  letI : LawfulMonadAttach (ErrorM f) := attachedLaw f
  exact StateTAttach agree ((law (σ := T) (m := ErrorM f)).toWeaklyLawfulMonadAttach)

open Lean in
run_cmd
  for n in [``fromReaderTWeakAttach, ``fromReaderTAttach, ``fromStateTWeakAttach, ``fromStateTAttach,
      ``fromReaderTFunctor, ``fromReaderTApplicative, ``fromReaderTMonad, ``fromStateTMonad] do
    unless (← collectAxioms n).isEmpty do throwError "transformer law witness {n} uses axioms"

private theorem constructorEndomorphisms (make : type_of% @LawfulMonad.mk'.{u,u})
    {T : Type u} {f g : T → T} (agree : ∀ x, f x = g x) : f = g := by
  let base : Monad (Except (Graph f)) := inferInstance
  let custom : Monad (ErrorM f) := { base with mapConst := fun a x =>
    match x with | .ok _ => .ok a | .error e => .error (resetGraph f e) }
  letI : Monad (ErrorM f) := custom
  let law := make (ErrorM f) (fun x => by cases x <;> rfl) (fun _ _ => rfl)
    (fun x _ _ => by cases x <;> rfl) (fun a x => by
      cases x with
      | ok b => rfl
      | error e => exact congrArg Except.error (resetGraph_eq f e))
    (fun x y => by cases x <;> cases y <;> rfl)
    (fun x y => by cases x <;> cases y <;> rfl)
    (fun k x => by cases x <;> rfl)
    (fun k x => by cases k <;> cases x <;> rfl)
  let input (t : T) : ErrorM f PUnit := .error ⟨t, g t, agree t⟩
  let see (k : PUnit → ErrorM f PUnit → ErrorM f PUnit) (t : T) :=
    match k .unit (input t) with | .error e => e.2.val | .ok _ => t
  exact congrArg see (@LawfulFunctor.map_const (ErrorM f) _ law.toLawfulApplicative.toLawfulFunctor PUnit PUnit)

public theorem fromMonadConstructor (make : type_of% @LawfulMonad.mk'.{max 1 u v, max 1 u v}) :
    type_of% @funext.{u,v} :=
  funextFromEndomorphisms (constructorEndomorphisms @make)

open Lean in
run_cmd
  unless (← collectAxioms ``fromMonadConstructor).isEmpty do throwError "monad constructor witness uses axioms"

end TransformerLaws

namespace MonadicTraversal

private def action {T : Type w} (k : T → T) (b : Option T) (flag : Bool) : ReaderM T (Option T) :=
  match flag with
  | false => fun x => some x
  | true => fun _ => b.map k

private theorem agree {T : Type w} {f g : T → T} (h : ∀ x, f x = g x)
    (b : Option T) (flag : Bool) : action f b flag = action g b flag := by
  cases flag with
  | false => rfl
  | true =>
    cases b with
    | none => rfl
    | some x => exact congrArg (fun y (_ : T) => some y) (h x)

private def extract {T : Type w} (r : ReaderM T (Option T)) (x : T) : T := (r x).getD x

private abbrev marked := { _b : Bool // True }

private def forward : List marked := [⟨false, trivial⟩, ⟨true, trivial⟩]
private def backward : List marked := [⟨true, trivial⟩, ⟨false, trivial⟩]

private theorem lawful (T : Type w) : LawfulMonad (ReaderM T) where
  id_map := by intros; rfl
  comp_map := by intros; rfl
  seq_pure := by intros; rfl
  seq_assoc := by intros; rfl
  map_pure := by intros; rfl
  map_const := by intros; rfl
  seqLeft_eq := by intros; rfl
  seqRight_eq := by intros; rfl
  pure_seq := by intros; rfl
  bind_pure_comp := by intros; rfl
  bind_map := by intros; rfl
  pure_bind := by intros; rfl
  bind_assoc := by intros; rfl

/-- A two-element left fold observes the callback on every reader input. -/
public theorem fromListFoldl (law : type_of% @List.foldlM_subtype.{max 1 u v,max 1 u v,0}) :
    type_of% @funext.{u,v} := by
  apply funextFromEndomorphisms
  intro T f g h
  have eq := @law (ReaderM T) Bool (Option T) _ _ forward
    (fun b a => action f b a.val) (action g) none (fun b a _ => agree h b a)
  exact congrArg extract eq

public theorem fromListFoldr (law : type_of% @List.foldrM_subtype.{max 1 u v,max 1 u v,0}) :
    type_of% @funext.{u,v} := by
  apply funextFromEndomorphisms
  intro T f g h
  have eq := @law (ReaderM T) Bool (Option T) _ (lawful T) _ backward
    (fun a b => action f b a.val) (fun a b => action g b a) none (fun a _ b => agree h b a)
  exact congrArg extract eq

open Lean in
run_cmd
  for n in [``fromListFoldl, ``fromListFoldr] do
    unless (← collectAxioms n).isEmpty do throwError "monadic traversal witness {n} uses axioms"

end MonadicTraversal

namespace RangeMap

open Std.PRange

@[instance_reducible] private def successor {T : Type w} (f : T → T) : UpwardEnumerable T where
  succ? x := some (f x)
  succMany? _ x := some x

private theorem endomorphisms {T : Type w}
    (commutes : type_of% @UpwardEnumerable.Map.succ?_toFun'.{w,w})
    {f g : T → T} (agree : ∀ x, f x = g x) : f = g := by
  let φ : @UpwardEnumerable.Map T T (successor g) (successor f) :=
    @UpwardEnumerable.Map.mk T T (successor g) (successor f) id (fun {_ _} h => h)
      (fun x => congrArg some (agree x)) (fun _ _ => rfl)
  have e := @commutes T T (successor g) (successor f) φ
  exact congrArg (fun k x => (k x).getD x) e

/-- The function equality for successor-preserving maps entails dependent function extensionality. -/
public theorem funextFromSuccMap (commutes : type_of% @UpwardEnumerable.Map.succ?_toFun'.{max 1 u v, max 1 u v}) :
    type_of% @funext.{u,v} :=
  funextFromEndomorphisms (endomorphisms commutes)

open Lean in
run_cmd
  unless (← collectAxioms ``funextFromSuccMap).isEmpty do
    throwError "the range-map extensionality witness depends on axioms"

end RangeMap

namespace IteratorLoopCongruence

open Std Std.Iterators

private abbrev State := ULift.{u} Bool

private def wrap {α : Type u} (x : α) : Shrink α :=
  cast (congrFun (Std.Internal.idOpaque (α := Type u)).property.symm α) x

@[instance_reducible] private def itInst (T : Type u) : Iterator State.{u} Id T where
  IsPlausibleStep it step := match step with
    | .done => True
    | .yield next _ => it.internalState.down = true ∧ next.internalState.down = false
    | .skip _ => False
  step _ := wrap ⟨.done, trivial⟩

private theorem finite (T : Type u) : letI := itInst T; Finite State.{u} Id := by
  letI := itInst T
  apply Finite.of_finitenessRelation
  let measure := fun it : IterM (α := State.{u}) Id T => Bool.toNat it.internalState.down
  refine ⟨InvImage Nat.lt measure, InvImage.wf _ Nat.lt_wfRel.wf, ?_⟩
  intro it next h
  obtain ⟨step, dest, h⟩ := h
  cases step with
  | yield j b =>
    cases Option.some.inj dest
    change it.internalState.down = true ∧ next.internalState.down = false at h
    change next.internalState.down.toNat < it.internalState.down.toNat
    rw [h.1, h.2]
    exact Nat.zero_lt_one
  | skip j => contradiction
  | done => cases dest

@[instance_reducible] private def reading (T : Type u) :
    letI := itInst T; IteratorLoop State.{u} Id (ReaderM T) := by
  letI := itInst T
  refine ⟨fun _ γ Pl it init f x => ?_⟩
  cases active : it.internalState.down with
  | false => exact init
  | true =>
    have out : it.IsPlausibleIndirectOutput x :=
      .direct ⟨⟨⟨false⟩⟩, ⟨active, rfl⟩⟩
    exact ForInStep.casesOn (f x out init x).val id id

private theorem endomorphisms (combine : type_of% (@Iter.forIn_congr.{u,u}))
    {T : Type u} {f g : T → T} (agree : ∀ x, f x = g x) : f = g := by
  letI := itInst T
  letI := finite T
  letI := reading T
  let i : Iter (α := State.{u}) T := ⟨⟨true⟩⟩
  let finish (y : T) : ReaderM T (ForInStep (Option T)) := fun _ => .done (some y)
  have eq := combine (ita := i) (itb := i) rfl (b := (none : Option T)) rfl
    (f := fun x _ => finish (f x)) (g := fun x _ => finish (g x)) (fun x _ => congrArg finish (agree x))
  exact congrArg (fun (k : T → Option T) x => (k x).getD x) eq


private theorem monadicEndomorphisms (combine : type_of% (@IterM.forIn_congr.{u,u,u}))
    {T : Type u} {f g : T → T} (agree : ∀ x, f x = g x) : f = g := by
  letI := itInst T
  letI := reading T
  letI : MonadLift Id (ReaderM T) := ⟨fun x _ => x⟩
  let i : IterM (α := State.{u}) Id T := ⟨⟨true⟩⟩
  let finish (y : T) : ReaderM T (ForInStep (Option T)) := fun _ => .done (some y)
  have eq := combine (ita := i) (itb := i) rfl (b := (none : Option T)) rfl
    (f := fun x _ => finish (f x)) (g := fun x _ => finish (g x)) (fun x _ => congrArg finish (agree x))
  exact congrArg (fun (k : T → Option T) x => (k x).getD x) eq

private theorem forgetMonadicMembership (combine : type_of% @IterM.forIn'_congr.{u,u,u}) :
    type_of% @IterM.forIn_congr.{u,u,u} := by
  intro α β m n monN monM iterator loop lift γ ita itb w b b' hb f g agree
  cases w
  exact combine rfl hb (fun a _ c => agree a c)

public theorem funextFromMonadicCongr (combine : type_of% @IterM.forIn_congr.{max 1 u v, max 1 u v,max 1 u v}) :
    type_of% @funext.{u,v} :=
  funextFromEndomorphisms (monadicEndomorphisms combine)

public theorem funextFromMonadicCongr' (combine : type_of% @IterM.forIn'_congr.{max 1 u v, max 1 u v,max 1 u v}) :
    type_of% @funext.{u,v} :=
  funextFromMonadicCongr (forgetMonadicMembership combine)

/-- Membership-dependent loop congruence specializes to ordinary loop congruence. -/
private theorem forgetMembership (combine : type_of% (@Iter.forIn'_congr.{u,u})) :
    type_of% (@Iter.forIn_congr.{u,u}) := by
  intro α β m monad iterator fin loop γ ita itb w b b' hb f g agree
  cases w
  exact combine rfl hb (fun a _ c => agree a c)

/-- A loop on a reader can select an output at each argument of the reader. -/
public theorem funextFromCongr (combine : type_of% @Iter.forIn_congr.{max 1 u v, max 1 u v}) :
    type_of% @funext.{u,v} :=
  funextFromEndomorphisms (endomorphisms combine)

public theorem funextFromCongr' (combine : type_of% @Iter.forIn'_congr.{max 1 u v, max 1 u v}) :
    type_of% @funext.{u,v} :=
  funextFromCongr (forgetMembership combine)

open Lean in
run_cmd
  for n in [``funextFromCongr, ``funextFromCongr', ``funextFromMonadicCongr, ``funextFromMonadicCongr'] do
    unless (← collectAxioms n).isEmpty do throwError "iterator congruence witness {n} uses axioms"

end IteratorLoopCongruence

namespace Collector

open Std Std.Iterators

private def next (f : Nat → Bool) (it : IterM (α := Nat) Id Unit) : IterStep (IterM (α := Nat) Id Unit) Unit :=
  match f it.internalState with
  | true => .done
  | false => .yield ⟨it.internalState + 1⟩ ()

@[instance_reducible] private def searchIterator (f : Nat → Bool) : Iterator Nat Id Unit where
  IsPlausibleStep it s := s = next f it
  step it := pure (.deflate ⟨next f it, rfl⟩)

private def search (k : Nat) : Iter (α := Nat) Unit := ⟨k⟩

private theorem signal_after {f : Nat → Bool} (sticky : ∀ i, f i = true → f (i+1) = true)
    {n : Nat} (hit : f n = true) {k : Nat} (le : n ≤ k) : f k = true := by
  induction le with
  | refl => exact hit
  | step _ ih => exact sticky _ ih

private theorem searchFinite {f : Nat → Bool} (sticky : ∀ i, f i = true → f (i+1) = true)
    {n : Nat} (hit : f n = true) :
    letI := searchIterator f
    Finite Nat Id := by
  letI := searchIterator f
  apply Finite.of_finitenessRelation
  refine ⟨InvImage Nat.lt (fun it : IterM (α := Nat) Id Unit => n - it.internalState),
    InvImage.wf _ Nat.lt_wfRel.wf, ?_⟩
  intro it it' h
  obtain ⟨s, dest, step⟩ := h
  change s = next f it at step
  subst s
  dsimp only [next] at dest
  cases e : f it.internalState with
  | true => rw [e] at dest; cases dest
  | false =>
    rw [e] at dest
    cases Option.some.inj dest
    have lt : it.internalState < n := Nat.lt_of_not_ge fun ge => Bool.noConfusion (e.symm.trans (signal_after sticky hit ge))
    change n - (it.internalState + 1) < n - it.internalState
    omega

private theorem searchStep (f : Nat → Bool) (k : Nat) :
    letI := searchIterator f
    (search k).step.val = (match f k with | true => .done | false => .yield (search (k+1)) ()) := by
  letI := searchIterator f
  change (IterM.Step.toPure (it := (search k).toIterM) (Shrink.inflate (Shrink.deflate _))).val = _
  refine Eq.trans (congrArg (fun q => (IterM.Step.toPure (it := (search k).toIterM) q).val) Shrink.inflate_deflate) ?_
  cases e : f k <;> simp only [search, next, IterM.Step.toPure, IterStep.mapIterator,
    Iter.toIterM, IterM.toIter, e] <;> rfl

private theorem length_hits {f : Nat → Bool} (sticky : ∀ i, f i = true → f (i+1) = true)
    {n : Nat} (hit : f n = true)
    (len : Nat → Nat)
    (unroll : ∀ k, len k = (match f k with | true => 0 | false => (len (k+1)).succ))
    (k : Nat) : f (k + len k) = true := by
  generalize h : n - k = fuel
  induction fuel generalizing k with
  | zero =>
    have yes := signal_after sticky hit (Nat.le_of_sub_eq_zero h)
    have l := unroll k
    rw [yes] at l
    simpa only [l, Nat.add_zero] using yes
  | succ fuel ih =>
    have l := unroll k
    cases e : f k with
    | true => rw [e] at l; simpa only [l, Nat.add_zero] using e
    | false =>
      rw [e] at l
      change len k = (len (k+1)).succ at l
      have eq : n - (k+1) = fuel := by omega
      have out := ih (k+1) eq
      exact (congrArg f (by omega : k + len k = k + 1 + len (k + 1))).trans out

private def seen (f : Nat → Bool) : Nat → Bool
  | 0 => f 0
  | n+1 => seen f n || f (n+1)

private theorem seenSticky (f : Nat → Bool) (n : Nat) (h : seen f n = true) :
    seen f (n+1) = true := by rw [seen, h]; rfl

private theorem seen_of_hit (f : Nat → Bool) (n : Nat) (hit : f n = true) :
    seen f n = true := by
  cases n with
  | zero => exact hit
  | succ n => rw [seen, hit, Bool.or_true]

private theorem hit_of_seen (f : Nat → Bool) (n : Nat) (h : seen f n = true) : ∃ k, f k = true := by
  induction n with
  | zero => exact ⟨0, h⟩
  | succ n ih =>
    cases eq : f (n+1) with
    | true => exact ⟨n+1, eq⟩
    | false => exact ih (by simpa only [seen, eq, Bool.or_false] using h)

/-- A decider for all Boolean streams cannot examine a bounded prefix at the all-false stream. -/
theorem noContinuousSignalDecider
    (answer : (Nat → Bool) → Bool)
    (correct : ∀ f, answer f = true ↔ ∃ n, f n = true)
    (stable : ∃ k, ∀ f : Nat → Bool, (∀ i, i < k → f i = false) →
      answer f = answer (fun _ => false)) : False := by
  obtain ⟨k, same⟩ := stable
  let spike (i : Nat) := Nat.beq i k
  have yes := (correct spike).mpr ⟨k, Nat.beq_refl k⟩
  have noSignal : ¬ ∃ n : Nat, false = true := fun ⟨_, h⟩ => Bool.noConfusion h
  apply noSignal
  apply (correct (fun _ => false)).mp
  have agree (i : Nat) (lt : i < k) : spike i = false := by
    cases eq : spike i with
    | false => rfl
    | true => exact False.elim ((Nat.ne_of_lt lt) (Nat.eq_of_beq_eq_true eq))
  exact (same spike agree).symm.trans yes

private def limitedOmniscienceFromLength
    (measure : ∀ {α β : Type} [Iterator α Id β], Iter (α := α) β → Nat)
    (correct : ∀ {α β : Type} [Iterator α Id β] [Finite α Id] (it : Iter (α := α) β),
      measure it = it.toList.length) (f : Nat → Bool) : Decidable (∃ n, f n = true) := by
  let g := seen f
  letI := searchIterator g
  let len := fun k => measure (search k)
  cases h : g (len 0) with
  | true => exact isTrue (hit_of_seen f _ h)
  | false =>
    refine isFalse fun ⟨n, hit⟩ => ?_
    have gHit := seen_of_hit f n hit
    letI := searchFinite (seenSticky f) gHit
    have unroll (k : Nat) : len k = (match g k with | true => 0 | false => (len (k+1)).succ) := by
      unfold len
      rw [correct (search k), Iter.toList_eq_match_step, searchStep]
      cases e : g k with
      | true => rfl
      | false => exact congrArg Nat.succ (correct (search (k+1))).symm
    have result := length_hits (seenSticky f) gHit len unroll 0
    exact Bool.noConfusion (h.symm.trans (by simpa only [Nat.zero_add] using result))

/-- Agreement with the official collector on finite iterators gives the limited principle
of omniscience for arbitrary Boolean streams. -/
def limitedOmniscienceFromCollector (collect : type_of% (@Std.Iter.toList.{0}))
    (correct : ∀ {α β : Type} [Iterator α Id β] [Finite α Id] (it : Iter (α := α) β),
      collect it = it.toList) (f : Nat → Bool) : Decidable (∃ n, f n = true) :=
  limitedOmniscienceFromLength (fun it => (collect it).length)
    (fun it => congrArg List.length (correct it)) f

/-- A universal default loop can count outputs before the first signal. It suffices that its
identity-monad specialization agrees with the official loop on finite iterators. -/
def limitedOmniscienceFromDefaultLoop (loop : type_of% (@Std.IteratorLoop.defaultImplementation.{0,0,0,0}))
    (correct : ∀ {α β : Type} [inst : Iterator α Id β] [Finite α Id],
      @loop β α Id Id _ inst = @IteratorLoop.defaultImplementation β α Id Id _ inst)
    (f : Nat → Bool) : Decidable (∃ n, f n = true) := by
  apply limitedOmniscienceFromLength (f := f) (fun {α β} [inst : Iterator α Id β] it =>
    letI := @loop β α Id Id _ inst
    it.length)
  intro α β inst finite it
  rw [correct]
  letI : IteratorLoop α Id Id := .defaultImplementation
  exact Iter.length_toList_eq_length.symm

/-- An array collector on unrestricted iterators also gives a list collector pointwise. -/
def limitedOmniscienceFromArray (collect : type_of% (@Std.Iter.toArray.{0}))
    (correct : ∀ {α β : Type} [Iterator α Id β] [Finite α Id] (it : Iter (α := α) β),
      collect it = it.toArray) (f : Nat → Bool) : Decidable (∃ n, f n = true) :=
  limitedOmniscienceFromCollector (fun it => (collect it).toList)
    (fun it => (congrArg Array.toList (correct it)).trans Iter.toList_toArray) f

/-- Reversing the reverse collector recovers the ordinary collector on every finite iterator. -/
def limitedOmniscienceFromReverse (collect : type_of% (@Std.Iter.toListRev.{0}))
    (correct : ∀ {α β : Type} [Iterator α Id β] [Finite α Id] (it : Iter (α := α) β),
      collect it = it.toListRev) (f : Nat → Bool) : Decidable (∃ n, f n = true) :=
  limitedOmniscienceFromCollector (fun it => (collect it).reverse)
    (fun it => (congrArg List.reverse (correct it)).trans Iter.reverse_toListRev) f

/-- A slice may use the iterator itself as its internal representation. -/
def limitedOmniscienceFromSlice (collect : type_of% (@Std.Slice.toList.{0,0}))
    (correct : ∀ {γ α β : Type} [ToIterator (Slice γ) Id α β] [Iterator α Id β]
      [Finite α Id] (s : Slice γ), collect s = s.toList) (f : Nat → Bool) :
    Decidable (∃ n, f n = true) := by
  apply limitedOmniscienceFromCollector (f := f) (fun {α β} [Iterator α Id β] it =>
    letI := ToIterator.of (γ := Slice (Iter (α := α) β)) α (fun s => s.internalRepresentation)
    collect ⟨it⟩)
  intro α β inst fin it
  letI := ToIterator.of (γ := Slice (Iter (α := α) β)) α (fun s => s.internalRepresentation)
  exact correct (Slice.mk it)

/-- Specializing monadic collection to the identity monad preserves the unrestricted pure interface. -/
def limitedOmniscienceFromMonadicCollector (collect : type_of% (@Std.IterM.toList.{0,0}))
    (correct : ∀ {α β : Type} [Iterator α Id β] [Finite α Id] (it : IterM (α := α) Id β),
      collect it = it.toList) (f : Nat → Bool) : Decidable (∃ n, f n = true) :=
  limitedOmniscienceFromCollector (fun it => (collect it.toIterM).run)
    (fun it => (correct it.toIterM).trans Iter.toList_eq_toList_toIterM.symm) f

/-- Only the identity-monad specialization is needed for the array collector. -/
def limitedOmniscienceFromMonadicArray (collect : type_of% (@Std.IterM.toArray.{0,0}))
    (correct : ∀ {α β : Type} [Iterator α Id β] [Finite α Id] (it : IterM (α := α) Id β),
      collect it = it.toArray) (f : Nat → Bool) : Decidable (∃ n, f n = true) :=
  limitedOmniscienceFromArray (fun it => (collect it.toIterM).run)
    (fun it => (correct it.toIterM).trans Iter.toArray_eq_toArray_toIterM.symm) f

/-- Only the identity-monad specialization is needed for the reverse collector. -/
def limitedOmniscienceFromMonadicReverse (collect : type_of% (@Std.IterM.toListRev.{0,0}))
    (correct : ∀ {α β : Type} [Iterator α Id β] [Finite α Id] (it : IterM (α := α) Id β),
      collect it = it.toListRev) (f : Nat → Bool) : Decidable (∃ n, f n = true) :=
  limitedOmniscienceFromReverse (fun it => (collect it.toIterM).run)
    (fun it => (correct it.toIterM).trans Iter.toListRev_eq_toListRev_toIterM.symm) f

/-- Rendering every output as one character makes the string length count the iterator's outputs. -/
@[instance_reducible] private def markerString (β : Type) : ToString β := ⟨fun _ => String.singleton 'x'⟩

def limitedOmniscienceFromStringList (collect : type_of% @Std.Iter.toStringList)
    (correct : ∀ {α β : Type} [Iterator α Id β] [Finite α Id] [ToString β] (it : Iter (α := α) β),
      collect it = it.toStringList) (f : Nat → Bool) : Decidable (∃ n, f n = true) := by
  apply limitedOmniscienceFromLength (f := f) (fun {α β} [Iterator α Id β] it =>
    letI := markerString β
    (collect it).length)
  intro α β inst fin it
  letI := markerString β
  rw [correct, Iter.toStringList, Iter.toList_map, List.length_map]

def limitedOmniscienceFromStringArray (collect : type_of% @Std.Iter.toStringArray)
    (correct : ∀ {α β : Type} [Iterator α Id β] [Finite α Id] [ToString β] (it : Iter (α := α) β),
      collect it = it.toStringArray) (f : Nat → Bool) : Decidable (∃ n, f n = true) := by
  apply limitedOmniscienceFromStringList (fun it => (collect it).toList) _ f
  intro α β inst fin fmt it
  rw [correct, Iter.toStringArray, Iter.toStringList, Iter.toList_toArray]

private theorem markerLength (xs : List β) :
    (String.join (xs.map (fun _ => String.singleton 'x'))).toList.length = xs.length := by
  rw [String.toList_join]
  induction xs with
  | nil => rfl
  | cons a as ih =>
    rw [List.map_cons, List.flatMap_cons, String.toList_singleton, List.singleton_append]
    exact congrArg Nat.succ ih

def limitedOmniscienceFromStringJoin (join : type_of% @Std.Iter.joinString)
    (correct : ∀ {α β : Type} [Iterator α Id β] [Finite α Id] [ToString β] (it : Iter (α := α) β),
      join it = String.join (it.toList.map toString)) (f : Nat → Bool) : Decidable (∃ n, f n = true) := by
  apply limitedOmniscienceFromLength (f := f) (fun {α β} [Iterator α Id β] it =>
    letI := markerString β
    (join it).toList.length)
  intro α β inst fin it
  letI := markerString β
  rw [correct]
  exact markerLength _

def limitedOmniscienceFromStringIntercalate (join : type_of% @Std.Iter.intercalateString)
    (correct : ∀ {α β : Type} [Iterator α Id β] [Finite α Id] [ToString β]
      (s : String.Slice) (it : Iter (α := α) β), join s it = s.copy.intercalate (it.toList.map toString))
    (f : Nat → Bool) : Decidable (∃ n, f n = true) := by
  apply limitedOmniscienceFromStringJoin (fun it => join "".toSlice it) _ f
  intro α β inst fin fmt it
  rw [correct, String.copy_toSlice]
  generalize it.toList.map toString = xs
  induction xs with
  | nil => exact String.intercalate_nil.trans String.join_nil.symm
  | cons x xs ih =>
    rw [String.join_cons, ← ih]
    cases xs with
    | nil => rw [String.intercalate_singleton, String.intercalate_nil, String.append_empty]
    | cons y ys => rw [String.intercalate_cons_cons, String.append_empty]

private def indexStep (f : Nat → Bool) (it : IterM (α := Option Nat) Id Nat) :
    IterStep (IterM (α := Option Nat) Id Nat) Nat :=
  match it.internalState with
  | none => .done
  | some k => if f k then .yield ⟨none⟩ k else .skip ⟨some (k+1)⟩

@[instance_reducible] private def indexIterator (f : Nat → Bool) : Iterator (Option Nat) Id Nat where
  IsPlausibleStep it s := s = indexStep f it
  step it := pure (.deflate ⟨indexStep f it, rfl⟩)

private theorem indexFinite {f : Nat → Bool} (sticky : ∀ i, f i = true → f (i+1) = true)
    {n : Nat} (hit : f n = true) :
    letI := indexIterator f
    Finite (Option Nat) Id := by
  letI := indexIterator f
  let rank (it : IterM (α := Option Nat) Id Nat) := it.internalState.elim 0 (fun k => n - k + 1)
  apply Finite.of_finitenessRelation
  refine ⟨InvImage Nat.lt rank, InvImage.wf _ Nat.lt_wfRel.wf, ?_⟩
  intro it next h
  obtain ⟨s, dest, step⟩ := h
  change s = indexStep f it at step
  subst s
  rcases it with ⟨_ | k⟩
  · cases dest
  · dsimp only [indexStep] at dest
    cases e : f k with
    | true =>
      rw [e] at dest
      cases Option.some.inj dest
      exact Nat.zero_lt_succ _
    | false =>
      rw [e] at dest
      cases Option.some.inj dest
      have lt : k < n := Nat.lt_of_not_ge fun ge =>
        Bool.noConfusion (e.symm.trans (signal_after sticky hit ge))
      change n - (k + 1) + 1 < n - k + 1
      omega

private theorem firstIndexHit {f : Nat → Bool} (sticky : ∀ i, f i = true → f (i+1) = true)
    {n : Nat} (hit : f n = true) (k : Nat) :
    letI := indexIterator f
    ∃ j, (⟨some k⟩ : Iter (α := Option Nat) Nat).atIdxSlow? 0 = some j ∧ f j = true := by
  letI := indexIterator f
  letI := indexFinite sticky hit
  have unroll (k : Nat) :
      (⟨some k⟩ : Iter (α := Option Nat) Nat).atIdxSlow? 0 =
        if f k then some k else (⟨some (k+1)⟩ : Iter (α := Option Nat) Nat).atIdxSlow? 0 := by
    rw [Iter.atIdxSlow?_eq_match]
    have eq := congrArg (fun q => (IterM.Step.toPure (it := (⟨some k⟩ : Iter (α := Option Nat) Nat).toIterM) q).val)
      (Shrink.inflate_deflate (x := (⟨indexStep f ⟨some k⟩, rfl⟩ : (⟨some k⟩ : IterM (α := Option Nat) Id Nat).Step)))
    change (⟨some k⟩ : Iter (α := Option Nat) Nat).step.val = _ at eq
    rw [eq]
    cases e : f k <;> simp [IterM.Step.toPure, indexStep, e, IterStep.mapIterator, IterM.toIter]
  generalize heq : n - k = fuel
  induction fuel generalizing k with
  | zero =>
    have yes := signal_after sticky hit (Nat.le_of_sub_eq_zero heq)
    exact ⟨k, by rw [unroll, yes]; rfl, yes⟩
  | succ fuel ih =>
    cases e : f k with
    | true => exact ⟨k, by rw [unroll, e]; rfl, e⟩
    | false =>
      obtain ⟨j, hj, h⟩ := ih (k+1) (by omega)
      exact ⟨j, by rw [unroll, e]; exact hj, h⟩

/-- The unrestricted lookup accepts iterators that skip before their first output.
For a stream with a signal its first output can be the location of that signal. -/
def limitedOmniscienceFromLookup (lookup : type_of% (@Std.Iter.atIdxSlow?.{0}))
    (correct : ∀ {α β : Type} [Iterator α Id β] [Finite α Id] (i : Nat) (it : Iter (α := α) β),
      lookup i it = it.atIdxSlow? i) (f : Nat → Bool) : Decidable (∃ i, f i = true) := by
  letI := indexIterator (seen f)
  let it : Iter (α := Option Nat) Nat := ⟨some 0⟩
  cases h : lookup 0 it with
  | none =>
    refine isFalse fun ⟨k, hk⟩ => ?_
    have yes := seen_of_hit f k hk
    letI := indexFinite (seenSticky f) yes
    obtain ⟨j, hj, _⟩ := firstIndexHit (seenSticky f) yes 0
    cases h.symm.trans ((correct 0 it).trans hj)
  | some j =>
    cases e : seen f j with
    | true => exact isTrue (hit_of_seen f j e)
    | false =>
      refine isFalse fun ⟨k, hk⟩ => ?_
      have yes := seen_of_hit f k hk
      letI := indexFinite (seenSticky f) yes
      obtain ⟨j', hj, sign⟩ := firstIndexHit (seenSticky f) yes 0
      cases Option.some.inj (h.symm.trans ((correct 0 it).trans hj))
      exact Bool.noConfusion (e.symm.trans sign)

open Std.Iterators.Types

/-- Identity mapping carries an arbitrary input iterator through the map loop without
changing its number of outputs. -/
def limitedOmniscienceFromMapLoop (loop : type_of% (@Map.instIteratorLoop.{0,0,0,0,0}))
    (correct : ∀ {α β : Type} [inst : Iterator α Id β] [Finite α Id],
      @loop α β β Id Id Id _ _ inst (fun _ => monadLift) (fun b => pure b) =
        @Map.instIteratorLoop α β β Id Id Id _ _ inst (fun _ => monadLift) (fun b => pure b))
    (f : Nat → Bool) : Decidable (∃ n, f n = true) := by
  apply limitedOmniscienceFromLength (f := f) (fun {α β} [inst : Iterator α Id β] it =>
    letI := @loop α β β Id Id Id _ _ inst (fun _ => monadLift) (fun b => pure b)
    (it.map id).length)
  intro α β inst finite it
  rw [correct]
  letI : IteratorLoop α Id Id := .defaultImplementation
  exact Iter.length_map.trans Iter.length_toList_eq_length.symm

/-- Attaching the constantly true predicate keeps every original output. -/
def limitedOmniscienceFromAttachLoop (loop : type_of% (@Attach.instIteratorLoop.{0,0,0,0}))
    (correct : ∀ {α β : Type} [inst : Iterator α Id β] [Finite α Id],
      @loop α β Id _ Id _ (fun _ => True) inst = @Attach.instIteratorLoop α β Id _ Id _ (fun _ => True) inst)
    (f : Nat → Bool) : Decidable (∃ n, f n = true) := by
  apply limitedOmniscienceFromLength (f := f) (fun {α β} [inst : Iterator α Id β] it =>
    letI := @loop α β Id _ Id _ (fun _ => True) inst
    (it.attachWith (fun _ => True) (fun _ _ => trivial)).length)
  intro α β inst finite it
  rw [correct]
  letI : IteratorLoop α Id Id := .defaultImplementation
  exact Iter.length_attachWith.trans Iter.length_toList_eq_length.symm

/-- Universe lifting keeps every output, including for a same-universe lift. -/
def limitedOmniscienceFromULiftLoop (loop : type_of% (@ULiftIterator.instIteratorLoop.{0,0,0,0,0,0}))
    (correct : ∀ {α β : Type} [inst : Iterator α Id β] [Finite α Id],
      @loop α Id Id β (fun _ => monadLift) Id _ _ inst =
        @ULiftIterator.instIteratorLoop α Id Id β (fun _ => monadLift) Id _ _ inst)
    (f : Nat → Bool) : Decidable (∃ n, f n = true) := by
  apply limitedOmniscienceFromLength (f := f) (fun {α β} [inst : Iterator α Id β] it =>
    letI := @loop α Id Id β (fun _ => monadLift) Id _ _ inst
    it.uLift.length)
  intro α β inst finite it
  rw [correct]
  letI : IteratorLoop α Id Id := .defaultImplementation
  exact Iter.length_uLift.trans Iter.length_toList_eq_length.symm

/-- A filter-map that returns every element preserves the output count. -/
def limitedOmniscienceFromFilterMapLoop (loop : type_of% (@FilterMap.instIteratorLoop.{0,0,0,0,0}))
    (correct : ∀ {α β : Type} [inst : Iterator α Id β] [Finite α Id],
      @loop α β β Id Id Id _ _ inst (fun _ => monadLift) (fun b => pure (some b)) =
        @FilterMap.instIteratorLoop α β β Id Id Id _ _ inst (fun _ => monadLift) (fun b => pure (some b)))
    (f : Nat → Bool) : Decidable (∃ n, f n = true) := by
  apply limitedOmniscienceFromLength (f := f) (fun {α β} [inst : Iterator α Id β] it =>
    letI := @loop α β β Id Id Id _ _ inst (fun _ => monadLift) (fun b => pure (some b))
    (it.filterMap some).length)
  intro α β inst finite it
  rw [correct]
  letI := FilterMap.instIteratorLoop (α := α) (β := β) (γ := β) (m := Id) (n := Id) (o := Id)
    (lift := fun _ => monadLift) (f := fun b => pure (some b))
  exact Iter.length_toList_eq_length.symm.trans
    (congrArg List.length ((Iter.toList_filterMap (it := it) (f := some)).trans (List.filterMap_some ..)))

/-- Appending an empty list iterator preserves the entire input. -/
def limitedOmniscienceFromAppendLoop (loop : type_of% (@Append.instIteratorLoop.{0,0,0,0}))
    (correct : ∀ {α β : Type} [inst : Iterator α Id β] [Finite α Id],
      @loop Id β α (ListIterator β) Id _ _ inst _ = @Append.instIteratorLoop Id β α (ListIterator β) Id _ _ inst _)
    (f : Nat → Bool) : Decidable (∃ n, f n = true) := by
  apply limitedOmniscienceFromLength (f := f) (fun {α β} [inst : Iterator α Id β] it =>
    letI := @loop Id β α (ListIterator β) Id _ _ inst _
    (it.append ([] : List β).iter).length)
  intro α β inst finite it
  rw [correct]
  simp only [← Iter.length_toList_eq_length, Iter.toList_append, List.toList_iter, List.append_nil]

/-- Flattening singleton list iterators preserves the full output sequence. -/
def limitedOmniscienceFromFlattenLoop (loop : type_of% (@Flatten.instIteratorLoop.{0,0,0,0}))
    (correct : ∀ {α α₂ β : Type} [out : Iterator α Id (IterM (α := α₂) Id β)]
      [inner : Iterator α₂ Id β] [Finite α Id] [Finite α₂ Id],
      @loop α α₂ β Id Id _ _ out inner = @Flatten.instIteratorLoop α α₂ β Id Id _ _ out inner)
    (f : Nat → Bool) : Decidable (∃ n, f n = true) := by
  apply limitedOmniscienceFromLength (f := f) (fun {α β} [inst : Iterator α Id β] it =>
    letI := @loop (Map α Id Id (fun _ => monadLift) (fun b : β => pure ([b].iter.toIterM))) (ListIterator β)
      β Id Id _ _ inferInstance inferInstance
    (it.flatMap (fun b => [b].iter)).length)
  intro α β inst finite it
  rw [correct]
  letI := @Flatten.instIteratorLoop (Map α Id Id (fun _ => monadLift) (fun b : β => pure ([b].iter.toIterM)))
    (ListIterator β) β Id Id _ _ inferInstance inferInstance
  have eq := Iter.length_toList_eq_length (it := it.flatMap fun b => [b].iter)
  rw [Iter.toList_flatMap, Iter.toList_map] at eq
  simpa [List.toList_iter, ← List.flatMap_def] using eq.symm

/-- Taking one output suffices to implement lookup at index zero when searching for a signal. -/
def limitedOmniscienceFromTakeLoop (loop : type_of% (@Take.instIteratorLoop.{0,0,0,0}))
    (correct : ∀ {α β : Type} [inst : Iterator α Id β] [Finite α Id],
      @loop α Id β Id _ _ inst = @Take.instIteratorLoop α Id β Id _ _ inst)
    (f : Nat → Bool) : Decidable (∃ n, f n = true) := by
  apply limitedOmniscienceFromLookup (f := f) (fun {α β} [inst : Iterator α Id β] n it =>
    letI := @loop α Id β Id _ _ inst
    ((it.take (n+1)).fold (init := ([] : List β)) fun xs b => b :: xs).reverse[n]?)
  intro α β inst finite n it
  rw [correct]
  letI := @Take.instIteratorLoop α Id β Id _ _ inst
  rw [← Iter.foldl_toList, List.foldl_flip_cons_eq_append', List.append_nil, List.reverse_reverse,
    Iter.toList_take_of_finite, List.getElem?_take, ite_eq_left (Nat.lt_succ_self _)]
  exact Iter.getElem?_toList_eq_atIdxSlow?

end Collector

end OmegaChecks.InitBoundaries

private def installedModules (dir : System.FilePath) (root : Name) : IO (Array Name) := do
  let mut modules := if ← (modToFilePath dir root "olean").pathExists then #[root] else #[]
  for file in ← (dir / root.toString).walkDir do
    if file.extension == some "olean" then
      modules := modules.push (← moduleNameOfFileName file dir)
  return modules.qsort Name.lt

private def declarationKind : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotientPrimitive"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

/-- The pinned Lean evaluator can calculate these on closed natural numbers
even when the public constant has no definition body (notably Nat.gcd). -/
private def officialReduction (env : Environment) (n : Name) : Option String := do
  let info ← env.find? n
  if #[`Nat.succ, `Nat.add, `Nat.sub, `Nat.mul, `Nat.div, `Nat.mod, `Nat.pow, `Nat.gcd,
       `Nat.beq, `Nat.ble, `Nat.land, `Nat.lor, `Nat.xor, `Nat.shiftLeft, `Nat.shiftRight].contains n then
    return "builtin natural-number reduction"
  match info with
  | .defnInfo _ => return "public definition body"
  | .recInfo _ => return "recursor computation rule"
  | .ctorInfo _ => return "constructor computation rule"
  | .inductInfo _ => return "primitive inductive type"
  | _ => none

/-- One shortest implementation-body path to a sealed strict implementation
whose official counterpart has a public computation rule or inductive interface. -/
private def reductionPaths (official strict full : Environment) : NameMap (List Name × String) := Id.run do
  let mut users : NameMap (Array Name) := {}
  let mut paths : NameMap (List Name × String) := {}
  let mut todo := #[]
  for (n, info) in full.constants.toList do
    let some value := info.value? (allowOpaque := true) | continue
    if !(strict.find? n).any (· matches .defnInfo _) then
      if let some rule := officialReduction official (n.replacePrefix `Omega .anonymous) then
        paths := paths.insert n ([n], rule)
        todo := todo.push n
    if info matches .defnInfo _ | .opaqueInfo _ then
      for dep in value.getUsedConstantsAsSet do
        users := users.insert dep ((users.getD dep #[]).push n)
  todo := todo.qsort Name.lt
  let mut i := 0
  while h : i < todo.size do
    let dependency := todo[i]
    i := i + 1
    let some (path, rule) := paths.get? dependency | continue
    for n in (users.getD dependency #[]).qsort Name.lt do
      unless paths.contains n do
        paths := paths.insert n (n :: path, rule)
        todo := todo.push n
  return paths

/-- Additional logical consequences with separate proof terms. These do not discharge a
missing official interface in the completeness check. -/
private def logicalConsequence? (owner name : Name) : Option (Name × Name) := do
  match owner, name with
  | `Init.Data.List.Lemmas, ``List.eq_replicate_or_eq_replicate_append_cons =>
    return (``OmegaChecks.InitBoundaries.FiniteMembership.EqualityCases,
      ``OmegaChecks.InitBoundaries.FiniteMembership.ofRunDecomposition)
  | `Init.Data.List.Lemmas, ``List.replicateRecOn =>
    return (``OmegaChecks.InitBoundaries.FiniteMembership.EqualityCases,
      ``OmegaChecks.InitBoundaries.FiniteMembership.ofRunInduction)
  | `Init.Data.List.Lemmas, ``List.eq_or_ne_mem_of_mem =>
    return (``OmegaChecks.InitBoundaries.FiniteMembership.EqualityCases,
      ``OmegaChecks.InitBoundaries.FiniteMembership.ofListMember)
  | `Init.Data.Array.Lemmas, ``Array.eq_or_ne_mem_of_mem =>
    return (``OmegaChecks.InitBoundaries.FiniteMembership.EqualityCases,
      ``OmegaChecks.InitBoundaries.FiniteMembership.ofArrayMember)
  | `Init.Data.List.Lemmas, ``List.eq_append_cons_of_mem =>
    return (``OmegaChecks.InitBoundaries.FiniteMembership.EqualityCases,
      ``OmegaChecks.InitBoundaries.FiniteMembership.ofFirstListMember)
  | `Init.Data.Array.Lemmas, ``Array.eq_push_append_of_mem =>
    return (``OmegaChecks.InitBoundaries.FiniteMembership.EqualityCases,
      ``OmegaChecks.InitBoundaries.FiniteMembership.ofFirstArrayMember)
  | `Init.Internal.Order.Basic, ``Lean.Order.inf =>
    return (``OmegaChecks.InitBoundaries.InternalOrder.UniqueChoice,
      ``OmegaChecks.InitBoundaries.InternalOrder.uniqueChoiceOfSup)
  | `Init.Internal.Order.Basic, ``Lean.Order.lfp =>
    return (``OmegaChecks.InitBoundaries.InternalOrder.UniqueChoice,
      ``OmegaChecks.InitBoundaries.InternalOrder.uniqueChoiceOfLfp)
  | `Init.Internal.Order.Basic, ``Lean.Order.lfp_monotone =>
    return (``OmegaChecks.InitBoundaries.InternalOrder.UniqueChoice,
      ``OmegaChecks.InitBoundaries.InternalOrder.uniqueChoiceOfMonotoneLfp)
  | `Init.Internal.Order.Basic, ``Lean.Order.fix =>
    return (``OmegaChecks.InitBoundaries.InternalOrder.UniqueChoice,
      ``OmegaChecks.InitBoundaries.InternalOrder.uniqueChoiceOfFix)
  | `Init.Internal.Order.Basic, ``Lean.Order.prod_sup =>
    return (``OmegaChecks.InitBoundaries.InternalOrder.UniqueChoice,
      ``OmegaChecks.InitBoundaries.InternalOrder.uniqueChoiceOfProdSup)
  | `Init.Internal.Order.Basic, ``Lean.Order.prod_csup =>
    return (``OmegaChecks.InitBoundaries.InternalOrder.UniqueChoice,
      ``OmegaChecks.InitBoundaries.InternalOrder.uniqueChoiceOfProdCSup)
  | `Init.Internal.Order.Basic, ``Lean.Order.fun_sup =>
    return (``OmegaChecks.InitBoundaries.InternalOrder.UniqueChoice,
      ``OmegaChecks.InitBoundaries.InternalOrder.uniqueChoiceOfFunSup)
  | `Init.Internal.Order.Basic, ``Lean.Order.EST.bot =>
    return (``OmegaChecks.InitBoundaries.InternalOrder.FamilyChoice,
      ``OmegaChecks.InitBoundaries.InternalOrder.familyChoiceOfStateBottom)
  | `Init.Internal.Order.Basic, ``Lean.Order.CompleteLattice.sup =>
    return (``OmegaChecks.InitBoundaries.InternalOrder.UniqueChoice,
      ``OmegaChecks.InitBoundaries.InternalOrder.uniqueChoiceOfSup)
  | `Init.Internal.Order.Basic, ``Lean.Order.CCPO.csup =>
    return (``OmegaChecks.InitBoundaries.InternalOrder.UniqueChoice,
      ``OmegaChecks.InitBoundaries.InternalOrder.uniqueChoiceOfChainSup)
  | `Init.Internal.Order.Basic, ``Lean.Order.bot =>
    return (``OmegaChecks.InitBoundaries.InternalOrder.UniqueChoice,
      ``OmegaChecks.InitBoundaries.InternalOrder.uniqueChoiceOfBot)
  | `Init.Control.Lawful.Basic, ``bind_congr =>
    return (``funext, ``OmegaChecks.InitBoundaries.dependentFunextFromBindCongr)
  | `Init.Control.Lawful.Basic, ``map_congr =>
    return (``funext, ``OmegaChecks.InitBoundaries.dependentFunextFromMapCongr)
  | `Init.Control.Basic, ``forIn'_eq_forIn => return (``funext, ``OmegaChecks.InitBoundaries.funextFromForInEq)
  | `Init.Control.Lawful.MonadAttach.Instances, ``instWeaklyLawfulMonadAttachReaderTOfLawfulMonad =>
    return (``funext, ``OmegaChecks.InitBoundaries.TransformerLaws.fromReaderTWeakAttach)
  | `Init.Control.Lawful.MonadAttach.Instances, ``instLawfulMonadAttachReaderTOfLawfulMonad =>
    return (``funext, ``OmegaChecks.InitBoundaries.TransformerLaws.fromReaderTAttach)
  | `Init.Control.Lawful.MonadAttach.Instances, ``instWeaklyLawfulMonadAttachStateTOfLawfulMonad =>
    return (``funext, ``OmegaChecks.InitBoundaries.TransformerLaws.fromStateTWeakAttach)
  | `Init.Control.Lawful.MonadAttach.Instances, ``instLawfulMonadAttachStateTOfLawfulMonad =>
    return (``funext, ``OmegaChecks.InitBoundaries.TransformerLaws.fromStateTAttach)
  | `Init.Control.Lawful.Basic, ``LawfulMonad.mk' =>
    return (``funext, ``OmegaChecks.InitBoundaries.TransformerLaws.fromMonadConstructor)
  | `Init.Control.Lawful.Instances, ``ReaderT.instLawfulFunctor =>
    return (``funext, ``OmegaChecks.InitBoundaries.TransformerLaws.fromReaderTFunctor)
  | `Init.Control.Lawful.Instances, ``ReaderT.instLawfulApplicative =>
    return (``funext, ``OmegaChecks.InitBoundaries.TransformerLaws.fromReaderTApplicative)
  | `Init.Control.Lawful.Instances, ``ReaderT.instLawfulMonad =>
    return (``funext, ``OmegaChecks.InitBoundaries.TransformerLaws.fromReaderTMonad)
  | `Init.Control.Lawful.Instances, ``StateT.instLawfulMonad =>
    return (``funext, ``OmegaChecks.InitBoundaries.TransformerLaws.fromStateTMonad)
  | `Init.Control.Lawful.Instances, ``ReaderT.ext => return (``funext, ``OmegaChecks.InitBoundaries.funextFromReaderExt)
  | `Init.Control.Lawful.Instances, ``ReaderT.ext_iff => return (``funext, ``OmegaChecks.InitBoundaries.funextFromReaderExtIff)
  | `Init.Control.Lawful.Instances, ``StateT.ext => return (``funext, ``OmegaChecks.InitBoundaries.funextFromStateExt)
  | `Init.Control.Lawful.Instances, ``StateT.ext_iff => return (``funext, ``OmegaChecks.InitBoundaries.funextFromStateExtIff)
  | `Init.Data.Function, ``Function.LeftInverse.id => return (``funext, ``OmegaChecks.InitBoundaries.funextFromLeftInverseId)
  | `Init.Data.Function, ``Function.RightInverse.id => return (``funext, ``OmegaChecks.InitBoundaries.funextFromRightInverseId)
  | `Init.Data.List.Monadic, ``List.foldlM_subtype =>
    return (``funext, ``OmegaChecks.InitBoundaries.MonadicTraversal.fromListFoldl)
  | `Init.Data.List.Monadic, ``List.foldrM_subtype =>
    return (``funext, ``OmegaChecks.InitBoundaries.MonadicTraversal.fromListFoldr)
  | `Init.Data.Iterators.Lemmas.Consumers.Monadic.Loop, ``Std.IterM.forIn_congr =>
    return (``funext, ``OmegaChecks.InitBoundaries.IteratorLoopCongruence.funextFromMonadicCongr)
  | `Init.Data.Iterators.Lemmas.Consumers.Monadic.Loop, ``Std.IterM.forIn'_congr =>
    return (``funext, ``OmegaChecks.InitBoundaries.IteratorLoopCongruence.funextFromMonadicCongr')
  | `Init.Data.Iterators.Lemmas.Consumers.Loop, ``Std.Iter.forIn_congr =>
    return (``funext, ``OmegaChecks.InitBoundaries.IteratorLoopCongruence.funextFromCongr)
  | `Init.Data.Iterators.Lemmas.Consumers.Loop, ``Std.Iter.forIn'_congr =>
    return (``funext, ``OmegaChecks.InitBoundaries.IteratorLoopCongruence.funextFromCongr')
  | `Init.Data.Range.Polymorphic.Map, ``Std.PRange.UpwardEnumerable.Map.succ?_toFun' =>
    return (``funext, ``OmegaChecks.InitBoundaries.RangeMap.funextFromSuccMap)
  | `Init.Core, ``Quotient.sound => return (``funext, ``OmegaChecks.InitBoundaries.funextFromQuotientSound)
  | `Init.Core, ``Pi.instSubsingleton => return (``funext, ``OmegaChecks.InitBoundaries.funextFromPiSubsingleton)
  | `Init.Core, ``instSubsingletonSquash => return (``funext, ``OmegaChecks.InitBoundaries.funextFromSquashSubsingleton)
  | `Init.PropLemmas, ``proof_irrel_heq =>
    return (``OmegaChecks.InitBoundaries.InhabitedPropExt, ``OmegaChecks.InitBoundaries.inhabitedPropExtOfProofHEq)
  | `Init.PropLemmas, ``eq_true_eq_id =>
    return (``OmegaChecks.InitBoundaries.InhabitedPropExt, ``OmegaChecks.InitBoundaries.inhabitedPropExtOfEqTrue)
  | `Init.Grind.Lemmas, ``Lean.Grind.of_decide_eq_true | `Init.SimpLemmas, ``eq_true_of_decide =>
    return (``OmegaChecks.InitBoundaries.InhabitedPropExt, ``OmegaChecks.InitBoundaries.inhabitedPropExtOfDecision)
  | `Init.Grind.Lemmas, ``Lean.Grind.of_decide_eq_false | `Init.SimpLemmas, ``eq_false_of_decide =>
    return (``OmegaChecks.InitBoundaries.RefutedPropExt, ``OmegaChecks.InitBoundaries.refutedPropExtOfDecision)
  | `Init.SimpLemmas, ``eq_true =>
    return (``OmegaChecks.InitBoundaries.InhabitedPropExt, ``OmegaChecks.InitBoundaries.inhabitedPropExtOfEqTrueRule)
  | `Init.SimpLemmas, ``eq_false | `Init.SimpLemmas, ``eq_false' =>
    return (``OmegaChecks.InitBoundaries.RefutedPropExt, ``OmegaChecks.InitBoundaries.refutedPropExtOfEqFalseRule)
  | `Init.Grind.Norm, ``Lean.Grind.ite_true_false =>
    return (``OmegaChecks.InitBoundaries.OptionalIndex.DecidablePropExt, ``OmegaChecks.InitBoundaries.OptionalIndex.decidablePropExtOfIte)
  | `Init.Data.Nat.Internal.Linear, ``Nat.Internal.Linear.Expr.of_cancel_eq =>
    return (``Nat.succ.injEq, ``OmegaChecks.InitBoundaries.NaturalCancellation.exprEq)
  | `Init.Data.Nat.Internal.Linear, ``Nat.Internal.Linear.Expr.of_cancel_le =>
    return (``OmegaChecks.InitBoundaries.NaturalCancellation.SuccLeEq, ``OmegaChecks.InitBoundaries.NaturalCancellation.exprLe)
  | `Init.Data.Nat.Internal.Linear, ``Nat.Internal.Linear.Expr.of_cancel_lt =>
    return (``OmegaChecks.InitBoundaries.NaturalCancellation.SuccLtEq, ``OmegaChecks.InitBoundaries.NaturalCancellation.exprLt)
  | `Init.Data.Nat.Internal.Linear, ``Nat.Internal.Linear.ExprCnstr.eq_of_toNormPoly_eq =>
    return (``Nat.succ.injEq, ``OmegaChecks.InitBoundaries.NaturalCancellation.exprNormEq)
  | `Init.Data.Nat.Internal.Linear, ``Nat.Internal.Linear.ExprCnstr.denote_toNormPoly =>
    return (``Nat.succ.injEq, ``OmegaChecks.InitBoundaries.NaturalCancellation.exprNorm)
  | `Init.Data.Nat.Internal.Linear, ``Nat.Internal.Linear.Poly.denote_eq_cancel_eq =>
    return (``Nat.succ.injEq, ``OmegaChecks.InitBoundaries.NaturalCancellation.polyEq)
  | `Init.Data.Nat.Internal.Linear, ``Nat.Internal.Linear.Poly.denote_le_cancel_eq =>
    return (``OmegaChecks.InitBoundaries.NaturalCancellation.SuccLeEq, ``OmegaChecks.InitBoundaries.NaturalCancellation.polyLe)
  | `Init.Data.Int.Linear, ``Int.Internal.Linear.norm_eq_var =>
    return (``OmegaChecks.InitBoundaries.IntegerCancellation.AddOneEq, ``OmegaChecks.InitBoundaries.IntegerCancellation.eqVar)
  | `Init.Data.Int.Linear, ``Int.Internal.Linear.norm_eq =>
    return (``OmegaChecks.InitBoundaries.IntegerCancellation.AddOneEq, ``OmegaChecks.InitBoundaries.IntegerCancellation.eqNorm)
  | `Init.Data.Int.Linear, ``Int.Internal.Linear.norm_le =>
    return (``OmegaChecks.InitBoundaries.IntegerCancellation.AddOneLE, ``OmegaChecks.InitBoundaries.IntegerCancellation.leNorm)
  | `Init.Data.Int.Linear, ``Int.Internal.Linear.norm_eq_coeff =>
    return (``OmegaChecks.InitBoundaries.IntegerCancellation.AddOneEq, ``OmegaChecks.InitBoundaries.IntegerCancellation.eqCoeff)
  | `Init.Data.Int.Linear, ``Int.Internal.Linear.norm_le_coeff =>
    return (``OmegaChecks.InitBoundaries.IntegerCancellation.AddOneLE, ``OmegaChecks.InitBoundaries.IntegerCancellation.leCoeff)
  | `Init.GetElem, ``isSome_getElem? =>
    return (``OmegaChecks.InitBoundaries.OptionalIndex.DecidablePropExt, ``OmegaChecks.InitBoundaries.OptionalIndex.decidablePropExtOfIsSome)
  | `Init.Data.Order.Lemmas, ``Std.Asymm.total_not =>
    return (`OmegaChecks.InitInventory.StringPatterns.WeakExcludedMiddle, ``OmegaChecks.InitBoundaries.AbstractOrder.weakMiddleOfTotalNot)
  | `Init.Data.Order.Factories, ``Std.IsLinearPreorder.of_lt =>
    return (`OmegaChecks.InitInventory.StringPatterns.WeakExcludedMiddle, ``OmegaChecks.InitBoundaries.AbstractOrder.weakMiddleOfLinearPreorder)
  | `Init.Data.Order.Factories, ``Std.IsLinearOrder.of_lt =>
    return (`OmegaChecks.InitInventory.StringPatterns.WeakExcludedMiddle, ``OmegaChecks.InitBoundaries.AbstractOrder.weakMiddleOfLinearOrder)
  | `Init.Data.String.Lemmas.Pattern.Basic, ``String.Slice.Pattern.Model.matchAt?_eq_none_iff =>
    return (`OmegaChecks.InitInventory.StringPatterns.WeakExcludedMiddle,
      `OmegaChecks.InitInventory.StringPatterns.weakExcludedMiddleOfMatchAtNone)
  | `Init.Data.String.Lemmas.Pattern.Basic, ``String.Slice.Pattern.Model.revMatchAt?_eq_none_iff =>
    return (`OmegaChecks.InitInventory.StringPatterns.WeakExcludedMiddle,
      `OmegaChecks.InitInventory.StringPatterns.weakExcludedMiddleOfRevMatchAtNone)
  | _, _ => pure ()
  let witness ← match owner, name with
    | `Init.Data.List.Lex, ``List.not_le | `Init.Data.List.Lex, `List.not_le_iff_gt =>
      some ``OmegaChecks.InitBoundaries.LexicographicOrder.ofListNotLE
    | `Init.Data.Array.Lex.Lemmas, ``Array.not_le | `Init.Data.Array.Lex.Lemmas, `Array.not_le_iff_gt =>
      some ``OmegaChecks.InitBoundaries.LexicographicOrder.ofArrayNotLE
    | `Init.Data.Vector.Lex, ``Vector.not_le | `Init.Data.Vector.Lex, `Vector.not_le_iff_gt =>
      some ``OmegaChecks.InitBoundaries.LexicographicOrder.ofVectorNotLE
    | `Init.Data.Vector.Lemmas, ``Vector.instDecidableExistsVectorSucc => some ``OmegaChecks.InitBoundaries.VectorExistence.emOfVectorSucc
    | `Init.Grind.Order, ``Lean.Grind.Order.le_of_not_lt => some ``OmegaChecks.InitBoundaries.GrindOrder.excludedMiddleFromComparison
    | `Init.Grind.Norm, ``Lean.Grind.imp_eq => some ``OmegaChecks.InitBoundaries.GrindOrder.excludedMiddleFromImplication
    | `Init.Grind.Norm, ``Lean.Grind.not_not => some ``OmegaChecks.InitBoundaries.GrindOrder.excludedMiddleFromNotNot
    | `Init.Grind.Lemmas, ``Lean.Grind.of_lookahead => some ``OmegaChecks.InitBoundaries.GrindOrder.excludedMiddleFromLookahead
    | `Init.Data.Order.Lemmas, ``Std.Trichotomous.rel_or_eq_or_rel_swap =>
      some ``OmegaChecks.InitBoundaries.AbstractOrder.excludedMiddleOfTrichotomy
    | `Init.Data.Order.Lemmas, ``Std.lt_trichotomy => some ``OmegaChecks.InitBoundaries.AbstractOrder.excludedMiddleOfLTTrichotomy
    | `Init.Data.Order.Lemmas, ``Std.total_of_refl_of_trichotomous =>
      some ``OmegaChecks.InitBoundaries.AbstractOrder.excludedMiddleOfTrichotomousTotal
    | `Init.Data.Order.Lemmas, ``Std.total_of_not_rel_swap_imp_rel =>
      some ``OmegaChecks.InitBoundaries.AbstractOrder.excludedMiddleOfNegationTotal
    | `Init.Data.Order.Factories, ``Std.LawfulOrderLT.of_lt => some ``OmegaChecks.InitBoundaries.AbstractOrder.excludedMiddleOfLawfulLT
    | `Init.Data.Order.Lemmas, ``Std.not_lt => some ``OmegaChecks.InitBoundaries.excludedMiddleOfNotLT
    | `Init.Data.Order.Lemmas, ``Std.not_lt_iff_not_le_or_ge =>
      some ``OmegaChecks.InitBoundaries.excludedMiddleOfNotLTIff
    | `Init.Data.String.Lemmas.Pattern.Basic, ``String.Slice.Pattern.Model.IsMatch.exists_isLongestMatch =>
      some `OmegaChecks.InitInventory.StringPatterns.excludedMiddleOfLongest
    | `Init.Data.String.Lemmas.Pattern.Basic, ``String.Slice.Pattern.Model.IsRevMatch.exists_isLongestRevMatch =>
      some `OmegaChecks.InitInventory.StringPatterns.excludedMiddleOfRevLongest
    | `Init.Data.String.Lemmas.Pattern.Basic, ``String.Slice.Pattern.Model.matchesAt_iff_exists_isMatch =>
      some `OmegaChecks.InitInventory.StringPatterns.excludedMiddleOfMatchesAt
    | `Init.Data.String.Lemmas.Pattern.Basic, ``String.Slice.Pattern.Model.revMatchesAt_iff_exists_isRevMatch =>
      some `OmegaChecks.InitInventory.StringPatterns.excludedMiddleOfRevMatchesAt
    | `Init.Data.String.Lemmas.Pattern.Basic, ``String.Slice.Pattern.Model.matchAt?_eq_some_iff =>
      some `OmegaChecks.InitInventory.StringPatterns.excludedMiddleOfMatchAtSome
    | `Init.Data.String.Lemmas.Pattern.Basic, ``String.Slice.Pattern.Model.revMatchAt?_eq_some_iff =>
      some `OmegaChecks.InitInventory.StringPatterns.excludedMiddleOfRevMatchAtSome
    | _, _ => none
  return (``Classical.em, witness)

/-- The conclusion uses the indicated semantic agreement in addition to the public type. -/
private def conditionalConsequence? (owner name : Name) : Option (String × Name × String) := do
  if owner == `Init.Data.Option.Lemmas && name == ``Option.choice then
    return ((``Classical.choice).toString, ``OmegaChecks.InitBoundaries.choiceFromOptionPresence,
      "For every nonempty type, the selector returns some, as specified by Option.isSome_choice")
  if owner == `Init.Internal.Order.Basic then
    if name == ``Lean.Order.Example.find then
      return ("∀ f : Nat → Bool, Decidable (∃ n, f n = true)",
        ``OmegaChecks.InitBoundaries.InternalOrder.limitedOmniscienceOfSearch,
        "The search follows find_eq and every returned index satisfies the predicate as in find_spec")
    if name == ``Lean.Order.instCompleteLatticePi then
      return ((``funext).toString, ``OmegaChecks.InitBoundaries.InternalOrder.funextOfCompletePointwiseOrder,
        "Pointwise comparison of functions implies comparison in the proposed complete lattice")
    if name == ``Lean.Order.instCCPOPi then
      return ((``funext).toString, ``OmegaChecks.InitBoundaries.InternalOrder.funextOfChainCompletePointwiseOrder,
        "Pointwise comparison of functions implies comparison in the proposed chain-complete order")
    if name == ``Lean.Order.instOrderPi then
      return ((``funext).toString, ``OmegaChecks.InitBoundaries.InternalOrder.funextOfPointwiseOrder,
        "Pointwise comparison of functions implies comparison in the proposed order")
    if name == ``Lean.Order.ImplicationOrder.instOrder then
      return ((``propext).toString, ``OmegaChecks.InitBoundaries.InternalOrder.propextOfImplicationOrder,
        "An implication from p to q implies p is below q")
    if name == ``Lean.Order.ReverseImplicationOrder.instOrder then
      return ((``propext).toString, ``OmegaChecks.InitBoundaries.InternalOrder.propextOfReverseImplicationOrder,
        "An implication from q to p implies p is below q")
    if name == ``Lean.Order.instCCPOOption then
      return ((``Classical.em).toString, ``OmegaChecks.InitBoundaries.InternalOrder.excludedMiddleOfOptionCCPO,
        "The order underlying the proposed CCPO on options agrees with the official flat order")
    if name == ``Lean.Order.FlatOrder.instCCPO then
      return ((``Classical.em).toString, ``OmegaChecks.InitBoundaries.InternalOrder.excludedMiddleOfFlatCCPO,
        "At options with bottom none the order underlying the proposed CCPO agrees with the flat order")
    if name == ``Lean.Order.flat_csup then
      return ((``Classical.em).toString, ``OmegaChecks.InitBoundaries.InternalOrder.excludedMiddleOfFlatCSup,
        "On chains of options with bottom none, the result satisfies flat_csup_is_sup")
  if owner == `Init.Data.String.Lemmas.Pattern.Basic then
    if name == ``String.Slice.Pattern.Model.matchAt? then
      return ((``Classical.em).toString, `OmegaChecks.InitInventory.StringPatterns.excludedMiddleOfForwardResult,
        "The matcher returns some b at a iff IsLongestMatchAt pat a b (matchAt?_eq_some_iff)")
    if name == ``String.Slice.Pattern.Model.revMatchAt? then
      return ((``Classical.em).toString, `OmegaChecks.InitInventory.StringPatterns.excludedMiddleOfBackwardResult,
        "The matcher returns some a at b iff IsLongestRevMatchAt pat a b (revMatchAt?_eq_some_iff)")
  if owner == `Init.Data.String.Lemmas.Pattern.Split.Basic && name == ``String.Slice.Pattern.Model.split then
    return ("OmegaChecks.InitInventory.StringPatterns.WeakExcludedMiddle",
      `OmegaChecks.InitInventory.StringPatterns.weakExcludedMiddleOfOfficialSplit,
      "Pointwise agreement with Model.split (split_endPos, split_eq_of_isLongestMatchAt, split_eq_of_not_matchesAt)")
  let (witness, behavior) ← match owner, name with
    | `Init.Data.Iterators.Consumers.Collect, ``Std.Iter.toList =>
      some (``OmegaChecks.InitBoundaries.Collector.limitedOmniscienceFromCollector,
        "the official result of the ordinary list collector")
    | `Init.Data.Iterators.Consumers.Collect, ``Std.Iter.toArray =>
      some (``OmegaChecks.InitBoundaries.Collector.limitedOmniscienceFromArray,
        "the official result of the ordinary array collector")
    | `Init.Data.Iterators.Consumers.Collect, ``Std.Iter.toListRev =>
      some (``OmegaChecks.InitBoundaries.Collector.limitedOmniscienceFromReverse,
        "the official result of the reverse list collector")
    | `Init.Data.Iterators.Consumers.Monadic.Collect, ``Std.IterM.toList =>
      some (``OmegaChecks.InitBoundaries.Collector.limitedOmniscienceFromMonadicCollector,
        "the official result of the identity-monad list collector")
    | `Init.Data.Iterators.Consumers.Monadic.Collect, ``Std.IterM.toArray =>
      some (``OmegaChecks.InitBoundaries.Collector.limitedOmniscienceFromMonadicArray,
        "the official result of the identity-monad array collector")
    | `Init.Data.Iterators.Consumers.Monadic.Collect, ``Std.IterM.toListRev =>
      some (``OmegaChecks.InitBoundaries.Collector.limitedOmniscienceFromMonadicReverse,
        "the official result of the identity-monad reverse collector")
    | `Init.Data.Slice.Operations, ``Std.Slice.toList =>
      some (``OmegaChecks.InitBoundaries.Collector.limitedOmniscienceFromSlice,
        "the official result of the list of each slice whose underlying iterator is finite")
    | `Init.Data.Iterators.Consumers.Access, ``Std.Iter.atIdxSlow? =>
      some (``OmegaChecks.InitBoundaries.Collector.limitedOmniscienceFromLookup,
        "the official result of the optional lookup at each natural index")
    | `Init.Data.Iterators.Consumers.Monadic.Loop, ``Std.IteratorLoop.defaultImplementation =>
      some (``OmegaChecks.InitBoundaries.Collector.limitedOmniscienceFromDefaultLoop,
        "the official result of the default identity-monad loop")
    | `Init.Data.Iterators.Combinators.Monadic.FilterMap, ``Std.Iterators.Types.Map.instIteratorLoop =>
      some (``OmegaChecks.InitBoundaries.Collector.limitedOmniscienceFromMapLoop,
        "the official result of the identity-monad loop for mapping the identity")
    | `Init.Data.Iterators.Combinators.Monadic.FilterMap, ``Std.Iterators.Types.FilterMap.instIteratorLoop =>
      some (``OmegaChecks.InitBoundaries.Collector.limitedOmniscienceFromFilterMapLoop,
        "the official result of the identity-monad loop for filtering with some")
    | `Init.Data.Iterators.Combinators.Monadic.Attach, ``Std.Iterators.Types.Attach.instIteratorLoop =>
      some (``OmegaChecks.InitBoundaries.Collector.limitedOmniscienceFromAttachLoop,
        "the official result of the identity-monad loop attaching the true predicate")
    | `Init.Data.Iterators.Combinators.Monadic.ULift, ``Std.Iterators.Types.ULiftIterator.instIteratorLoop =>
      some (``OmegaChecks.InitBoundaries.Collector.limitedOmniscienceFromULiftLoop,
        "the official result of the same-universe identity-monad lifting loop")
    | `Init.Data.Iterators.Combinators.Monadic.Append, ``Std.Iterators.Types.Append.instIteratorLoop =>
      some (``OmegaChecks.InitBoundaries.Collector.limitedOmniscienceFromAppendLoop,
        "the official result of the identity-monad append loop with a list iterator as the second input")
    | `Init.Data.Iterators.Combinators.Monadic.FlatMap, ``Std.Iterators.Types.Flatten.instIteratorLoop =>
      some (``OmegaChecks.InitBoundaries.Collector.limitedOmniscienceFromFlattenLoop,
        "the official result of the identity-monad flattening loop for finite outer and inner iterators")
    | `Init.Data.Iterators.Combinators.Monadic.Take, ``Std.Iterators.Types.Take.instIteratorLoop =>
      some (``OmegaChecks.InitBoundaries.Collector.limitedOmniscienceFromTakeLoop,
        "the official result of the identity-monad take loop")
    | `Init.Data.String.Iter.Basic, ``Std.Iter.toStringList =>
      some (``OmegaChecks.InitBoundaries.Collector.limitedOmniscienceFromStringList, "it.toStringList")
    | `Init.Data.String.Iter.Basic, ``Std.Iter.toStringArray =>
      some (``OmegaChecks.InitBoundaries.Collector.limitedOmniscienceFromStringArray, "it.toStringArray")
    | `Init.Data.String.Iter.Intercalate, ``Std.Iter.joinString =>
      some (``OmegaChecks.InitBoundaries.Collector.limitedOmniscienceFromStringJoin, "String.join (it.toList.map toString)")
    | `Init.Data.String.Iter.Intercalate, ``Std.Iter.intercalateString =>
      some (``OmegaChecks.InitBoundaries.Collector.limitedOmniscienceFromStringIntercalate,
        "s.copy.intercalate (it.toList.map toString) for every separator s")
    | _, _ => none
  return ("∀ f : Nat → Bool, Decidable (∃ n, f n = true)", witness,
    "On every finite iterator it the result equals " ++ behavior)

private def inventory (lib : System.FilePath) (visible strict full : Environment) (modules : Array Name)
    (gaps : Option IO.FS.Handle) : CoreM Json := do
  let official ← getEnv
  let reductions := reductionPaths visible strict full
  let boundaries : Std.HashMap (Name × Name) (Name × Name) := OmegaChecks.InitBoundaries.reductions.foldl
    (init := {}) fun acc (owner, name, target, witness) => acc.insert (owner, name) (target, witness)
  let mut names : NameSet := {}
  let mut duplicateNames : NameSet := {}
  let publicName := fun (n : Name) => !isPrivateName n && !n.isInternalOrNum && !n.hasMacroScopes
  for data in visible.header.moduleData do
    for n in data.constNames do
      if publicName n then
        if names.contains n then duplicateNames := duplicateNames.insert n
        names := names.insert n
  let mut certifiedSites := 0
  let mut matchedUnique : NameSet := {}
  let mut axiomUnique : NameSet := {}
  let mut withAxiomsUnique : NameSet := {}
  let mut rows := #[]
  let mut matchingNames := 0
  let mut directAxioms := 0
  let mut withAxioms := 0
  if let some file := gaps then
    file.putStrLn "module\tdeclaration\tkind\tunsafe\tpartial\tupstreamAxioms\timpliesAxiom\treductionWitness\tlogicalConsequence\tlogicalConsequenceWitness\trequiredBehavior"
  for owner in modules do
    let some idx := visible.getModuleIdx? owner | throwError "missing official module {owner}"
    let publicNames := visible.header.moduleData[idx]!.constNames.filter publicName
    let some privateIdx := official.getModuleIdx? owner | throwError "missing private module {owner}"
    let infos ← if publicNames.any duplicateNames.contains then do
      -- Load this defining file directly. The combined environment may select a different
      -- module's declaration with the same name.
      let path := modToFilePath lib owner "olean"
      let parts ← readModuleDataParts #[path, path.addExtension "server", path.addExtension "private"]
      pure (parts.map (·.1))[2]!.constants
    else pure official.header.moduleData[privateIdx]!.constants
    let localDecls : NameMap ConstantInfo := infos.foldl (fun m c => m.insert c.name c) {}
    let localAxioms := exportedAxiomsExt.getModuleEntries official privateIdx
    let expected := owner.replacePrefix `Init `OmegaInit
    let strictNames := (strict.getModuleIdx? expected).map fun i =>
      NameSet.ofList strict.header.moduleData[i]!.constNames.toList
    for name in publicNames.qsort Name.lt do
      let some info := localDecls.find? name | throwError "missing declaration {owner}/{name}"
      let some (_, axioms) := localAxioms.binSearch (name, #[]) (fun a b => Name.quickLt a.1 b.1)
        | throwError "missing official axiom closure for {owner}/{name}"
      let conditional := conditionalConsequence? owner name
      let consequence := (logicalConsequence? owner name).map (fun (target, witness) => (target.toString, witness))
        <|> conditional.map (fun (target, witness, _) => (target, witness))
      let behavior := conditional.map (fun (_, _, premise) => premise)
      let boundary := boundaries[(owner, name)]?
      if boundary.isSome then certifiedSites := certifiedSites + 1
      let strictName := `Omega ++ name
      let matched := strictNames.any (·.contains strictName)
      let strictOwner := if matched then some expected else none
      if matched then
        matchingNames := matchingNames + 1
        matchedUnique := matchedUnique.insert name
      if !matched && !info.isAxiom then
        if let some file := gaps then
          file.putStrLn <| String.intercalate "\t" [owner.toString, name.toString,
            declarationKind info, toString info.isUnsafe, toString info.isPartial,
            String.intercalate "," (axioms.toList.map Name.toString),
            (boundary.map (·.1.toString)).getD "", (boundary.map (·.2.toString)).getD "",
            (consequence.map Prod.fst).getD "", (consequence.map (·.2.toString)).getD "", behavior.getD ""]
      if info.isAxiom then
        directAxioms := directAxioms + 1
        axiomUnique := axiomUnique.insert name
      if !axioms.isEmpty then
        withAxioms := withAxioms + 1
        withAxiomsUnique := withAxiomsUnique.insert name
      let reduction := if matched then reductions.get? strictName else none
      let row := Json.mkObj [
        ("name", toJson name.toString), ("module", toJson owner.toString),
        ("kind", toJson (declarationKind info)), ("unsafe", toJson info.isUnsafe), ("partial", toJson info.isPartial),
        ("matchingNameAndModule", toJson matched),
        ("publicReductionBoundary", toJson ((reduction.map Prod.fst).getD []).toArray),
        ("officialReductionMechanism", toJson (reduction.map Prod.snd)),
        ("axioms", toJson (axioms.map Name.toString)),
        ("impliesAxiom", toJson (boundary.map (·.1.toString))),
        ("reductionWitness", toJson (boundary.map (·.2.toString))),
        ("strictModule", toJson (strictOwner.map Name.toString))]
      rows := rows.push <| match consequence with
        | some (target, witness) => row.mergeObj <| Json.mkObj [
            ("logicalConsequence", toJson target), ("logicalConsequenceWitness", toJson witness.toString),
            ("requiredBehavior", toJson behavior)]
        | none => row
  unless certifiedSites == boundaries.size do throwError "missing registered public definition site"
  let summary := Json.mkObj [("declarations", toJson rows.size), ("directAxioms", toJson directAxioms),
    ("withAxioms", toJson withAxioms), ("matchingNameAndModule", toJson matchingNames)]
  let unique := Json.mkObj [("declarations",toJson names.size), ("directAxioms",toJson axiomUnique.size),
    ("withAxioms",toJson withAxiomsUnique.size), ("matchingNameAndModule",toJson matchedUnique.size)]
  return Json.mkObj [("schemaVersion", toJson 3), ("uniqueNames", unique), ("leanVersion", toJson Lean.versionString), ("leanCommit", toJson Lean.githash),
    ("modules", toJson (modules.map Name.toString)), ("summary", summary), ("declarations", .arr rows)]

def main (args : List String) : IO Unit := do
  let strictDir :: outputPath :: rest := args | throw <| IO.userError "expected strict olean directory and output file"
  let gaps ← match rest with
    | [] => pure none
    | [path] =>
      if path == outputPath then throw <| IO.userError "inventory and gaps require distinct files"
      pure (some (← IO.FS.Handle.mk path .write))
    | _ => throw <| IO.userError "expected at most one gaps TSV file"
  let sysroot ← findSysroot
  let lib ← getLibDir sysroot
  searchPathRef.set [lib]
  let modules ← installedModules lib `Init
  let imports := modules.map fun mod => {module := mod : Import}
  let visible ← importModules imports {} (level := .exported)
  -- The public environment can replace a hidden body with an axiom-shaped entry.
  -- Use the private artifact for the original declaration kind and axiom dependencies.
  -- Load Lean's exported-axiom extension from the pinned toolchain so every query
  -- can use the dependency closure recorded by Lean when the module was compiled.
  unsafe enableInitializersExecution
  let official ← importModules imports {} (loadExts := true)
  searchPathRef.set [strictDir]
  let basis ← installedModules strictDir `OmegaInit
  let strictImports := basis.map fun mod => {module := mod : Import}
  let strict ← importModules strictImports {} (level := .exported)
  let full ← importModules strictImports {} (level := .private)
  for owner in strict.allImportedModuleNames do
    unless owner.getRoot == `OmegaInit do
      throw <| IO.userError s!"expected a strict OmegaInit build, found import {owner}"
  let result ← (inventory lib visible strict full modules gaps).toIO' {fileName := "<Init inventory>", fileMap := default} {env := official}
  IO.FS.writeFile outputPath (result.compress ++ "\n")
  IO.println (← IO.ofExcept (result.getObjVal? "summary")).compress
