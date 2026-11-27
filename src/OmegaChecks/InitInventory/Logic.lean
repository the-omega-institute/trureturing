module
public import Lean
import Lean.Replay
import all Lean.Util.CollectAxioms

public section

open Lean
namespace OmegaChecks.InitBoundaries
universe u v w z

/-- The official option selector returns a value on every inhabited input.
Lifting a sort into a type also covers propositional inputs to choice. -/
def choiceFromOptionPresence (select : type_of% (@Option.choice.{u}))
    (present : ∀ (α : Type u), Nonempty α → (select α).isSome) :
    type_of% (@Classical.choice.{u}) := by
  intro α h
  have nonempty : Nonempty (PLift α) := h.elim fun a => ⟨⟨a⟩⟩
  exact ((select (PLift α)).get (present _ nonempty)).down

namespace OptionSelector

def fromSome (select : type_of% (@Option.choice.{u}))
    (law : ∀ {α : Type u} [Nonempty α], (select α).isSome) :
    type_of% (@Classical.choice.{u}) := choiceFromOptionPresence select fun α h => @law α h

def fromSomeIff (select : type_of% (@Option.choice.{u}))
    (law : ∀ {α : Type u}, (select α).isSome ↔ Nonempty α) :
    type_of% (@Classical.choice.{u}) := choiceFromOptionPresence select fun _ => law.mpr

def fromNoneEq (select : type_of% (@Option.choice.{u}))
    (law : ∀ {α : Type u}, select α = none ↔ ¬Nonempty α) :
    type_of% (@Classical.choice.{u}) := choiceFromOptionPresence select fun α h => by
  cases e : select α with
  | none => exact False.elim (law.mp e h)
  | some a => rfl

def fromNoneIff (select : type_of% (@Option.choice.{u}))
    (law : ∀ {α : Type u}, (select α).isNone ↔ ¬Nonempty α) :
    type_of% (@Classical.choice.{u}) := choiceFromOptionPresence select fun α h => by
  cases e : select α with
  | none => exact False.elim (law.mp (e ▸ rfl) h)
  | some a => rfl

def fromNoneFalse (select : type_of% (@Option.choice.{u}))
    (law : ∀ {α : Type u} [Nonempty α], (select α).isNone = false) :
    type_of% (@Classical.choice.{u}) := choiceFromOptionPresence select fun α h => by
  have eq := @law α h
  cases e : select α with
  | none => rw [e] at eq; contradiction
  | some a => rfl

def fromListLength (select : type_of% (@Option.choice.{u}))
    (law : ∀ {α : Type u} [Nonempty α], (select α).toList.length = 1) :
    type_of% (@Classical.choice.{u}) := choiceFromOptionPresence select fun α h => by
  have eq := @law α h
  cases e : select α with
  | none => rw [e] at eq; contradiction
  | some a => rfl

def fromArraySize (select : type_of% (@Option.choice.{u}))
    (law : ∀ {α : Type u} [Nonempty α], (select α).toArray.size = 1) :
    type_of% (@Classical.choice.{u}) := choiceFromOptionPresence select fun α h => by
  have eq := @law α h
  cases e : select α with
  | none => rw [e] at eq; contradiction
  | some a => rfl
/-- An arbitrary well-typed witness for the dependent projection suffices.
Eliminating the inhabited input into the tag proposition is constructive. -/
def fromGetD (select : type_of% @Option.choice.{u})
    (law : ∀ {α : Type u} {a : α}, ∃ h : (select α).isSome, (select α).getD a = (select α).get h) :
    type_of% @Classical.choice.{u} :=
  choiceFromOptionPresence select fun α ne => ne.elim fun a => (@law α a).elim fun h _ => h

def fromGetBang (select : type_of% @Option.choice.{u})
    (law : ∀ {α : Type u} [Inhabited α], ∃ h : (select α).isSome, (select α).get! = (select α).get h) :
    type_of% @Classical.choice.{u} :=
  choiceFromOptionPresence select fun α ne => ne.elim fun a => (@law α ⟨a⟩).elim fun h _ => h

/-- For each law, every selector satisfying its exact public statement yields unrestricted choice. -/
def laws : List (Name × Name × Name) := [
  (`Init.Data.Option.Lemmas, ``Option.getD_choice, ``fromGetD),
  (`Init.Data.Option.Lemmas, ``Option.get!_choice, ``fromGetBang),
  (`Init.Data.Option.Lemmas, ``Option.isSome_choice, ``fromSome),
  (`Init.Data.Option.Lemmas, ``Option.isSome_choice_iff_nonempty, ``fromSomeIff),
  (`Init.Data.Option.Lemmas, ``Option.choice_eq_none_iff_not_nonempty, ``fromNoneEq),
  (`Init.Data.Option.Lemmas, ``Option.isNone_choice_iff_not_nonempty, ``fromNoneIff),
  (`Init.Data.Option.Lemmas, ``Option.isNone_choice_eq_false, ``fromNoneFalse),
  (`Init.Data.Option.List, ``Option.length_toList_choice_eq_one, ``fromListLength),
  (`Init.Data.Option.Array, ``Option.size_toArray_choice_eq_one, ``fromArraySize)]

def usesSelector (owner name : Name) : Bool :=
  laws.any fun (m, n, _) => m == owner && n == name

end OptionSelector

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

private theorem neNegationOfIff {p q : Prop} (equiv : p ↔ q) : p ≠ ¬q := by
  intro eq
  have np : ¬p := fun hp => (eq.mp hp) (equiv.mp hp)
  exact np (eq.mpr (fun hq => np (equiv.mpr hq)))

/-- Taking the second proposition to be the negation of the first gives
double-negation elimination. Apply it to equality of equivalent propositions. -/
theorem propextFromNotEqProp (norm : type_of% @Lean.Grind.not_eq_prop) : type_of% @propext := by
  have dne (p : Prop) : ¬¬p → p :=
    ((norm p (¬p)).mp (neNegationOfIff (Iff.rfl (a := p)))).mpr
  intro p q equiv
  exact dne _ fun ne => neNegationOfIff equiv ((norm p q).mp ne)


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

/-- Equality of vector values ignores their length proof. These kernels build the same
array data with length proofs that replay without axioms. -/
theorem sizeAfterPush {α : Type u} (xs : Array α) (v : α) :
    (xs.push v).size = xs.size + 1 := by
  cases xs with
  | mk xs =>
    change (xs.concat v).length = xs.length + 1
    induction xs with
    | nil => rfl
    | cons x xs ih => exact congrArg Nat.succ ih

@[expose] def pushed {α : Type u} {n} (xs : Vector α n) (v : α) : Vector α (n+1) :=
  ⟨xs.toArray.push v, (sizeAfterPush xs.toArray v).trans (congrArg Nat.succ xs.size_toArray)⟩

theorem ofVectorMember (branch : ∀ {α : Type u} {n} {a b : α} {xs : Vector α n},
    a ∈ pushed xs b → a = b ∨ (a ≠ b ∧ a ∈ xs)) :
    EqualityCases.{u} := by
  intro α a b
  have h : a ∈ pushed #[a].toVector b := ⟨⟨.head _⟩⟩
  exact (branch h).imp_right And.left

example (branch : type_of% (@Vector.eq_or_ne_mem_of_mem.{u})) : EqualityCases.{u} :=
  ofVectorMember (@branch)

theorem sizeAfterAppend {α : Type u} (xs ys : Array α) : (xs ++ ys).size = xs.size + ys.size := by
  have loop (fuel i : Nat) (st : Array α) (eqn : i + fuel = ys.size) :
      (Array.foldlM.loop (m := Id) (fun as x => pure (as.push x)) ys ys.size (Nat.le_refl _)
        fuel i st).run.size = st.size + fuel := by
    induction fuel generalizing i st with
    | zero =>
      have n : ¬ i < ys.size := (eqn ▸ Nat.lt_irrefl i)
      unfold Array.foldlM.loop
      rw [dite_eq_right n]
      rfl
    | succ fuel ih =>
      have hi : i < ys.size := eqn ▸ (Nat.lt_of_lt_of_le (Nat.lt_succ_self i) (Nat.succ_le_succ (Nat.le_add_right i fuel)))
      unfold Array.foldlM.loop
      rw [dite_eq_left hi]
      exact (ih (i+1) (st.push ys[i]) ((Nat.succ_add i fuel).trans eqn)).trans
        ((congrArg (· + fuel) (sizeAfterPush st ys[i])).trans (Nat.succ_add st.size fuel))
  change (Array.foldl (fun st x => st.push x) xs ys).size = _
  unfold Array.foldl Array.foldlM
  rw [dite_eq_left (Nat.le_refl _)]
  exact loop ys.size 0 xs (Nat.zero_add _)

@[expose] def appended {α : Type u} {n m} (xs : Vector α n) (ys : Vector α m) : Vector α (n+m) :=
  ⟨xs.toArray ++ ys.toArray, (sizeAfterAppend ..).trans ((congrArg (· + ys.toArray.size) xs.size_toArray).trans (congrArg (n + ·) ys.size_toArray))⟩

@[expose] def casted {α : Type u} {n m} (h : n = m) (xs : Vector α n) : Vector α m :=
  ⟨xs.toArray, xs.size_toArray.trans h⟩

theorem ofFirstVectorMember (split : ∀ {α : Type u} {n} {xs : Vector α n} {x : α} (_ : x ∈ xs),
      ∃ (i j : Nat) (pre : Vector α i) (post : Vector α j) (h : i + 1 + j = n),
        xs = casted h (appended (pushed pre x) post) ∧ x ∉ pre) :
    EqualityCases.{u} := by
  apply ofFirstArrayMember
  intro α xs x mem
  obtain ⟨_, _, pre, post, h, shape, absent⟩ := split (xs := xs.toVector) ⟨mem⟩
  exact ⟨pre.toArray, post.toArray, congrArg Vector.toArray shape, fun h => absent ⟨h⟩⟩

example (split : type_of% (@Vector.eq_push_append_of_mem.{u})) : EqualityCases.{u} :=
  ofFirstVectorMember (@split)

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

namespace PropositionalChoice

/-- Existence of one selector for all nonempty sorts at this universe. -/
abbrev Selection := Nonempty (type_of% (@Classical.choice.{u}))

private def unliftChoice (select : (t : NonemptyType.{u}) → t.type) : type_of% (@Classical.choice.{u}) :=
  fun {α} h => (select ⟨PLift α, h.elim fun a => ⟨⟨a⟩⟩⟩).down

theorem ofProducts (product : type_of% (@Pi.instNonempty.{u+2,u+1})) : Selection.{u} := by
  have inhabited (t : NonemptyType.{u}) : Nonempty t.type := t.property
  exact (@product NonemptyType (fun t => t.type) inhabited).elim fun select => ⟨unliftChoice select⟩

theorem ofChoice (choose : type_of% (@Classical.axiomOfChoice.{u+2,u+1})) : Selection.{u} := by
  have entries (t : NonemptyType.{u}) : ∃ _ : t.type, True :=
    t.property.elim fun x => ⟨x, trivial⟩
  obtain ⟨select, _⟩ := choose entries
  exact ⟨unliftChoice select⟩

theorem ofSkolem (split : type_of% (@Classical.skolem.{u+2,u+1})) : Selection.{u} :=
  ofChoice (@split _ _ _ |>.mp)

end PropositionalChoice

namespace ClassicalConsequences

theorem ofByCases (cases : type_of% @Classical.byCases) : type_of% @Classical.em :=
  fun _ => cases Or.inl Or.inr

theorem ofContradiction (dne : type_of% @Classical.byContradiction) : type_of% @Classical.em :=
  excludedMiddleFromDNE fun _ => dne

theorem ofNotNot (law : type_of% @Classical.not_not) : type_of% @Classical.em :=
  excludedMiddleFromDNE fun _ => law.mp

private theorem ofDecision {p : Prop} : Decidable p → p ∨ ¬p
  | .isTrue yes => .inl yes
  | .isFalse no => .inr no

theorem ofPropDecidable (dec : type_of% @Classical.propDecidable) : type_of% @Classical.em :=
  fun p => ofDecision (dec p)

theorem ofInhabitedDecision (dec : type_of% @Classical.decidableInhabited) : type_of% @Classical.em :=
  fun p => ofDecision (dec p).default

theorem ofNonemptyDecision (dec : type_of% @Classical.instNonemptyDecidable) : type_of% @Classical.em :=
  fun p => (dec p).elim ofDecision

theorem ofDecidableNot (transfer : type_of% @Classical.decidable_of_decidable_not) : type_of% @Classical.em :=
  excludedMiddleFromDNE fun p nn => match @transfer p (.isFalse nn) with
    | .isTrue hp => hp
    | .isFalse np => (nn np).elim

theorem ofNotForall (law : type_of% @Classical.not_forall.{0}) : type_of% @Classical.em :=
  excludedMiddleFromDNE fun p nn => ((@law p (fun _ => False)).mp nn).elim fun hp _ => hp

theorem ofNotForallNot (law : type_of% @Classical.not_forall_not.{1}) : type_of% @Classical.em :=
  excludedMiddleFromDNE fun p nn =>
    ((@law Unit (fun _ => p)).mp (fun denied => nn (denied ()))).elim fun _ hp => hp

theorem ofNotExistsNot (law : type_of% @Classical.not_exists_not.{1}) : type_of% @Classical.em :=
  excludedMiddleFromDNE fun p nn =>
    (@law Unit (fun _ => p)).mp (fun ex => ex.elim fun _ np => nn np) ()

theorem ofForallOrExists (law : type_of% @Classical.forall_or_exists_not.{1}) : type_of% @Classical.em :=
  fun p => (@law Unit (fun _ => p)).elim (fun all => .inl (all ())) (fun ex => ex.elim fun _ np => .inr np)

theorem ofExistsOrForall (law : type_of% @Classical.exists_or_forall_not.{1}) : type_of% @Classical.em :=
  fun p => (@law Unit (fun _ => p)).elim (fun ex => ex.elim fun _ hp => .inl hp) (fun none => .inr (none ()))

theorem ofOrImpLeft (law : type_of% @Classical.or_iff_not_imp_left) : type_of% @Classical.em :=
  fun p => (@law p (¬p)).mpr id

theorem ofOrImpRight (law : type_of% @Classical.or_iff_not_imp_right) : type_of% @Classical.em :=
  fun p => ((@law (¬p) p).mpr id).elim Or.inr Or.inl

theorem ofNotImp (law : type_of% @Classical.not_imp) : type_of% @Classical.em :=
  excludedMiddleFromDNE fun p nn => ((@law p False).mp nn).1

theorem ofNotIff (law : type_of% @Classical.not_iff) : type_of% @Classical.em :=
  excludedMiddleFromDNE fun p nn =>
    ((@law False p).mp (fun equiv => nn equiv.mpr)).mp id

theorem ofImpLeft (law : type_of% @Classical.imp_iff_left_iff) : type_of% @Classical.em :=
  fun p => (@law (¬p) p).mp ⟨fun np _ => np, fun both hp => both hp hp⟩

theorem ofImpRight (law : type_of% @Classical.imp_iff_right_iff) : type_of% @Classical.em :=
  fun p => (@law p (¬p)).mp ⟨fun both hp => both hp hp, fun np _ => np⟩

theorem ofAndOrImp (law : type_of% @Classical.and_or_imp) : type_of% @Classical.em :=
  fun p => ((@law p True False).mpr (fun _ => .inl trivial)).elim (fun yes => .inl yes.1) Or.inr

theorem ofTwoImplications (law : type_of% @Classical.imp_and_neg_imp_iff) : type_of% @Classical.em :=
  fun p => (law p).mp ⟨Or.inl, Or.inr⟩

theorem ofExcludedMiddle (law : type_of% @Classical.em) : type_of% @Classical.em := law

/-- Names are paired with reductions so the gap report and the fresh replay use the same witnesses. -/
def witnesses : List (Name × Name) := [
  (``Classical.byCases, ``ofByCases), (``Classical.byContradiction, ``ofContradiction),
  (``Classical.not_not, ``ofNotNot), (``Classical.propDecidable, ``ofPropDecidable),
  (``Classical.decidableInhabited, ``ofInhabitedDecision), (``Classical.instNonemptyDecidable, ``ofNonemptyDecision),
  (``Classical.decidable_of_decidable_not, ``ofDecidableNot), (``Classical.not_forall, ``ofNotForall),
  (``Classical.not_forall_not, ``ofNotForallNot), (``Classical.not_exists_not, ``ofNotExistsNot),
  (``Classical.forall_or_exists_not, ``ofForallOrExists), (``Classical.exists_or_forall_not, ``ofExistsOrForall),
  (``Classical.or_iff_not_imp_left, ``ofOrImpLeft), (``Classical.or_iff_not_imp_right, ``ofOrImpRight),
  (``Classical.not_imp, ``ofNotImp), (``Classical.not_imp_iff_and_not, ``ofNotImp),
  (``Classical.not_iff, ``ofNotIff), (``Classical.imp_iff_left_iff, ``ofImpLeft),
  (``Classical.imp_iff_right_iff, ``ofImpRight), (``Classical.and_or_imp, ``ofAndOrImp),
  (``Classical.imp_and_neg_imp_iff, ``ofTwoImplications), (``Classical.em, ``ofExcludedMiddle)]

end ClassicalConsequences

namespace EmbeddingRange

/-- A retraction of the inclusion of {false} ∪ {true | p} must decide p at true. -/
theorem ofExists (split : type_of% @Function.Injective.exists_leftInverse.{1,1}) : type_of% @Classical.em := by
  intro p
  let T := {b : Bool // b = false ∨ p}
  letI : Nonempty T := ⟨⟨false, .inl rfl⟩⟩
  obtain ⟨back, retract⟩ := @split T Bool Subtype.val (fun _ _ => Subtype.ext) _
  cases h : (back true).val with
  | false =>
    right
    intro hp
    have atTrue := congrArg Subtype.val (retract (⟨true, .inr hp⟩ : T))
    exact Bool.noConfusion (h.symm.trans atTrue)
  | true =>
    exact (back true).property.elim (fun atFalse => Bool.noConfusion (h.symm.trans atFalse)) Or.inl

set_option linter.deprecated false in
theorem ofLeftInverse (split : type_of% @Function.Injective.leftInverse.{1,1}) : type_of% @Classical.em :=
  ofExists fun {α β f} hf hα => @split α β f hf hα

end EmbeddingRange

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

namespace BooleanReflection

/-- The truth of a successful Boolean test, expressed as equality of propositions. -/
def TrueBit := (true = true) = True

/-- The falsity of an unsuccessful Boolean test, expressed as equality of propositions. -/
def FalseBit := (false = true) = False

/-- Simultaneously negating both sides preserves Boolean identity propositions. -/
def Mirror := ((false = false) = (true = true)) ∧ ((true = false) = (false = true))

theorem mirrorOfNotTrue (rule : type_of% @Bool.not_eq_true') : Mirror :=
  ⟨(rule false).symm, (rule true).symm⟩

theorem mirrorOfNotFalse (rule : type_of% @Bool.not_eq_false') : Mirror :=
  ⟨rule true, rule false⟩

theorem mirrorOfBEq (rule : type_of% @Bool.beq_to_eq) : Mirror :=
  ⟨(rule false false).symm, (rule true false).symm⟩

private theorem matched {b : Bool} (h : b = true) : ((b = true) = True) ↔ TrueBit := by
  cases h
  exact Iff.rfl

private theorem mismatched {b : Bool} (h : ¬ b = true) : ((b = true) = False) ↔ FalseBit := by
  cases b with
  | false => exact Iff.rfl
  | true => exact (h rfl).elim

theorem int8LTTrue (rule : type_of% @Lean.Sym.Int8.lt_eq_true) : TrueBit :=
  (matched (show (0 : Int8) < 1 from by decide)).mp (rule (0 : Int8) 1 (by decide))

theorem int8LTFalse (rule : type_of% @Lean.Sym.Int8.lt_eq_false) : FalseBit :=
  (mismatched (show ¬ (0 : Int8) < 0 from by decide)).mp (rule (0 : Int8) 0 (by decide))

theorem int8LETrue (rule : type_of% @Lean.Sym.Int8.le_eq_true) : TrueBit :=
  (matched (show (0 : Int8) ≤ 0 from by decide)).mp (rule (0 : Int8) 0 (by decide))

theorem int8LEFalse (rule : type_of% @Lean.Sym.Int8.le_eq_false) : FalseBit :=
  (mismatched (show ¬ (1 : Int8) ≤ 0 from by decide)).mp (rule (1 : Int8) 0 (by decide))

theorem int16LTTrue (rule : type_of% @Lean.Sym.Int16.lt_eq_true) : TrueBit :=
  (matched (show (0 : Int16) < 1 from by decide)).mp (rule (0 : Int16) 1 (by decide))

theorem int16LTFalse (rule : type_of% @Lean.Sym.Int16.lt_eq_false) : FalseBit :=
  (mismatched (show ¬ (0 : Int16) < 0 from by decide)).mp (rule (0 : Int16) 0 (by decide))

theorem int16LETrue (rule : type_of% @Lean.Sym.Int16.le_eq_true) : TrueBit :=
  (matched (show (0 : Int16) ≤ 0 from by decide)).mp (rule (0 : Int16) 0 (by decide))

theorem int16LEFalse (rule : type_of% @Lean.Sym.Int16.le_eq_false) : FalseBit :=
  (mismatched (show ¬ (1 : Int16) ≤ 0 from by decide)).mp (rule (1 : Int16) 0 (by decide))

theorem int32LTTrue (rule : type_of% @Lean.Sym.Int32.lt_eq_true) : TrueBit :=
  (matched (show (0 : Int32) < 1 from by decide)).mp (rule (0 : Int32) 1 (by decide))

theorem int32LTFalse (rule : type_of% @Lean.Sym.Int32.lt_eq_false) : FalseBit :=
  (mismatched (show ¬ (0 : Int32) < 0 from by decide)).mp (rule (0 : Int32) 0 (by decide))

theorem int32LETrue (rule : type_of% @Lean.Sym.Int32.le_eq_true) : TrueBit :=
  (matched (show (0 : Int32) ≤ 0 from by decide)).mp (rule (0 : Int32) 0 (by decide))

theorem int32LEFalse (rule : type_of% @Lean.Sym.Int32.le_eq_false) : FalseBit :=
  (mismatched (show ¬ (1 : Int32) ≤ 0 from by decide)).mp (rule (1 : Int32) 0 (by decide))

theorem int64LTTrue (rule : type_of% @Lean.Sym.Int64.lt_eq_true) : TrueBit :=
  (matched (show (0 : Int64) < 1 from by decide)).mp (rule (0 : Int64) 1 (by decide))

theorem int64LTFalse (rule : type_of% @Lean.Sym.Int64.lt_eq_false) : FalseBit :=
  (mismatched (show ¬ (0 : Int64) < 0 from by decide)).mp (rule (0 : Int64) 0 (by decide))

theorem int64LETrue (rule : type_of% @Lean.Sym.Int64.le_eq_true) : TrueBit :=
  (matched (show (0 : Int64) ≤ 0 from by decide)).mp (rule (0 : Int64) 0 (by decide))

theorem int64LEFalse (rule : type_of% @Lean.Sym.Int64.le_eq_false) : FalseBit :=
  (mismatched (show ¬ (1 : Int64) ≤ 0 from by decide)).mp (rule (1 : Int64) 0 (by decide))

private def ratZero : Rat := ⟨0, 1, by decide, rfl⟩
private def ratOne : Rat := ⟨1, 1, by decide, rfl⟩

theorem ratLTTrue (rule : type_of% @Lean.Sym.Rat.lt_eq_true) : TrueBit :=
  (matched (show ratZero < ratOne from by decide)).mp (rule ratZero ratOne (by decide))

theorem ratLTFalse (rule : type_of% @Lean.Sym.Rat.lt_eq_false) : FalseBit :=
  (mismatched (show ¬ ratZero < ratZero from by decide)).mp (rule ratZero ratZero (by decide))

/-- The rational non-strict order tests whether the reverse comparison is false. -/
def FalseEqualsFalse := (false = false) = True

def TrueEqualsFalse := (true = false) = False

theorem ratLETrue (rule : type_of% @Lean.Sym.Rat.le_eq_true) : FalseEqualsFalse :=
  rule ratZero ratZero (by decide)

theorem ratLEFalse (rule : type_of% @Lean.Sym.Rat.le_eq_false) : TrueEqualsFalse :=
  rule ratOne ratZero (by decide)

theorem decidablePropExtOfReflection (rule : type_of% @decide_eq_true_eq)
    : OptionalIndex.DecidablePropExt := by
  intro p q dp dq equiv
  have agree : decide p = decide q := by
    cases dp with
    | isTrue hp => exact (decide_eq_true (equiv.mp hp)).symm
    | isFalse hn => exact (decide_eq_false (fun hq => hn (equiv.mpr hq))).symm
  exact (rule (p := p)).symm.trans ((congrArg (fun b : Bool => b = true) agree).trans (rule (p := q)))

def witnesses : List (Name × (Name × Name)) := [
  (``Lean.Sym.Int8.lt_eq_true, ``TrueBit, ``int8LTTrue),
  (``Lean.Sym.Int8.lt_eq_false, ``FalseBit, ``int8LTFalse),
  (``Lean.Sym.Int8.le_eq_true, ``TrueBit, ``int8LETrue),
  (``Lean.Sym.Int8.le_eq_false, ``FalseBit, ``int8LEFalse),
  (``Lean.Sym.Int16.lt_eq_true, ``TrueBit, ``int16LTTrue),
  (``Lean.Sym.Int16.lt_eq_false, ``FalseBit, ``int16LTFalse),
  (``Lean.Sym.Int16.le_eq_true, ``TrueBit, ``int16LETrue),
  (``Lean.Sym.Int16.le_eq_false, ``FalseBit, ``int16LEFalse),
  (``Lean.Sym.Int32.lt_eq_true, ``TrueBit, ``int32LTTrue),
  (``Lean.Sym.Int32.lt_eq_false, ``FalseBit, ``int32LTFalse),
  (``Lean.Sym.Int32.le_eq_true, ``TrueBit, ``int32LETrue),
  (``Lean.Sym.Int32.le_eq_false, ``FalseBit, ``int32LEFalse),
  (``Lean.Sym.Int64.lt_eq_true, ``TrueBit, ``int64LTTrue),
  (``Lean.Sym.Int64.lt_eq_false, ``FalseBit, ``int64LTFalse),
  (``Lean.Sym.Int64.le_eq_true, ``TrueBit, ``int64LETrue),
  (``Lean.Sym.Int64.le_eq_false, ``FalseBit, ``int64LEFalse),
  (``Lean.Sym.Rat.lt_eq_true, ``TrueBit, ``ratLTTrue),
  (``Lean.Sym.Rat.lt_eq_false, ``FalseBit, ``ratLTFalse),
  (``Lean.Sym.Rat.le_eq_true, ``FalseEqualsFalse, ``ratLETrue),
  (``Lean.Sym.Rat.le_eq_false, ``TrueEqualsFalse, ``ratLEFalse),
  (``Bool.not_eq_true', ``Mirror, ``mirrorOfNotTrue),
  (``Bool.not_eq_false', ``Mirror, ``mirrorOfNotFalse),
  (``Bool.beq_to_eq, ``Mirror, ``mirrorOfBEq),
  (``decide_eq_true_eq, ``OptionalIndex.DecidablePropExt, ``decidablePropExtOfReflection)]

end BooleanReflection

namespace ConstructorNormalization

theorem propextOfDecision
    (lift : type_of% @instDecidableEqOfIff)
    (accept : ∀ (p q : Prop) (h : p ↔ q), @decide (p = q) (@lift p q (.isTrue h)) = true) :
    type_of% @propext :=
  fun {p q} h => @of_decide_eq_true (p = q) (@lift p q (.isTrue h)) (accept p q h)

/-- Adding the same natural to both sides preserves their equality proposition. -/
def AddCancel := ∀ n a b : Nat, (a + n = b + n) = (a = b)

theorem addCancelOfSucc (inject : type_of% @Nat.succ.injEq) : AddCancel := by
  intro n a b
  induction n with
  | zero => rfl
  | succ n prev => exact (inject (a+n) (b+n)).trans prev

/-- The proposition equating two prefixed lists retains every equality of corresponding heads. -/
def PrefixEquality : Prop := ∀ {α : Type u} (s t : List α) (xs ys : List α), s.length = t.length →
  ((s ++ xs) = (t ++ ys)) = List.foldr (fun ab r => ab.1 = ab.2 ∧ r) (xs = ys) (s.zip t)

theorem prefixEqualityOfCons (inject : type_of% @List.cons.injEq.{u}) : PrefixEquality.{u} := by
  intro α s
  induction s with
  | nil =>
    intro t xs ys eq
    cases t with
    | nil => rfl
    | cons _ _ => exact nomatch eq
  | cons a as ih =>
    intro t xs ys eq
    cases t with
    | nil => exact nomatch eq
    | cons b bs =>
      exact (inject a (as ++ xs) b (bs ++ ys)).trans
        (congrArg (fun r : Prop => a = b ∧ r) (ih bs xs ys (Nat.succ.inj eq)))

end ConstructorNormalization

end OmegaChecks.InitBoundaries
