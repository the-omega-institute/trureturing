module
public import Lean

/-! Zero-axiom reductions of pinned Boolean, numeric and constructor equality rules. -/

public section
open Lean
namespace OmegaChecks.InitBoundaries
universe u

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

/-- A successful lookup transports its reflection equation to the Boolean value true. -/
theorem successfulBitRead {b : Bool} (value : b = true) (law : (b = true) = True) : TrueBit :=
  (matched value).mp law

/-- Reading the single set bit compares its truth with a bound-witnessed truth. -/
def SingleBitBound := (true = true) = (∃ _ : 0 < 1, true = true)

theorem extractSingleBit {out source : Bool} (read : out = true) (original : source = true)
    (law : (out = true) = (∃ _ : 0 < 1, source = true)) : SingleBitBound := by
  cases read
  cases original
  exact law

example : (type_of% @BitVec.getElem_of_getLsbD_eq_true) ↔ TrueBit := by
  constructor
  · intro rule
    exact successfulBitRead rfl (@rule 1 1#1 0 rfl)
  · intro tag w x i h
    exact (matched ((BitVec.getLsbD_eq_getElem (BitVec.lt_of_getLsbD h)).symm.trans h)).mpr tag

example (rule : type_of% @BitVec.getElem_extractLsb'_eq_decide_getElem) : SingleBitBound := by
  apply extractSingleBit (out := (BitVec.extractLsb' 0 1 1#1)[0]) (source := (1#1)[0])
  · rw [BitVec.getElem_extractLsb']
    rfl
  · rfl
  · exact @rule 1 0 1 1#1 0 (by decide)

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

/-- A single Boolean tag constructs every original signed-word comparison of this polarity
and the corresponding strict rational comparison, at every input. -/
theorem trueComparisons : TrueBit ↔
    (type_of% @Lean.Sym.Int8.lt_eq_true) ∧ (type_of% @Lean.Sym.Int8.le_eq_true) ∧
    (type_of% @Lean.Sym.Int16.lt_eq_true) ∧ (type_of% @Lean.Sym.Int16.le_eq_true) ∧
    (type_of% @Lean.Sym.Int32.lt_eq_true) ∧ (type_of% @Lean.Sym.Int32.le_eq_true) ∧
    (type_of% @Lean.Sym.Int64.lt_eq_true) ∧ (type_of% @Lean.Sym.Int64.le_eq_true) ∧
    (type_of% @Lean.Sym.Rat.lt_eq_true) := by
  constructor
  · intro tag
    repeat' apply And.intro
    all_goals exact fun _ _ h => (matched (of_decide_eq_true h)).mpr tag
  · intro rules
    exact int8LTTrue rules.1

/-- A single Boolean tag constructs every original signed-word comparison of this polarity
and the corresponding strict rational comparison, at every input. -/
theorem falseComparisons : FalseBit ↔
    (type_of% @Lean.Sym.Int8.lt_eq_false) ∧ (type_of% @Lean.Sym.Int8.le_eq_false) ∧
    (type_of% @Lean.Sym.Int16.lt_eq_false) ∧ (type_of% @Lean.Sym.Int16.le_eq_false) ∧
    (type_of% @Lean.Sym.Int32.lt_eq_false) ∧ (type_of% @Lean.Sym.Int32.le_eq_false) ∧
    (type_of% @Lean.Sym.Int64.lt_eq_false) ∧ (type_of% @Lean.Sym.Int64.le_eq_false) ∧
    (type_of% @Lean.Sym.Rat.lt_eq_false) := by
  constructor
  · intro tag
    repeat' apply And.intro
    all_goals exact fun _ _ h => (mismatched (of_decide_eq_false h)).mpr tag
  · intro rules
    exact int8LTFalse rules.1

theorem ratLETrueIff : (type_of% @Lean.Sym.Rat.le_eq_true) ↔ FalseEqualsFalse := by
  refine ⟨ratLETrue, fun tag a b h => ?_⟩
  have yes : b.blt a = false := of_decide_eq_true h
  change (b.blt a = false) = True
  rw [yes]
  exact tag

theorem ratLEFalseIff : (type_of% @Lean.Sym.Rat.le_eq_false) ↔ TrueEqualsFalse := by
  refine ⟨ratLEFalse, fun tag a b h => ?_⟩
  have no : ¬b.blt a = false := of_decide_eq_false h
  change (b.blt a = false) = False
  cases e : b.blt a with
  | false => exact (no e).elim
  | true => exact tag

theorem decidablePropExtOfReflection (rule : type_of% @decide_eq_true_eq)
    : OptionalIndex.DecidablePropExt := by
  intro p q dp dq equiv
  have agree : decide p = decide q := by
    cases dp with
    | isTrue hp => exact (decide_eq_true (equiv.mp hp)).symm
    | isFalse hn => exact (decide_eq_false (fun hq => hn (equiv.mpr hq))).symm
  exact (rule (p := p)).symm.trans ((congrArg (fun b : Bool => b = true) agree).trans (rule (p := q)))

/-- Swapping distinct Boolean constructors preserves the proposition expressing their equality. -/
def Swapped : Prop := (true = false) = (false = true)

theorem ofEqSelf (rule : type_of% @eq_self.{1}) : TrueBit := @rule Bool true

theorem ofBooleanDecision (rule : type_of% @Lean.Sym.Bool.eq_eq_true) : TrueBit :=
  rule true true rfl

theorem ofNegativeDecision (rule : type_of% @Lean.Sym.Bool.eq_eq_false) : FalseBit :=
  rule false true rfl

theorem swappedOfFalseLeft (rule : type_of% @Bool.false_eq) : Swapped := (rule true).symm

theorem swappedOfTrueLeft (rule : type_of% @Bool.true_eq) : Swapped := rule false

/-- The only non-reflexive branch of either swapping rule is the same closed equation. -/
theorem swappingRules : Swapped ↔ (type_of% @Bool.false_eq) ∧ (type_of% @Bool.true_eq) := by
  constructor
  · intro swap
    exact ⟨fun | false => rfl | true => swap.symm, fun | false => swap | true => rfl⟩
  · exact fun rules => swappedOfTrueLeft rules.2

run_cmd
  let env ← getEnv
  for name in [``TrueBit, ``FalseBit, ``Swapped, ``SingleBitBound] do
    let some (.defnInfo closed) := env.find? name | throwError "missing Boolean equation {name}"
    let some (_, lhs, rhs) := closed.value.eq? | throwError "{name} must be an equality"
    if Kernel.isDefEqGuarded env {} lhs rhs then
      throwError "the closed propositions in {name} must be definitionally distinct"

def witnesses : List (Name × (Name × Name)) := [
  (``eq_self, ``TrueBit, ``ofEqSelf),
  (``Lean.Sym.Bool.eq_eq_true, ``TrueBit, ``ofBooleanDecision),
  (``Lean.Sym.Bool.eq_eq_false, ``FalseBit, ``ofNegativeDecision),
  (``Bool.false_eq, ``Swapped, ``swappedOfFalseLeft),
  (``Bool.true_eq, ``Swapped, ``swappedOfTrueLeft),
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

namespace NaturalComparison

/-- Every pair of naturals fits in one finite type. Its cardinality remains arbitrary
in the symbolic rule for `Fin`. -/
private theorem onFin (P : Nat → Nat → Prop) :
    (∀ {n} (a b : Fin n), P a.val b.val) ↔ ∀ a b, P a b :=
  ⟨fun rule a b => @rule (a+b+1) ⟨a, Nat.lt_succ_of_le (Nat.le_add_right a b)⟩
    ⟨b, Nat.lt_succ_of_le (Nat.le_add_left b a)⟩, fun rule _ a b => rule a.val b.val⟩

private theorem onWords (P : Nat → Nat → Prop) :
    (∀ {n} (a b : BitVec n), P a.toNat b.toNat) ↔ ∀ a b, P a b :=
  ⟨fun rule a b => @rule (a+b)
    (.ofFin ⟨a, Nat.lt_of_le_of_lt (Nat.le_add_right a b) Nat.lt_two_pow_self⟩)
    (.ofFin ⟨b, Nat.lt_of_le_of_lt (Nat.le_add_left b a) Nat.lt_two_pow_self⟩),
   fun rule _ a b => rule a.toNat b.toNat⟩

theorem finLTTrue : (type_of% @Lean.Sym.Fin.lt_eq_true) ↔ (type_of% @Lean.Sym.Nat.lt_eq_true) :=
  onFin fun a b => decide (a < b) = true → (a < b) = True

theorem finLTFalse : (type_of% @Lean.Sym.Fin.lt_eq_false) ↔ (type_of% @Lean.Sym.Nat.lt_eq_false) :=
  onFin fun a b => decide (a < b) = false → (a < b) = False

theorem finLETrue : (type_of% @Lean.Sym.Fin.le_eq_true) ↔ (type_of% @Lean.Sym.Nat.le_eq_true) :=
  onFin fun a b => decide (a ≤ b) = true → (a ≤ b) = True

theorem finLEFalse : (type_of% @Lean.Sym.Fin.le_eq_false) ↔ (type_of% @Lean.Sym.Nat.le_eq_false) :=
  onFin fun a b => decide (a ≤ b) = false → (a ≤ b) = False

theorem bitVecLTTrue : (type_of% @Lean.Sym.BitVec.lt_eq_true) ↔ (type_of% @Lean.Sym.Nat.lt_eq_true) :=
  onWords fun a b => decide (a < b) = true → (a < b) = True

theorem bitVecLTFalse : (type_of% @Lean.Sym.BitVec.lt_eq_false) ↔ (type_of% @Lean.Sym.Nat.lt_eq_false) :=
  onWords fun a b => decide (a < b) = false → (a < b) = False

theorem bitVecLETrue : (type_of% @Lean.Sym.BitVec.le_eq_true) ↔ (type_of% @Lean.Sym.Nat.le_eq_true) :=
  onWords fun a b => decide (a ≤ b) = true → (a ≤ b) = True

theorem bitVecLEFalse : (type_of% @Lean.Sym.BitVec.le_eq_false) ↔ (type_of% @Lean.Sym.Nat.le_eq_false) :=
  onWords fun a b => decide (a ≤ b) = false → (a ≤ b) = False

def equivalences : List (Name × Name × Name) := [
  (``Lean.Sym.Fin.lt_eq_true, ``Lean.Sym.Nat.lt_eq_true, ``finLTTrue),
  (``Lean.Sym.Fin.lt_eq_false, ``Lean.Sym.Nat.lt_eq_false, ``finLTFalse),
  (``Lean.Sym.Fin.le_eq_true, ``Lean.Sym.Nat.le_eq_true, ``finLETrue),
  (``Lean.Sym.Fin.le_eq_false, ``Lean.Sym.Nat.le_eq_false, ``finLEFalse),
  (``Lean.Sym.BitVec.lt_eq_true, ``Lean.Sym.Nat.lt_eq_true, ``bitVecLTTrue),
  (``Lean.Sym.BitVec.lt_eq_false, ``Lean.Sym.Nat.lt_eq_false, ``bitVecLTFalse),
  (``Lean.Sym.BitVec.le_eq_true, ``Lean.Sym.Nat.le_eq_true, ``bitVecLETrue),
  (``Lean.Sym.BitVec.le_eq_false, ``Lean.Sym.Nat.le_eq_false, ``bitVecLEFalse)]

end NaturalComparison

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

namespace ContainerEquality

/-- Equality of the propositions obtained before and after prepending one common head. -/
def CommonHead : Prop := ∀ {α : Type u} (a : α) (xs ys : List α), (a :: xs = a :: ys) = (xs = ys)

/-- Equality of the propositions obtained before and after appending one common element. -/
def CommonLast : Prop := ∀ {α : Type u} (a : α) (xs ys : List α), (xs ++ [a] = ys ++ [a]) = (xs = ys)

theorem leftIff : (type_of% @List.append_cancel_left_eq.{u}) ↔ CommonHead.{u} := by
  constructor
  · intro rule α a xs ys
    exact rule [a] xs ys
  · intro rule α s xs ys
    induction s with
    | nil => rfl
    | cons a s ih => exact (rule a (s ++ xs) (s ++ ys)).trans ih

private theorem snocAppend (l : List α) (x : α) (r : List α) : (l ++ [x]) ++ r = l ++ x :: r := by
  induction l with
  | nil => rfl
  | cons a l ih => exact congrArg (List.cons a) ih

private theorem appendNil (l : List α) : l ++ [] = l := by
  induction l with
  | nil => rfl
  | cons a l ih => exact congrArg (List.cons a) ih


theorem rightIff : (type_of% @List.append_cancel_right_eq.{u}) ↔ CommonLast.{u} := by
  constructor
  · intro rule α a xs ys
    exact rule xs [a] ys
  · intro rule α xs s ys
    induction s generalizing xs ys with
    | nil => rw [appendNil, appendNil]
    | cons a s ih =>
      rw [← snocAppend xs a s, ← snocAppend ys a s]
      exact (ih (xs ++ [a]) (ys ++ [a])).trans (rule a xs ys)

private theorem bitEq {b c : Bool} (h : (b = true) ↔ (c = true)) : b = c := by
  cases b <;> cases c
  · rfl
  · cases h.mpr rfl
  · cases h.mp rfl
  · rfl

private theorem coherent {b c : Bool} {p q : Prop} (hb : (b = true) = p)
    (hc : (c = true) = q) (h : p ↔ q) : p = q := by
  have eq := bitEq ((Iff.of_eq hb).trans (h.trans (Iff.of_eq hc.symm)))
  exact hb.symm.trans ((congrArg (fun t : Bool => t = true) eq).trans hc)

/-- Logically equivalent list equalities have equal proposition types across element types. -/
def ListEquality : Prop := ∀ {α β : Type u} [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β]
    (a b : List α) (c d : List β), (a = b ↔ c = d) → (a = b) = (c = d)

theorem ofList (rule : type_of% @List.isEqv_eq.{u}) : ListEquality.{u} := by
  intro α β _ _ _ _ a b c d h
  exact coherent (@rule α _ _ a b) (@rule β _ _ c d) h

/-- The two compared pairs of arrays may have different element types. -/
def ArrayEquality : Prop := ∀ {α β : Type u} [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β]
    (a b : Array α) (c d : Array β), (a = b ↔ c = d) → (a = b) = (c = d)

theorem ofArray (rule : type_of% @Array.isEqv_eq.{u}) : ArrayEquality.{u} := by
  intro α β _ _ _ _ a b c d h
  exact coherent (@rule α _ _ a b) (@rule β _ _ c d) h

/-- The two pairs of vectors may have different element types and different lengths. -/
def VectorEquality : Prop := ∀ {α β : Type u} [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β]
    {m n : Nat} (a b : Vector α m) (c d : Vector β n), (a = b ↔ c = d) → (a = b) = (c = d)
/-- The bounds in the public vector comparison are proof-irrelevant. -/
def vectorComparison {α : Type u} [BEq α] {n : Nat} (xs ys : Vector α n) : Bool :=
  Array.isEqvAux xs.toArray ys.toArray (xs.size_toArray.trans ys.size_toArray.symm)
    (· == ·) n (Nat.le_of_eq xs.size_toArray.symm)

abbrev VectorRule : Prop := ∀ {α : Type u} {n : Nat} [BEq α] [LawfulBEq α] {xs ys : Vector α n},
  (vectorComparison xs ys = true) = (xs = ys)

theorem ofVector (rule : VectorRule.{u}) : VectorEquality.{u} := by
  intro α β _ _ _ _ m n a b c d h
  exact coherent (rule (xs := a) (ys := b)) (rule (xs := c) (ys := d)) h

example : (type_of% @Vector.isEqv_eq.{u}) = VectorRule.{u} := rfl

/-- Equivalent nonmembership propositions have equal types across lists. -/
def ListAbsence : Prop := ∀ {α β : Type u} [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β]
    (a : α) (xs : List α) (b : β) (ys : List β), (a ∉ xs ↔ b ∉ ys) → (a ∉ xs) = (b ∉ ys)

theorem ofListSearch (rule : type_of% @List.isNone_idxOf?.{u}) : ListAbsence.{u} := by
  intro α β _ _ _ _ a xs b ys h
  exact coherent (rule (a := a) (l := xs)) (rule (a := b) (l := ys)) h

/-- Equivalent nonmembership propositions have equal types across arrays. -/
def ArrayAbsence : Prop := ∀ {α β : Type u} [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β]
    (a : α) (xs : Array α) (b : β) (ys : Array β), (a ∉ xs ↔ b ∉ ys) → (a ∉ xs) = (b ∉ ys)

/-- The observer can be specialized to the pinned array search, including its hidden bound proofs. -/
abbrev ArraySearchRule (observe : {α : Type u} → [BEq α] → Array α → α → Bool) : Prop :=
  ∀ {α : Type u} [BEq α] [LawfulBEq α] {xs : Array α} {a : α}, (observe xs a = true) = (a ∉ xs)

theorem ofArraySearch (observe : {α : Type u} → [BEq α] → Array α → α → Bool)
    (rule : ArraySearchRule @observe) : ArrayAbsence.{u} := by
  intro α β _ _ _ _ a xs b ys h
  exact coherent (rule (a := a) (xs := xs)) (rule (a := b) (xs := ys)) h

example : (type_of% @Array.isNone_idxOf?.{u}) =
    ArraySearchRule.{u} (fun {α} [beq : BEq α] xs a => (@Array.idxOf? α beq xs a).isNone) := rfl

def witnesses : List (Name × Name × Name) := [
  (``List.append_cancel_left_eq, ``CommonHead, ``leftIff),
  (``List.append_cancel_right_eq, ``CommonLast, ``rightIff),
  (``List.isEqv_eq, ``ListEquality, ``ofList),
  (``Array.isEqv_eq, ``ArrayEquality, ``ofArray),
  (``Vector.isEqv_eq, ``VectorEquality, ``ofVector),
  (``List.isNone_idxOf?, ``ListAbsence, ``ofListSearch),
  (``Array.isNone_idxOf?, ``ArrayAbsence, ``ofArraySearch)]

end ContainerEquality

end OmegaChecks.InitBoundaries
