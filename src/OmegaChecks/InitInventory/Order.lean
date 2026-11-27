module
public import Lean
import all Init.Internal.Order.Basic
import all Init.Internal.Order.MonadTail
import all Init.Data.Order.Lemmas
import all Init.Grind.Ordered.Order
import all Init.Data.Order.LemmasExtra
import Lean.Replay
import all Lean.Util.CollectAxioms
public import OmegaChecks.InitInventory.Logic
import all OmegaChecks.InitInventory.Logic

public section

open Lean
namespace OmegaChecks.InitBoundaries
universe u v w z

namespace ClassicalOrderDecisions

/-- Both directions of the Boolean relation express the same arbitrary proposition. -/
@[instance_reducible, expose] def testOrder (p : Prop) : LE Bool := ⟨fun _ _ => p⟩

private def decideWith {p : Prop} (b : Bool) (h : b = true ↔ p) : Decidable p :=
  match b with
  | true => isTrue (h.mp rfl)
  | false => isFalse fun hp => Bool.noConfusion (h.mpr hp)

def fromMin (make : type_of% @Classical.Order.instMin.{0})
    (h : ∀ p, (@make Bool (testOrder p)).min true false = true ↔ p) (p : Prop) : Decidable p :=
  decideWith _ (h p)

def fromMax (make : type_of% @Classical.Order.instMax.{0})
    (h : ∀ p, (@make Bool (testOrder p)).max true false = true ↔ p) (p : Prop) : Decidable p :=
  decideWith _ (h p)

def fromBEq (make : type_of% @Classical.Order.instBEq.{0})
    (h : ∀ p, (@make Bool (testOrder p)).beq true false = true ↔ p) (p : Prop) : Decidable p :=
  decideWith _ (h p)

def fromOrd (make : type_of% @Classical.Order.instOrd.{0})
    (h : ∀ p, (@make Bool (testOrder p)).compare true false = .eq ↔ p) (p : Prop) : Decidable p := by
  have reflects := h p
  generalize h : (@make Bool (testOrder p)).compare true false = result at reflects
  cases result with
  | eq => exact isTrue (reflects.mp rfl)
  | lt | gt => exact isFalse fun hp => Ordering.noConfusion (reflects.mpr hp)

private theorem officialMin (p : Prop) :
    (@Classical.Order.instMin Bool (testOrder p)).min true false = true ↔ p := by
  classical
  change (if p then true else false) = true ↔ p
  by_cases h : p <;> simp [h]

private theorem officialMax (p : Prop) :
    (@Classical.Order.instMax Bool (testOrder p)).max true false = true ↔ p := by
  classical
  change (if p then true else false) = true ↔ p
  by_cases h : p <;> simp [h]

private theorem officialBEq (p : Prop) :
    (@Classical.Order.instBEq Bool (testOrder p)).beq true false = true ↔ p := by
  classical
  change decide (p ∧ p) = true ↔ p
  simp

private theorem officialOrd (p : Prop) :
    (@Classical.Order.instOrd Bool (testOrder p)).compare true false = .eq ↔ p := by
  classical
  change (if p then if p then Ordering.eq else .lt else .gt) = .eq ↔ p
  by_cases h : p <;> simp [h]

run_cmd
  for name in [``fromMin, ``fromMax, ``fromBEq, ``fromOrd] do
    unless (← collectAxioms name).isEmpty do throwError "order observation uses axioms: {name}"

end ClassicalOrderDecisions

namespace AbstractOrder


section
open Std
variable {α : Type u} {a b : α}

/-- The two named endpoints inherit a linear order even if equality on the ambient type is undecided. -/
private abbrev Endpoints (a b : α) := {x : α // x = a ∨ x = b}
@[instance_reducible] private def orderEndpoints (a b : α) : LE (Endpoints a b) :=
  ⟨fun x y => x.val = y.val ∨ x.val = a ∧ y.val = b⟩
@[instance_reducible] private def strictEndpoints (a b : α) : LT (Endpoints a b) :=
  letI := orderEndpoints a b
  ⟨fun x y => x ≤ y ∧ ¬ y ≤ x⟩

private theorem endpointsLinear (a b : α) : letI := orderEndpoints a b; IsLinearOrder (Endpoints a b) := by
  letI := orderEndpoints a b
  exact {
    le_refl _ := Or.inl rfl
    le_trans x y z xy yz := by
      rcases xy with eq | ⟨xa, yb⟩
      · exact (Subtype.ext eq) ▸ yz
      rcases yz with eq | ⟨_, zb⟩
      · exact Or.inr ⟨xa, eq ▸ yb⟩
      · exact Or.inr ⟨xa, zb⟩
    le_antisymm x y xy yx := by
      rcases xy with eq | ⟨xa, _⟩
      · exact Subtype.ext eq
      rcases yx with eq | ⟨ya, _⟩
      · exact Subtype.ext eq.symm
      · exact Subtype.ext (xa.trans ya.symm)
    le_total x y := by
      rcases x.property with xa | xb <;> rcases y.property with ya | yb
      · exact Or.inl (Or.inl (xa.trans ya.symm))
      · exact Or.inl (Or.inr ⟨xa, yb⟩)
      · exact Or.inr (Or.inr ⟨ya, xb⟩)
      · exact Or.inl (Or.inl (xb.trans yb.symm)) }

private abbrev leftEnd (a b : α) : Endpoints a b := ⟨a, Or.inl rfl⟩
private abbrev rightEnd (a b : α) : Endpoints a b := ⟨b, Or.inr rfl⟩

private theorem endpointsLT (a b : α) :
    letI := orderEndpoints a b; letI := strictEndpoints a b; LawfulOrderLT (Endpoints a b) :=
  by
    letI := orderEndpoints a b
    letI := strictEndpoints a b
    exact ⟨fun _ _ => Iff.rfl⟩

private theorem endpointsForward (a b : α) : letI := orderEndpoints a b; leftEnd a b ≤ rightEnd a b :=
  Or.inr ⟨rfl, rfl⟩

private theorem eqOfReverse {a b : α} : (letI := orderEndpoints a b; rightEnd a b ≤ leftEnd a b) → a = b :=
  fun r => r.elim Eq.symm (fun h => h.2)

theorem equalityCasesOfLeIffLtOrEq (split : type_of% @Std.le_iff_lt_or_eq.{u}) :
    FiniteMembership.EqualityCases.{u} := by
  intro α a b
  letI := orderEndpoints a b
  letI := strictEndpoints a b
  letI := endpointsLinear a b
  letI := endpointsLT a b
  rcases (split (a := leftEnd a b) (b := rightEnd a b)).mp (endpointsForward a b) with lt | eq
  · exact Or.inr fun eq => lt.2 (Or.inl eq.symm)
  · exact Or.inl (congrArg Subtype.val eq)

example : (type_of% @Std.le_iff_lt_or_eq.{u}) = (type_of% @Lean.Grind.PartialOrder.le_iff_lt_or_eq.{u}) := rfl

theorem equalityCasesOfGrindTrichotomy (tri : type_of% @Lean.Grind.LinearOrder.trichotomy.{u}) :
    FiniteMembership.EqualityCases.{u} := by
  intro α a b
  letI := orderEndpoints a b
  letI := strictEndpoints a b
  letI := endpointsLinear a b
  letI := endpointsLT a b
  rcases tri (leftEnd a b) (rightEnd a b) with lt | eq | gt
  · exact Or.inr fun eq => lt.2 (Or.inl eq.symm)
  · exact Or.inl (congrArg Subtype.val eq)
  · exact (gt.2 (endpointsForward a b)).elim

/-- Equality is stable under double negation at this universe. -/
def StableEquality : Prop := ∀ {α : Type u} (a b : α), ¬¬a = b → a = b

theorem stableEqualityOfGrindComparison (le : type_of% @Lean.Grind.LinearOrder.le_of_not_lt.{u}) :
    StableEquality.{u} := by
  intro α a b nn
  letI := orderEndpoints a b
  letI := strictEndpoints a b
  letI := endpointsLinear a b
  letI := endpointsLT a b
  exact eqOfReverse (le (a := leftEnd a b) (b := rightEnd a b)
    (fun lt => nn fun eq => lt.2 (Or.inl eq.symm)))

private theorem endpointsEqualWhenEqual (h : a = b) (x y : Endpoints a b) : x = y := by
  subst b
  exact Subtype.ext ((x.property.elim id id).trans (y.property.elim id id).symm)

private theorem endpointsInseparable (nn : ¬¬ a = b) (x y : Endpoints a b) : ¬¬ x = y :=
  fun no => nn fun eq => no (endpointsEqualWhenEqual eq x y)

/-- Choosing the left operand obeys the left-leaning rules whenever no two endpoints
can be distinguished by a proof of inequality. -/
private theorem leftMinimum (nn : ¬¬ a = b) :
    letI := orderEndpoints a b
    letI : Min (Endpoints a b) := ⟨fun x _ => x⟩
    LawfulOrderLeftLeaningMin (Endpoints a b) := by
  letI := orderEndpoints a b
  letI : Min (Endpoints a b) := ⟨fun x _ => x⟩
  exact ⟨fun _ _ _ => rfl, fun x y no => (endpointsInseparable nn x y fun eq => no (Or.inl (congrArg Subtype.val eq))).elim⟩

private theorem leftMaximum (nn : ¬¬ a = b) :
    letI := orderEndpoints a b
    letI : Max (Endpoints a b) := ⟨fun x _ => x⟩
    LawfulOrderLeftLeaningMax (Endpoints a b) := by
  letI := orderEndpoints a b
  letI : Max (Endpoints a b) := ⟨fun x _ => x⟩
  exact ⟨fun _ _ _ => rfl, fun x y no => (endpointsInseparable nn y x fun eq => no (Or.inl (congrArg Subtype.val eq))).elim⟩

theorem stableEqualityOfCommutativeMin (law : type_of% @Std.instCommutativeMinOfLawfulOrderLeftLeaningMinOfIsLinearOrder.{u}) :
    StableEquality.{u} := by
  intro α a b nn
  letI := orderEndpoints a b
  letI := endpointsLinear a b
  letI : Min (Endpoints a b) := ⟨fun x _ => x⟩
  letI := leftMinimum nn
  exact congrArg Subtype.val (law.comm (leftEnd a b) (rightEnd a b))

theorem stableEqualityOfOrderMin (law : type_of% @Std.instLawfulOrderMinOfIsLinearPreorderOfLawfulOrderLeftLeaningMin.{u}) :
    StableEquality.{u} := by
  intro α a b nn
  letI := orderEndpoints a b
  letI := endpointsLinear a b
  letI : Min (Endpoints a b) := ⟨fun x _ => x⟩
  letI := leftMinimum nn
  exact eqOfReverse (((law.le_min_iff (rightEnd a b) (rightEnd a b) (leftEnd a b)).mp (Or.inl rfl)).2)

theorem stableEqualityOfOrderMax (law : type_of% @Std.instLawfulOrderMaxOfIsLinearPreorderOfLawfulOrderLeftLeaningMax.{u}) :
    StableEquality.{u} := by
  intro α a b nn
  letI := orderEndpoints a b
  letI := endpointsLinear a b
  letI : Max (Endpoints a b) := ⟨fun x _ => x⟩
  letI := leftMaximum nn
  exact eqOfReverse (((law.max_le_iff (leftEnd a b) (rightEnd a b) (leftEnd a b)).mp (Or.inl rfl)).2)

theorem stableEqualityOfMinEqOr (law : type_of% @Std.instMinEqOrOfLawfulOrderLeftLeaningMin.{u}) :
    StableEquality.{u} := by
  intro α a b nn
  letI : LE (Endpoints a b) := ⟨fun x _ => leftEnd a b = x⟩
  letI : Min (Endpoints a b) := ⟨fun _ _ => leftEnd a b⟩
  letI : LawfulOrderLeftLeaningMin (Endpoints a b) :=
    ⟨fun _ _ h => h, fun x _ no => (endpointsInseparable nn (leftEnd a b) x no).elim⟩
  exact congrArg Subtype.val ((law.min_eq_or (rightEnd a b) (rightEnd a b)).elim id id)

theorem stableEqualityOfMaxEqOr (law : type_of% @Std.instMaxEqOrOfLawfulOrderLeftLeaningMax.{u}) :
    StableEquality.{u} := by
  intro α a b nn
  letI : LE (Endpoints a b) := ⟨fun _ x => leftEnd a b = x⟩
  letI : Max (Endpoints a b) := ⟨fun _ _ => leftEnd a b⟩
  letI : LawfulOrderLeftLeaningMax (Endpoints a b) :=
    ⟨fun _ _ h => h, fun x _ no => (endpointsInseparable nn (leftEnd a b) x no).elim⟩
  exact congrArg Subtype.val ((law.max_eq_or (rightEnd a b) (rightEnd a b)).elim id id)

theorem stableEqualityOfTrichotomousLT (law : type_of% @Std.instTrichotomousLtOfLawfulOrderLTOfTotalOfAntisymmLe.{u}) :
    StableEquality.{u} := by
  intro α a b nn
  letI := orderEndpoints a b
  letI := strictEndpoints a b
  letI := endpointsLinear a b
  letI := endpointsLT a b
  let tri : Trichotomous (α := Endpoints a b) (· < ·) := @law (Endpoints a b) _ _ _
    ⟨(endpointsLinear a b).le_total⟩ ⟨(endpointsLinear a b).le_antisymm⟩
  exact congrArg Subtype.val (tri.trichotomous (leftEnd a b) (rightEnd a b)
    (fun h => nn fun eq => h.2 (Or.inl eq.symm))
    (fun h => h.2 (endpointsForward a b)))

private abbrev SingletonAntisym := ∀ {T : Type u} [LT T] [LE T] [IsLinearOrder T] [LawfulOrderLT T]
  (x y : T), [x] ≤ [y] → [y] ≤ [x] → x = y

private theorem equalityStableOfSingletons (anti : SingletonAntisym.{u}) : StableEquality.{u} := by
  intro α a b nn
  letI := orderEndpoints a b
  letI := strictEndpoints a b
  letI := endpointsLinear a b
  letI := endpointsLT a b
  have le (x y : Endpoints a b) (nn : ¬¬ x = y) : [x] ≤ [y] := by
    intro lt
    apply nn
    rintro rfl
    cases lt with
    | rel rel => exact rel.2 rel.1
    | cons tail => cases tail
  have both : ¬¬ leftEnd a b = rightEnd a b := fun no => nn fun e => no (Subtype.ext e)
  exact congrArg Subtype.val (anti _ _ (le _ _ both) (le _ _ fun no => both fun e => no e.symm))

theorem stableEqualityOfArrayAntisymm (anti : type_of% @Array.le_antisymm.{u}) : StableEquality.{u} :=
  equalityStableOfSingletons fun {_} _ _ _ _ x y le ge =>
    (List.cons.inj (congrArg Array.toList (anti (xs := #[x]) (ys := #[y]) le ge))).1

theorem stableEqualityOfVectorAntisymm (anti : type_of% @Vector.le_antisymm.{u}) : StableEquality.{u} :=
  equalityStableOfSingletons fun {T} _ _ _ _ x y le ge =>
    (List.cons.inj (congrArg (fun v : Vector T 1 => v.toArray.toList)
      (anti (xs := Vector.mk #[x] rfl) (ys := Vector.mk #[y] rfl) le ge))).1

theorem stableEqualityOfArrayOrder (order : type_of% @Array.instIsLinearOrderOfLawfulOrderLT.{u}) : StableEquality.{u} :=
  stableEqualityOfArrayAntisymm fun {_} _ _ _ _ {x y} => order.le_antisymm x y

theorem stableEqualityOfVectorOrder (order : type_of% @Vector.instIsLinearOrderOfLawfulOrderLT.{u}) : StableEquality.{u} :=
  stableEqualityOfVectorAntisymm fun {_ _} _ _ _ _ {x y} => order.le_antisymm x y

theorem stableEqualityOfListOrder (order : type_of% @List.instIsLinearOrder.{u}) : StableEquality.{u} :=
  equalityStableOfSingletons fun {_} _ _ _ _ x y le ge =>
    (List.cons.inj (order.le_antisymm [x] [y] le ge)).1

private abbrev PrefixComparison := ∀ {T : Type u} [LT T] [LE T] [IsLinearOrder T] [LawfulOrderLT T]
  (x y : T), [x] ≤ [y] → [y] < [y,y] → [x] < [y,y]

private theorem singletonReverse {T : Type u} [LT T] {x y : T} (h : [y] < [x]) : y < x := by
  cases h with
  | rel h => exact h
  | cons h => cases h

private theorem singletonToPair {T : Type u} [LT T] {x y : T} (h : [x] < [y,y]) : x < y ∨ x = y := by
  cases h with
  | rel h => exact Or.inl h
  | cons _ => exact Or.inr rfl

/-- Comparing a singleton with a length-two list exposes its first unequal head or an equal head. -/
private theorem equalityCasesOfPrefix (comparePrefix : PrefixComparison.{u}) : FiniteMembership.EqualityCases.{u} := by
  intro α a b
  letI := orderEndpoints a b
  letI := strictEndpoints a b
  letI := endpointsLinear a b
  letI := endpointsLT a b
  let x := leftEnd a b
  let y := rightEnd a b
  have le : [x] ≤ [y] := by
    intro reverse
    exact (singletonReverse reverse).2 (endpointsForward a b)
  rcases singletonToPair (comparePrefix x y le (List.Lex.cons List.Lex.nil)) with strict | eq
  · exact Or.inr fun eq => strict.2 (Or.inl eq.symm)
  · exact Or.inl (congrArg Subtype.val eq)

theorem equalityCasesOfListComparison (law : type_of% @List.lt_of_le_of_lt.{u}) :
    FiniteMembership.EqualityCases.{u} :=
  equalityCasesOfPrefix fun _ _ le lt => law le lt

theorem equalityCasesOfArrayComparison (law : type_of% @Array.lt_of_le_of_lt.{u}) :
    FiniteMembership.EqualityCases.{u} :=
  equalityCasesOfPrefix fun x y le lt => law (xs := #[x]) (ys := #[y]) (zs := #[y,y]) le lt

end

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

set_option linter.deprecated false in
theorem weakMiddleOfTotalNotLT (total : type_of% @Std.instTotalNotLtOfLawfulOrderLTOfLe.{0}) (p : Prop) :
    ¬p ∨ ¬¬p := by
  letI : LE Bool := ⟨signed p⟩
  letI : LT Bool := ⟨signed p⟩
  letI : Std.LawfulOrderLT Bool := ⟨fun a b =>
    ⟨fun h => ⟨h, (signedAsymm p).asymm a b h⟩, And.left⟩⟩
  exact (@total Bool _ _ _).total false true

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

/-- Singleton lexicographic comparisons distinguish a proposition from its negation. -/
private theorem weakMiddleOfSingletons (p : Prop) (total :
    letI : LT Bool := ⟨signed p⟩
    [false] ≤ [true] ∨ [true] ≤ [false]) : ¬p ∨ ¬¬p := by
  letI : LT Bool := ⟨signed p⟩
  exact total.elim (fun le => .inr fun neg => le (.rel neg)) (fun le => .inl fun pos => le (.rel pos))

theorem weakMiddleOfListTotal (total : type_of% @List.le_total.{0}) (p : Prop) : ¬p ∨ ¬¬p :=
  weakMiddleOfSingletons p (@total Bool ⟨signed p⟩ (signedAsymm p) [false] [true])

theorem weakMiddleOfListTotalInstance (total : type_of% @List.instTotalLeOfAsymmLt.{0}) (p : Prop) : ¬p ∨ ¬¬p :=
  weakMiddleOfSingletons p ((@total Bool ⟨signed p⟩ (signedAsymm p)).total [false] [true])

theorem weakMiddleOfArrayTotal (total : type_of% @Array.le_total.{0}) (p : Prop) : ¬p ∨ ¬¬p :=
  weakMiddleOfSingletons p (@total Bool ⟨signed p⟩ (signedAsymm p) #[false] #[true])

theorem weakMiddleOfArrayTotalInstance (total : type_of% @Array.instTotalLeOfAsymmLt.{0}) (p : Prop) : ¬p ∨ ¬¬p :=
  weakMiddleOfSingletons p ((@total Bool ⟨signed p⟩ (signedAsymm p)).total #[false] #[true])

theorem weakMiddleOfVectorTotal (total : type_of% @Vector.le_total.{0}) (p : Prop) : ¬p ∨ ¬¬p := by
  letI : LT Bool := ⟨signed p⟩
  letI := signedAsymm p
  apply weakMiddleOfSingletons p
  exact total (Vector.mk #[false] rfl) (Vector.mk #[true] rfl)

theorem weakMiddleOfVectorTotalInstance (total : type_of% @Vector.instTotalLeOfAsymmLt.{0}) (p : Prop) : ¬p ∨ ¬¬p := by
  letI : LT Bool := ⟨signed p⟩
  letI := signedAsymm p
  apply weakMiddleOfSingletons p
  exact total.total (Vector.mk #[false] rfl) (Vector.mk #[true] rfl)

private theorem singletonLe (p : Prop) (nn : ¬¬p) :
    letI : LT Bool := ⟨signed p⟩
    [false] ≤ [true] := by
  letI : LT Bool := ⟨signed p⟩
  intro reverse
  cases reverse with
  | rel h => exact nn h

theorem excludedMiddleOfConsLe (consLe : type_of% @List.cons_le_cons_iff.{0}) (p : Prop) : p ∨ ¬p := by
  apply excludedMiddleFromDNE _ p
  intro q nn
  letI : LT Bool := ⟨signed q⟩
  have parts := (@consLe Bool _ (signedAsymm q) (signedTri q) false true [] []).mp (singletonLe q nn)
  exact parts.elim id (fun h => False.elim (Bool.noConfusion h.1))

private theorem singletonStrictOrEqual (q : Prop) :
    letI : LT Bool := ⟨signed q⟩
    [false] < [true] ∨ [false] = [true] → q := by
  letI : LT Bool := ⟨signed q⟩
  intro h
  rcases h with h | h
  · cases h with
    | rel h => exact h
  · exact Bool.noConfusion (List.cons.inj h).1

theorem excludedMiddleOfListLeIffLTOrEq (split : type_of% @List.le_iff_lt_or_eq.{0}) (p : Prop) : p ∨ ¬p := by
  apply excludedMiddleFromDNE _ p
  intro q nn
  letI : LT Bool := ⟨signed q⟩
  letI := signedAsymm q
  letI := signedTri q
  exact singletonStrictOrEqual q (split.mp (singletonLe q nn))

theorem excludedMiddleOfArrayLeIffLTOrEq (split : type_of% @Array.le_iff_lt_or_eq.{0}) (p : Prop) : p ∨ ¬p := by
  apply excludedMiddleFromDNE _ p
  intro q nn
  letI : LT Bool := ⟨signed q⟩
  letI := signedAsymm q
  letI := signedTri q
  exact singletonStrictOrEqual q (((split (xs := #[false]) (ys := #[true])).mp (singletonLe q nn)).imp_right
    (congrArg Array.toList))

theorem excludedMiddleOfVectorLeIffLTOrEq (split : type_of% @Vector.le_iff_lt_or_eq.{0}) (p : Prop) : p ∨ ¬p := by
  apply excludedMiddleFromDNE _ p
  intro q nn
  letI : LT Bool := ⟨signed q⟩
  letI := signedAsymm q
  letI := signedTri q
  exact singletonStrictOrEqual q (((split (xs := Vector.mk #[false] rfl) (ys := Vector.mk #[true] rfl)).mp
    (singletonLe q nn)).imp_right (congrArg fun v : Vector Bool 1 => v.toArray.toList))

theorem excludedMiddleOfListLeExists (descr : type_of% @List.le_iff_exists.{0}) (p : Prop) : p ∨ ¬p := by
  apply excludedMiddleFromDNE _ p
  intro q nn
  letI : LT Bool := ⟨signed q⟩
  obtain eq | ⟨i, hi, _, _, hit⟩ :=
    (@descr Bool _ (signedAsymm q) (signedTri q) [false] [true]).mp (singletonLe q nn)
  · exact Bool.noConfusion (List.cons.inj eq).1
  · cases i with
    | zero => exact hit
    | succ i => exact (Nat.not_succ_le_zero i (Nat.le_of_lt_succ hi)).elim

theorem excludedMiddleOfArrayLeExists (descr : type_of% @Array.le_iff_exists.{0}) (p : Prop) : p ∨ ¬p := by
  apply excludedMiddleFromDNE _ p
  intro q nn
  letI : LT Bool := ⟨signed q⟩
  obtain eq | ⟨i, hi, _, _, hit⟩ :=
    (@descr Bool _ (signedAsymm q) (signedTri q) #[false] #[true]).mp (singletonLe q nn)
  · exact Bool.noConfusion (List.cons.inj (congrArg Array.toList eq)).1
  · cases i with
    | zero => exact hit
    | succ i => exact (Nat.not_succ_le_zero i (Nat.le_of_lt_succ hi)).elim

theorem excludedMiddleOfVectorLeExists (descr : type_of% @Vector.le_iff_exists.{0}) (p : Prop) : p ∨ ¬p := by
  apply excludedMiddleFromDNE _ p
  intro q nn
  letI : LT Bool := ⟨signed q⟩
  letI := signedAsymm q
  letI := signedTri q
  obtain eq | ⟨i, hi, _, hit⟩ :=
    (descr (xs := Vector.mk #[false] rfl) (ys := Vector.mk #[true] rfl)).mp (singletonLe q nn)
  · exact Bool.noConfusion (List.cons.inj (congrArg (fun v => v.toArray.toList) eq)).1
  · cases i with
    | zero => exact hit
    | succ i => exact (Nat.not_succ_le_zero i (Nat.le_of_lt_succ hi)).elim

namespace PredicateBounds

/-- At the distinguished endpoint, the bound of two elements tests both predicates. -/
private def condition : Option Prop → Prop
  | none => True
  | some p => p

private def compare (a : Option Prop) : Option Prop → Prop
  | none => condition a
  | some _ => True

private def joint (a b : Option Prop) : Option Prop := some (condition a ∧ condition b)

private theorem total (a b : Option Prop) : compare a b ∨ compare b a := by
  cases b with
  | some _ => exact .inl trivial
  | none => cases a with
    | some _ => exact .inr trivial
    | none => exact .inl trivial

private theorem bound (a b c : Option Prop) :
    compare (joint a b) c ↔ compare a c ∧ compare b c := by
  cases c with
  | none => exact Iff.rfl
  | some _ => exact ⟨fun _ => ⟨trivial, trivial⟩, fun _ => trivial⟩

private def strict (a b : Option Prop) := compare a b ∧ ¬compare b a

theorem weakMiddleOfLTMax (law : type_of% @Std.lt_max_iff.{0}) (p : Prop) : ¬p ∨ ¬¬p := by
  letI : LE (Option Prop) := ⟨compare⟩
  letI : LT (Option Prop) := ⟨strict⟩
  letI : Max (Option Prop) := ⟨joint⟩
  letI : Std.Total (α := Option Prop) (· ≤ ·) := ⟨total⟩
  letI : Std.LawfulOrderSup (Option Prop) := ⟨bound⟩
  letI : Std.LawfulOrderLT (Option Prop) := ⟨fun _ _ => Iff.rfl⟩
  exact ((law (a := none) (b := some p) (c := some (¬p))).mp
    ⟨trivial, fun h => h.2 h.1⟩).imp And.right And.right

theorem weakMiddleOfMinLT (law : type_of% @Std.min_lt_iff.{0}) (p : Prop) : ¬p ∨ ¬¬p := by
  letI : LE (Option Prop) := ⟨fun a b => compare b a⟩
  letI : LT (Option Prop) := ⟨fun a b => strict b a⟩
  letI : Min (Option Prop) := ⟨joint⟩
  letI : Std.Total (α := Option Prop) (· ≤ ·) := ⟨fun a b => total b a⟩
  letI : Std.LawfulOrderInf (Option Prop) := ⟨fun a b c => bound b c a⟩
  letI : Std.LawfulOrderLT (Option Prop) := ⟨fun _ _ => Iff.rfl⟩
  exact ((law (a := some p) (b := some (¬p)) (c := none)).mp
    ⟨trivial, fun h => h.2 h.1⟩).imp And.right And.right

end PredicateBounds

end AbstractOrder

namespace OrderTags
open Lean.Grind Std

/-- Two off-diagonal comparisons encode arbitrary disjoint propositions. -/
private def comparison (diagonal p q : Prop) (a b : Bool) : Prop :=
  Bool.rec (Bool.rec diagonal p b) (Bool.rec q diagonal b) a

@[instance_reducible] private def weak (p q : Prop) : LE Bool := ⟨comparison True p q⟩
@[instance_reducible] private def strict (p q : Prop) : LT Bool := ⟨comparison False p q⟩

private theorem preorder (p q : Prop) : @IsPreorder Bool (weak p q) :=
  @IsPreorder.mk Bool (weak p q) (fun a => by cases a <;> exact True.intro)
    (fun a b c h k => by cases a <;> cases b <;> cases c <;> first | exact trivial | exact h | exact k)

private theorem lawful (p q : Prop) (disjoint : p → ¬q) : @LawfulOrderLT Bool (strict p q) (weak p q) := by
  apply @LawfulOrderLT.mk Bool (strict p q) (weak p q)
  intro a b
  cases a <;> cases b
  · exact ⟨False.elim, fun h => h.2 h.1⟩
  · exact ⟨fun h => ⟨h, disjoint h⟩, And.left⟩
  · exact ⟨fun h => ⟨h, fun hp => disjoint hp h⟩, And.left⟩
  · exact ⟨False.elim, fun h => h.2 h.1⟩

theorem weakRefl : (type_of% @Order.le_eq_true.{0}) ↔ InhabitedPropExt := by
  constructor
  · intro law p hp
    letI : LE Unit := ⟨fun _ _ => p⟩
    letI : IsPreorder Unit := ⟨fun _ => hp, fun _ _ _ h _ => h⟩
    exact @law Unit _ _ ()
  · intro canon α _ _ a
    exact canon _ (IsPreorder.le_refl a)

theorem weakOfStrict : (type_of% @Order.le_eq_true_of_lt.{0}) ↔ InhabitedPropExt := by
  constructor
  · intro law p hp
    exact @law Bool (weak p False) (strict p False) (lawful p False (fun _ => id)) false true hp
  · intro canon α _ _ _ a b h
    exact canon _ ((LawfulOrderLT.lt_iff a b).mp h).1

theorem strictRefl : (type_of% @Order.lt_eq_false.{0}) ↔ RefutedPropExt := by
  constructor
  · intro law p np
    letI : LE Unit := ⟨fun _ _ => True⟩
    letI : LT Unit := ⟨fun _ _ => p⟩
    letI : LawfulOrderLT Unit := ⟨fun _ _ => ⟨fun h => (np h).elim, fun h => (h.2 h.1).elim⟩⟩
    exact @law Unit _ _ _ ()
  · intro canon α _ _ _ a
    apply canon
    intro h
    have k := (LawfulOrderLT.lt_iff a a).mp h
    exact k.2 k.1

theorem weakOfReverseStrict : (type_of% @Order.le_eq_false_of_lt.{0}) ↔ RefutedPropExt := by
  constructor
  · intro law p np
    exact @law Bool (weak True p) (strict True p) (lawful True p (fun _ => np)) (preorder True p) false true trivial
  · intro canon α _ _ _ _ a b h
    exact canon _ ((LawfulOrderLT.lt_iff a b).mp h).2

theorem strictOfReverseStrict : (type_of% @Order.lt_eq_false_of_lt.{0}) ↔ RefutedPropExt := by
  constructor
  · intro law p np
    exact @law Bool (weak True p) (strict True p) (lawful True p (fun _ => np)) (preorder True p) false true trivial
  · intro canon α _ _ _ _ a b h
    exact canon _ fun k => ((LawfulOrderLT.lt_iff a b).mp h).2 ((LawfulOrderLT.lt_iff b a).mp k).1

theorem strictOfReverseWeak : (type_of% @Order.lt_eq_false_of_le.{0}) ↔ RefutedPropExt := by
  constructor
  · intro law p np
    exact @law Bool (weak True p) (strict True p) (lawful True p (fun _ => np)) (preorder True p) false true trivial
  · intro canon α _ _ _ _ a b h
    exact canon _ fun k => ((LawfulOrderLT.lt_iff b a).mp k).2 h

/-- The three pinned rules together identify equivalent propositions. The
comparison supplies the case split, and the two tags identify each case. -/
theorem propextFromOrderRules (compare : type_of% @Order.le_of_not_lt.{0})
    (positive : type_of% @Order.le_eq_true.{0}) (negative : type_of% @Order.lt_eq_false.{0}) :
    type_of% @propext := by
  intro p q equiv
  cases GrindOrder.excludedMiddleFromComparison (@compare) p with
  | inl hp =>
    have normalize := weakRefl.mp (@positive)
    exact (normalize p hp).trans (normalize q (equiv.mp hp)).symm
  | inr np =>
    have normalize := strictRefl.mp (@negative)
    exact (normalize p np).trans (normalize q (fun hq => np (equiv.mpr hq))).symm

/-- Each full rule is equivalent at the small universe to the indicated
truth-value normalization. Neither normalization is marked as a forbidden axiom. -/
def equivalences : List (Name × Name × Name) := [
  (``Order.le_eq_true, ``InhabitedPropExt, ``weakRefl),
  (``Order.le_eq_true_of_lt, ``InhabitedPropExt, ``weakOfStrict),
  (``Order.lt_eq_false, ``RefutedPropExt, ``strictRefl),
  (``Order.le_eq_false_of_lt, ``RefutedPropExt, ``weakOfReverseStrict),
  (``Order.lt_eq_false_of_lt, ``RefutedPropExt, ``strictOfReverseStrict),
  (``Order.lt_eq_false_of_le, ``RefutedPropExt, ``strictOfReverseWeak)]

end OrderTags

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

/-- A chain of encoded decisions has at most one member. When the decision exists,
its encoding must be the supremum in every chain-complete partial order. -/
private theorem excludedMiddleOfDecisionChain {α : Type} {p : Prop} (order : CCPO α)
    (encode : Decidable p → α) (decode : α → Option (Decidable p))
    (recover : ∀ d, decode (encode d) = some d) : p ∨ ¬p := by
  letI := order
  let c : α → Prop := fun x => ∃ d, x = encode d
  have ordered : chain c := by
    rintro _ _ ⟨d, rfl⟩ ⟨d', rfl⟩
    cases Subsingleton.elim d d'
    exact .inl PartialOrder.rel_refl
  obtain ⟨s, least⟩ := order.has_csup ordered
  cases hs : decode s with
  | some d => cases d with
    | isTrue hp => exact .inl hp
    | isFalse hn => exact .inr hn
  | none =>
    refine .inr fun hp => ?_
    let d : Decidable p := .isTrue hp
    have first : s ⊑ encode d := (least _).mpr (by
      rintro _ ⟨d', rfl⟩
      cases Subsingleton.elim d' d
      exact PartialOrder.rel_refl)
    have second : encode d ⊑ s := (least s).mp PartialOrder.rel_refl _ ⟨d, rfl⟩
    have same := PartialOrder.rel_antisymm first second
    exact nomatch hs.symm.trans ((congrArg decode same).trans (recover d))

theorem excludedMiddleOfOptionCCPO (order : type_of% @Lean.Order.instCCPOOption.{0})
    (p : Prop) : p ∨ ¬p :=
  excludedMiddleOfDecisionChain (@order (Decidable p)) some id (fun _ => rfl)

theorem excludedMiddleOfFlatCCPO (order : type_of% @Lean.Order.FlatOrder.instCCPO.{1})
    (p : Prop) : p ∨ ¬p :=
  excludedMiddleOfDecisionChain (@order (Option (Decidable p)) none) some id (fun _ => rfl)

/-- In a flat order a chain containing a nonbottom element has that element as its supremum.
Otherwise excluded middle shows every member is the bottom. Both choices take place in Prop. -/
@[instance_reducible] def flatCCPOOfEM (em : ∀ p : Prop, p ∨ ¬p) :
    type_of% @FlatOrder.instCCPO.{u} := fun {α b} => {
  toPartialOrder := FlatOrder.instOrder
  has_csup := by
    intro c ordered
    cases em (∃ x, c x ∧ x ≠ b) with
    | inl existsNonbottom =>
      obtain ⟨s, member, above⟩ := existsNonbottom
      refine ⟨s, fun x => ⟨?_, fun upper => upper s member⟩⟩
      intro sx y hy
      cases ordered y s hy member with
      | inl ys => exact PartialOrder.rel_trans ys sx
      | inr sy =>
        change FlatOrder.rel s y at sy
        cases sy with
        | bot => exact (above rfl).elim
        | refl => exact sx
    | inr allBottom =>
      refine ⟨b, fun x => ⟨?_, fun _ => FlatOrder.rel.bot⟩⟩
      intro _ y hy
      cases em (y = b) with
      | inl same => cases same; exact FlatOrder.rel.bot
      | inr above => exact (allBottom ⟨y, hy, above⟩).elim }

@[instance_reducible] def optionCCPOOfEM (em : ∀ p : Prop, p ∨ ¬p) :
    type_of% @Lean.Order.instCCPOOption.{u} :=
  fun {α} => @flatCCPOOfEM.{u+1} em (Option α) none

theorem flatCCPOIffEM : Nonempty (type_of% @FlatOrder.instCCPO.{1}) ↔ (∀ p : Prop, p ∨ ¬p) :=
  ⟨fun h => h.elim fun order => excludedMiddleOfFlatCCPO (@order), fun em => ⟨@flatCCPOOfEM.{1} em⟩⟩

theorem optionCCPOIffEM : Nonempty (type_of% @Lean.Order.instCCPOOption.{0}) ↔ (∀ p : Prop, p ∨ ¬p) :=
  ⟨fun h => h.elim fun order => excludedMiddleOfOptionCCPO (@order), fun em => ⟨@optionCCPOOfEM.{0} em⟩⟩

example (em : ∀ p : Prop, p ∨ ¬p) {α : Sort u} {b : α} :
    (@flatCCPOOfEM em α b).toPartialOrder = FlatOrder.instOrder := rfl

example (em : ∀ p : Prop, p ∨ ¬p) {α : Type u} :
    (@optionCCPOOfEM em α).toPartialOrder = Lean.Order.instPartialOrderOption := rfl

private theorem excludedMiddleOfStateResult {ε σ : Type} {p : Prop}
    (order : CCPO (EST ε σ (Option (Decidable p)))) : p ∨ ¬p := by
  obtain ⟨w⟩ := Void.instNonempty (σ := σ)
  apply excludedMiddleOfDecisionChain order (fun d t => .ok (some d) t) (fun act =>
    match act w with
    | .ok d _ => d
    | .error _ _ => none)
  intro d
  rfl

theorem excludedMiddleOfESTCCPO (order : type_of% @Lean.Order.instCCPOESTOfNonempty)
    (p : Prop) : p ∨ ¬p := excludedMiddleOfStateResult (@order Unit Unit (Option (Decidable p)) inferInstance)

theorem excludedMiddleOfEIOCCPO (order : type_of% @Lean.Order.instCCPOEIOOfNonempty)
    (p : Prop) : p ∨ ¬p := excludedMiddleOfStateResult (@order Unit (Option (Decidable p)) inferInstance)

theorem excludedMiddleOfIOCCPO (order : type_of% @Lean.Order.instCCPOIO)
    (p : Prop) : p ∨ ¬p := excludedMiddleOfStateResult (@order (Option (Decidable p)))

private theorem excludedMiddleOfSTResult {σ : Type} {p : Prop}
    (order : CCPO (ST σ (Option (Decidable p)))) : p ∨ ¬p := by
  obtain ⟨w⟩ := Void.instNonempty (σ := σ)
  exact excludedMiddleOfDecisionChain order (fun d t => ⟨some d, t⟩)
    (fun act => (act w).val) (fun _ => rfl)

theorem excludedMiddleOfSTCCPO (order : type_of% @instCCPOSTOfNonempty)
    (p : Prop) : p ∨ ¬p := excludedMiddleOfSTResult (@order (Option (Decidable p)) Unit ⟨none⟩)

private abbrev tailOrder {m : Type → Type} [Bind m] (order : MonadTail m) (p : Prop) :
    CCPO (m (Option (Decidable p))) :=
  @MonadTail.instCCPO m _ order (Option (Decidable p)) ⟨none⟩

theorem excludedMiddleOfIdTail (order : type_of% @instMonadTailId.{0})
    (p : Prop) : p ∨ ¬p :=
  excludedMiddleOfDecisionChain (tailOrder order p) some id (fun _ => rfl)

theorem excludedMiddleOfOptionTail (order : type_of% @instMonadTailOption.{0})
    (p : Prop) : p ∨ ¬p :=
  excludedMiddleOfDecisionChain (tailOrder order p) (some ∘ some)
    Option.join (fun _ => rfl)

theorem excludedMiddleOfExceptTail (order : type_of% @instMonadTailExcept.{0,0})
    (p : Prop) : p ∨ ¬p :=
  excludedMiddleOfDecisionChain (tailOrder (@order Unit) p)
    (fun d => .ok (some d)) (fun act => match act with | .ok val => val | .error _ => none)
    (fun _ => rfl)

theorem excludedMiddleOfSTTail (order : type_of% @instMonadTailST)
    (p : Prop) : p ∨ ¬p := excludedMiddleOfSTResult (tailOrder (@order Unit) p)

theorem excludedMiddleOfBaseIOTail (order : type_of% @instMonadTailBaseIO)
    (p : Prop) : p ∨ ¬p := excludedMiddleOfSTResult (tailOrder order p)

theorem excludedMiddleOfESTTail (order : type_of% @instMonadTailESTOfNonempty)
    (p : Prop) : p ∨ ¬p := excludedMiddleOfStateResult (tailOrder (@order Unit Unit inferInstance) p)

theorem excludedMiddleOfEIOTail (order : type_of% @instMonadTailEIOOfNonempty)
    (p : Prop) : p ∨ ¬p := excludedMiddleOfStateResult (tailOrder (@order Unit inferInstance) p)

theorem excludedMiddleOfIOTail (order : type_of% @instMonadTailIO)
    (p : Prop) : p ∨ ¬p := excludedMiddleOfStateResult (tailOrder order p)

def decisionChains : List (Name × Name) := [
  (``Lean.Order.instCCPOOption, ``excludedMiddleOfOptionCCPO),
  (``FlatOrder.instCCPO, ``excludedMiddleOfFlatCCPO),
  (``Lean.Order.instCCPOESTOfNonempty, ``excludedMiddleOfESTCCPO),
  (``Lean.Order.instCCPOEIOOfNonempty, ``excludedMiddleOfEIOCCPO),
  (``Lean.Order.instCCPOIO, ``excludedMiddleOfIOCCPO)]

def tailDecisionChains : List (Name × Name) := [
  (``Lean.Order.instCCPOSTOfNonempty, ``excludedMiddleOfSTCCPO),
  (``Lean.Order.instMonadTailId, ``excludedMiddleOfIdTail),
  (``Lean.Order.instMonadTailOption, ``excludedMiddleOfOptionTail),
  (``Lean.Order.instMonadTailExcept, ``excludedMiddleOfExceptTail),
  (``Lean.Order.instMonadTailST, ``excludedMiddleOfSTTail),
  (``Lean.Order.instMonadTailBaseIO, ``excludedMiddleOfBaseIOTail),
  (``Lean.Order.instMonadTailESTOfNonempty, ``excludedMiddleOfESTTail),
  (``Lean.Order.instMonadTailEIOOfNonempty, ``excludedMiddleOfEIOTail),
  (``Lean.Order.instMonadTailIO, ``excludedMiddleOfIOTail)]

theorem excludedMiddleOfFlatCSup (pick : type_of% @flat_csup.{1})
    (valid : ∀ {α : Type} (c : Option α → Prop), chain c → is_sup c (@pick (Option α) none c))
    (p : Prop) : p ∨ ¬p :=
  excludedMiddleOfFlatSuprema (fun {_ c} hc => ⟨_, valid c hc⟩) p

/-- The tag of the returned option for the predicate containing every point
of the flat order, including its bottom. -/
abbrev flatOptionTag (pick : type_of% @flat_csup.{u+1}) (α : Type u) : Bool :=
  (@pick (Option α) none (fun _ => True)).inner.isSome

abbrev returnsFlatSome (pick : type_of% @flat_csup.{u+1}) : Prop :=
  ∀ (α : Type u), Nonempty α → flatOptionTag (@pick) α = true

/-- The official definition selects a nonbottom point whenever one exists,
including for predicates that are not chains. -/
theorem officialFlatPresence : returnsFlatSome (@flat_csup.{u+1}) := by
  intro α nonempty
  have has : ∃ x : FlatOrder (none : Option α), True ∧ x ≠ none :=
    nonempty.elim fun a => ⟨some a, trivial, fun eq => nomatch eq⟩
  unfold flatOptionTag flat_csup
  rw [dite_eq_left has]
  have notBottom := (Classical.choose_spec has).2
  generalize eq : Classical.choose has = x at *
  cases x with
  | none => exact (notBottom rfl).elim
  | some => rfl

/-- Preserving the pinned tag exposes a witness for every inhabited sort. -/
def choiceFromFlatPresence (pick : type_of% @flat_csup.{u+1}) (present : returnsFlatSome (@pick)) :
    type_of% @Classical.choice.{u} := fun {α} nonempty =>
  ((@pick (Option (PLift α)) none (fun _ => True)).inner.get
    (present (PLift α) (nonempty.elim fun x => ⟨⟨x⟩⟩))).down

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

theorem propextOfImplicationLattice (order : CompleteLattice Prop)
    (rel : ∀ p q : Prop, (p → q) → order.rel p q) : type_of% @propext :=
  propextOfImplicationOrder order.toPartialOrder rel

theorem propextOfReverseImplicationLattice (order : CompleteLattice Prop)
    (rel : ∀ p q : Prop, (q → p) → order.rel p q) : type_of% @propext :=
  propextOfReverseImplicationOrder order.toPartialOrder rel

/-- Each witness needs only that the replacement admits all comparisons
of the original instance. The inventory constructs this premise from the
pinned instance's actual projection. -/
def implicationOrders : List (Name × Name) := [
  (``ImplicationOrder.instOrder, ``propextOfImplicationOrder),
  (``ReverseImplicationOrder.instOrder, ``propextOfReverseImplicationOrder),
  (``ImplicationOrder.instCompleteLattice, ``propextOfImplicationLattice),
  (``ReverseImplicationOrder.instCompleteLattice, ``propextOfReverseImplicationLattice)]

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

/-- A choice function for all inhabited subsingletons in the selected universe. -/
abbrev MereUniqueChoice := Nonempty UniqueChoice.{u}

private structure PointedSubsingleton where
  carrier : Sort u
  uniq : Subsingleton carrier
  inh : Nonempty carrier

private theorem selectionOfSection (h : Nonempty ((i : PointedSubsingleton.{u}) → i.carrier)) :
    MereUniqueChoice.{u} :=
  h.elim fun f => ⟨fun {α} inst ne => f ⟨α, inst, ne⟩⟩

theorem uniqueSelectionOfCompletePi (order : type_of% @Lean.Order.instCompleteLatticePi.{u+1,u}) :
    MereUniqueChoice.{u} := by
  let carriers (i : PointedSubsingleton.{u}) : CompleteLattice i.carrier :=
    @singletonLattice _ i.uniq i.inh
  obtain ⟨s, _⟩ := (@order PointedSubsingleton.{u} (·.carrier) carriers).has_sup (fun _ => False)
  exact selectionOfSection ⟨s⟩

theorem uniqueSelectionOfChainCompletePi (order : type_of% @Lean.Order.instCCPOPi.{u+1,u}) :
    MereUniqueChoice.{u} := by
  let carriers (i : PointedSubsingleton.{u}) : CCPO i.carrier :=
    @singletonCCPO _ i.uniq i.inh
  let productOrder := @order PointedSubsingleton.{u} (·.carrier) carriers
  obtain ⟨s, _⟩ := @CCPO.has_csup _ productOrder _ (@chain_empty _ productOrder.toPartialOrder)
  exact selectionOfSection ⟨s⟩

def uniqueChoiceOfSup (select : type_of% @CompleteLattice.sup.{u}) : UniqueChoice.{u} :=
  fun {α} _ inh => @select α (singletonLattice α inh) (fun _ => False)

def uniqueChoiceOfChainSup (select : type_of% @CCPO.csup.{u}) : UniqueChoice.{u} := by
  intro α _ inh
  letI : CCPO α := singletonCCPO α inh
  exact select (chain_empty α)

/-- Least upper bounds form a subsingleton by antisymmetry. An existence proof
therefore suffices for the selector on subsingletons. -/
private def selectSupremum (pick : UniqueChoice.{max 1 u}) {α : Sort u} [PartialOrder α]
    (c : α → Prop) (h : ∃ s, is_sup c s) : {s : α // is_sup c s} := by
  letI : Subsingleton {s : α // is_sup c s} :=
    ⟨fun a b => Subtype.ext (is_sup_unique a.property b.property)⟩
  exact @pick _ _ (h.elim fun s hs => ⟨⟨s, hs⟩⟩)

def latticeSupOfUniqueChoice (pick : UniqueChoice.{max 1 u}) : type_of% @CompleteLattice.sup.{u} :=
  fun {_} inst c => (selectSupremum (@pick) c (inst.has_sup c)).val

theorem latticeSupOfUniqueChoice_spec (pick : UniqueChoice.{max 1 u}) {α : Sort u} [order : CompleteLattice α]
    (c : α → Prop) : is_sup c (latticeSupOfUniqueChoice (@pick) c) :=
  (selectSupremum (@pick) c (order.has_sup c)).property

def chainSupOfUniqueChoice (pick : UniqueChoice.{max 1 u}) : type_of% @CCPO.csup.{u} :=
  fun {_} inst {c} hc => (selectSupremum (@pick) c (inst.has_csup hc)).val

theorem chainSupOfUniqueChoice_spec (pick : UniqueChoice.{max 1 u}) {α : Sort u} [order : CCPO α]
    {c : α → Prop} (hc : chain c) : is_sup c (chainSupOfUniqueChoice (@pick) hc) :=
  (selectSupremum (@pick) c (order.has_csup hc)).property

theorem latticeSupIffUniqueChoice :
    Nonempty (type_of% @CompleteLattice.sup.{u+1}) ↔ MereUniqueChoice.{u+1} :=
  ⟨fun h => h.elim fun sup => ⟨@uniqueChoiceOfSup (@sup)⟩,
   fun h => h.elim fun pick => ⟨@latticeSupOfUniqueChoice (@pick)⟩⟩

theorem chainSupIffUniqueChoice :
    Nonempty (type_of% @CCPO.csup.{u+1}) ↔ MereUniqueChoice.{u+1} :=
  ⟨fun h => h.elim fun sup => ⟨@uniqueChoiceOfChainSup (@sup)⟩,
   fun h => h.elim fun pick => ⟨@chainSupOfUniqueChoice (@pick)⟩⟩

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

/-- Expand the pointwise chain relation in the type of the selected supremum. -/
abbrev FunctionChainSup (α : Sort u) (β : α → Sort v) [∀ x, CCPO (β x)]
    (c : (∀ x, β x) → Prop) :=
  (∀ f g, c f → c g → (∀ x, f x ⊑ g x) ∨ (∀ x, g x ⊑ f x)) → (x : α) → β x

example : (∀ {α : Sort u} {β : α → Sort v} [∀ x, CCPO (β x)] (c), FunctionChainSup α β c)
    = (type_of% @fun_csup.{u,v}) := rfl

def uniqueChoiceOfFunCSup (select : ∀ {ι : Type} {β : ι → Sort u} [∀ x, CCPO (β x)] (c),
    FunctionChainSup ι β c) : UniqueChoice.{u} :=
  fun {α} _ inh => @select Unit (fun _ => α) (fun _ => singletonCCPO α inh)
    (fun _ => False) (fun _ _ denied => denied.elim) ()

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

/-- The index selecting the bottom point disappears when the flat carrier unfolds. -/
abbrev StateOutput := ∀ {α σ : Type} [Nonempty α], Void σ → ST.Out σ α

example : StateOutput = (type_of% @Lean.Order.ST.bot') := rfl

theorem familyChoiceOfSTBottom (bot : StateOutput) : FamilyChoice.{u} :=
  fun {_} {β} inh => (Void.instNonempty (σ := Unit)).elim fun token =>
    ⟨fun x => (@bot (β x) Unit (inh x) token).val⟩

theorem familyChoiceOfStateBottom (bot : type_of% @Lean.Order.EST.bot) : FamilyChoice.{u} :=
  fun {_} {β} inh =>
    (Void.instNonempty (σ := Unit)).elim fun token => ⟨fun x =>
      match @bot (β x) Unit Empty (inh x) token with
      | .ok impossible _ => impossible.elim
      | .error element _ => element⟩

end InternalOrder

namespace RangeSize

open Std Std.PRange

/-- A one-element enumeration in which the only element has no successor. -/
@[instance_reducible] private def terminal : UpwardEnumerable Unit where
  succ? _ := none

/-- A dense comparison on the one-element range has size one. Positivity recovers the comparison. -/
theorem emOfClosed (sizeLaw : type_of% @Rxc.size_pos_iff_le.{0}) (p : Prop) : p ∨ ¬p := by
  letI := terminal
  letI : LE Unit := ⟨fun _ _ => p ∨ ¬p⟩
  letI : Rxc.HasSize Unit := ⟨fun _ _ => 1⟩
  letI : Rxc.LawfulHasSize Unit := {
    size_eq_zero_of_not_le := fun _ _ neither => (neither (.inr fun hp => neither (.inl hp))).elim
    size_eq_one_of_succ?_eq_none := fun _ _ _ _ => rfl
    size_eq_succ_of_succ?_eq_some := fun _ _ _ _ eq => nomatch eq
  }
  exact (sizeLaw (lo := ()) (hi := ())).mp (Nat.zero_lt_succ 0)

theorem emOfOpen (sizeLaw : type_of% @Rxo.size_pos_iff_lt.{0}) (p : Prop) : p ∨ ¬p := by
  letI := terminal
  letI : LT Unit := ⟨fun _ _ => p ∨ ¬p⟩
  letI : Rxo.HasSize Unit := ⟨fun _ _ => 1⟩
  letI : Rxo.LawfulHasSize Unit := {
    size_eq_zero_of_not_le := fun _ _ neither => (neither (.inr fun hp => neither (.inl hp))).elim
    size_eq_one_of_succ?_eq_none := fun _ _ _ _ => rfl
    size_eq_succ_of_succ?_eq_some := fun _ _ _ _ eq => nomatch eq
  }
  exact (sizeLaw (lo := ()) (hi := ())).mp (Nat.zero_lt_succ 0)

private theorem positive {p : Prop} {n : Nat} (em : ∀ r : Prop, r ∨ ¬r)
    (empty : ¬p → n = 0) (nonempty : p → n ≠ 0) : 0 < n ↔ p :=
  ⟨fun pos => (em p).elim id fun no => (Nat.ne_of_gt pos (empty no)).elim,
   fun yes => Nat.pos_of_ne_zero (nonempty yes)⟩

theorem closedOfEM (em : ∀ p : Prop, p ∨ ¬p) : type_of% @Rxc.size_pos_iff_le.{u} := by
  intro α _ _ _ _ lo hi
  apply positive em (Rxc.size_eq_zero_of_not_le lo hi)
  intro h
  cases s : UpwardEnumerable.succ? lo with
  | none =>
    rw [Rxc.size_eq_one_of_succ?_eq_none lo hi h s]
    exact fun eq => nomatch eq
  | some k =>
    rw [Rxc.size_eq_succ_of_succ?_eq_some lo hi k h s]
    exact fun eq => nomatch eq

theorem openOfEM (em : ∀ p : Prop, p ∨ ¬p) : type_of% @Rxo.size_pos_iff_lt.{u} := by
  intro α _ _ _ _ lo hi
  apply positive em (Rxo.size_eq_zero_of_not_le lo hi)
  intro h
  cases s : UpwardEnumerable.succ? lo with
  | none =>
    rw [Rxo.size_eq_one_of_succ?_eq_none lo hi h s]
    exact fun eq => nomatch eq
  | some k =>
    rw [Rxo.size_eq_succ_of_succ?_eq_some lo hi k h s]
    exact fun eq => nomatch eq

end RangeSize

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

end OmegaChecks.InitBoundaries
