module
public import Lean
import all Init.Data.Order.Lemmas
import all Init.Grind.Ordered.Order
import all Init.Data.Order.LemmasExtra
public import OmegaChecks.InitInventory.Logic
import all OmegaChecks.InitInventory.Logic
import all OmegaChecks.InitInventory.FiniteCollectionLogic

public section

open Lean
namespace OmegaChecks.InitBoundaries
universe u v w z

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

theorem stableEqualityOfHeadLE (law : type_of% @List.left_le_left_of_cons_le_cons.{u}) : StableEquality.{u} := by
  intro α a b nn
  letI := orderEndpoints a b
  letI := strictEndpoints a b
  letI := endpointsLinear a b
  letI := endpointsLT a b
  apply eqOfReverse
  apply law (l₁ := []) (l₂ := [])
  intro h
  exact nn fun eq => (singletonReverse h).2 (Or.inl eq.symm)

/-- The two negations give a weak case split even when equality is undecided. -/
def WeakEqualityCases : Prop := ∀ {α : Type u} (a b : α), a ≠ b ∨ ¬¬a = b

theorem weakEqualityOfLexTotal (law : type_of% @List.not_lex_total.{u}) : WeakEqualityCases.{u} := by
  intro α a b
  letI := orderEndpoints a b
  letI := strictEndpoints a b
  let x := leftEnd a b
  let y := rightEnd a b
  have total (v w : Endpoints a b) : ¬ v < w ∨ ¬ w < v :=
    ((endpointsLinear a b).le_total v w).elim
      (fun le => Or.inr fun gt => gt.2 le) (fun ge => Or.inl fun lt => lt.2 ge)
  rcases law total [y] [x,x] with denied | denied
  · exact Or.inl fun eq => denied ((Subtype.ext eq : x = y) ▸ List.Lex.cons (a := x) List.Lex.nil)
  · exact Or.inr fun ne => denied (List.Lex.rel ⟨endpointsForward a b, fun g => ne (eqOfReverse g)⟩)

private theorem optionLinear {T : Type u} [LE T] [o : IsLinearOrder T] : IsLinearOrder (Option T) where
  le_refl v := by cases v with | none => trivial | some t => exact o.le_refl t
  le_trans v w z vw wz := by
    cases v <;> cases w <;> cases z <;> first | exact trivial | exact False.elim vw | exact False.elim wz | exact o.le_trans _ _ _ vw wz
  le_total v w := by
    cases v <;> cases w <;> first | exact Or.inl trivial | exact Or.inr trivial | exact o.le_total _ _
  le_antisymm v w vw wv := by
    cases v <;> cases w <;> first | rfl | exact False.elim vw | exact False.elim wv | exact congrArg some (o.le_antisymm _ _ vw wv)

private theorem optionStrict {T : Type u} [LE T] [LT T] [o : LawfulOrderLT T] : LawfulOrderLT (Option T) where
  lt_iff v w := by
    cases v <;> cases w
    · exact ⟨False.elim, fun h => h.2 trivial⟩
    · exact ⟨fun _ => ⟨trivial, id⟩, fun _ => trivial⟩
    · exact ⟨False.elim, And.left⟩
    · exact o.lt_iff _ _

private theorem twoHeads {T : Type u} [LT T] {v w : T} {s t : List T} (h : v::s < w::t) :
    v < w ∨ v = w ∧ s < t := by
  cases h with
  | rel lt => exact Or.inl lt
  | cons tail => exact Or.inr ⟨rfl, tail⟩

theorem equalityCasesOfVectorComparison (law : type_of% @Vector.lt_of_le_of_lt.{u}) :
    FiniteMembership.EqualityCases.{u} := by
  intro α a b
  letI := orderEndpoints a b
  letI := strictEndpoints a b
  letI := endpointsLinear a b
  letI := endpointsLT a b
  letI := optionStrict (T := Endpoints a b)
  letI := optionLinear (T := Endpoints a b)
  let x := leftEnd a b
  let y := rightEnd a b
  let xs : Vector (Option (Endpoints a b)) 2 := #v[some x, none]
  let ys : Vector (Option (Endpoints a b)) 2 := #v[some y, none]
  let zs : Vector (Option (Endpoints a b)) 2 := #v[some y, some x]
  have le : xs ≤ ys := by
    intro back
    rcases twoHeads (show [some y, none] < [some x, none] from back) with lt | ⟨_, tail⟩
    · exact lt.2 (endpointsForward a b)
    · exact singletonReverse tail
  have strict : ys < zs := List.Lex.cons (List.Lex.rel (show (none : Option (Endpoints a b)) < some x from trivial))
  rcases twoHeads (show [some x, none] < [some y, some x] from law le strict) with lt | ⟨eq, _⟩
  · exact Or.inr fun eq => lt.2 (Or.inl eq.symm)
  · exact Or.inl (congrArg Subtype.val (Option.some.inj eq))

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

private theorem excludedMiddleOfSingletonStrict (law : ∀ q : Prop,
    letI : LT Bool := ⟨signed q⟩
    ([false] : List Bool) ≤ [true] ∧ ¬ ([true] : List Bool) ≤ [false] →
      ([false] : List Bool) < [true]) (p : Prop) : p ∨ ¬p := by
  apply excludedMiddleFromDNE _ p
  intro q nn
  letI : LT Bool := ⟨signed q⟩
  exact singletonReverse (law q ⟨singletonLe q nn,
    fun le => nn fun yes => le (List.Lex.rel yes)⟩)

private theorem signedListsAsymm (p : Prop) : Std.Asymm (List.Lex (signed p)) := by
  constructor
  intro xs ys h
  induction h with
  | nil => intro rev; cases rev
  | rel h =>
    intro rev
    cases rev with
    | rel k => exact (signedAsymm p).asymm _ _ h k
    | cons _ => exact (signedAsymm p).asymm _ _ h h
  | cons _ ih =>
    intro rev
    cases rev with
    | rel k => exact (signedAsymm p).asymm _ _ k k
    | cons k => exact ih k

theorem excludedMiddleOfListOrderLT (rule : type_of% @List.instLawfulOrderLTOfAsymmLt.{0}) :
    type_of% @Classical.em :=
  excludedMiddleOfSingletonStrict fun q => (@rule Bool ⟨signed q⟩ (signedListsAsymm q)).lt_iff [false] [true] |>.mpr

theorem excludedMiddleOfVectorOrderLT (rule : type_of% @Vector.instLawfulOrderLTOfAsymmLt.{0}) :
    type_of% @Classical.em :=
  excludedMiddleOfSingletonStrict fun q =>
    (@rule Bool 1 ⟨signed q⟩ (signedAsymm q)).lt_iff #v[false] #v[true] |>.mpr

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

end OmegaChecks.InitBoundaries
