module
public import Lean
import all Init.Internal.Order.Basic
import all Init.Internal.Order.MonadTail
import all Init.Data.Order.Lemmas
import all Init.Grind.Ordered.Order
import all Init.Data.Order.LemmasExtra
import Lean.Replay
import all Lean.Util.CollectAxioms
public import OmegaChecks.InitInventory.AbstractOrder
public import OmegaChecks.InitInventory.KripkeModels
public import OmegaChecks.InitInventory.Extensionality
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

/-- The law takes exactly the proposed equality operation as its instance. -/
@[expose] def BEqLaw (make : type_of% @Classical.Order.instBEq.{0}) : Prop :=
  ∀ {α : Type} [le : LE α], @Std.LawfulOrderBEq α (@make α le) le

example : BEqLaw (@Classical.Order.instBEq.{0}) := @Classical.Order.instLawfulOrderBEq.{0}

def fromLawfulBEq (make : type_of% @Classical.Order.instBEq.{0}) (law : BEqLaw (@make))
    (p : Prop) : Decidable p :=
  fromBEq (@make) (fun q =>
    ((@law Bool (testOrder q)).beq_iff_le_and_ge true false).trans
      ⟨And.left, fun h => ⟨h, h⟩⟩) p

/-- The forward comparison is arbitrary, while the reverse comparison makes the
relation total as required by the official ternary comparison law. -/
@[instance_reducible] private def totalTestOrder (p : Prop) : LE Bool where
  le a b := Bool.rec True (Bool.rec p True b) a

private theorem totalTestOrder_total (p : Prop) :
    @Std.Total Bool (@LE.le Bool (totalTestOrder p)) := by
  constructor
  intro a b
  cases a <;> cases b <;> first | exact Or.inl trivial | exact Or.inr trivial

/-- Only the first lawful comparison field is needed. Its Boolean projection is
abstracted so the witness also works with the port's implementation of `Ordering.isLE`. -/
@[expose] def OrdLELaw (isLE : Ordering → Bool) (make : type_of% @Classical.Order.instOrd.{0}) : Prop :=
  ∀ {α : Type} [le : LE α] [@Std.Total α (@LE.le α le)] (a b : α),
    isLE ((@make α le).compare a b) = true ↔ a ≤ b

example : OrdLELaw Ordering.isLE (@Classical.Order.instOrd.{0}) :=
  fun {α} le total => (@Classical.Order.instLawfulOrderOrd α le total).isLE_compare

def fromLawfulOrd (isLE : Ordering → Bool) (make : type_of% @Classical.Order.instOrd.{0})
    (law : OrdLELaw isLE (@make)) (p : Prop) : Decidable p :=
  decideWith _ (@law Bool (totalTestOrder p) (totalTestOrder_total p) true false)

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
  for name in [``fromMin, ``fromMax, ``fromBEq, ``fromOrd, ``fromLawfulBEq, ``fromLawfulOrd] do
    unless (← collectAxioms name).isEmpty do throwError "order observation uses axioms: {name}"

end ClassicalOrderDecisions

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
private theorem flatSupBottomOrMember (em : ∀ p : Prop, p ∨ ¬p) {α : Sort u} {b : α}
    (c : FlatOrder b → Prop) (ordered : chain c) :
    ∃ s, (s = b ∨ c s) ∧ is_sup c s := by
  cases em (∃ x, c x ∧ x ≠ b) with
  | inl existsNonbottom =>
    obtain ⟨s, member, above⟩ := existsNonbottom
    refine ⟨s, .inr member, fun x => ⟨?_, fun upper => upper s member⟩⟩
    intro sx y hy
    cases ordered y s hy member with
    | inl ys => exact PartialOrder.rel_trans ys sx
    | inr sy =>
      change FlatOrder.rel s y at sy
      cases sy with
      | bot => exact (above rfl).elim
      | refl => exact sx
  | inr allBottom =>
    refine ⟨b, .inl rfl, fun x => ⟨?_, fun _ => FlatOrder.rel.bot⟩⟩
    intro _ y hy
    cases em (y = b) with
    | inl same => cases same; exact FlatOrder.rel.bot
    | inr above => exact (allBottom ⟨y, hy, above⟩).elim

@[instance_reducible] def flatCCPOOfEM (em : ∀ p : Prop, p ∨ ¬p) :
    type_of% @FlatOrder.instCCPO.{u} := fun {α b} => {
  toPartialOrder := FlatOrder.instOrder
  has_csup := fun h => (@flatSupBottomOrMember em α b _ h).imp fun _ h => h.2 }

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

abbrev AtSup {α : Sort u} [PartialOrder α] (P : α → Prop) : Prop :=
  ∀ (c : α → Prop), chain c → (∀ x, c x → P x) → ∀ s, is_sup c s → P s

abbrev BinaryUpperBounds (α : Sort u) [PartialOrder α] :=
  ∀ (c : α → Prop) (s a b : α), chain c → is_sup c s →
    (∀ x, c x → x ⊑ a ∨ x ⊑ b) → s ⊑ a ∨ s ⊑ b

private theorem principal {α : Sort u} [PartialOrder α] (a : α) : AtSup (fun x => x ⊑ a) :=
  fun _ _ h _ hs => (hs a).2 h

/-- A disjunction of admissible predicates is admissible for all predicates exactly
when the union of any two principal lower sets contains the suprema of its chains. -/
theorem orIffUpperBounds {α : Sort u} [order : CCPO α] :
    (∀ (P Q : α → Prop), AtSup P → AtSup Q → AtSup (fun x => P x ∨ Q x)) ↔ BinaryUpperBounds α := by
  constructor
  · intro close c s a b hc hs cover
    exact close _ _ (principal a) (principal b) c hc cover s hs
  · intro bounds P Q hP hQ c hc together s hs
    obtain ⟨a, ha⟩ := order.has_csup (chain_conj c P hc)
    obtain ⟨b, hb⟩ := order.has_csup (chain_conj c Q hc)
    have inSup := (hs s).mp PartialOrder.rel_refl
    have left := hP _ (chain_conj c P hc) (fun _ h => h.2) a ha
    have right := hQ _ (chain_conj c Q hc) (fun _ h => h.2) b hb
    have cover (x : α) (hx : c x) : x ⊑ a ∨ x ⊑ b := by
      cases together x hx with
      | inl px => exact Or.inl ((ha a).mp PartialOrder.rel_refl x ⟨hx, px⟩)
      | inr qx => exact Or.inr ((hb b).mp PartialOrder.rel_refl x ⟨hx, qx⟩)
    cases bounds c s a b hc hs cover with
    | inl le =>
      have eq := PartialOrder.rel_antisymm le ((ha s).mpr (fun x hx => inSup x hx.1))
      exact .inl (eq.symm ▸ left)
    | inr le =>
      have eq := PartialOrder.rel_antisymm le ((hb s).mpr (fun x hx => inSup x hx.1))
      exact .inr (eq.symm ▸ right)

/-- Proposition extensionality makes pairs of propositions a complete partial order
under componentwise implication. A supremum records the two existential projections. -/
@[instance_reducible] private def propositionPairs (ext : type_of% @propext) : CCPO (Prop × Prop) where
  rel a b := (a.1 → b.1) ∧ (a.2 → b.2)
  rel_refl := ⟨id, id⟩
  rel_trans h k := ⟨fun a => k.1 (h.1 a), fun a => k.2 (h.2 a)⟩
  rel_antisymm h k := Prod.ext (ext ⟨h.1, k.1⟩) (ext ⟨h.2, k.2⟩)
  has_csup := by
    intro c _
    refine ⟨(∃ a, c a ∧ a.1, ∃ a, c a ∧ a.2), fun b => ⟨?_, ?_⟩⟩
    · intro h a ha
      exact ⟨fun x => h.1 ⟨a, ha, x⟩, fun x => h.2 ⟨a, ha, x⟩⟩
    · intro upper
      exact ⟨fun ⟨a, ha, x⟩ => (upper a ha).1 x, fun ⟨a, ha, x⟩ => (upper a ha).2 x⟩

abbrev OrClosure := ∀ {α : Sort u} [CCPO α] (P Q : α → Prop),
  AtSup P → AtSup Q → AtSup (fun x => P x ∨ Q x)

/-- The two conditional axes indexed by p and ¬p form a chain. Its supremum is
(p, ¬p). Covering it with one of the two principal ideals gives weak excluded middle. -/
theorem weakExcludedMiddleOfOr (law : OrClosure.{1}) (ext : type_of% @propext)
    (p : Prop) : ¬p ∨ ¬¬p := by
  letI : CCPO (Prop × Prop) := propositionPairs ext
  let a : Prop × Prop := (True, False)
  let b : Prop × Prop := (False, True)
  let c (x : Prop × Prop) := (x = a ∧ p) ∨ (x = b ∧ ¬p)
  have hc : chain c := by
    intro x y hx hy
    rcases hx with ⟨rfl, hp⟩ | ⟨rfl, np⟩ <;> rcases hy with ⟨rfl, hq⟩ | ⟨rfl, nq⟩
    · exact Or.inl PartialOrder.rel_refl
    · exact (nq hp).elim
    · exact (np hq).elim
    · exact Or.inl PartialOrder.rel_refl
  have hs : is_sup c (p, ¬p) := by
    intro y
    constructor
    · rintro ⟨l, r⟩ x (⟨rfl, hp⟩ | ⟨rfl, np⟩)
      · exact ⟨fun _ => l hp, False.elim⟩
      · exact ⟨False.elim, fun _ => r np⟩
    · intro upper
      exact ⟨fun hp => (upper a (.inl ⟨rfl, hp⟩)).1 trivial,
        fun np => (upper b (.inr ⟨rfl, np⟩)).2 trivial⟩
  have cover : ∀ x, c x → x ⊑ a ∨ x ⊑ b := by
    rintro _ (⟨rfl, _⟩ | ⟨rfl, _⟩)
    · exact .inl PartialOrder.rel_refl
    · exact .inr PartialOrder.rel_refl
  have bound := orIffUpperBounds.mp (law (α := Prop × Prop)) c _ a b hc hs cover
  exact bound.elim (fun h => .inr h.2) (fun h => .inl h.1)

private theorem conditionalSup {α : Type u} [PartialOrder α] {z : α}
    (stable : ∀ y, ¬¬(z ⊑ y) → z ⊑ y)
    (p : Prop) (nn : ¬¬p) : is_sup (fun b => b = z ∧ p) z :=
  fun y => ⟨fun le _ ⟨rfl, _⟩ => le, fun upper => stable y fun no => nn fun hp => no (upper z ⟨rfl, hp⟩)⟩

private theorem conditionalChain {α : Type u} [PartialOrder α] (z : α) (p : Prop) :
    chain (fun b => b = z ∧ p) := by
  rintro _ _ ⟨rfl, _⟩ ⟨rfl, _⟩
  exact Or.inl PartialOrder.rel_refl

private theorem someUnitStable (y : Option Unit) : ¬¬(some () ⊑ y) → some () ⊑ y := by
  cases y with
  | some u => exact fun _ => PartialOrder.rel_refl
  | none => intro nn; exact False.elim (nn (fun h => nomatch h))

private theorem decisionOfOption (law : ∀ (P : Prop), AtSup (fun x : Option Unit => x = some () → P))
    (p : Prop) : p ∨ ¬p := by
  let d := p ∨ ¬p
  have nn : ¬¬d := fun no => no (.inr (fun hp => no (.inl hp)))
  exact law d _ (conditionalChain (some ()) d) (fun _ h _ => h.2) _ (conditionalSup someUnitStable d nn) rfl

/-- These statements use the pinned partial orders after unfolding strict admissibility. -/
abbrev FlatClosure := ∀ {α : Sort u} {b : α} (P : FlatOrder b → Prop), P b → AtSup P
abbrev OptionClosure := ∀ {α : Type u} (P : Prop) (y : α), AtSup (fun x : Option α => x = some y → P)

theorem excludedMiddleOfFlat (law : FlatClosure.{1}) (p : Prop) : p ∨ ¬p :=
  decisionOfOption (fun P => @law (Option Unit) none (fun x => x = some () → P) (fun h => nomatch h)) p

theorem excludedMiddleOfSome (law : OptionClosure.{0}) (p : Prop) : p ∨ ¬p :=
  decisionOfOption (fun P => law P ()) p

private theorem flatOfEM (em : ∀ p : Prop, p ∨ ¬p) : FlatClosure.{u} := by
  intro α b P bottom c ordered all s hs
  obtain ⟨z, hz, least⟩ := flatSupBottomOrMember em c ordered
  cases is_sup_unique hs least
  exact hz.elim (fun eq => eq.symm ▸ bottom) (all s)

theorem flatAdmissibleIffEM : FlatClosure.{1} ↔ (∀ p : Prop, p ∨ ¬p) := ⟨excludedMiddleOfFlat, flatOfEM⟩
theorem someAdmissibleIffEM : OptionClosure.{0} ↔ (∀ p : Prop, p ∨ ¬p) :=
  ⟨excludedMiddleOfSome, fun em {α} P y => @flatOfEM em (Option α) none (fun x => x = some y → P) (fun h => nomatch h)⟩

run_cmd
  for name in [``orIffUpperBounds, ``weakExcludedMiddleOfOr, ``flatAdmissibleIffEM, ``someAdmissibleIffEM] do
    unless (← collectAxioms name).isEmpty do throwError "admissibility reduction uses axioms: {name}"

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

/-- Equality as an order exposes the relation computed by the transformer on endomorphisms. -/
@[instance_reducible] private def equalityOrder (T : Type w) : PartialOrder T :=
  ⟨Eq, rfl, Eq.trans, fun h _ => h⟩

def ReaderPointwise (order : type_of% @instPartialOrderReaderT.{w,w}) : Prop :=
  ∀ {T : Type w} (f g : T → T), (∀ t, f t = g t) → (@order Id T T (equalityOrder T)).rel f g

example : ReaderPointwise @instPartialOrderReaderT.{w,w} := fun _ _ h => h

theorem funextOfReaderOrder (order : type_of% @instPartialOrderReaderT.{max 1 u v,max 1 u v})
    (pointwise : ReaderPointwise order) : type_of% @funext.{u,v} := by
  apply funextFromEndomorphisms
  intro T f g h
  exact (@order Id T T (equalityOrder T)).rel_antisymm (pointwise f g h)
    (pointwise g f fun t => (h t).symm)

def StatePointwise (order : type_of% @instPartialOrderStateT.{w,w}) : Prop :=
  ∀ {T : Type w} (f g : T → T), (∀ t, f t = g t) →
    (@order (fun _ => T) T T (fun _ => equalityOrder T)).rel f g

example : StatePointwise @instPartialOrderStateT.{w,w} := fun _ _ h => h

theorem funextOfStateOrder (order : type_of% @instPartialOrderStateT.{max 1 u v,max 1 u v})
    (pointwise : StatePointwise order) : type_of% @funext.{u,v} := by
  apply funextFromEndomorphisms
  intro T f g h
  exact (@order (fun _ => T) T T (fun _ => equalityOrder T)).rel_antisymm (pointwise f g h)
    (pointwise g f fun t => (h t).symm)

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

namespace FlatSelection

/-- A pointed flat chain of optional values selects the unique inhabitant without
requiring a supremum law on the predicates that are not chains. -/
private def selectSubsingleton (pick : type_of% @flat_csup.{u+1})
    (valid : ∀ {α : Type u} (c : Option α → Prop), chain c → is_sup c (@pick (Option α) none c))
    {β : Type u} [Subsingleton β] (h : Nonempty β) : β := by
  let c : Option β → Prop := fun x => ∃ b, x = some b
  have ordered : chain c := by
    rintro _ _ ⟨b, rfl⟩ ⟨d, rfl⟩
    cases Subsingleton.elim b d
    exact Or.inl PartialOrder.rel_refl
  let top := @pick (Option β) none c
  have hup := valid c ordered
  cases ht : top.inner with
  | some b => exact b
  | none =>
    exact False.elim <| h.elim fun b => by
      have eq : top = (none : Option β) := ht
      rw [show @pick (Option β) none c = (none : Option β) from eq] at hup
      have rel := (hup none).mp PartialOrder.rel_refl (some b) ⟨b, rfl⟩
      change FlatOrder.rel (b := (none : Option β)) (some b) none at rel
      cases rel

private def decideProp (pick : type_of% @flat_csup.{1})
    (valid : ∀ {α : Type} (c : Option α → Prop), chain c → is_sup c (@pick (Option α) none c))
    (P : Prop) : Decidable P := by
  apply selectSubsingleton (@pick) valid
  cases excludedMiddleOfFlatCSup (@pick) valid P with
  | inl h => exact ⟨.isTrue h⟩
  | inr h => exact ⟨.isFalse h⟩

private theorem eqOfNonbottom {α : Type u} {b : α} {x y : FlatOrder b} (h : x ⊑ y)
    (hx : x ≠ b) : x = y := by
  cases h with
  | bot => exact (hx rfl).elim
  | refl => rfl

private def chooseSup (D : ∀ P : Prop, Decidable P) (choose : UniqueChoice.{u+1})
    {α : Type u} {b : α} (c : FlatOrder b → Prop) (hc : chain c) :
    {top : FlatOrder b // is_sup c top} := by
  let bottom := FlatOrder.mk b b
  cases D (∃ x, c x ∧ x ≠ bottom) with
  | isTrue h =>
    letI : Subsingleton {x // c x ∧ x ≠ bottom} := ⟨fun x y => by
      apply Subtype.ext
      cases hc x y x.property.1 y.property.1 with
      | inl le => exact eqOfNonbottom le x.property.2
      | inr le => exact (eqOfNonbottom le y.property.2).symm⟩
    let top := choose (α := {x // c x ∧ x ≠ bottom}) (h.elim fun x hx => ⟨⟨x, hx⟩⟩)
    refine ⟨top.val, fun x => ⟨?_, fun h => h top.val top.property.1⟩⟩
    intro hle y hy
    cases hc y top hy top.property.1 with
    | inl le => exact PartialOrder.rel_trans le hle
    | inr le => exact (eqOfNonbottom le top.property.2) ▸ hle
  | isFalse hn =>
    refine ⟨bottom, fun x => ⟨?_, fun _ => FlatOrder.rel.bot⟩⟩
    intro _ y hy
    cases D (y = bottom) with
    | isTrue e => cases e; exact FlatOrder.rel.bot
    | isFalse ne => exact (hn ⟨y, hy, ne⟩).elim

abbrev ChainLaw (pick : type_of% @flat_csup.{u+1}) : Prop :=
  ∀ {α : Type u} {b : α} (c : FlatOrder b → Prop) (_ : chain c), is_sup c (@pick α b c)

private def picker (D : ∀ P : Prop, Decidable P) (choose : UniqueChoice.{u+1}) : type_of% @flat_csup.{u+1} :=
  fun {_ b} c => match D (chain c) with
  | .isTrue hc => (chooseSup D (@choose) c hc).1
  | .isFalse _ => FlatOrder.mk b b

private theorem pickerLaw (D : ∀ P : Prop, Decidable P) (choose : UniqueChoice.{u+1}) : ChainLaw (@picker D (@choose)) := by
  intro α b c hc
  unfold picker
  cases h : D (chain c) with
  | isTrue yes => exact (chooseSup D (@choose) c yes).property
  | isFalse no => exact (no hc).elim

/-- Choosing suprema on the chains of small flat orders is equivalent to having
a proposition decider and a selector on inhabited subsingletons. -/
theorem smallChainSelections :
    (∃ pick : type_of% @flat_csup.{1}, ChainLaw (@pick)) ↔
      Nonempty (∀ P : Prop, Decidable P) ∧ Nonempty UniqueChoice.{1} := by
  constructor
  · rintro ⟨pick, law⟩
    have valid {α : Type} (c : Option α → Prop) (h : chain c) := law (b := (none : Option α)) c h
    exact ⟨⟨decideProp (@pick) (@valid)⟩, ⟨@selectSubsingleton (@pick) (@valid)⟩⟩
  · rintro ⟨⟨D⟩, ⟨choose⟩⟩
    exact ⟨@picker D (@choose), pickerLaw D (@choose)⟩

example : ChainLaw (@flat_csup.{1}) = type_of% @flat_csup_is_sup.{1} := rfl

end FlatSelection

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

end OmegaChecks.InitBoundaries
