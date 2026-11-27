module
public import Lean
import all Init.Internal.Order.Basic
import Lean.Replay
import all Lean.Util.CollectAxioms
public import OmegaChecks.InitInventory.Logic

public section

open Lean
namespace OmegaChecks.InitBoundaries
universe u v w z

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

end OmegaChecks.InitBoundaries
