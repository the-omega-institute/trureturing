module

public import OmegaChecks.InitInventory.Quotient
public import Init.WFComputable
public import Init.Data.Option.Basic
public import Init.Core
public import Init.Internal.Order.Basic
import all Init.Internal.Order.Basic

namespace OmegaChecks.Interface.Equations

public theorem Option.isNone {α : Type u} (x : _root_.Option α) :
    (!x.isSome) = x.isNone := by cases x <;> rfl

open _root_.Lean.Order in
public theorem Lean.Order.admissible {α : Sort u} [CCPO α] (P : α → Prop) :
    (∀ (c : α → Prop), chain c → (∀ x, c x → P x) → ∀ s, is_sup c s → P s) =
      _root_.Lean.Order.admissible P := by
  apply propext
  constructor
  · intro close c hc h
    exact close c hc h _ (CCPO.csup_spec hc)
  · intro close c hc h s hs
    exact is_sup_unique (CCPO.csup_spec hc) hs ▸ close c hc h

/-- The public conjunction interface represents standard conjunction. -/
public theorem And (a b : Prop) : (∀ r : Prop, (a → b → r) → r) = (a ∧ b) :=
  propext ⟨fun h => h _ _root_.And.intro, fun h _ use => use h.left h.right⟩

/-- The public disjunction interface represents standard disjunction. -/
public theorem Or (a b : Prop) : (∀ r : Prop, (a → r) → (b → r) → r) = (a ∨ b) :=
  propext ⟨fun h => h _ _root_.Or.inl _root_.Or.inr, fun h _ left right => h.elim left right⟩

public theorem Iff (a b : Prop) : ((a → b) ∧ (b → a)) = (a ↔ b) :=
  propext ⟨fun h => ⟨h.left, h.right⟩, fun h => ⟨h.mp, h.mpr⟩⟩

public theorem And.rec {a b : Prop} {motive : (a ∧ b) → Sort u}
    (intro : ∀ left right, motive ⟨left, right⟩) (t : a ∧ b) :
    intro t.left t.right = _root_.And.rec (motive := motive) intro t := by
  cases t
  rfl

public theorem Iff.rec {a b : Prop} {motive : (a ↔ b) → Sort u}
    (intro : ∀ mp mpr, motive ⟨mp, mpr⟩) (t : a ↔ b) :
    intro t.mp t.mpr = _root_.Iff.rec (motive := motive) intro t := by
  cases t
  rfl

public theorem Exists {α : Sort u} (p : α → Prop) :
    (∀ r : Prop, (∀ w, p w → r) → r) = (∃ w, p w) :=
  propext ⟨fun h => h _ _root_.Exists.intro, fun h _ use => h.elim use⟩

public theorem Nat.pred (a : Nat) :
    Nat.rec 0 (fun n _ => n) a = a.pred := by
  cases a <;> rfl

public theorem Nat.sub (a b : Nat) :
    Nat.rec a (fun _ r => _root_.Nat.pred r) b = a - b := by
  induction b with
  | zero => rfl
  | succ b ih =>
    change _root_.Nat.pred (Nat.rec (motive := fun _ => Nat) a (fun _ r => _root_.Nat.pred r) b) = a - b.succ
    rw [ih]
    exact (_root_.Nat.sub_succ a b).symm

public theorem Nat.mul (a b : Nat) :
    Nat.rec 0 (fun _ r => r + a) b = a * b := by
  induction b with
  | zero => rfl
  | succ b ih =>
    change Nat.rec 0 (fun _ r => r + a) b + a = a * b.succ
    rw [ih]
    exact (_root_.Nat.mul_succ a b).symm

/-- The strict elimination principle for nonemptiness characterizes the official proposition. -/
public theorem Nonempty (α : Sort u) : (∀ p : Prop, (α → p) → p) = _root_.Nonempty α :=
  propext ⟨fun h => h _ _root_.Nonempty.intro, fun h _ f => h.elim f⟩

public theorem Acc.recC.{v,u} {α : Sort u} {r : α → α → Prop} {motive : (a : α) → Acc r a → Sort v}
    (step : (x : α) → (h : ∀ y, r y x → Acc r y) →
      ((y : α) → (hr : r y x) → motive y (h y hr)) → motive x (.intro x h))
    {a : α} (t : Acc r a) :
    @_root_.Acc.rec α r motive step a t = @_root_.Acc.recC α r motive step a t :=
  congrArg (fun k => @k α r motive step a t) _root_.Acc.rec_eq_recC

public theorem Quot.hrecOn.{u,v} {α : Sort u} {r : α → α → Prop} {motive : Quot r → Sort v}
    (q : Quot r) (f : (a : α) → motive (Quot.mk r a))
    (c : (a b : α) → r a b → HEq (f a) (f b)) :
    OmegaChecks.InitPort.Alternatives.Quot.hrecOn q f c = _root_.Quot.hrecOn q f c :=
  OmegaChecks.InitBoundaries.HeterogeneousQuotient.agrees q f c

end OmegaChecks.Interface.Equations
