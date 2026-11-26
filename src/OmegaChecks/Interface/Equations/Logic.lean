module

public import Init.Core

namespace OmegaChecks.Interface.Equations

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

end OmegaChecks.Interface.Equations
