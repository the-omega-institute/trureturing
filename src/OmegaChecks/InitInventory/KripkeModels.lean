module
public import Lean

public section

namespace OmegaChecks.InitBoundaries

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

namespace ForkFrame

/-- The root is below both Boolean leaves, and each leaf reaches only itself. -/
def reaches (u v : Option Bool) : Prop := u = none ∨ u = v

def neg (p : Option Bool → Prop) (w : Option Bool) : Prop :=
  ∀ v, reaches w v → p v → False

/-- The atom holds at one leaf and its negation at the other. The root forces
neither its negation nor its double negation. -/
theorem countermodel :
    let p := fun w : Option Bool => w = some true
    (∀ w, reaches w w) ∧ (∀ u v w, reaches u v → reaches v w → reaches u w) ∧
    (∀ u v, reaches u v → p u → p v) ∧ ¬ (neg p none ∨ neg (neg p) none) := by
  let p := fun w : Option Bool => w = some true
  have no : neg p (some false) := fun v h hp => by
    rcases h with h | h
    · cases h
    · cases h; cases hp
  refine ⟨fun _ => Or.inr rfl, ?_, ?_, ?_⟩
  · intro u v w h k
    exact h.elim Or.inl fun e => e ▸ k
  · intro u v h hp
    rcases h with h | h
    · cases hp; cases h
    · exact h ▸ hp
  · exact fun h => h.elim (fun n => n (some true) (Or.inl rfl) rfl)
      (fun nn => nn (some false) (Or.inl rfl) no)

/-- Two sections of a varying set. Both names survive on the left branch and
the restriction to the right branch identifies them. -/
def restrictName (w : Option Bool) (name : Bool) : Bool :=
  w.elim name (fun leaf => bif leaf then false else name)

def equalAt (a b : Bool) (w : Option Bool) : Prop := restrictName w a = restrictName w b

private theorem equalityPersists {u v : Option Bool} (uv : reaches u v) (a b : Bool) :
    equalAt a b u → equalAt a b v := by
  rcases uv with h | h
  · cases h
    intro eq
    exact congrArg (restrictName v) eq
  · cases h
    exact id

/-- The two names are distinct at the root. At one leaf they coincide and at
the other their inequality persists. This refutes both strong and weak case
splitting for equality in this varying set. -/
theorem equalityCountermodel :
    (∀ u v, reaches u v → ∀ a b, equalAt a b u → equalAt a b v) ∧
    ¬ (equalAt false true none ∨ neg (equalAt false true) none) ∧
    ¬ (neg (equalAt false true) none ∨ neg (neg (equalAt false true)) none) := by
  let e := equalAt false true
  have distinct : ¬e none := fun eq => nomatch eq
  have identified : e (some true) := rfl
  have apart : neg e (some false) := by
    intro w h eq
    rcases h with h | h
    · cases h
    · cases h
      exact nomatch eq
  have nn : ¬neg e none := fun no => no (some true) (Or.inl rfl) identified
  exact ⟨fun _ _ => equalityPersists, fun h => h.elim distinct nn,
    fun h => h.elim nn (fun double => double (some false) (Or.inl rfl) apart)⟩

/-- The membership premise of the list case split holds at the root. Its right
disjunct also requires an inequality that remains valid at every later world. -/
theorem membershipCountermodel :
    restrictName none false ∈ [restrictName none true, restrictName none false] ∧
    ¬ (equalAt false true none ∨
      (neg (equalAt false true) none ∧ restrictName none false ∈ [restrictName none false])) := by
  exact ⟨.tail _ (.head _), fun h => equalityCountermodel.2.1 (h.imp_right And.left)⟩

end ForkFrame

end OmegaChecks.InitBoundaries
