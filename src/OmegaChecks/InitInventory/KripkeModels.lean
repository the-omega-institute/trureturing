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

end ForkFrame

end OmegaChecks.InitBoundaries
