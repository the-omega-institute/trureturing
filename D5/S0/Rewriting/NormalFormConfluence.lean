/- GID: D5/S0/Rewriting/NormalFormConfluence
   generality: G
   mirror-B: Blueprint/D5/S0/Rewriting/NormalFormConfluence.scribe.cs
   mirror-E: none(waiver:no-numeric-experiment-declared)
   anchors: []
   digest: Confluence makes reachable or equivalent normal forms unique. -/

import Mathlib

namespace NormalFormConfluence

/-- An element is a normal form when no rewrite step leaves it. -/
def IsNormalForm {α : Type*} (r : α → α → Prop) (a : α) : Prop :=
  ∀ b, ¬r a b

private theorem eq_of_reflTransGen_of_normal {α : Type*} {r : α → α → Prop} {a b : α}
    (hab : Relation.ReflTransGen r a b) (ha : IsNormalForm r a) : a = b := by
  exact ((Relation.reflTransGen_iff_eq ha).mp hab).symm

/-- Two normal forms reached from a common source in a confluent relation are equal. -/
theorem normal_form_unique_of_confluent {α : Type*} {r : α → α → Prop} {a n1 n2 : α}
    (confluent : ∀ h a b, Relation.ReflTransGen r h a → Relation.ReflTransGen r h b →
      ∃ c, Relation.ReflTransGen r a c ∧ Relation.ReflTransGen r b c)
    (han1 : Relation.ReflTransGen r a n1) (han2 : Relation.ReflTransGen r a n2)
    (hn1 : IsNormalForm r n1) (hn2 : IsNormalForm r n2) : n1 = n2 := by
  obtain ⟨c, hn1c, hn2c⟩ := confluent a n1 n2 han1 han2
  exact (eq_of_reflTransGen_of_normal hn1c hn1).trans
    (eq_of_reflTransGen_of_normal hn2c hn2).symm

private theorem eqvGen_joinable_of_confluent {α : Type*} {r : α → α → Prop}
    (confluent : ∀ h a b, Relation.ReflTransGen r h a → Relation.ReflTransGen r h b →
      ∃ c, Relation.ReflTransGen r a c ∧ Relation.ReflTransGen r b c) :
    ∀ {x y}, Relation.EqvGen r x y →
      ∃ c, Relation.ReflTransGen r x c ∧ Relation.ReflTransGen r y c := by
  intro x y hxy
  induction hxy with
  | rel x y hxy =>
      exact ⟨y, Relation.ReflTransGen.single hxy, Relation.ReflTransGen.refl⟩
  | refl x =>
      exact ⟨x, Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩
  | symm x y _ ih =>
      obtain ⟨c, hxc, hyc⟩ := ih
      exact ⟨c, hyc, hxc⟩
  | trans x y z _ _ ihxy ihyz =>
      obtain ⟨c, hxc, hyc⟩ := ihxy
      obtain ⟨d, hyd, hzd⟩ := ihyz
      obtain ⟨e, hce, hde⟩ := confluent y c d hyc hyd
      exact ⟨e, hxc.trans hce, hzd.trans hde⟩

/-- Equivalent normal forms in a confluent relation are equal. -/
theorem eqvGen_normal_form_eq {α : Type*} {r : α → α → Prop} {n1 n2 : α}
    (confluent : ∀ h a b, Relation.ReflTransGen r h a → Relation.ReflTransGen r h b →
      ∃ c, Relation.ReflTransGen r a c ∧ Relation.ReflTransGen r b c)
    (hn12 : Relation.EqvGen r n1 n2) (hn1 : IsNormalForm r n1)
    (hn2 : IsNormalForm r n2) : n1 = n2 := by
  obtain ⟨c, hn1c, hn2c⟩ := eqvGen_joinable_of_confluent confluent hn12
  exact (eq_of_reflTransGen_of_normal hn1c hn1).trans
    (eq_of_reflTransGen_of_normal hn2c hn2).symm

example (n1 n2 : Fin 2) (h : Relation.EqvGen (fun _ _ : Fin 2 => False) n1 n2) :
    n1 = n2 := by
  refine eqvGen_normal_form_eq (r := fun _ _ : Fin 2 => False) (hn12 := h) ?_ ?_ ?_
  · intro source left right hleft hright
    have hleftEq : left = source :=
      (Relation.reflTransGen_iff_eq (fun _ hFalse => hFalse)).mp hleft
    have hrightEq : right = source :=
      (Relation.reflTransGen_iff_eq (fun _ hFalse => hFalse)).mp hright
    subst left
    subst right
    exact ⟨source, Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩
  · intro _ hFalse
    exact hFalse
  · intro _ hFalse
    exact hFalse

end NormalFormConfluence
