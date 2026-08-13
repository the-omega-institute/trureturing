/- GID: D5/S0/Rewriting/ChurchRosser
   generality: G
   mirror-B: D5/B/S0/Rewriting/ChurchRosser
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Logic.Relation]
   digest: Global confluence is equivalent to Church-Rosser convertibility-joinability. -/

import D5.S0.Rewriting.NewmanConfluence

namespace D5.S0.Rewriting.ChurchRosser

private theorem reflTransGen_to_eqvGen {α : Type*} {r : α → α → Prop}
    {a b : α} (h : Relation.ReflTransGen r a b) : Relation.EqvGen r a b := by
  induction h with
  | refl => exact .refl _
  | tail h hab ih => exact .trans _ _ _ ih (.rel _ _ hab)

/-- Confluence is exactly convertibility iff joinability. -/
theorem confluent_iff_church_rosser {α : Type*} (r : α → α → Prop) :
    (∀ h a b, Relation.ReflTransGen r h a → Relation.ReflTransGen r h b →
      ∃ c, Relation.ReflTransGen r a c ∧ Relation.ReflTransGen r b c) ↔
    (∀ a b, Relation.EqvGen r a b ↔ Relation.Join (Relation.ReflTransGen r) a b) := by
  constructor
  · intro hconf a b
    letI : Std.Refl (Relation.ReflTransGen r) := ⟨fun x => .refl⟩
    letI : IsTrans α (Relation.ReflTransGen r) := ⟨fun _ _ _ => .trans⟩
    let joinEquiv : Equivalence (Relation.Join (Relation.ReflTransGen r)) :=
      Relation.equivalence_join (fun x y z hxy hxz => hconf x y z hxy hxz)
    constructor
    · intro hab
      induction hab with
      | rel x y h =>
          obtain ⟨c, hbc, hac⟩ := hconf _ _ _ (.refl) (.single h)
          exact ⟨c, hbc, hac⟩
      | refl => exact ⟨_, .refl, .refl⟩
      | symm x y h ih => exact joinEquiv.symm ih
      | trans x y z h₁ h₂ ih₁ ih₂ => exact joinEquiv.trans ih₁ ih₂
    · intro hab
      obtain ⟨c, hac, hbc⟩ := hab
      exact .trans _ _ _ (reflTransGen_to_eqvGen hac) (reflTransGen_to_eqvGen hbc).symm
  · intro hcr h a b hac hab
    exact (hcr a b).mp (Relation.EqvGen.trans _ _ _
      (Relation.EqvGen.symm _ _ (reflTransGen_to_eqvGen hac))
      (reflTransGen_to_eqvGen hab))

/-- Newman confluence yields the Church-Rosser characterization under termination. -/
theorem newman_church_rosser {α : Type*} (r : α → α → Prop)
    (termination : WellFounded (Function.swap r))
    (localConfluence : ∀ h a b, r h a → r h b →
      ∃ c, Relation.ReflTransGen r a c ∧ Relation.ReflTransGen r b c) :
    ∀ a b, Relation.EqvGen r a b ↔ Relation.Join (Relation.ReflTransGen r) a b :=
  (confluent_iff_church_rosser r).mp
    (D5.S0.Rewriting.NewmanConfluence.newman_confluent r termination localConfluence)

/-- Mathlib's ReflGen/ReflTransGen diamond criterion is a sufficient confluence route. -/
theorem mathlib_church_rosser_confluent {α : Type*} {r : α → α → Prop}
    (h : ∀ a b c, r a b → r a c →
      ∃ d, Relation.ReflGen r b d ∧ Relation.ReflTransGen r c d) :
    ∀ a b c, Relation.ReflTransGen r a b → Relation.ReflTransGen r a c →
      ∃ d, Relation.ReflTransGen r b d ∧ Relation.ReflTransGen r c d := by
  intro a b c hab hac
  exact Relation.church_rosser h hab hac

private example :
    ∀ a b : Fin 3,
      Relation.EqvGen (fun _ _ : Fin 3 => True) a b ↔
        Relation.Join (Relation.ReflTransGen (fun _ _ : Fin 3 => True)) a b := by
  intro a b
  apply (confluent_iff_church_rosser (fun _ _ : Fin 3 => True)).mp
  intro h x y _ _
  exact ⟨x, .refl, .single trivial⟩

end D5.S0.Rewriting.ChurchRosser
