/- GID: D5/S0/Rewriting/HindleyRosen
   generality: G
   mirror-B: Blueprint/D5/S0/Rewriting/HindleyRosen.scribe.cs
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Logic.Relation]
   digest: Strongly commuting confluent relations have a confluent union. -/

import Mathlib
import D5.S0.Rewriting.ChurchRosser

namespace D5.S0.Rewriting.HindleyRosen

/-- Strong commutation lifts from one-step reductions to reflexive transitive closures. -/
theorem reflTransGen_commute_of_strong_commute {α : Type*} {r s : α → α → Prop}
    (strongCommute : ∀ h a b, r h a → s h b → ∃ c, s a c ∧ r b c) :
    ∀ h a b, Relation.ReflTransGen r h a → Relation.ReflTransGen s h b →
      ∃ c, Relation.ReflTransGen s a c ∧ Relation.ReflTransGen r b c := by
  have commuteSingle : ∀ h a b, Relation.ReflTransGen r h a → s h b →
      ∃ c, s a c ∧ Relation.ReflTransGen r b c := by
    intro h a b hra hsb
    induction hra with
    | refl => exact ⟨b, hsb, .refl⟩
    | tail hrd rda ih =>
        obtain ⟨e, hde, hbe⟩ := ih
        obtain ⟨c, hac, hec⟩ := strongCommute _ _ _ rda hde
        exact ⟨c, hac, hbe.tail hec⟩
  intro h a b hra hsb
  induction hsb with
  | refl => exact ⟨a, .refl, hra⟩
  | tail hsd sdb ih =>
      obtain ⟨e, hae, hde⟩ := ih
      obtain ⟨c, hec, hbc⟩ := commuteSingle _ _ _ hde sdb
      exact ⟨c, hae.tail hec, hbc⟩

/-- The Hindley-Rosen theorem: confluent strongly commuting relations have a confluent union. -/
theorem hindley_rosen_confluent {α : Type*} {r s : α → α → Prop}
    (rConfluent : ∀ h a b, Relation.ReflTransGen r h a → Relation.ReflTransGen r h b →
      ∃ c, Relation.ReflTransGen r a c ∧ Relation.ReflTransGen r b c)
    (sConfluent : ∀ h a b, Relation.ReflTransGen s h a → Relation.ReflTransGen s h b →
      ∃ c, Relation.ReflTransGen s a c ∧ Relation.ReflTransGen s b c)
    (strongCommute : ∀ h a b, r h a → s h b → ∃ c, s a c ∧ r b c) :
    ∀ h a b, Relation.ReflTransGen (fun a b => r a b ∨ s a b) h a →
      Relation.ReflTransGen (fun a b => r a b ∨ s a b) h b →
      ∃ c, Relation.ReflTransGen (fun a b => r a b ∨ s a b) a c ∧
        Relation.ReflTransGen (fun a b => r a b ∨ s a b) b c := by
  let t : α → α → Prop := fun a b =>
    Relation.ReflTransGen r a b ∨ Relation.ReflTransGen s a b
  have tLocal : ∀ h a b, t h a → t h b →
      ∃ c, Relation.ReflGen t a c ∧ Relation.ReflTransGen t b c := by
    intro h a b ha hb
    rcases ha with har | has <;> rcases hb with hbr | hbs
    · obtain ⟨c, hac, hbc⟩ := rConfluent _ _ _ har hbr
      exact ⟨c, .single (Or.inl hac), .single (Or.inl hbc)⟩
    · obtain ⟨c, hac, hbc⟩ :=
        reflTransGen_commute_of_strong_commute strongCommute _ _ _ har hbs
      exact ⟨c, .single (Or.inr hac), .single (Or.inl hbc)⟩
    · obtain ⟨c, hbc, hac⟩ :=
        reflTransGen_commute_of_strong_commute strongCommute _ _ _ hbr has
      exact ⟨c, .single (Or.inl hac), .single (Or.inr hbc)⟩
    · obtain ⟨c, hac, hbc⟩ := sConfluent _ _ _ has hbs
      exact ⟨c, .single (Or.inr hac), .single (Or.inr hbc)⟩
  have unionToT : ∀ {a b}, Relation.ReflTransGen (fun a b => r a b ∨ s a b) a b →
      Relation.ReflTransGen t a b := by
    intro a b hab
    exact hab.mono fun _ _ h => h.elim
      (fun hr => Or.inl (.single hr))
      (fun hs => Or.inr (.single hs))
  have tToUnion : ∀ {a b}, Relation.ReflTransGen t a b →
      Relation.ReflTransGen (fun a b => r a b ∨ s a b) a b := by
    intro a b hab
    induction hab with
    | refl => exact .refl
    | tail hab hbc ih =>
        apply ih.trans
        rcases hbc with hbc | hbc
        · exact hbc.mono fun _ _ hr => Or.inl hr
        · exact hbc.mono fun _ _ hs => Or.inr hs
  intro h a b ha hb
  obtain ⟨c, hac, hbc⟩ := Relation.church_rosser tLocal (unionToT ha) (unionToT hb)
  exact ⟨c, tToUnion hac, tToUnion hbc⟩

/-- Hindley-Rosen confluence yields the Church-Rosser characterization for the union. -/
theorem hindley_rosen_church_rosser {α : Type*} {r s : α → α → Prop}
    (rConfluent : ∀ h a b, Relation.ReflTransGen r h a → Relation.ReflTransGen r h b →
      ∃ c, Relation.ReflTransGen r a c ∧ Relation.ReflTransGen r b c)
    (sConfluent : ∀ h a b, Relation.ReflTransGen s h a → Relation.ReflTransGen s h b →
      ∃ c, Relation.ReflTransGen s a c ∧ Relation.ReflTransGen s b c)
    (strongCommute : ∀ h a b, r h a → s h b → ∃ c, s a c ∧ r b c) :
    ∀ a b, Relation.EqvGen (fun a b => r a b ∨ s a b) a b ↔
      Relation.Join (Relation.ReflTransGen (fun a b => r a b ∨ s a b)) a b :=
  (D5.S0.Rewriting.ChurchRosser.confluent_iff_church_rosser
    (fun a b => r a b ∨ s a b)).mp
      (hindley_rosen_confluent rConfluent sConfluent strongCommute)

private example :
    ∀ h a b : Fin 3,
      Relation.ReflTransGen (fun _ _ : Fin 3 => True ∨ True) h a →
      Relation.ReflTransGen (fun _ _ : Fin 3 => True ∨ True) h b →
      ∃ c, Relation.ReflTransGen (fun _ _ : Fin 3 => True ∨ True) a c ∧
        Relation.ReflTransGen (fun _ _ : Fin 3 => True ∨ True) b c := by
  apply hindley_rosen_confluent
      (r := fun _ _ : Fin 3 => True) (s := fun _ _ : Fin 3 => True)
  · intro h a b _ _
    exact ⟨a, .refl, .single trivial⟩
  · intro h a b _ _
    exact ⟨a, .refl, .single trivial⟩
  · intro h a b _ _
    exact ⟨a, trivial, trivial⟩

end D5.S0.Rewriting.HindleyRosen
