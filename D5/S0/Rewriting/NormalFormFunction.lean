/- GID: D5/S0/Rewriting/NormalFormFunction
   generality: G
   mirror-B: D5/B/S0/Rewriting/NormalFormFunction
   mirror-E: none(waiver:no-numeric-experiment-declared)
   anchors: []
   digest: Terminating locally confluent rewrite systems admit a canonical normal-form function. -/

import D5.S0.Rewriting.ChurchRosser
import D5.S0.Rewriting.NormalFormConfluence

namespace NormalFormFunction

open D5.S0.Rewriting

/-- A chosen reachable normal form for a terminating locally confluent relation. -/
noncomputable def nf {α : Type*} (r : α → α → Prop)
    (termination : WellFounded (Function.swap r))
    (localConfluence : ∀ h a b, r h a → r h b →
      ∃ c, Relation.ReflTransGen r a c ∧ Relation.ReflTransGen r b c)
    (a : α) : α :=
  Classical.choose (newman_unique_normal_form r termination localConfluence a)

/-- The chosen normal form is reachable and irreducible. -/
theorem nf_spec {α : Type*} (r : α → α → Prop)
    (termination : WellFounded (Function.swap r))
    (localConfluence : ∀ h a b, r h a → r h b →
      ∃ c, Relation.ReflTransGen r a c ∧ Relation.ReflTransGen r b c)
    (a : α) :
    Relation.ReflTransGen r a (nf r termination localConfluence a) ∧
      NormalFormConfluence.IsNormalForm r (nf r termination localConfluence a) := by
  have h := Classical.choose_spec
    (newman_unique_normal_form r termination localConfluence a)
  exact ⟨h.1.1, fun b hba => h.1.2 ⟨b, hba⟩⟩

/-- Choosing a normal form twice has the same result as choosing it once. -/
theorem nf_idempotent {α : Type*} (r : α → α → Prop)
    (termination : WellFounded (Function.swap r))
    (localConfluence : ∀ h a b, r h a → r h b →
      ∃ c, Relation.ReflTransGen r a c ∧ Relation.ReflTransGen r b c)
    (a : α) :
    nf r termination localConfluence (nf r termination localConfluence a) =
      nf r termination localConfluence a := by
  let confluent :=
    D5.S0.Rewriting.NewmanConfluence.newman_confluent r termination localConfluence
  exact NormalFormConfluence.normal_form_unique_of_confluent confluent
    (nf_spec r termination localConfluence (nf r termination localConfluence a)).1
    Relation.ReflTransGen.refl
    (nf_spec r termination localConfluence (nf r termination localConfluence a)).2
    (nf_spec r termination localConfluence a).2

/-- Equivalent starting points have the same chosen normal form. -/
theorem nf_eq_of_eqvGen {α : Type*} (r : α → α → Prop)
    (termination : WellFounded (Function.swap r))
    (localConfluence : ∀ h a b, r h a → r h b →
      ∃ c, Relation.ReflTransGen r a c ∧ Relation.ReflTransGen r b c)
    {a b : α} (hab : Relation.EqvGen r a b) :
    nf r termination localConfluence a = nf r termination localConfluence b := by
  let confluent :=
    D5.S0.Rewriting.NewmanConfluence.newman_confluent r termination localConfluence
  obtain ⟨c, hac, hbc⟩ :=
    (D5.S0.Rewriting.ChurchRosser.newman_church_rosser r termination localConfluence a b).mp hab
  have hna : nf r termination localConfluence a = nf r termination localConfluence c :=
    NormalFormConfluence.normal_form_unique_of_confluent confluent
      (nf_spec r termination localConfluence a).1
      (hac.trans (nf_spec r termination localConfluence c).1)
      (nf_spec r termination localConfluence a).2
      (nf_spec r termination localConfluence c).2
  have hnb : nf r termination localConfluence b = nf r termination localConfluence c :=
    NormalFormConfluence.normal_form_unique_of_confluent confluent
      (nf_spec r termination localConfluence b).1
      (hbc.trans (nf_spec r termination localConfluence c).1)
      (nf_spec r termination localConfluence b).2
      (nf_spec r termination localConfluence c).2
  exact hna.trans hnb.symm

private def emptyRelation : Fin 2 → Fin 2 → Prop := fun _ _ => False

private theorem emptyTermination : WellFounded (Function.swap emptyRelation) := by
  refine ⟨?_⟩
  intro a
  exact Acc.intro a (fun b h => False.elim h)

private theorem emptyLocalConfluence :
    ∀ h a b, emptyRelation h a → emptyRelation h b →
      ∃ c, Relation.ReflTransGen emptyRelation a c ∧
        Relation.ReflTransGen emptyRelation b c := by
  intro h a b ha hb
  exact False.elim ha

example :
    nf emptyRelation emptyTermination emptyLocalConfluence (0 : Fin 2) =
      nf emptyRelation emptyTermination emptyLocalConfluence (0 : Fin 2) := by
  exact nf_eq_of_eqvGen emptyRelation emptyTermination emptyLocalConfluence
    (Relation.EqvGen.refl _)

end NormalFormFunction
