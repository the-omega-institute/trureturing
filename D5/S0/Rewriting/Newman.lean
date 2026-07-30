/- GID: D5/S0/Rewriting/Newman
   generality: G
   mirror-B: D5/B/S0/Rewriting/Newman
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Terminating locally confluent rewrite systems have unique reachable normal forms. -/

import Mathlib.Logic.Relation
import Mathlib.Logic.ExistsUnique

theorem newman_unique_normal_form {α : Type*} (r : α → α → Prop)
    (termination : WellFounded (Function.swap r))
    (localConfluence : ∀ h a b, r h a → r h b →
      ∃ c, Relation.ReflTransGen r a c ∧ Relation.ReflTransGen r b c) :
    ∀ h, ∃! n, Relation.ReflTransGen r h n ∧ ¬ ∃ x, r n x := by
  have existsNormal : ∀ h, ∃ n, Relation.ReflTransGen r h n ∧ ¬ ∃ x, r n x :=
    fun h => termination.induction (C := fun h =>
      ∃ n, Relation.ReflTransGen r h n ∧ ¬ ∃ x, r n x) h fun h ih => by
      by_cases reducible : ∃ x, r h x
      · obtain ⟨x, hx⟩ := reducible
        obtain ⟨n, hxn, hn⟩ := ih x hx
        exact ⟨n, .head hx hxn, hn⟩
      · exact ⟨h, .refl, reducible⟩
  intro h
  obtain ⟨n, hn, normalN⟩ := existsNormal h
  refine ⟨n, ⟨hn, normalN⟩, ?_⟩
  intro m hm
  obtain ⟨hm, normalM⟩ := hm
  have uniqueFrom : ∀ h, ∀ n m,
      Relation.ReflTransGen r h n → (¬ ∃ x, r n x) →
      Relation.ReflTransGen r h m → (¬ ∃ x, r m x) → n = m :=
    fun h => termination.induction (C := fun h => ∀ n m,
      Relation.ReflTransGen r h n → (¬ ∃ x, r n x) →
      Relation.ReflTransGen r h m → (¬ ∃ x, r m x) → n = m) h
      fun h ih n m hn normalN hm normalM => by
      rcases hn.cases_head with hEq | ⟨a, hna, hnaPath⟩
      · subst n
        rcases hm.cases_head with hEq | ⟨b, hmb, _⟩
        · exact hEq
        · exact False.elim (normalN ⟨b, hmb⟩)
      · rcases hm.cases_head with hEq | ⟨b, hmb, hmbPath⟩
        · subst m
          exact False.elim (normalM ⟨a, hna⟩)
        · obtain ⟨c, hac, hbc⟩ := localConfluence h a b hna hmb
          obtain ⟨q, hcq, normalQ⟩ := existsNormal c
          have haq := hac.trans hcq
          have hbq := hbc.trans hcq
          have naq : n = q := ih a hna n q hnaPath normalN haq normalQ
          have mbq : m = q := ih b hmb m q hmbPath normalM hbq normalQ
          exact naq.trans mbq.symm
  exact (uniqueFrom h n m hn normalN hm normalM).symm
