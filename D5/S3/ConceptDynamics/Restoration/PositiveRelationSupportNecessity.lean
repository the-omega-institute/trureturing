/- GID: D5/S3/ConceptDynamics/Restoration/PositiveRelationSupportNecessity
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Restoration/PositiveRelationSupportNecessity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Basic.Rel, mathlib/module/Mathlib.Data.Fintype.Card, mathlib/module/Mathlib.Logic.Equiv.Basic]
   utility: none
   digest: Unexposed nonisolated endpoint labels admit evidence-preserving full relabelings with different targets, forcing both supports and certificate size. -/

import Mathlib.Basic.Rel
import Mathlib.Data.Fintype.Card
import Mathlib.Logic.Equiv.Basic

/-! Positive evidence forces support exposure under unrestricted full relabeling. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Restoration.PositiveRelationSupportNecessity

variable {A B L R : Type*}

/-- The whole relation transported by two full injective label maps. -/
def transport (E : SetRel A B) (left : A ↪ L) (right : B ↪ R) : SetRel L R :=
  Prod.map left right '' E

/-- Swapping an unobserved used left label with an unused ambient label preserves
every positive evidence pair, while an incident edge changes the whole target. -/
theorem unexposed_left_label_competitor
    (E : SetRel A B) (left : A ↪ L) (right : B ↪ R)
    (D : SetRel L R) (attained : D ⊆ transport E left right)
    (a : A) (incident : ∃ b, (a, b) ∈ E)
    (unexposed : left a ∉ D.dom) (fresh : L) (unused : fresh ∉ Set.range left) :
    ∃ alternative : A ↪ L,
      alternative a = fresh ∧
      (∀ x, x ≠ a → alternative x = left x) ∧
      D ⊆ transport E alternative right ∧
      transport E alternative right ≠ transport E left right := by
  classical
  let alternative := left.trans (Equiv.swap (left a) fresh).toEmbedding
  have at_a : alternative a = fresh := Equiv.swap_apply_left _ _
  have away (x : A) (hx : x ≠ a) : alternative x = left x := by
    exact Equiv.swap_apply_of_ne_of_ne (fun h => hx (left.injective h))
      (fun h => unused ⟨x, h⟩)
  refine ⟨alternative, at_a, away, ?_, ?_⟩
  · intro pair hp
    obtain ⟨⟨x, y⟩, hxy, rfl⟩ := attained hp
    have hxa : x ≠ a := by
      intro h
      subst x
      exact unexposed ⟨right y, hp⟩
    exact ⟨(x, y), hxy, Prod.ext (away x hxa) rfl⟩
  · obtain ⟨b, hab⟩ := incident
    have added : (fresh, right b) ∈ transport E alternative right :=
      ⟨(a, b), hab, Prod.ext at_a rfl⟩
    intro same
    rw [same] at added
    obtain ⟨⟨x, y⟩, _, hxy⟩ := added
    exact unused ⟨x, congrArg Prod.fst hxy⟩

/-- The right-side transposition retains the full right injection and the same
source relation, with all positive pairs preserved and a different target. -/
theorem unexposed_right_label_competitor
    (E : SetRel A B) (left : A ↪ L) (right : B ↪ R)
    (D : SetRel L R) (attained : D ⊆ transport E left right)
    (b : B) (incident : ∃ a, (a, b) ∈ E)
    (unexposed : right b ∉ D.cod) (fresh : R) (unused : fresh ∉ Set.range right) :
    ∃ alternative : B ↪ R,
      alternative b = fresh ∧
      (∀ y, y ≠ b → alternative y = right y) ∧
      D ⊆ transport E left alternative ∧
      transport E left alternative ≠ transport E left right := by
  classical
  let alternative := right.trans (Equiv.swap (right b) fresh).toEmbedding
  have at_b : alternative b = fresh := Equiv.swap_apply_left _ _
  have away (y : B) (hy : y ≠ b) : alternative y = right y := by
    exact Equiv.swap_apply_of_ne_of_ne (fun h => hy (right.injective h))
      (fun h => unused ⟨y, h⟩)
  refine ⟨alternative, at_b, away, ?_, ?_⟩
  · intro pair hp
    obtain ⟨⟨x, y⟩, hxy, rfl⟩ := attained hp
    have hyb : y ≠ b := by
      intro h
      subst y
      exact unexposed ⟨left x, hp⟩
    exact ⟨(x, y), hxy, Prod.ext rfl (away y hyb)⟩
  · obtain ⟨a, hab⟩ := incident
    have added : (left a, fresh) ∈ transport E left alternative :=
      ⟨(a, b), hab, Prod.ext rfl at_b⟩
    intro same
    rw [same] at added
    obtain ⟨⟨x, y⟩, _, hxy⟩ := added
    exact unused ⟨y, congrArg Prod.snd hxy⟩

/-- With ambient slack on both sides, target constancy over all full injections
forces every used endpoint label into the attained positive evidence. Distinct
pairs and completed slots, including repetitions, each obey the resulting bound. -/
theorem positive_certificate_support_lower_bound
    [Fintype A] [Fintype B] [Fintype L] [Fintype R]
    [DecidableEq L] [DecidableEq R]
    (E : SetRel A B) (left : A ↪ L) (right : B ↪ R)
    (D : Finset (L × R))
    (attained : (D : SetRel L R) ⊆ transport E left right)
    (left_incident : ∀ a, ∃ b, (a, b) ∈ E)
    (right_incident : ∀ b, ∃ a, (a, b) ∈ E)
    (left_slack : Fintype.card A < Fintype.card L)
    (right_slack : Fintype.card B < Fintype.card R)
    (constant : ∀ (other_left : A ↪ L) (other_right : B ↪ R),
      (D : SetRel L R) ⊆ transport E other_left other_right →
      transport E other_left other_right = transport E left right) :
    SetRel.dom (D : SetRel L R) = Set.range left ∧
    SetRel.cod (D : SetRel L R) = Set.range right ∧
    max (Fintype.card A) (Fintype.card B) ≤ D.card ∧
    ∀ samples : List (L × R), samples.toFinset = D →
      max (Fintype.card A) (Fintype.card B) ≤ samples.length := by
  classical
  have left_fresh : ∃ fresh, fresh ∉ Set.range left := by
    by_contra h
    have surj : Function.Surjective left := by
      intro x
      by_contra hx
      exact h ⟨x, hx⟩
    exact (Nat.not_le_of_lt left_slack) (Fintype.card_le_of_surjective left surj)
  have right_fresh : ∃ fresh, fresh ∉ Set.range right := by
    by_contra h
    have surj : Function.Surjective right := by
      intro x
      by_contra hx
      exact h ⟨x, hx⟩
    exact (Nat.not_le_of_lt right_slack) (Fintype.card_le_of_surjective right surj)
  have exposed_left (a : A) : left a ∈ SetRel.dom (D : SetRel L R) := by
    by_contra missing
    obtain ⟨fresh, unused⟩ := left_fresh
    obtain ⟨alternative, _, _, preserves, differs⟩ :=
      unexposed_left_label_competitor E left right D attained a
        (left_incident a) missing fresh unused
    exact differs (constant alternative right preserves)
  have exposed_right (b : B) : right b ∈ SetRel.cod (D : SetRel L R) := by
    by_contra missing
    obtain ⟨fresh, unused⟩ := right_fresh
    obtain ⟨alternative, _, _, preserves, differs⟩ :=
      unexposed_right_label_competitor E left right D attained b
        (right_incident b) missing fresh unused
    exact differs (constant left alternative preserves)
  have left_support : SetRel.dom (D : SetRel L R) = Set.range left := by
    apply Set.Subset.antisymm
    · rintro l ⟨r, hp⟩
      obtain ⟨⟨a, b⟩, _, h⟩ := attained hp
      exact ⟨a, congrArg Prod.fst h⟩
    · rintro _ ⟨a, rfl⟩
      exact exposed_left a
  have right_support : SetRel.cod (D : SetRel L R) = Set.range right := by
    apply Set.Subset.antisymm
    · rintro r ⟨l, hp⟩
      obtain ⟨⟨a, b⟩, _, h⟩ := attained hp
      exact ⟨b, congrArg Prod.snd h⟩
    · rintro _ ⟨b, rfl⟩
      exact exposed_right b
  have left_count : Fintype.card A ≤ D.card := by
    have included : Finset.univ.image left ⊆ D.image Prod.fst := by
      intro l hl
      obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hl
      obtain ⟨r, hp⟩ := exposed_left a
      exact Finset.mem_image.mpr ⟨(left a, r), hp, rfl⟩
    calc
      Fintype.card A = (Finset.univ.image left).card :=
        (Finset.card_image_of_injective _ left.injective).symm
      _ ≤ (D.image Prod.fst).card := Finset.card_le_card included
      _ ≤ D.card := Finset.card_image_le
  have right_count : Fintype.card B ≤ D.card := by
    have included : Finset.univ.image right ⊆ D.image Prod.snd := by
      intro r hr
      obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hr
      obtain ⟨l, hp⟩ := exposed_right b
      exact Finset.mem_image.mpr ⟨(l, right b), hp, rfl⟩
    calc
      Fintype.card B = (Finset.univ.image right).card :=
        (Finset.card_image_of_injective _ right.injective).symm
      _ ≤ (D.image Prod.snd).card := Finset.card_le_card included
      _ ≤ D.card := Finset.card_image_le
  have bound := max_le left_count right_count
  refine ⟨left_support, right_support, bound, ?_⟩
  intro samples hsamples
  exact bound.trans (hsamples ▸ samples.toFinset_card_le)

#print axioms unexposed_left_label_competitor
#print axioms unexposed_right_label_competitor
#print axioms positive_certificate_support_lower_bound

end D5.S3.ConceptDynamics.Restoration.PositiveRelationSupportNecessity
