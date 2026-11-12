/- GID: D5/S3/Combinatorics/Graph/Roommates/BufferLayout
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Roommates/BufferLayout
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.Fin.VecNotation]
   utility: none
   digest: Six-buffer completion pairs every free boundary site and isolates at most one interior single. -/

import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic

open scoped Classical

set_option autoImplicit false
namespace D5.S3.Combinatorics.Graph.Roommates.BufferLayout

/-- The four boundary sites already reserved for old partners. -/
def occupied (b : Fin 4 → Bool) : Fin 6 → Bool :=
  ![b 0, b 1, false, false, b 2, b 3]

/-- Deterministic pairing of unreserved sites. Fixed points at reserved sites
are placeholders for the old requesting vertices, not singles. -/
def mate (b : Fin 4 → Bool) : Fin 6 → Fin 6 :=
  match b 0, b 1, b 2, b 3 with
  | false, false, false, false => ![1, 0, 3, 2, 5, 4]
  | false, false, false, true => ![1, 0, 2, 4, 3, 5]
  | false, false, true, false => ![1, 0, 2, 5, 4, 3]
  | false, false, true, true => ![1, 0, 3, 2, 4, 5]
  | false, true, false, false => ![2, 1, 0, 3, 5, 4]
  | false, true, false, true => ![2, 1, 0, 4, 3, 5]
  | false, true, true, false => ![2, 1, 0, 5, 4, 3]
  | false, true, true, true => ![2, 1, 0, 3, 4, 5]
  | true, false, false, false => ![0, 2, 1, 3, 5, 4]
  | true, false, false, true => ![0, 2, 1, 4, 3, 5]
  | true, false, true, false => ![0, 2, 1, 5, 4, 3]
  | true, false, true, true => ![0, 2, 1, 3, 4, 5]
  | true, true, false, false => ![0, 1, 3, 2, 5, 4]
  | true, true, false, true => ![0, 1, 2, 4, 3, 5]
  | true, true, true, false => ![0, 1, 2, 5, 4, 3]
  | true, true, true, true => ![0, 1, 3, 2, 4, 5]

/-- All local pairing obligations, for every possible boundary subset. -/
private theorem layout_facts (b : Fin 4 → Bool) :
    (∀ i, mate b (mate b i) = i) ∧
    (∀ i, occupied b i = true → mate b i = i) ∧
    (∀ i, mate b i ≠ i → occupied b (mate b i) = false) ∧
    (∀ i, (mate b i).val ≤ i.val + 2 ∧ i.val ≤ (mate b i).val + 2) ∧
    (∀ i, occupied b i = false → mate b i = i → i = 2 ∨ i = 3) ∧
    (∀ i j, occupied b i = false → mate b i = i →
      i ≠ j → i.val ≤ j.val + 2 → j.val ≤ i.val + 2 →
      occupied b j = true ∨ mate b j ≠ j) := by
  rcases h0 : b 0 with _ | _ <;> rcases h1 : b 1 with _ | _ <;>
    rcases h2 : b 2 with _ | _ <;> rcases h3 : b 3 with _ | _ <;>
    simp only [mate, occupied, h0, h1, h2, h3] <;> decide

/-- The layout is an involution, with every newly single site interior and
surrounded by matched sites after occupied sites receive their old partners. -/
theorem buffer_completion (b : Fin 4 → Bool) :
    Function.Involutive (mate b) ∧
    (∀ i, occupied b i = true → mate b i = i) ∧
    (∀ i, mate b i ≠ i → occupied b (mate b i) = false) ∧
    (∀ i, (mate b i).val ≤ i.val + 2 ∧ i.val ≤ (mate b i).val + 2) ∧
    (∀ i, occupied b i = false → mate b i = i → i = 2 ∨ i = 3) ∧
    (∀ i j, occupied b i = false → mate b i = i →
      i ≠ j → i.val ≤ j.val + 2 → j.val ≤ i.val + 2 →
      occupied b j = true ∨ mate b j ≠ j) := layout_facts b


/-- Boundary sites at which old requests can land. -/
def boundarySite : Fin 4 → Fin 6 := ![0, 1, 4, 5]

noncomputable def flags {α : Type} (request : α → Fin 6) : Fin 4 → Bool :=
  fun j => decide (∃ a, request a = boundarySite j)

private theorem occupied_iff {α : Type} (request : α → Fin 6)
    (hcentral : ∀ a, request a ≠ 2 ∧ request a ≠ 3) (i : Fin 6) :
    occupied (flags request) i = true ↔ ∃ a, request a = i := by
  classical
  fin_cases i <;> simp [occupied, flags, boundarySite, hcentral,
    show ¬ (∃ a, request a = 2) from fun ⟨a, h⟩ => (hcentral a).1 h,
    show ¬ (∃ a, request a = 3) from fun ⟨a, h⟩ => (hcentral a).2 h]

/-- Every request is fulfilled. Unreserved buffer sites use the local layout. -/
noncomputable def partner {α : Type} (request : α → Fin 6) :
    Sum α (Fin 6) → Sum α (Fin 6)
  | .inl a => .inr (request a)
  | .inr i => if h : ∃ a, request a = i then .inl (Classical.choose h)
      else .inr (mate (flags request) i)

/-- Completion handles an arbitrary injective family of exterior requests.
It produces an actual involution, rather than a list of small examples. -/
theorem complete_requests {α : Type} (request : α → Fin 6)
    (hinj : Function.Injective request)
    (hcentral : ∀ a, request a ≠ 2 ∧ request a ≠ 3) :
    Function.Involutive (partner request) ∧
    (∀ a, partner request (.inl a) = .inr (request a)) ∧
    (∀ i, partner request (.inr i) = .inr i → i = 2 ∨ i = 3) := by
  classical
  have hlocal := buffer_completion (flags request)
  have hocc := occupied_iff request hcentral
  have hmate := hlocal.1
  constructor
  · intro x
    cases x with
    | inl a =>
      have h : ∃ a', request a' = request a := ⟨a, rfl⟩
      have hc : Classical.choose h = a := hinj (Classical.choose_spec h)
      simp only [partner, dif_pos h, hc]
    | inr i =>
      by_cases h : ∃ a, request a = i
      · simp only [partner, dif_pos h]
        rw [Classical.choose_spec h]
      · have ho : occupied (flags request) i = false := by
          cases he : occupied (flags request) i
          · rfl
          · exact (h ((hocc i).mp he)).elim
        have hfree : ¬ ∃ a, request a = mate (flags request) i := by
          intro ⟨a, ha⟩
          have hx := hlocal.2.1 _ ((hocc _).mpr ⟨a, ha⟩)
          have hy := hmate i
          rw [hx] at hy
          exact h ⟨a, ha.trans hy⟩
        simp only [partner, dif_neg h, dif_neg hfree, hmate]
  · constructor
    · intro a
      rfl
    · intro i hi
      by_cases h : ∃ a, request a = i
      · simp only [partner, dif_pos h] at hi
        cases hi
      · have ho : occupied (flags request) i = false := by
          cases he : occupied (flags request) i
          · rfl
          · exact (h ((hocc i).mp he)).elim
        have he : mate (flags request) i = i := by
          simpa only [partner, dif_neg h, Sum.inr.injEq] using hi
        exact hlocal.2.2.2.2.1 i ho he

#print axioms complete_requests
#print axioms buffer_completion
end D5.S3.Combinatorics.Graph.Roommates.BufferLayout
