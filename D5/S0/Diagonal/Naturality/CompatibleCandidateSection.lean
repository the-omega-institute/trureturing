/- GID: D5/S0/Diagonal/Naturality/CompatibleCandidateSection
   generality: G
   mirror-B: D5/B/S0/Diagonal/Naturality/CompatibleCandidateSection
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Cofiltered finite candidates admit a compatible section. -/

import Mathlib.CategoryTheory.CofilteredSystem

/- Library-search audit trail (2026-08-16):
   * Repository search found no D5 declaration for compatible sections of finite cofiltered
     candidate systems.
   * Pinned-Mathlib search found the exact general result
     `nonempty_sections_of_finite_cofiltered_system`, imported and applied below.
   * Loogle exact-name query `nonempty_sections_of_finite_inverse_system` returned that theorem
     and its cofiltered generalization.
   * LeanSearch query `the inverse limit of nonempty finite types over a cofiltered index is
     nonempty` returned `nonempty_sections_of_finite_cofiltered_system` as the direct hit. -/

namespace D5.S0.Diagonal.Naturality.CompatibleCandidateSection

open CategoryTheory Set

universe u v w

variable {J : Type u} [Category.{w} J]

/-- A point in every candidate subset, compatible with every transition in the diagram. -/
structure CandidateSection
    (D : J ⥤ Type v) (O : ∀ j, Set (D.obj j)) where
  point : ∀ j, D.obj j
  point_mem : ∀ j, point j ∈ O j
  compatible : ∀ {i j} (f : i ⟶ j), D.map f (point i) = point j

/-- Nonempty finite candidate subsets preserved by a cofiltered diagram have a compatible
section. -/
theorem compatible_candidate_section_nonempty
    [IsCofiltered J] (D : J ⥤ Type v) (O : ∀ j, Set (D.obj j))
    (h_transition : ∀ {i j} (f : i ⟶ j) {x}, x ∈ O i → D.map f x ∈ O j)
    [∀ j, Finite ↥(O j)] [∀ j, Nonempty ↥(O j)] :
    Nonempty (CandidateSection D O) := by
  let candidates : J ⥤ Type v :=
    { obj := fun j => ↥(O j)
      map := fun {i j} f => ↾fun x : ↥(O i) =>
        (⟨D.map f x.1, h_transition f x.2⟩ : ↥(O j))
      map_id := by
        intro i
        ext x
        simp
      map_comp := by
        intro i j k f g
        ext x
        simp }
  obtain ⟨s, hs⟩ := nonempty_sections_of_finite_cofiltered_system candidates
  exact ⟨
    { point := fun j => (s j).1
      point_mem := fun j => (s j).2
      compatible := fun f => by
        simpa [candidates] using congrArg Subtype.val (hs f) }⟩

example : CandidateSection ((Functor.const Unit).obj Bool) (fun _ => Set.univ) := by
  refine { point := fun _ => false, point_mem := ?_, compatible := ?_ }
  · intro j
    exact Set.mem_univ _
  · intro i j f
    change false = false
    rfl

example : Nonempty
    (CandidateSection ((Functor.const Unit).obj Bool) (fun _ => Set.univ)) := by
  let D : Unit ⥤ Type := (Functor.const Unit).obj Bool
  let O : ∀ j, Set (D.obj j) := fun _ => Set.univ
  letI : ∀ j, Finite ↥(O j) := fun _ => by
    change Finite ↥(Set.univ : Set Bool)
    infer_instance
  letI : ∀ j, Nonempty ↥(O j) := fun _ => ⟨⟨false, Set.mem_univ _⟩⟩
  simpa [D, O] using compatible_candidate_section_nonempty D O (by
    intro i j f x hx
    exact Set.mem_univ _)

#print axioms compatible_candidate_section_nonempty

end D5.S0.Diagonal.Naturality.CompatibleCandidateSection
