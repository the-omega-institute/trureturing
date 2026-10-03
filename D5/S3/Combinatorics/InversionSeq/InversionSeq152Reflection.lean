/- GID: D5/S3/Combinatorics/InversionSeq/InversionSeq152Reflection
   generality: G
   mirror-B: D5/B/S3/Combinatorics/InversionSeq/InversionSeq152Reflection
   mirror-E: none(waiver:reflected-dyck-run-statistics)
   anchors: []
   utility: none
   digest: The existing Dyck reflection reverses the ordered ascent and descent run lengths. -/

import D5.S3.Combinatorics.Nonnesting.NonnestingBasicRoyalReverse

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.InversionSeq.InversionSeq152Reflection

open DyckStep
open D5.S3.Combinatorics.Nonnesting.NonnestingBasicRoyalReverse

theorem reflection_runs (path : DyckWord) :
    (((reflection path).toList.splitOn D).map List.length).filter (· != 0) =
      (((path.toList.splitOn U).map List.length).filter (· != 0)).reverse := by
  let flip : DyckStep → DyckStep := fun step => match step with | U => D | D => U
  have habsent : ∀ (steps : List DyckStep) (separator : DyckStep),
      ∀ piece ∈ steps.splitOn separator, separator ∉ piece := by
    intro steps
    induction steps with
    | nil => simp
    | cons step steps ih =>
      intro separator piece hpiece
      rw [List.splitOn_cons_eq_if_modifyHead] at hpiece
      by_cases heq : step = separator
      · subst step
        simp only [beq_self_eq_true, if_true, List.mem_cons] at hpiece
        rcases hpiece with rfl | hpiece
        · simp
        · exact ih separator piece hpiece
      · have hne : (step == separator) = false := by simp [heq]
        simp only [hne, Bool.false_eq_true, if_false] at hpiece
        obtain ⟨head, tail, hsplit⟩ := List.exists_cons_of_ne_nil
          (List.splitOn_ne_nil separator steps)
        rw [hsplit, List.modifyHead_cons] at hpiece
        rcases List.mem_cons.mp hpiece with rfl | hpiece
        · simp only [List.mem_cons, not_or]
          exact ⟨Ne.symm heq, ih separator head (by rw [hsplit]; simp)⟩
        · exact ih separator piece (by rw [hsplit]; simp [hpiece])
  have hsnoc (separator : DyckStep) : ∀ pieces : List (List DyckStep),
      pieces ≠ [] → ∀ last : List DyckStep,
      [separator].intercalate (pieces ++ [last]) =
        [separator].intercalate pieces ++ [separator] ++ last := by
    intro pieces
    induction pieces with
    | nil => simp
    | cons head tail ih =>
      intro hne last
      cases tail with
      | nil => simp
      | cons next tail =>
        simp only [List.cons_append, List.intercalate_cons_cons]
        simp only [List.cons_append] at ih
        rw [ih (by simp) last]
        simp only [List.append_assoc]
  have hreverse (separator : DyckStep) : ∀ pieces : List (List DyckStep),
      ([separator].intercalate pieces).reverse =
        [separator].intercalate (pieces.reverse.map List.reverse) := by
    intro pieces
    induction pieces with
    | nil => simp
    | cons head tail ih =>
      cases tail with
      | nil => simp
      | cons next tail =>
        simp only [List.intercalate_cons_cons, List.reverse_append,
          List.reverse_cons, List.map_append, List.map_singleton]
        rw [hsnoc separator _ (by simp) head.reverse]
        simpa only [List.reverse_cons, List.map_append, List.map_singleton,
          List.reverse_nil, List.nil_append, List.append_assoc] using
          congrArg (fun word => word ++ [separator] ++ head.reverse) ih
  have hmap (separator : DyckStep) : ∀ pieces : List (List DyckStep),
      ([separator].intercalate pieces).map flip =
        [flip separator].intercalate (pieces.map (List.map flip)) := by
    intro pieces
    induction pieces with
    | nil => simp
    | cons head tail ih =>
      cases tail with
      | nil => simp
      | cons next tail => simp [ih]
  have hruns (steps : List DyckStep) :
      (((steps.reverse.map flip).splitOn D).map List.length) =
        ((steps.splitOn U).map List.length).reverse := by
    let pieces := (steps.splitOn U).reverse.map (fun piece => piece.reverse.map flip)
    have hnonempty : pieces ≠ [] := by
      simp [pieces]
    have hpieces : ∀ piece ∈ pieces, D ∉ piece := by
      intro piece hpiece
      obtain ⟨original, horiginal, rfl⟩ := List.mem_map.mp hpiece
      have ha := habsent steps U original (List.mem_reverse.mp horiginal)
      intro hdown
      obtain ⟨step, hstep, hflipstep⟩ := List.mem_map.mp hdown
      have hstepU : step = U := by cases step <;> simp_all [flip]
      subst step
      exact ha (List.mem_reverse.mp hstep)
    have hword : steps.reverse.map flip = [D].intercalate pieces := by
      nth_rw 1 [← List.intercalate_splitOn U (xs := steps)]
      rw [hreverse, hmap]
      simp only [flip, pieces, List.map_map, Function.comp_def]
    rw [hword, List.splitOn_intercalate D hpieces hnonempty]
    simp [pieces, List.map_map, List.map_reverse]
  change ((((path.toList.reverse.map flip).splitOn D).map List.length).filter
    (· != 0)) = _
  rw [hruns, List.filter_reverse]

end D5.S3.Combinatorics.InversionSeq.InversionSeq152Reflection
