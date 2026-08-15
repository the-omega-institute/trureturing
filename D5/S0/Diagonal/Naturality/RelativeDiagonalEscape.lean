/- GID: D5/S0/Diagonal/Naturality/RelativeDiagonalEscape
   generality: G
   mirror-B: D5/B/S0/Diagonal/Naturality/RelativeDiagonalEscape
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A fixed-point-free twist sends every diagonal listing outside its range. -/

import D5.S0.Diagonal.EscapeCount

/- Library-search audit trail (2026-08-15):
   * Loogle query `Function.Surjective (?f : ?a -> ?a -> ?b)` found the related theorem
     `Function.exists_fixed_point_of_surjective`, but not this explicit diagonal witness.
   * LeanSearch natural-language and exact-name queries found no theorem matching the target.
   * Pinned-Mathlib search confirmed `Function.exists_fixed_point_of_surjective`,
     `Function.cantor_surjective`, and `Function.cantor_injective`, but no full-statement match.
   * Repository search found the exact support lemma `EscapeCount.diagonal_landing_fixed`,
     imported and applied below, and no duplicate of this arbitrary-type escape theorem. -/

namespace D5.S0.Diagonal.Naturality.RelativeDiagonalEscape

open D5.S0.Diagonal

/-- The diagonal obtained from a fixed-point-free twist cannot be a row of the original listing. -/
theorem relative_diagonal_escape
    {A Y : Type*} (e : A -> A -> Y) (tau : Y -> Y)
    (hfix : forall y, tau y ≠ y) :
    EscapeCount.diagonal tau e ∉ Set.range e := by
  intro hRange
  rcases hRange with ⟨a, ha⟩
  exact hfix (e a a) (EscapeCount.diagonal_landing_fixed ha)

example : Unit := ()

example :
    EscapeCount.diagonal Bool.not (fun _ : Unit => fun _ => false) ∉
      Set.range (fun _ : Unit => fun _ => false) :=
  relative_diagonal_escape _ _ (by decide)

#print axioms relative_diagonal_escape

end D5.S0.Diagonal.Naturality.RelativeDiagonalEscape
