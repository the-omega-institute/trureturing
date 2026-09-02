/- GID: D5/S1/Words/AdmissibleWords/AdmissibleRelationSpaceGrowth
   generality: G
   mirror-B: D5/B/S1/Words/AdmissibleWords/AdmissibleRelationSpaceGrowth
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The endomorphism space of complex-valued admissible words has
   squared Fibonacci dimension and golden-ratio-squared consecutive growth. -/

import D5.S1.Words.AdmissibleWords.AdmissibleCount
import Mathlib.Analysis.SpecificLimits.Fibonacci
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix

/-!
# Relation-space growth for admissible words

The complex function space on length-`n` Zeckendorf-admissible binary words
has Fibonacci dimension. Its full linear endomorphism space therefore has the
square of that dimension, and consecutive dimensions grow by the square of
the golden ratio.
-/

/- Library-search and duplication audit trail (2026-09-02):
   * `AdmissibleCount.admissibleWord_card_eq_fib` is the existing owner of the
     admissible-word count and is used directly.
   * Pinned Mathlib supplies `Module.finrank_linearMap`,
     `Module.finrank_fintype_fun_eq_card`, and
     `tendsto_fib_succ_div_fib_atTop`; all are used directly.
   * Repository searches for endomorphism finrank combined with admissible
     words, squared Fibonacci growth, and relation-space growth found no
     equivalent theorem. Receipt and digest indices had no coverage entry.
   * Searches of commits on `origin/lane/math/*` beyond `origin/dev` found no
     theorem with this dimension formula or limit. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S1.Words.AdmissibleWords.AdmissibleRelationSpaceGrowth

open Filter Topology
open scoped goldenRatio
open D5.S1.Words.AdmissibleWords.AdmissibleCount

/-- The finite complex function space on admissible words of length `n`. -/
abbrev admissibleWordSpace (n : Nat) :=
  {word : Fin n -> Bool // Adm n word} -> Complex

/-- The space of all complex-linear relations between admissible words. -/
abbrev admissibleRelationSpace (n : Nat) :=
  Module.End Complex (admissibleWordSpace n)

/-- The full relation space has the square of the admissible-word count as
its complex dimension. -/
theorem admissible_relation_space_finrank (n : Nat) :
    Module.finrank Complex (admissibleRelationSpace n) =
      (Nat.fib (n + 2)) ^ 2 := by
  rw [Module.finrank_linearMap]
  simp only [admissibleWordSpace, Module.finrank_fintype_fun_eq_card,
    admissibleWord_card_eq_fib]
  ring

/-- Consecutive full relation-space dimensions grow by the square of the
golden ratio. -/
theorem admissible_relation_space_growth :
    Tendsto
      (fun n : Nat =>
        (Module.finrank Complex (admissibleRelationSpace (n + 1)) : Real) /
          Module.finrank Complex (admissibleRelationSpace n))
      atTop (nhds (Real.goldenRatio ^ 2)) := by
  have hratio :
      Tendsto
        (fun n : Nat =>
          (Nat.fib (n + 3) : Real) / Nat.fib (n + 2))
        atTop (nhds Real.goldenRatio) := by
    simpa only [Function.comp_def, Nat.reduceAdd, Nat.add_assoc] using
      tendsto_fib_succ_div_fib_atTop.comp
        (Filter.tendsto_add_atTop_nat 2)
  simpa [admissible_relation_space_finrank, Nat.cast_pow, div_pow,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hratio.pow 2

#print axioms admissible_relation_space_finrank
#print axioms admissible_relation_space_growth

end D5.S1.Words.AdmissibleWords.AdmissibleRelationSpaceGrowth
