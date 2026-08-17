/- GID: D5/S3/ObserverMemory/InverseLimits/FactorImageStability
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/InverseLimits/FactorImageStability
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Surjective semiconjugacies preserve iterate images and their stabilization. -/

import Mathlib.Data.Set.Card
import Mathlib.Logic.Function.Iterate

/- Library-search audit trail (2026-08-18):
   * Repository searches found the stable-image theorem for one finite self-map, but no theorem
     transporting iterate ranges, their cardinal bound, and stabilization through a factor map.
   * Pinned Mathlib supplies `Function.Semiconj.iterate_right`, `Set.range_comp`,
     `Function.Surjective.range_comp`, and `Set.ncard_image_le`; all are applied below.
   * Two local `smart_search.sh` queries found no full-statement match. Loogle returned zero hits
     for the semiconjugacy/surjectivity type query. LeanSearch's API returned HTTP 404, so it
     supplied no search conclusion.
-/

namespace D5.S3.ObserverMemory.InverseLimits.FactorImageStability

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- A surjective semiconjugacy maps every iterated source image onto the corresponding factor
image. On a finite source this bounds the factor image cardinality, and equality of two
successive source images forces equality of the corresponding factor images. -/
theorem surjective_semiconj_iterate_ranges
    {Y Z : Type*} [Finite Y]
    (sourceStep : Y -> Y) (factorStep : Z -> Z) (quotientMap : Y -> Z)
    (hSurjective : Function.Surjective quotientMap)
    (hSemiconj : Function.Semiconj quotientMap sourceStep factorStep)
    (k : Nat) :
    quotientMap '' Set.range (sourceStep^[k]) = Set.range (factorStep^[k]) /\
      (Set.range (factorStep^[k])).ncard <= (Set.range (sourceStep^[k])).ncard /\
      (Set.range (sourceStep^[k]) = Set.range (sourceStep^[k + 1]) ->
        Set.range (factorStep^[k]) = Set.range (factorStep^[k + 1])) := by
  have hRange (n : Nat) :
      quotientMap '' Set.range (sourceStep^[n]) = Set.range (factorStep^[n]) := by
    rw [<- Set.range_comp, (hSemiconj.iterate_right n).comp_eq]
    exact hSurjective.range_comp (factorStep^[n])
  refine ⟨hRange k, ?_, ?_⟩
  · rw [<- hRange k]
    exact Set.ncard_image_le
  · intro hStable
    calc
      Set.range (factorStep^[k]) = quotientMap '' Set.range (sourceStep^[k]) :=
        (hRange k).symm
      _ = quotientMap '' Set.range (sourceStep^[k + 1]) :=
        congrArg (Set.image quotientMap) hStable
      _ = Set.range (factorStep^[k + 1]) := hRange (k + 1)

#print axioms surjective_semiconj_iterate_ranges

end D5.S3.ObserverMemory.InverseLimits.FactorImageStability
