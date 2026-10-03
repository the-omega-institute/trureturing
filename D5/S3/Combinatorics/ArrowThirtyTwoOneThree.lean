/- GID: D5/S3/Combinatorics/ArrowThirtyTwoOneThree
   generality: G
   mirror-B: D5/B/S3/Combinatorics/ArrowThirtyTwoOneThree
   mirror-E: none(waiver:enumeration-of-the-arrow-pattern-32-1-to-3)
   anchors: []
   utility: none
   digest: The avoider series satisfies the Zhou--Yu cubic and is its unique branch with constant and linear coefficients one. -/

import D5.S3.Combinatorics.ArrowThirtyTwoOneThreeDefs
import D5.S3.Combinatorics.ArrowThirtyTwoOneThreeSeries
import D5.S3.Combinatorics.ArrowThirtyTwoOneThreeRefined
import D5.S3.Combinatorics.ArrowThirtyTwoOneThreeAlgebra

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.ArrowThirtyTwoOneThree

open D5.S3.Combinatorics.ArrowWilfDefs
open D5.S3.Combinatorics.ArrowThirtyTwoOneThreeDefs

noncomputable section

/-- The corrected Zhou--Yu enumeration claim, with both branch coefficients fixed. -/
theorem result : ArrowThirtyTwoOneThreeDefs.claim := by
  have hzeroSet :
      avoiders 0 [3, 2] [(1, 3)] 3 = ({[]} : Set (List ℕ)) := by
    ext p
    constructor
    · intro hp
      have hnil : p = [] := List.Perm.eq_nil hp.1
      simpa [hnil]
    · intro hp
      have hnil : p = [] := by simpa using hp
      subst p
      constructor
      · simp [avoiders]
      · intro h
        rcases h with ⟨x, hxlt, hxmem, hxsub, hxhat⟩
        simp at hxmem
        have hfalse := hxmem 1 (by omega)
        omega
  have honeSet :
      avoiders 1 [3, 2] [(1, 3)] 3 = ({[1]} : Set (List ℕ)) := by
    ext p
    constructor
    · intro hp
      have hperm : p.Perm [1] := by simpa using hp.1
      have hpone : p = [1] := List.perm_singleton.mp hperm
      simpa [hpone]
    · intro hp
      have hpone : p = [1] := by simpa using hp
      subst p
      constructor
      · simp [avoiders]
      · intro h
        rcases h with ⟨x, hxlt, hxmem, hxsub, hxhat⟩
        have h1 : x 1 = 1 := by simpa using hxmem 1 (by omega) (by omega)
        have h2 : x 2 = 1 := by simpa using hxmem 2 (by omega) (by omega)
        have hlt := hxlt 1 (by omega) (by omega)
        rw [h1, h2] at hlt
        omega
  have hzero : count 0 = 1 := by
    rw [count, hzeroSet, Set.ncard_singleton]
  have hone : count 1 = 1 := by
    rw [count, honeSet, Set.ncard_singleton]
  have hconstant : PowerSeries.constantCoeff series = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff]
    simp [series, hzero]
  have hlinear : PowerSeries.coeff 1 series = 1 := by
    simp [series, hone]
  have hcubic := ArrowThirtyTwoOneThreeAlgebra.cubic_of_recurrence count hzero
    (by simpa only [series] using ArrowThirtyTwoOneThreeRefined.count_recurrence)
  change 1 + (3 * PowerSeries.X - 2) * series +
    (1 - PowerSeries.X) * (1 - 2 * PowerSeries.X) * series ^ 2 +
      PowerSeries.X ^ 3 * series ^ 3 = 0 at hcubic
  refine ⟨hcubic, ?_⟩
  intro G hG0 hG1 hG
  exact ArrowThirtyTwoOneThreeSeries.cubic_solution_unique G series hG0
    hconstant hG1 hlinear hG hcubic

end
end D5.S3.Combinatorics.ArrowThirtyTwoOneThree
