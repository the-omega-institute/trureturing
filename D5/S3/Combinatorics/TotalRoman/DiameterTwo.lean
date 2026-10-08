/- GID: D5/S3/Combinatorics/TotalRoman/DiameterTwo
   generality: G
   mirror-B: D5/B/S3/Combinatorics/TotalRoman/DiameterTwo
   mirror-E: none(waiver:mynhardt-ogden-question-one)
   anchors: []
   utility: none
   digest: Connected six-total-Roman edge-supercritical graphs exist at every order at least ten. -/

import D5.S3.Combinatorics.TotalRoman.DiameterTwoMetric
import D5.S3.Combinatorics.TotalRoman.DiameterTwoRepair

set_option autoImplicit false

namespace D5.S3.Combinatorics.TotalRoman.DiameterTwo

open SupercriticalDefs SupercriticalBasics DiameterTwoConstruction
open DiameterTwoWeight DiameterTwoRepair DiameterTwoMetric

/-- An affirmative answer to Mynhardt–Ogden Question 1 at every order at least ten. -/
theorem result : DiameterTwoDefs.claim := by
  classical
  intro n hn
  have hiso : ∀ w : Fin n, ∃ u, (family n).Adj w u := by
    intro w
    obtain ⟨u, _, hu⟩ := total_domination hn w
    exact ⟨u, hu⟩
  have hvalue : gammaTR (family n) = 6 := by
    have hu : gammaTR (family n) ≤ 6 := by
      have h03 : Fin.castLE hn 0 ≠ Fin.castLE hn 3 := by simp
      have h06 : Fin.castLE hn 0 ≠ Fin.castLE hn 6 := by simp
      have h36 : Fin.castLE hn 3 ≠ Fin.castLE hn 6 := by simp
      simpa [h03, h06, h36] using doubled_bound (family n) _ (total_domination hn)
    obtain ⟨f, hf, hw⟩ := attained hiso
    have hl : 6 ≤ gammaTR (family n) := by
      by_contra hh
      obtain ⟨a, b, hd⟩ := dominating_pair_of_weight_le_five
        (by simpa using (show 6 ≤ n by omega)) hf (by omega)
      obtain ⟨w, hwa, hwb, hnota, hnotb⟩ := obstruction hn a b
      rcases hd w with h | h | h | h
      · exact hwa h
      · exact hwb h
      · exact hnota h
      · exact hnotb h
    omega
  obtain ⟨hconn, hdiam, hmissing⟩ := metric hn
  refine ⟨family n, hconn, hdiam, ?_, hvalue⟩
  refine ⟨⟨hiso, hmissing⟩, ?_⟩
  intro a b hab hgap
  rw [repaired hn a b hab hgap, hvalue]

#print axioms result

end D5.S3.Combinatorics.TotalRoman.DiameterTwo
