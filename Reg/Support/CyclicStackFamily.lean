import D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily
import Reg.Support.DependentFamily

namespace Reg.Support.CyclicStackFamily
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily

/-- A rejected whole-family intervention is sensitive in the sole observed role;
there are no anchors, and the other-role equality is vacuous. -/
theorem singleSensitivity {P X Y : Type}
    (law : Realization (singleObservation P X Y) → Prop)
    (actual bad : Realization (singleObservation P X Y)) (hbad : ¬ law bad) :
    Sensitivity ⟨singleObservation P X Y, law⟩ actual := by
  constructor
  · intro i
    refine ⟨bad, ?_, ?_, hbad⟩
    · intro j h
      exact (h (show j = i from @Subsingleton.elim Unit _ j i)).elim
    · funext e
      exact nomatch e
  · intro i
    exact nomatch i

open _root_.D5.S1.Words.Patterns.CyclicStackPreimages

/-- Fibre words retain the complete input length, independently of enumeration. -/
theorem fibre_distinct_of_member {m n : ℕ} {word : List ℕ}
    (hmem : word ∈ fibre m) (hlen : word.length ≠ n) : fibre m ≠ fibre n := by
  intro h
  rw [h] at hmem
  have hp := List.mem_permutations.mp (List.mem_filter.mp hmem).1
  exact hlen (by simpa using hp.length_eq)

end Reg.Support.CyclicStackFamily
