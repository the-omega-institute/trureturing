/- GID: D5/S3/QuantumChannels/ContractionGeometry/SubmultiplicativeLogRate
   generality: G
   mirror-B: D5/B/S3/QuantumChannels/ContractionGeometry/SubmultiplicativeLogRate
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Positive submultiplicative profiles have a unique finite logarithmic rate. -/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Subadditive

open Filter Set

namespace D5.S3.QuantumChannels.ContractionGeometry.SubmultiplicativeLogRate

/- Pinned Mathlib supplies Fekete's lemma as `Subadditive.tendsto_lim`. The logarithmic
bridge uses `Real.log_le_log` and `Real.log_mul`. -/

/-- A positive submultiplicative profile whose normalized logarithm is bounded below has a
unique finite logarithmic asymptotic rate. -/
theorem submultiplicative_profile_has_unique_log_rate
    (eta : Nat -> Real)
    (positive : forall n, 0 < eta n)
    (submultiplicative : forall m n, eta (m + n) <= eta m * eta n)
    (boundedBelow : BddBelow (range fun n => Real.log (eta n) / n)) :
    ∃! gamma : Real,
      Tendsto (fun n => Real.log (eta n) / n) atTop (nhds gamma) := by
  have logSubadditive : Subadditive (fun n => Real.log (eta n)) := by
    intro m n
    calc
      Real.log (eta (m + n)) <= Real.log (eta m * eta n) :=
        Real.log_le_log (positive (m + n)) (submultiplicative m n)
      _ = Real.log (eta m) + Real.log (eta n) :=
        Real.log_mul (ne_of_gt (positive m)) (ne_of_gt (positive n))
  have converges := logSubadditive.tendsto_lim boundedBelow
  refine ⟨logSubadditive.lim, converges, ?_⟩
  intro gamma hgamma
  exact tendsto_nhds_unique hgamma converges

#print axioms submultiplicative_profile_has_unique_log_rate

end D5.S3.QuantumChannels.ContractionGeometry.SubmultiplicativeLogRate
