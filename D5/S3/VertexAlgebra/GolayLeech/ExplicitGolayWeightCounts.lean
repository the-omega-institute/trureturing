/- GID: D5/S3/VertexAlgebra/GolayLeech/ExplicitGolayWeightCounts
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/GolayLeech/ExplicitGolayWeightCounts
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The actual Golay code has exact weight counts one, seven-hundred-fifty-nine, and two-thousand-five-hundred-seventy-six. -/
import D5.S3.VertexAlgebra.GolayLeech.ExplicitGolayEnumerator
set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace D5.S3.VertexAlgebra.GolayLeech.ExplicitGolayWeightCounts
open ExplicitGolayCode ExplicitGolayCertificates ExplicitGolayWeights ExplicitGolayEnumerator
open scoped BigOperators

theorem finite_row_counts : ∀ lower : Fin 64, ∀ category : Fin 5,
    packedEnumerateRow lower category = rowCertificate lower category := by
  intro lower category
  fin_cases lower <;> fin_cases category <;> decide

theorem finite_weight_choices : ∀ pair : Fin 64 × Fin 64,
    packedWeight (bitsAt pair) ∈ ({0, 8, 12, 16, 24} : Finset ℕ) := by decide

theorem exact_weight_enumerator : ∀ category : Fin 5,
    enumerate category = (![1, 759, 2576, 759, 1] : Fin 5 → ℕ) category := by
  intro category
  have rows : ∀ lower : Fin 64,
      (∑ upper : Fin 64, if weight (wordAt (lower, upper)) = weightValues category then 1 else 0) =
        rowCertificate lower category := by
    intro lower
    simp_rw [word_weight_identity]
    exact finite_row_counts lower category
  simp only [enumerate]
  simp_rw [rows]
  have checked : ∀ category : Fin 5,
      (∑ lower : Fin 64, rowCertificate lower category) =
        (![1, 759, 2576, 759, 1] : Fin 5 → ℕ) category := by decide
  exact checked category

end D5.S3.VertexAlgebra.GolayLeech.ExplicitGolayWeightCounts
