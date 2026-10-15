/- GID: D5/S3/VertexAlgebra/GolayLeech/ExplicitGolayWeights
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/GolayLeech/ExplicitGolayWeights
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite kernel certificates give universal Golay weight bounds. -/
import D5.S3.VertexAlgebra.GolayLeech.ExplicitGolayCertificates

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace D5.S3.VertexAlgebra.GolayLeech.ExplicitGolayWeights
open ExplicitGolayCode ExplicitGolayCertificates

 theorem finite_prefix_surjectivity :
    ∀ lowerHalf : Fin 6 → Binary, ∃ block : Fin 64, packedPrefix block = lowerHalf := by
  decide

 theorem finite_weight_constraints :
    ∀ message : Message, weight (encode message) % 4 = 0 ∧
      (encode message ≠ 0 → 8 ≤ weight (encode message)) := by
  intro message
  let lowerHalf : Fin 6 → Binary := fun position => message ⟨position.val, by omega⟩
  let tail : Fin 6 → Binary := fun position => message ⟨position.val + 6, by omega⟩
  obtain ⟨block, equality⟩ := finite_prefix_surjectivity lowerHalf
  have eta : message = joinedMessage (packedPrefix block) tail := by
    rw [equality]
    ext position
    fin_cases position <;> rfl
  rw [eta]
  exact certified_blocks block tail

 theorem code_doubly_even (word : Word) (member : word ∈ code) :
    weight word % 4 = 0 := by
  obtain ⟨message, rfl⟩ := member
  exact (finite_weight_constraints message).1

 theorem code_minimum_weight (word : Word) (member : word ∈ code) (nonzero : word ≠ 0) :
    8 ≤ weight word := by
  obtain ⟨message, rfl⟩ := member
  exact (finite_weight_constraints message).2 nonzero

end D5.S3.VertexAlgebra.GolayLeech.ExplicitGolayWeights
