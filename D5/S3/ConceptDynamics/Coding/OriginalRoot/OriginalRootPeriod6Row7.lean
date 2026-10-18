import D5.S3.ConceptDynamics.Coding.OriginalRoot.OriginalRootPeriod6Base

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace D5.S3.ConceptDynamics.Coding

set_option maxHeartbeats 12000000 in
set_option maxRecDepth 100000 in
theorem onePlusShardLeaf_eq_value_row7 (j k : Fin 8) :
    onePlusShardLeaf 7 j k = onePlusChunkValue 7 j k := by
  fin_cases j <;> fin_cases k <;>
    first
    | apply onePlusShardLeaf_eq_zero_of_middle_empty <;> decide
    | apply onePlusShardLeaf_eq_zero_of_source_pair <;> decide
    | decide +kernel

end D5.S3.ConceptDynamics.Coding
