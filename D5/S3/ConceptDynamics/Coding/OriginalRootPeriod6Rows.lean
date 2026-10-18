import D5.S3.ConceptDynamics.Coding.OriginalRootPeriod6Row0
import D5.S3.ConceptDynamics.Coding.OriginalRootPeriod6Row1
import D5.S3.ConceptDynamics.Coding.OriginalRootPeriod6Row2
import D5.S3.ConceptDynamics.Coding.OriginalRootPeriod6Row3
import D5.S3.ConceptDynamics.Coding.OriginalRootPeriod6Row4
import D5.S3.ConceptDynamics.Coding.OriginalRootPeriod6Row5
import D5.S3.ConceptDynamics.Coding.OriginalRootPeriod6Row6
import D5.S3.ConceptDynamics.Coding.OriginalRootPeriod6Row7

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace D5.S3.ConceptDynamics.Coding

theorem onePlusShardLeaf_eq_value (i j k : Fin 8) :
    onePlusShardLeaf i j k = onePlusChunkValue i j k := by
  fin_cases i
  · exact onePlusShardLeaf_eq_value_row0 j k
  · exact onePlusShardLeaf_eq_value_row1 j k
  · exact onePlusShardLeaf_eq_value_row2 j k
  · exact onePlusShardLeaf_eq_value_row3 j k
  · exact onePlusShardLeaf_eq_value_row4 j k
  · exact onePlusShardLeaf_eq_value_row5 j k
  · exact onePlusShardLeaf_eq_value_row6 j k
  · exact onePlusShardLeaf_eq_value_row7 j k

end D5.S3.ConceptDynamics.Coding
