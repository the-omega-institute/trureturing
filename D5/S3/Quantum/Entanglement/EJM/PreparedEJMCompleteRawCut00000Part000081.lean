/- Prepared exact original-context source; not kernel accepted.
Partition counts are not theorem premises. All original coordinates,
four values, coefficient functions, actual prefixes and child edges remain. -/
import D5.S3.Quantum.Entanglement.EJM.EJMOriginalReplayAssembly
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteRawCut00000Part000061
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteRawCut00000Part000074
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteRawCut00000Part000079
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteRawCut00000Part000080
import Mathlib.Tactic.FinCases
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteRawCut00000
open EJMOriginalReplayAssembly
open D5.S0.Certificates.FiniteCachedSymmetryDAGReplay (checked_split_node)

theorem node_13_412 : EJMOriginalGlobalDAGData.nodes 8 ⟨412, by decide⟩ =
    .split (EJMOriginalReplayAssembly.coordinate 13) (![⟨293, by decide⟩,⟨377, by decide⟩,⟨411, by decide⟩,⟨291, by decide⟩]) := by
  apply checked_split_node
  decide +kernel

theorem accepted_13_1_412 : Accepted 13 1 ⟨412, by decide⟩ := by
  apply assemble 13 1 ⟨412, by decide⟩ (by decide) (![⟨293, by decide⟩,⟨377, by decide⟩,⟨411, by decide⟩,⟨291, by decide⟩]) node_13_412
  intro a
  fin_cases a
  · exact accepted_14_4_293
  · exact accepted_14_5_377
  · exact accepted_14_6_411
  · exact accepted_14_7_291

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteRawCut00000
