/- Prepared exact original-context source; not kernel accepted.
Partition counts are not theorem premises. All original coordinates,
four values, coefficient functions, actual prefixes and child edges remain. -/
import D5.S3.Quantum.Entanglement.EJM.EJMOriginalReplayAssembly
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteRawCut00000Part000062
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteRawCut00000Part000067
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteRawCut00000Part000072
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteRawCut00000Part000073
import Mathlib.Tactic.FinCases
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteRawCut00000
open EJMOriginalReplayAssembly
open D5.S0.Certificates.FiniteCachedSymmetryDAGReplay (checked_split_node)

theorem node_14_377 : EJMOriginalGlobalDAGData.nodes 7 ⟨377, by decide⟩ =
    .split (EJMOriginalReplayAssembly.coordinate 14) (![⟨294, by decide⟩,⟨330, by decide⟩,⟨376, by decide⟩,⟨109, by decide⟩]) := by
  apply checked_split_node
  decide +kernel

theorem accepted_14_5_377 : Accepted 14 5 ⟨377, by decide⟩ := by
  apply assemble 14 5 ⟨377, by decide⟩ (by decide) (![⟨294, by decide⟩,⟨330, by decide⟩,⟨376, by decide⟩,⟨109, by decide⟩]) node_14_377
  intro a
  fin_cases a
  · exact accepted_15_20_294
  · exact accepted_15_21_330
  · exact accepted_15_22_376
  · exact accepted_15_23_109

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteRawCut00000
