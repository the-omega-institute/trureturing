/- Prepared exact original-context source; not kernel accepted.
Partition counts are not theorem premises. All original coordinates,
four values, coefficient functions, actual prefixes and child edges remain. -/
import D5.S3.Quantum.Entanglement.EJM.EJMOriginalReplayAssembly
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteRawCut00000Part000044
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteRawCut00000Part000045
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteRawCut00000Part000046
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteRawCut00000Part000047
import Mathlib.Tactic.FinCases
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteRawCut00000
open EJMOriginalReplayAssembly
open D5.S0.Certificates.FiniteCachedSymmetryDAGReplay (checked_split_node)

theorem node_16_246 : EJMOriginalGlobalDAGData.nodes 5 ⟨246, by decide⟩ =
    .split (EJMOriginalReplayAssembly.coordinate 16) (![⟨227, by decide⟩,⟨230, by decide⟩,⟨236, by decide⟩,⟨245, by decide⟩]) := by
  apply checked_split_node
  decide +kernel

theorem accepted_16_25_246 : Accepted 16 25 ⟨246, by decide⟩ := by
  apply assemble 16 25 ⟨246, by decide⟩ (by decide) (![⟨227, by decide⟩,⟨230, by decide⟩,⟨236, by decide⟩,⟨245, by decide⟩]) node_16_246
  intro a
  fin_cases a
  · exact accepted_17_100_227
  · exact accepted_17_101_230
  · exact accepted_17_102_236
  · exact accepted_17_103_245

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteRawCut00000
