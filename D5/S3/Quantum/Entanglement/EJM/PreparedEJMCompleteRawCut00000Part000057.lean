/- Prepared exact original-context source; not kernel accepted.
Partition counts are not theorem premises. All original coordinates,
four values, coefficient functions, actual prefixes and child edges remain. -/
import D5.S3.Quantum.Entanglement.EJM.EJMOriginalReplayAssembly
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteRawCut00000Part000029
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteRawCut00000Part000042
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteRawCut00000Part000055
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteRawCut00000Part000056
import Mathlib.Tactic.FinCases
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteRawCut00000
open EJMOriginalReplayAssembly
open D5.S0.Certificates.FiniteCachedSymmetryDAGReplay (checked_split_node)

theorem node_14_289 : EJMOriginalGlobalDAGData.nodes 7 ⟨289, by decide⟩ =
    .split (EJMOriginalReplayAssembly.coordinate 14) (![⟨151, by decide⟩,⟨213, by decide⟩,⟨288, by decide⟩,⟨109, by decide⟩]) := by
  apply checked_split_node
  decide +kernel

theorem accepted_14_1_289 : Accepted 14 1 ⟨289, by decide⟩ := by
  apply assemble 14 1 ⟨289, by decide⟩ (by decide) (![⟨151, by decide⟩,⟨213, by decide⟩,⟨288, by decide⟩,⟨109, by decide⟩]) node_14_289
  intro a
  fin_cases a
  · exact accepted_15_4_151
  · exact accepted_15_5_213
  · exact accepted_15_6_288
  · exact accepted_15_7_109

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteRawCut00000
