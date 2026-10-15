/- Prepared exact original-context source; not kernel accepted.
Partition counts are not theorem premises. All original coordinates,
four values, coefficient functions, actual prefixes and child edges remain. -/
import D5.S3.Quantum.Entanglement.EJM.EJMOriginalReplayAssembly
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteRawCut00000Part000000
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteRawCut00000Part000005
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteRawCut00000Part000006
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteRawCut00000Part000007
import Mathlib.Tactic.FinCases
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteRawCut00000
open EJMOriginalReplayAssembly
open D5.S0.Certificates.FiniteCachedSymmetryDAGReplay (checked_split_node)

theorem node_15_55 : EJMOriginalGlobalDAGData.nodes 6 ⟨55, by decide⟩ =
    .split (EJMOriginalReplayAssembly.coordinate 15) (![⟨30, by decide⟩,⟨52, by decide⟩,⟨53, by decide⟩,⟨54, by decide⟩]) := by
  apply checked_split_node
  decide +kernel

theorem accepted_15_0_55 : Accepted 15 0 ⟨55, by decide⟩ := by
  apply assemble 15 0 ⟨55, by decide⟩ (by decide) (![⟨30, by decide⟩,⟨52, by decide⟩,⟨53, by decide⟩,⟨54, by decide⟩]) node_15_55
  intro a
  fin_cases a
  · exact accepted_16_0_30
  · exact accepted_16_1_52
  · exact accepted_16_2_53
  · exact accepted_16_3_54

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteRawCut00000
