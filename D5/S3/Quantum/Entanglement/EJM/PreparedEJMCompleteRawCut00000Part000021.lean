/- Prepared exact original-context source; not kernel accepted.
Partition counts are not theorem premises. All original coordinates,
four values, coefficient functions, actual prefixes and child edges remain. -/
import D5.S3.Quantum.Entanglement.EJM.EJMOriginalReplayAssembly
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteRawCut00000Part000009
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteRawCut00000Part000014
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteRawCut00000Part000019
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteRawCut00000Part000020
import Mathlib.Tactic.FinCases
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteRawCut00000
open EJMOriginalReplayAssembly
open D5.S0.Certificates.FiniteCachedSymmetryDAGReplay (checked_split_node)

theorem node_15_107 : EJMOriginalGlobalDAGData.nodes 6 ⟨107, by decide⟩ =
    .split (EJMOriginalReplayAssembly.coordinate 15) (![⟨56, by decide⟩,⟨77, by decide⟩,⟨106, by decide⟩,⟨54, by decide⟩]) := by
  apply checked_split_node
  decide +kernel

theorem accepted_15_1_107 : Accepted 15 1 ⟨107, by decide⟩ := by
  apply assemble 15 1 ⟨107, by decide⟩ (by decide) (![⟨56, by decide⟩,⟨77, by decide⟩,⟨106, by decide⟩,⟨54, by decide⟩]) node_15_107
  intro a
  fin_cases a
  · exact accepted_16_4_56
  · exact accepted_16_5_77
  · exact accepted_16_6_106
  · exact accepted_16_7_54

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteRawCut00000
