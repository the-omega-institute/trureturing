/- Prepared exact original-context source; not kernel accepted.
Partition counts are not theorem premises. All original coordinates,
four values, coefficient functions, actual prefixes and child edges remain. -/
import D5.S3.Quantum.Entanglement.EJM.EJMOriginalReplayAssembly
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteRawCut00000Part000063
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteRawCut00000Part000064
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteRawCut00000Part000065
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteRawCut00000Part000066
import Mathlib.Tactic.FinCases
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteRawCut00000
open EJMOriginalReplayAssembly
open D5.S0.Certificates.FiniteCachedSymmetryDAGReplay (checked_split_node)

theorem node_15_330 : EJMOriginalGlobalDAGData.nodes 6 ⟨330, by decide⟩ =
    .split (EJMOriginalReplayAssembly.coordinate 15) (![⟨111, by decide⟩,⟨306, by decide⟩,⟨329, by decide⟩,⟨54, by decide⟩]) := by
  apply checked_split_node
  decide +kernel

theorem accepted_15_21_330 : Accepted 15 21 ⟨330, by decide⟩ := by
  apply assemble 15 21 ⟨330, by decide⟩ (by decide) (![⟨111, by decide⟩,⟨306, by decide⟩,⟨329, by decide⟩,⟨54, by decide⟩]) node_15_330
  intro a
  fin_cases a
  · exact accepted_16_84_111
  · exact accepted_16_85_306
  · exact accepted_16_86_329
  · exact accepted_16_87_54

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteRawCut00000
