/- Prepared exact original-context source; not kernel accepted.
Partition counts are not theorem premises. All original coordinates,
four values, coefficient functions, actual prefixes and child edges remain. -/
import D5.S3.Quantum.Entanglement.EJM.EJMOriginalReplayAssembly
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteRawCut00000Part000043
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteRawCut00000Part000048
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteRawCut00000Part000049
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteRawCut00000Part000054
import Mathlib.Tactic.FinCases
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteRawCut00000
open EJMOriginalReplayAssembly
open D5.S0.Certificates.FiniteCachedSymmetryDAGReplay (checked_split_node)

theorem node_15_288 : EJMOriginalGlobalDAGData.nodes 6 ⟨288, by decide⟩ =
    .split (EJMOriginalReplayAssembly.coordinate 15) (![⟨111, by decide⟩,⟨246, by decide⟩,⟨247, by decide⟩,⟨287, by decide⟩]) := by
  apply checked_split_node
  decide +kernel

theorem accepted_15_6_288 : Accepted 15 6 ⟨288, by decide⟩ := by
  apply assemble 15 6 ⟨288, by decide⟩ (by decide) (![⟨111, by decide⟩,⟨246, by decide⟩,⟨247, by decide⟩,⟨287, by decide⟩]) node_15_288
  intro a
  fin_cases a
  · exact accepted_16_24_111
  · exact accepted_16_25_246
  · exact accepted_16_26_247
  · exact accepted_16_27_287

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteRawCut00000
