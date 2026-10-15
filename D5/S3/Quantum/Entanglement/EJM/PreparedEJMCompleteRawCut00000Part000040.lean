/- Prepared exact original-context source; not kernel accepted.
Partition counts are not theorem premises. All original coordinates,
four values, coefficient functions, actual prefixes and child edges remain. -/
import D5.S3.Quantum.Entanglement.EJM.EJMOriginalReplayAssembly
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteRawCut00000Part000036
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteRawCut00000Part000037
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteRawCut00000Part000038
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteRawCut00000Part000039
import Mathlib.Tactic.FinCases
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteRawCut00000
open EJMOriginalReplayAssembly
open D5.S0.Certificates.FiniteCachedSymmetryDAGReplay (checked_split_node)

theorem node_16_212 : EJMOriginalGlobalDAGData.nodes 5 ⟨212, by decide⟩ =
    .split (EJMOriginalReplayAssembly.coordinate 16) (![⟨174, by decide⟩,⟨184, by decide⟩,⟨194, by decide⟩,⟨211, by decide⟩]) := by
  apply checked_split_node
  decide +kernel

theorem accepted_16_22_212 : Accepted 16 22 ⟨212, by decide⟩ := by
  apply assemble 16 22 ⟨212, by decide⟩ (by decide) (![⟨174, by decide⟩,⟨184, by decide⟩,⟨194, by decide⟩,⟨211, by decide⟩]) node_16_212
  intro a
  fin_cases a
  · exact accepted_17_88_174
  · exact accepted_17_89_184
  · exact accepted_17_90_194
  · exact accepted_17_91_211

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteRawCut00000
