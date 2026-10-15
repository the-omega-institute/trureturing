/- Prepared exact original-context source; not kernel accepted.
Partition counts are not theorem premises. All original coordinates,
four values, coefficient functions, actual prefixes and child edges remain. -/
import D5.S3.Quantum.Entanglement.EJM.EJMOriginalReplayAssembly
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteRawCut00000Part000068
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteRawCut00000Part000069
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteRawCut00000Part000070
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteRawCut00000Part000071
import Mathlib.Tactic.FinCases
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteRawCut00000
open EJMOriginalReplayAssembly
open D5.S0.Certificates.FiniteCachedSymmetryDAGReplay (checked_split_node)

theorem node_15_376 : EJMOriginalGlobalDAGData.nodes 6 ⟨376, by decide⟩ =
    .split (EJMOriginalReplayAssembly.coordinate 15) (![⟨111, by decide⟩,⟨56, by decide⟩,⟨355, by decide⟩,⟨375, by decide⟩]) := by
  apply checked_split_node
  decide +kernel

theorem accepted_15_22_376 : Accepted 15 22 ⟨376, by decide⟩ := by
  apply assemble 15 22 ⟨376, by decide⟩ (by decide) (![⟨111, by decide⟩,⟨56, by decide⟩,⟨355, by decide⟩,⟨375, by decide⟩]) node_15_376
  intro a
  fin_cases a
  · exact accepted_16_88_111
  · exact accepted_16_89_56
  · exact accepted_16_90_355
  · exact accepted_16_91_375

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteRawCut00000
