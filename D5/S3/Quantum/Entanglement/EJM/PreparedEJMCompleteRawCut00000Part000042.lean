/- Prepared exact original-context source; not kernel accepted.
Partition counts are not theorem premises. All original coordinates,
four values, coefficient functions, actual prefixes and child edges remain. -/
import D5.S3.Quantum.Entanglement.EJM.EJMOriginalReplayAssembly
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteRawCut00000Part000030
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteRawCut00000Part000035
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteRawCut00000Part000040
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteRawCut00000Part000041
import Mathlib.Tactic.FinCases
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteRawCut00000
open EJMOriginalReplayAssembly
open D5.S0.Certificates.FiniteCachedSymmetryDAGReplay (checked_split_node)

theorem node_15_213 : EJMOriginalGlobalDAGData.nodes 6 ⟨213, by decide⟩ =
    .split (EJMOriginalReplayAssembly.coordinate 15) (![⟨111, by decide⟩,⟨165, by decide⟩,⟨212, by decide⟩,⟨54, by decide⟩]) := by
  apply checked_split_node
  decide +kernel

theorem accepted_15_5_213 : Accepted 15 5 ⟨213, by decide⟩ := by
  apply assemble 15 5 ⟨213, by decide⟩ (by decide) (![⟨111, by decide⟩,⟨165, by decide⟩,⟨212, by decide⟩,⟨54, by decide⟩]) node_15_213
  intro a
  fin_cases a
  · exact accepted_16_20_111
  · exact accepted_16_21_165
  · exact accepted_16_22_212
  · exact accepted_16_23_54

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteRawCut00000
