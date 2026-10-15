/- Prepared exact original-context source; not kernel accepted.
Partition counts are not theorem premises. All original coordinates,
four values, coefficient functions, actual prefixes and child edges remain. -/
import D5.S3.Quantum.Entanglement.EJM.EJMOriginalReplayAssembly
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteRawCut00000Part000031
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteRawCut00000Part000032
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteRawCut00000Part000033
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteRawCut00000Part000034
import Mathlib.Tactic.FinCases
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteRawCut00000
open EJMOriginalReplayAssembly
open D5.S0.Certificates.FiniteCachedSymmetryDAGReplay (checked_split_node)

theorem node_16_165 : EJMOriginalGlobalDAGData.nodes 5 ⟨165, by decide⟩ =
    .split (EJMOriginalReplayAssembly.coordinate 16) (![⟨155, by decide⟩,⟨159, by decide⟩,⟨164, by decide⟩,⟨29, by decide⟩]) := by
  apply checked_split_node
  decide +kernel

theorem accepted_16_21_165 : Accepted 16 21 ⟨165, by decide⟩ := by
  apply assemble 16 21 ⟨165, by decide⟩ (by decide) (![⟨155, by decide⟩,⟨159, by decide⟩,⟨164, by decide⟩,⟨29, by decide⟩]) node_16_165
  intro a
  fin_cases a
  · exact accepted_17_84_155
  · exact accepted_17_85_159
  · exact accepted_17_86_164
  · exact accepted_17_87_29

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteRawCut00000
