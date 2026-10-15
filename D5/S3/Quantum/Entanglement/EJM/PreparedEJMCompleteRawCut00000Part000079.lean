/- Prepared exact original-context source; not kernel accepted.
Partition counts are not theorem premises. All original coordinates,
four values, coefficient functions, actual prefixes and child edges remain. -/
import D5.S3.Quantum.Entanglement.EJM.EJMOriginalReplayAssembly
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteRawCut00000Part000075
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteRawCut00000Part000076
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteRawCut00000Part000077
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteRawCut00000Part000078
import Mathlib.Tactic.FinCases
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteRawCut00000
open EJMOriginalReplayAssembly
open D5.S0.Certificates.FiniteCachedSymmetryDAGReplay (checked_split_node)

theorem node_14_411 : EJMOriginalGlobalDAGData.nodes 7 ⟨411, by decide⟩ =
    .split (EJMOriginalReplayAssembly.coordinate 14) (![⟨378, by decide⟩,⟨407, by decide⟩,⟨378, by decide⟩,⟨410, by decide⟩]) := by
  apply checked_split_node
  decide +kernel

theorem accepted_14_6_411 : Accepted 14 6 ⟨411, by decide⟩ := by
  apply assemble 14 6 ⟨411, by decide⟩ (by decide) (![⟨378, by decide⟩,⟨407, by decide⟩,⟨378, by decide⟩,⟨410, by decide⟩]) node_14_411
  intro a
  fin_cases a
  · exact accepted_15_24_378
  · exact accepted_15_25_407
  · exact accepted_15_26_378
  · exact accepted_15_27_410

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteRawCut00000
