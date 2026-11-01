/- GID: D5/S3/Quantum/Entanglement/EJM/Replay/Cut00000/Parts/PreparedEJMCompleteRawCut00000Part000040
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/Replay/Cut00000/Parts/PreparedEJMCompleteRawCut00000Part000040
   mirror-E: none(waiver:exact-original-context-mathematical-source)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Quantum/Entanglement/EJM/PreparedEJMCompleteFrontierRoot.original_score_lower_bound; premises=D5/S3/Quantum/Entanglement/EJM/Replay/Cut00000/Parts/PreparedEJMCompleteRawCut00000Part000040.node_16_212,D5/S3/Quantum/Entanglement/EJM/Replay/Cut00000/Parts/PreparedEJMCompleteRawCut00000Part000040.accepted_16_22_212
   digest: Exact original cached replay is checked at the stated prefix occurrences. -/

/- Prepared exact original-context source; not kernel accepted.
Partition counts are not theorem premises. All original coordinates,
four values, coefficient functions, actual prefixes and child edges remain. -/
import D5.S3.Quantum.Entanglement.EJM.EJMOriginalReplayAssembly
import D5.S3.Quantum.Entanglement.EJM.Replay.Cut00000.Parts.PreparedEJMCompleteRawCut00000Part000036
import D5.S3.Quantum.Entanglement.EJM.Replay.Cut00000.Parts.PreparedEJMCompleteRawCut00000Part000037
import D5.S3.Quantum.Entanglement.EJM.Replay.Cut00000.Parts.PreparedEJMCompleteRawCut00000Part000038
import D5.S3.Quantum.Entanglement.EJM.Replay.Cut00000.Parts.PreparedEJMCompleteRawCut00000Part000039
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
