/- GID: D5/S3/Quantum/Entanglement/EJM/Frontier/Raw/Part004/PreparedEJMCompleteFrontierRaw413
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/Frontier/Raw/Part004/PreparedEJMCompleteFrontierRaw413
   mirror-E: none(waiver:exact-original-context-mathematical-source)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Quantum/Entanglement/EJM/PreparedEJMCompleteFrontierRoot.original_score_lower_bound; premises=D5/S3/Quantum/Entanglement/EJM/Frontier/Raw/Part004/PreparedEJMCompleteFrontierRaw413.response_cut_52864,D5/S3/Quantum/Entanglement/EJM/Frontier/Raw/Part004/PreparedEJMCompleteFrontierRaw413.response_cut_52865,D5/S3/Quantum/Entanglement/EJM/Frontier/Raw/Part004/PreparedEJMCompleteFrontierRaw413.response_cut_52866
   digest: Each original cut receives its own canonical-cache suffix check or a semantic score bound. -/

/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierTypes
import D5.S3.Quantum.Entanglement.EJM.EJMOriginalNodeMemo
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem raw_cut_52864 : EJMOriginalReplayAssembly.Accepted 1 1 ⟨1558773, by decide⟩ := by
  unfold EJMOriginalReplayAssembly.Accepted
  exact (EJMOriginalNodeMemo.check_eq_original
    (21 - 1) ⟨1558773, by decide⟩
    (prefixCache 1 1) (prefixPartial 1 1)).symm.trans (by
      decide +kernel)

theorem response_cut_52864 : CanonicalResponse ⟨1, 1, 0, 1558773, 1, 1, 274877906944⟩ :=
  response_of_raw ⟨1, 1, 0, 1558773, 1, 1, 274877906944⟩ (by decide) (by decide) raw_cut_52864

theorem raw_cut_52865 : EJMOriginalReplayAssembly.Accepted 1 2 ⟨1558774, by decide⟩ := by
  unfold EJMOriginalReplayAssembly.Accepted
  exact (EJMOriginalNodeMemo.check_eq_original
    (21 - 1) ⟨1558774, by decide⟩
    (prefixCache 1 2) (prefixPartial 1 2)).symm.trans (by
      decide +kernel)

theorem response_cut_52865 : CanonicalResponse ⟨1, 1, 0, 1558774, 2, 1, 274877906944⟩ :=
  response_of_raw ⟨1, 1, 0, 1558774, 2, 1, 274877906944⟩ (by decide) (by decide) raw_cut_52865

theorem raw_cut_52866 : EJMOriginalReplayAssembly.Accepted 1 3 ⟨1558775, by decide⟩ := by
  unfold EJMOriginalReplayAssembly.Accepted
  exact (EJMOriginalNodeMemo.check_eq_original
    (21 - 1) ⟨1558775, by decide⟩
    (prefixCache 1 3) (prefixPartial 1 3)).symm.trans (by
      decide +kernel)

theorem response_cut_52866 : CanonicalResponse ⟨1, 1, 0, 1558775, 3, 1, 274877906944⟩ :=
  response_of_raw ⟨1, 1, 0, 1558775, 3, 1, 274877906944⟩ (by decide) (by decide) raw_cut_52866

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
