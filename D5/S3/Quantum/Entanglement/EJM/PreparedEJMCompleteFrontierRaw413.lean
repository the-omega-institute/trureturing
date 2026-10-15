/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierTypes
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem raw_cut_52864 : EJMOriginalReplayAssembly.Accepted 1 1 ⟨1558773, by decide⟩ := by
  unfold EJMOriginalReplayAssembly.Accepted
  decide +kernel

theorem response_cut_52864 : CanonicalResponse ⟨1, 1, 0, 1558773, 1, 1, 274877906944⟩ :=
  response_of_raw ⟨1, 1, 0, 1558773, 1, 1, 274877906944⟩ (by decide) (by decide) raw_cut_52864

theorem raw_cut_52865 : EJMOriginalReplayAssembly.Accepted 1 2 ⟨1558774, by decide⟩ := by
  unfold EJMOriginalReplayAssembly.Accepted
  decide +kernel

theorem response_cut_52865 : CanonicalResponse ⟨1, 1, 0, 1558774, 2, 1, 274877906944⟩ :=
  response_of_raw ⟨1, 1, 0, 1558774, 2, 1, 274877906944⟩ (by decide) (by decide) raw_cut_52865

theorem raw_cut_52866 : EJMOriginalReplayAssembly.Accepted 1 3 ⟨1558775, by decide⟩ := by
  unfold EJMOriginalReplayAssembly.Accepted
  decide +kernel

theorem response_cut_52866 : CanonicalResponse ⟨1, 1, 0, 1558775, 3, 1, 274877906944⟩ :=
  response_of_raw ⟨1, 1, 0, 1558775, 3, 1, 274877906944⟩ (by decide) (by decide) raw_cut_52866

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
