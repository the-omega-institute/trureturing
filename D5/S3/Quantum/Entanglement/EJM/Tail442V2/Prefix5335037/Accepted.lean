/- GID: D5/S3/Quantum/Entanglement/EJM/Tail442V2/Prefix5335037/Accepted
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/Tail442V2/Prefix5335037/Accepted
   mirror-E: none(waiver:exact-original-context-mathematical-source)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Quantum/Entanglement/EJM/Frontier/Raw/Part000/Raw002Tail442/Assembly.raw_cut_00337; premises=D5/S3/Quantum/Entanglement/EJM/Tail442V2/Prefix5335037/Accepted.all_steps,D5/S3/Quantum/Entanglement/EJM/Tail442V2/Prefix5335037/Accepted.all_bounds,D5/S3/Quantum/Entanglement/EJM/Tail442V2/Prefix5335037/Accepted.literal_context,D5/S3/Quantum/Entanglement/EJM/Tail442V2/Prefix5335037/Accepted.accepted
   digest: This prefix's own full prefix-cache equality, four whole-cache steps and four lower inequalities retain its exact original Accepted statement. -/

/- Source-only complete Tail442 checkpoint candidate. Kernel acceptance pending. -/
import D5.S3.Quantum.Entanglement.EJM.Tail442V2.Prefix5335037.Parent
import D5.S3.Quantum.Entanglement.EJM.Tail442V2.Prefix5335037.Branch0
import D5.S3.Quantum.Entanglement.EJM.Tail442V2.Prefix5335037.Branch1
import D5.S3.Quantum.Entanglement.EJM.Tail442V2.Prefix5335037.Branch2
import D5.S3.Quantum.Entanglement.EJM.Tail442V2.Prefix5335037.Branch3

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.longLine false

namespace D5.S3.Quantum.Entanglement.EJM.Tail442V2.Prefix5335037
open EJMCacheState (Cache triangleStep singletonStep step lower)
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
open EJMPartialBoundData (scale)
open Tail442V2.Helper
open D5.S0.Certificates.FiniteCachedSymmetryDAGReplay (check)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem all_steps : ∀ a, step parentCache (coordinate 18) a = nextCache a := by
  intro a
  fin_cases a
  · exact branch0_step
  · exact branch1_step
  · exact branch2_step
  · exact branch3_step

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem all_bounds : ∀ a, scale ≤ lower (nextCache a) := by
  intro a
  fin_cases a
  · exact branch0_bound
  · exact branch1_bound
  · exact branch2_bound
  · exact branch3_bound

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem literal_context :
    check EJMOriginalGlobalDAGData.nodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨442, by decide⟩ parentCache (prefixPartial 18 5335037) = true :=
  tail442 parentCache (prefixPartial 18 5335037) nextCache all_steps all_bounds

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem accepted : EJMOriginalReplayAssembly.Accepted 18 5335037 ⟨442, by decide⟩ := by
  unfold EJMOriginalReplayAssembly.Accepted
  rw [← parent_exact]
  exact literal_context

#print axioms parent_exact
#print axioms all_steps
#print axioms all_bounds
#print axioms literal_context
#print axioms accepted

end D5.S3.Quantum.Entanglement.EJM.Tail442V2.Prefix5335037
