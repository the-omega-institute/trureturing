/- GID: D5/S3/Arith/FibonacciAtomic/Observer/ActualObserverPrefixRigidity
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Cross-source actual-prefix replay and terminating shared-state raw-history rigidity. -/

import D5.S3.Arith.FibonacciAtomic.Observer.ActualObserverBoundedLowerBounds
import D5.S3.Arith.FibonacciAtomic.Observer.ActualExactSupportPruning

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.Observer.ActualObserverPrefixRigidity

universe u
open GenealogicalFiberTransport (Source)
open ActualTreeReadoutAcquisition (Address Reply readout paid)
open ActualFiniteObserverAbsentElimination
open ActualObserverBoundedLowerBounds (prefix_cache_spectrum)
open ActualExactSupportPruning (prefix_run_tail)

variable {E : Type u} [Fintype E]

/-- Agreement only on the paid prefix replays every logical request, including
hits, at exactly the same complete rows. No legality or termination is assumed. -/
theorem actualPrefix_replay (M : Observer E) (U V : Source)
    {e : E} {h : RawHistory} (pref : ActualPrefix M U e h)
    (agree : ∀ q ∈ paid h, readout q V = readout q U) :
    ActualPrefix M V e h := by
  induction pref with
  | initial => exact .initial
  | @query e h q prior row ih =>
      have old := ih (fun r hr => agree r (by
        simpa [paid, List.map_append] using Or.inr hr))
      have head : q ∈ paid (h ++ [⟨q, queryReply (M.decoder e) q U⟩]) := by
        simp [paid, List.map_append]
      have reply : queryReply (M.decoder e) q V = queryReply (M.decoder e) q U := by
        unfold queryReply
        cases (M.decoder e).find? (fun a => a.1 == q) with
        | none => exact agree q head
        | some a => rfl
      simpa only [reply] using ActualPrefix.query old row

/-- A persistent truthful common cache and one terminating run make the raw
actual history unique at a shared complete state. Only the second source needs
a terminating run; arbitrary counterfactual words are outside this statement. -/
theorem actualPrefix_history_rigid (M : Observer E) (U V : Source)
    (legalU : Legal M U) {e : E} {h h' t : RawHistory} {f : E} {b : Bool}
    (hu : ActualPrefix M U e h) (hv : ActualPrefix M V e h')
    (truthV : CacheTruth (M.decoder e) V) (runV : Run M V M.e0 t f b) :
    h = h' := by
  have support := (prefix_cache_spectrum M U legalU hu).1
  have agree : ∀ q ∈ paid h, readout q V = readout q U := by
    intro q member
    have cached : q ∈ paid (M.decoder e) := by rwa [support]
    obtain ⟨a, ha, address⟩ := List.mem_map.mp (List.mem_toFinset.mp cached)
    have truthU := (legalU.2 e h hu).1 a ha
    simpa only [address] using (truthV a ha).symm.trans truthU
  have replay := actualPrefix_replay M U V hu agree
  obtain ⟨s, left, ht⟩ := prefix_run_tail M V replay runV
  obtain ⟨s', right, h't⟩ := prefix_run_tail M V hv runV
  have tails := (run_deterministic M V left right).1
  subst s'
  exact List.append_cancel_right (ht.trans h't.symm)

#print axioms actualPrefix_replay
#print axioms actualPrefix_history_rigid

end D5.S3.Arith.FibonacciAtomic.Observer.ActualObserverPrefixRigidity
