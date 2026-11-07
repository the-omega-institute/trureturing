/- GID: D5/S3/Quantum/Entanglement/EJM/CanonicalCacheStateEqualityCandidate
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/CanonicalCacheStateEqualityCandidate
   mirror-E: none(waiver:exact-original-context-mathematical-source)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Quantum/Entanglement/EJM/Frontier/Raw/Part000/Raw002Tail442/Assembly.raw_cut_00337; premises=D5/S3/Quantum/Entanglement/EJM/CanonicalCacheStateEqualityCandidate.cachedLocal_eq_of_state_and_canonical_rows,D5/S3/Quantum/Entanglement/EJM/CanonicalCacheStateEqualityCandidate.triangleStep_row_canonical,D5/S3/Quantum/Entanglement/EJM/CanonicalCacheStateEqualityCandidate.singletonStep_row_canonical,D5/S3/Quantum/Entanglement/EJM/CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror,D5/S3/Quantum/Entanglement/EJM/CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror
   digest: Equality of complete State and both full canonical rows determines whole CachedLocal equality and the actual triangle and singleton transition outputs. -/

/- Complete local-cache equality from the full State and canonical rows.
   All representative and action indices and all MirrorRow fields are retained.
   The consuming context modules supply their own concrete transition receipts.
   These reusable contracts assume neither mere association nor whole-certificate acceptance. -/
import D5.S3.Quantum.Entanglement.EJM.EJMCacheSoundness

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
set_option trace.profiler true

namespace D5.S3.Quantum.Entanglement.EJM.CanonicalCacheStateEqualityCandidate

open EJMCacheState (CachedLocal triangleStep singletonStep)
open EJMLocalCacheData (MirrorRow)

/-- Both canonical-row hypotheses and the entire State equality are necessary.
State is `Fin N × (Fin 12 × Fin 24)`: it contains the actual row index and both
action IDs. The row hypotheses identify all four MirrorRow fields, not only
hash/lower. For valid triangle/singleton caches, the existing TriangleValid or
SingletonValid proof's `.1` supplies the corresponding canonical-row premise.
Association alone supplies neither premise nor the State equality. -/
theorem cachedLocal_eq_of_state_and_canonical_rows {N : ℕ}
    (mirror : Fin N → MirrorRow) (actual proposed : CachedLocal N)
    (actualCanonical : actual.row = mirror actual.state.1)
    (proposedCanonical : proposed.row = mirror proposed.state.1)
    (stateEqual : actual.state = proposed.state) : actual = proposed := by
  have rowEqual : actual.row = proposed.row := by
    rw [actualCanonical, proposedCanonical, stateEqual]
  cases actual with
  | mk actualState actualRow =>
    cases proposed with
    | mk proposedState proposedRow =>
      change actualState = proposedState at stateEqual
      change actualRow = proposedRow at rowEqual
      cases stateEqual
      cases rowEqual
      rfl

/-- The actual triangle transition constructs a canonical row definitionally.
This needs no association hypothesis or validity transport. -/
theorem triangleStep_row_canonical (current : CachedLocal 41294)
    (i : Fin 10) (a : Fin 4) :
    (triangleStep current i a).row =
      EJMTriangleCacheData.mirror (triangleStep current i a).state.1 := by
  rfl

/-- The same definitional canonical-row fact for the actual singleton step. -/
theorem singletonStep_row_canonical (current : CachedLocal 8689)
    (i : Fin 9) (a : Fin 4) :
    (singletonStep current i a).row =
      EJMSingletonCacheData.mirror (singletonStep current i a).state.1 := by
  rfl

/-- The dynamic receipt checks only the complete resulting State. A separate
full mirror receipt can be shared by all occurrences of the same proposed row.
Together they imply equality of the complete actual triangleStep output. -/
theorem triangleStep_eq_of_state_and_mirror
    (current proposed : CachedLocal 41294) (i : Fin 10) (a : Fin 4)
    (stateReceipt : (triangleStep current i a).state = proposed.state)
    (mirrorReceipt : proposed.row = EJMTriangleCacheData.mirror proposed.state.1) :
    triangleStep current i a = proposed :=
  cachedLocal_eq_of_state_and_canonical_rows EJMTriangleCacheData.mirror _ _
    (triangleStep_row_canonical current i a) mirrorReceipt stateReceipt

/-- Singleton analogue; the receipt still compares all three State indices. -/
theorem singletonStep_eq_of_state_and_mirror
    (current proposed : CachedLocal 8689) (i : Fin 9) (a : Fin 4)
    (stateReceipt : (singletonStep current i a).state = proposed.state)
    (mirrorReceipt : proposed.row = EJMSingletonCacheData.mirror proposed.state.1) :
    singletonStep current i a = proposed :=
  cachedLocal_eq_of_state_and_canonical_rows EJMSingletonCacheData.mirror _ _
    (singletonStep_row_canonical current i a) mirrorReceipt stateReceipt

#print axioms cachedLocal_eq_of_state_and_canonical_rows
#print axioms triangleStep_row_canonical
#print axioms singletonStep_row_canonical
#print axioms triangleStep_eq_of_state_and_mirror
#print axioms singletonStep_eq_of_state_and_mirror

end D5.S3.Quantum.Entanglement.EJM.CanonicalCacheStateEqualityCandidate
