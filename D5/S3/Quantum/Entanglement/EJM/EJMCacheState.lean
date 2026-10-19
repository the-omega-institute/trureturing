/- GID: D5/S3/Quantum/Entanglement/EJM/EJMCacheState
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/EJMCacheState
   mirror-E: none(waiver:actual-exact-certificate-cache)
   anchors: []
   utility: none
   digest: Thirty-two local states retain compact literal row data and transport every affected original block. -/

/- Prepared executable data, not compiled. This module asserts no cache
soundness or acceptance. Full row/action association is proved by the actual
consumer; storing a row literal is justified only by its mirror receipts. -/

import D5.S3.Quantum.Entanglement.EJM.EJMTriangleCacheData
import D5.S3.Quantum.Entanglement.EJM.EJMSingletonCacheData

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Entanglement.EJM.EJMCacheState
open D5.S0.Certificates.FiniteLocalRowCache (State)
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundData (LocalSym outcome)
open D5.S3.Quantum.Entanglement.EJM.EJMLocalCacheData
open scoped BigOperators

/-- The row literal is retained so leaf arithmetic never reopens a packed row.
Its equality with the proposed row index's actual mirror is a proved invariant. -/
structure CachedLocal (N : ℕ) where
  state : State N LocalSym
  row : MirrorRow

structure Cache where
  triangle : Fin 16 → CachedLocal 41294
  singleton : Fin 16 → CachedLocal 8689

def triangleStep (current : CachedLocal 41294) (i : Fin 10) (a : Fin 4) :
    CachedLocal 41294 :=
  let next := readTransition (by decide) current.row (trianglePreimage current.state.2 i).val
    (outcome current.state.2.2 a)
  ⟨(next.1, triangleCompose next.2 current.state.2), EJMTriangleCacheData.mirror next.1⟩

def singletonStep (current : CachedLocal 8689) (i : Fin 9) (a : Fin 4) :
    CachedLocal 8689 :=
  let next := readTransition (by decide) current.row (singletonPreimage current.state.2 i).val
    (outcome current.state.2.2 a)
  ⟨(next.1, singletonCompose next.2 current.state.2), EJMSingletonCacheData.mirror next.1⟩

/-- Exact incidence changes only the blocks containing this original coordinate.
All unaffected row literals and earned actions are reused. -/
def step (cache : Cache) (g : Fin 20) (a : Fin 4) : Cache :=
  ⟨fun k => match triangleIncidence g k with
     | none => cache.triangle k
     | some i => triangleStep (cache.triangle k) i a,
   fun k => match singletonIncidence g k with
     | none => cache.singleton k
     | some i => singletonStep (cache.singleton k) i a⟩

def lower (cache : Cache) : ℤ :=
  (∑ k : Fin 16, (cache.triangle k).row.lower) +
    ∑ k : Fin 16, (cache.singleton k).row.lower

end D5.S3.Quantum.Entanglement.EJM.EJMCacheState
