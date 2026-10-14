/- Prepared uncompiled exact scalar aggregate bridge.
The full original cache states and future transitions remain unchanged.
Only delta's next lower projection uses the fully checked scalar table;
the current row is already needed for its unchanged transition payload.
There is no replay acceptance theorem in this candidate. -/

import D5.S3.Quantum.Entanglement.EJM.EJMPackedLowerReceipts
import D5.S3.Quantum.Entanglement.EJM.EJMAggregateCachePacking

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

namespace D5.S3.Quantum.Entanglement.EJM.EJMPackedLowerAggregate
open EJMCachePacking
open EJMLocalCacheData
open EJMPackedLowerData
open EJMAggregateCachePacking (AggregateCache)

def triangleDelta (g : Fin 20) (a : Fin 4) (k : Fin 16) (word : ℕ) : ℤ :=
  match triangleIncidence g k with
  | none => 0
  | some i =>
    let state := decodeState (by decide : 0 < 41294) word
    let current := EJMTriangleCacheData.mirror state.1
    let next := readTransition (by decide) current (trianglePreimage state.2 i).val
      (EJMPartialBoundData.outcome state.2.2 a)
    triangleLower next.1 - current.lower

def singletonDelta (g : Fin 20) (a : Fin 4) (k : Fin 16) (word : ℕ) : ℤ :=
  match singletonIncidence g k with
  | none => 0
  | some i =>
    let state := decodeState (by decide : 0 < 8689) word
    let current := EJMSingletonCacheData.mirror state.1
    let next := readTransition (by decide) current (singletonPreimage state.2 i).val
      (EJMPartialBoundData.outcome state.2.2 a)
    singletonLower next.1 - current.lower

theorem triangleDelta_eq (g : Fin 20) (a : Fin 4) (k : Fin 16) (word : ℕ) :
    triangleDelta g a k word = EJMAggregateCachePacking.triangleDelta g a k word := by
  cases hi : triangleIncidence g k with
  | none => simp only [triangleDelta, EJMAggregateCachePacking.triangleDelta, hi]
  | some i =>
    simp only [triangleDelta, EJMAggregateCachePacking.triangleDelta, hi,
      EJMPackedLowerReceipts.triangle_eq, EJMCacheState.triangleStep]

theorem singletonDelta_eq (g : Fin 20) (a : Fin 4) (k : Fin 16) (word : ℕ) :
    singletonDelta g a k word = EJMAggregateCachePacking.singletonDelta g a k word := by
  cases hi : singletonIncidence g k with
  | none => simp only [singletonDelta, EJMAggregateCachePacking.singletonDelta, hi]
  | some i =>
    simp only [singletonDelta, EJMAggregateCachePacking.singletonDelta, hi,
      EJMPackedLowerReceipts.singleton_eq, EJMCacheState.singletonStep]

def delta (cache : PackedCache) (g : Fin 20) (a : Fin 4) : ℤ :=
  EJMStreamingCachePacking.sumWords 16 (triangleDelta g a) cache.triangle +
    EJMStreamingCachePacking.sumWords 16 (singletonDelta g a) cache.singleton

theorem delta_eq (cache : PackedCache) (g : Fin 20) (a : Fin 4) :
    delta cache g a = EJMAggregateCachePacking.delta cache g a := by
  unfold delta EJMAggregateCachePacking.delta
  have ht : triangleDelta g a = EJMAggregateCachePacking.triangleDelta g a := by
    funext k word
    exact triangleDelta_eq g a k word
  have hs : singletonDelta g a = EJMAggregateCachePacking.singletonDelta g a := by
    funext k word
    exact singletonDelta_eq g a k word
  rw [ht, hs]

def step (cache : AggregateCache) (g : Fin 20) (a : Fin 4) : AggregateCache :=
  ⟨EJMStreamingCachePacking.step cache.words g a,
    cache.total + delta cache.words g a⟩

theorem step_eq (cache : AggregateCache) (g : Fin 20) (a : Fin 4) :
    step cache g a = EJMAggregateCachePacking.step cache g a := by
  simp only [step, EJMAggregateCachePacking.step, delta_eq]

#print axioms triangleDelta_eq
#print axioms singletonDelta_eq
#print axioms delta_eq
#print axioms step_eq

end D5.S3.Quantum.Entanglement.EJM.EJMPackedLowerAggregate
