/- Prepared exact aggregate-cache candidate. Its scalar total is earned from
the complete original 32-block integer sum and is updated by the exact changed
local rows. It preserves every original state, transition and replay branch.
Neither the invariant nor the representation bridge asserts acceptance. -/

import D5.S3.Quantum.Entanglement.EJM.EJMStreamingCachePacking
import D5.S3.Quantum.Entanglement.EJM.EJMCompactCachedReplay

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

namespace D5.S3.Quantum.Entanglement.EJM.EJMAggregateCachePacking

open EJMCachePacking
open EJMLocalCacheData (triangleIncidence singletonIncidence)
open EJMCacheState (triangleStep singletonStep)
open EJMStreamingCachePacking (sumWords)
open EJMCompactPartial (PackedPartial checkPacked)
open scoped BigOperators

def triangleDelta (g : Fin 20) (a : Fin 4) (k : Fin 16) (word : ℕ) : ℤ :=
  match triangleIncidence g k with
  | none => 0
  | some i =>
    let state := decodeState (by decide : 0 < 41294) word
    let current := EJMTriangleCacheData.mirror state.1
    (triangleStep ⟨state, current⟩ i a).row.lower - current.lower

def singletonDelta (g : Fin 20) (a : Fin 4) (k : Fin 16) (word : ℕ) : ℤ :=
  match singletonIncidence g k with
  | none => 0
  | some i =>
    let state := decodeState (by decide : 0 < 8689) word
    let current := EJMSingletonCacheData.mirror state.1
    (singletonStep ⟨state, current⟩ i a).row.lower - current.lower

def delta (cache : PackedCache) (g : Fin 20) (a : Fin 4) : ℤ :=
  sumWords 16 (triangleDelta g a) cache.triangle +
    sumWords 16 (singletonDelta g a) cache.singleton

private theorem triangle_update (cache : PackedCache) (g : Fin 20) (a : Fin 4)
    (k : Fin 16) :
    ((EJMCacheState.step (decode cache) g a).triangle k).row.lower =
      ((decode cache).triangle k).row.lower +
        triangleDelta g a k (wordAt cache.triangle k.val) := by
  cases h : triangleIncidence g k <;>
    simp only [EJMCacheState.step, triangleDelta, decode, h]
  · simp
  · ring

private theorem singleton_update (cache : PackedCache) (g : Fin 20) (a : Fin 4)
    (k : Fin 16) :
    ((EJMCacheState.step (decode cache) g a).singleton k).row.lower =
      ((decode cache).singleton k).row.lower +
        singletonDelta g a k (wordAt cache.singleton k.val) := by
  cases h : singletonIncidence g k <;>
    simp only [EJMCacheState.step, singletonDelta, decode, h]
  · simp
  · ring

theorem lower_step (cache : PackedCache) (g : Fin 20) (a : Fin 4) :
    EJMStreamingCachePacking.lower (EJMStreamingCachePacking.step cache g a) =
      EJMStreamingCachePacking.lower cache + delta cache g a := by
  rw [EJMStreamingCachePacking.step_eq_original,
    EJMStreamingCachePacking.lower_eq_original,
    EJMStreamingCachePacking.lower_eq_original]
  unfold EJMCachePacking.lower
  rw [decode_step]
  simp only [EJMCacheState.lower, triangle_update, singleton_update,
    delta, EJMStreamingCachePacking.sumWords_eq_sum, Finset.sum_add_distrib]
  ring

structure AggregateCache where
  words : PackedCache
  total : ℤ

def Valid (cache : AggregateCache) : Prop :=
  cache.total = EJMStreamingCachePacking.lower cache.words

def initial : AggregateCache :=
  ⟨EJMCachePacking.initial, EJMStreamingCachePacking.lower EJMCachePacking.initial⟩

theorem initial_valid : Valid initial := rfl

def step (cache : AggregateCache) (g : Fin 20) (a : Fin 4) : AggregateCache :=
  ⟨EJMStreamingCachePacking.step cache.words g a,
    cache.total + delta cache.words g a⟩

theorem step_valid (cache : AggregateCache) (h : Valid cache) (g : Fin 20)
    (a : Fin 4) : Valid (step cache g a) := by
  change cache.total + delta cache.words g a =
    EJMStreamingCachePacking.lower (EJMStreamingCachePacking.step cache.words g a)
  rw [lower_step, h]

def lower (cache : AggregateCache) : ℤ := cache.total

theorem replay_eq_streaming (fuel : ℕ) (index : Fin EJMGlobalDAGData.Size)
    (cache : AggregateCache) (h : Valid cache) (q : PackedPartial) :
    checkPacked EJMGlobalDAGData.nodes step lower EJMGlobalScoreSymmetry.dominates
        EJMPartialBoundData.scale fuel index cache q =
      checkPacked EJMGlobalDAGData.nodes EJMStreamingCachePacking.step
        EJMStreamingCachePacking.lower EJMGlobalScoreSymmetry.dominates
        EJMPartialBoundData.scale fuel index cache.words q := by
  induction fuel generalizing index cache q with
  | zero => rfl
  | succ fuel ih =>
    cases hn : EJMGlobalDAGData.nodes (fuel + 1) index with
    | bound =>
      simp only [checkPacked, hn, lower]
      rw [show cache.total = EJMStreamingCachePacking.lower cache.words from h]
    | symmetry s =>
      simp only [checkPacked, hn]
    | split i children =>
      simp only [checkPacked, hn]
      have children_eq (a : Fin 4) :
          checkPacked EJMGlobalDAGData.nodes step lower EJMGlobalScoreSymmetry.dominates
              EJMPartialBoundData.scale fuel (children a) (step cache i a)
              (EJMCompactPartial.advance fuel q i a) =
            checkPacked EJMGlobalDAGData.nodes EJMStreamingCachePacking.step
              EJMStreamingCachePacking.lower EJMGlobalScoreSymmetry.dominates
              EJMPartialBoundData.scale fuel (children a)
              (EJMStreamingCachePacking.step cache.words i a)
              (EJMCompactPartial.advance fuel q i a) :=
        ih (children a) (step cache i a) (step_valid cache h i a) _
      simp only [children_eq]

theorem replay_eq_original (fuel : ℕ) (index : Fin EJMGlobalDAGData.Size)
    (cache : AggregateCache) (h : Valid cache) (q : PackedPartial)
    (hwell : EJMCompactPartial.WellFormed q) (hinv : q.depth + fuel = 21) :
    checkPacked EJMGlobalDAGData.nodes step lower EJMGlobalScoreSymmetry.dominates
        EJMPartialBoundData.scale fuel index cache q =
      D5.S0.Certificates.FiniteCachedSymmetryDAGReplay.check EJMGlobalDAGData.nodes
        EJMCacheState.step EJMCacheState.lower EJMGlobalScoreSymmetry.dominates
        EJMPartialBoundData.scale fuel index (decode cache.words) (EJMCompactPartial.decode q) := by
  rw [replay_eq_streaming fuel index cache h q]
  have hs : EJMStreamingCachePacking.step = EJMCachePacking.step := by
    funext c g a
    exact EJMStreamingCachePacking.step_eq_original c g a
  have hl : EJMStreamingCachePacking.lower = EJMCachePacking.lower := by
    funext c
    exact EJMStreamingCachePacking.lower_eq_original c
  rw [hs, hl]
  exact EJMCompactCachedReplay.replay_eq_original fuel index cache.words q hwell hinv

#print axioms lower_step
#print axioms step_valid
#print axioms replay_eq_streaming
#print axioms replay_eq_original

end D5.S3.Quantum.Entanglement.EJM.EJMAggregateCachePacking
