/- Prepared streaming representation candidate. Every word is decoded with
the original row-index and complete local action, and every affected state
uses the original transition. The tail is divided once per local block.
No acceptance or performance result is supplied by this module. -/

import D5.S3.Quantum.Entanglement.EJM.EJMCachePacking

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

namespace D5.S3.Quantum.Entanglement.EJM.EJMStreamingCachePacking

open EJMCachePacking
open EJMCacheState (triangleStep singletonStep)
open EJMLocalCacheData (triangleIncidence singletonIncidence)
open scoped BigOperators

/-- Stream low words in order; no lookup restarts at the head of the vector. -/
def mapWords : (n : ℕ) → (Fin n → ℕ → ℕ) → ℕ → ℕ
  | 0, _, _ => 0
  | n + 1, f, vector =>
    f 0 (vector % radix) +
      radix * mapWords n (fun k => f k.succ) (vector / radix)

theorem mapWords_eq_packWords (n : ℕ) (f : Fin n → ℕ → ℕ) (vector : ℕ) :
    mapWords n f vector = packWords n (fun k => f k (wordAt vector k.val)) := by
  induction n generalizing vector with
  | zero => rfl
  | succ n ih =>
    simp only [mapWords, packWords, wordAt, Fin.val_zero, Fin.val_succ]
    rw [ih]

/-- Fold the exact original integer lowers in the same streamed word order. -/
def sumWords : (n : ℕ) → (Fin n → ℕ → ℤ) → ℕ → ℤ
  | 0, _, _ => 0
  | n + 1, f, vector =>
    f 0 (vector % radix) + sumWords n (fun k => f k.succ) (vector / radix)

theorem sumWords_eq_sum (n : ℕ) (f : Fin n → ℕ → ℤ) (vector : ℕ) :
    sumWords n f vector = ∑ k : Fin n, f k (wordAt vector k.val) := by
  induction n generalizing vector with
  | zero => simp [sumWords]
  | succ n ih =>
    rw [Fin.sum_univ_succ]
    simp only [sumWords, wordAt, Fin.val_zero, Fin.val_succ]
    rw [ih]

def triangleWord (g : Fin 20) (a : Fin 4) (k : Fin 16) (word : ℕ) : ℕ :=
  let state := decodeState (by decide : 0 < 41294) word
  match triangleIncidence g k with
  | none => encodeState state
  | some i => encodeState (triangleStep ⟨state, EJMTriangleCacheData.mirror state.1⟩ i a).state

def singletonWord (g : Fin 20) (a : Fin 4) (k : Fin 16) (word : ℕ) : ℕ :=
  let state := decodeState (by decide : 0 < 8689) word
  match singletonIncidence g k with
  | none => encodeState state
  | some i =>
    encodeState (singletonStep ⟨state, EJMSingletonCacheData.mirror state.1⟩ i a).state

def step (cache : PackedCache) (g : Fin 20) (a : Fin 4) : PackedCache :=
  ⟨mapWords 16 (triangleWord g a) cache.triangle,
   mapWords 16 (singletonWord g a) cache.singleton⟩

theorem step_eq_original (cache : PackedCache) (g : Fin 20) (a : Fin 4) :
    step cache g a = EJMCachePacking.step cache g a := by
  unfold step
  rw [mapWords_eq_packWords, mapWords_eq_packWords]
  unfold EJMCachePacking.step encode
  apply congrArg₂ PackedCache.mk
  · apply congrArg (packWords 16)
    funext k
    cases h : triangleIncidence g k <;>
      simp only [triangleWord, EJMCacheState.step, decode, h]
  · apply congrArg (packWords 16)
    funext k
    cases h : singletonIncidence g k <;>
      simp only [singletonWord, EJMCacheState.step, decode, h]

def lower (cache : PackedCache) : ℤ :=
  sumWords 16 (fun _ word =>
    (EJMTriangleCacheData.mirror (decodeState (by decide : 0 < 41294) word).1).lower)
      cache.triangle +
  sumWords 16 (fun _ word =>
    (EJMSingletonCacheData.mirror (decodeState (by decide : 0 < 8689) word).1).lower)
      cache.singleton

theorem lower_eq_original (cache : PackedCache) :
    lower cache = EJMCachePacking.lower cache := by
  simp only [lower, sumWords_eq_sum, EJMCachePacking.lower, EJMCacheState.lower, decode]

#print axioms mapWords_eq_packWords
#print axioms sumWords_eq_sum
#print axioms step_eq_original
#print axioms lower_eq_original

end D5.S3.Quantum.Entanglement.EJM.EJMStreamingCachePacking
