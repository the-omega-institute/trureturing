/- Prepared representation/performance candidate only. Each of the two
numeric vectors retains all sixteen exact row indices and earned actions.
Decoding restores every field of each indexed MirrorRow, including the full
future-transition payload. Equality uses the original row-consistency
invariant; neither row bounds nor global shapes substitute for future state.
No compilation, performance result or global acceptance is claimed here. -/

import D5.S3.Quantum.Entanglement.EJM.EJMCacheState
import D5.S0.Certificates.FiniteCachedSymmetryDAGReplay

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Entanglement.EJM.EJMCachePacking
open D5.S0.Certificates.FiniteLocalRowCache (State)
open D5.S0.Certificates.FiniteSymmetryBoundReplay (Partial)
open D5.S0.Certificates.FiniteSymmetryDAGReplay (Node)
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundData (LocalSym action)
open D5.S3.Quantum.Entanglement.EJM.EJMLocalCacheData
open D5.S3.Quantum.Entanglement.EJM.EJMCacheState (Cache CachedLocal)

/-- One exact 16-bit row index and a complete 9-bit local action code. -/
def radix : ℕ := 33554432

/-- Low-index-first scalar construction forces every retained numeric field. -/
def packWords : (n : ℕ) → (Fin n → ℕ) → ℕ
  | 0, _ => 0
  | n + 1, f => f 0 + radix * packWords n (fun k => f k.succ)

/-- Repeated division avoids constructing a fresh large power at each lookup. -/
def wordAt : ℕ → ℕ → ℕ
  | vector, 0 => vector % radix
  | vector, k + 1 => wordAt (vector / radix) k

private theorem head_mod (word tail : ℕ) (h : word < radix) :
    (word + radix * tail) % radix = word := by
  unfold radix at h ⊢
  omega

private theorem head_div (word tail : ℕ) (h : word < radix) :
    (word + radix * tail) / radix = tail := by
  unfold radix at h ⊢
  omega

theorem wordAt_packWords : ∀ (n : ℕ) (f : Fin n → ℕ),
    (∀ k, f k < radix) → ∀ k, wordAt (packWords n f) k.val = f k := by
  intro n
  induction n with
  | zero =>
    intro f h k
    exact Fin.elim0 k
  | succ n ih =>
    intro f h k
    refine Fin.cases ?_ (fun j => ?_) k
    · change (f 0 + radix * packWords n (fun j => f j.succ)) % radix = f 0
      exact head_mod _ _ (h 0)
    · change wordAt ((f 0 + radix * packWords n (fun j => f j.succ)) / radix)
        j.val = f j.succ
      rw [head_div _ _ (h 0)]
      exact ih _ (fun j => h j.succ) j

def encodeState {N : ℕ} (state : State N LocalSym) : ℕ :=
  state.1.val + 65536 * (24 * state.2.1.val + state.2.2.val)

def decodeState {N : ℕ} (hN : 0 < N) (word : ℕ) : State N LocalSym :=
  (⟨word % 65536 % N, Nat.mod_lt _ hN⟩, action (word / 65536))

theorem encodeState_lt {N : ℕ} (hN : N ≤ 65536) (state : State N LocalSym) :
    encodeState state < radix := by
  rcases state with ⟨j, ⟨i, v⟩⟩
  have hj := j.isLt
  have hi := i.isLt
  have hv := v.isLt
  change j.val + 65536 * (24 * i.val + v.val) < 33554432
  omega

theorem decodeState_encodeState {N : ℕ} (hpos : 0 < N) (hN : N ≤ 65536)
    (state : State N LocalSym) : decodeState hpos (encodeState state) = state := by
  rcases state with ⟨j, ⟨i, v⟩⟩
  have hj := j.isLt
  have hi := i.isLt
  have hv := v.isLt
  have hrem : encodeState (j, (i, v)) % 65536 = j.val := by
    change (j.val + 65536 * (24 * i.val + v.val)) % 65536 = j.val
    omega
  have hdiv : encodeState (j, (i, v)) / 65536 = 24 * i.val + v.val := by
    change (j.val + 65536 * (24 * i.val + v.val)) / 65536 = 24 * i.val + v.val
    omega
  apply Prod.ext
  · apply Fin.ext
    change encodeState (j, (i, v)) % 65536 % N = j.val
    rw [hrem, Nat.mod_eq_of_lt hj]
  · apply Prod.ext
    · apply Fin.ext
      change encodeState (j, (i, v)) / 65536 / 24 % 12 = i.val
      rw [hdiv]
      omega
    · apply Fin.ext
      change encodeState (j, (i, v)) / 65536 % 24 = v.val
      rw [hdiv]
      omega

structure PackedCache where
  triangle : ℕ
  singleton : ℕ

def encode (cache : Cache) : PackedCache :=
  ⟨packWords 16 (fun k => encodeState (cache.triangle k).state),
   packWords 16 (fun k => encodeState (cache.singleton k).state)⟩

/-- The index restores the complete actual transition row, not just its lower. -/
def decode (cache : PackedCache) : Cache :=
  ⟨fun k =>
     let state := decodeState (by decide : 0 < 41294) (wordAt cache.triangle k.val)
     ⟨state, EJMTriangleCacheData.mirror state.1⟩,
   fun k =>
     let state := decodeState (by decide : 0 < 8689) (wordAt cache.singleton k.val)
     ⟨state, EJMSingletonCacheData.mirror state.1⟩⟩

/-- Row literals agree in every field with the actual indexed mirrors. -/
def RowsCurrent (cache : Cache) : Prop :=
  (∀ k, (cache.triangle k).row = EJMTriangleCacheData.mirror (cache.triangle k).state.1) ∧
    ∀ k, (cache.singleton k).row = EJMSingletonCacheData.mirror (cache.singleton k).state.1

private theorem state_packed_exact {N : ℕ} (hpos : 0 < N) (hN : N ≤ 65536)
    (f : Fin 16 → CachedLocal N) (k : Fin 16) :
    decodeState hpos (wordAt (packWords 16 (fun j => encodeState (f j).state)) k.val) =
      (f k).state := by
  rw [wordAt_packWords 16 _ (fun j => encodeState_lt hN (f j).state) k]
  exact decodeState_encodeState hpos hN (f k).state

private theorem cachedLocal_eq {N : ℕ} (a b : CachedLocal N)
    (hs : a.state = b.state) (hr : a.row = b.row) : a = b := by
  cases a
  cases b
  cases hs
  cases hr
  rfl

theorem decode_encode (cache : Cache) (h : RowsCurrent cache) :
    decode (encode cache) = cache := by
  have htstate (k : Fin 16) :
      ((decode (encode cache)).triangle k).state = (cache.triangle k).state :=
    state_packed_exact (by decide) (by decide) cache.triangle k
  have hsstate (k : Fin 16) :
      ((decode (encode cache)).singleton k).state = (cache.singleton k).state :=
    state_packed_exact (by decide) (by decide) cache.singleton k
  have ht : (decode (encode cache)).triangle = cache.triangle := by
    funext k
    apply cachedLocal_eq _ _ (htstate k)
    change EJMTriangleCacheData.mirror ((decode (encode cache)).triangle k).state.1 =
      (cache.triangle k).row
    rw [htstate k]
    exact (h.1 k).symm
  have hs : (decode (encode cache)).singleton = cache.singleton := by
    funext k
    apply cachedLocal_eq _ _ (hsstate k)
    change EJMSingletonCacheData.mirror ((decode (encode cache)).singleton k).state.1 =
      (cache.singleton k).row
    rw [hsstate k]
    exact (h.2 k).symm
  exact congrArg₂ Cache.mk ht hs

theorem rowsCurrent_decode (cache : PackedCache) : RowsCurrent (decode cache) :=
  ⟨fun _ => rfl, fun _ => rfl⟩

theorem rowsCurrent_step (cache : Cache) (h : RowsCurrent cache) (g : Fin 20)
    (a : Fin 4) : RowsCurrent (EJMCacheState.step cache g a) := by
  constructor
  · intro k
    cases hi : triangleIncidence g k with
    | none => simpa only [EJMCacheState.step, hi] using h.1 k
    | some i =>
      simp only [EJMCacheState.step, hi]
      rfl
  · intro k
    cases hi : singletonIncidence g k with
    | none => simpa only [EJMCacheState.step, hi] using h.2 k
    | some i =>
      simp only [EJMCacheState.step, hi]
      rfl

def initial : PackedCache := encode EJMCacheState.initial

def step (cache : PackedCache) (g : Fin 20) (a : Fin 4) : PackedCache :=
  encode (EJMCacheState.step (decode cache) g a)

def lower (cache : PackedCache) : ℤ := EJMCacheState.lower (decode cache)

theorem decode_initial : decode initial = EJMCacheState.initial :=
  decode_encode _ ⟨fun _ => rfl, fun _ => rfl⟩

theorem decode_step (cache : PackedCache) (g : Fin 20) (a : Fin 4) :
    decode (step cache g a) = EJMCacheState.step (decode cache) g a :=
  decode_encode _ (rowsCurrent_step _ (rowsCurrent_decode cache) g a)

theorem lower_decode (cache : PackedCache) :
    lower cache = EJMCacheState.lower (decode cache) := rfl

/-- Every numeric, symmetry and all-value recursive result is unchanged.
In particular dominance is evaluated on the same complete actual partial p. -/
theorem check_decode {N : ℕ} {Sym : Type*}
    (nodes : ℕ → Fin N → Node N (Fin 20) (Fin 4) Sym)
    (dominates : Sym → Partial (Fin 20) (Fin 4) → Bool) (gap : ℤ)
    (fuel : ℕ) (index : Fin N) (cache : PackedCache) (p : Partial (Fin 20) (Fin 4)) :
    D5.S0.Certificates.FiniteCachedSymmetryDAGReplay.check nodes step lower dominates gap
      fuel index cache p =
    D5.S0.Certificates.FiniteCachedSymmetryDAGReplay.check nodes
      EJMCacheState.step EJMCacheState.lower dominates gap fuel index (decode cache) p := by
  induction fuel generalizing index cache p with
  | zero => rfl
  | succ fuel ih =>
    cases hn : nodes (fuel + 1) index with
    | bound =>
      simp only [D5.S0.Certificates.FiniteCachedSymmetryDAGReplay.check, hn, lower]
    | symmetry s =>
      simp only [D5.S0.Certificates.FiniteCachedSymmetryDAGReplay.check, hn]
    | split i children =>
      simp only [D5.S0.Certificates.FiniteCachedSymmetryDAGReplay.check, hn]
      have children_eq (a : Fin 4) :
          D5.S0.Certificates.FiniteCachedSymmetryDAGReplay.check nodes step lower dominates
            gap fuel (children a) (step cache i a) (Function.update p i (some a)) =
          D5.S0.Certificates.FiniteCachedSymmetryDAGReplay.check nodes EJMCacheState.step
            EJMCacheState.lower dominates gap fuel (children a)
            (EJMCacheState.step (decode cache) i a) (Function.update p i (some a)) := by
        rw [ih, decode_step]
      simp only [children_eq]

#print axioms decode_encode
#print axioms decode_step
#print axioms lower_decode
#print axioms check_decode
end D5.S3.Quantum.Entanglement.EJM.EJMCachePacking
