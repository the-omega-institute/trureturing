/- UNCOMPILED exact action-table representation candidate.
All finite local coordinate and outcome actions are compared with their
original functions. The original rows, transitions, assignments, four-value
branches and fuel remain unchanged. This module proves no acceptance. -/
import D5.S3.Quantum.Entanglement.EJM.EJMPackedLowerAggregate

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.style.longLine false

namespace D5.S3.Quantum.Entanglement.EJM.EJMPackedActions
open EJMCachePacking (PackedCache decodeState encodeState)
open EJMPartialBoundData (LocalSym)
open EJMLocalCacheData (triangleIncidence singletonIncidence readTransition)
open EJMAggregateCachePacking (AggregateCache)

def outcome (s : Fin 24) (a : Fin 4) : Fin 4 :=
  ⟨(0x1b4b278763931e4e36c672d22d8d39c9b1e16c9c78d8b4e4 / 2 ^ (2 * (4 * s.val + a.val)) % 4) % 4, Nat.mod_lt _ (by decide)⟩

private theorem outcome_all : ∀ (s : Fin 24) (a : Fin 4),
    outcome s a = (EJMPartialBoundData.outcome) s a := by decide +kernel

theorem outcome_eq (s : Fin 24) (a : Fin 4) :
    outcome s a = (EJMPartialBoundData.outcome) s a := outcome_all s a

def coordinateMul (s : Fin 12) (a : Fin 12) : Fin 12 :=
  ⟨(0x123456789ab2301548967ba10452376ab89451032ab769832540198ba67543210ba98766789ab0123458967ba23015476ab89104523ab769845103298ba67325401ba9876543210 / 2 ^ (4 * (12 * s.val + a.val)) % 16) % 12, Nat.mod_lt _ (by decide)⟩

private theorem coordinateMul_all : ∀ (s : Fin 12) (a : Fin 12),
    coordinateMul s a = (EJMCertificateData.triangleMul) s a := by decide +kernel

theorem coordinateMul_eq (s : Fin 12) (a : Fin 12) :
    coordinateMul s a = (EJMCertificateData.triangleMul) s a := coordinateMul_all s a

def outcomeMul (s : Fin 24) (a : Fin 24) : Fin 24 :=
  ⟨(0x443214c74254b635cf84653a56d731d0952c0110c8573d8d8c29594ef610c012918d73e1131d0952e72b5e95635cf84443004a4424c75aad79cab4424c75a9cf6363000443216b4bda5373d8d8c10931d6a10c01292f6ad2720808510ce652d0994e95b5d8d73e113994b4242021443a5653bd9cf636302142018a53a56d73994b425ac845cf94e95b5c850806252ce64a2116b1ee52ce64a29594ef60808510dee8c18da5653bd94b399282142018a307b9ac188a4005ac845cf9cad7a54c74254b6b21173c6229001b5e72ad10931d6a2906208272b5e956b21173ce652d099cad7a54a418820845ac7b94b39928845ac7bad79cab4188a4005285a8c7b5e72ad2116b1ee290620816a4a0e64a16a31dee8c18dad2f694c0110c857ba30635285a8c7bdab49c843004a45a92839ab4bda537ba306342021443ad2f694d6a4a0e68c1ee6b085080628c1ee6b2f6ad2724a16a31c6229001bdab49ca307b9ac5a928398a418820 / 2 ^ (5 * (24 * s.val + a.val)) % 32) % 24, Nat.mod_lt _ (by decide)⟩

private theorem outcomeMul_all : ∀ (s : Fin 24) (a : Fin 24),
    outcomeMul s a = (EJMLocalCacheData.outcomeMul) s a := by decide +kernel

theorem outcomeMul_eq (s : Fin 24) (a : Fin 24) :
    outcomeMul s a = (EJMLocalCacheData.outcomeMul) s a := outcomeMul_all s a

def trianglePreimage (s : Fin 12) (a : Fin 10) : Fin 10 :=
  ⟨(0x934567820193546872019435768201953486720194537862019543876201967834521096873542109768435210986753421097864532109876543210 / 2 ^ (4 * (10 * s.val + a.val)) % 16) % 10, Nat.mod_lt _ (by decide)⟩

private theorem trianglePreimage_all : ∀ (s : Fin 12) (a : Fin 10),
    trianglePreimage s a = (fun s i => EJMLocalCacheData.trianglePreimage (s, 0) i) s a := by decide +kernel

theorem trianglePreimage_eq (s : Fin 12) (a : Fin 10) :
    trianglePreimage s a = (fun s i => EJMLocalCacheData.trianglePreimage (s, 0) i) s a := trianglePreimage_all s a

def singletonPreimage (s : Fin 12) (a : Fin 9) : Fin 9 :=
  ⟨(0x781234560781256340783412560785612340783456120785634120872143650872165430874321650876521430874365210876543210 / 2 ^ (4 * (9 * s.val + a.val)) % 16) % 9, Nat.mod_lt _ (by decide)⟩

private theorem singletonPreimage_all : ∀ (s : Fin 12) (a : Fin 9),
    singletonPreimage s a = (fun s i => EJMLocalCacheData.singletonPreimage (s, 0) i) s a := by decide +kernel

theorem singletonPreimage_eq (s : Fin 12) (a : Fin 9) :
    singletonPreimage s a = (fun s i => EJMLocalCacheData.singletonPreimage (s, 0) i) s a := singletonPreimage_all s a

private theorem singleton_coordinateMul_eq (s a : Fin 12) :
    coordinateMul s a = EJMCertificateData.singletonMul s a := by
  exact coordinateMul_eq s a

def triangleCompose (t s : LocalSym) : LocalSym :=
  (coordinateMul s.1 t.1, outcomeMul t.2 s.2)
def singletonCompose (t s : LocalSym) : LocalSym :=
  (coordinateMul s.1 t.1, outcomeMul t.2 s.2)

private theorem triangleCompose_eq (t s : LocalSym) :
    triangleCompose t s = EJMLocalCacheData.triangleCompose t s := by
  simp only [triangleCompose, EJMLocalCacheData.triangleCompose,
    coordinateMul_eq, outcomeMul_eq]
private theorem singletonCompose_eq (t s : LocalSym) :
    singletonCompose t s = EJMLocalCacheData.singletonCompose t s := by
  simp only [singletonCompose, EJMLocalCacheData.singletonCompose,
    singleton_coordinateMul_eq, outcomeMul_eq]

private theorem trianglePreimage_actual (s : LocalSym) (i : Fin 10) :
    trianglePreimage s.1 i = EJMLocalCacheData.trianglePreimage s i :=
  trianglePreimage_eq s.1 i
private theorem singletonPreimage_actual (s : LocalSym) (i : Fin 9) :
    singletonPreimage s.1 i = EJMLocalCacheData.singletonPreimage s i :=
  singletonPreimage_eq s.1 i

def triangleWord (g : Fin 20) (a : Fin 4) (k : Fin 16) (word : ℕ) : ℕ :=
  let state := decodeState (by decide : 0 < 41294) word
  match triangleIncidence g k with
  | none => encodeState state
  | some i =>
    let next := readTransition (by decide : 0 < 41294) (EJMTriangleCacheData.mirror state.1)
      (trianglePreimage state.2.1 i).val (outcome state.2.2 a)
    encodeState (next.1, triangleCompose next.2 state.2)

def singletonWord (g : Fin 20) (a : Fin 4) (k : Fin 16) (word : ℕ) : ℕ :=
  let state := decodeState (by decide : 0 < 8689) word
  match singletonIncidence g k with
  | none => encodeState state
  | some i =>
    let next := readTransition (by decide : 0 < 8689) (EJMSingletonCacheData.mirror state.1)
      (singletonPreimage state.2.1 i).val (outcome state.2.2 a)
    encodeState (next.1, singletonCompose next.2 state.2)

private theorem triangleWord_eq (g : Fin 20) (a : Fin 4) (k : Fin 16) (word : ℕ) :
    triangleWord g a k word = EJMStreamingCachePacking.triangleWord g a k word := by
  cases hi : triangleIncidence g k with
  | none => simp only [triangleWord, EJMStreamingCachePacking.triangleWord, hi]
  | some i =>
    simp only [triangleWord, EJMStreamingCachePacking.triangleWord, hi,
      trianglePreimage_actual, outcome_eq, triangleCompose_eq, EJMCacheState.triangleStep]

private theorem singletonWord_eq (g : Fin 20) (a : Fin 4) (k : Fin 16) (word : ℕ) :
    singletonWord g a k word = EJMStreamingCachePacking.singletonWord g a k word := by
  cases hi : singletonIncidence g k with
  | none => simp only [singletonWord, EJMStreamingCachePacking.singletonWord, hi]
  | some i =>
    simp only [singletonWord, EJMStreamingCachePacking.singletonWord, hi,
      singletonPreimage_actual, outcome_eq, singletonCompose_eq, EJMCacheState.singletonStep]

def stepWords (cache : PackedCache) (g : Fin 20) (a : Fin 4) : PackedCache :=
  ⟨EJMStreamingCachePacking.mapWords 16 (triangleWord g a) cache.triangle,
   EJMStreamingCachePacking.mapWords 16 (singletonWord g a) cache.singleton⟩

private theorem stepWords_eq (cache : PackedCache) (g : Fin 20) (a : Fin 4) :
    stepWords cache g a = EJMStreamingCachePacking.step cache g a := by
  have ht : triangleWord g a = EJMStreamingCachePacking.triangleWord g a := by
    funext k word; exact triangleWord_eq g a k word
  have hs : singletonWord g a = EJMStreamingCachePacking.singletonWord g a := by
    funext k word; exact singletonWord_eq g a k word
  simp only [stepWords, EJMStreamingCachePacking.step, ht, hs]

def triangleDelta (g : Fin 20) (a : Fin 4) (k : Fin 16) (word : ℕ) : ℤ :=
  match triangleIncidence g k with
  | none => 0
  | some i =>
    let state := decodeState (by decide : 0 < 41294) word
    let current := EJMTriangleCacheData.mirror state.1
    let next := readTransition (by decide) current
      (trianglePreimage state.2.1 i).val (outcome state.2.2 a)
    EJMPackedLowerData.triangleLower next.1 - current.lower

def singletonDelta (g : Fin 20) (a : Fin 4) (k : Fin 16) (word : ℕ) : ℤ :=
  match singletonIncidence g k with
  | none => 0
  | some i =>
    let state := decodeState (by decide : 0 < 8689) word
    let current := EJMSingletonCacheData.mirror state.1
    let next := readTransition (by decide) current
      (singletonPreimage state.2.1 i).val (outcome state.2.2 a)
    EJMPackedLowerData.singletonLower next.1 - current.lower

private theorem triangleDelta_eq (g : Fin 20) (a : Fin 4) (k : Fin 16) (word : ℕ) :
    triangleDelta g a k word = EJMPackedLowerAggregate.triangleDelta g a k word := by
  cases hi : triangleIncidence g k with
  | none => simp only [triangleDelta, EJMPackedLowerAggregate.triangleDelta, hi]
  | some i =>
    simp only [triangleDelta, EJMPackedLowerAggregate.triangleDelta, hi,
      trianglePreimage_actual, outcome_eq]
private theorem singletonDelta_eq (g : Fin 20) (a : Fin 4) (k : Fin 16) (word : ℕ) :
    singletonDelta g a k word = EJMPackedLowerAggregate.singletonDelta g a k word := by
  cases hi : singletonIncidence g k with
  | none => simp only [singletonDelta, EJMPackedLowerAggregate.singletonDelta, hi]
  | some i =>
    simp only [singletonDelta, EJMPackedLowerAggregate.singletonDelta, hi,
      singletonPreimage_actual, outcome_eq]

def delta (cache : PackedCache) (g : Fin 20) (a : Fin 4) : ℤ :=
  EJMStreamingCachePacking.sumWords 16 (triangleDelta g a) cache.triangle +
    EJMStreamingCachePacking.sumWords 16 (singletonDelta g a) cache.singleton

private theorem delta_eq (cache : PackedCache) (g : Fin 20) (a : Fin 4) :
    delta cache g a = EJMPackedLowerAggregate.delta cache g a := by
  have ht : triangleDelta g a = EJMPackedLowerAggregate.triangleDelta g a := by
    funext k word; exact triangleDelta_eq g a k word
  have hs : singletonDelta g a = EJMPackedLowerAggregate.singletonDelta g a := by
    funext k word; exact singletonDelta_eq g a k word
  simp only [delta, EJMPackedLowerAggregate.delta, ht, hs]

def step (cache : AggregateCache) (g : Fin 20) (a : Fin 4) : AggregateCache :=
  ⟨stepWords cache.words g a, cache.total + delta cache.words g a⟩

theorem step_eq (cache : AggregateCache) (g : Fin 20) (a : Fin 4) :
    step cache g a = EJMPackedLowerAggregate.step cache g a := by
  simp only [step, EJMPackedLowerAggregate.step, stepWords_eq, delta_eq]

#print axioms step_eq
end D5.S3.Quantum.Entanglement.EJM.EJMPackedActions
