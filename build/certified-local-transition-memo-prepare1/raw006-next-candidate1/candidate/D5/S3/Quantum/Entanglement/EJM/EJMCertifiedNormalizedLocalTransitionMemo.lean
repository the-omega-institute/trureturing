/- Prepared source only; no elaboration, kernel result or cost claim.
   The outer oracle still returns a proof for the complete nine-field input.
   Only internal functions are factored by their exact definitional inputs. -/
import D5.S3.Quantum.Entanglement.EJM.EJMCertifiedLocalTransitionMemo

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Entanglement.EJM.EJMCertifiedNormalizedLocalTransitionMemo

open D5.S0.Certificates.CertifiedLocalTransitionMemo (Receipt memoStep memoStep_eq)
open D5.S0.Certificates.FiniteCachedSymmetryDAGReplay (check)
open EJMCacheState (Cache CachedLocal step lower)
open EJMLocalCacheData
  (MirrorRow readTransition trianglePreimage singletonPreimage triangleCompose singletonCompose)
open EJMPartialBoundData (LocalSym outcome scale)
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial Accepted)
open EJMCertifiedLocalTransitionMemo
  (LocalInput TriangleReceipt SingletonReceipt triangleActual singletonActual
   memoGlobalStep memoGlobalStep_eq check_eq_actual)

/-- These are precisely the arguments inspected by the packed edge reader.
The ignored row hash/lower and the two current actions remain in LocalInput;
actions determine this key and are reattached after the reader returns. -/
structure PackedInput where
  slots : ℕ
  edges : ℕ
  coordinate : ℕ
  value : Fin 4
  deriving DecidableEq

def PackedInput.ofLocal {N dimensions : ℕ}
    (preimage : LocalSym → Fin dimensions → ℕ) (input : LocalInput N dimensions) :
    PackedInput :=
  ⟨input.rowSlots, input.rowEdges, preimage input.current.state.2 input.coordinate,
   outcome input.current.state.2.2 input.value⟩

def packedActual {N : ℕ} (positive : 0 < N) (input : PackedInput) :
    Fin N × LocalSym :=
  readTransition positive ⟨0, 0, input.slots, input.edges⟩ input.coordinate input.value

/-- No row-validity, canonical-row, unknown-coordinate or action hypothesis.
readTransition definitionally does not inspect row.hash or row.lower. -/
theorem packedActual_ofLocal {N dimensions : ℕ} (positive : 0 < N)
    (preimage : LocalSym → Fin dimensions → ℕ) (input : LocalInput N dimensions) :
    packedActual positive (PackedInput.ofLocal preimage input) =
      readTransition positive input.current.row
        (preimage input.current.state.2 input.coordinate)
        (outcome input.current.state.2.2 input.value) := by
  rfl

def plainLocal {N dimensions : ℕ} (positive : 0 < N)
    (mirror : Fin N → MirrorRow) (preimage : LocalSym → Fin dimensions → ℕ)
    (compose : LocalSym → LocalSym → LocalSym) (input : LocalInput N dimensions) :
    CachedLocal N :=
  let next := readTransition positive input.current.row
    (preimage input.current.state.2 input.coordinate)
    (outcome input.current.state.2.2 input.value)
  ⟨(next.1, compose next.2 input.current.state.2), mirror next.1⟩

/-- Packed-edge and complete-mirror computations have separate certified
selectors. Missing or mismatched proposals execute their original functions.
The actual action composition is performed for the current full input. -/
def normalizedLocal {N dimensions : ℕ} (positive : 0 < N)
    (mirror : Fin N → MirrorRow) (preimage : LocalSym → Fin dimensions → ℕ)
    (compose : LocalSym → LocalSym → LocalSym)
    (transitionLookup : PackedInput → Option (Receipt (packedActual positive)))
    (mirrorLookup : Fin N → Option (Receipt mirror))
    (input : LocalInput N dimensions) : CachedLocal N :=
  let next := memoStep (packedActual positive) transitionLookup (PackedInput.ofLocal preimage input)
  ⟨(next.1, compose next.2 input.current.state.2), memoStep mirror mirrorLookup next.1⟩

/-- Both selectors are arbitrary; no completeness or coverage premise is used.
The equality includes the full resulting State and all four MirrorRow fields. -/
theorem normalizedLocal_eq {N dimensions : ℕ} (positive : 0 < N)
    (mirror : Fin N → MirrorRow) (preimage : LocalSym → Fin dimensions → ℕ)
    (compose : LocalSym → LocalSym → LocalSym)
    (transitionLookup : PackedInput → Option (Receipt (packedActual positive)))
    (mirrorLookup : Fin N → Option (Receipt mirror))
    (input : LocalInput N dimensions) :
    normalizedLocal positive mirror preimage compose transitionLookup mirrorLookup input =
      plainLocal positive mirror preimage compose input := by
  simp only [normalizedLocal, plainLocal, memoStep_eq, packedActual_ofLocal]

abbrev TrianglePackedReceipt := Receipt (packedActual (N := 41294) (by decide))
abbrev SingletonPackedReceipt := Receipt (packedActual (N := 8689) (by decide))
abbrev TriangleMirrorReceipt := Receipt EJMTriangleCacheData.mirror
abbrev SingletonMirrorReceipt := Receipt EJMSingletonCacheData.mirror

def triangleNormalized (transitionLookup : PackedInput → Option TrianglePackedReceipt)
    (mirrorLookup : Fin 41294 → Option TriangleMirrorReceipt)
    (input : LocalInput 41294 10) : CachedLocal 41294 :=
  normalizedLocal (by decide) EJMTriangleCacheData.mirror
    (fun s i => (trianglePreimage s i).val) triangleCompose transitionLookup mirrorLookup input

def singletonNormalized (transitionLookup : PackedInput → Option SingletonPackedReceipt)
    (mirrorLookup : Fin 8689 → Option SingletonMirrorReceipt)
    (input : LocalInput 8689 9) : CachedLocal 8689 :=
  normalizedLocal (by decide) EJMSingletonCacheData.mirror
    (fun s i => (singletonPreimage s i).val) singletonCompose transitionLookup mirrorLookup input

theorem triangleNormalized_eq (transitionLookup : PackedInput → Option TrianglePackedReceipt)
    (mirrorLookup : Fin 41294 → Option TriangleMirrorReceipt) (input : LocalInput 41294 10) :
    triangleNormalized transitionLookup mirrorLookup input = triangleActual input :=
  normalizedLocal_eq (by decide) EJMTriangleCacheData.mirror
    (fun s i => (trianglePreimage s i).val) triangleCompose transitionLookup mirrorLookup input

theorem singletonNormalized_eq (transitionLookup : PackedInput → Option SingletonPackedReceipt)
    (mirrorLookup : Fin 8689 → Option SingletonMirrorReceipt) (input : LocalInput 8689 9) :
    singletonNormalized transitionLookup mirrorLookup input = singletonActual input :=
  normalizedLocal_eq (by decide) EJMSingletonCacheData.mirror
    (fun s i => (singletonPreimage s i).val) singletonCompose transitionLookup mirrorLookup input

/-- This is a receipt for the original complete nine-field key. Its transparent
output shares only proved internal calculations; outer key checking remains
the unchanged memoStep used by memoGlobalStep. -/
def triangleOracle (transitionLookup : PackedInput → Option TrianglePackedReceipt)
    (mirrorLookup : Fin 41294 → Option TriangleMirrorReceipt)
    (input : LocalInput 41294 10) : Option TriangleReceipt :=
  some ⟨input, triangleNormalized transitionLookup mirrorLookup input,
    triangleNormalized_eq transitionLookup mirrorLookup input⟩

def singletonOracle (transitionLookup : PackedInput → Option SingletonPackedReceipt)
    (mirrorLookup : Fin 8689 → Option SingletonMirrorReceipt)
    (input : LocalInput 8689 9) : Option SingletonReceipt :=
  some ⟨input, singletonNormalized transitionLookup mirrorLookup input,
    singletonNormalized_eq transitionLookup mirrorLookup input⟩

/-- Leading zero outcomes, original initial cache, all thirty-two rows and the
original depth-dependent coordinate are retained in the complete prefix. -/
def memoPrefixCache (triangleLookup : LocalInput 41294 10 → Option TriangleReceipt)
    (singletonLookup : LocalInput 8689 9 → Option SingletonReceipt) : ℕ → ℕ → Cache
  | 0, _ => EJMCacheSoundness.initial
  | depth + 1, code => memoGlobalStep triangleLookup singletonLookup
      (memoPrefixCache triangleLookup singletonLookup depth (code / 4)) (coordinate depth)
      ⟨code % 4, Nat.mod_lt _ (by decide)⟩

/-- Structural induction applies to every depth and every full prefix code;
there is no imported finite list of accepted prefixes. -/
theorem memoPrefixCache_eq_actual
    (triangleLookup : LocalInput 41294 10 → Option TriangleReceipt)
    (singletonLookup : LocalInput 8689 9 → Option SingletonReceipt) (depth code : ℕ) :
    memoPrefixCache triangleLookup singletonLookup depth code = prefixCache depth code := by
  induction depth generalizing code with
  | zero => rfl
  | succ depth ih =>
    simp only [memoPrefixCache, prefixCache, memoGlobalStep_eq, ih]

/-- The unchanged Accepted proposition, including its actual original packed
nodes, fuel, complete partial assignment, lower/scale and symmetry predicate. -/
theorem accepted_iff_memo
    (triangleLookup : LocalInput 41294 10 → Option TriangleReceipt)
    (singletonLookup : LocalInput 8689 9 → Option SingletonReceipt)
    (depth code : ℕ) (index : Fin EJMOriginalGlobalDAGData.Size) :
    Accepted depth code index ↔
      check EJMOriginalGlobalDAGData.nodes (memoGlobalStep triangleLookup singletonLookup)
        lower EJMGlobalScoreSymmetry.dominates scale (21 - depth) index
        (memoPrefixCache triangleLookup singletonLookup depth code) (prefixPartial depth code) = true := by
  unfold Accepted
  rw [memoPrefixCache_eq_actual, check_eq_actual]

#print axioms packedActual_ofLocal
#print axioms normalizedLocal_eq
#print axioms triangleNormalized_eq
#print axioms singletonNormalized_eq
#print axioms memoPrefixCache_eq_actual
#print axioms accepted_iff_memo

end D5.S3.Quantum.Entanglement.EJM.EJMCertifiedNormalizedLocalTransitionMemo
