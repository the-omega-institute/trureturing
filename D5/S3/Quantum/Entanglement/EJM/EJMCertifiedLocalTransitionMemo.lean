/- Candidate only: not installed, elaborated, kernel checked or cost accepted.
   The local keys retain all nine input fields. Every original replay input
   remains explicit; no new acceptance or global-bound assumption is used. -/
import D5.S0.Certificates.CertifiedLocalTransitionMemo
import D5.S3.Quantum.Entanglement.EJM.EJMOriginalReplayAssembly

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Entanglement.EJM.EJMCertifiedLocalTransitionMemo

open D5.S0.Certificates.CertifiedLocalTransitionMemo (Receipt memoStep memoStep_eq)
open D5.S0.Certificates.FiniteSymmetryBoundReplay (Partial)
open D5.S0.Certificates.FiniteCachedSymmetryDAGReplay (check checkPrefix)
open EJMCacheState (Cache CachedLocal triangleStep singletonStep step lower)
open EJMLocalCacheData (triangleIncidence singletonIncidence)
open EJMPartialBoundData (scale)

/-- Three State indices, four complete MirrorRow fields, coordinate and value.
The hash is one row field, never an equality witness for the other fields. -/
structure LocalInput (N dimensions : ℕ) where
  rowIndex : Fin N
  coordinateAction : Fin 12
  outcomeAction : Fin 24
  rowHash : ℕ
  rowLower : ℤ
  rowSlots : ℕ
  rowEdges : ℕ
  coordinate : Fin dimensions
  value : Fin 4
  deriving DecidableEq

def LocalInput.current {N dimensions : ℕ} (input : LocalInput N dimensions) :
    CachedLocal N :=
  ⟨(input.rowIndex, (input.coordinateAction, input.outcomeAction)),
   ⟨input.rowHash, input.rowLower, input.rowSlots, input.rowEdges⟩⟩

def LocalInput.ofCurrent {N dimensions : ℕ} (current : CachedLocal N)
    (i : Fin dimensions) (a : Fin 4) : LocalInput N dimensions :=
  ⟨current.state.1, current.state.2.1, current.state.2.2,
   current.row.hash, current.row.lower, current.row.slots, current.row.edges, i, a⟩

/-- Candidate selection can deliberately ignore the four row fields. A collision
still passes through memoStep's complete nine-field equality check. -/
def LocalInput.bucket {N dimensions : ℕ} (input : LocalInput N dimensions) : ℕ :=
  ((((input.rowIndex.val * 12 + input.coordinateAction.val) * 24 +
      input.outcomeAction.val) * dimensions + input.coordinate.val) * 4 +
      input.value.val)

def triangleActual (input : LocalInput 41294 10) : CachedLocal 41294 :=
  triangleStep input.current input.coordinate input.value

def singletonActual (input : LocalInput 8689 9) : CachedLocal 8689 :=
  singletonStep input.current input.coordinate input.value

abbrev TriangleReceipt := Receipt triangleActual
abbrev SingletonReceipt := Receipt singletonActual

/-- The supplied equation proves the entire actual output, including its row.
An existing state-and-canonical-mirror theorem can supply this equation. -/
def triangleReceipt (current proposed : CachedLocal 41294) (i : Fin 10) (a : Fin 4)
    (exactUpdate : triangleStep current i a = proposed) : TriangleReceipt where
  input := LocalInput.ofCurrent current i a
  output := proposed
  correct := exactUpdate.symm

def singletonReceipt (current proposed : CachedLocal 8689) (i : Fin 9) (a : Fin 4)
    (exactUpdate : singletonStep current i a = proposed) : SingletonReceipt where
  input := LocalInput.ofCurrent current i a
  output := proposed
  correct := exactUpdate.symm

def triangleMemo (lookup : LocalInput 41294 10 → Option TriangleReceipt)
    (current : CachedLocal 41294) (i : Fin 10) (a : Fin 4) : CachedLocal 41294 :=
  memoStep triangleActual lookup (LocalInput.ofCurrent current i a)

def singletonMemo (lookup : LocalInput 8689 9 → Option SingletonReceipt)
    (current : CachedLocal 8689) (i : Fin 9) (a : Fin 4) : CachedLocal 8689 :=
  memoStep singletonActual lookup (LocalInput.ofCurrent current i a)

theorem triangleMemo_eq (lookup : LocalInput 41294 10 → Option TriangleReceipt)
    (current : CachedLocal 41294) (i : Fin 10) (a : Fin 4) :
    triangleMemo lookup current i a = triangleStep current i a :=
  memoStep_eq triangleActual lookup (LocalInput.ofCurrent current i a)

theorem singletonMemo_eq (lookup : LocalInput 8689 9 → Option SingletonReceipt)
    (current : CachedLocal 8689) (i : Fin 9) (a : Fin 4) :
    singletonMemo lookup current i a = singletonStep current i a :=
  memoStep_eq singletonActual lookup (LocalInput.ofCurrent current i a)

/-- Keep every one of the sixteen triangle and sixteen singleton rows and the
original incidence decisions. Unaffected rows are copied verbatim. -/
def memoGlobalStep (triangleLookup : LocalInput 41294 10 → Option TriangleReceipt)
    (singletonLookup : LocalInput 8689 9 → Option SingletonReceipt)
    (cache : Cache) (g : Fin 20) (a : Fin 4) : Cache :=
  ⟨fun k => match triangleIncidence g k with
     | none => cache.triangle k
     | some i => triangleMemo triangleLookup (cache.triangle k) i a,
   fun k => match singletonIncidence g k with
     | none => cache.singleton k
     | some i => singletonMemo singletonLookup (cache.singleton k) i a⟩

theorem memoGlobalStep_eq
    (triangleLookup : LocalInput 41294 10 → Option TriangleReceipt)
    (singletonLookup : LocalInput 8689 9 → Option SingletonReceipt)
    (cache : Cache) (g : Fin 20) (a : Fin 4) :
    memoGlobalStep triangleLookup singletonLookup cache g a = step cache g a := by
  simp only [memoGlobalStep, step, triangleMemo_eq, singletonMemo_eq]

theorem memoGlobalStep_fun_eq
    (triangleLookup : LocalInput 41294 10 → Option TriangleReceipt)
    (singletonLookup : LocalInput 8689 9 → Option SingletonReceipt) :
    memoGlobalStep triangleLookup singletonLookup = step :=
  funext fun cache => funext fun g => funext fun a =>
    memoGlobalStep_eq triangleLookup singletonLookup cache g a

/-- The exact original checker: all nodes, fuel, full cache, partial assignment,
original lower/scale, symmetry test and exhaustive value branches are retained. -/
theorem check_eq_actual
    (triangleLookup : LocalInput 41294 10 → Option TriangleReceipt)
    (singletonLookup : LocalInput 8689 9 → Option SingletonReceipt)
    (fuel : ℕ) (index : Fin EJMOriginalGlobalDAGData.Size) (cache : Cache)
    (p : Partial (Fin 20) (Fin 4)) :
    check EJMOriginalGlobalDAGData.nodes (memoGlobalStep triangleLookup singletonLookup)
      lower EJMGlobalScoreSymmetry.dominates scale fuel index cache p =
    check EJMOriginalGlobalDAGData.nodes step
      lower EJMGlobalScoreSymmetry.dominates scale fuel index cache p := by
  rw [memoGlobalStep_fun_eq]

/-- The same extensional transport keeps an arbitrary complete frontier input. -/
theorem checkPrefix_eq_actual
    (triangleLookup : LocalInput 41294 10 → Option TriangleReceipt)
    (singletonLookup : LocalInput 8689 9 → Option SingletonReceipt)
    (frontier : ℕ → Fin EJMOriginalGlobalDAGData.Size → Cache →
      Partial (Fin 20) (Fin 4) → Bool)
    (depth fuel : ℕ) (index : Fin EJMOriginalGlobalDAGData.Size) (cache : Cache)
    (p : Partial (Fin 20) (Fin 4)) :
    checkPrefix EJMOriginalGlobalDAGData.nodes (memoGlobalStep triangleLookup singletonLookup)
      lower EJMGlobalScoreSymmetry.dominates scale frontier depth fuel index cache p =
    checkPrefix EJMOriginalGlobalDAGData.nodes step
      lower EJMGlobalScoreSymmetry.dominates scale frontier depth fuel index cache p := by
  rw [memoGlobalStep_fun_eq]

#print axioms triangleMemo_eq
#print axioms singletonMemo_eq
#print axioms memoGlobalStep_eq
#print axioms check_eq_actual
#print axioms checkPrefix_eq_actual

end D5.S3.Quantum.Entanglement.EJM.EJMCertifiedLocalTransitionMemo
