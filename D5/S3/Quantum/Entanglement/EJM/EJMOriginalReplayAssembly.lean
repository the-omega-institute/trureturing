/- GID: D5/S3/Quantum/Entanglement/EJM/EJMOriginalReplayAssembly
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/EJMOriginalReplayAssembly
   mirror-E: none(waiver:actual-complete-original-dag-input)
   anchors: []
   utility: none
   digest: Actual base-four prefixes bind every original cache update and partial event when assembling adaptive suffix receipts. -/

/- Prepared source, not yet compiled. The complete original replay still
requires all of its actual suffix receipts. These composition lemmas transfer
no acceptance between equal shape IDs or different original contexts. -/

import D5.S3.Quantum.Entanglement.EJM.EJMOriginalCachedGlobalReplay

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Entanglement.EJM.EJMOriginalReplayAssembly
open D5.S0.Certificates.FiniteSymmetryBoundReplay (Partial)
open D5.S0.Certificates.FiniteCachedSymmetryDAGReplay (check checked_split)
open D5.S3.Quantum.Entanglement.EJM.EJMCacheState
open D5.S3.Quantum.Entanglement.EJM.EJMCacheSoundness (initial)
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundData (scale)

/-- The natural original coordinate at a prefix depth. The assembly theorem
restricts this coordinate to depths below twenty. -/
def coordinate (depth : ℕ) : Fin 20 := ⟨depth % 20, Nat.mod_lt _ (by decide)⟩

/-- All thirty-two original states are computed from the actual initial cache
and every digit of the prefix, including leading zero outcomes. -/
def prefixCache : ℕ → ℕ → Cache
  | 0, _ => initial
  | depth + 1, code => step (prefixCache depth (code / 4)) (coordinate depth)
      ⟨code % 4, Nat.mod_lt _ (by decide)⟩

/-- The partial assignment follows exactly the same prefix and updates as the
cache. Its depth remains explicit, so leading zeros never discard coordinates. -/
def prefixPartial : ℕ → ℕ → Partial (Fin 20) (Fin 4)
  | 0, _ => fun _ => none
  | depth + 1, code => Function.update (prefixPartial depth (code / 4))
      (coordinate depth) (some ⟨code % 4, Nat.mod_lt _ (by decide)⟩)

/-- An actual suffix receipt retains its original depth, entire prefix,
remaining fuel, node index, cache and partial assignment. -/
def Accepted (depth code : ℕ) (index : Fin EJMOriginalGlobalDAGData.Size) : Prop :=
  check EJMOriginalGlobalDAGData.nodes step lower EJMGlobalScoreSymmetry.dominates
    scale (21 - depth) index (prefixCache depth code) (prefixPartial depth code) = true

/-- Adaptive cuts assemble through the actual four original value branches.
No fixed-depth frontier or context-free shape acceptance is assumed. -/
theorem assemble (depth code : ℕ) (index : Fin EJMOriginalGlobalDAGData.Size)
    (within : depth < 20) (children : Fin 4 → Fin EJMOriginalGlobalDAGData.Size)
    (node : EJMOriginalGlobalDAGData.nodes (21 - depth) index =
      .split (coordinate depth) children)
    (branches : ∀ a : Fin 4, Accepted (depth + 1) (4 * code + a.val) (children a)) :
    Accepted depth code index := by
  have fuel : 21 - depth = (21 - (depth + 1)) + 1 := by omega
  unfold Accepted
  rw [fuel]
  apply checked_split EJMOriginalGlobalDAGData.nodes step lower
    EJMGlobalScoreSymmetry.dominates scale (21 - (depth + 1)) index
    (prefixCache depth code) (prefixPartial depth code) (coordinate depth) children
    (by simpa only [← fuel] using node)
  intro a
  have codeDiv : (4 * code + a.val) / 4 = code := by omega
  have codeMod : (4 * code + a.val) % 4 = a.val := by omega
  simpa only [Accepted, prefixCache, prefixPartial, codeDiv, codeMod, Fin.eta]
    using branches a

#print axioms assemble
end D5.S3.Quantum.Entanglement.EJM.EJMOriginalReplayAssembly
