/- UNCOMPILED representation candidate. The complete scalar-table receipts
are required. Every original state, local action, future transition, symmetry
test and four-value branch is retained. This module supplies no acceptance.

This alternative reads scalar lowers directly at bound leaves. It avoids
recomputing transitions both for next words and for aggregate deltas; its
performance must be measured on the same actual 545-visit suffix.
-/
import D5.S3.Quantum.Entanglement.EJM.EJMPackedLowerReceipts
import D5.S3.Quantum.Entanglement.EJM.EJMStreamingCachePacking
import D5.S3.Quantum.Entanglement.EJM.EJMCompactDominates

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

namespace D5.S3.Quantum.Entanglement.EJM.EJMPackedLowerReplay
open EJMCachePacking (PackedCache decodeState)
open EJMStreamingCachePacking (sumWords)
open EJMPackedLowerData (triangleLower singletonLower)
open EJMCompactPartial (PackedPartial WellFormed)

def lower (cache : PackedCache) : ℤ :=
  sumWords 16 (fun _ word =>
    triangleLower (decodeState (by decide : 0 < 41294) word).1) cache.triangle +
  sumWords 16 (fun _ word =>
    singletonLower (decodeState (by decide : 0 < 8689) word).1) cache.singleton

theorem lower_eq (cache : PackedCache) :
    lower cache = EJMCachePacking.lower cache := by
  have ht : (fun (_ : Fin 16) word =>
      triangleLower (decodeState (by decide : 0 < 41294) word).1) =
      (fun (_ : Fin 16) word =>
        (EJMTriangleCacheData.mirror (decodeState (by decide : 0 < 41294) word).1).lower) := by
    funext k word
    exact EJMPackedLowerReceipts.triangle_eq _
  have hs : (fun (_ : Fin 16) word =>
      singletonLower (decodeState (by decide : 0 < 8689) word).1) =
      (fun (_ : Fin 16) word =>
        (EJMSingletonCacheData.mirror (decodeState (by decide : 0 < 8689) word).1).lower) := by
    funext k word
    exact EJMPackedLowerReceipts.singleton_eq _
  unfold lower
  rw [ht, hs]
  exact EJMStreamingCachePacking.lower_eq_original cache

def check := EJMCompactDominates.checkFast EJMStreamingCachePacking.step lower
  EJMPartialBoundData.scale

theorem check_eq_original (fuel : ℕ) (index : Fin EJMGlobalDAGData.Size)
    (cache : PackedCache) (q : PackedPartial)
    (hwell : WellFormed q) (hinv : q.depth + fuel = 21) :
    check fuel index cache q =
      D5.S0.Certificates.FiniteCachedSymmetryDAGReplay.check EJMGlobalDAGData.nodes
        EJMCacheState.step EJMCacheState.lower EJMGlobalScoreSymmetry.dominates
        EJMPartialBoundData.scale fuel index (EJMCachePacking.decode cache)
        (EJMCompactPartial.decode q) := by
  have hl : lower = EJMCachePacking.lower := funext lower_eq
  have hs : EJMStreamingCachePacking.step = EJMCachePacking.step := by
    funext cache g a
    exact EJMStreamingCachePacking.step_eq_original cache g a
  unfold check
  rw [hl, hs]
  exact (EJMCompactDominates.checkFast_eq_original EJMCachePacking.step
    EJMCachePacking.lower fuel index cache q hwell hinv).trans
      (EJMCachePacking.check_decode EJMGlobalDAGData.nodes
        EJMGlobalScoreSymmetry.dominates EJMPartialBoundData.scale fuel index cache
        (EJMCompactPartial.decode q))

#print axioms lower_eq
#print axioms check_eq_original
end D5.S3.Quantum.Entanglement.EJM.EJMPackedLowerReplay
