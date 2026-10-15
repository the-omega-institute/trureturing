/- Prepared transient actual-prefix semantic bound; uncompiled.
Original anchor: depth13/code4/index674/fuel8. No raw Accepted or
global coverage is asserted. Every original factor, outcome and
scaled integer is retained; no native fact is a mathematical premise. -/
import D5.S3.Quantum.Entanglement.EJM.EJMOriginalReplayAssembly

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536

namespace D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674Common
open D5.S0.Certificates.FiniteSymmetryBoundReplay
open D5.S3.Quantum.Entanglement.EJM.EJMOriginalReplayAssembly (prefixPartial)
open D5.S3.Quantum.Entanglement.EJM.EJMCertificateData (F1 F2)
open D5.S3.Quantum.Entanglement.EJMInflationScore (lhsTriangle lhsSingleton triangleBlock singletonBlock)

open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundData (LocalSym triangleRows singletonRows)
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundTransport (trianglePartialAct singletonPartialAct)
open D5.S3.Quantum.Entanglement.EJM.EJMCacheState (CachedLocal)
open D5.S3.Quantum.Entanglement.EJM.EJMCacheSoundness (TriangleValid SingletonValid)

def mkTriangle (s : Fin 41294 × LocalSym) : CachedLocal 41294 :=
  ⟨s, EJMTriangleCacheData.mirror s.1⟩
def mkSingleton (s : Fin 8689 × LocalSym) : CachedLocal 8689 :=
  ⟨s, EJMSingletonCacheData.mirror s.1⟩

theorem triangle_from_assignment (s : Fin 41294 × LocalSym)
    (p : Partial (Fin 10) (Fin 4))
    (checked : EJMTriangleCacheData.assignment s.1 = trianglePartialAct s.2 p) :
    TriangleValid (mkTriangle s) p := by
  refine ⟨rfl, ?_⟩
  change (triangleRows s.1).assignment = trianglePartialAct s.2 p
  rw [← EJMTriangleCacheReceipts.assignment_eq]
  exact checked

theorem singleton_from_assignment (s : Fin 8689 × LocalSym)
    (p : Partial (Fin 9) (Fin 4))
    (checked : EJMSingletonCacheData.assignment s.1 = singletonPartialAct s.2 p) :
    SingletonValid (mkSingleton s) p := by
  refine ⟨rfl, ?_⟩
  change (singletonRows s.1).assignment = singletonPartialAct s.2 p
  rw [← EJMSingletonCacheReceipts.assignment_eq]
  exact checked

theorem compatible_fill (p : Partial (Fin 20) (Fin 4))
    (e : Event (Fin 20) (Fin 4)) (hp : Compatible p e) (i : Fin 20) :
    Compatible (Function.update p i (some (e i))) e := by
  intro j a ha
  by_cases same : j = i
  · subst j
    simpa only [Function.update_self, Option.some.injEq] using ha
  · rw [Function.update_of_ne same] at ha
    exact hp j a ha

theorem compatible_project {n : ℕ} (p : Partial (Fin 20) (Fin 4))
    (e : Event (Fin 20) (Fin 4)) (projection : Fin n → Fin 20)
    (hp : Compatible p e) : Compatible (p ∘ projection) (e ∘ projection) := by
  intro i a ha
  exact hp (projection i) a ha

/-- Finite-table receipt producers supply a pointwise exact sum; this
composition lemma needs no native minimum, row identity or domain pruning.
The concrete callers below kernel-check every scoped four-valued case. -/
theorem checked_finite_table_merge_lower {Coord Value : Type*}
    (p : Partial Coord Value)
    (left right merged leftScore rightScore : Event Coord Value → ℤ)
    (sumReceipt : ∀ e, merged e = left e + right e)
    (leftLower : ∀ e, Compatible p e → left e ≤ leftScore e)
    (rightLower : ∀ e, Compatible p e → right e ≤ rightScore e)
    (e : Event Coord Value) (hp : Compatible p e) :
    merged e ≤ leftScore e + rightScore e := by
  rw [sumReceipt]
  exact add_le_add (leftLower e hp) (rightLower e hp)

#print axioms checked_finite_table_merge_lower
end D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674Common
