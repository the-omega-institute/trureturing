/- GID: D5/S3/Quantum/Entanglement/EJM/EJMSharedLocalReadouts
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/EJMSharedLocalReadouts
   mirror-E: none(waiver:actual-exact-certificate-cache)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Quantum/Entanglement/EJM/EJMStaticGlobalReplay.accepted_excludes_triangle_local; instance=D5/S3/Quantum/Entanglement/EJM/EJMSharedLocalReadoutsPilot.triangle_accepted
   digest: Shared original local row and action readouts retain all thirty-two actual inflation-score projection checks. -/

/- Prepared source, not yet compiled or admitted. The first concrete table
must be kernel checked before this checker is delivered. Complete global
context acceptance remains required for the original score margin. -/

import D5.S0.Certificates.FiniteSharedLocalBounds
import D5.S3.Quantum.Entanglement.EJM.EJMTriangleCacheReceipts
import D5.S3.Quantum.Entanglement.EJM.EJMSingletonCacheReceipts
import D5.S3.Quantum.Entanglement.EJM.EJMLocalBoundAcceptance

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Entanglement.EJM.EJMSharedLocalReadouts
open D5.S0.Certificates.FiniteSymmetryBoundReplay
open D5.S0.Certificates.FiniteSharedLocalBounds
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundData
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundTransport
open D5.S3.Quantum.Entanglement.EJM.EJMScoreSymmetry
open D5.S3.Quantum.Entanglement.EJMInflationScore
open D5.S3.Quantum.Entanglement.EJM.EJMCertificateData (F1 F2)
open scoped BigOperators

abbrev TriangleReadout := Readout 41294 (Fin 10) (Fin 4) LocalSym
abbrev SingletonReadout := Readout 8689 (Fin 9) (Fin 4) LocalSym

def checkTriangle : TriangleReadout → Bool :=
  checkReadout EJMTriangleCacheData.assignment EJMTriangleCacheData.lower trianglePartialAct

def checkSingleton : SingletonReadout → Bool :=
  checkReadout EJMSingletonCacheData.assignment EJMSingletonCacheData.lower singletonPartialAct

def checkBound {T S : ℕ}
    (triangles : Fin T → TriangleReadout) (singletons : Fin S → SingletonReadout)
    (triangleSelection : Fin 16 → Fin T) (singletonSelection : Fin 16 → Fin S)
    (p : Partial (Fin 20) (Fin 4)) : Bool :=
  decide (checkSelection triangles triangleSelection lhsTriangle p = true ∧
    checkSelection singletons singletonSelection lhsSingleton p = true ∧
    scale ≤ (∑ k, (triangles (triangleSelection k)).lower) +
      ∑ k, (singletons (singletonSelection k)).lower)

/-- The exact original local certificates discharge the numerical premises.
Each actual leaf independently checks all projections and the original sum. -/
theorem checked_bound {T S : ℕ}
    (triangles : Fin T → TriangleReadout) (singletons : Fin S → SingletonReadout)
    (trianglesAccepted : ∀ j, checkTriangle (triangles j) = true)
    (singletonsAccepted : ∀ j, checkSingleton (singletons j) = true)
    (triangleSelection : Fin 16 → Fin T) (singletonSelection : Fin 16 → Fin S)
    (p : Partial (Fin 20) (Fin 4))
    (accepted : checkBound triangles singletons triangleSelection singletonSelection p = true)
    (e : Event (Fin 20) (Fin 4)) (hp : Compatible p e) : scale ≤ score F1 F2 e := by
  obtain ⟨triangleProjections, singletonProjections, arithmetic⟩ := of_decide_eq_true accepted
  have ht := checked_selection_sum_lower (triangleCentered F1) triangleAct trianglePartialAct
    triangle_compatible triangle_score_invariant triangleRows EJMLocalBoundAcceptance.triangle_accepted
    EJMTriangleCacheData.assignment EJMTriangleCacheData.lower
    EJMTriangleCacheReceipts.assignment_eq EJMTriangleCacheReceipts.lower_eq
    triangles trianglesAccepted triangleSelection lhsTriangle p triangleProjections e hp
  have hs := checked_selection_sum_lower (singletonCentered F2) singletonAct singletonPartialAct
    singleton_compatible singleton_score_invariant singletonRows EJMLocalBoundAcceptance.singleton_accepted
    EJMSingletonCacheData.assignment EJMSingletonCacheData.lower
    EJMSingletonCacheReceipts.assignment_eq EJMSingletonCacheReceipts.lower_eq
    singletons singletonsAccepted singletonSelection lhsSingleton p singletonProjections e hp
  exact arithmetic.trans (add_le_add ht hs)

#print axioms checked_bound
end D5.S3.Quantum.Entanglement.EJM.EJMSharedLocalReadouts
