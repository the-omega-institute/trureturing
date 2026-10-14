/- GID: D5/S3/Quantum/Entanglement/EJM/EJMStaticGlobalReplay
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/EJMStaticGlobalReplay
   mirror-E: none(waiver:actual-exact-certificate-cache)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Quantum/Entanglement/EJM/EJMStaticGlobalReplay.accepted_excludes_triangle_local; instance=D5/S3/Quantum/Entanglement/EJM/EJMGlobalDAGData.root
   digest: Shared exact local readouts bind every actual static leaf projection to the unchanged original EJM score. -/

/- Prepared, not yet compiled or admitted. Static rows name actual partial
contexts rather than original shared rule indices. Every bound leaf checks
its 32 actual projections against shared original row and action readouts.
The complete table and all four child edges remain required.
No complete global acceptance or unconditional locality refutation is asserted. -/

import D5.S0.Certificates.FiniteAnnotatedSymmetryDAG
import D5.S3.Quantum.Entanglement.EJM.EJMSharedLocalReadouts
import D5.S3.Quantum.Entanglement.EJM.EJMGlobalScoreSymmetry

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Entanglement.EJM.EJMStaticGlobalReplay
open D5.S0.Certificates.FiniteSymmetryBoundReplay
open D5.S0.Certificates.FiniteAnnotatedSymmetryDAG (Row)
open D5.S3.Quantum.Entanglement.EJM.EJMCertificateData (F1 F2)
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundData (scale)
open D5.S3.Quantum.Entanglement.EJM.EJMSharedLocalReadouts
open D5.S3.Quantum.Entanglement.EJMInflationScore

/-- Complete checked static contexts prove the original threshold directly.
This conditional theorem changes the executable certificate representation,
while its numerical conclusion still consumes the original F1, F2 and score. -/
theorem accepted_score_lower_bound {N T S : ℕ}
    (triangles : Fin T → TriangleReadout) (singletons : Fin S → SingletonReadout)
    (trianglesAccepted : ∀ j, checkTriangle (triangles j) = true)
    (singletonsAccepted : ∀ j, checkSingleton (singletons j) = true)
    (rows : Fin N → Row N (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut)
    (triangleSelection : Fin N → Fin 16 → Fin T)
    (singletonSelection : Fin N → Fin 16 → Fin S)
    (accepted : ∀ index, D5.S0.Certificates.FiniteAnnotatedSymmetryDAG.checkRow rows
      (fun index p => checkBound triangles singletons
        (triangleSelection index) (singletonSelection index) p)
      EJMGlobalScoreSymmetry.dominates index = true)
    (root : Fin N) (rootAssignment : (rows root).assignment = fun _ => none) :
    ∀ e : Event (Fin 20) (Fin 4), scale ≤ score F1 F2 e := by
  exact D5.S0.Certificates.FiniteAnnotatedSymmetryDAG.checked_global_lower_bound
    (score F1 F2) FiniteLex.rank EJMGlobalScoreSymmetry.act scale rows
    (fun index p => checkBound triangles singletons
      (triangleSelection index) (singletonSelection index) p) EJMGlobalScoreSymmetry.dominates
    (fun index p e accepted hp => checked_bound triangles singletons
      trianglesAccepted singletonsAccepted (triangleSelection index)
      (singletonSelection index) p accepted e hp)
    EJMGlobalScoreSymmetry.actual_score_invariant EJMGlobalScoreSymmetry.dominates_rank_lt
    accepted root rootAssignment

theorem accepted_excludes_triangle_local {N T S : ℕ}
    (triangles : Fin T → TriangleReadout) (singletons : Fin S → SingletonReadout)
    (trianglesAccepted : ∀ j, checkTriangle (triangles j) = true)
    (singletonsAccepted : ∀ j, checkSingleton (singletons j) = true)
    (rows : Fin N → Row N (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut)
    (triangleSelection : Fin N → Fin 16 → Fin T)
    (singletonSelection : Fin N → Fin 16 → Fin S)
    (accepted : ∀ index, D5.S0.Certificates.FiniteAnnotatedSymmetryDAG.checkRow rows
      (fun index p => checkBound triangles singletons
        (triangleSelection index) (singletonSelection index) p)
      EJMGlobalScoreSymmetry.dominates index = true)
    (root : Fin N) (rootAssignment : (rows root).assignment = fun _ => none) :
    ¬ D5.S3.Quantum.Entanglement.TriangleSymmetricLocalRefutation.IsTriangleLocal
      ejmDistribution := by
  apply positive_score_excludes_triangle_local F1 F2
  intro e
  exact (by decide : (1 : ℤ) ≤ scale).trans
    (accepted_score_lower_bound triangles singletons trianglesAccepted singletonsAccepted
      rows triangleSelection singletonSelection accepted root rootAssignment e)

#print axioms accepted_score_lower_bound
#print axioms accepted_excludes_triangle_local

end D5.S3.Quantum.Entanglement.EJM.EJMStaticGlobalReplay
