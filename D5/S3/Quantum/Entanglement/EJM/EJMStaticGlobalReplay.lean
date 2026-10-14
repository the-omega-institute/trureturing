/- GID: D5/S3/Quantum/Entanglement/EJM/EJMStaticGlobalReplay
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/EJMStaticGlobalReplay
   mirror-E: none(waiver:actual-exact-certificate-cache)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Quantum/Entanglement/EJM/EJMStaticGlobalReplay.accepted_excludes_triangle_local; instance=D5/S3/Quantum/Entanglement/EJM/EJMGlobalDAGData.root
   digest: Direct full row and action association binds static leaf snapshots to the unchanged original EJM score. -/

/- Prepared, not yet compiled or admitted. Static rows name actual partial
contexts rather than original shared rule indices. All bound snapshots check
their 32 original projections, full mirror row and action-transformed partial
assignment. The complete table and all four child edges remain required.
No complete global acceptance or unconditional locality refutation is asserted. -/

import D5.S0.Certificates.FiniteAnnotatedSymmetryDAG
import D5.S3.Quantum.Entanglement.EJM.EJMCacheSoundness
import D5.S3.Quantum.Entanglement.EJM.EJMGlobalScoreSymmetry

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Entanglement.EJM.EJMStaticGlobalReplay
open D5.S0.Certificates.FiniteSymmetryBoundReplay
open D5.S0.Certificates.FiniteAnnotatedSymmetryDAG (Row)
open D5.S3.Quantum.Entanglement.EJM.EJMCertificateData (F1 F2)
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundData (scale triangleRows singletonRows)
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundTransport
open D5.S3.Quantum.Entanglement.EJM.EJMLocalCacheData (MirrorRow)
open D5.S3.Quantum.Entanglement.EJM.EJMCacheState
open D5.S3.Quantum.Entanglement.EJM.EJMCacheSoundness
open D5.S3.Quantum.Entanglement.EJMInflationScore

private theorem mirror_eq_of_fields (r s : MirrorRow)
    (hh : r.hash = s.hash) (hl : r.lower = s.lower)
    (hs : r.slots = s.slots) (he : r.edges = s.edges) : r = s := by
  cases r
  cases s
  cases hh
  cases hl
  cases hs
  cases he
  rfl

/-- Full row equality and full transported local assignment, with the exact
proposed coordinate and outcome action. No hash equality stands in for either. -/
def checkTriangleSnapshot (current : CachedLocal 41294)
    (p : Partial (Fin 10) (Fin 4)) : Bool :=
  let mirror := EJMTriangleCacheData.mirror current.state.1
  decide (current.row.hash = mirror.hash ∧ current.row.lower = mirror.lower ∧
    current.row.slots = mirror.slots ∧ current.row.edges = mirror.edges ∧
    EJMTriangleCacheData.assignment current.state.1 = trianglePartialAct current.state.2 p)

def checkSingletonSnapshot (current : CachedLocal 8689)
    (p : Partial (Fin 9) (Fin 4)) : Bool :=
  let mirror := EJMSingletonCacheData.mirror current.state.1
  decide (current.row.hash = mirror.hash ∧ current.row.lower = mirror.lower ∧
    current.row.slots = mirror.slots ∧ current.row.edges = mirror.edges ∧
    EJMSingletonCacheData.assignment current.state.1 = singletonPartialAct current.state.2 p)

private theorem checked_triangle_associated (current : CachedLocal 41294)
    (p : Partial (Fin 10) (Fin 4)) (accepted : checkTriangleSnapshot current p = true) :
    TriangleValid current p := by
  have fields := of_decide_eq_true accepted
  refine ⟨mirror_eq_of_fields _ _ fields.1 fields.2.1 fields.2.2.1 fields.2.2.2.1, ?_⟩
  change (triangleRows current.state.1).assignment = trianglePartialAct current.state.2 p
  rw [← EJMTriangleCacheReceipts.assignment_eq]
  exact fields.2.2.2.2

private theorem checked_singleton_associated (current : CachedLocal 8689)
    (p : Partial (Fin 9) (Fin 4)) (accepted : checkSingletonSnapshot current p = true) :
    SingletonValid current p := by
  have fields := of_decide_eq_true accepted
  refine ⟨mirror_eq_of_fields _ _ fields.1 fields.2.1 fields.2.2.1 fields.2.2.2.1, ?_⟩
  change (singletonRows current.state.1).assignment = singletonPartialAct current.state.2 p
  rw [← EJMSingletonCacheReceipts.assignment_eq]
  exact fields.2.2.2.2

/-- Each original projection is checked against its own local state. Arithmetic
then sums the same 32 scaled lower values as the original EJM score bridge. -/
def checkBoundSnapshot (cache : Cache) (p : Partial (Fin 20) (Fin 4)) : Bool :=
  decide ((∀ k, checkTriangleSnapshot (cache.triangle k) (p ∘ lhsTriangle k) = true) ∧
    (∀ k, checkSingletonSnapshot (cache.singleton k) (p ∘ lhsSingleton k) = true) ∧
    scale ≤ lower cache)

theorem checked_bound_snapshot (cache : Cache) (p : Partial (Fin 20) (Fin 4))
    (accepted : checkBoundSnapshot cache p = true)
    (e : Event (Fin 20) (Fin 4)) (hp : Compatible p e) : scale ≤ score F1 F2 e := by
  obtain ⟨triangles, singletons, arithmetic⟩ := of_decide_eq_true accepted
  have associated : AssociatedCache cache p :=
    ⟨fun k => checked_triangle_associated _ _ (triangles k),
     fun k => checked_singleton_associated _ _ (singletons k)⟩
  exact arithmetic.trans (associated_lower_le_score cache p e associated hp)

/-- Complete checked static contexts prove the original threshold directly.
This conditional theorem changes the executable certificate representation,
while its numerical conclusion still consumes the original F1, F2 and score. -/
theorem accepted_score_lower_bound {N : ℕ}
    (rows : Fin N → Row N (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut)
    (snapshots : Fin N → Cache)
    (accepted : ∀ index, D5.S0.Certificates.FiniteAnnotatedSymmetryDAG.checkRow rows
      (fun index p => checkBoundSnapshot (snapshots index) p)
      EJMGlobalScoreSymmetry.dominates index = true)
    (root : Fin N) (rootAssignment : (rows root).assignment = fun _ => none) :
    ∀ e : Event (Fin 20) (Fin 4), scale ≤ score F1 F2 e := by
  exact D5.S0.Certificates.FiniteAnnotatedSymmetryDAG.checked_global_lower_bound
    (score F1 F2) FiniteLex.rank EJMGlobalScoreSymmetry.act scale rows
    (fun index p => checkBoundSnapshot (snapshots index) p) EJMGlobalScoreSymmetry.dominates
    (fun index p e accepted hp => checked_bound_snapshot (snapshots index) p accepted e hp)
    EJMGlobalScoreSymmetry.actual_score_invariant EJMGlobalScoreSymmetry.dominates_rank_lt
    accepted root rootAssignment

theorem accepted_excludes_triangle_local {N : ℕ}
    (rows : Fin N → Row N (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut)
    (snapshots : Fin N → Cache)
    (accepted : ∀ index, D5.S0.Certificates.FiniteAnnotatedSymmetryDAG.checkRow rows
      (fun index p => checkBoundSnapshot (snapshots index) p)
      EJMGlobalScoreSymmetry.dominates index = true)
    (root : Fin N) (rootAssignment : (rows root).assignment = fun _ => none) :
    ¬ D5.S3.Quantum.Entanglement.TriangleSymmetricLocalRefutation.IsTriangleLocal
      ejmDistribution := by
  apply positive_score_excludes_triangle_local F1 F2
  intro e
  exact (by decide : (1 : ℤ) ≤ scale).trans
    (accepted_score_lower_bound rows snapshots accepted root rootAssignment e)

#print axioms checked_bound_snapshot
#print axioms accepted_score_lower_bound
#print axioms accepted_excludes_triangle_local

end D5.S3.Quantum.Entanglement.EJM.EJMStaticGlobalReplay
