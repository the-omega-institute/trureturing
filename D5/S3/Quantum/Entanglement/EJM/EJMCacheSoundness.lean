/- GID: D5/S3/Quantum/Entanglement/EJM/EJMCacheSoundness
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/EJMCacheSoundness
   mirror-E: none(waiver:actual-exact-certificate-cache)
   anchors: []
   utility: none
   digest: Full original block association survives every unknown-coordinate update and bounds the unchanged actual EJM score. -/

/- Prepared source, not compiled. The consumed receipts cover every actual
local row mirror and all 408356 unknown-coordinate/value transitions. No
producer premise or guessed action equation is used. This proof is part of
the same exact certificate, whose complete actual global acceptance is still
required before delivering a locality refutation. -/

import D5.S3.Quantum.Entanglement.EJM.EJMCacheState
import D5.S3.Quantum.Entanglement.EJM.EJMCacheLaws
import D5.S3.Quantum.Entanglement.EJM.EJMTriangleCacheReceipts
import D5.S3.Quantum.Entanglement.EJM.EJMSingletonCacheReceipts
import D5.S3.Quantum.Entanglement.EJM.EJMLocalBoundAcceptance

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Entanglement.EJM.EJMCacheSoundness
open D5.S0.Certificates.FiniteSymmetryBoundReplay
open D5.S0.Certificates.FiniteLocalRowCache (Associated)
open D5.S3.Quantum.Entanglement.EJM.EJMCertificateData (F1 F2 trianglePerm singletonPerm)
open D5.S3.Quantum.Entanglement.EJM.EJMScoreSymmetry (triangleCentered singletonCentered)
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundData
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundTransport
open D5.S3.Quantum.Entanglement.EJM.EJMLocalCacheData
open D5.S3.Quantum.Entanglement.EJM.EJMCacheState
open D5.S3.Quantum.Entanglement.EJM.EJMCacheLaws
open D5.S3.Quantum.Entanglement.EJMInflationScore
open scoped BigOperators

private def identity : LocalSym := (0, 0)

/-- The actual empty-assignment cache uses the original final row of each
local table and the identity action. Its association is proved below. -/
def initial : Cache :=
  ⟨fun _ => ⟨(41293, identity), EJMTriangleCacheData.mirror 41293⟩,
   fun _ => ⟨(8688, identity), EJMSingletonCacheData.mirror 8688⟩⟩

private theorem triangle_identity_receipt : trianglePerm 0 = id := by decide +kernel
private theorem singleton_identity_receipt : singletonPerm 0 = id := by decide +kernel
private theorem outcome_identity_receipt : outcome 0 = id := by decide +kernel

private theorem triangle_identity (p : Partial (Fin 10) (Fin 4)) :
    trianglePartialAct identity p = p := by
  funext i
  change (p (trianglePerm 0 i)).map (outcome 0) = p i
  rw [triangle_identity_receipt, outcome_identity_receipt]
  exact congrFun Option.map_id (p i)

private theorem singleton_identity (p : Partial (Fin 9) (Fin 4)) :
    singletonPartialAct identity p = p := by
  funext i
  change (p (singletonPerm 0 i)).map (outcome 0) = p i
  rw [singleton_identity_receipt, outcome_identity_receipt]
  exact congrFun Option.map_id (p i)

def TriangleValid (current : CachedLocal 41294) (p : Partial (Fin 10) (Fin 4)) : Prop :=
  current.row = EJMTriangleCacheData.mirror current.state.1 ∧
    Associated trianglePartialAct triangleRows current.state p

def SingletonValid (current : CachedLocal 8689) (p : Partial (Fin 9) (Fin 4)) : Prop :=
  current.row = EJMSingletonCacheData.mirror current.state.1 ∧
    Associated singletonPartialAct singletonRows current.state p

def AssociatedCache (cache : Cache) (p : Partial (Fin 20) (Fin 4)) : Prop :=
  (∀ k, TriangleValid (cache.triangle k) (p ∘ lhsTriangle k)) ∧
    ∀ k, SingletonValid (cache.singleton k) (p ∘ lhsSingleton k)

theorem triangle_step_valid (current : CachedLocal 41294) (p : Partial (Fin 10) (Fin 4))
    (valid : TriangleValid current p) (i : Fin 10) (a : Fin 4) (unknown : p i = none) :
    TriangleValid (triangleStep current i a) (Function.update p i (some a)) := by
  have rowUnknown : (triangleRows current.state.1).assignment
      (trianglePreimage current.state.2 i) = none := by
    rw [valid.2]
    exact triangle_unknown current.state.2 p i unknown
  have accepted := EJMTriangleCacheReceipts.transition_accepted current.state.1
    (trianglePreimage current.state.2 i) (outcome current.state.2.2 a) rowUnknown
  have associated := D5.S0.Certificates.FiniteLocalRowCache.checked_step_associated
    trianglePartialAct triangleRows EJMTriangleCacheData.transition trianglePreimage
    (fun s a => outcome s.2 a) triangleCompose triangle_update triangle_compose
    current.state p valid.2 i a accepted
  have hstate : (triangleStep current i a).state =
      D5.S0.Certificates.FiniteLocalRowCache.step EJMTriangleCacheData.transition
        trianglePreimage (fun s a => outcome s.2 a) triangleCompose current.state i a := by
    simp only [triangleStep, D5.S0.Certificates.FiniteLocalRowCache.step,
      EJMTriangleCacheData.transition, valid.1]
  exact ⟨rfl, by simpa only [hstate] using associated⟩

theorem singleton_step_valid (current : CachedLocal 8689) (p : Partial (Fin 9) (Fin 4))
    (valid : SingletonValid current p) (i : Fin 9) (a : Fin 4) (unknown : p i = none) :
    SingletonValid (singletonStep current i a) (Function.update p i (some a)) := by
  have rowUnknown : (singletonRows current.state.1).assignment
      (singletonPreimage current.state.2 i) = none := by
    rw [valid.2]
    exact singleton_unknown current.state.2 p i unknown
  have accepted := EJMSingletonCacheReceipts.transition_accepted current.state.1
    (singletonPreimage current.state.2 i) (outcome current.state.2.2 a) rowUnknown
  have associated := D5.S0.Certificates.FiniteLocalRowCache.checked_step_associated
    singletonPartialAct singletonRows EJMSingletonCacheData.transition singletonPreimage
    (fun s a => outcome s.2 a) singletonCompose singleton_update singleton_compose
    current.state p valid.2 i a accepted
  have hstate : (singletonStep current i a).state =
      D5.S0.Certificates.FiniteLocalRowCache.step EJMSingletonCacheData.transition
        singletonPreimage (fun s a => outcome s.2 a) singletonCompose current.state i a := by
    simp only [singletonStep, D5.S0.Certificates.FiniteLocalRowCache.step,
      EJMSingletonCacheData.transition, valid.1]
  exact ⟨rfl, by simpa only [hstate] using associated⟩

/-- A global fill changes the whole original local projection by the proved
injective incidence law, not by an assumed representative mask. -/
theorem step_associated (cache : Cache) (p : Partial (Fin 20) (Fin 4))
    (associated : AssociatedCache cache p) (g : Fin 20) (a : Fin 4) (unknown : p g = none) :
    AssociatedCache (step cache g a) (Function.update p g (some a)) := by
  constructor
  · intro k
    have projection := triangle_projection_update p g a k
    cases incidence : triangleIncidence g k with
    | none =>
      simpa only [step, projection, incidence] using associated.1 k
    | some i =>
      have localUnknown : (p ∘ lhsTriangle k) i = none := by
        change p (lhsTriangle k i) = none
        rw [triangle_incidence_some g k i incidence, unknown]
      simpa only [step, projection, incidence] using
        triangle_step_valid (cache.triangle k) _ (associated.1 k) i a localUnknown
  · intro k
    have projection := singleton_projection_update p g a k
    cases incidence : singletonIncidence g k with
    | none =>
      simpa only [step, projection, incidence] using associated.2 k
    | some i =>
      have localUnknown : (p ∘ lhsSingleton k) i = none := by
        change p (lhsSingleton k i) = none
        rw [singleton_incidence_some g k i incidence, unknown]
      simpa only [step, projection, incidence] using
        singleton_step_valid (cache.singleton k) _ (associated.2 k) i a localUnknown

set_option maxHeartbeats 10000000 in
-- This finite kernel receipt exhausts its explicit concrete domain; no producer premise is used.
private theorem triangle_mirror_root : EJMTriangleCacheData.assignment 41293 =
    (fun _ => none) := by decide +kernel
set_option maxHeartbeats 10000000 in
-- This finite kernel receipt exhausts its explicit concrete domain; no producer premise is used.
private theorem singleton_mirror_root : EJMSingletonCacheData.assignment 8688 =
    (fun _ => none) := by decide +kernel

theorem initial_associated : AssociatedCache initial (fun _ => none) := by
  constructor
  · intro k
    constructor
    · rfl
    · change (triangleRows (41293 : Fin 41294)).assignment =
        trianglePartialAct identity (fun _ => none)
      rw [triangle_identity, ← EJMTriangleCacheReceipts.assignment_eq, triangle_mirror_root]
  · intro k
    constructor
    · rfl
    · change (singletonRows (8688 : Fin 8689)).assignment =
        singletonPartialAct identity (fun _ => none)
      rw [singleton_identity, ← EJMSingletonCacheReceipts.assignment_eq, singleton_mirror_root]

theorem triangle_valid_lower (current : CachedLocal 41294) (p : Partial (Fin 10) (Fin 4))
    (e : Event (Fin 10) (Fin 4)) (valid : TriangleValid current p) (hp : Compatible p e) :
    current.row.lower ≤ triangleCentered F1 e := by
  rw [valid.1]
  change EJMTriangleCacheData.lower current.state.1 ≤ triangleCentered F1 e
  rw [EJMTriangleCacheReceipts.lower_eq]
  exact D5.S0.Certificates.FiniteLocalRowCache.associated_lower_bound
    (triangleCentered F1) triangleAct trianglePartialAct triangle_compatible
    triangle_score_invariant triangleRows EJMLocalBoundAcceptance.triangle_accepted
    current.state p e valid.2 hp

theorem singleton_valid_lower (current : CachedLocal 8689) (p : Partial (Fin 9) (Fin 4))
    (e : Event (Fin 9) (Fin 4)) (valid : SingletonValid current p) (hp : Compatible p e) :
    current.row.lower ≤ singletonCentered F2 e := by
  rw [valid.1]
  change EJMSingletonCacheData.lower current.state.1 ≤ singletonCentered F2 e
  rw [EJMSingletonCacheReceipts.lower_eq]
  exact D5.S0.Certificates.FiniteLocalRowCache.associated_lower_bound
    (singletonCentered F2) singletonAct singletonPartialAct singleton_compatible
    singleton_score_invariant singletonRows EJMLocalBoundAcceptance.singleton_accepted
    current.state p e valid.2 hp

theorem associated_lower_le_score (cache : Cache) (p : Partial (Fin 20) (Fin 4))
    (e : Event (Fin 20) (Fin 4)) (associated : AssociatedCache cache p)
    (hp : Compatible p e) : lower cache ≤ score F1 F2 e := by
  have ht : (∑ k : Fin 16, (cache.triangle k).row.lower) ≤
      ∑ k : Fin 16, triangleBlock F1 k e := by
    apply Finset.sum_le_sum
    intro k _
    have hc : Compatible (p ∘ lhsTriangle k) (e ∘ lhsTriangle k) := by
      intro i a ha
      exact hp (lhsTriangle k i) a ha
    exact triangle_valid_lower _ _ _ (associated.1 k) hc
  have hs : (∑ k : Fin 16, (cache.singleton k).row.lower) ≤
      ∑ k : Fin 16, singletonBlock F2 k e := by
    apply Finset.sum_le_sum
    intro k _
    have hc : Compatible (p ∘ lhsSingleton k) (e ∘ lhsSingleton k) := by
      intro i a ha
      exact hp (lhsSingleton k i) a ha
    exact singleton_valid_lower _ _ _ (associated.2 k) hc
  exact add_le_add ht hs

#print axioms triangle_step_valid
#print axioms singleton_step_valid
#print axioms step_associated
#print axioms initial_associated
#print axioms associated_lower_le_score

end D5.S3.Quantum.Entanglement.EJM.EJMCacheSoundness
