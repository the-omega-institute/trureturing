/- GID: D5/S3/Quantum/Entanglement/EJM/EJMOriginalResidualReplay
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/EJMOriginalResidualReplay
   mirror-E: none(waiver:original-residual-replay)
   anchors: []
   utility: none
   digest: Original residual weights retain the actual marginal coordinates and earn bounds only from checked local rows and every reached global context. -/

import D5.S3.Quantum.Entanglement.EJM.EJMOriginalResidualWeightsData
import D5.S3.Quantum.Entanglement.EJM.EJMOriginalResidualLocalData
import D5.S3.Quantum.Entanglement.EJM.EJMOriginalResidualGlobalData
import D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundLookup

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Entanglement.EJM.EJMOriginalResidualReplay

/-! This unfinished consumer makes the remaining acceptance obligations explicit.
The concrete local checks and complete context-sensitive replay have not been
proved here. A native receipt supplies none of these premises. The residual
score differs from the original centered score; no nonlocality margin follows
without the separate exact residual identity and dual inequalities. -/

open D5.S0.Certificates.FiniteSymmetryBoundReplay
open D5.S0.Certificates.FinitePartialBoundDAG
open D5.S3.Quantum.Entanglement.EJM.EJMCertificateData
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundData (LocalSym outcome)
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundTransport
open EJMOriginalResidualWeightsData
open EJMOriginalResidualLocalData (triangleRows singletonRows)
open EJMOriginalResidualGlobalData (nodes root rankedCoordinate)
open scoped BigOperators

open private orbitKey_relabel orbitKey_coordinate trianglePerm_mul triangleMul_surjective
  singletonPerm_mul singletonMul_surjective from
  D5.S3.Quantum.Entanglement.EJM.EJMCertificateData

private theorem triangle_weight_relabel (e : Fin 10 → Fin 4) (s : Fin 24) :
    triangleWeight (outcome s ∘ e) = triangleWeight e := by
  exact congrArg triangleWeights.get
    (orbitKey_relabel trianglePerm e (outcomeEquiv s) (outcomeEquiv s).injective)

private theorem singleton_weight_relabel (e : Fin 9 → Fin 4) (s : Fin 24) :
    singletonWeight (outcome s ∘ e) = singletonWeight e := by
  exact congrArg singletonWeights.get
    (orbitKey_relabel singletonPerm e (outcomeEquiv s) (outcomeEquiv s).injective)

private theorem triangle_weight_invariant (s : LocalSym) (e : Fin 10 → Fin 4) :
    triangleWeight (triangleAct s e) = triangleWeight e := by
  change triangleWeight (outcome s.2 ∘ (e ∘ trianglePerm s.1)) = _
  rw [triangle_weight_relabel]
  exact congrArg triangleWeights.get
    (orbitKey_coordinate trianglePerm triangleMul trianglePerm_mul triangleMul_surjective e s.1)

private theorem singleton_weight_invariant (s : LocalSym) (e : Fin 9 → Fin 4) :
    singletonWeight (singletonAct s e) = singletonWeight e := by
  change singletonWeight (outcome s.2 ∘ (e ∘ singletonPerm s.1)) = _
  rw [singleton_weight_relabel]
  exact congrArg singletonWeights.get
    (orbitKey_coordinate singletonPerm singletonMul singletonPerm_mul
      singletonMul_surjective e s.1)

abbrev TriangleAccepted : Prop :=
  ∀ j, checkRow triangleWeight trianglePartialAct triangleRows j = true

abbrev SingletonAccepted : Prop :=
  ∀ j, checkRow singletonWeight singletonPartialAct singletonRows j = true

def triangleLower (p : Partial (Fin 10) (Fin 4)) : ℤ :=
  checkedLookupLower trianglePartialAct triangleRows 41293 EJMPartialBoundLookup.triangleSelect p

def singletonLower (p : Partial (Fin 9) (Fin 4)) : ℤ :=
  checkedLookupLower singletonPartialAct singletonRows 8688 EJMPartialBoundLookup.singletonSelect p

private theorem triangle_lower_bound (accepted : TriangleAccepted)
    (p : Partial (Fin 10) (Fin 4)) (e : Event (Fin 10) (Fin 4)) (hp : Compatible p e) :
    triangleLower p ≤ triangleWeight e := by
  exact checked_lookup_lower_bound triangleWeight triangleAct trianglePartialAct
    triangle_compatible triangle_weight_invariant triangleRows accepted 41293
    EJMPartialBoundLookup.triangle_root_assignment EJMPartialBoundLookup.triangleSelect p e hp

private theorem singleton_lower_bound (accepted : SingletonAccepted)
    (p : Partial (Fin 9) (Fin 4)) (e : Event (Fin 9) (Fin 4)) (hp : Compatible p e) :
    singletonLower p ≤ singletonWeight e := by
  exact checked_lookup_lower_bound singletonWeight singletonAct singletonPartialAct
    singleton_compatible singleton_weight_invariant singletonRows accepted 8688
    EJMPartialBoundLookup.singleton_root_assignment EJMPartialBoundLookup.singletonSelect p e hp

def triangleScope (i : Fin 16) : Fin 10 → Fin 20 :=
  rankedCoordinate ∘ EJMInflationScore.lhsTriangle i

def singletonScope (i : Fin 16) : Fin 9 → Fin 20 :=
  rankedCoordinate ∘ EJMInflationScore.lhsSingleton i

def score (e : Event (Fin 20) (Fin 4)) : ℤ :=
  (∑ i : Fin 16, triangleWeight (e ∘ triangleScope i)) +
    ∑ i : Fin 16, singletonWeight (e ∘ singletonScope i)

def lower (p : Partial (Fin 20) (Fin 4)) : ℤ :=
  (∑ i : Fin 16, triangleLower (p ∘ triangleScope i)) +
    ∑ i : Fin 16, singletonLower (p ∘ singletonScope i)

private theorem lower_le_score (triangleAccepted : TriangleAccepted)
    (singletonAccepted : SingletonAccepted) (p : Partial (Fin 20) (Fin 4))
    (e : Event (Fin 20) (Fin 4)) (hp : Compatible p e) : lower p ≤ score e := by
  apply add_le_add
  · apply Finset.sum_le_sum
    intro i _
    exact triangle_lower_bound triangleAccepted _ _ (fun j a ha => hp (triangleScope i j) a ha)
  · apply Finset.sum_le_sum
    intro i _
    exact singleton_lower_bound singletonAccepted _ _
      (fun j a ha => hp (singletonScope i j) a ha)

def act (s : Fin 24) (e : Event (Fin 20) (Fin 4)) : Event (Fin 20) (Fin 4) :=
  outcome s ∘ e

private theorem score_invariant (s : Fin 24) (e : Event (Fin 20) (Fin 4)) :
    score (act s e) = score e := by
  simp only [score, act, Function.comp_assoc, triangle_weight_relabel, singleton_weight_relabel]

def dominates (s : Fin 24) (p : Partial (Fin 20) (Fin 4)) : Bool :=
  FiniteLex.dominates (Equiv.refl (Fin 20)) (outcomeEquiv s) p

private theorem dominates_rank_lt (s : Fin 24) (p : Partial (Fin 20) (Fin 4))
    (h : dominates s p = true) (e : Event (Fin 20) (Fin 4)) (hp : Compatible p e) :
    FiniteLex.rank (act s e) < FiniteLex.rank e := by
  exact FiniteLex.dominates_rank_lt (Equiv.refl (Fin 20)) (outcomeEquiv s) p h e hp

def globalAccepted : Prop :=
  D5.S0.Certificates.FiniteSymmetryDAGReplay.check nodes lower dominates 1024
    21 root (fun _ => none) = true

theorem accepted_residual_lower_bound (triangleAccepted : TriangleAccepted)
    (singletonAccepted : SingletonAccepted) (accepted : globalAccepted) :
    ∀ e : Event (Fin 20) (Fin 4), 1024 ≤ score e := by
  exact D5.S0.Certificates.FiniteSymmetryDAGReplay.checked_global_lower_bound
    score FiniteLex.rank act lower dominates 1024
    (lower_le_score triangleAccepted singletonAccepted) score_invariant dominates_rank_lt
    nodes 21 root accepted

#print axioms accepted_residual_lower_bound

end D5.S3.Quantum.Entanglement.EJM.EJMOriginalResidualReplay
