/- GID: D5/S3/Quantum/Entanglement/EJM/EJMGlobalBoundReplay
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/EJMGlobalBoundReplay
   mirror-E: none(waiver:actual-global-inflation-bound-replay)
   anchors: [D5/S3/Quantum/Entanglement/EJM/EJMPartialBoundLookup, D5/S3/Quantum/Entanglement/EJM/EJMGlobalDAGData]
   utility: none
   digest: Actual local lookup bounds sum to a valid global score bound and earned context-specific replay acceptance excludes the original EJM local model. -/

import D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundLookup
import D5.S3.Quantum.Entanglement.EJM.EJMGlobalDAGData

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Entanglement.EJM.EJMGlobalBoundReplay
open D5.S0.Certificates.FiniteSymmetryBoundReplay
open D5.S0.Certificates.FinitePartialBoundDAG
open D5.S3.Quantum.Entanglement.ElegantJointMeasurementInflation (Node)
open D5.S3.Quantum.Entanglement.EJMInflationScore
open D5.S3.Quantum.Entanglement.EJM.EJMCertificateData (F1 F2)
open D5.S3.Quantum.Entanglement.EJM.EJMScoreSymmetry (triangleCentered singletonCentered)
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundData
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundTransport
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundLookup
open scoped BigOperators

/-!
Each of the literal 16 triangle and 16 singleton blocks projects the actual
current global partial assignment into its original local coordinate order.
Every lookup guards its proposed symmetry representative by full assignment
equality and otherwise uses the accepted all-unknown root. The resulting sum
is recomputed at every actual context of the shared global DAG.

All conclusions below are conditional: acceptance of every actual local row
and of the complete concrete global replay remain mandatory mathematical
obligations. No imported minimum or branch-shape sharing discharges them.
-/

abbrev TriangleAccepted : Prop :=
  ∀ j, checkRow (triangleCentered F1) trianglePartialAct triangleRows j = true

abbrev SingletonAccepted : Prop :=
  ∀ j, checkRow (singletonCentered F2) singletonPartialAct singletonRows j = true

/-- Project into the actual original marginal maps before using any local bound. -/
def lower (p : Partial Node (Fin 4)) : ℤ :=
  (∑ i : Fin 16, triangleLower (p ∘ lhsTriangle i)) +
    ∑ i : Fin 16, singletonLower (p ∘ lhsSingleton i)

theorem lower_le_score (triangleAccepted : TriangleAccepted)
    (singletonAccepted : SingletonAccepted)
    (p : Partial Node (Fin 4)) (e : Event Node (Fin 4)) (hp : Compatible p e) :
    lower p ≤ score F1 F2 e := by
  have ht : (∑ i : Fin 16, triangleLower (p ∘ lhsTriangle i)) ≤
      ∑ i : Fin 16, triangleBlock F1 i e := by
    apply Finset.sum_le_sum
    intro i _
    have hc : Compatible (p ∘ lhsTriangle i) (e ∘ lhsTriangle i) := by
      intro j a ha
      exact hp (lhsTriangle i j) a ha
    exact triangle_lower_bound triangleAccepted _ _ hc
  have hs : (∑ i : Fin 16, singletonLower (p ∘ lhsSingleton i)) ≤
      ∑ i : Fin 16, singletonBlock F2 i e := by
    apply Finset.sum_le_sum
    intro i _
    have hc : Compatible (p ∘ lhsSingleton i) (e ∘ lhsSingleton i) := by
      intro j a ha
      exact hp (lhsSingleton i j) a ha
    exact singleton_lower_bound singletonAccepted _ _ hc
  exact add_le_add ht hs

/-- The actual rounded cover requires a bound of one full positive scale unit. -/
def globalAccepted : Prop :=
  D5.S0.Certificates.FiniteSymmetryDAGReplay.check EJMGlobalDAGData.nodes lower
    EJMGlobalScoreSymmetry.dominates scale 21 EJMGlobalDAGData.root
    (fun _ => none) = true

theorem accepted_score_lower_bound (triangleAccepted : TriangleAccepted)
    (singletonAccepted : SingletonAccepted) (accepted : globalAccepted) :
    ∀ e : Event Node (Fin 4), scale ≤ score F1 F2 e := by
  exact D5.S0.Certificates.FiniteSymmetryDAGReplay.checked_global_lower_bound
    (score F1 F2) FiniteLex.rank EJMGlobalScoreSymmetry.act lower
    EJMGlobalScoreSymmetry.dominates scale
    (lower_le_score triangleAccepted singletonAccepted)
    EJMGlobalScoreSymmetry.actual_score_invariant EJMGlobalScoreSymmetry.dominates_rank_lt
    EJMGlobalDAGData.nodes 21 EJMGlobalDAGData.root accepted

theorem accepted_score_positive (triangleAccepted : TriangleAccepted)
    (singletonAccepted : SingletonAccepted) (accepted : globalAccepted) :
    ∀ e : Event Node (Fin 4), 1 ≤ score F1 F2 e := by
  intro e
  exact (by decide : (1 : ℤ) ≤ scale).trans
    (accepted_score_lower_bound triangleAccepted singletonAccepted accepted e)

theorem accepted_excludes_triangle_local (triangleAccepted : TriangleAccepted)
    (singletonAccepted : SingletonAccepted) (accepted : globalAccepted) :
    ¬ D5.S3.Quantum.Entanglement.TriangleSymmetricLocalRefutation.IsTriangleLocal
      ejmDistribution :=
  positive_score_excludes_triangle_local F1 F2
    (accepted_score_positive triangleAccepted singletonAccepted accepted)

#print axioms lower_le_score
#print axioms accepted_score_lower_bound
#print axioms accepted_score_positive
#print axioms accepted_excludes_triangle_local

end D5.S3.Quantum.Entanglement.EJM.EJMGlobalBoundReplay
