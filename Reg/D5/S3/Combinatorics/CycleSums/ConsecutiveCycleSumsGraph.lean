import D5.S3.Combinatorics.CycleSums.ConsecutiveCycleSumsGraph
import Reg.Support.DependentFamily

noncomputable section
namespace Reg.D5.S3.Combinatorics.CycleSums.ConsecutiveCycleSumsGraph
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

/-- The varying operand is the graph in the induced-connectivity conclusion. -/
abbrev PredecessorSig : Signature where
  Params := ℕ
  State n := SimpleGraph (Fin n)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ n := SimpleGraph (Fin n)
  Anchor := Empty
  finiteAnchor := inferInstance

def predecessorActual : Realization PredecessorSig :=
  realize PredecessorSig (fun _ _ G => G) (fun e => nomatch e)
def predecessorBad : Realization PredecessorSig :=
  realize PredecessorSig (fun _ _ _ => ⊥) (fun e => nomatch e)
def predecessorArena : Arena where
  signature := PredecessorSig
  Law a := ∀ {n : ℕ} {G : SimpleGraph (Fin n)} {C : Finset (Fin n)}
    (r : Fin n), r ∈ C →
    (∀ v ∈ C, v ≠ r → ∃ u ∈ C, u.val < v.val ∧ G.Adj u v) →
    ((a.readout () n G).induce (C : Set (Fin n))).Connected

theorem predecessorBridge :
    (∀ {n : ℕ} {G : SimpleGraph (Fin n)} {C : Finset (Fin n)}
      (r : Fin n), r ∈ C →
      (∀ v ∈ C, v ≠ r → ∃ u ∈ C, u.val < v.val ∧ G.Adj u v) →
      (G.induce (C : Set (Fin n))).Connected) ↔
    predecessorArena.Law predecessorActual := Iff.rfl

theorem predecessorBadLaw : ¬ predecessorArena.Law predecessorBad := by
  intro h
  have hp : ∀ v ∈ (Finset.univ : Finset (Fin 2)), v ≠ 0 →
      ∃ u ∈ (Finset.univ : Finset (Fin 2)),
        u.val < v.val ∧ (⊤ : SimpleGraph (Fin 2)).Adj u v := by decide
  have hc := h (G := (⊤ : SimpleGraph (Fin 2)))
    (C := (Finset.univ : Finset (Fin 2))) (0 : Fin 2) (Finset.mem_univ _) hp
  change ((⊥ : SimpleGraph (Fin 2)).induce
    ((Finset.univ : Finset (Fin 2)) : Set (Fin 2))).Connected at hc
  have hbot : (⊥ : SimpleGraph (Fin 2)).Connected :=
    (SimpleGraph.induceUnivIso (⊥ : SimpleGraph (Fin 2))).connected_iff.mp
      (Eq.mp (congrArg (fun C : Set (Fin 2) =>
        ((⊥ : SimpleGraph (Fin 2)).induce C).Connected) Finset.coe_univ) hc)
  exact SimpleGraph.not_connected_bot hbot

theorem predecessorDependence : ObservationalDependence PredecessorSig predecessorActual := by
  intro i
  refine ⟨2, ⊥, ⊤, ?_⟩
  change (⊥ : SimpleGraph (Fin 2)) ≠ ⊤
  intro h
  have ha : (⊤ : SimpleGraph (Fin 2)).Adj 0 1 := by decide
  rw [← h] at ha
  exact ha

def predecessorRegistration : Registration predecessorArena
    (∀ {n : ℕ} {G : SimpleGraph (Fin n)} {C : Finset (Fin n)}
      (r : Fin n), r ∈ C →
      (∀ v ∈ C, v ≠ r → ∃ u ∈ C, u.val < v.val ∧ G.Adj u v) →
      (G.induce (C : Set (Fin n))).Connected) where
  actual := predecessorActual
  bridge := predecessorBridge
  variation := ⟨by
    intro n G C r hr hp
    exact _root_.D5.S3.Combinatorics.CycleSums.ConsecutiveCycleSumsGraph.connected_of_predecessor
      r hr hp, predecessorBad, predecessorBadLaw⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨predecessorBad, ?_, rfl, predecessorBadLaw⟩
      intro j h
      cases i
      cases j
      exact (h rfl).elim
    · intro i
      exact nomatch i
  dependence := predecessorDependence

end Reg.D5.S3.Combinatorics.CycleSums.ConsecutiveCycleSumsGraph
