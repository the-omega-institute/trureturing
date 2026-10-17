/- GID: D5/S3/Quantum/Entanglement/EJM/EJMPartialBoundTransport
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/EJMPartialBoundTransport
   mirror-E: none(waiver:exact-local-partial-state-transport)
   anchors: []
   utility: none
   digest: Actual local symmetries transport partial events and preserve centered EJM scores. -/

import D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundData
import D5.S3.Quantum.Entanglement.EJM.EJMScoreSymmetry

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundTransport
open D5.S0.Certificates.FiniteSymmetryBoundReplay
open D5.S3.Quantum.Entanglement.EJM.EJMCertificateData (F1 F2 trianglePerm singletonPerm)
open D5.S3.Quantum.Entanglement.EJM.EJMScoreSymmetry

open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundData (outcome LocalSym)

private theorem outcome_bijective (s : Fin 24) : Function.Bijective (outcome s) := by
  have h : ∀ s : Fin 24, Function.Bijective (outcome s) := by decide
  exact h s

noncomputable def outcomeEquiv (s : Fin 24) : Fin 4 ≃ Fin 4 :=
  Equiv.ofBijective (outcome s) (outcome_bijective s)

def eventAct {Coord : Type*} (coordinate : Coord → Coord) (outcome : Fin 4 → Fin 4)
    (e : Event Coord (Fin 4)) : Event Coord (Fin 4) := outcome ∘ e ∘ coordinate

def partialAct {Coord : Type*} (coordinate : Coord → Coord) (outcome : Fin 4 → Fin 4)
    (p : Partial Coord (Fin 4)) : Partial Coord (Fin 4) :=
  fun i => (p (coordinate i)).map outcome

/-- This is exact transport of the actual partial assignment, including unknown coordinates. -/
theorem compatible_act {Coord : Type*} (coordinate : Coord → Coord)
    (outcome : Fin 4 → Fin 4) (p : Partial Coord (Fin 4)) (e : Event Coord (Fin 4))
    (hp : Compatible p e) : Compatible (partialAct coordinate outcome p)
      (eventAct coordinate outcome e) := by
  intro i a ha
  change (p (coordinate i)).map outcome = some a at ha
  cases h : p (coordinate i) with
  | none => simp only [h, Option.map_none, reduceCtorEq] at ha
  | some b =>
    have hb : e (coordinate i) = b := hp _ _ h
    simp only [h, Option.map_some, Option.some.injEq] at ha
    change outcome (e (coordinate i)) = a
    rw [hb]
    exact ha

def triangleAct (s : LocalSym) := eventAct (trianglePerm s.1) (outcome s.2)
def trianglePartialAct (s : LocalSym) := partialAct (trianglePerm s.1) (outcome s.2)
def singletonAct (s : LocalSym) := eventAct (singletonPerm s.1) (outcome s.2)
def singletonPartialAct (s : LocalSym) := partialAct (singletonPerm s.1) (outcome s.2)

theorem triangle_compatible (s : LocalSym) (p : Partial (Fin 10) (Fin 4))
    (e : Event (Fin 10) (Fin 4)) (hp : Compatible p e) :
    Compatible (trianglePartialAct s p) (triangleAct s e) :=
  compatible_act _ _ p e hp

theorem singleton_compatible (s : LocalSym) (p : Partial (Fin 9) (Fin 4))
    (e : Event (Fin 9) (Fin 4)) (hp : Compatible p e) :
    Compatible (singletonPartialAct s p) (singletonAct s e) :=
  compatible_act _ _ p e hp

theorem triangle_score_invariant (s : LocalSym) (e : Fin 10 → Fin 4) :
    triangleCentered F1 (triangleAct s e) = triangleCentered F1 e := by
  change triangleCentered F1 ((outcomeEquiv s.2) ∘ (e ∘ trianglePerm s.1)) = _
  rw [actual_triangleCentered_relabel, actual_triangleCentered_coordinate]

theorem singleton_score_invariant (s : LocalSym) (e : Fin 9 → Fin 4) :
    singletonCentered F2 (singletonAct s e) = singletonCentered F2 e := by
  change singletonCentered F2 ((outcomeEquiv s.2) ∘ (e ∘ singletonPerm s.1)) = _
  rw [actual_singletonCentered_relabel, actual_singletonCentered_coordinate]

#print axioms compatible_act
#print axioms triangle_score_invariant
#print axioms singleton_score_invariant

end D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundTransport
