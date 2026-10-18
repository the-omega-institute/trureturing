/- GID: D5/S0/Certificates/FiniteLocalRowCache
   generality: G
   mirror-B: D5/B/S0/Certificates/FiniteLocalRowCache
   mirror-E: none(waiver:finite-cached-certificate-replay)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Quantum/Entanglement/EJM/EJMCacheSoundness.step_associated; instance=D5/S3/Quantum/Entanglement/EJM/EJMTriangleCacheReceipts.transition_accepted
   digest: Checked finite local transitions retain their actual-context association under exact coordinate, outcome and composition laws. -/

/- The concrete instance checks every local mirror and unknown-coordinate
transition. EJMCacheSoundness uses the earned exact updates and lower bounds
for the original thirty-two inflation-score projections. No global search
acceptance or nonlocality conclusion is asserted by this local checker. -/

import D5.S0.Certificates.FinitePartialBoundDAG

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Certificates.FiniteLocalRowCache
open D5.S0.Certificates.FiniteSymmetryBoundReplay
open D5.S0.Certificates.FinitePartialBoundDAG

variable {Coord Value Sym : Type*} [Fintype Coord] [Fintype Value]
  [DecidableEq Coord] [DecidableEq Value] {N : ℕ}

abbrev State (N : ℕ) (Sym : Type*) := Fin N × Sym

def Associated
    (partialAct : Sym → Partial Coord Value → Partial Coord Value)
    (rows : Fin N → Row N Coord Value Sym)
    (state : State N Sym) (p : Partial Coord Value) : Prop :=
  (rows state.1).assignment = partialAct state.2 p

def checkTransition
    (partialAct : Sym → Partial Coord Value → Partial Coord Value)
    (rows : Fin N → Row N Coord Value Sym)
    (transition : Fin N → Coord → Value → State N Sym)
    (j : Fin N) (i : Coord) (a : Value) : Bool :=
  let next := transition j i a
  decide ((rows next.1).assignment =
    partialAct next.2 (Function.update (rows j).assignment i (some a)))

/-- Actual update is transported into the current row coordinates before
querying a transition; the newly earned action is composed with the old one. -/
def step
    (transition : Fin N → Coord → Value → State N Sym)
    (coordinatePreimage : Sym → Coord → Coord)
    (outcome : Sym → Value → Value) (compose : Sym → Sym → Sym)
    (state : State N Sym) (i : Coord) (a : Value) : State N Sym :=
  let next := transition state.1 (coordinatePreimage state.2 i) (outcome state.2 a)
  (next.1, compose next.2 state.2)

/-- The exact assignment of each transition is checked once. Its use at a
new global context is justified by the old association and action laws. -/
theorem checked_step_associated
    (partialAct : Sym → Partial Coord Value → Partial Coord Value)
    (rows : Fin N → Row N Coord Value Sym)
    (transition : Fin N → Coord → Value → State N Sym)
    (coordinatePreimage : Sym → Coord → Coord)
    (outcome : Sym → Value → Value) (compose : Sym → Sym → Sym)
    (updateLaw : ∀ s p i a,
      partialAct s (Function.update p i (some a)) =
        Function.update (partialAct s p) (coordinatePreimage s i) (some (outcome s a)))
    (compositionLaw : ∀ t s p,
      partialAct t (partialAct s p) = partialAct (compose t s) p)
    (state : State N Sym) (p : Partial Coord Value)
    (associated : Associated partialAct rows state p) (i : Coord) (a : Value)
    (accepted : checkTransition partialAct rows transition state.1
      (coordinatePreimage state.2 i) (outcome state.2 a) = true) :
    Associated partialAct rows
      (step transition coordinatePreimage outcome compose state i a)
      (Function.update p i (some a)) := by
  let next := transition state.1 (coordinatePreimage state.2 i) (outcome state.2 a)
  have exactTransition : (rows next.1).assignment =
      partialAct next.2 (Function.update (rows state.1).assignment
        (coordinatePreimage state.2 i) (some (outcome state.2 a))) :=
    of_decide_eq_true accepted
  change (rows next.1).assignment =
    partialAct (compose next.2 state.2) (Function.update p i (some a))
  change (rows state.1).assignment = partialAct state.2 p at associated
  rw [exactTransition, associated, ← updateLaw, compositionLaw]

/-- A cached row bounds the actual original event, because its full partial
assignment is related to that actual event by the earned symmetry action. -/
theorem associated_lower_bound
    (score : Event Coord Value → ℤ)
    (act : Sym → Event Coord Value → Event Coord Value)
    (partialAct : Sym → Partial Coord Value → Partial Coord Value)
    (hact : ∀ s p e, Compatible p e → Compatible (partialAct s p) (act s e))
    (hscore : ∀ s e, score (act s e) = score e)
    (rows : Fin N → Row N Coord Value Sym)
    (accepted : ∀ j, checkRow score partialAct rows j = true)
    (state : State N Sym) (p : Partial Coord Value) (e : Event Coord Value)
    (associated : Associated partialAct rows state p) (hp : Compatible p e) :
    (rows state.1).lower ≤ score e := by
  have compatible : Compatible (rows state.1).assignment (act state.2 e) := by
    change (rows state.1).assignment = partialAct state.2 p at associated
    rw [associated]
    exact hact state.2 p e hp
  have bound := checked_rows_lower_bound score act partialAct hact hscore
    rows accepted state.1 (act state.2 e) compatible
  simpa only [hscore] using bound

#print axioms checked_step_associated
#print axioms associated_lower_bound

end D5.S0.Certificates.FiniteLocalRowCache
