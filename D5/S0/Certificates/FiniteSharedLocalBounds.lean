/- GID: D5/S0/Certificates/FiniteSharedLocalBounds
   generality: G
   mirror-B: D5/B/S0/Certificates/FiniteSharedLocalBounds
   mirror-E: none(waiver:finite-cached-certificate-replay)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Quantum/Entanglement/EJM/EJMSharedLocalReadouts.checked_bound; instance=D5/S3/Quantum/Entanglement/EJM/EJMSharedLocalReadoutsPilot.triangle_accepted
   digest: Shared checked local readouts bound every separately checked actual projection without duplicating transition rows. -/

import D5.S0.Certificates.FiniteLocalRowCache

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Certificates.FiniteSharedLocalBounds
open D5.S0.Certificates.FiniteSymmetryBoundReplay
open D5.S0.Certificates.FinitePartialBoundDAG (Row checkRow)
open D5.S0.Certificates.FiniteLocalRowCache (State Associated)
open scoped BigOperators

variable {Coord Value Sym Global : Type*}
  [Fintype Coord] [Fintype Value] [DecidableEq Coord] [DecidableEq Value]
  {N M K : ℕ}

/-- A readout names the original row and action. Its transported partial and
lower value are proposals, checked against the original local certificate. -/
structure Readout (N : ℕ) (Coord Value Sym : Type*) where
  state : State N Sym
  assignment : Partial Coord Value
  lower : ℤ

def checkReadout
    (assignment : Fin N → Partial Coord Value) (lower : Fin N → ℤ)
    (partialAct : Sym → Partial Coord Value → Partial Coord Value)
    (readout : Readout N Coord Value Sym) : Bool :=
  decide (assignment readout.state.1 = partialAct readout.state.2 readout.assignment ∧
    lower readout.state.1 = readout.lower)

/-- The lookup tables are independently tied to every original row. The
actual row/action association, rather than a key or hash, supplies the bound. -/
theorem checked_readout_lower
    (score : Event Coord Value → ℤ)
    (act : Sym → Event Coord Value → Event Coord Value)
    (partialAct : Sym → Partial Coord Value → Partial Coord Value)
    (hact : ∀ s p e, Compatible p e → Compatible (partialAct s p) (act s e))
    (hscore : ∀ s e, score (act s e) = score e)
    (rows : Fin N → Row N Coord Value Sym)
    (rowsAccepted : ∀ j, checkRow score partialAct rows j = true)
    (assignment : Fin N → Partial Coord Value) (lower : Fin N → ℤ)
    (assignmentExact : ∀ j, assignment j = (rows j).assignment)
    (lowerExact : ∀ j, lower j = (rows j).lower)
    (readout : Readout N Coord Value Sym)
    (accepted : checkReadout assignment lower partialAct readout = true)
    (e : Event Coord Value) (hp : Compatible readout.assignment e) :
    readout.lower ≤ score e := by
  obtain ⟨associated, readoutLower⟩ := of_decide_eq_true accepted
  have originalAssociation : Associated partialAct rows readout.state readout.assignment := by
    change (rows readout.state.1).assignment = partialAct readout.state.2 readout.assignment
    rw [← assignmentExact]
    exact associated
  rw [← readoutLower, lowerExact]
  exact D5.S0.Certificates.FiniteLocalRowCache.associated_lower_bound
    score act partialAct hact hscore rows rowsAccepted readout.state
    readout.assignment e originalAssociation hp

/-- Every use checks its own actual projection, even when many uses share a
single local readout. No distinct global contexts are identified by a key. -/
def checkSelection
    (readouts : Fin M → Readout N Coord Value Sym) (select : Fin K → Fin M)
    (projection : Fin K → Coord → Global) (p : Partial Global Value) : Bool :=
  decide (∀ k, (readouts (select k)).assignment = p ∘ projection k)

theorem checked_selection_sum_lower
    (score : Event Coord Value → ℤ)
    (act : Sym → Event Coord Value → Event Coord Value)
    (partialAct : Sym → Partial Coord Value → Partial Coord Value)
    (hact : ∀ s p e, Compatible p e → Compatible (partialAct s p) (act s e))
    (hscore : ∀ s e, score (act s e) = score e)
    (rows : Fin N → Row N Coord Value Sym)
    (rowsAccepted : ∀ j, checkRow score partialAct rows j = true)
    (assignment : Fin N → Partial Coord Value) (lower : Fin N → ℤ)
    (assignmentExact : ∀ j, assignment j = (rows j).assignment)
    (lowerExact : ∀ j, lower j = (rows j).lower)
    (readouts : Fin M → Readout N Coord Value Sym)
    (readoutsAccepted : ∀ j, checkReadout assignment lower partialAct (readouts j) = true)
    (select : Fin K → Fin M) (projection : Fin K → Coord → Global)
    (p : Partial Global Value)
    (selectionAccepted : checkSelection readouts select projection p = true)
    (e : Event Global Value) (hp : Compatible p e) :
    (∑ k, (readouts (select k)).lower) ≤ ∑ k, score (e ∘ projection k) := by
  have projections := of_decide_eq_true selectionAccepted
  apply Finset.sum_le_sum
  intro k _
  apply checked_readout_lower score act partialAct hact hscore rows rowsAccepted
    assignment lower assignmentExact lowerExact (readouts (select k))
    (readoutsAccepted (select k)) (e ∘ projection k)
  rw [projections k]
  intro i a ha
  exact hp (projection k i) a ha

#print axioms checked_readout_lower
#print axioms checked_selection_sum_lower
end D5.S0.Certificates.FiniteSharedLocalBounds
