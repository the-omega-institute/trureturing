/- GID: D5/S3/ObserverMemory/TwoTimeKnowledge
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/TwoTimeKnowledge
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Characterize two-time forgetting by persistent events and observer-fiber constancy. -/

/- Library-search audit trail (2026-08-12):
   * Reused `Function.FactorsThrough` for constancy on observer readout fibers.
   * Checked `Function.factorsThrough_iff`, `Function.FactorsThrough.extend_comp`,
     `Function.not_injective_iff`, `Classical.not_forall`, and `Set.Icc`.
   * No existing declaration combines factorization failure with the required time interval and
     complete-ledger persistence. The quantifier conversion below normalizes the local definition;
     the substantive bridge computes an imported finite certificate as a concrete model. -/

import D5.S3.ObserverMemory.FiniteForgettingCertificate
import Mathlib.Logic.Function.Basic

namespace D5.S3.ObserverMemory.TwoTimeKnowledge

variable {Time World Event View Value : Type*}

/-- An event is known when its value is constant on every fiber of the observer readout. -/
def Knows (readout : Time → World → View) (value : Event → World → Value)
    (e : Event) (t : Time) : Prop :=
  (value e).FactorsThrough (readout t)

/-- The event remains in the complete ledger throughout the closed two-time interval. -/
def Persists [Preorder Time] (ledger : Time → Set Event) (e : Event) (t0 t1 : Time) : Prop :=
  ∀ t, t0 ≤ t → t ≤ t1 → e ∈ ledger t

/-- Semantic forgetting: strict time elapses while a persistent event ceases to be known. -/
def Forgot [Preorder Time] (readout : Time → World → View)
    (value : Event → World → Value) (ledger : Time → Set Event)
    (e : Event) (t0 t1 : Time) : Prop :=
  t0 < t1 ∧ Persists ledger e t0 t1 ∧
    Knows readout value e t0 ∧ ¬Knows readout value e t1

/-- Quantifier-normalized form of `Forgot`, exposing a counterexample on the later fiber. -/
theorem forgot_iff_later_fiber_counterexample [Preorder Time]
    (readout : Time → World → View) (value : Event → World → Value)
    (ledger : Time → Set Event) (e : Event) (t0 t1 : Time) :
    Forgot readout value ledger e t0 t1 ↔
      t0 < t1 ∧ Persists ledger e t0 t1 ∧
        (∀ ⦃x y : World⦄, readout t0 x = readout t0 y → value e x = value e y) ∧
        ∃ x y : World, readout t1 x = readout t1 y ∧ value e x ≠ value e y := by
  classical
  unfold Forgot Knows
  constructor
  · rintro ⟨hlt, hpersist, hearly, hlater⟩
    refine ⟨hlt, hpersist, hearly, ?_⟩
    simp only [Function.FactorsThrough] at hlater
    push Not at hlater
    exact hlater
  · rintro ⟨hlt, hpersist, hearly, ⟨x, y, hsame, hne⟩⟩
    refine ⟨hlt, hpersist, hearly, ?_⟩
    intro hlater
    exact hne (hlater hsame)

/-- Knowledge at a coarser later readout implies knowledge at the finer earlier readout. -/
theorem knows_of_later_readout_factors_through_earlier
    (readout : Time → World → View) (value : Event → World → Value)
    {e : Event} {t0 t1 : Time}
    (hreadout : (readout t1).FactorsThrough (readout t0))
    (hknow : Knows readout value e t1) :
    Knows readout value e t0 :=
  fun _ _ hsame => hknow (hreadout hsame)

open D5.S3.ObserverMemory.FiniteForgettingCertificate

/-- The two concrete times are interpreted by the frozen Remember and Forgotten certificates. -/
def certificateStateAt (t : Bool) : CertificateState Unit :=
  match t with
  | false => initialRemember
  | true => forgottenAfterRemember

/-- Remember distinguishes Boolean worlds; the resulting Forgotten certificate does not. -/
def certificateReadout (t world : Bool) : Bool :=
  match (certificateStateAt t).cognition with
  | .remember => world
  | _ => false

/-- The sole witness event takes the Boolean world itself as its value. -/
def boolEventValue (_ : Unit) (world : Bool) : Bool :=
  world

/-- The witness event is present in the complete ledger at both Boolean times. -/
def boolLedger (_ : Bool) : Set Unit :=
  Set.univ

/--
Model-satisfies-semantics bridge: the frozen finite certificate computes a genuine Forget
transition from its concrete Remember state to its concrete Forgotten state. Under the displayed
readout interpretation, that same pair of times satisfies `Forgot`, and the target retains the
certificate's forgetting audit mark.
-/
theorem finite_certificate_instantiates_forgot :
    Transition (certificateStateAt false) (certificateStateAt true) ∧
      Forgot certificateReadout boolEventValue boolLedger () false true ∧
      ForgottenLogged (certificateStateAt true) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [certificateStateAt, initialRemember, forgottenAfterRemember, closeClaims] using
      (remember_forgets (Reason := Unit) ({} : Ledger Unit))
  · refine ⟨by decide, ?_, ?_, ?_⟩
    · intro t _ _
      exact Set.mem_univ ()
    · intro x y hsame
      simpa [certificateReadout, certificateStateAt, initialRemember, boolEventValue] using hsame
    · intro hknow
      have hsame : certificateReadout true false = certificateReadout true true := rfl
      have hvalue : boolEventValue () false = boolEventValue () true := hknow hsame
      exact Bool.false_ne_true hvalue
  · rfl

end D5.S3.ObserverMemory.TwoTimeKnowledge
