/- GID: D5/S0/Computability/FiniteCounterexampleCertificate
   generality: G
   mirror-B: D5/B/S0/Computability/FiniteCounterexampleCertificate
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A false universal finite readout has exactly a bounded counterexample certificate. -/

import D5.S0.History.MarkerHistorySearch
import Mathlib.Data.Bool.Basic

namespace D5.S0.Computability.FiniteCounterexampleCertificate

open D5.S0.History

/- Provenance: pinned mathlib supplies the classical quantifier bridge
   (`not_forall`) and Boolean rejection bridge
   (`Bool.eq_false_of_not_eq_true`). The executable bounded certificate uses
   the repository-local sound and complete marker-history search. -/

/-- Failure of a universal finite readout is equivalent to a sound bounded
search certificate. -/
theorem finite_readout_counterexample_certificate
    (D : MarkerHistory -> Bool) :
    (¬ ∀ h, D h = true) ↔
      ∃ n h, findCounterexample D n = some h ∧ D h = false := by
  constructor
  · intro hnot
    obtain ⟨h, rejected⟩ := not_forall.mp hnot
    have rejected' : D h = false := Bool.eq_false_of_not_eq_true rejected
    obtain ⟨w, found⟩ :=
      findCounterexample_complete (D := D) (n := h.length)
        ⟨h, Nat.le_refl h.length, rejected'⟩
    exact ⟨h.length, w, found, findCounterexample_sound found⟩
  · rintro ⟨_n, h, _found, rejected⟩ hall
    have accepted := hall h
    rw [rejected] at accepted
    cases accepted

end D5.S0.Computability.FiniteCounterexampleCertificate
