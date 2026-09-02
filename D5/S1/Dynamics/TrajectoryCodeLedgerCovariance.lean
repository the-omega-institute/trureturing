/- GID: D5/S1/Dynamics/TrajectoryCodeLedgerCovariance
   generality: I
   mirror-B: D5/B/S1/Dynamics/TrajectoryCodeLedgerCovariance
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Legal normalized trajectories have unique codes and code-ledger identity. -/

import D5.S1.Dynamics.CodeLedgerIdentity
import D5.S1.Digit.PrimeAxis.PrimeAxisNormalizationUnique

namespace D5.S1.Dynamics.TrajectoryCodeLedgerCovariance

open D5.S1.Digit
open D5.S1.Digit.PrimeAxis.PrimeAxisNormalizationUnique
open D5.S1.Dynamics.CodeLedgerIdentity

/-- A trajectory advanced by canonical prime-axis generation has a unique normalized
coordinate at every step. When adjacent states preserve the rule component, that
component is constant throughout the orbit, so state identity reduces to equality of
the canonical coordinate code and the remaining ledger state. -/
theorem legal_trajectory_code_ledger_covariance
    {Rules Ledger : Type*}
    (events : ℕ → PrimeAxisTable)
    (trajectory : ℕ → CodeLedgerState (Rules × Ledger))
    (coordinate_step : ∀ t,
      (trajectory (t + 1)).coordinate =
        normalizedPrimeAxisAdd (trajectory t).coordinate (events t))
    (rule_step : ∀ t,
      (trajectory (t + 1)).ledger.1 = (trajectory t).ledger.1) :
    (∀ t,
      ((∀ p,
          CanonicalRaw ((trajectory (t + 1)).coordinate.digits p) ∧
            rawValue ((trajectory (t + 1)).coordinate.digits p) =
              rawValue ((trajectory t).coordinate.digits p) +
                rawValue ((events t).digits p)) ∧
        decodePrimeAxisTable (trajectory (t + 1)).coordinate =
          decodePrimeAxisTable (trajectory t).coordinate *
            decodePrimeAxisTable (events t))) ∧
    (∀ t left right,
      ((∀ p,
          CanonicalRaw (left.digits p) ∧
            rawValue (left.digits p) =
              rawValue ((trajectory t).coordinate.digits p) +
                rawValue ((events t).digits p)) ∧
        decodePrimeAxisTable left =
          decodePrimeAxisTable (trajectory t).coordinate *
            decodePrimeAxisTable (events t)) →
      ((∀ p,
          CanonicalRaw (right.digits p) ∧
            rawValue (right.digits p) =
              rawValue ((trajectory t).coordinate.digits p) +
                rawValue ((events t).digits p)) ∧
        decodePrimeAxisTable right =
          decodePrimeAxisTable (trajectory t).coordinate *
            decodePrimeAxisTable (events t)) →
      left = right) ∧
    (∀ i j, (trajectory i).ledger.1 = (trajectory j).ledger.1) ∧
    (∀ i j,
      trajectory i = trajectory j ↔
        canonicalCode (trajectory i) = canonicalCode (trajectory j) ∧
          (trajectory i).ledger.2 = (trajectory j).ledger.2) ∧
    (∀ i j,
      canonicalCode (trajectory i) ≠ canonicalCode (trajectory j) →
        trajectory i ≠ trajectory j) ∧
    ∀ i j,
      trajectory i = trajectory j →
        canonicalCode (trajectory i) = canonicalCode (trajectory j) := by
  have rule_eq_initial : ∀ n,
      (trajectory n).ledger.1 = (trajectory 0).ledger.1 := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
        exact (rule_step n).trans ih
  have rule_constant : ∀ i j,
      (trajectory i).ledger.1 = (trajectory j).ledger.1 := by
    intro i j
    exact (rule_eq_initial i).trans (rule_eq_initial j).symm
  have step_legal : ∀ t,
      ((∀ p,
          CanonicalRaw ((trajectory (t + 1)).coordinate.digits p) ∧
            rawValue ((trajectory (t + 1)).coordinate.digits p) =
              rawValue ((trajectory t).coordinate.digits p) +
                rawValue ((events t).digits p)) ∧
        decodePrimeAxisTable (trajectory (t + 1)).coordinate =
          decodePrimeAxisTable (trajectory t).coordinate *
            decodePrimeAxisTable (events t)) := by
    intro t
    rw [coordinate_step t]
    constructor
    · intro p
      constructor
      · exact (normalizedPrimeAxisAdd (trajectory t).coordinate (events t)).canonical p
      · change rawValue
          (normalize (((trajectory t).coordinate.digits + (events t).digits) p)) = _
        rw [rawValue_normalize]
        simpa using rawValue_add
          ((trajectory t).coordinate.digits p) ((events t).digits p)
    · exact (prime_axis_addition_spec (trajectory t).coordinate (events t)).2
  have step_unique : ∀ t left right,
      ((∀ p,
          CanonicalRaw (left.digits p) ∧
            rawValue (left.digits p) =
              rawValue ((trajectory t).coordinate.digits p) +
                rawValue ((events t).digits p)) ∧
        decodePrimeAxisTable left =
          decodePrimeAxisTable (trajectory t).coordinate *
            decodePrimeAxisTable (events t)) →
      ((∀ p,
          CanonicalRaw (right.digits p) ∧
            rawValue (right.digits p) =
              rawValue ((trajectory t).coordinate.digits p) +
                rawValue ((events t).digits p)) ∧
        decodePrimeAxisTable right =
          decodePrimeAxisTable (trajectory t).coordinate *
            decodePrimeAxisTable (events t)) →
      left = right := by
    intro t left right hleft hright
    obtain ⟨result, _, unique⟩ :=
      normalized_prime_axis_add_unique (trajectory t).coordinate (events t)
    exact (unique left hleft).trans (unique right hright).symm
  have identity_criterion : ∀ i j,
      trajectory i = trajectory j ↔
        canonicalCode (trajectory i) = canonicalCode (trajectory j) ∧
          (trajectory i).ledger.2 = (trajectory j).ledger.2 := by
    intro i j
    constructor
    · intro hstate
      exact ⟨congrArg canonicalCode hstate,
        congrArg (fun state => state.ledger.2) hstate⟩
    · rintro ⟨hcode, hledger⟩
      apply (same_state_iff_same_code_and_ledger (trajectory i) (trajectory j)).2
      exact ⟨hcode, Prod.ext (rule_constant i j) hledger⟩
  refine ⟨step_legal, step_unique, rule_constant, identity_criterion, ?_, ?_⟩
  · intro i j hcode hstate
    exact hcode ((identity_criterion i j).1 hstate).1
  · intro i j hstate
    exact ((identity_criterion i j).1 hstate).1

end D5.S1.Dynamics.TrajectoryCodeLedgerCovariance
