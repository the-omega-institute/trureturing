/- GID: D5/S3/ConceptDynamics/Causal/FiniteEventCouplingSharpBounds
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Causal/FiniteEventCouplingSharpBounds
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Two counterfactual events have explicit primal-dual sharp coupling bounds. -/

import D5.S3.ConceptDynamics.Causal.BenefitProbabilityBounds

/- Library-search audit trail (2026-09-03):
   * `BenefitProbabilityBounds` proves the Boolean Fréchet inequalities but does not
     construct a coupling attaining every point of the interval.
   * Repository searches found no reusable feasible-coupling predicate, endpoint
     witness, or replay theorem for an LP dual certificate in the causal family.
   * The proof uses only four-cell linear arithmetic. The certificate equalities expose
     the nonnegative slacks used by the corresponding two-event coupling LP. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Causal.FiniteEventCouplingSharpBounds

/-- The four-cell coupling with event marginals `leftMarginal` and
`rightMarginal`, and intersection mass `target`. -/
def eventCoupling
    (leftMarginal rightMarginal target : Real) :
    Bool × Bool -> Real
  | (false, false) => 1 - leftMarginal - rightMarginal + target
  | (false, true) => rightMarginal - target
  | (true, false) => leftMarginal - target
  | (true, true) => target

/-- A normalized nonnegative four-cell law with the displayed event marginals. -/
structure IsEventCoupling
    (mass : Bool × Bool -> Real)
    (leftMarginal rightMarginal : Real) : Prop where
  nonnegative : forall pair, 0 <= mass pair
  total :
    mass (false, false) + mass (false, true) +
        mass (true, false) + mass (true, true) = 1
  leftMarginalEq :
    mass (true, false) + mass (true, true) = leftMarginal
  rightMarginalEq :
    mass (false, true) + mass (true, true) = rightMarginal

/-- The mass on which the two counterfactual event indicators disagree. -/
def disagreementMass (mass : Bool × Bool -> Real) : Real :=
  mass (false, true) + mass (true, false)

/-- A replayable linear certificate for the lower, upper, and
dependence-constrained bounds of the two-event coupling LP. Each field is an
exact slack identity obtained from normalization and the two marginal rows. -/
structure EventCouplingDualCertificate
    (mass : Bool × Bool -> Real)
    (leftMarginal rightMarginal disagreementCap : Real) : Prop where
  frechetLowerSlack :
    mass (true, true) - (leftMarginal + rightMarginal - 1) =
      mass (false, false)
  leftUpperSlack :
    leftMarginal - mass (true, true) = mass (true, false)
  rightUpperSlack :
    rightMarginal - mass (true, true) = mass (false, true)
  disagreementLowerSlack :
    2 * mass (true, true) -
          (leftMarginal + rightMarginal - disagreementCap) =
      disagreementCap - disagreementMass mass

/-- The marginal and normalization rows produce the exact dual-slack
certificate, independently of nonnegativity or the chosen disagreement cap. -/
theorem event_coupling_dual_certificate
    (mass : Bool × Bool -> Real)
    (leftMarginal rightMarginal disagreementCap : Real)
    (feasible : IsEventCoupling mass leftMarginal rightMarginal) :
    EventCouplingDualCertificate
      mass leftMarginal rightMarginal disagreementCap := by
  refine
    { frechetLowerSlack := ?_
      leftUpperSlack := ?_
      rightUpperSlack := ?_
      disagreementLowerSlack := ?_ }
  · linarith [feasible.total, feasible.leftMarginalEq, feasible.rightMarginalEq]
  · linarith [feasible.leftMarginalEq]
  · linarith [feasible.rightMarginalEq]
  · dsimp [disagreementMass]
    linarith [feasible.leftMarginalEq, feasible.rightMarginalEq]

/-- Replaying only the certificate identities, cell nonnegativity, and the
additional disagreement inequality proves the tightened primal bounds. -/
theorem replay_event_coupling_dual_certificate
    (mass : Bool × Bool -> Real)
    (leftMarginal rightMarginal disagreementCap : Real)
    (mass_nonnegative : forall pair, 0 <= mass pair)
    (disagreement_cap : disagreementMass mass <= disagreementCap)
    (certificate :
      EventCouplingDualCertificate
        mass leftMarginal rightMarginal disagreementCap) :
    max
        (max 0 (leftMarginal + rightMarginal - 1))
        ((leftMarginal + rightMarginal - disagreementCap) / 2) <=
      mass (true, true) /\
      mass (true, true) <= min leftMarginal rightMarginal := by
  have target_nonnegative : 0 <= mass (true, true) :=
    mass_nonnegative (true, true)
  have frechet_lower :
      leftMarginal + rightMarginal - 1 <= mass (true, true) := by
    linarith [
      mass_nonnegative (false, false),
      certificate.frechetLowerSlack
    ]
  have disagreement_lower :
      (leftMarginal + rightMarginal - disagreementCap) / 2 <=
        mass (true, true) := by
    linarith [
      disagreement_cap,
      certificate.disagreementLowerSlack
    ]
  have left_upper : mass (true, true) <= leftMarginal := by
    linarith [
      mass_nonnegative (true, false),
      certificate.leftUpperSlack
    ]
  have right_upper : mass (true, true) <= rightMarginal := by
    linarith [
      mass_nonnegative (false, true),
      certificate.rightUpperSlack
    ]
  constructor
  · rw [max_le_iff, max_le_iff]
    exact ⟨⟨target_nonnegative, frechet_lower⟩, disagreement_lower⟩
  · rw [le_min_iff]
    exact ⟨left_upper, right_upper⟩

/-- Every feasible four-cell coupling obeys the usual two-event
Fréchet bounds. -/
theorem event_coupling_primal_bounds
    (mass : Bool × Bool -> Real)
    (leftMarginal rightMarginal : Real)
    (feasible : IsEventCoupling mass leftMarginal rightMarginal) :
    max 0 (leftMarginal + rightMarginal - 1) <= mass (true, true) /\
      mass (true, true) <= min leftMarginal rightMarginal := by
  have certificate :=
    event_coupling_dual_certificate
      mass leftMarginal rightMarginal (disagreementMass mass) feasible
  have replayed :=
    replay_event_coupling_dual_certificate
      mass leftMarginal rightMarginal (disagreementMass mass)
      feasible.nonnegative le_rfl certificate
  constructor
  · exact le_trans (le_max_left _ _) replayed.1
  · exact replayed.2

/-- The explicit four-cell law is feasible for every target in the
Fréchet interval. -/
theorem eventCoupling_isEventCoupling
    (leftMarginal rightMarginal target : Real)
    (lower :
      max 0 (leftMarginal + rightMarginal - 1) <= target)
    (upper : target <= min leftMarginal rightMarginal) :
    IsEventCoupling
      (eventCoupling leftMarginal rightMarginal target)
      leftMarginal rightMarginal := by
  have target_nonnegative : 0 <= target :=
    (le_max_left 0 (leftMarginal + rightMarginal - 1)).trans lower
  have sum_lower :
      leftMarginal + rightMarginal - 1 <= target :=
    (le_max_right 0 (leftMarginal + rightMarginal - 1)).trans lower
  have left_upper : target <= leftMarginal :=
    upper.trans (min_le_left leftMarginal rightMarginal)
  have right_upper : target <= rightMarginal :=
    upper.trans (min_le_right leftMarginal rightMarginal)
  refine
    { nonnegative := ?_
      total := ?_
      leftMarginalEq := ?_
      rightMarginalEq := ?_ }
  · intro pair
    rcases pair with ⟨left, right⟩
    cases left <;> cases right <;>
      simp [eventCoupling] <;> linarith
  · simp [eventCoupling]
    ring
  · simp [eventCoupling]
  · simp [eventCoupling]

/-- The projection of the feasible coupling polytope onto its intersection
coordinate is exactly the closed Fréchet interval. This is the sharpness
statement: necessity follows from a dual certificate and sufficiency from the
explicit primal coupling. -/
theorem event_coupling_target_feasible_iff
    (leftMarginal rightMarginal target : Real) :
    (max 0 (leftMarginal + rightMarginal - 1) <= target /\
        target <= min leftMarginal rightMarginal) <->
      exists mass : Bool × Bool -> Real,
        IsEventCoupling mass leftMarginal rightMarginal /\
          mass (true, true) = target := by
  constructor
  · intro bounds
    refine
      ⟨eventCoupling leftMarginal rightMarginal target,
        eventCoupling_isEventCoupling
          leftMarginal rightMarginal target bounds.1 bounds.2, ?_⟩
    simp [eventCoupling]
  · rintro ⟨mass, feasible, target_eq⟩
    have bounds :=
      event_coupling_primal_bounds mass leftMarginal rightMarginal feasible
    simpa [target_eq] using bounds

/-- Adding an upper bound on counterfactual disagreement adds one valid dual
lower plane while leaving the two Fréchet upper planes unchanged. -/
theorem event_coupling_bounds_with_disagreement_cap
    (mass : Bool × Bool -> Real)
    (leftMarginal rightMarginal disagreementCap : Real)
    (feasible : IsEventCoupling mass leftMarginal rightMarginal)
    (disagreement_cap : disagreementMass mass <= disagreementCap) :
    max
        (max 0 (leftMarginal + rightMarginal - 1))
        ((leftMarginal + rightMarginal - disagreementCap) / 2) <=
      mass (true, true) /\
      mass (true, true) <= min leftMarginal rightMarginal := by
  exact replay_event_coupling_dual_certificate
    mass leftMarginal rightMarginal disagreementCap feasible.nonnegative
    disagreement_cap
    (event_coupling_dual_certificate
      mass leftMarginal rightMarginal disagreementCap feasible)

/-- The disagreement-constrained interval is also exact. Every point in it is
attained by the explicit primal coupling, and the cap is certified by the new
lower-plane inequality. -/
theorem event_coupling_target_feasible_with_disagreement_cap_iff
    (leftMarginal rightMarginal disagreementCap target : Real) :
    (max
          (max 0 (leftMarginal + rightMarginal - 1))
          ((leftMarginal + rightMarginal - disagreementCap) / 2) <=
        target /\
        target <= min leftMarginal rightMarginal) <->
      exists mass : Bool × Bool -> Real,
        IsEventCoupling mass leftMarginal rightMarginal /\
          disagreementMass mass <= disagreementCap /\
          mass (true, true) = target := by
  constructor
  · intro bounds
    have frechet_lower :
        max 0 (leftMarginal + rightMarginal - 1) <= target :=
      (le_max_left
        (max 0 (leftMarginal + rightMarginal - 1))
        ((leftMarginal + rightMarginal - disagreementCap) / 2)).trans
        bounds.1
    have disagreement_lower :
        (leftMarginal + rightMarginal - disagreementCap) / 2 <=
          target :=
      (le_max_right
        (max 0 (leftMarginal + rightMarginal - 1))
        ((leftMarginal + rightMarginal - disagreementCap) / 2)).trans
        bounds.1
    refine
      ⟨eventCoupling leftMarginal rightMarginal target,
        eventCoupling_isEventCoupling
          leftMarginal rightMarginal target frechet_lower bounds.2, ?_, ?_⟩
    · simp [disagreementMass, eventCoupling]
      linarith
    · simp [eventCoupling]
  · rintro ⟨mass, feasible, disagreement_cap, target_eq⟩
    have bounds :=
      event_coupling_bounds_with_disagreement_cap
        mass leftMarginal rightMarginal disagreementCap
        feasible disagreement_cap
    simpa [target_eq] using bounds

#print axioms event_coupling_target_feasible_iff
#print axioms event_coupling_target_feasible_with_disagreement_cap_iff

end D5.S3.ConceptDynamics.Causal.FiniteEventCouplingSharpBounds
