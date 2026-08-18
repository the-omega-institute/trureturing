/- GID: D5/S3/ResourceOrder/PaidInformationIncentiveConflict
   generality: G
   mirror-B: D5/B/S3/ResourceOrder/PaidInformationIncentiveConflict
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Costly information production conflicts with a fully revealing price. -/

import Mathlib.Data.Real.Basic

/- Library-search audit trail (2026-08-18):
   * Pinned Mathlib and Loogle returned the exact polymorphic order theorem
     `not_le_of_gt`; it is applied directly to positive information cost and
     the equilibrium incentive inequality below.
   * Repository searches for fully revealing prices, paid information,
     private-information production, and marginal trading benefit found no
     equal or stronger theorem. Adjacent pricing modules did not cover this
     incentive contradiction.
   * LeanSearch's query endpoint returned HTTP 404 and no usable declaration. -/

namespace D5.S3.ResourceOrder.PaidInformationIncentiveConflict

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- A fully revealing price cannot coexist with positive costly private
information production when price information comes from paid trades and
equilibrium production must cover its information cost. -/
theorem paid_information_full_revelation_conflict
    {MarketState Agent : Type*}
    (isEquilibrium : MarketState -> Prop)
    (positivePrivateInformationProduction : MarketState -> Prop)
    (priceFullyRevealsPrivateInformation : MarketState -> Prop)
    (paidInformationTrade : MarketState -> Agent -> Prop)
    (marginalGrossTradingBenefit : MarketState -> Agent -> ℝ)
    (informationCost : ℝ)
    (price_information_from_paid_trade :
      ∀ state,
        isEquilibrium state ->
          positivePrivateInformationProduction state ->
          priceFullyRevealsPrivateInformation state ->
          ∃ agent, paidInformationTrade state agent)
    (full_revelation_zero_marginal_benefit :
      ∀ state agent,
        isEquilibrium state ->
          priceFullyRevealsPrivateInformation state ->
          marginalGrossTradingBenefit state agent = 0)
    (positive_production_incentive :
      ∀ state agent,
        isEquilibrium state ->
          positivePrivateInformationProduction state ->
          paidInformationTrade state agent ->
          informationCost <= marginalGrossTradingBenefit state agent)
    (information_cost_pos : 0 < informationCost) :
    ¬ ∃ state,
      isEquilibrium state ∧
        positivePrivateInformationProduction state ∧
        priceFullyRevealsPrivateInformation state := by
  rintro ⟨state, hequilibrium, hproduction, hrevelation⟩
  obtain ⟨agent, hpaid⟩ := price_information_from_paid_trade state
    hequilibrium hproduction hrevelation
  have hincentive := positive_production_incentive state agent
    hequilibrium hproduction hpaid
  have hzero := full_revelation_zero_marginal_benefit state agent
    hequilibrium hrevelation
  rw [hzero] at hincentive
  exact (not_le_of_gt information_cost_pos) hincentive

#print axioms paid_information_full_revelation_conflict

end D5.S3.ResourceOrder.PaidInformationIncentiveConflict
