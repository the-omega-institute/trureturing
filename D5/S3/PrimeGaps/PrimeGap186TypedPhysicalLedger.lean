/- GID: D5/S3/PrimeGaps/PrimeGap186TypedPhysicalLedger
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Assemble the exact typed 152-cell PrimeGaps186 numerical certificate from independently dischargeable propositions. -/

import D5.S3.PrimeGaps.PrimeGap186PhysicalCertificateLedger
import D5.S3.PrimeGaps.PrimeGap186ExactCertificateIndex

namespace D5.S3.PrimeGaps.PrimeGap186TypedPhysicalLedger

open D5.S3.PrimeGaps.PrimeGap186PhysicalCertificateLedger
open D5.S3.PrimeGaps.PrimeGap186ExactCertificateIndex

/-- Assemble a typed ledger directly on the exact physical-bound address space. -/
def typedPhysicalLedger
    (outer : OuterBoundAddress → Prop)
    (inner : InnerRowAddress → Prop)
    (scalar : ScalarBoundAddress → Prop) :
    FiniteProofLedger PhysicalBoundAddress where
  obligation
    | .outer a => outer a
    | .inner a => inner a
    | .scalar a => scalar a

/-- Completeness is exactly the conjunction of all typed outer, inner, and scalar cells. -/
theorem typedPhysicalLedger_complete_iff
    (outer : OuterBoundAddress → Prop)
    (inner : InnerRowAddress → Prop)
    (scalar : ScalarBoundAddress → Prop) :
    (typedPhysicalLedger outer inner scalar).Complete ↔
      (∀ a, outer a) ∧ (∀ a, inner a) ∧ (∀ a, scalar a) := by
  constructor
  · intro h
    exact ⟨fun a => h (.outer a), fun a => h (.inner a), fun a => h (.scalar a)⟩
  · rintro ⟨ho, hi, hs⟩ a
    cases a with
    | outer a => exact ho a
    | inner a => exact hi a
    | scalar a => exact hs a

/-- Outer completeness can be split into the two source-row tables and the two component kinds. -/
theorem outer_complete_iff
    (outer : OuterBoundAddress → Prop) :
    (∀ a, outer a) ↔
      (∀ j : Fin 17, outer ⟨.orderTwo j, .root⟩ ∧ outer ⟨.orderTwo j, .face⟩) ∧
      (∀ j : Fin 35, outer ⟨.orderFiveHalves j, .root⟩ ∧
        outer ⟨.orderFiveHalves j, .face⟩) := by
  constructor
  · intro h
    exact ⟨fun j => ⟨h _, h _⟩, fun j => ⟨h _, h _⟩⟩
  · rintro ⟨h2, h25⟩ a
    rcases a with ⟨row, component⟩
    cases row with
    | orderTwo j =>
        cases component with
        | root => exact (h2 j).1
        | face => exact (h2 j).2
    | orderFiveHalves j =>
        cases component with
        | root => exact (h25 j).1
        | face => exact (h25 j).2

/-- Inner completeness is exactly the four source tables. -/
theorem inner_complete_iff
    (inner : InnerRowAddress → Prop) :
    (∀ a, inner a) ↔
      (∀ j : Fin 7, inner (.oldOrderTwo j)) ∧
      (∀ j : Fin 10, inner (.oldOrderFiveHalves j)) ∧
      (∀ j : Fin 11, inner (.newOrderTwo j)) ∧
      (∀ j : Fin 17, inner (.newOrderFiveHalves j)) := by
  constructor
  · intro h
    exact ⟨fun j => h _, fun j => h _, fun j => h _, fun j => h _⟩
  · rintro ⟨h02, h025, h12, h125⟩ a
    cases a with
    | oldOrderTwo j => exact h02 j
    | oldOrderFiveHalves j => exact h025 j
    | newOrderTwo j => exact h12 j
    | newOrderFiveHalves j => exact h125 j

/-- Scalar completeness is exactly the three named cap/trial inequalities. -/
theorem scalar_complete_iff
    (scalar : ScalarBoundAddress → Prop) :
    (∀ a, scalar a) ↔
      scalar .trialIHLower ∧ scalar .trialIHUpper ∧ scalar .trialJLambdaHLower := by
  constructor
  · intro h
    exact ⟨h _, h _, h _⟩
  · rintro ⟨hlo, hup, hj⟩ a
    cases a <;> assumption

/-- A complete typed ledger is therefore equivalent to the exact six table blocks plus three
named global inequalities used by the upstream physical input. -/
theorem typedPhysicalLedger_exact_decomposition
    (outer : OuterBoundAddress → Prop)
    (inner : InnerRowAddress → Prop)
    (scalar : ScalarBoundAddress → Prop) :
    (typedPhysicalLedger outer inner scalar).Complete ↔
      ((∀ j : Fin 17, outer ⟨.orderTwo j, .root⟩ ∧ outer ⟨.orderTwo j, .face⟩) ∧
       (∀ j : Fin 35, outer ⟨.orderFiveHalves j, .root⟩ ∧
          outer ⟨.orderFiveHalves j, .face⟩)) ∧
      ((∀ j : Fin 7, inner (.oldOrderTwo j)) ∧
       (∀ j : Fin 10, inner (.oldOrderFiveHalves j)) ∧
       (∀ j : Fin 11, inner (.newOrderTwo j)) ∧
       (∀ j : Fin 17, inner (.newOrderFiveHalves j))) ∧
      (scalar .trialIHLower ∧ scalar .trialIHUpper ∧ scalar .trialJLambdaHLower) := by
  rw [typedPhysicalLedger_complete_iff, outer_complete_iff, inner_complete_iff,
    scalar_complete_iff]

#print axioms typedPhysicalLedger
#print axioms typedPhysicalLedger_complete_iff
#print axioms outer_complete_iff
#print axioms inner_complete_iff
#print axioms scalar_complete_iff
#print axioms typedPhysicalLedger_exact_decomposition

end D5.S3.PrimeGaps.PrimeGap186TypedPhysicalLedger
