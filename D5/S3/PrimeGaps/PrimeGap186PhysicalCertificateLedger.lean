/- GID: D5/S3/PrimeGaps/PrimeGap186PhysicalCertificateLedger
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Split the PrimeGaps186 physical-integral input into independently dischargeable finite obligations. -/

import Mathlib
import D5.S3.PrimeGaps.PrimeGap186PhysicalSourceGeometry

/-!
The upstream `physical_integral_bounds` input packages 104 outer inequalities,
45 inner inequalities, and three scalar cap/trial inequalities.  Treating that
package as one proposition hides which pieces have actually been replayed in
Lean.  This file introduces a finite proof ledger in which every cell is an
independent proposition.

No numerical inequality is assumed here.  The point is architectural: a future
interval/rational certificate may discharge one cell at a time, while the final
assembly theorem is already kernel checked.
-/

namespace D5.S3.PrimeGaps.PrimeGap186PhysicalCertificateLedger

/-- A finite family of independently checkable proof obligations. -/
structure FiniteProofLedger (ι : Type) where
  obligation : ι → Prop

namespace FiniteProofLedger

/-- Every cell in a proof ledger has been discharged. -/
def Complete {ι : Type} (L : FiniteProofLedger ι) : Prop :=
  ∀ i, L.obligation i

/-- Disjointly combine two proof ledgers. -/
def sum {ι κ : Type} (L : FiniteProofLedger ι) (R : FiniteProofLedger κ) :
    FiniteProofLedger (Sum ι κ) where
  obligation := Sum.elim L.obligation R.obligation

/-- Completeness of a disjoint union is exactly completeness of both components. -/
theorem complete_sum_iff {ι κ : Type} (L : FiniteProofLedger ι) (R : FiniteProofLedger κ) :
    (L.sum R).Complete ↔ L.Complete ∧ R.Complete := by
  constructor
  · intro h
    constructor
    · intro i
      exact h (Sum.inl i)
    · intro k
      exact h (Sum.inr k)
  · rintro ⟨hL, hR⟩ i
    cases i with
    | inl i => exact hL i
    | inr k => exact hR k

/-- A ledger can be refined without changing its logical content by replacing each cell
with an equivalent certificate proposition. -/
theorem complete_congr {ι : Type} {L R : FiniteProofLedger ι}
    (h : ∀ i, L.obligation i ↔ R.obligation i) :
    L.Complete ↔ R.Complete := by
  constructor
  · intro hL i
    exact (h i).1 (hL i)
  · intro hR i
    exact (h i).2 (hR i)

end FiniteProofLedger

/-- The three scalar inequalities appended to the 104 outer and 45 inner rows upstream. -/
inductive PhysicalScalarObligation
  | trialIHLower
  | trialIHUpper
  | trialJLambdaLower
  deriving DecidableEq, Fintype

/-- Exact index type of the numerical input packaged by the upstream physical-bound axiom. -/
abbrev PrimeGap186PhysicalObligationIndex : Type :=
  Sum (Fin 104) (Sum (Fin 45) PhysicalScalarObligation)

/-- The upstream physical package contains exactly 152 independently dischargeable cells. -/
theorem primeGap186PhysicalObligationIndex_card :
    Fintype.card PrimeGap186PhysicalObligationIndex = 152 := by
  norm_num [PrimeGap186PhysicalObligationIndex]

/-- Package the three source-level classes of physical inequalities without asserting any of them. -/
def primeGap186PhysicalLedger
    (outer : Fin 104 → Prop)
    (inner : Fin 45 → Prop)
    (scalar : PhysicalScalarObligation → Prop) :
    FiniteProofLedger PrimeGap186PhysicalObligationIndex :=
  (⟨outer⟩ : FiniteProofLedger (Fin 104)).sum
    ((⟨inner⟩ : FiniteProofLedger (Fin 45)).sum
      (⟨scalar⟩ : FiniteProofLedger PhysicalScalarObligation))

/-- Final assembly theorem for the physical proof ledger.  It exposes all three blocks
separately, so replacing any subset by kernel-checked certificates never requires trusting
the remaining blocks as one opaque proposition. -/
theorem primeGap186PhysicalLedger_complete_iff
    (outer : Fin 104 → Prop)
    (inner : Fin 45 → Prop)
    (scalar : PhysicalScalarObligation → Prop) :
    (primeGap186PhysicalLedger outer inner scalar).Complete ↔
      (∀ j, outer j) ∧ (∀ j, inner j) ∧ (∀ j, scalar j) := by
  rw [primeGap186PhysicalLedger, FiniteProofLedger.complete_sum_iff,
    FiniteProofLedger.complete_sum_iff]
  rfl

/-- Monotone migration principle: if every old ledger cell is implied by a new,
stronger certificate cell, completeness of the new ledger discharges the old one. -/
theorem complete_of_pointwise_stronger {ι : Type}
    (old new : FiniteProofLedger ι)
    (hstrong : ∀ i, new.obligation i → old.obligation i)
    (hnew : new.Complete) : old.Complete := by
  intro i
  exact hstrong i (hnew i)

#print axioms FiniteProofLedger.complete_sum_iff
#print axioms FiniteProofLedger.complete_congr
#print axioms primeGap186PhysicalObligationIndex_card
#print axioms primeGap186PhysicalLedger_complete_iff
#print axioms complete_of_pointwise_stronger

end D5.S3.PrimeGaps.PrimeGap186PhysicalCertificateLedger
