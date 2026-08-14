/- GID: D5/S0/Asymptotics/WeightedProbability/UniformEscapeProbabilityBridge
   generality: G
   mirror-B: D5/B/S0/Asymptotics/WeightedProbability/UniformEscapeProbabilityBridge
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Uniform sample weights identify weighted escape probability with frozen counting. -/

/- Library-search audit trail (2026-08-15):
   * Repository searches found the matrix-coordinate equivalence only as the private
     `listing_equiv` in `Diagonal/EscapeCount` and the private `listingEquiv` in
     `Diagonal/DistanceProfile`; neither can be imported by this bridge.
   * Repository searches found no theorem relating the weighted and counting
     `escapeProbability` declarations and no uniform `sampleWeight` theorem.
   * Pinned Mathlib supplies `Equiv.subtypeEquiv`, `Nat.card_congr`,
     `Fintype.card_subtype`, `Fintype.card_fun`, and the finite sum/product lemmas used
     below; no theorem packages this repository-specific probability bridge.
-/

import D5.S0.Asymptotics.FixedPointFreeEscapeProbability
import D5.S0.Asymptotics.WeightedProbability.FiniteBonferroni

open scoped BigOperators

namespace D5.S0.Asymptotics.WeightedProbability.UniformEscapeProbabilityBridge

open FiniteProductCapture
open D5.S0.Diagonal.EscapeCount

noncomputable section

variable {A Y : Type*}

local instance (priority := low) (p : Prop) : Decidable p := Classical.propDecidable p

/-- The independent diagonal/off-row coordinates reassemble bijectively into listings. -/
def listingEquiv [DecidableEq A] : Sample A Y ≃ (A -> A -> Y) where
  toFun := listing
  invFun g := (fun a => g a a, fun a b => g a b.1)
  left_inv s := by
    rcases s with ⟨X, R⟩
    apply Prod.ext
    · funext a
      simp [listing]
    · funext a b
      simp [listing, b.property]
  right_inv g := by
    funext a b
    by_cases h : b = a <;> simp [listing, h]

/-- Every sample has the reciprocal matrix-cardinality weight under uniform cell weights. -/
theorem sampleWeight_uniform [Fintype A] [Fintype Y] [DecidableEq A]
    (s : Sample A Y) :
    sampleWeight (fun _ _ => (1 : Real) / Fintype.card Y) s =
      (1 : Real) / Nat.card (A -> A -> Y) := by
  classical
  have hoff (a : A) : Fintype.card {b : A // b ≠ a} = Fintype.card A - 1 := by
    rw [Fintype.card_subtype_compl]
    simp
  rw [sampleWeight, Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fun]
  simp only [Finset.prod_const, Finset.card_univ, hoff]
  rw [← pow_mul, ← pow_add, one_div_pow, Nat.cast_pow, Nat.cast_pow, ← pow_mul]
  congr 1
  generalize Fintype.card A = n
  cases n with
  | zero => rfl
  | succ n => simp; ring

/-- Under uniform cell weights, every event is its finite cardinality ratio. -/
theorem eventProbability_uniform [Fintype A] [Fintype Y] [DecidableEq A]
    (P : Sample A Y -> Prop) [DecidablePred P] :
    eventProbability (fun _ _ => (1 : Real) / Fintype.card Y) P =
      (Nat.card {s : Sample A Y // P s} : Real) /
        Nat.card (A -> A -> Y) := by
  classical
  rw [eventProbability]
  simp_rw [sampleWeight_uniform]
  have hcard :
      ((Finset.univ.filter P).card : Real) = Nat.card {s : Sample A Y // P s} := by
    norm_cast
    simpa [Nat.card_eq_fintype_card] using (Fintype.card_subtype P).symm
  calc
    (∑ s : Sample A Y,
        if P s then (1 : Real) / Nat.card (A -> A -> Y) else 0) =
        (Finset.univ.filter P).sum
          (fun _ => (1 : Real) / Nat.card (A -> A -> Y)) := by
      simpa using (Finset.sum_filter (s := Finset.univ) P
        (fun _ => (1 : Real) / Nat.card (A -> A -> Y))).symm
    _ = ((Finset.univ.filter P).card : Real) *
        ((1 : Real) / Nat.card (A -> A -> Y)) := by simp
    _ = _ := by rw [hcard]; ring

/-- Uniform weighted escape probability is exactly the frozen counting probability. -/
theorem uniform_escapeProbability_eq_counting
    [Fintype A] [Fintype Y] [DecidableEq A] (f : Y -> Y) :
    FiniteBonferroni.escapeProbability
        (fun (_ : A) (_ : Y) => (1 : Real) / Fintype.card Y) f =
      D5.S0.Asymptotics.FixedPointFreeEscapeProbability.escapeProbability
        (A := A) f := by
  classical
  rw [FiniteBonferroni.escapeProbability, eventProbability_uniform,
    D5.S0.Asymptotics.FixedPointFreeEscapeProbability.escapeProbability]
  congr 1
  exact_mod_cast Nat.card_congr
    ((listingEquiv (A := A) (Y := Y)).subtypeEquiv fun s =>
      FiniteBonferroni.no_capture_iff_isEscaped f s)

#print axioms listingEquiv
#print axioms sampleWeight_uniform
#print axioms eventProbability_uniform
#print axioms uniform_escapeProbability_eq_counting

end

end D5.S0.Asymptotics.WeightedProbability.UniformEscapeProbabilityBridge
