/- GID: D5/S1/Words/Complexity/MorseHedlundConverse
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Eventually periodic one-sided words have uniformly bounded factor complexity; together with the forward theorem, this yields the finite-alphabet Morse-Hedlund equivalence. -/

import D5.S1.Words.Complexity.MorseHedlund
import Mathlib.Data.Nat.Periodic

/- Provenance: Native proof over pinned mathlib. -/

/-! SEARCH RECEIPT (2026-08-18, pinned repository and pinned mathlib):
Repository searches for `MorseHedlund`, `EventuallyPeriodicWord`, `wordFactorSet`,
and factor-complexity variants found the definitions and membership theorem in
`D5/S1/Words/Complexity/MorseHedlund.lean:17-29`, the eventual-periodicity
convention at `:45-46`, and the forward Morse-Hedlund implication at `:136-147`.
Relevant candidates inspected for reuse included the purely periodic
mechanical-word bound in
`D5/S1/Words/Complexity/MechanicalComplexityCharacterization.lean:17-38` and its
exact-complexity/aperiodicity equivalence at `:41-73`; the exact mechanical and
golden factor counts at
`D5/S1/Words/Mechanical/MechanicalFactorComplexity.lean:350-390` and
`D5/S1/Words/GoldenFactorComplexity.lean:340-341`; the specialized mechanical
eventual-periodicity predicate and characterization in
`D5/S1/Words/Mechanical/MechanicalPeriodicity.lean:14-17,112-122`; the
`wordFactorSet` inclusion and equality results at
`D5/S1/Words/Complexity/GoldenSubshiftMinimality.lean:42-82`; the golden-word
periodic-tail counting argument at
`D5/S1/Words/Complexity/SubshiftTopology.lean:122-153`, which runs the same
`Periodic.add_const` / `map_mod_nat` / `card_image_le` chain used below but only
for the golden word inside a private proof; and the finite-state orbit
eventual-periodicity result in
`D5/S3/ObserverMemory/Prediction/FiniteInputGeneratorPeriodicity.lean:26-63`,
which concerns iterated orbits of finite product states rather than factor
counts. This list is the set of candidates actually examined and is not claimed
to be exhaustive. Each is restricted to mechanical words, to the golden word, or
to a private local proof, so none of them bounds `wordFactorSet` from the general
`EventuallyPeriodicWord` hypothesis or states the equivalence proved below.

Pinned-mathlib searches for Morse-Hedlund, word/subword/factor complexity,
periodic words, and symbolic-dynamics language cardinality found no such
complexity theorem. Mathlib provides the generic `Function.Periodic` convention
at `Mathlib/Algebra/Ring/Periodic.lean:43-46`, its `add_const` transport at
`:116-118`, and reduction modulo a natural period at
`Mathlib/Data/Nat/Periodic.lean:35-37`; these are reused below. Its symbolic
language API defines `FullShift.LanguageOn` and `MulSubshift.languageOn` at
`Mathlib/Dynamics/SymbolicDynamics/Basic.lean:611-621`, without a periodicity or
cardinality theorem, while `Mathlib/Data/List/Sublists.lean:17-19` explicitly
concerns not-necessarily-contiguous sublists. The finite counting steps reuse
`Finset.card_le_card`, `Finset.card_range`, and `Finset.card_image_le` from
`Mathlib/Data/Finset/Card.lean:65-67,173-175,225-226`.

Statement-shape audit: the existential natural bound is retained because a
downstream caller can use its witness directly as a factor length; the proof
supplies the sharper witness `s + p`, and Layer 2 specializes the bound at that
witness. A `BddAbove (Set.range ...)` wrapper would require unpacking the same
natural inequality before that specialization and would not strengthen it. -/

namespace D5.S1.Words.Complexity.MorseHedlundConverse

open D5.S1.Words.Complexity

private theorem tail_wordFactor_eq_mod {A : Type*} {x : Nat -> A} {s p n i : Nat}
    (hperiodic : forall t, x (s + t + p) = x (s + t))
    (hi : s <= i) :
    wordFactor x n i = wordFactor x n (s + (i - s) % p) := by
  have htail : Function.Periodic (fun t => x (s + t)) p := by
    intro t
    simpa [Nat.add_assoc] using hperiodic t
  funext k
  have hmod := (htail.add_const k.val).map_mod_nat (i - s)
  change x (i + k.val) = x (s + (i - s) % p + k.val)
  rw [show i + k.val = s + ((i - s) + k.val) by omega]
  simpa [Nat.add_assoc] using hmod.symm

variable {A : Type*} [Fintype A]

/-- An eventually periodic one-sided word has a uniform finite bound on all of
its factor complexities. -/
theorem factor_complexity_bddAbove_of_eventuallyPeriodic (x : Nat -> A)
    (h : EventuallyPeriodicWord x) :
    exists C, forall n, (wordFactorSet x n).card <= C := by
  classical
  obtain ⟨s, p, hp, hperiodic⟩ := h
  refine ⟨s + p, fun n => ?_⟩
  let representatives : Finset (Fin n -> A) :=
    (Finset.range (s + p)).image fun i => wordFactor x n i
  have hsubset : wordFactorSet x n ⊆ representatives := by
    intro w hw
    obtain ⟨i, rfl⟩ := mem_wordFactorSet.mp hw
    by_cases hi : i < s
    · exact Finset.mem_image.mpr
        ⟨i, Finset.mem_range.mpr (hi.trans_le (Nat.le_add_right s p)), rfl⟩
    · let j := s + (i - s) % p
      have hj : j < s + p := by
        dsimp [j]
        exact Nat.add_lt_add_left (Nat.mod_lt _ hp) s
      refine Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr hj, ?_⟩
      exact (tail_wordFactor_eq_mod hperiodic (Nat.le_of_not_gt hi)).symm
  exact (Finset.card_le_card hsubset).trans
    (Finset.card_image_le.trans_eq (Finset.card_range (s + p)))

/-- A one-sided infinite word is eventually periodic exactly when its factor
complexity is at most the factor length for some length. -/
theorem eventuallyPeriodic_iff_exists_factor_complexity_le (x : Nat -> A) :
    EventuallyPeriodicWord x <-> exists n, (wordFactorSet x n).card <= n := by
  constructor
  · intro h
    obtain ⟨C, hC⟩ := factor_complexity_bddAbove_of_eventuallyPeriodic x h
    exact ⟨C, hC C⟩
  · rintro ⟨n, hn⟩
    exact eventuallyPeriodic_of_factor_complexity_le x n hn

#print axioms factor_complexity_bddAbove_of_eventuallyPeriodic
#print axioms eventuallyPeriodic_iff_exists_factor_complexity_le

end D5.S1.Words.Complexity.MorseHedlundConverse
