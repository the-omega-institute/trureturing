/- GID: D5/S0/Tower/OneStepMemoryUniqueNaming
   generality: I
   mirror-B: D5/B/S0/Tower/OneStepMemoryUniqueNaming
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Gapless unique weighting of one-step binary names forces Fibonacci weights and growth. -/

import D5.S0.Tower.GoldenNames
import Mathlib.Analysis.SpecificLimits.Fibonacci
import Mathlib.Data.Set.Card
import Mathlib.Order.Interval.Set.Nat
import Mathlib.Tactic

/- Library-search audit trail (2026-09-02):
   * D5 searches for a `BijOn` theorem on `GoldenName`, unique one-step
     naming, and forced Fibonacci weights found no equivalent declaration.
     `GoldenNames.golden_name_card` supplies the canonical layer count, but
     its theorems assume Fibonacci weights rather than proving uniqueness.
   * Pinned Mathlib searches for `BijOn` with Fibonacci weights and uniqueness
     of Fibonacci recurrences found no exact theorem. The proof directly uses
     `Set.BijOn.ncard_eq`, `Set.ncard_Iio_nat`,
     `Nat.fib_add_two_strictMono`, and
     `tendsto_fib_succ_div_fib_atTop`.
   * GitHub Lean-code searches for `one step memory` with Fibonacci and for
     `BijOn Nat.fib` returned no third-party declaration. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S0.Tower.OneStepMemoryUniqueNaming

open Filter Set Topology
open D5.S0.Tower.GoldenNames

/-- Suppose that at every length, summing a weight over the occupied indices
of each canonical one-step-memory binary name is a bijection onto an initial
interval of natural numbers. Then the source's one-based weights (represented
at canonical index `n + 2`) and the interval sizes are forced to be Fibonacci,
and consecutive interval sizes have golden-ratio growth. -/
theorem one_step_memory_unique_naming
    (weight B : Nat -> Nat)
    (gaplessUnique : forall n, Set.BijOn
      (fun name : GoldenName n => (name.1.1.map weight).sum)
      Set.univ (Set.Iio (B n))) :
    (forall n, weight (n + 2) = Nat.fib (n + 2)) /\
      (forall n, B n = Nat.fib (n + 2)) /\
      Tendsto (fun n => (B (n + 1) : Real) / (B n : Real))
        atTop (nhds Real.goldenRatio) := by
  have hB : forall n, B n = Nat.fib (n + 2) := by
    intro n
    have hcard := (gaplessUnique n).ncard_eq
    rw [Set.ncard_univ, Nat.card_eq_fintype_card, golden_name_card,
      Set.ncard_Iio_nat] at hcard
    exact hcard.symm
  have hweight : forall n, weight (n + 2) = Nat.fib (n + 2) := by
    intro n
    let last : GoldenName (n + 1) := by
      refine ⟨⟨[n + 2], ?_⟩, ?_⟩
      · simp [List.IsZeckendorfRep]
      · simp
    have hlastValue :
        (last.1.1.map weight).sum = weight (n + 2) := by
      simp [last]
    have hLower : B n <= weight (n + 2) := by
      by_contra hnot
      have hInside : weight (n + 2) < B n := Nat.lt_of_not_ge hnot
      obtain ⟨lower, _, hlower⟩ := (gaplessUnique n).surjOn hInside
      let lifted : GoldenName (n + 1) :=
        ⟨lower.1, fun k hk => by have := lower.2 k hk; omega⟩
      have hliftedValue :
          (lifted.1.1.map weight).sum = weight (n + 2) := by
        simpa [lifted] using hlower
      have heq : lifted = last := (gaplessUnique (n + 1)).injOn
        (by simp) (by simp) (hliftedValue.trans hlastValue.symm)
      have hlist : lower.1.1 = [n + 2] := by
        simpa [lifted, last] using congrArg
          (fun name : GoldenName (n + 1) => name.1.1) heq
      have := lower.2 (n + 2) (by simp [hlist])
      omega
    have hUpper : weight (n + 2) <= B n := by
      by_contra hnot
      have hAbove : B n < weight (n + 2) := Nat.lt_of_not_ge hnot
      have hNext : B n < B (n + 1) := by
        rw [hB n, hB (n + 1)]
        exact Nat.fib_add_two_strictMono (Nat.lt_succ_self n)
      obtain ⟨name, _, hname⟩ := (gaplessUnique (n + 1)).surjOn hNext
      by_cases htop : n + 2 ∈ name.1.1
      · have hweightMem : weight (n + 2) ∈ name.1.1.map weight :=
          List.mem_map.mpr ⟨n + 2, htop, by simp⟩
        have hsum := List.le_sum_of_mem hweightMem
        change (name.1.1.map weight).sum = B n at hname
        rw [hname] at hsum
        omega
      · let lower : GoldenName n :=
          ⟨name.1, fun k hk => by
            have hklt := name.2 k hk
            have hkne : k ≠ n + 2 := fun heq => htop (heq.symm ▸ hk)
            omega⟩
        have hlowerMem := (gaplessUnique n).mapsTo (by simp : lower ∈ Set.univ)
        have hlowerValue : (lower.1.1.map weight).sum = B n := by
          simpa [lower] using hname
        rw [hlowerValue] at hlowerMem
        exact (lt_irrefl (B n)) hlowerMem
    exact (Nat.le_antisymm hUpper hLower).trans (hB n)
  refine ⟨hweight, hB, ?_⟩
  have hlim : Tendsto
      (fun n => (Nat.fib ((n + 2) + 1) : Real) / (Nat.fib (n + 2) : Real))
      atTop (nhds Real.goldenRatio) := by
    simpa only [Function.comp_def] using
      tendsto_fib_succ_div_fib_atTop.comp (Filter.tendsto_add_atTop_nat 2)
  simpa [hB, Nat.add_assoc] using hlim

#print axioms one_step_memory_unique_naming

end D5.S0.Tower.OneStepMemoryUniqueNaming
