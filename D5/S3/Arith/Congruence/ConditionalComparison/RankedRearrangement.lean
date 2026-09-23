/- GID: D5/S3/Arith/Congruence/ConditionalComparison/RankedRearrangement
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: MIT source transplant: Ranked Bernoulli rearrangement. -/

/-
Copyright (c) 2026 Michael Schroeder. MIT License.
Source: three-prime-factors-complete/formal/Erdos7/RankedRearrangement.lean
Archive, full license, import map and retirement condition:
Library/Arith/schroeder2026noncoverage.md.
Original declaration names and proofs are retained. Utility is none: the
results are symbolic laws on arbitrary finite types, without certified
instances, bounded enumerations, checkers or numerical certificate inputs.
-/

import D5.S3.Arith.Congruence.ConditionalComparison.Hybrid
import D5.S3.Arith.Congruence.ConditionalComparison.Runs
import Mathlib.Tactic

/-!
# Ranked Bernoulli rearrangement

The initial ternary selector supplies marginal bounds indexed by prefix
depth, not conditional digit bounds.  This module packages the precise
bridge: after labels are ordered by depth, the Lovasz-chain linearization is
exactly expectation under the finite run having those depth survivals.
-/

namespace Erdos7

/-- Extend a rank on `Fin L` to natural labels; only labels below `L` will be
used. -/
def rankNat {L : ℕ} (rank : Fin L → ℕ) (l : ℕ) : ℕ :=
  if h : l < L then rank ⟨l, h⟩ else 0

/-- Labels whose rank is at most `d`. -/
noncomputable def rankSet {L : ℕ} (rank : Fin L → ℕ) (d : ℕ) : Finset ℕ :=
  (Finset.range L).filter fun l ↦ rankNat rank l ≤ d

/-- The natural label order is nondecreasing in rank. -/
def RankSorted {L : ℕ} (rank : Fin L → ℕ) : Prop :=
  ∀ i j : Fin L, (i : ℕ) ≤ j → rank i ≤ rank j

/-- Every finite downward-closed subset of the natural numbers is its own
cardinality-sized initial segment. -/
theorem downwardFinset_eq_range_card (s : Finset ℕ)
    (hdown : ∀ ⦃i j : ℕ⦄, i ≤ j → j ∈ s → i ∈ s) :
    s = Finset.range s.card := by
  ext i
  constructor
  · intro hi
    have hsub : Finset.range (i + 1) ⊆ s := by
      intro k hk
      exact hdown (by simpa using Finset.mem_range.mp hk) hi
    have hcard := Finset.card_le_card hsub
    simp only [Finset.card_range] at hcard
    exact Finset.mem_range.mpr (by omega)
  · intro hi
    have hicard : i < s.card := Finset.mem_range.mp hi
    by_contra his
    have hsub : s ⊆ Finset.range i := by
      intro j hj
      apply Finset.mem_range.mpr
      by_contra hji
      have hij : i ≤ j := by omega
      exact his (hdown hij hj)
    have hcard := Finset.card_le_card hsub
    simp only [Finset.card_range] at hcard
    omega

theorem rankSet_downward {L : ℕ} {rank : Fin L → ℕ}
    (hsorted : RankSorted rank) (d : ℕ) :
    ∀ ⦃i j : ℕ⦄, i ≤ j → j ∈ rankSet rank d → i ∈ rankSet rank d := by
  intro i j hij hj
  have hjL : j < L := by
    exact Finset.mem_range.mp (Finset.mem_filter.mp hj).1
  have hiL : i < L := lt_of_le_of_lt hij hjL
  have hjrank : rank ⟨j, hjL⟩ ≤ d := by
    simpa [rankSet, rankNat, hjL] using (Finset.mem_filter.mp hj).2
  have hirank : rank ⟨i, hiL⟩ ≤ rank ⟨j, hjL⟩ :=
    hsorted ⟨i, hiL⟩ ⟨j, hjL⟩ hij
  simp only [rankSet, Finset.mem_filter, Finset.mem_range]
  simp [rankNat, hiL, hirank.trans hjrank]

theorem rankSet_eq_range_card {L : ℕ} {rank : Fin L → ℕ}
    (hsorted : RankSorted rank) (d : ℕ) :
    rankSet rank d = Finset.range (rankSet rank d).card :=
  downwardFinset_eq_range_card _ (rankSet_downward hsorted d)

/-- Telescoping along a ranked initial segment. -/
theorem value_rankSet_eq_linearization {L : ℕ} {rank : Fin L → ℕ}
    (hsorted : RankSorted rank) (F : Finset ℕ → ℚ) (d : ℕ) :
    F (rankSet rank d) =
      F ∅ + ∑ l ∈ rankSet rank d, prefixMarginal F l := by
  rw [rankSet_eq_range_card hsorted]
  rw [sum_prefixMarginal]
  ring

/-- The common-coupling chain expression is exactly a run expectation. -/
theorem run_expect_rankSet_eq {a L : ℕ} (R : RunSpec a)
    (rank : Fin L → ℕ) (hsorted : RankSorted rank)
    (hrank : ∀ l, rank l ≤ a) (F : Finset ℕ → ℚ) :
    R.law.expect (fun d ↦ F (rankSet rank d)) =
      F ∅ + ∑ l ∈ Finset.range L,
        R.survival (rankNat rank l) *
          prefixMarginal F l := by
  have hpoint : (fun d : Fin (a + 1) ↦ F (rankSet rank d)) =
      (fun d : Fin (a + 1) ↦
        F ∅ + ∑ l ∈ rankSet rank d, prefixMarginal F l) := by
    funext d
    exact value_rankSet_eq_linearization hsorted F d
  rw [hpoint, FiniteLaw.expect_add, FiniteLaw.expect_const]
  have hreindex : ∀ d : Fin (a + 1),
      (∑ l ∈ rankSet rank d, prefixMarginal F l) =
        ∑ l ∈ Finset.range L,
          if rankNat rank l ≤ (d : ℕ) then prefixMarginal F l else 0 := by
    intro d
    unfold rankSet
    rw [Finset.sum_filter]
  simp_rw [hreindex]
  rw [R.law.expect_finset_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro l hl
  let lf : Fin L := ⟨l, Finset.mem_range.mp hl⟩
  calc
    R.law.expect (fun d ↦
        if rankNat rank l ≤ (d : ℕ) then prefixMarginal F l else 0) =
        R.law.prob (fun d ↦ rankNat rank l ≤ (d : ℕ)) *
          prefixMarginal F l :=
      R.law.expect_indicator_mul _ _
    _ = R.survival (rankNat rank l) * prefixMarginal F l := by
      congr 1
      have hrankNat : rankNat rank l = rank lf := by
        simp [rankNat, lf, Finset.mem_range.mp hl]
      rw [hrankNat]
      exact R.law_prob_ge_eq_survival (hrank lf)

namespace BasedCausalLaw

/-- Hybrid comparison with the initial common coupling presented as an exact
finite run rather than as a linearized sum. -/
theorem hybrid_rank_run_bound
    {Ω : Type*} [Fintype Ω] {Q n a L : ℕ}
    (P : BasedCausalLaw Ω Q n)
    (initial : Ω → Finset ℕ)
    (hinitial : ∀ ω, initial ω ⊆ Finset.range L)
    (req : ℕ → Fin n → Option (Fin Q))
    (F : Finset ℕ → ℚ) (hSup : Supermodular F) (hInc : Increasing F)
    (R : RunSpec a) (rank : Fin L → ℕ)
    (hsorted : RankSorted rank) (hrank : ∀ l, rank l ≤ a)
    (hmarg : ∀ l : Fin L,
      P.initialLaw.prob (fun ω ↦ (l : ℕ) ∈ initial ω) ≤
        R.survival (rank l)) :
    P.expect (fun x ↦ F (active initial req x)) ≤
      R.law.expect (fun d ↦
        P.gateFunctional req F (rankSet rank d)) := by
  let ρ : ℕ → ℚ := fun l ↦
    if h : l < L then R.survival (rank ⟨l, h⟩) else 0
  have hmarg' : ∀ l < L,
      P.initialLaw.prob (fun ω ↦ l ∈ initial ω) ≤ ρ l := by
    intro l hl
    simpa [ρ, hl] using hmarg ⟨l, hl⟩
  have h := P.hybrid_prefix_causal_bound initial hinitial req F hSup hInc
    ρ hmarg'
  calc
    P.expect (fun x ↦ F (active initial req x)) ≤
        P.gateFunctional req F ∅ +
          ∑ l ∈ Finset.range L,
            ρ l * prefixMarginal (P.gateFunctional req F) l := h
    _ = P.gateFunctional req F ∅ +
          ∑ l ∈ Finset.range L,
            R.survival
                (rankNat rank l) *
              prefixMarginal (P.gateFunctional req F) l := by
          apply congrArg (fun z ↦ P.gateFunctional req F ∅ + z)
          apply Finset.sum_congr rfl
          intro l hl
          have hlL : l < L := Finset.mem_range.mp hl
          have hrho : ρ l = R.survival (rankNat rank l) := by
            simp [ρ, rankNat, hlL]
          rw [hrho]
    _ = R.law.expect (fun d ↦
          P.gateFunctional req F (rankSet rank d)) :=
        (run_expect_rankSet_eq R rank hsorted hrank
          (P.gateFunctional req F)).symm

end BasedCausalLaw
end Erdos7
