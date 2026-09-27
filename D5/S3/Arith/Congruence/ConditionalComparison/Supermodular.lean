/- GID: D5/S3/Arith/Congruence/ConditionalComparison/Supermodular
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: MIT source transplant: Increasing supermodular set functions. -/

/-
Copyright (c) 2026 Michael Schroeder. MIT License.
Source: three-prime-factors-complete/formal/Erdos7/Supermodular.lean
Archive, full license, import map and retirement condition:
Library/Arith/schroeder2026noncoverage.md.
Original declaration names and proofs are retained. Utility is none: the
results are symbolic laws on arbitrary finite types, without certified
instances, bounded enumerations, checkers or numerical certificate inputs.
-/

import D5.S3.Arith.Congruence.ConditionalComparison.FiniteProbability
import Mathlib.Data.Finset.BooleanAlgebra

/-!
# Increasing supermodular set functions

The paper uses supermodularity twice: to replace mutually exclusive symbols by
one common gate, and to replace all first-block prefix events by a single
monotone run.  This module isolates the exact finite inequalities.
-/

namespace Erdos7

variable {ι : Type*} [DecidableEq ι]

/-- Supermodularity on the Boolean lattice of finite subsets. -/
def Supermodular (F : Finset ι → ℚ) : Prop :=
  ∀ A B, F A + F B ≤ F (A ∩ B) + F (A ∪ B)

/-- Monotonicity on the Boolean lattice of finite subsets. -/
def Increasing (F : Finset ι → ℚ) : Prop :=
  ∀ ⦃A B⦄, A ⊆ B → F A ≤ F B

theorem Supermodular.marginal_mono {F : Finset ι → ℚ} (hF : Supermodular F)
    {A B : Finset ι} (hAB : A ⊆ B) {x : ι} (hx : x ∉ B) :
    F (insert x A) - F A ≤ F (insert x B) - F B := by
  have hinter : insert x A ∩ B = A := by
    ext y
    simp only [Finset.mem_inter, Finset.mem_insert]
    constructor
    · rintro ⟨hy, hyB⟩
      rcases hy with rfl | hyA
      · exact (hx hyB).elim
      · exact hyA
    · intro hyA
      exact ⟨Or.inr hyA, hAB hyA⟩
  have hunion : insert x A ∪ B = insert x B := by
    ext y
    simp only [Finset.mem_union, Finset.mem_insert]
    tauto
  have h := hF (insert x A) B
  rw [hinter, hunion] at h
  linarith

/-- The marginal increment along the canonical chain of initial segments. -/
def prefixMarginal (F : Finset ℕ → ℚ) (i : ℕ) : ℚ :=
  F (Finset.range (i + 1)) - F (Finset.range i)

theorem prefixMarginal_nonneg {F : Finset ℕ → ℚ} (hF : Increasing F) (i : ℕ) :
    0 ≤ prefixMarginal F i := by
  unfold prefixMarginal
  have hsub : Finset.range i ⊆ Finset.range (i + 1) := by
    intro k hk
    simp only [Finset.mem_range] at hk ⊢
    omega
  linarith [hF hsub]

/--
Every supermodular function lies below its modular linearization along a
maximal chain.  This deterministic inequality is the formal core of the
Bernoulli rearrangement used in the proof.
-/
theorem supermodular_le_prefix_linearization
    {F : Finset ℕ → ℚ} (hF : Supermodular F) (n : ℕ)
    (S : Finset ℕ) (hS : S ⊆ Finset.range n) :
    F S ≤ F ∅ + ∑ i ∈ S, prefixMarginal F i := by
  induction n generalizing S with
  | zero =>
      have hEmpty : S = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro i hi
        exact (Finset.notMem_empty i) (hS hi)
      simp [hEmpty]
  | succ n ih =>
      by_cases hn : n ∈ S
      · let T := S.erase n
        have hnT : n ∉ T := Finset.notMem_erase n S
        have hTsub : T ⊆ Finset.range n := by
          intro i hi
          have hiS : i ∈ S := (Finset.mem_erase.mp hi).2
          have hin : i < n + 1 := Finset.mem_range.mp (hS hiS)
          have hine : i ≠ n := (Finset.mem_erase.mp hi).1
          exact Finset.mem_range.mpr (by omega)
        have hInd := ih T hTsub
        have hMarg := hF.marginal_mono hTsub
          (show n ∉ Finset.range n from Finset.notMem_range_self)
        have hInsert : insert n T = S := by
          simpa [T] using Finset.insert_erase hn
        have hRange : insert n (Finset.range n) = Finset.range (n + 1) := by
          exact Finset.range_add_one.symm
        rw [hRange] at hMarg
        rw [← hInsert, Finset.sum_insert hnT]
        calc
          F (insert n T) = (F (insert n T) - F T) + F T := by ring
          _ ≤ (F (Finset.range (n + 1)) - F (Finset.range n)) +
                (F ∅ + ∑ i ∈ T, prefixMarginal F i) :=
              add_le_add hMarg hInd
          _ = F ∅ + (prefixMarginal F n + ∑ i ∈ T, prefixMarginal F i) := by
              unfold prefixMarginal
              ring
      · have hS' : S ⊆ Finset.range n := by
          intro i hi
          have hin : i < n + 1 := Finset.mem_range.mp (hS hi)
          have hine : i ≠ n := by
            intro hEq
            exact hn (hEq ▸ hi)
          exact Finset.mem_range.mpr (by omega)
        exact ih S hS'

/--
Bernoulli rearrangement in the exact form used later.  The labels are ordered
along the chain `range 0 ⊆ range 1 ⊆ ...`; no independence is assumed.
-/
theorem bernoulli_rearrangement
    {Ω : Type*} [Fintype Ω] (μ : FiniteLaw Ω)
    {F : Finset ℕ → ℚ} (hSup : Supermodular F) (hInc : Increasing F)
    (n : ℕ) (active : Ω → Finset ℕ)
    (hactive : ∀ ω, active ω ⊆ Finset.range n)
    (ρ : ℕ → ℚ)
    (hmarg : ∀ i < n, μ.prob (fun ω ↦ i ∈ active ω) ≤ ρ i) :
    μ.expect (fun ω ↦ F (active ω)) ≤
      F ∅ + ∑ i ∈ Finset.range n, ρ i * prefixMarginal F i := by
  have hpoint : ∀ ω,
      F (active ω) ≤ F ∅ + ∑ i ∈ active ω, prefixMarginal F i := by
    intro ω
    exact supermodular_le_prefix_linearization hSup n (active ω) (hactive ω)
  calc
    μ.expect (fun ω ↦ F (active ω))
        ≤ μ.expect (fun ω ↦ F ∅ + ∑ i ∈ active ω, prefixMarginal F i) :=
          μ.expect_mono hpoint
    _ = F ∅ + ∑ i ∈ Finset.range n,
          μ.prob (fun ω ↦ i ∈ active ω) * prefixMarginal F i := by
          rw [μ.expect_add, μ.expect_const]
          congr 1
          have hrewrite : ∀ ω,
              (∑ i ∈ active ω, prefixMarginal F i) =
                ∑ i ∈ Finset.range n,
                  if i ∈ active ω then prefixMarginal F i else 0 := by
            intro ω
            calc
              (∑ i ∈ active ω, prefixMarginal F i) =
                  ∑ i ∈ active ω,
                    (if i ∈ active ω then prefixMarginal F i else 0) := by simp
              _ = ∑ i ∈ Finset.range n,
                    (if i ∈ active ω then prefixMarginal F i else 0) := by
                    apply Finset.sum_subset (hactive ω)
                    intro i _ hi
                    simp [hi]
          simp_rw [hrewrite]
          rw [μ.expect_finset_sum]
          apply Finset.sum_congr rfl
          intro i _
          exact μ.expect_indicator_mul (fun ω ↦ i ∈ active ω) (prefixMarginal F i)
    _ ≤ F ∅ + ∑ i ∈ Finset.range n, ρ i * prefixMarginal F i := by
          have hsum :
              (∑ i ∈ Finset.range n,
                μ.prob (fun ω ↦ i ∈ active ω) * prefixMarginal F i) ≤
              ∑ i ∈ Finset.range n, ρ i * prefixMarginal F i := by
            apply Finset.sum_le_sum
            intro i hi
            exact mul_le_mul_of_nonneg_right
                (hmarg i (Finset.mem_range.mp hi))
                (prefixMarginal_nonneg hInc i)
          linarith

theorem sum_prefixMarginal (F : Finset ℕ → ℚ) (n : ℕ) :
    (∑ i ∈ Finset.range n, prefixMarginal F i) =
      F (Finset.range n) - F ∅ := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ]
      rw [ih]
      unfold prefixMarginal
      ring

/-- Equal marginal caps collapse all labels to one all-open gate. -/
theorem common_gate_bound
    {Ω : Type*} [Fintype Ω] (μ : FiniteLaw Ω)
    {F : Finset ℕ → ℚ} (hSup : Supermodular F) (hInc : Increasing F)
    (n : ℕ) (active : Ω → Finset ℕ)
    (hactive : ∀ ω, active ω ⊆ Finset.range n)
    (r : ℚ)
    (hmarg : ∀ i < n, μ.prob (fun ω ↦ i ∈ active ω) ≤ r) :
    μ.expect (fun ω ↦ F (active ω)) ≤
      (1 - r) * F ∅ + r * F (Finset.range n) := by
  have h := bernoulli_rearrangement μ hSup hInc n active hactive (fun _ ↦ r) hmarg
  calc
    μ.expect (fun ω ↦ F (active ω))
        ≤ F ∅ + ∑ i ∈ Finset.range n, r * prefixMarginal F i := h
    _ = (1 - r) * F ∅ + r * F (Finset.range n) := by
        rw [← Finset.mul_sum, sum_prefixMarginal]
        ring

/-- A rational-valued cardinality hinge. -/
def cardHinge (t : ℕ) (A : Finset ι) : ℚ :=
  (A.card - t : ℕ)

theorem cardHinge_increasing (t : ℕ) : Increasing (cardHinge (ι := ι) t) := by
  intro A B hAB
  unfold cardHinge
  norm_cast
  exact Nat.sub_le_sub_right (Finset.card_le_card hAB) t

theorem cardHinge_supermodular (t : ℕ) : Supermodular (cardHinge (ι := ι) t) := by
  intro A B
  unfold cardHinge
  norm_cast
  have hcard := Finset.card_union_add_card_inter A B
  have hIA : (A ∩ B).card ≤ A.card :=
    Finset.card_le_card Finset.inter_subset_left
  have hIB : (A ∩ B).card ≤ B.card :=
    Finset.card_le_card Finset.inter_subset_right
  have hAU : A.card ≤ (A ∪ B).card :=
    Finset.card_le_card Finset.subset_union_left
  have hBU : B.card ≤ (A ∪ B).card :=
    Finset.card_le_card Finset.subset_union_right
  omega

end Erdos7
