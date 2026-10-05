/- GID: D5/S3/Arith/Covering/CoupledSevenBudgetRefutation
   generality: I
   mirror-B: D5/B/S3/Arith/Covering/CoupledSevenBudgetRefutation
   mirror-E: none(waiver:finite-certificate-no-numeric-artifact)
   anchors: [mathlib/module/Mathlib.Tactic]
   utility: kind=bounded-enumeration; basis=refutes=gid:D5/S3/Arith/Covering/CoupledSevenBudgetRefutation.claim; result=D5/S3/Arith/Covering/CoupledSevenBudgetRefutation.result; claim=D5/S3/Arith/Covering/CoupledSevenBudgetRefutation.claim
   digest: Two prime-palette envelopes with a shared seven axis cannot both reach one under their joint real allocation constraints. -/

import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.Covering.CoupledSevenBudgetRefutation

open scoped BigOperators

/-- The ordinary primes available to the first of the two envelopes. -/
def smallPalette : Finset ℕ := {5, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43}

/-- The additional ordinary primes available only to the second envelope. -/
def tailPalette : Finset ℕ := {47, 53, 59, 61, 67, 71}

def otherPalette (A : Finset ℕ) : Finset ℕ := (smallPalette \ A) ∪ tailPalette

def ordinaryWeight (p : ℕ) : ℚ := 1 / ((p : ℚ) - 3)

def ordinaryProduct (A : Finset ℕ) : ℚ := ∏ p ∈ A, (1 + ordinaryWeight p)

def budget (κ b : ℚ) (A : Finset ℕ) : ℚ :=
  (2 + κ) * ((1 + b) * ordinaryProduct A - 1) -
    2 * (b + ∑ p ∈ A, ordinaryWeight p)

def gain (κ : ℚ) (A : Finset ℕ) : ℚ := (2 + κ) * (ordinaryProduct A - 1)

def rawDemand (κ : ℚ) (A : Finset ℕ) (t : ℚ) : ℚ :=
  ((1 - budget κ 0 A) * (5 - t) - gain κ A) / κ

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- Kernel evaluation checks all 2048 subsets of the ordinary-prime palette.
/-- A finite obstruction: either a coarse bound fails, or both affine endpoints
require more than the entire second allocation pool. -/
theorem partition_obstruction :
    ∀ A : Finset ℕ, A ⊆ smallPalette →
      (budget (1 / 2) (1 / 4) A < 1 ∨
        budget (1 / 3) (1 / 4) (otherPalette A) < 1) ∨
      (1 < rawDemand (1 / 2) A 0 + rawDemand (1 / 3) (otherPalette A) 1) ∧
        (1 < rawDemand (1 / 2) A 1 + rawDemand (1 / 3) (otherPalette A) 0) := by
  decide +kernel

/-- The allocations are real; only the palette coefficients are rational. -/
noncomputable def envelope (κ : ℚ) (A : Finset ℕ) (t v : ℝ) : ℝ :=
  (budget κ 0 A : ℝ) + ((gain κ A : ℝ) + (κ : ℝ) * v) / (5 - t)

noncomputable def demand (κ : ℚ) (A : Finset ℕ) (t : ℝ) : ℝ :=
  ((1 - (budget κ 0 A : ℝ)) * (5 - t) - (gain κ A : ℝ)) / (κ : ℝ)

/-- Both necessary envelopes can reach one with two independent unit pools. -/
def claim : Prop :=
  ∃ A : Finset ℕ, A ⊆ smallPalette ∧
    ∃ t0 t1 v0 v1 : ℝ,
      0 ≤ t0 ∧ 0 ≤ t1 ∧ 0 ≤ v0 ∧ 0 ≤ v1 ∧
      t0 + t1 ≤ 1 ∧ v0 + v1 ≤ 1 ∧
      1 ≤ envelope (1 / 2) A t0 v0 ∧
      1 ≤ envelope (1 / 3) (otherPalette A) t1 v1

private theorem palette_prime_ge_five {p : ℕ}
    (hp : p ∈ smallPalette ∪ tailPalette) : 5 ≤ p := by
  simp only [smallPalette, tailPalette, Finset.mem_union, Finset.mem_insert,
    Finset.mem_singleton] at hp
  omega

private theorem gain_nonneg (κ : ℚ) (A : Finset ℕ)
    (hκ : 0 ≤ κ) (hA : A ⊆ smallPalette ∪ tailPalette) : 0 ≤ gain κ A := by
  have hP : 1 ≤ ordinaryProduct A := by
    apply Finset.one_le_prod
    intro p hp
    have hpQ : (5 : ℚ) ≤ p := by exact_mod_cast palette_prime_ge_five (hA hp)
    have hw : 0 ≤ ordinaryWeight p := div_nonneg (by norm_num) (by linarith)
    linarith
  exact mul_nonneg (by linarith) (sub_nonneg.mpr hP)

private theorem coarse_budget_eq (κ : ℚ) (A : Finset ℕ) :
    budget κ (1 / 4) A = budget κ 0 A + (gain κ A + κ) / 4 := by
  unfold budget gain
  ring

private theorem envelope_le_coarse (κ : ℚ) (A : Finset ℕ)
    (hκ : 0 ≤ κ) (hG : 0 ≤ gain κ A)
    (t v : ℝ) (ht : t ≤ 1) (hv1 : v ≤ 1) :
    envelope κ A t v ≤ (budget κ (1 / 4) A : ℝ) := by
  rw [coarse_budget_eq]
  push_cast
  unfold envelope
  apply add_le_add le_rfl
  have hk : (0 : ℝ) ≤ (κ : ℝ) := by exact_mod_cast hκ
  have hg : (0 : ℝ) ≤ (gain κ A : ℝ) := by exact_mod_cast hG
  apply (div_le_div_iff₀ (by linarith : (0 : ℝ) < 5 - t)
    (by norm_num : (0 : ℝ) < 4)).2
  have hkv : (κ : ℝ) * v ≤ (κ : ℝ) := by
    simpa using mul_le_mul_of_nonneg_left hv1 hk
  have hden := mul_le_mul_of_nonneg_left (show (4 : ℝ) ≤ 5 - t by linarith)
    (show (0 : ℝ) ≤ (gain κ A : ℝ) + (κ : ℝ) by linarith)
  nlinarith

private theorem envelope_mono_t (κ : ℚ) (A : Finset ℕ)
    (hκ : 0 ≤ κ) (hG : 0 ≤ gain κ A)
    (v : ℝ) (hv : 0 ≤ v) (t u : ℝ) (htu : t ≤ u) (hu : u ≤ 1) :
    envelope κ A t v ≤ envelope κ A u v := by
  unfold envelope
  apply add_le_add le_rfl
  apply div_le_div_of_nonneg_left
  · exact add_nonneg (by exact_mod_cast hG)
      (mul_nonneg (by exact_mod_cast hκ) hv)
  · linarith
  · linarith

private theorem demand_le_of_budget (κ : ℚ) (A : Finset ℕ) (hκ : 0 < κ)
    (t v : ℝ) (ht : t ≤ 1) (hbudget : 1 ≤ envelope κ A t v) :
    demand κ A t ≤ v := by
  have hk : (0 : ℝ) < (κ : ℝ) := by exact_mod_cast hκ
  have hd : (0 : ℝ) < 5 - t := by linarith
  have hh : 1 - (budget κ 0 A : ℝ) ≤
      ((gain κ A : ℝ) + (κ : ℝ) * v) / (5 - t) := by
    unfold envelope at hbudget
    linarith
  have hm := (le_div_iff₀ hd).mp hh
  unfold demand
  apply (div_le_iff₀ hk).2
  nlinarith

private theorem cast_rawDemand (κ : ℚ) (A : Finset ℕ) (t : ℚ) :
    (rawDemand κ A t : ℝ) = demand κ A (t : ℝ) := by
  unfold rawDemand demand
  push_cast
  rfl

private theorem demand_sum_gt_one (A B : Finset ℕ) (t : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hzero : 1 < rawDemand (1 / 2) A 0 + rawDemand (1 / 3) B 1)
    (hone : 1 < rawDemand (1 / 2) A 1 + rawDemand (1 / 3) B 0) :
    1 < demand (1 / 2) A t + demand (1 / 3) B (1 - t) := by
  have hz : (1 : ℝ) < demand (1 / 2) A 0 + demand (1 / 3) B 1 := by
    have hc : (1 : ℝ) <
        (rawDemand (1 / 2) A 0 : ℝ) + (rawDemand (1 / 3) B 1 : ℝ) := by
      exact_mod_cast hzero
    simpa only [cast_rawDemand, Rat.cast_zero, Rat.cast_one] using hc
  have ho : (1 : ℝ) < demand (1 / 2) A 1 + demand (1 / 3) B 0 := by
    have hc : (1 : ℝ) <
        (rawDemand (1 / 2) A 1 : ℝ) + (rawDemand (1 / 3) B 0 : ℝ) := by
      exact_mod_cast hone
    simpa only [cast_rawDemand, Rat.cast_zero, Rat.cast_one] using hc
  have ha : demand (1 / 2) A t + demand (1 / 3) B (1 - t) =
      (1 - t) * (demand (1 / 2) A 0 + demand (1 / 3) B 1) +
      t * (demand (1 / 2) A 1 + demand (1 / 3) B 0) := by
    unfold demand
    ring
  rw [ha]
  have hp0 := mul_nonneg (show 0 ≤ 1 - t by linarith)
    (sub_nonneg.mpr hz.le)
  have hp1 := mul_nonneg ht0 (sub_nonneg.mpr ho.le)
  by_cases ht : t = 0
  · simpa [ht] using hz
  · have hp := mul_pos ((lt_or_eq_of_le ht0).resolve_right (Ne.symm ht))
      (sub_pos.mpr ho)
    nlinarith

/-- No real allocation and ordinary-prime partition satisfies both budgets. -/
theorem result : ¬ claim := by
  rintro ⟨A, hA, t0, t1, v0, v1, ht0, ht1, hv0, hv1, htotal, vtotal,
    hbudget0, hbudget1⟩
  have hg0 : 0 ≤ gain (1 / 2) A := gain_nonneg _ _ (by norm_num) (by
    intro p hp
    exact Finset.mem_union.mpr (Or.inl (hA hp)))
  have hg1 : 0 ≤ gain (1 / 3) (otherPalette A) := gain_nonneg _ _ (by norm_num) (by
    intro p hp
    rcases Finset.mem_union.mp hp with hs | hs
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_sdiff.mp hs).1)
    · exact Finset.mem_union.mpr (Or.inr hs))
  rcases partition_obstruction A hA with hcoarse | hdual
  · rcases hcoarse with hleft | hright
    · have hupper := envelope_le_coarse (1 / 2) A (by norm_num) hg0
        t0 v0 (by linarith) (by linarith)
      have hh : (budget (1 / 2) (1 / 4) A : ℝ) < 1 := by exact_mod_cast hleft
      linarith
    · have hupper := envelope_le_coarse (1 / 3) (otherPalette A) (by norm_num) hg1
        t1 v1 (by linarith) (by linarith)
      have hh : (budget (1 / 3) (1 / 4) (otherPalette A) : ℝ) < 1 := by
        exact_mod_cast hright
      linarith
  · have hsaturate := envelope_mono_t (1 / 3) (otherPalette A) (by norm_num) hg1
      v1 hv1 t1 (1 - t0) (by linarith) (by linarith)
    have hr0 := demand_le_of_budget (1 / 2) A (by norm_num)
      t0 v0 (by linarith) hbudget0
    have hr1 := demand_le_of_budget (1 / 3) (otherPalette A) (by norm_num)
      (1 - t0) v1 (by linarith) (hbudget1.trans hsaturate)
    have hstrict := demand_sum_gt_one A (otherPalette A) t0 ht0 (by linarith)
      hdual.1 hdual.2
    linarith

end D5.S3.Arith.Covering.CoupledSevenBudgetRefutation
