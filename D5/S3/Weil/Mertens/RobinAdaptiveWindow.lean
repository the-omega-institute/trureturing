/- GID: D5/S3/Weil/Mertens/RobinAdaptiveWindow
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/RobinAdaptiveWindow
   mirror-E: none(waiver:analytic-integral-estimate)
   anchors: []
   utility: none
   digest: Bounded-error sampling of the actual Robin mass on whole windows. -/

import D5.S3.Weil.Mertens.RobinFiniteMesh
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Partition a window into doubling blocks, clipping the final block at its
right endpoint. Scale each mesh so that both its sampling error and its share
of the sample count are controlled by a summable geometric weight. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Weil.Mertens.RobinAdaptiveWindow

open Filter MeasureTheory Real Set
open Finset (range)
open scoped Topology
open D5.S3.Arith.Robin.CompleteMertensPeak (psiErrorKernel complete_mertens_ledger)
open D5.S3.Weil.Mertens.RobinFiniteMesh (chordMass abs_mass_sub_mesh_le_nine_mul_sq)
open D5.S3.Weil.Mertens.RobinWeightedRamp (R u)
open D5.S3.Weil.Mertens.WeightedTailTransport (weightedTail)
open D5.S3.Weil.Mertens.WeightedTailWindowMass (weightedNegativeMass)

noncomputable section

/-- The number of nonempty blocks is the ceiling of `log (B / A) / log 2`. -/
def blockCount (A B : ℝ) : ℕ := ⌈logb 2 (B / A)⌉₊

/-- The endpoints of the blocks, constant at the right endpoint after the last block. -/
def blockEnd (A B : ℝ) (j : ℕ) : ℝ := min B (A * (2 : ℝ) ^ j)

private def meshScale (B a : ℝ) : ℝ := (a / B) ^ (1 / 12 : ℝ)

def stepBound (B a : ℝ) : ℝ := meshScale B a * a ^ (3 / 4 : ℝ)

def cellCount (A B : ℝ) (j : ℕ) : ℕ :=
  ⌈(blockEnd A B (j + 1) - blockEnd A B j) / stepBound B (blockEnd A B j)⌉₊

/-- Equal spacing in the ordinary real coordinate within a block. -/
def meshPoint (A B : ℝ) (j i : ℕ) : ℝ :=
  blockEnd A B j + (i : ℝ) *
    ((blockEnd A B (j + 1) - blockEnd A B j) / (cellCount A B j : ℝ))

private def blockPoints (A B : ℝ) (j : ℕ) : Finset ℝ := by
  classical
  exact (range (cellCount A B j)).image (meshPoint A B j)

/-- Each block contributes its left and interior nodes. The terminal node is inserted once. -/
def samplePoints (A B : ℝ) : Finset ℝ := by
  classical
  exact insert B ((range (blockCount A B)).biUnion (blockPoints A B))

/-- Integrate the positive part of each signed chord through the actual Robin samples. -/
def windowChordSum (A B : ℝ) : ℝ :=
  ∑ j ∈ range (blockCount A B), ∑ i ∈ range (cellCount A B j),
    chordMass (meshPoint A B j i) (meshPoint A B j (i + 1))

def geometricConstant : ℝ := 1 / (1 - (2 : ℝ) ^ (-(1 / 6) : ℝ))

private theorem one_lt_of_exp_one_le {A : ℝ} (hA : exp 1 ≤ A) : 1 < A :=
  (Real.one_lt_exp_iff.mpr zero_lt_one).trans_le hA

private theorem blockEnd_zero {A B : ℝ} (hAB : A ≤ B) : blockEnd A B 0 = A := by
  simp [blockEnd, min_eq_right hAB]

private theorem blockEnd_mono {A B : ℝ} (hA : 0 ≤ A) : Monotone (blockEnd A B) := by
  intro i j hij
  change min B (A * (2 : ℝ) ^ i) ≤ min B (A * (2 : ℝ) ^ j)
  have hpow := mul_le_mul_of_nonneg_left
    (pow_right_mono₀ (by norm_num : (1 : ℝ) ≤ 2) hij) hA
  exact le_min (min_le_left _ _) ((min_le_right _ _).trans hpow)

private theorem blockEnd_last {A B : ℝ} (hA : 0 < A) (hAB : A ≤ B) :
    blockEnd A B (blockCount A B) = B := by
  have hB := hA.trans_le hAB
  have hlog : logb 2 (B / A) ≤ (blockCount A B : ℝ) := Nat.le_ceil _
  have hpow := (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 2)
    (div_pos hB hA)).mp hlog
  rw [Real.rpow_natCast] at hpow
  exact min_eq_left (by simpa only [mul_comm] using (div_le_iff₀ hA).mp hpow)

private theorem rawBlock_lt {A B : ℝ} (hA : 0 < A) (hAB : A ≤ B)
    {j : ℕ} (hj : j < blockCount A B) : A * (2 : ℝ) ^ j < B := by
  have hlog : (j : ℝ) < logb 2 (B / A) := Nat.lt_ceil.mp hj
  have hpow := (Real.lt_logb_iff_rpow_lt (by norm_num : (1 : ℝ) < 2)
    (div_pos (hA.trans_le hAB) hA)).mp hlog
  rw [Real.rpow_natCast] at hpow
  simpa only [mul_comm] using (lt_div_iff₀ hA).mp hpow

/-- Every used block has a strict left endpoint and ends at its double or at the window end. -/
private theorem blockEnd_succ {A B : ℝ} (hA : 0 < A) (hAB : A ≤ B)
    {j : ℕ} (hj : j < blockCount A B) :
    blockEnd A B j < blockEnd A B (j + 1) ∧
      blockEnd A B (j + 1) = min B (2 * blockEnd A B j) := by
  have hraw := rawBlock_lt hA hAB hj
  have hraw0 : 0 < A * (2 : ℝ) ^ j := by positivity
  have hleft : blockEnd A B j = A * (2 : ℝ) ^ j := min_eq_right hraw.le
  have hright : blockEnd A B (j + 1) = min B (2 * blockEnd A B j) := by
    rw [hleft]
    change min B (A * (2 : ℝ) ^ (j + 1)) = min B (2 * (A * (2 : ℝ) ^ j))
    rw [pow_succ]
    congr 1
    ring
  refine ⟨?_, hright⟩
  rw [hright, lt_min_iff, hleft]
  exact ⟨hraw, by linarith⟩

private theorem stepBound_pos {B a : ℝ} (hB : 0 < B) (ha : 0 < a) :
    0 < stepBound B a := by
  unfold stepBound meshScale
  exact mul_pos (rpow_pos_of_pos (div_pos ha hB) _) (rpow_pos_of_pos ha _)

private theorem equalMesh {a b h : ℝ} (hab : a < b) (hh : 0 < h) :
    let N := ⌈(b - a) / h⌉₊
    let x := fun i : ℕ => a + (i : ℝ) * ((b - a) / (N : ℝ))
    0 < N ∧ x 0 = a ∧ x N = b ∧ StrictMono x ∧
      (∀ i : ℕ, x (i + 1) - x i ≤ h) ∧ (N : ℝ) ≤ (b - a) / h + 1 := by
  dsimp only
  let N := ⌈(b - a) / h⌉₊
  have hd : 0 < b - a := sub_pos.mpr hab
  have hratio : 0 < (b - a) / h := div_pos hd hh
  have hN : 0 < N := Nat.ceil_pos.mpr hratio
  have hN' : 0 < (N : ℝ) := by exact_mod_cast hN
  have hstep : (b - a) / (N : ℝ) ≤ h := by
    have hceil : (b - a) / h ≤ (N : ℝ) := Nat.le_ceil _
    apply (div_le_iff₀ hN').mpr
    simpa only [mul_comm] using (div_le_iff₀ hh).mp hceil
  have hstep0 : 0 < (b - a) / (N : ℝ) := div_pos hd hN'
  refine ⟨hN, by simp, ?_, ?_, ?_, (Nat.ceil_lt_add_one hratio.le).le⟩
  · change a + (N : ℝ) * ((b - a) / (N : ℝ)) = b
    field_simp [hN'.ne'] <;> ring
  · intro i k hik
    have hik' : (i : ℝ) < (k : ℝ) := by exact_mod_cast hik
    exact add_lt_add_right (mul_lt_mul_of_pos_right hik' hstep0) a
  · intro i
    calc
      _ = (b - a) / (N : ℝ) := by push_cast; ring
      _ ≤ h := hstep

private theorem meshPoint_spec {A B : ℝ} (hA : 0 < A) (hAB : A ≤ B)
    {j : ℕ} (hj : j < blockCount A B) :
    0 < cellCount A B j ∧
      meshPoint A B j 0 = blockEnd A B j ∧
      meshPoint A B j (cellCount A B j) = blockEnd A B (j + 1) ∧
      StrictMono (meshPoint A B j) ∧
      (∀ i : ℕ, meshPoint A B j (i + 1) - meshPoint A B j i ≤
        stepBound B (blockEnd A B j)) ∧
      (cellCount A B j : ℝ) ≤
        (blockEnd A B (j + 1) - blockEnd A B j) / stepBound B (blockEnd A B j) + 1 := by
  have hleft : A ≤ blockEnd A B j :=
    (blockEnd_zero hAB).symm.le.trans (blockEnd_mono hA.le (Nat.zero_le j))
  exact equalMesh (blockEnd_succ hA hAB hj).1
    (stepBound_pos (hA.trans_le hAB) (hA.trans_le hleft))

/-- A zero-length window has an empty chord sum and its endpoint as the sole sample. -/
theorem degenerate_window (A : ℝ) (hA : 0 < A) :
    blockCount A A = 0 ∧ windowChordSum A A = 0 ∧ samplePoints A A = {A} := by
  classical
  have hm : blockCount A A = 0 := by
    simp [blockCount, div_self hA.ne', Real.logb_one]
  exact ⟨hm, by simp [windowChordSum, hm], by simp [samplePoints, hm]⟩

private theorem blockPoints_subset {A B : ℝ} (hA : 0 < A) (hAB : A ≤ B)
    {j : ℕ} (hj : j < blockCount A B) {x : ℝ} (hx : x ∈ blockPoints A B j) :
    blockEnd A B j ≤ x ∧ x < blockEnd A B (j + 1) := by
  classical
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨_, hzero, hlast, hmono, _, _⟩ := meshPoint_spec hA hAB hj
  refine ⟨?_, ?_⟩
  · simpa only [hzero] using hmono.monotone (Nat.zero_le i)
  · simpa only [hlast] using hmono (Finset.mem_range.mp hi)

/-- The two nodes of every chord are among the samples. A shared block endpoint
is supplied by the following block, or by the terminal node. -/
private theorem meshPoint_mem_samplePoints {A B : ℝ} (hA : 0 < A) (hAB : A ≤ B)
    {j i : ℕ} (hj : j < blockCount A B) (hi : i ≤ cellCount A B j) :
    meshPoint A B j i ∈ samplePoints A B := by
  classical
  have insertBlock {k l : ℕ} (hk : k < blockCount A B) (hl : l < cellCount A B k) :
      meshPoint A B k l ∈ samplePoints A B :=
    Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr
      ⟨k, Finset.mem_range.mpr hk, Finset.mem_image_of_mem _ (Finset.mem_range.mpr hl)⟩)
  rcases lt_or_eq_of_le hi with hil | rfl
  · exact insertBlock hj hil
  · rw [(meshPoint_spec hA hAB hj).2.2.1]
    rcases lt_or_eq_of_le (Nat.succ_le_iff.mpr hj) with hnext | hlast
    · obtain ⟨hN, hzero, _, _, _, _⟩ := meshPoint_spec hA hAB hnext
      rw [← hzero]
      exact insertBlock hnext hN
    · rw [show j + 1 = blockCount A B from hlast, blockEnd_last hA hAB]
      exact Finset.mem_insert_self _ _

/-- Shared block endpoints are counted once, so the number of distinct samples
is exactly the number of cells plus one. -/
private theorem samplePoints_card {A B : ℝ} (hA : 0 < A) (hAB : A ≤ B) :
    (samplePoints A B).card = (∑ j ∈ range (blockCount A B), cellCount A B j) + 1 := by
  classical
  have mono := blockEnd_mono (B := B) hA.le
  have hterminal : B ∉ (range (blockCount A B)).biUnion (blockPoints A B) := by
    intro h
    obtain ⟨j, hj, hx⟩ := Finset.mem_biUnion.mp h
    have hup := (blockPoints_subset hA hAB (Finset.mem_range.mp hj) hx).2
    exact (not_lt_of_ge (min_le_left B _)) hup
  have hordered {i j : ℕ} (hi : i < blockCount A B) (hj : j < blockCount A B)
      (hij : i < j) : Disjoint (blockPoints A B i) (blockPoints A B j) := by
    apply Finset.disjoint_left.mpr
    intro x hxi hxj
    have hup := (blockPoints_subset hA hAB hi hxi).2
    have hlo := (blockPoints_subset hA hAB hj hxj).1
    exact (not_lt_of_ge ((mono (Nat.succ_le_iff.mpr hij)).trans hlo)) hup
  have hdisjoint : ((range (blockCount A B) : Finset ℕ) : Set ℕ).PairwiseDisjoint
      (blockPoints A B) := by
    intro i hi j hj hij
    have hi' := Finset.mem_range.mp (Finset.mem_coe.mp hi)
    have hj' := Finset.mem_range.mp (Finset.mem_coe.mp hj)
    rcases lt_or_gt_of_ne hij with h | h
    · exact hordered hi' hj' h
    · exact (hordered hj' hi' h).symm
  rw [samplePoints, Finset.card_insert_of_notMem hterminal, Finset.card_biUnion hdisjoint]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [blockPoints, Finset.card_image_of_injOn
    (meshPoint_spec hA hAB (Finset.mem_range.mp hj)).2.2.2.1.injective.injOn, Finset.card_range]

private theorem geometricConstant_nonneg : 0 ≤ geometricConstant := by
  have hq : (2 : ℝ) ^ (-(1 / 6) : ℝ) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  exact one_div_nonneg.mpr (sub_nonneg.mpr hq.le)

private theorem sum_blockWeights_le {A B : ℝ} (hA : 0 < A) (hAB : A ≤ B) :
    (∑ j ∈ range (blockCount A B), (blockEnd A B j / B) ^ (1 / 6 : ℝ)) ≤
      geometricConstant := by
  let m := blockCount A B
  let q : ℝ := (2 : ℝ) ^ (-(1 / 6) : ℝ)
  let w (j : ℕ) : ℝ := (A * (2 : ℝ) ^ j / B) ^ (1 / 6 : ℝ)
  have hB := hA.trans_le hAB
  have hq : 0 < q := Real.rpow_pos_of_pos (by norm_num) _
  have hq1 : q < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  have hrec (j : ℕ) : q * w (j + 1) = w j := by
    have hbase : 0 ≤ A * (2 : ℝ) ^ j / B := by positivity
    have htwo : 0 < (2 : ℝ) ^ (1 / 6 : ℝ) := rpow_pos_of_pos (by norm_num) _
    dsimp only [q, w]
    rw [pow_succ, show A * ((2 : ℝ) ^ j * 2) / B =
      (A * (2 : ℝ) ^ j / B) * 2 by ring,
      Real.mul_rpow hbase (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    field_simp [htwo.ne']
  have hsum : (∑ j ∈ range m, (blockEnd A B j / B) ^ (1 / 6 : ℝ)) =
      ∑ j ∈ range m, w j := by
    apply Finset.sum_congr rfl
    intro j hj
    have hj' : j < blockCount A B := Finset.mem_range.mp hj
    rw [blockEnd, min_eq_right (rawBlock_lt hA hAB hj').le]
  rw [hsum]
  by_cases hm : m = 0
  · simpa only [hm, Finset.range_zero, Finset.sum_empty] using geometricConstant_nonneg
  have hlast : m - 1 < blockCount A B := by
    change m - 1 < m
    omega
  have hsucc : m - 1 + 1 = m := by omega
  have htop : q * w m ≤ 1 := by
    rw [← hsucc, hrec]
    have hdiv : A * (2 : ℝ) ^ (m - 1) / B ≤ 1 := by
      exact (div_le_iff₀ hB).mpr (by simpa only [one_mul] using (rawBlock_lt hA hAB hlast).le)
    simpa only [w, Real.one_rpow] using
      (Real.rpow_le_rpow (by positivity : 0 ≤ A * (2 : ℝ) ^ (m - 1) / B)
        hdiv (by norm_num : (0 : ℝ) ≤ 1 / 6))
  have hstart : 0 ≤ q * w 0 := mul_nonneg hq.le (by dsimp only [w]; positivity)
  have htel : (∑ j ∈ range m, (w j - q * w j)) = q * w m - q * w 0 := by
    simpa only [hrec] using (Finset.sum_range_sub (fun j => q * w j) m)
  have hbudget : (1 - q) * (∑ j ∈ range m, w j) ≤ 1 := calc
    _ = ∑ j ∈ range m, (w j - q * w j) := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
      ring
    _ = q * w m - q * w 0 := htel
    _ ≤ 1 := by linarith only [htop, hstart]
  change (∑ j ∈ range m, w j) ≤ 1 / (1 - q)
  apply (le_div_iff₀ (sub_pos.mpr hq1)).mpr
  simpa only [mul_comm] using hbudget

private theorem stepBound_eq {a B : ℝ} (ha : 0 < a) (hB : 0 < B) :
    stepBound B a = a ^ (5 / 6 : ℝ) / B ^ (1 / 12 : ℝ) := by
  rw [stepBound, meshScale, Real.div_rpow ha.le hB.le,
    show (5 / 6 : ℝ) = 1 / 12 + 3 / 4 by norm_num, Real.rpow_add ha]
  ring

private theorem div_stepBound {a B : ℝ} (ha : 0 < a) (hB : 0 < B) :
    a / stepBound B a = B ^ (1 / 4 : ℝ) * (a / B) ^ (1 / 6 : ℝ) := by
  have ha' : 0 < a ^ (5 / 6 : ℝ) := rpow_pos_of_pos ha _
  have hB' : 0 < B ^ (1 / 6 : ℝ) := rpow_pos_of_pos hB _
  have hB'' : 0 < B ^ (1 / 12 : ℝ) := rpow_pos_of_pos hB _
  have ha_split : a = a ^ (5 / 6 : ℝ) * a ^ (1 / 6 : ℝ) := by
    rw [← Real.rpow_add ha, show (5 / 6 : ℝ) + 1 / 6 = 1 by norm_num, Real.rpow_one]
  have hB_split : B ^ (1 / 4 : ℝ) = B ^ (1 / 12 : ℝ) * B ^ (1 / 6 : ℝ) := by
    rw [← Real.rpow_add hB, show (1 / 12 : ℝ) + 1 / 6 = 1 / 4 by norm_num]
  calc
    a / stepBound B a = B ^ (1 / 12 : ℝ) * a ^ (1 / 6 : ℝ) := by
      calc
        _ = (a ^ (5 / 6 : ℝ) * a ^ (1 / 6 : ℝ)) /
            (a ^ (5 / 6 : ℝ) / B ^ (1 / 12 : ℝ)) :=
          congrArg₂ (· / ·) ha_split (stepBound_eq ha hB)
        _ = _ := by
          field_simp [ha'.ne', hB''.ne']
    _ = _ := by
      rw [Real.div_rpow ha.le hB.le, hB_split]
      field_simp [hB'.ne']

private theorem one_le_div_stepBound {a B : ℝ} (ha : 1 ≤ a) (hB : 1 ≤ B) :
    1 ≤ a / stepBound B a := by
  have hB0 := zero_lt_one.trans_le hB
  have ha0 := zero_lt_one.trans_le ha
  have hden : 0 < B ^ (1 / 12 : ℝ) := rpow_pos_of_pos hB0 _
  have hBpow : 1 ≤ B ^ (1 / 12 : ℝ) := Real.one_le_rpow hB (by norm_num)
  have hpow : a ^ (5 / 6 : ℝ) ≤ a := by
    simpa only [Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_le ha (show (5 / 6 : ℝ) ≤ 1 by norm_num))
  apply (le_div_iff₀ (stepBound_pos hB0 ha0)).mpr
  rw [one_mul, stepBound_eq ha0 hB0, div_le_iff₀ hden]
  exact hpow.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hBpow ha0.le)

private theorem cellCount_le {A B : ℝ} (hA : 0 < A) (hAB : A ≤ B)
    {j : ℕ} (hj : j < blockCount A B) :
    (cellCount A B j : ℝ) ≤
      B ^ (1 / 4 : ℝ) * (blockEnd A B j / B) ^ (1 / 6 : ℝ) + 1 := by
  have hleft : A ≤ blockEnd A B j :=
    (blockEnd_zero hAB).symm.le.trans (blockEnd_mono hA.le (Nat.zero_le j))
  have ha := hA.trans_le hleft
  have hB := hA.trans_le hAB
  have hright : blockEnd A B (j + 1) ≤ 2 * blockEnd A B j := by
    rw [(blockEnd_succ hA hAB hj).2]
    exact min_le_right _ _
  calc
    _ ≤ (blockEnd A B (j + 1) - blockEnd A B j) / stepBound B (blockEnd A B j) + 1 :=
      (meshPoint_spec hA hAB hj).2.2.2.2.2
    _ ≤ blockEnd A B j / stepBound B (blockEnd A B j) + 1 :=
      add_le_add_left (div_le_div_of_nonneg_right (by linarith only [hright])
        (stepBound_pos hB ha).le) 1
    _ = _ := by rw [div_stepBound ha hB]

/-- Additivity for the actual weighted negative mass on ordered adjacent blocks. -/
private theorem sum_blockMass {A B : ℝ} (hA : exp 1 ≤ A) (hAB : A ≤ B) :
    (∑ j ∈ range (blockCount A B),
      weightedNegativeMass psiErrorKernel (blockEnd A B j) (blockEnd A B (j + 1))) =
      weightedNegativeMass psiErrorKernel A B := by
  have hA0 : 0 < A := (exp_pos 1).trans_le hA
  have hA2 : 2 ≤ A := Real.exp_one_gt_two.le.trans hA
  let f (t : ℝ) := (WeightedTailInverse.a t / sqrt t) * max (-weightedTail psiErrorKernel t) 0
  have hf : ContinuousOn f (Icc A B) := by
    have hlog : ContinuousOn log (Icc A B) := fun _ ht =>
      (continuousAt_log (hA0.trans_le ht.1).ne').continuousWithinAt
    have hweight : ContinuousOn WeightedTailInverse.a (Icc A B) := by
      unfold WeightedTailInverse.a
      exact (hlog.pow 2).div (hlog.const_add 1) (fun t ht => by
        have ht1 : 1 < t := (one_lt_of_exp_one_le hA).trans_le ht.1
        have htlog := log_pos ht1
        exact ne_of_gt (by positivity))
    have htail : ContinuousOn (weightedTail psiErrorKernel) (Icc A B) :=
      (complete_mertens_ledger hA2).2.1.continuousOn_Ici_primitive_Ioi.mono (fun _ ht => ht.1)
    exact (hweight.div continuous_sqrt.continuousOn
      (fun _ ht => (sqrt_pos.2 (hA0.trans_le ht.1)).ne')).mul
      (htail.neg.sup continuousOn_const)
  have hint (j : ℕ) (_ : j < blockCount A B) :
      IntervalIntegrable f volume (blockEnd A B j) (blockEnd A B (j + 1)) := by
    have hleft : A ≤ blockEnd A B j :=
      (blockEnd_zero hAB).symm.le.trans (blockEnd_mono hA0.le (Nat.zero_le j))
    have hright : blockEnd A B (j + 1) ≤ B := min_le_left _ _
    exact (hf.mono (Icc_subset_Icc hleft hright)).intervalIntegrable_of_Icc
      (blockEnd_mono hA0.le (Nat.le_succ j))
  simpa only [weightedNegativeMass, f, blockEnd_zero hAB, blockEnd_last hA0 hAB] using
    (intervalIntegral.sum_integral_adjacent_intervals hint)

private theorem block_error {A B : ℝ} (hA : exp 1 ≤ A) (hAB : A ≤ B)
    {j : ℕ} (hj : j < blockCount A B) :
    |weightedNegativeMass psiErrorKernel (blockEnd A B j) (blockEnd A B (j + 1)) -
      (∑ i ∈ range (cellCount A B j),
        chordMass (meshPoint A B j i) (meshPoint A B j (i + 1)))| ≤
      9 * (blockEnd A B j / B) ^ (1 / 6 : ℝ) := by
  have hA0 : 0 < A := (exp_pos 1).trans_le hA
  have hleft : A ≤ blockEnd A B j :=
    (blockEnd_zero hAB).symm.le.trans (blockEnd_mono hA0.le (Nat.zero_le j))
  have hright : blockEnd A B (j + 1) ≤ 2 * blockEnd A B j := by
    rw [(blockEnd_succ hA0 hAB hj).2]
    exact min_le_right _ _
  obtain ⟨_, hzero, hlast, hmono, hstep, _⟩ := meshPoint_spec hA0 hAB hj
  have hlocal := abs_mass_sub_mesh_le_nine_mul_sq
    (η := meshScale B (blockEnd A B j))
    (hA.trans hleft) hright hzero hlast (hmono.strictMonoOn _) (fun i _ => hstep i) le_rfl
  have hr : 0 ≤ blockEnd A B j / B :=
    div_nonneg (hA0.trans_le hleft).le (hA0.trans_le hAB).le
  simpa only [meshScale, ← Real.rpow_two, ← Real.rpow_mul hr,
    show (1 / 12 : ℝ) * 2 = 1 / 6 by norm_num] using hlocal

/-- The actual weighted negative mass of the entire window is determined up to
an absolute error by the sampled chords. The two count bounds include both
window endpoints and count each shared node once. -/
theorem window_sampling {A B : ℝ} (hA : exp 1 ≤ A) (hAB : A ≤ B) :
    |weightedNegativeMass psiErrorKernel A B - windowChordSum A B| ≤
      9 * geometricConstant ∧
    ((samplePoints A B).card : ℝ) ≤
      geometricConstant * B ^ (1 / 4 : ℝ) + (blockCount A B : ℝ) + 1 ∧
    ((samplePoints A B).card : ℝ) ≤ 2 * geometricConstant * B ^ (1 / 4 : ℝ) + 1 := by
  have hA0 : 0 < A := (exp_pos 1).trans_le hA
  have hB0 := hA0.trans_le hAB
  let m := blockCount A B
  let w (j : ℕ) : ℝ := (blockEnd A B j / B) ^ (1 / 6 : ℝ)
  let K : ℝ := B ^ (1 / 4 : ℝ)
  let M (j : ℕ) : ℝ :=
    weightedNegativeMass psiErrorKernel (blockEnd A B j) (blockEnd A B (j + 1))
  let P (j : ℕ) : ℝ := ∑ i ∈ range (cellCount A B j),
    chordMass (meshPoint A B j i) (meshPoint A B j (i + 1))
  have hK : 0 ≤ K := rpow_nonneg hB0.le _
  have hw : (∑ j ∈ range m, w j) ≤ geometricConstant := sum_blockWeights_le hA0 hAB
  have hcard : ((samplePoints A B).card : ℝ) =
      (∑ j ∈ range m, (cellCount A B j : ℝ)) + 1 := by
    rw [samplePoints_card hA0 hAB, Nat.cast_add, Nat.cast_one, Nat.cast_sum]
  have hweight (j : ℕ) : 1 ≤ K * w j := by
    have hleft : A ≤ blockEnd A B j :=
      (blockEnd_zero hAB).symm.le.trans (blockEnd_mono hA0.le (Nat.zero_le j))
    change 1 ≤ B ^ (1 / 4 : ℝ) * (blockEnd A B j / B) ^ (1 / 6 : ℝ)
    rw [← div_stepBound (hA0.trans_le hleft) hB0]
    exact one_le_div_stepBound ((one_lt_of_exp_one_le hA).le.trans hleft)
      ((one_lt_of_exp_one_le hA).le.trans hAB)
  refine ⟨?_, ?_, ?_⟩
  · change |weightedNegativeMass psiErrorKernel A B - (∑ j ∈ range m, P j)| ≤ _
    have hM : (∑ j ∈ range m, M j) = weightedNegativeMass psiErrorKernel A B :=
      sum_blockMass hA hAB
    rw [← hM, ← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ j ∈ range m, |M j - P j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ range m, 9 * w j :=
        Finset.sum_le_sum fun _ hj => block_error hA hAB (Finset.mem_range.mp hj)
      _ = 9 * (∑ j ∈ range m, w j) := (Finset.mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hw (by norm_num)
  · rw [hcard]
    calc
      _ ≤ (∑ j ∈ range m, (K * w j + 1)) + 1 := by
        exact add_le_add_left (Finset.sum_le_sum fun _ hj =>
          cellCount_le hA0 hAB (Finset.mem_range.mp hj)) 1
      _ = K * (∑ j ∈ range m, w j) + (m : ℝ) + 1 := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
          Finset.card_range, nsmul_eq_mul, mul_one]
      _ ≤ geometricConstant * K + (m : ℝ) + 1 := by
        simpa only [mul_comm K geometricConstant] using
          add_le_add_left (add_le_add_left (mul_le_mul_of_nonneg_left hw hK) (m : ℝ)) 1
  · rw [hcard]
    calc
      _ ≤ (∑ j ∈ range m, 2 * (K * w j)) + 1 := by
        apply add_le_add_left
        apply Finset.sum_le_sum
        intro j hj
        have hj' := Finset.mem_range.mp hj
        calc
          (cellCount A B j : ℝ) ≤ K * w j + 1 := cellCount_le hA0 hAB hj'
          _ ≤ 2 * (K * w j) := by linarith only [hweight j]
      _ = 2 * (K * (∑ j ∈ range m, w j)) + 1 := by simp only [Finset.mul_sum]
      _ ≤ 2 * geometricConstant * K + 1 := by
        have hbound := mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hw hK) (by norm_num : (0 : ℝ) ≤ 2)
        calc
          _ ≤ 2 * (K * geometricConstant) + 1 := add_le_add_left hbound 1
          _ = _ := by ring

/-- Every stored sample lies inside the requested window. -/
private theorem samplePoints_subset {A B : ℝ} (hA : 0 < A) (hAB : A ≤ B) :
    (samplePoints A B : Set ℝ) ⊆ Icc A B := by
  classical
  intro t ht
  change t ∈ samplePoints A B at ht
  rw [samplePoints, Finset.mem_insert] at ht
  rcases ht with rfl | ht
  · exact ⟨hAB, le_rfl⟩
  · obtain ⟨j, hj, ht⟩ := Finset.mem_biUnion.mp ht
    obtain ⟨hlo, hup⟩ := blockPoints_subset hA hAB (Finset.mem_range.mp hj) ht
    have hleft : A ≤ blockEnd A B j :=
      (blockEnd_zero hAB).symm.le.trans (blockEnd_mono hA.le (Nat.zero_le j))
    exact ⟨hleft.trans hlo, hup.le.trans (min_le_left _ _)⟩

/-- Evaluate each actual sample with the same finite Mangoldt cutoff. -/
theorem sample_value_eq_sum {A B x : ℝ} (hA : exp 1 ≤ A) (hAB : A ≤ B)
    (hx : x ∈ samplePoints A B) :
    R x = (∑ n ∈ Finset.Icc 2 ⌊B⌋₊, ArithmeticFunction.vonMangoldt n *
      max (u x / u (n : ℝ) - 1) 0) - u x * (log (log x) + eulerMascheroniConstant) + x := by
  have hAxB : x ∈ Icc A B := samplePoints_subset ((exp_pos 1).trans_le hA) hAB hx
  exact RobinWeightedRamp.ramp_eq_sum
    (Real.exp_one_gt_two.le.trans (hA.trans hAxB.1)) (Nat.floor_mono hAxB.2)

private def chordMassFrom (values : ℝ → ℝ) (a b : ℝ) : ℝ :=
  let q (t : ℝ) := (u t - u a) / (u b - u a)
  let H (t : ℝ) := (1 - q t) * values a + q t * values b
  ∫ t in a..b, (log t / (1 + log t)) / (t * sqrt t) * max (H t) 0

/-- The sampled chord sum can be evaluated from any extension of the sampled data. -/
private def windowChordSumFrom (values : ℝ → ℝ) (A B : ℝ) : ℝ :=
  ∑ j ∈ range (blockCount A B), ∑ i ∈ range (cellCount A B j),
    chordMassFrom values (meshPoint A B j i) (meshPoint A B j (i + 1))

private theorem windowChordSumFrom_eq {A B : ℝ} (hA : 0 < A) (hAB : A ≤ B)
    {values : ℝ → ℝ} (hvalues : EqOn values R (samplePoints A B : Set ℝ)) :
    windowChordSumFrom values A B = windowChordSum A B := by
  unfold windowChordSumFrom windowChordSum
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro i hi
  have hj' := Finset.mem_range.mp hj
  have hi' := Finset.mem_range.mp hi
  have hleft := hvalues (meshPoint_mem_samplePoints hA hAB hj' hi'.le)
  have hright := hvalues (meshPoint_mem_samplePoints hA hAB hj' (Nat.succ_le_iff.mpr hi'))
  simp only [chordMassFrom, chordMass, hleft, hright]

/-- On a power window the sample bounds have leading order `Y^(b/4)`. -/
private theorem power_window_sampling {Y b : ℝ} (hY : exp 1 ≤ Y) (hb : 1 ≤ b) :
    |weightedNegativeMass psiErrorKernel Y (Y ^ b) - windowChordSum Y (Y ^ b)| ≤
      9 * geometricConstant ∧
    ((samplePoints Y (Y ^ b)).card : ℝ) ≤
      geometricConstant * Y ^ (b / 4) + (blockCount Y (Y ^ b) : ℝ) + 1 ∧
    ((samplePoints Y (Y ^ b)).card : ℝ) ≤ 2 * geometricConstant * Y ^ (b / 4) + 1 := by
  have hY1 := (one_lt_of_exp_one_le hY).le
  have hscale : (Y ^ b) ^ (1 / 4 : ℝ) = Y ^ (b / 4) := by
    rw [← Real.rpow_mul (zero_le_one.trans hY1)]
    congr 1
    ring
  simpa only [hscale] using window_sampling hY (Real.self_le_rpow_of_one_le hY1 hb)

/-- The chord sum computed with a common inclusive Mangoldt cutoff at `⌊B⌋₊`. -/
def arithmeticWindowChordSum (A B : ℝ) : ℝ :=
  windowChordSumFrom (fun x =>
    (∑ n ∈ Finset.Icc 2 ⌊B⌋₊, ArithmeticFunction.vonMangoldt n *
      max (u x / u (n : ℝ) - 1) 0) - u x * (log (log x) + eulerMascheroniConstant) + x) A B

/-- The finite arithmetic chord sum is exact, and a cofinal subpower bound on it
transfers to the whole-window mass at the same outer exponent. -/
theorem arithmetic_window_sampling :
    (∀ {A B : ℝ}, exp 1 ≤ A → A ≤ B → arithmeticWindowChordSum A B = windowChordSum A B) ∧
    ∀ {b : ℝ}, 1 ≤ b →
    (∀ η : ℝ, 0 < η → ∃ᶠ Y : ℝ in atTop, arithmeticWindowChordSum Y (Y ^ b) ≤ Y ^ η) →
    ∀ η : ℝ, 0 < η → ∃ᶠ Y : ℝ in atTop, weightedNegativeMass psiErrorKernel Y (Y ^ b) ≤ Y ^ η := by
  have hexact {A B : ℝ} (hA : exp 1 ≤ A) (hAB : A ≤ B) :
      arithmeticWindowChordSum A B = windowChordSum A B :=
    windowChordSumFrom_eq ((exp_pos 1).trans_le hA) hAB
      (fun _ hx => (sample_value_eq_sum hA hAB hx).symm)
  refine ⟨@hexact, ?_⟩
  intro b hb hsamples η hη
  have hhalf : 0 < η / 2 := half_pos hη
  have hlarge : ∀ᶠ Y : ℝ in atTop, 9 * geometricConstant + 1 ≤ Y ^ (η / 2) :=
    (tendsto_rpow_atTop hhalf).eventually_ge_atTop _
  refine ((hsamples (η / 2) hhalf).and_eventually
    ((eventually_ge_atTop (exp 1)).and hlarge)).mono ?_
  intro Y hY
  obtain ⟨hsmall, hstart, hlargeY⟩ := hY
  have hY1 := (one_lt_of_exp_one_le hstart).le
  rw [hexact hstart (Real.self_le_rpow_of_one_le hY1 hb)] at hsmall
  have hpow1 : 1 ≤ Y ^ (η / 2) := Real.one_le_rpow hY1 hhalf.le
  have herror := (abs_le.mp (power_window_sampling hstart hb).1).2
  calc
    weightedNegativeMass psiErrorKernel Y (Y ^ b) ≤
        windowChordSum Y (Y ^ b) + 9 * geometricConstant := by linarith only [herror]
    _ ≤ Y ^ (η / 2) + 9 * geometricConstant := add_le_add_left hsmall _
    _ ≤ (9 * geometricConstant + 1) * Y ^ (η / 2) := by
      have h := mul_le_mul_of_nonneg_left hpow1
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 9) geometricConstant_nonneg)
      linarith only [h]
    _ ≤ Y ^ (η / 2) * Y ^ (η / 2) :=
      mul_le_mul_of_nonneg_right hlargeY (rpow_nonneg (zero_le_one.trans hY1) _)
    _ = _ := by
      rw [← Real.rpow_add (zero_lt_one.trans_le hY1),
        show η / 2 + η / 2 = η by ring]

end
end D5.S3.Weil.Mertens.RobinAdaptiveWindow
