/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/SubstochasticEscape
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/SubstochasticEscape
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A strict substochastic escape block makes the real resolvent nonsingular. -/
/-
Copyright 2026 Hugh Zheng
Released under Apache 2.0; see docs/reports/licenses/aldous-broder-substochastic.md.
Source: YuZh98/aldous-broder-lean, bd20382923d987fc54a9773e04a4bc22b851872c,
EAB/Paper/ConfinedChain.lean, SHA256
 d235b9788731933c6f9b315b164ed71859748ca44658eef3cf033acfefbb8fba.
The live substochastic dependency slice retains upstream statements and proofs.
Imports and the owning namespace are adapted to the pinned repository.
Retire this port when this repository's pinned Mathlib supplies equivalent declarations;
replace each live use with the matching pinned supplier.
-/
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Data.Matrix.Mul
import Mathlib.Topology.Instances.Matrix

open Finset Matrix Filter Topology
namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.SubstochasticEscape

section Substochastic

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A nonnegative matrix whose row sums are at most one. -/
structure IsSubstochastic (A : Matrix ι ι ℝ) : Prop where
  nonneg : ∀ i j, 0 ≤ A i j
  row_le : ∀ i, ∑ j, A i j ≤ 1

/-- The row sum at `i` of the `t`-th power. -/
def rowSum (A : Matrix ι ι ℝ) (t : ℕ) (i : ι) : ℝ :=
  ∑ j, (A ^ t) i j

variable {A : Matrix ι ι ℝ}

theorem IsSubstochastic.pow_nonneg (hA : IsSubstochastic A) (t : ℕ)
    (i j : ι) : 0 ≤ (A ^ t) i j :=
  Matrix.pow_apply_nonneg hA.nonneg t i j

theorem rowSum_zero (A : Matrix ι ι ℝ) (i : ι) : rowSum A 0 i = 1 := by
  simp [rowSum, Matrix.one_apply]

theorem rowSum_one (A : Matrix ι ι ℝ) (i : ι) :
    rowSum A 1 i = ∑ j, A i j := by
  simp [rowSum]

theorem rowSum_add (A : Matrix ι ι ℝ) (a b : ℕ) (i : ι) :
    rowSum A (a + b) i = ∑ k, (A ^ a) i k * rowSum A b k := by
  simp only [rowSum, pow_add, Matrix.mul_apply, Finset.mul_sum]
  exact Finset.sum_comm

theorem IsSubstochastic.rowSum_nonneg (hA : IsSubstochastic A)
    (t : ℕ) (i : ι) : 0 ≤ rowSum A t i :=
  Finset.sum_nonneg fun j _ => hA.pow_nonneg t i j

theorem IsSubstochastic.entry_le_rowSum (hA : IsSubstochastic A)
    (t : ℕ) (i j : ι) : (A ^ t) i j ≤ rowSum A t i :=
  Finset.single_le_sum (fun k _ => hA.pow_nonneg t i k)
    (Finset.mem_univ j)

/-- Submultiplicativity of the maximum row sum. -/
theorem IsSubstochastic.rowSum_add_le (hA : IsSubstochastic A)
    (a b : ℕ) {c : ℝ} (hc : ∀ k, rowSum A b k ≤ c) (i : ι) :
    rowSum A (a + b) i ≤ rowSum A a i * c := by
  rw [rowSum_add, rowSum, Finset.sum_mul]
  exact Finset.sum_le_sum fun k _ =>
    mul_le_mul_of_nonneg_left (hc k) (hA.pow_nonneg a i k)

theorem IsSubstochastic.rowSum_succ_le (hA : IsSubstochastic A)
    (t : ℕ) (i : ι) : rowSum A (t + 1) i ≤ rowSum A t i := by
  have h := hA.rowSum_add_le t 1 (c := 1)
    (fun k => by rw [rowSum_one]; exact hA.row_le k) i
  simpa using h

theorem IsSubstochastic.rowSum_antitone (hA : IsSubstochastic A)
    (i : ι) : Antitone fun t => rowSum A t i :=
  antitone_nat_of_succ_le fun t => hA.rowSum_succ_le t i

/-- Geometric decay along multiples of `N`. -/
theorem IsSubstochastic.rowSum_mul_le (hA : IsSubstochastic A)
    {N : ℕ} {c : ℝ} (hc : ∀ k, rowSum A N k ≤ c) (m : ℕ) (i : ι) :
    rowSum A (m * N) i ≤ c ^ m := by
  have hc0 : 0 ≤ c := (hA.rowSum_nonneg N i).trans (hc i)
  induction m generalizing i with
  | zero => simp [rowSum_zero]
  | succ m ih =>
      rw [Nat.succ_mul, pow_succ]
      exact (hA.rowSum_add_le (m * N) N hc i).trans
        (mul_le_mul_of_nonneg_right (ih i) hc0)

/-- The entries of the powers tend to zero. -/
theorem IsSubstochastic.tendsto_pow_entry (hA : IsSubstochastic A)
    {N : ℕ} (hN : 0 < N) {c : ℝ} (hc1 : c < 1)
    (hc : ∀ k, rowSum A N k ≤ c) (i j : ι) :
    Tendsto (fun t => (A ^ t) i j) atTop (𝓝 0) := by
  have hc0 : 0 ≤ c := (hA.rowSum_nonneg N i).trans (hc i)
  have hbound : ∀ t, (A ^ t) i j ≤ c ^ (t / N) := by
    intro t
    calc
      (A ^ t) i j ≤ rowSum A t i := hA.entry_le_rowSum t i j
      _ ≤ rowSum A (t / N * N) i :=
        hA.rowSum_antitone i (Nat.div_mul_le_self t N)
      _ ≤ c ^ (t / N) := hA.rowSum_mul_le hc (t / N) i
  have hdiv : Tendsto (fun t : ℕ => t / N) atTop atTop :=
    Nat.tendsto_div_const_atTop (Nat.pos_iff_ne_zero.mp hN)
  have hpow : Tendsto (fun t : ℕ => c ^ (t / N)) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one hc0 hc1).comp hdiv
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    hpow (fun t => hA.pow_nonneg t i j) hbound

/-- `I - A` is nonsingular: a vector fixed by `A` is fixed by every
power, and the powers tend to zero. -/
theorem IsSubstochastic.det_one_sub_ne_zero (hA : IsSubstochastic A)
    {N : ℕ} (hN : 0 < N) {c : ℝ} (hc1 : c < 1)
    (hc : ∀ k, rowSum A N k ≤ c) : (1 - A).det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv, hker⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hfix : A *ᵥ v = v := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at hker
    exact hker.symm
  have hpow : ∀ t : ℕ, (A ^ t) *ᵥ v = v := by
    intro t
    induction t with
    | zero => simp
    | succ t ih => rw [pow_succ, ← Matrix.mulVec_mulVec, hfix, ih]
  apply hv
  funext i
  have hlim : Tendsto (fun t => ((A ^ t) *ᵥ v) i) atTop (𝓝 0) := by
    have h := tendsto_finsetSum (Finset.univ : Finset ι)
      (fun j _ => (hA.tendsto_pow_entry hN hc1 hc i j).mul_const (v j))
    simpa [Matrix.mulVec, dotProduct] using h
  have hconst : Tendsto (fun t => ((A ^ t) *ᵥ v) i) atTop (𝓝 (v i)) := by
    simp only [hpow]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique hconst hlim

/-- The Neumann series: the powers of `A` sum entrywise to the
inverse of `I - A`. -/
theorem IsSubstochastic.hasSum_pow_entry (hA : IsSubstochastic A)
    {N : ℕ} (hN : 0 < N) {c : ℝ} (hc1 : c < 1)
    (hc : ∀ k, rowSum A N k ≤ c) (i j : ι) :
    HasSum (fun t => (A ^ t) i j) ((1 - A)⁻¹ i j) := by
  have hunit : IsUnit (1 - A).det :=
    isUnit_iff_ne_zero.mpr (hA.det_one_sub_ne_zero hN hc1 hc)
  rw [hasSum_iff_tendsto_nat_of_nonneg (fun t => hA.pow_nonneg t i j)]
  have hpartial : ∀ T : ℕ,
      ∑ t ∈ Finset.range T, (A ^ t) i j =
        (1 - A)⁻¹ i j - ∑ k, (1 - A)⁻¹ i k * (A ^ T) k j := by
    intro T
    have hgeom : (1 - A) * ∑ t ∈ Finset.range T, A ^ t = 1 - A ^ T :=
      mul_neg_geom_sum A T
    have hsolve : ∑ t ∈ Finset.range T, A ^ t =
        (1 - A)⁻¹ * (1 - A ^ T) := by
      rw [← hgeom, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hunit,
        Matrix.one_mul]
    have hentry := congrFun (congrFun hsolve i) j
    rw [Matrix.sum_apply] at hentry
    rw [hentry, Matrix.mul_sub, Matrix.mul_one, Matrix.sub_apply,
      Matrix.mul_apply]
  simp only [hpartial]
  have hzero : Tendsto
      (fun T => ∑ k, (1 - A)⁻¹ i k * (A ^ T) k j) atTop (𝓝 0) := by
    have h := tendsto_finsetSum (Finset.univ : Finset ι)
      (fun k _ => (hA.tendsto_pow_entry hN hc1 hc k j).const_mul
        ((1 - A)⁻¹ i k))
    simpa using h
  simpa using tendsto_const_nhds.sub hzero

end Substochastic

end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.SubstochasticEscape
