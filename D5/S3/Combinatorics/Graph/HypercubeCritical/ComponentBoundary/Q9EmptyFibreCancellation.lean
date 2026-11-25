/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9EmptyFibreCancellation
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9EmptyFibreCancellation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: At an empty nine-cube fibre both layers must cancel the same paired Huang residual. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.HuangCubeCovariance

/-! At an empty first-axis fibre of a balanced cubic support, each layer
must supply its own singleton neighbours to cancel the common paired sum. -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9EmptyFibreCancellation

open scoped BigOperators
open Finset
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum
  (Q flip_adj IsSwitching switchingVector switching_sq ambient_eigenvector)
open private huangMatrix from D5.S3.Combinatorics.Graph.HypercubeSubQuorum
open private matrix_flip_zero matrix_flip_succ from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCriticalSpectrum
open private edge matrix_row flip_cons_zero flip_cons_succ from
  D5.S3.Combinatorics.Graph.HypercubeCritical.HuangCubeCovariance

local notation "flip" => BalancedCriticalSpectrum.flip

open Classical in
private theorem transverse_sum_eq_zero {C : Finset (Q 9)} {σ : Q 9 → ℝ}
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hs : IsSwitching C σ) (r : Q 8)
    (hempty : ∀ b : Bool, Fin.cons b r ∉ C) (b : Bool) :
    ∑ i ∈ univ.filter (fun i => Fin.cons b (flip r i) ∈ C),
      huangMatrix 8 r (flip r i) * σ (Fin.cons b (flip r i)) = 0 := by
  have h := congrFun (ambient_eigenvector (d := 3) C σ hr hs) (Fin.cons b r)
  change (huangMatrix 9).mulVec (switchingVector C σ) (Fin.cons b r) =
    3 * switchingVector C σ (Fin.cons b r) at h
  have htail : Sensitivity.π (Fin.cons b r) = r :=
    Fin.tail_cons (α := fun _ : Fin 9 => Bool) b r
  have hz (a : Bool) : switchingVector C σ (Fin.cons a r) = 0 := by
    simp only [switchingVector, ite_eq_right (hempty a)]
  have htrans (i : Fin 8) :
      huangMatrix 9 (Fin.cons b r) (Fin.cons b (flip r i)) =
        (if b then 1 else -1) * huangMatrix 8 r (flip r i) := by
    rw [← flip_cons_succ, matrix_flip_succ, Fin.cons_zero, htail]
  rw [matrix_row, Fin.sum_univ_succ] at h
  simp only [edge, flip_cons_zero, flip_cons_succ, htrans, hz, mul_zero, zero_add,
    mul_assoc, ← mul_sum] at h
  rw [sum_filter]
  suffices hsum :
      (∑ i : Fin 8, huangMatrix 8 r (flip r i) * switchingVector C σ (Fin.cons b (flip r i))) =
        0 by
    simpa only [switchingVector, mul_ite, mul_zero] using hsum
  cases b <;> simpa using h

open Classical in
/-- At an empty first-axis fibre, the common paired Huang sum is bounded by each
singleton count. The combined budget is eight, and the paired residual has magnitude
at most two and the same parity as the number of paired neighbours. -/
theorem paired_residual_bound {C : Finset (Q 9)} {σ : Q 9 → ℝ}
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hs : IsSwitching C σ) (r : Q 8)
    (hf : Fin.cons false r ∉ C) (ht : Fin.cons true r ∉ C) :
    let A := univ.filter fun i => Fin.cons false (flip r i) ∈ C
    let B := univ.filter fun i => Fin.cons true (flip r i) ∈ C
    let k := (A ∩ B).card
    let d := ∑ i ∈ A ∩ B, huangMatrix 8 r (flip r i) * σ (Fin.cons false (flip r i))
    |d| ≤ ((A \ B).card : ℝ) ∧ |d| ≤ ((B \ A).card : ℝ) ∧
      (k : ℝ) + 2 * |d| ≤ 8 ∧ |d| ≤ 2 ∧
      ∃ m : ℕ, m ≤ k ∧ d = (k : ℝ) - 2 * (m : ℝ) := by
  intro A B k d
  let term (b : Bool) (i : Fin 8) :=
    huangMatrix 8 r (flip r i) * σ (Fin.cons b (flip r i))
  have hempty (b : Bool) : Fin.cons b r ∉ C := by cases b <;> assumption
  have hA : ∑ i ∈ A, term false i = 0 := transverse_sum_eq_zero hr hs r hempty false
  have hB : ∑ i ∈ B, term true i = 0 := transverse_sum_eq_zero hr hs r hempty true
  have hpair : ∑ i ∈ B ∩ A, term true i = d := by
    rw [inter_comm B A]
    apply sum_congr rfl
    intro i hi
    obtain ⟨hiA, hiB⟩ := mem_inter.mp hi
    let q := flip r i
    have hfalse : Fin.cons false q ∈ C := (mem_filter.mp hiA).2
    have htrue : Fin.cons true q ∈ C := (mem_filter.mp hiB).2
    have hflip : flip (Fin.cons false q) 0 = Fin.cons true q := by
      rw [flip_cons_zero, Bool.not_false]
    have hedge := hs.2 _ hfalse _ (hflip.symm ▸ htrue) (flip_adj _ 0)
    rw [matrix_flip_zero, hflip] at hedge
    have hsquare := switching_sq hs hfalse
    have hsign : σ (Fin.cons true q) = σ (Fin.cons false q) := by
      calc
        _ = σ (Fin.cons false q) ^ 2 * σ (Fin.cons true q) := by rw [hsquare, one_mul]
        _ = σ (Fin.cons false q) * (σ (Fin.cons false q) * σ (Fin.cons true q)) := by ring
        _ = _ := by rw [← hedge, mul_one]
    change huangMatrix 8 r (flip r i) * σ (Fin.cons true q) =
      huangMatrix 8 r (flip r i) * σ (Fin.cons false q)
    rw [hsign]
  have hleft : ∑ i ∈ A \ B, term false i = -d := by
    have h := sum_inter_add_sum_sdiff A B (term false)
    rw [hA] at h
    change d + (∑ i ∈ A \ B, term false i) = 0 at h
    linarith only [h]
  have hright : ∑ i ∈ B \ A, term true i = -d := by
    have h := sum_inter_add_sum_sdiff B A (term true)
    rw [hpair, hB] at h
    linarith only [h]
  have hunit (b : Bool) {i : Fin 8} (hi : Fin.cons b (flip r i) ∈ C) :
      term b i ^ 2 = 1 := by
    dsimp only [term]
    rw [mul_pow, SupportedEigenSaturation.matrix_sq_of_adj (flip_adj r i),
      switching_sq hs hi, mul_one]
  have habs (b : Bool) (S : Finset (Fin 8))
      (hS : ∀ i ∈ S, Fin.cons b (flip r i) ∈ C) :
      |∑ i ∈ S, term b i| ≤ (S.card : ℝ) := by
    calc
      _ ≤ ∑ i ∈ S, |term b i| := abs_sum_le_sum_abs _ _
      _ = ∑ _i ∈ S, (1 : ℝ) := by
        apply sum_congr rfl
        intro i hi
        simpa only [one_pow, abs_one] using
          (sq_eq_sq_iff_abs_eq_abs (term b i) 1).mp (by rw [hunit b (hS i hi), one_pow])
      _ = _ := by simp
  have hleftBound := habs false (A \ B) fun i hi => (mem_filter.mp (mem_sdiff.mp hi).1).2
  have hrightBound := habs true (B \ A) fun i hi => (mem_filter.mp (mem_sdiff.mp hi).1).2
  rw [hleft, abs_neg] at hleftBound
  rw [hright, abs_neg] at hrightBound
  have hcard : k + (A \ B).card + (B \ A).card ≤ 8 := by
    have hsplit := card_inter_add_card_sdiff A B
    have hunion := card_sdiff_add_card B A
    have hmax : (B ∪ A).card ≤ 8 := by
      simpa only [Fintype.card_fin] using card_le_univ (B ∪ A)
    change k + (A \ B).card = A.card at hsplit
    omega
  have hcardReal : (k : ℝ) + ((A \ B).card : ℝ) + ((B \ A).card : ℝ) ≤ 8 := by
    exact_mod_cast hcard
  have hbudget : (k : ℝ) + 2 * |d| ≤ 8 := by
    linarith only [hcardReal, hleftBound, hrightBound]
  classical
  let negative := (A ∩ B).filter fun i => term false i = -1
  have hsum : d = (k : ℝ) - 2 * (negative.card : ℝ) := by
    calc
      d = ∑ i ∈ A ∩ B, (1 - 2 * (if term false i = -1 then (1 : ℝ) else 0)) := by
        apply sum_congr rfl
        intro i hi
        have hiC := (mem_filter.mp (mem_inter.mp hi).1).2
        change term false i = 1 - 2 * (if term false i = -1 then (1 : ℝ) else 0)
        rcases sq_eq_one_iff.mp (hunit false hiC) with h | h <;> norm_num [h]
      _ = _ := by
        simp only [sum_sub_distrib, ← mul_sum, ← sum_filter, sum_const, nsmul_eq_mul,
          mul_one, negative, k]
  have hdBound : |d| ≤ 2 := by
    by_contra! hlarge
    have hk : (k : ℝ) < 4 := by linarith only [hbudget, hlarge]
    have hkNat : k < 4 := by exact_mod_cast hk
    by_cases hsmall : k ≤ 2
    · have h := habs false (A ∩ B) fun i hi => (mem_filter.mp (mem_inter.mp hi).1).2
      change |d| ≤ (k : ℝ) at h
      have hkReal : (k : ℝ) ≤ 2 := by exact_mod_cast hsmall
      linarith only [h, hkReal, hlarge]
    · have hkEq : k = 3 := by omega
      have hlt : |d| < 3 := by
        rw [hkEq] at hbudget
        norm_num at hbudget
        linarith only [hbudget]
      let z : ℤ := (k : ℤ) - 2 * (negative.card : ℤ)
      have hz : (z : ℝ) = d := by
        push_cast [z]
        exact hsum.symm
      rw [← hz, ← Int.cast_abs] at hlarge hlt
      have hlo : (2 : ℤ) < |z| := by exact_mod_cast hlarge
      have hhi : |z| < (3 : ℤ) := by exact_mod_cast hlt
      omega
  exact ⟨hleftBound, hrightBound, hbudget, hdBound, negative.card,
    card_mono (filter_subset _ _), hsum⟩

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9EmptyFibreCancellation
