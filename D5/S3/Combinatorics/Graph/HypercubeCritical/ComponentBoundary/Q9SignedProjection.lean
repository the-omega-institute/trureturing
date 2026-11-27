/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SignedProjection
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SignedProjection
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Matrix.PosDef]
   utility: none
   digest: Negative compatible incidences bound the energy of a signed projection. -/

module

public import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Signed projection bounds for the opposite-dimer branch of Hong, Wu and Xia's Problem 2. -/

set_option autoImplicit false

public section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9SignedProjection

open scoped BigOperators Matrix
open Finset (univ)

variable {ι δ : Type*} [Fintype ι] [Fintype δ]

open Classical in
/-- The number of rows whose incidence in a column has sign opposite to the source. -/
@[expose] noncomputable def negativeIncidences (R : Matrix ι δ ℝ) (m : ι → ℝ) (d : δ) : ℕ :=
  (univ.filter (fun i => m i * R i d < 0)).card

private theorem nonneg_of_mulVec_eq {G : Matrix δ δ ℝ} (hG : G.PosDef)
    (hoff : ∀ d e, d ≠ e → G d e ≤ 0) {q k : δ → ℝ}
    (hsolve : G *ᵥ q = k) (hk : ∀ d, 0 ≤ k d) : ∀ d, 0 ≤ q d := by
  classical
  let p : δ → ℝ := fun d => max (q d) 0
  let n : δ → ℝ := fun d => max (-q d) 0
  have hp (d) : 0 ≤ p d := le_max_right _ _
  have hn (d) : 0 ≤ n d := le_max_right _ _
  have hsplit : q = p - n := by
    funext d
    change q d = max (q d) 0 - max (-q d) 0
    rcases le_total (q d) 0 with hd | hd
    · rw [max_eq_right hd, max_eq_left (neg_nonneg.mpr hd), zero_sub, neg_neg]
    · rw [max_eq_left hd, max_eq_right (neg_nonpos.mpr hd), sub_zero]
  have hcross : n ⬝ᵥ (G *ᵥ p) ≤ 0 := by
    unfold dotProduct
    apply Finset.sum_nonpos
    intro d _
    rw [Matrix.mulVec, dotProduct, Finset.mul_sum]
    apply Finset.sum_nonpos
    intro e _
    by_cases hde : d = e
    · subst e
      rcases le_total (q d) 0 with hd | hd
      · simp [p, max_eq_right hd]
      · simp [n, max_eq_right (neg_nonpos.mpr hd)]
    · exact mul_nonpos_of_nonneg_of_nonpos (hn d)
        (mul_nonpos_of_nonpos_of_nonneg (hoff d e hde) (hp e))
  intro d
  by_contra! hd
  have hnpos : 0 < n d := (neg_pos.mpr hd).trans_le (le_max_left _ _)
  have hnzero : n ≠ 0 := fun h => (ne_of_gt hnpos) (congrFun h d)
  have hstrict : 0 < n ⬝ᵥ (G *ᵥ n) := by
    simpa using hG.dotProduct_mulVec_pos hnzero
  have hright : 0 ≤ n ⬝ᵥ k := Finset.sum_nonneg (fun e _ => mul_nonneg (hn e) (hk e))
  rw [← hsolve, hsplit, Matrix.mulVec_sub, dotProduct_sub] at hright
  linarith

private theorem projection_energy_le_incidence_count
    (R : Matrix ι δ ℝ) (m : ι → ℝ) (q : δ → ℝ)
    (hm : ∀ i, m i ^ 2 ≤ 1) (hq : ∀ d, 0 ≤ q d)
    (horth : Rᵀ *ᵥ (R *ᵥ q + m) = 0) :
    (R *ᵥ q) ⬝ᵥ (R *ᵥ q) ≤ ((∑ d, negativeIncidences R m d : ℕ) : ℝ) := by
  classical
  let x := R *ᵥ q
  have hxorth : x ⬝ᵥ x + x ⬝ᵥ m = 0 := by
    rw [← dotProduct_add, dotProduct_comm x]
    change (R *ᵥ q + m) ⬝ᵥ (R *ᵥ q) = 0
    rw [← Matrix.dotProduct_transpose_mulVec, horth, dotProduct_zero]
  have henergy : x ⬝ᵥ x = ∑ i, (m i ^ 2 - (x i + m i) ^ 2) := by
    calc
      x ⬝ᵥ x = -(x ⬝ᵥ x) - 2 * (x ⬝ᵥ m) := by linarith
      _ = _ := by
        simp only [dotProduct, ← Finset.sum_neg_distrib, Finset.mul_sum, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl (fun i _ => by ring)
  have hrow (i : ι) :
      m i ^ 2 - (x i + m i) ^ 2 ≤ ∑ d, if m i * R i d < 0 then (1 : ℝ) else 0 := by
    by_cases hit : ∃ d, m i * R i d < 0
    · obtain ⟨d, hd⟩ := hit
      calc
        _ ≤ 1 := (sub_le_self _ (sq_nonneg _)).trans (hm i)
        _ = (if m i * R i d < 0 then (1 : ℝ) else 0) := (ite_eq_left hd).symm
        _ ≤ _ := Finset.single_le_sum (f := fun e => if m i * R i e < 0 then (1 : ℝ) else 0)
          (fun e _ => by split <;> norm_num) (Finset.mem_univ d)
    · push Not at hit
      have hsign : 0 ≤ m i * x i := by
        simp only [x, Matrix.mulVec, dotProduct, Finset.mul_sum, ← mul_assoc]
        exact Finset.sum_nonneg (fun d _ => mul_nonneg (hit d) (hq d))
      have hres : m i ^ 2 - (x i + m i) ^ 2 ≤ 0 := by
        nlinarith only [hsign, sq_nonneg (x i)]
      exact hres.trans (Finset.sum_nonneg (fun d _ => by split <;> norm_num))
  calc
    _ = _ := henergy
    _ ≤ ∑ i, ∑ d, if m i * R i d < 0 then (1 : ℝ) else 0 :=
      Finset.sum_le_sum (fun i _ => hrow i)
    _ = _ := by
      rw [Finset.sum_comm]
      simp only [Finset.sum_boole, negativeIncidences, Nat.cast_sum]

omit [Fintype δ] in
open Classical in
private theorem twice_negativeIncidences (R : Matrix ι δ ℝ) (m : ι → ℝ) (d : δ) (k : ℕ)
    (hsign : ∀ i, m i * R i d = 0 ∨ m i * R i d = 1 ∨ m i * R i d = -1)
    (hsum : (∑ i, m i * R i d) = -(k : ℝ)) :
    2 * negativeIncidences R m d = (univ.filter (fun i => m i * R i d ≠ 0)).card + k := by
  classical
  have hterm (i : ι) :
      (if m i * R i d ≠ 0 then (1 : ℝ) else 0) -
        2 * (if m i * R i d < 0 then (1 : ℝ) else 0) = m i * R i d := by
    rcases hsign i with h | h | h <;> norm_num [h]
  have hcount := Finset.sum_congr (s₁ := univ) rfl (fun i _ => hterm i)
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hsum] at hcount
  have hcast :
      ((univ.filter (fun i => m i * R i d ≠ 0)).card : ℝ) -
        2 * (negativeIncidences R m d : ℝ) = -(k : ℝ) := by
    simpa only [Finset.sum_boole, negativeIncidences] using hcount
  exact_mod_cast (show 2 * (negativeIncidences R m d : ℝ) =
      ((univ.filter (fun i => m i * R i d ≠ 0)).card : ℝ) + (k : ℝ) by linarith)

open Classical in
/-- For the omitted-row matrix, a signed source of magnitude at most one and a Gram
solve give a projection energy bounded by the actual number of negative incidences.
If only the rank-four columns have compatible faces, at most four each, the
signed column sums bound the number of negative incidences by twice their count. -/
theorem signed_projection_bounds (R : Matrix ι δ ℝ) (m : ι → ℝ)
    (rankFour : Finset δ) (k : δ → ℕ) (q : δ → ℝ)
    (hm : ∀ i, m i ^ 2 ≤ 1)
    (hsign : ∀ i d, m i * R i d = 0 ∨ m i * R i d = 1 ∨ m i * R i d = -1)
    (hfaces : ∀ d, (univ.filter (fun i => m i * R i d ≠ 0)).card + k d ≤
      if d ∈ rankFour then 4 else 0)
    (hpos : (Rᵀ * R).PosDef)
    (hoff : ∀ d e, d ≠ e → (Rᵀ * R) d e ≤ 0)
    (hsource : Rᵀ *ᵥ m = -(fun d => (k d : ℝ)))
    (hsolve : (Rᵀ * R) *ᵥ q = fun d => (k d : ℝ)) :
    q ⬝ᵥ (fun d => (k d : ℝ)) = (R *ᵥ q) ⬝ᵥ (R *ᵥ q) ∧
      (R *ᵥ q) ⬝ᵥ (R *ᵥ q) ≤ ((∑ d, negativeIncidences R m d : ℕ) : ℝ) ∧
      (∑ d, negativeIncidences R m d) ≤ 2 * rankFour.card := by
  classical
  have hq := nonneg_of_mulVec_eq hpos hoff hsolve (fun d => Nat.cast_nonneg (k d))
  have horth : Rᵀ *ᵥ (R *ᵥ q + m) = 0 := by
    rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, hsolve, hsource, add_neg_cancel]
  refine ⟨?_, projection_energy_le_incidence_count R m q hm hq horth, ?_⟩
  · rw [← hsolve, ← Matrix.mulVec_mulVec, Matrix.dotProduct_transpose_mulVec]
  · have hcol (d : δ) : negativeIncidences R m d ≤ if d ∈ rankFour then 2 else 0 := by
      have hsum : (∑ i, m i * R i d) = -(k d : ℝ) := by
        simpa [Matrix.mulVec, dotProduct, mul_comm] using congrFun hsource d
      have hcap := hfaces d
      rw [← twice_negativeIncidences R m d (k d) (fun i => hsign i d) hsum] at hcap
      by_cases hd : d ∈ rankFour <;> simp only [hd, ite_true, ite_false] at hcap ⊢ <;> omega
    calc
      _ ≤ ∑ d, if d ∈ rankFour then 2 else 0 := Finset.sum_le_sum (fun d _ => hcol d)
      _ = _ := by simp [Nat.mul_comm]

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9SignedProjection
