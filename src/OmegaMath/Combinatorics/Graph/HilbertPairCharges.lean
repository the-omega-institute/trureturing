import OmegaBuild.Commands
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Indicator
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Max
import Mathlib.Order.Interval.Finset.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Charging ordered pairs to their endpoints -/

compile_only_with_mathlib

open scoped BigOperators

namespace HilbertPairCharges

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

/-- A sum over each pair once, indexed by its later endpoint. -/
noncomputable def pairs (f : ι → ι → ℝ) : ℝ :=
  ∑ j, ∑ i ∈ Finset.univ.filter (fun i => i < j), f i j

/-- Each pair contributes to its two endpoint marginals. -/
theorem incidence (x : ι → ι → ℝ) (hx : ∀ i j, x i j = x j i)
    (hz : ∀ i, x i i = 0) (S : Finset ι) (f : ι → ℝ) :
    (∑ j ∈ S, ∑ i ∈ S, if i < j then x i j * (f i + f j) else 0) =
      ∑ j ∈ S, (∑ i ∈ S, x i j) * f j := by
  classical
  have split (i j : ι) : (if i < j then x i j * (f i + f j) else 0) =
      (if i < j then x i j * f i else 0) + (if i < j then x i j * f j else 0) := by
    split_ifs <;> ring
  simp_rw [split, Finset.sum_add_distrib]
  have swap : (∑ j ∈ S, ∑ i ∈ S, if i < j then x i j * f i else 0) =
      ∑ j ∈ S, ∑ i ∈ S, if j < i then x i j * f j else 0 := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by
      rw [hx j i]
  rw [swap, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rcases lt_trichotomy i j with h | rfl | h
  · simp [h, h.not_gt]
  · simp [hz]
  · simp [h, h.not_gt]

/-- The incidence inequality retains only pairs whose two endpoints belong to
the prescribed earlier portion of the clique. -/
theorem prefix_incidence_le (p : ι → ℝ) (x : ι → ι → ℝ) (hx : ∀ i j, x i j = x j i)
    (hx₀ : ∀ i j, 0 ≤ x i j) (hz : ∀ i, x i i = 0)
    (hdegree : ∀ j, (∑ i, x i j) ≤ p j) (S : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ S, 0 ≤ f i) :
    (∑ j ∈ S, ∑ i ∈ S, if i < j then x i j * (f i + f j) else 0) ≤
      ∑ j ∈ S, p j * f j := by
  rw [incidence x hx hz]
  apply Finset.sum_le_sum
  intro j hj
  apply mul_le_mul_of_nonneg_right _ (hf j hj)
  exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
    (fun i _ _ => hx₀ i j)).trans (hdegree j)

/-- In a suffix charge on a pair, a companion vertex contributes to the two
edges joining it to the pair's endpoints. -/
theorem suffix_companions_le (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (x : ι → ι → ℝ) (hx : ∀ i j, x i j = x j i) (hx₀ : ∀ i j, 0 ≤ x i j)
    (hz : ∀ i, x i i = 0) (hdegree : ∀ j, (∑ i, x i j) ≤ p j)
    (cut : ι → ι → Prop) [DecidableRel cut]
    (hcut : ∀ {i j k}, i < j → cut j k → cut i k)
    (f : ι → ι → ℝ) (hf : ∀ i k, cut i k → 0 ≤ f i k) :
    pairs (fun i j => x i j * ∑ k ∈ Finset.univ.filter (cut j),
        p k * (f i k + f j k)) ≤
      ∑ k, ∑ i ∈ Finset.univ.filter (fun i => cut i k), p i * p k * f i k := by
  classical
  let charge (k j i : ι) := if i < j ∧ cut j k then p k * (x i j * (f i k + f j k)) else 0
  have expand : pairs (fun i j => x i j * ∑ k ∈ Finset.univ.filter (cut j),
      p k * (f i k + f j k)) = ∑ j, ∑ i, ∑ k, charge k j i := by
    unfold pairs
    apply Finset.sum_congr rfl
    intro j _
    simp only [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hij : i < j
    · simp only [hij, if_true, true_and, Finset.mul_sum, charge]
      apply Finset.sum_congr rfl
      intro k _
      split_ifs <;> ring
    · simp [hij, charge]
  rw [expand, show (∑ j, ∑ i, ∑ k, charge k j i) = ∑ k, ∑ j, ∑ i, charge k j i by
    calc
      _ = ∑ j, ∑ k, ∑ i, charge k j i :=
        Finset.sum_congr rfl fun j _ => Finset.sum_comm
      _ = _ := Finset.sum_comm]
  apply Finset.sum_le_sum
  intro k _
  let S := Finset.univ.filter (fun i => cut i k)
  have extract : (∑ j, ∑ i, charge k j i) =
      p k * ∑ j ∈ S, ∑ i ∈ S, if i < j then x i j * (f i k + f j k) else 0 := by
    simp only [S, Finset.sum_filter, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : cut j k
    · simp only [hj, if_true, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hij : i < j
      · simp [charge, hj, hij, hcut hij hj]
      · simp [charge, hij, mul_ite]
    · simp [charge, hj]
  rw [extract]
  calc
    _ ≤ p k * ∑ i ∈ S, p i * f i k := mul_le_mul_of_nonneg_left
      (prefix_incidence_le p x hx hx₀ hz hdegree S (fun i => f i k)
        (fun i hi => hf i k (Finset.mem_filter.mp hi).2)) (hp k)
    _ = _ := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring

end HilbertPairCharges


namespace HilbertPairCharges

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

/-- For a symmetric function vanishing on the diagonal, the ordered sum
counts each pair twice. -/
theorem twice_pairs (f : ι → ι → ℝ) (hs : ∀ i j, f i j = f j i)
    (hd : ∀ i, f i i = 0) :
    2 * pairs f = ∑ j, ∑ i, f i j := by
  classical
  have hh := incidence f hs hd Finset.univ (fun _ => 1)
  simp only [show (1 : ℝ) + 1 = 2 by norm_num, mul_one] at hh
  rw [← hh]
  simp only [pairs, Finset.sum_filter, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by
    split_ifs <;> ring

/-- Normalized pair rows assign half their weight to each endpoint.
Rows indexed by diagonal pairs are the singleton rows. -/
noncomputable def endpointWeight (w : ι × ι → ℝ) (i : ι) : ℝ :=
  ∑ j, (w (i, j) + w (j, i)) / 2

noncomputable def edgeWeight (w : ι × ι → ℝ) (i j : ι) : ℝ :=
  if i = j then 0 else (w (i, j) + w (j, i)) / 2

theorem endpointWeight_nonneg (w : ι × ι → ℝ) (hw : ∀ u, 0 ≤ w u) (i : ι) :
    0 ≤ endpointWeight w i :=
  Finset.sum_nonneg fun j _ => div_nonneg (add_nonneg (hw _) (hw _)) (by norm_num)

theorem endpointWeight_sum (w : ι × ι → ℝ) (hw : ∑ u, w u = 1) :
    (∑ i, endpointWeight w i) = 1 := by
  classical
  unfold endpointWeight
  simp only [add_div, Finset.sum_add_distrib, div_eq_mul_inv, ← Finset.sum_mul]
  rw [show (∑ i, ∑ j, w (j, i)) = ∑ i, ∑ j, w (i, j) from Finset.sum_comm,
    ← Fintype.sum_prod_type, hw]
  norm_num

theorem edgeWeight_symm (w : ι × ι → ℝ) (i j : ι) :
    edgeWeight w i j = edgeWeight w j i := by
  simp [edgeWeight, eq_comm, add_comm]

theorem edgeWeight_diag (w : ι × ι → ℝ) (i : ι) : edgeWeight w i i = 0 := by
  simp [edgeWeight]

theorem edgeWeight_nonneg (w : ι × ι → ℝ) (hw : ∀ u, 0 ≤ w u) (i j : ι) :
    0 ≤ edgeWeight w i j := by
  unfold edgeWeight
  split_ifs
  · rfl
  · exact div_nonneg (add_nonneg (hw _) (hw _)) (by norm_num)

theorem edgeWeight_degree (w : ι × ι → ℝ) (hw : ∀ u, 0 ≤ w u) (j : ι) :
    (∑ i, edgeWeight w i j) ≤ endpointWeight w j := by
  unfold endpointWeight
  apply Finset.sum_le_sum
  intro i _
  rw [edgeWeight_symm]
  unfold edgeWeight
  split_ifs
  · exact div_nonneg (add_nonneg (hw _) (hw _)) (by norm_num)
  · rfl

theorem endpointWeight_mix (w : ι × ι → ℝ) (f : ι → ℝ) :
    (∑ u, w u * ((f u.1 + f u.2) / 2)) = ∑ i, endpointWeight w i * f i := by
  simp only [Fintype.sum_prod_type, add_div, mul_add, Finset.sum_add_distrib]
  have hh : (∑ i, ∑ j, w (i, j) * (f j / 2)) =
      ∑ i, ∑ j, w (j, i) * (f i / 2) := Finset.sum_comm
  rw [hh, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [endpointWeight, Finset.sum_mul, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem edgeWeight_mix (w : ι × ι → ℝ) (f : ι → ι → ℝ) :
    (∑ u, w u * ((if u.1 < u.2 then f u.1 u.2 else if u.2 < u.1 then f u.2 u.1 else 0) / 2)) =
      pairs (fun i j => edgeWeight w i j * f i j) := by
  classical
  have hsplit (i j : ι) :
      w (i, j) * ((if i < j then f i j else if j < i then f j i else 0) / 2) =
        (if i < j then w (i, j) * (f i j / 2) else 0) +
        (if j < i then w (i, j) * (f j i / 2) else 0) := by
    rcases lt_trichotomy i j with h | rfl | h
    · simp [h, h.not_gt]
    · simp
    · simp [h, h.not_gt]
  simp only [Fintype.sum_prod_type, hsplit, Finset.sum_add_distrib]
  have he : (∑ i, ∑ j, if i < j then w (i, j) * (f i j / 2) else 0) =
      ∑ j, ∑ i, if i < j then w (i, j) * (f i j / 2) else 0 := Finset.sum_comm
  rw [he, ← Finset.sum_add_distrib]
  simp only [pairs, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : i < j
  · simp [h, h.ne, edgeWeight]
    ring
  · simp [h]

end HilbertPairCharges


namespace HilbertPairCharges

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

/-- A decreasing suffix charge against pair weights is bounded by an
antiderivative evaluated at their total mass. -/
theorem suffix_mass_le (p q : ι → ℝ) (hq : ∀ i, 0 ≤ q i)
    (hpq : ∀ i, q i ≤ p i) (hp : ∑ i, p i ≤ 1)
    (B P : ℝ → ℝ) (hB : AntitoneOn B (Set.Icc 0 1))
    (hStep : ∀ l u : ℝ, 0 ≤ l → l ≤ u → u ≤ 1 → (u - l) * B u ≤ P u - P l) :
    (∑ j, q j * B (∑ k ∈ Finset.univ.filter (fun k => j ≤ k), p k)) ≤
      P (∑ j, q j) - P 0 := by
  classical
  have hp₀ (i : ι) : 0 ≤ p i := (hq i).trans (hpq i)
  have bound (S : Finset ι) :
      (∑ j ∈ S, q j * B (∑ k ∈ S.filter (fun k => j ≤ k), p k)) ≤ P (∑ j ∈ S, q j) - P 0 := by
    induction S using Finset.induction_on_min with
    | empty => simp
    | insert j S hj ih =>
      have hnot : j ∉ S := fun h => lt_irrefl j (hj j h)
      have full : (insert j S).filter (fun k => j ≤ k) = insert j S := by
        apply Finset.filter_eq_self.mpr
        intro k hk
        rcases Finset.mem_insert.mp hk with he | h
        · simp [he]
        · exact (hj k h).le
      have same (i : ι) (hi : i ∈ S) :
          (insert j S).filter (fun k => i ≤ k) = S.filter (fun k => i ≤ k) := by
        simp [Finset.filter_insert, (hj i hi).not_ge]
      let u := ∑ k ∈ insert j S, q k
      let l := ∑ k ∈ S, q k
      let v := ∑ k ∈ insert j S, p k
      have hu : u = q j + l := Finset.sum_insert hnot
      have hl₀ : 0 ≤ l := Finset.sum_nonneg fun i _ => hq i
      have hlu : l ≤ u := by rw [hu]; linarith [hq j]
      have huv : u ≤ v := Finset.sum_le_sum fun i _ => hpq i
      have hv₁ : v ≤ 1 :=
        (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ => hp₀ i)).trans hp
      have hbu : B v ≤ B u := hB ⟨hl₀.trans hlu, huv.trans hv₁⟩
        ⟨(hl₀.trans hlu).trans huv, hv₁⟩ huv
      have hfirst : q j * B v ≤ P u - P l :=
        (mul_le_mul_of_nonneg_left hbu (hq j)).trans (by
          simpa only [show u - l = q j by linarith] using hStep l u hl₀ hlu (huv.trans hv₁))
      rw [Finset.sum_insert hnot, full]
      have hnext :
          (∑ i ∈ S, q i * B (∑ k ∈ (insert j S).filter (fun k => i ≤ k), p k)) =
            ∑ i ∈ S, q i * B (∑ k ∈ S.filter (fun k => i ≤ k), p k) :=
        Finset.sum_congr rfl fun i hi => by rw [same i hi]
      rw [hnext]
      change q j * B v + _ ≤ P u - P 0
      linarith
  exact bound Finset.univ

theorem pair_mass_le_half (p : ι → ℝ) (hp : ∑ j, p j = 1) (x : ι → ι → ℝ)
    (hx : ∀ i j, x i j = x j i) (hdiag : ∀ i, x i i = 0)
    (hdegree : ∀ j, (∑ i, x i j) ≤ p j) : pairs x ≤ 1 / 2 := by
  have hh : (∑ j, ∑ i, x i j) ≤ ∑ j, p j := Finset.sum_le_sum fun j _ => hdegree j
  rw [← twice_pairs x hx hdiag, hp] at hh
  linarith

end HilbertPairCharges
