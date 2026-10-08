/- GID: D5/S3/Combinatorics/DihedralRamsey/NestedCounting
   generality: G
   mirror-B: D5/B/S3/Combinatorics/DihedralRamsey/NestedCounting
   mirror-E: none(waiver:endpoint-sum-counting)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Extremal.Turan]
   utility: none
   digest: Endpoint-sum class bounds force a degree obstruction, sharpened by parity. -/

import D5.S3.Combinatorics.DihedralRamsey.NestedRamseyDefs
import D5.S3.Combinatorics.DihedralRamsey.NestedCountingArithmetic
import Mathlib.Combinatorics.SimpleGraph.Extremal.Turan

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.DihedralRamsey.NestedCounting

open Finset
open scoped BigOperators

theorem endpoint_degree_bound {n r : ℕ} (hn : 0 < n)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hc : ∀ c : Fin n,
      (univ.filter fun e : Fin n × Fin n =>
        e.1 < e.2 ∧ G.Adj e.1 e.2 ∧ (e.1.val + e.2.val) % n = c.val).card ≤ r) :
    (∃ v, G.degree v ≤ 2 * r) ∧
      (n % 2 = 0 → r % 2 = 1 → ∃ v, G.degree v < 2 * r) := by
  classical
  let P : Finset (Fin n × Fin n) := univ.filter fun e => e.1 < e.2 ∧ G.Adj e.1 e.2
  let D : Finset (Fin n × Fin n) := univ.filter fun e => G.Adj e.1 e.2
  have split : D = P ∪ P.image Prod.swap := by
    ext e
    simp only [D, P, mem_filter, mem_univ, true_and, mem_union, mem_image]
    constructor
    · intro he
      rcases lt_or_gt_of_ne (G.ne_of_adj he) with h | h
      · exact Or.inl ⟨h, he⟩
      · exact Or.inr ⟨e.swap, ⟨h, he.symm⟩, Prod.swap_swap e⟩
    · rintro (⟨_, h⟩ | ⟨f, ⟨_, h⟩, rfl⟩)
      · exact h
      · exact h.symm
  have disj : Disjoint P (P.image Prod.swap) := by
    apply disjoint_left.mpr
    intro e he hf
    obtain ⟨f, hf, hfe⟩ := mem_image.mp hf
    have h1 := (mem_filter.mp he).2.1
    have h2 := (mem_filter.mp hf).2.1
    subst e
    exact (lt_asymm h1 h2)
  have sumD : ∀ f : Fin n × Fin n → ℕ,
      (∑ e ∈ D, f e) = (∑ e ∈ P, f e) + ∑ e ∈ P, f e.swap := by
    intro f
    rw [split, sum_union disj, sum_image]
    intro x _ y _ h
    exact Prod.swap_injective h
  have Dsum : ∀ f : Fin n × Fin n → ℕ,
      (∑ e ∈ D, f e) = ∑ u : Fin n, ∑ v : Fin n,
        if G.Adj u v then f (u, v) else 0 := by
    intro f
    dsimp only [D]
    rw [sum_filter]
    exact Fintype.sum_prod_type _
  have deg : ∀ v, G.degree v = ∑ u : Fin n, if G.Adj v u then 1 else 0 := by
    intro v
    rw [sum_boole, ← G.card_neighborFinset_eq_degree]
    simp [SimpleGraph.neighborFinset_eq_filter]
  have total : (∑ v : Fin n, G.degree v) = 2 * P.card := by
    have hh := sumD (fun _ => 1)
    rw [Dsum] at hh
    simp only [sum_const, smul_eq_mul, mul_one] at hh
    simpa only [deg, Nat.two_mul] using hh
  have weighted : (∑ v : Fin n, v.val * G.degree v) =
      ∑ e ∈ P, (e.1.val + e.2.val) := by
    have hfst : (∑ e ∈ D, e.1.val) = ∑ v : Fin n, v.val * G.degree v := by
      rw [Dsum]
      simp_rw [deg, mul_sum, mul_ite, mul_one, mul_zero]
    have hsnd : (∑ e ∈ D, e.2.val) = ∑ v : Fin n, v.val * G.degree v := by
      rw [Dsum, sum_comm]
      simp_rw [G.adj_comm, deg, mul_sum, mul_ite, mul_one, mul_zero]
    have hh := sumD (fun e => e.1.val + e.2.val)
    simp only [Prod.fst_swap, Prod.snd_swap, Nat.add_comm] at hh
    rw [sum_add_distrib, hfst, hsnd] at hh
    omega
  let f : Fin n × Fin n → Fin n := fun e =>
    ⟨(e.1.val + e.2.val) % n, Nat.mod_lt _ hn⟩
  let q : Fin n → ℕ := fun c => (P.filter fun e => f e = c).card
  have qle : ∀ c, q c ≤ r := by
    intro c
    simpa [q, P, f, filter_filter, Fin.ext_iff, and_assoc] using hc c
  have cardP : (∑ c : Fin n, q c) = P.card := by
    exact card_eq_sum_card_fiberwise (fun _ _ => mem_univ _) |>.symm
  have bound : (∑ v : Fin n, G.degree v) ≤ n * (2 * r) := by
    rw [total, ← cardP]
    have hh := sum_le_sum (fun c (_ : c ∈ (univ : Finset (Fin n))) => qle c)
    simpa only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul,
      Nat.mul_left_comm n 2 r] using Nat.mul_le_mul_left 2 hh
  constructor
  · by_contra h
    have hv : ∀ v, 2 * r < G.degree v := by simpa using h
    have hh : n * (2 * r) < ∑ v : Fin n, G.degree v := by
      have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
      simpa using sum_lt_sum_of_nonempty (s := univ) univ_nonempty (fun v _ => hv v)
    omega
  · intro hne hre
    by_contra h
    have hv : ∀ v, 2 * r ≤ G.degree v := by simpa using h
    have eqtotal : (∑ v : Fin n, G.degree v) = n * (2 * r) := by
      apply le_antisymm bound
      simpa using sum_le_sum (fun v (_ : v ∈ (univ : Finset (Fin n))) => hv v)
    have reg : ∀ v, G.degree v = 2 * r := by
      have heq : (∑ v : Fin n, G.degree v) = ∑ _ : Fin n, 2 * r := by
        simpa using eqtotal
      have hh := (sum_eq_sum_iff_of_le (fun v (_ : v ∈ (univ : Finset (Fin n))) =>
        hv v)).mp heq.symm
      intro v
      exact (hh v (mem_univ v)).symm
    have eqclasses : (∑ c : Fin n, q c) = n * r := by
      rw [total, ← cardP] at eqtotal
      rw [Nat.mul_left_comm n 2 r] at eqtotal
      exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < 2) eqtotal
    have qeq : ∀ c, q c = r := by
      have heq : (∑ c : Fin n, q c) = ∑ _ : Fin n, r := by simpa using eqclasses
      have hh := (sum_eq_sum_iff_of_le (fun c (_ : c ∈ (univ : Finset (Fin n))) =>
        qle c)).mp heq
      intro c
      exact hh c (mem_univ c)
    have modsum : (∑ e ∈ P, (e.1.val + e.2.val)) % n =
        (∑ c : Fin n, c.val * q c) % n := by
      rw [sum_nat_mod]
      have hh : (∑ c : Fin n, ∑ e ∈ P.filter (fun e => f e = c),
          (e.1.val + e.2.val) % n) = ∑ e ∈ P, (e.1.val + e.2.val) % n := by
        exact sum_fiberwise_of_maps_to (fun _ _ => mem_univ _) _
      rw [← hh]
      congr 1
      apply sum_congr rfl
      intro c _
      rw [show c.val * q c = ∑ _e ∈ P.filter (fun e => f e = c), c.val by
        simp [q, Nat.mul_comm]]
      apply sum_congr rfl
      intro e he
      exact congrArg Fin.val (mem_filter.mp he).2
    let S := ∑ v : Fin n, v.val
    have hS : 2 * S = n * (n - 1) := by
      rw [show S = ∑ i ∈ range n, i from ?_]
      · simpa [Nat.mul_comm] using sum_range_id_mul_two n
      · exact Fin.sum_univ_eq_sum_range (fun i => i) n
    have hmod : (2 * r * S) % n = (r * S) % n := by
      simpa [← weighted, reg, qeq, ← sum_mul, ← mul_sum, Nat.mul_comm,
        Nat.mul_left_comm, Nat.mul_assoc, S] using modsum
    have hleft : (2 * r * S) % n = 0 := by
      have heq : 2 * r * S = r * (n * (n - 1)) := by
        calc
          _ = r * (2 * S) := by ac_rfl
          _ = _ := by rw [hS]
      rw [heq]
      simp [Nat.mul_left_comm]
    have hdiv : n ∣ r * S := Nat.dvd_of_mod_eq_zero (hmod.symm.trans hleft)
    exact NestedCountingArithmetic.weighted_parity_obstruction hn hne hre hdiv

end D5.S3.Combinatorics.DihedralRamsey.NestedCounting
