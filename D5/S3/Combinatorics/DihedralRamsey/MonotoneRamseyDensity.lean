/- GID: D5/S3/Combinatorics/DihedralRamsey/MonotoneRamseyDensity
   generality: G
   mirror-B: D5/B/S3/Combinatorics/DihedralRamsey/MonotoneRamseyDensity
   mirror-E: none(waiver:circular-monotone-density)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Extremal.Turan]
   utility: none
   digest: Circular monotone path avoidance gives a sharp enough quadratic edge bound. -/

import D5.S3.Combinatorics.DihedralRamsey.MonotoneRamseyDefs
import D5.S3.Combinatorics.DihedralRamsey.MonotoneRamseyCopies
import D5.S3.Combinatorics.DihedralRamsey.PathStar
import Mathlib.Combinatorics.SimpleGraph.Extremal.Turan

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.DihedralRamsey.MonotoneRamseyDensity

open Finset
open DihedralRamseyDefs CyclicRamseyDefs MonotoneRamseyDefs

/-- Count directed edges according to the two parts of a vertex partition. -/
theorem edge_partition {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Finset (Fin n)) :
    2 * G.edgeFinset.card =
      (∑ x ∈ C, ∑ y ∈ C, if G.Adj x y then 1 else 0) +
      2 * (∑ x ∈ Cᶜ, ∑ y ∈ C, if G.Adj x y then 1 else 0) +
      (∑ x ∈ Cᶜ, ∑ y ∈ Cᶜ, if G.Adj x y then 1 else 0) := by
  classical
  have split : ∀ f : Fin n → ℕ,
      (∑ x, f x) = (∑ x ∈ C, f x) + ∑ x ∈ Cᶜ, f x := by
    intro f
    rw [← Finset.sum_union disjoint_compl_right, Finset.union_compl]
  have deg : ∀ x, G.degree x = ∑ y : Fin n, if G.Adj x y then 1 else 0 := by
    intro x
    rw [Finset.sum_boole, ← G.card_neighborFinset_eq_degree]
    simp [SimpleGraph.neighborFinset_eq_filter]
  rw [← G.sum_degrees_eq_twice_card_edges]
  simp_rw [deg, split]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have cross : (∑ x ∈ C, ∑ y ∈ Cᶜ, if G.Adj x y then 1 else 0) =
      ∑ x ∈ Cᶜ, ∑ y ∈ C, if G.Adj x y then 1 else 0 := by
    rw [Finset.sum_comm]
    simp_rw [G.adj_comm]
  rw [cross]
  omega

/-- Removing a set with uniformly bounded cross degrees bounds the lost edges. -/
theorem deletion_bound {n d : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Finset (Fin n))
    (hc : ∀ x ∉ C, (C.filter (G.Adj x)).card ≤ d) :
    2 * G.edgeFinset.card ≤
      2 * (G.comap (Cᶜ.orderEmbOfFin rfl)).edgeFinset.card +
      C.card * (C.card - 1) + 2 * d * Cᶜ.card := by
  classical
  have internal : (∑ x ∈ C, ∑ y ∈ C, if G.Adj x y then 1 else 0) ≤
      C.card * (C.card - 1) := by
    calc
      _ ≤ ∑ _ ∈ C, (C.card - 1) := by
        apply Finset.sum_le_sum
        intro x hx
        rw [Finset.sum_boole]
        calc
          _ ≤ (C.erase x).card := Finset.card_le_card (by
            intro y hy
            exact Finset.mem_erase.mpr
              ⟨(G.ne_of_adj (Finset.mem_filter.mp hy).2).symm,
                (Finset.mem_filter.mp hy).1⟩)
          _ = C.card - 1 := Finset.card_erase_of_mem hx
      _ = _ := by simp
  have cross : (∑ x ∈ Cᶜ, ∑ y ∈ C, if G.Adj x y then 1 else 0) ≤ d * Cᶜ.card := by
    calc
      _ ≤ ∑ _ ∈ Cᶜ, d := by
        apply Finset.sum_le_sum
        intro x hx
        rw [Finset.sum_boole]
        exact hc x (Finset.mem_compl.mp hx)
      _ = _ := by simp [Nat.mul_comm]
  have remain : (∑ x ∈ Cᶜ, ∑ y ∈ Cᶜ, if G.Adj x y then 1 else 0) =
      2 * (G.comap (Cᶜ.orderEmbOfFin rfl)).edgeFinset.card := by
    let e := Cᶜ.orderEmbOfFin rfl
    have sum_e : ∀ f : Fin n → ℕ,
        (∑ x ∈ Cᶜ, f x) = ∑ i : Fin Cᶜ.card, f (e i) := by
      intro f
      conv_lhs => rw [← Cᶜ.image_orderEmbOfFin_univ rfl]
      rw [Finset.sum_image]
      exact fun x _ y _ hxy => e.injective hxy
    simp_rw [sum_e]
    rw [← (G.comap e).sum_degrees_eq_twice_card_edges]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.sum_boole, ← (G.comap e).card_neighborFinset_eq_degree]
    simp [SimpleGraph.neighborFinset_eq_filter, SimpleGraph.comap_adj, e]
  rw [edge_partition G C, remain]
  nlinarith

/-- Two missing neighbors across each saturated clique improve the Turán density bound. -/
theorem density_of_clique_separation {r : ℕ} (hr : 2 ≤ r) :
    ∀ n, r + 2 ≤ n → ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ (m : ℕ) (e : Fin m ↪o Fin n) (C : Finset (Fin m)),
        (G.comap e).IsNClique (r + 1) C → ∀ x ∉ C,
          ∃ u ∈ C, ∃ v ∈ C, u ≠ v ∧
            ¬(G.comap e).Adj x u ∧ ¬(G.comap e).Adj x v) →
      2 * r * G.edgeFinset.card ≤ (r - 1) * n ^ 2 := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn G _ hsep
    by_cases hfree : G.CliqueFree (r + 1)
    · obtain ⟨H, _, hH⟩ := SimpleGraph.exists_isTuranMaximal (V := Fin n) (by omega : 0 < r)
      have hle := hH.2 hfree
      have he := hH.nonempty_iso_turanGraph.some.card_edgeFinset_eq
      have hturan := SimpleGraph.mul_card_edgeFinset_turanGraph_le
        (n := Fintype.card (Fin n)) (r := r)
      rw [← he] at hturan
      simp only [Fintype.card_fin] at hturan
      calc
        2 * r * G.edgeFinset.card ≤ 2 * r * H.edgeFinset.card :=
          Nat.mul_le_mul_left _ hle
        _ ≤ _ := hturan
    · obtain ⟨C, hC⟩ := not_forall.mp hfree
      replace hC := not_not.mp hC
      let D := Cᶜ
      let s := D.card
      let e := D.orderEmbOfFin rfl
      have hcard : C.card = r + 1 := hC.card_eq
      have hs : s + (r + 1) = n := by
        have h := Finset.card_compl C
        simp only [Fintype.card_fin] at h
        have hle : C.card ≤ n := by simpa using C.card_le_univ
        dsimp [s, D]
        omega
      have hcross : ∀ x ∉ C, (C.filter (G.Adj x)).card ≤ r - 1 := by
        intro x hx
        obtain ⟨u, hu, v, hv, huv, hxu, hxv⟩ :=
          hsep n (OrderIso.refl _).toOrderEmbedding C hC x hx
        have sub : C.filter (G.Adj x) ⊆ (C.erase u).erase v := by
          intro y hy
          obtain ⟨hyC, hxy⟩ := Finset.mem_filter.mp hy
          exact Finset.mem_erase.mpr ⟨(fun h => hxv (h ▸ hxy)),
            Finset.mem_erase.mpr ⟨(fun h => hxu (h ▸ hxy)), hyC⟩⟩
        calc
          _ ≤ ((C.erase u).erase v).card := Finset.card_le_card sub
          _ = r - 1 := by
            rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨huv.symm, hv⟩),
              Finset.card_erase_of_mem hu, hcard]
            omega
      have bound := deletion_bound G C hcross
      change 2 * G.edgeFinset.card ≤
        2 * (G.comap e).edgeFinset.card + C.card * (C.card - 1) + 2 * (r - 1) * s at bound
      rw [hcard] at bound
      have hspos : 1 ≤ s := by omega
      have hslt : s < n := by omega
      have hrone : 1 ≤ r := by omega
      simp only [Nat.add_sub_cancel] at bound
      have hbound := Nat.mul_le_mul_left r bound
      conv_rhs => rw [← hs]
      by_cases hsmall : s ≤ r + 1
      · have hrem : 2 * (G.comap e).edgeFinset.card ≤ s * (s - 1) := by
          have hc := (G.comap e).card_edgeFinset_le_card_choose_two
          simp only [Fintype.card_fin, Nat.choose_two_right] at hc
          have hd := Nat.mul_div_le (s * (s - 1)) 2
          nlinarith
        have hpositive : 0 ≤ (s - 1) * (r + 1 - s) + 2 * (r - 2) * s :=
          Nat.zero_le _
        have hremr := Nat.mul_le_mul_left r hrem
        zify [hrone, hspos, hsmall, hr] at hbound hremr hpositive ⊢
        nlinarith only [hbound, hremr, hpositive]
      · have hrem := ih s hslt (by omega) (G.comap e) (fun m f => hsep m (f.trans e))
        have hstrict : r + 1 ≤ 2 * (r - 1) * s := by
          have h1 : 1 ≤ r - 1 := by omega
          have h2 : r + 2 ≤ s := by omega
          nlinarith
        zify [hrone] at hbound hrem hstrict ⊢
        nlinarith only [hbound, hrem, hstrict]

/-- At the Ramsey host order, the two complementary density bounds are incompatible. -/
theorem density_conflict {a r : ℕ} (ha : 3 ≤ a) (hr : 2 ≤ r)
    (G : SimpleGraph (Fin (1 + (a - 1) * r))) [DecidableRel G.Adj]
    (hsparse : 2 * G.edgeFinset.card ≤ (a - 2) * (1 + (a - 1) * r))
    (hsep : ∀ (m : ℕ) (e : Fin m ↪o Fin (1 + (a - 1) * r)) (C : Finset (Fin m)),
      (Gᶜ.comap e).IsNClique (r + 1) C → ∀ x ∉ C,
        ∃ u ∈ C, ∃ v ∈ C, u ≠ v ∧
          ¬(Gᶜ.comap e).Adj x u ∧ ¬(Gᶜ.comap e).Adj x v) : False := by
  classical
  let N := 1 + (a - 1) * r
  have hN : r + 2 ≤ N := by
    dsimp [N]
    have ha' : 2 ≤ a - 1 := by omega
    nlinarith
  have hblue := density_of_clique_separation hr N hN Gᶜ hsep
  have partition : 2 * G.edgeFinset.card + 2 * Gᶜ.edgeFinset.card = N * (N - 1) := by
    rw [← G.sum_degrees_eq_twice_card_edges, ← Gᶜ.sum_degrees_eq_twice_card_edges,
      ← Finset.sum_add_distrib]
    calc
      _ = ∑ _ : Fin N, (N - 1) := by
        apply Finset.sum_congr rfl
        intro v hv
        rw [G.degree_compl, Fintype.card_fin]
        have hvdegree := G.degree_lt_card_verts v
        simp only [Fintype.card_fin] at hvdegree
        omega
      _ = _ := by simp
  have hsparse' := Nat.mul_le_mul_left r hsparse
  dsimp [N] at hblue partition hN
  simp only [Nat.add_sub_cancel_left] at partition
  have hpartition := congrArg (fun x : ℕ => r * x) partition
  have haone : 1 ≤ a := by omega
  have hatwo : 2 ≤ a := by omega
  have hrone : 1 ≤ r := by omega
  zify [haone, hatwo, hrone] at hblue hpartition hsparse' hN ha hr
  nlinarith only [hblue, hpartition, hsparse', hN, hr]

/-- A graph below the alternating-path edge bound forces a complementary monotone copy. -/
theorem forces_monotone {a b : ℕ} (ha : 3 ≤ a) (hb : 4 ≤ b)
    (G : SimpleGraph (Fin (1 + (a - 1) * (b - 2)))) [DecidableRel G.Adj]
    (hsparse : 2 * G.edgeFinset.card ≤ (a - 2) * (1 + (a - 1) * (b - 2))) :
    CyclicEmbeddable (monoPath b) Gᶜ := by
  classical
  by_contra havoid
  apply density_conflict ha (by omega : 2 ≤ b - 2) G hsparse
  intro m e C hC x hx
  apply saturated_clique_non_neighbors (by omega : 3 ≤ b)
    (Gᶜ.comap e) _ C hC.isClique (by have hc := hC.card_eq; omega) x hx
  rintro ⟨s, ψ, hψ, he⟩
  exact havoid ⟨s, e ∘ ψ, e.strictMono.comp hψ, he⟩

end D5.S3.Combinatorics.DihedralRamsey.MonotoneRamseyDensity
