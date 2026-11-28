/- GID: D5/S3/Combinatorics/Graph/CubicGraphs/CubicSquareCompletion
   generality: G
   mirror-B: none(waiver:covered-by-q9-square-mask-graph-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Square completion at cubic neighbors of a vertex forces complete bipartite structure. -/

module

public import OmegaBuild.Commands
public import Mathlib.Combinatorics.SimpleGraph.LapMatrix

/-!
Omega original.

Square completion at cubic neighbors of a vertex forces complete bipartite structure.
-/

compile_only_with_mathlib

@[expose] public section

set_option autoImplicit false

namespace Omega.CubicSquareCompletion

open Finset

/-- With two nonneighbors of the distinguished vertex and cubic neighbors,
the square law forces both cubicity and the complete bipartite structure. -/
theorem complete_bipartite {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h : V)
    (hmin : 3 ≤ G.degree h) (hmax : G.degree h ≤ 4)
    (hcard : Fintype.card V = G.degree h + 3)
    (hcubic : ∀ v ≠ h, G.degree v = 3)
    (hsquare : ∀ {a b c}, G.Adj a b → G.Adj a c → b ≠ c →
      G.degree a = 3 → G.degree b = 3 →
      ∃ d, d ≠ a ∧ G.Adj b d ∧ G.Adj c d) :
    G.degree h = 3 ∧ ∀ a b, G.Adj a b ↔
      (G.Adj h a ∧ ¬ G.Adj h b) ∨ (¬ G.Adj h a ∧ G.Adj h b) := by
  let A := G.neighborFinset h
  let B := (univ.erase h) \ A
  have hAm (v : V) : v ∈ A ↔ G.Adj h v := by simp [A]
  have hhA : h ∉ A := fun hm => (G.ne_of_adj ((hAm h).mp hm)) rfl
  have hAs : A ⊆ univ.erase h := by
    intro v hv
    exact mem_erase.mpr ⟨fun he => hhA (he ▸ hv), mem_univ _⟩
  have hAc : A.card = G.degree h := rfl
  have hBc : B.card = 2 := by
    simp [B, card_sdiff_of_subset hAs, hAc, hcard]
  let N (S : Finset V) (v : V) := S.filter (G.Adj v)
  let n (S : Finset V) (v : V) := (N S v).card
  have hN (S : Finset V) (u v : V) : v ∈ N S u ↔ v ∈ S ∧ G.Adj u v := by
    simp [N]
  have hroot (v : V) : (if G.Adj v h then 1 else 0 : ℕ) = if v ∈ A then 1 else 0 := by
    have he : G.Adj v h ↔ v ∈ A := (G.adj_comm v h).trans (hAm v).symm
    simp [he]
  have hdeg (v : V) : G.degree v = n A v + n B v + if v ∈ A then 1 else 0 := by
    have hu : A ∪ B = univ.erase h := by simp [B, hAs]
    have hdis : Disjoint A B := disjoint_left.mpr (fun _ ha hb => (mem_sdiff.mp hb).2 ha)
    have hsplit : (∑ x ∈ A ∪ B, if G.Adj v x then 1 else 0 : ℕ) = n A v + n B v := by
      rw [sum_union hdis]
      simp [n, N]
    have hfull := G.degree_eq_sum_if_adj (R := ℕ) v
    change G.degree v = (∑ x : V, if G.Adj v x then 1 else 0 : ℕ) at hfull
    rw [← sum_erase_add univ (fun x => if G.Adj v x then 1 else 0) (mem_univ h),
      ← hu, hsplit, hroot] at hfull
    exact hfull
  have hArow (a : V) (ha : a ∈ A) : n A a + n B a = 2 := by
    have hd := hdeg a
    have ha' := hcubic a (mem_erase.mp (hAs ha)).1
    rw [ha', ite_eq_left ha] at hd
    omega
  have hBrow (a : V) (ha : a ∈ B) : n A a + n B a = 3 := by
    have hd := hdeg a
    have hmem := mem_sdiff.mp ha
    rw [hcubic a (mem_erase.mp hmem.1).1, ite_eq_right hmem.2, Nat.add_zero] at hd
    exact hd.symm
  have hcross : (∑ a ∈ A, n B a) = ∑ b ∈ B, n A b := by
    have hsum (S : Finset V) (a : V) :
        n S a = (∑ b ∈ S, if G.Adj a b then 1 else 0 : ℕ) := (sum_boole _ _).symm
    simp only [hsum]
    calc
      _ = ∑ b ∈ B, ∑ a ∈ A, if G.Adj a b then 1 else 0 := sum_comm
      _ = _ := sum_congr rfl fun b _ => sum_congr rfl fun a _ => by simp [(G.adj_comm a b)]
  have hsumA : (∑ a ∈ A, n A a) + (∑ a ∈ A, n B a) = 2 * G.degree h := by
    rw [← sum_add_distrib]
    calc
      _ = ∑ _ ∈ A, 2 := sum_congr rfl hArow
      _ = _ := by simp [hAc, Nat.mul_comm]
  have hsumB : (∑ b ∈ B, n A b) + (∑ b ∈ B, n B b) = 6 := by
    rw [← sum_add_distrib]
    calc
      _ = ∑ _ ∈ B, 3 := sum_congr rfl hBrow
      _ = 6 := by simp [hBc]
  have hupperB : (∑ b ∈ B, n B b) ≤ 2 := by
    calc
      _ ≤ ∑ _ ∈ B, 1 := by
        apply sum_le_sum
        intro b hb
        have hsub : N B b ⊆ B.erase b := by
          intro x hx
          obtain ⟨hxB, hbx⟩ := (hN B b x).mp hx
          exact mem_erase.mpr ⟨fun he => (G.ne_of_adj hbx) he.symm, hxB⟩
        have he := card_le_card hsub
        rw [card_erase_of_mem hb, hBc] at he
        exact he
      _ = 2 := by simp [hBc]
  have hbound : (∑ a ∈ A, n A a) ≤ 4 := by omega
  have htwo {a b : V} (ha : a ∈ A) (hb : b ∈ A) (hab : G.Adj a b) : n A a = 2 := by
    have ha' := hcubic a (mem_erase.mp (hAs ha)).1
    have hb' := hcubic b (mem_erase.mp (hAs hb)).1
    have hbh : G.Adj b h := ((hAm b).mp hb).symm
    have hha : h ≠ a := (mem_erase.mp (hAs ha)).1.symm
    obtain ⟨d, hdb, had, hhd⟩ := hsquare hab.symm hbh hha.symm hb' ha'
    have hld : 2 ≤ n A a := one_lt_card.mpr
      ⟨b, (hN A a b).mpr ⟨hb, hab⟩, d, (hN A a d).mpr ⟨(hAm d).mpr hhd, had⟩, hdb.symm⟩
    have hw := hArow a ha
    omega
  have hzero (a : V) (ha : a ∈ A) : n A a = 0 := by
    by_contra hna
    have hna : 0 < n A a := Nat.pos_of_ne_zero hna
    obtain ⟨b, hb⟩ := card_pos.mp hna
    obtain ⟨hbA, hab⟩ := (hN A a b).mp hb
    have ha₂ := htwo ha hbA hab
    obtain ⟨c, hc, hcb⟩ := exists_mem_ne (s := N A a) (by change 1 < n A a; omega) b
    obtain ⟨hcA, hac⟩ := (hN A a c).mp hc
    have hb₂ := htwo hbA ha hab.symm
    have hc₂ := htwo hcA ha hac.symm
    have hab' : a ≠ b := fun he => (G.ne_of_adj hab) he
    have hac' : a ≠ c := fun he => (G.ne_of_adj hac) he
    have htriple : ({a, b, c} : Finset V) ⊆ A :=
      insert_subset ha (insert_subset hbA (singleton_subset_iff.mpr hcA))
    have hlower := sum_le_sum_of_subset_of_nonneg (f := n A) htriple (fun _ _ _ => Nat.zero_le _)
    simp [hab', hac', hcb.symm, ha₂, hb₂, hc₂] at hlower
    omega
  have hiA : (∑ a ∈ A, n A a) = 0 := sum_eq_zero hzero
  have hd : G.degree h = 3 := by omega
  have hiB : (∑ b ∈ B, n B b) = 0 := by omega
  have hzB {b : V} (hb : b ∈ B) : n B b = 0 := by
    have hle := single_le_sum (f := n B) (fun _ _ => Nat.zero_le _) hb
    omega
  have hnB {a : V} (ha : a ∈ A) : N B a = B := by
    have hn := hArow a ha
    rw [hzero a ha, Nat.zero_add] at hn
    apply eq_of_subset_of_card_le (filter_subset _ _)
    change B.card ≤ n B a
    rw [hBc, hn]
  have neighborA {a b : V} (ha : a ∈ A) : G.Adj a b ↔ b ∉ A := by
    constructor
    · intro hab hb
      have hn := htwo ha hb hab
      rw [hzero a ha] at hn
      omega
    · intro hb
      by_cases he : b = h
      · exact he.symm ▸ ((hAm a).mp ha).symm
      · have hbB : b ∈ B := mem_sdiff.mpr ⟨mem_erase.mpr ⟨he, mem_univ _⟩, hb⟩
        have hbN : b ∈ N B a := (hnB ha).symm ▸ hbB
        exact ((hN B a b).mp hbN).2
  refine ⟨hd, fun a b => ?_⟩
  change G.Adj a b ↔ (G.Adj h a ∧ ¬ G.Adj h b) ∨ (¬ G.Adj h a ∧ G.Adj h b)
  rw [← hAm a, ← hAm b]
  by_cases ha : a ∈ A
  · simpa [ha] using (neighborA (b := b) ha)
  by_cases hb : b ∈ A
  · simpa [ha, hb] using (G.adj_comm a b).trans (neighborA (b := a) hb)
  simp [ha, hb]
  intro hab
  have hah : a ≠ h := by
    intro he
    exact hb ((hAm b).mpr (he ▸ hab))
  have hbh : b ≠ h := by
    intro he
    exact ha ((hAm a).mpr (he ▸ hab).symm)
  have haB : a ∈ B := mem_sdiff.mpr ⟨mem_erase.mpr ⟨hah, mem_univ _⟩, ha⟩
  have hbB : b ∈ B := mem_sdiff.mpr ⟨mem_erase.mpr ⟨hbh, mem_univ _⟩, hb⟩
  have hn : 0 < n B a := card_pos.mpr ⟨b, (hN B a b).mpr ⟨hbB, hab⟩⟩
  rw [hzB haB] at hn
  omega

end Omega.CubicSquareCompletion
