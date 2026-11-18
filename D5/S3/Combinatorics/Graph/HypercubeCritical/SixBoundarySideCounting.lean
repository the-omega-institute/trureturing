/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/SixBoundarySideCounting
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/SixBoundarySideCounting
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Girth]
   utility: none
   digest: Private actual path counts for the six-boundary side gap. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.GirthSliceCounting
import Batteries.Tactic.OpenPrivate

/-! The right side may have degrees zero and one; all path counts use actual
neighbors and retain the original left roots. -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.SixBoundarySideGap

open scoped BigOperators Classical
open SimpleGraph GirthSliceCounting
attribute [local instance] Classical.propDecidable
open private threePaths one_three_paths_card_le_rectangle
  one_paths_card_eq_three_mul three_paths_card_eq_sum_local localThreeCount
  forwardWeight forwardWeight_add_one sum_high_neighbors from
  D5.S3.Combinatorics.Graph.HypercubeCritical.GirthSliceCounting

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} {L R : Finset V}

private def degreeSlice (G : SimpleGraph V) (S : Finset V) (j : ℕ) : Finset V :=
  S.filter (fun x => G.degree x = j)

private theorem neighbors_left
    (hb : G.IsBipartiteWith (L : Set V) (R : Set V))
    {y : V} (hy : y ∈ R) : G.neighborFinset y ⊆ L := by
  intro x hx
  exact hb.mem_of_mem_adj' hy ((G.mem_neighborFinset _ _).mp hx).symm

private theorem side_path_bound
    (hb : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hd : ∀ x ∈ L, G.degree x = 3) (hg : (8 : ℕ∞) ≤ G.egirth) :
    3 * L.card + ∑ y ∈ R, 2 * G.degree y * (G.degree y - 1) ≤
      L.card * R.card := by
  have hL : degreeThree G L = L := Finset.filter_eq_self.mpr hd
  have hn (y : V) (hy : y ∈ R) :
      degreeThree G (G.neighborFinset y) = G.neighborFinset y := by
    apply Finset.filter_eq_self.mpr
    intro x hx
    exact hd x (neighbors_left hb hy hx)
  have hl (y : V) (hy : y ∈ R) :
      localThreeCount G y = 2 * G.degree y * (G.degree y - 1) := by
    unfold localThreeCount
    rw [hn y hy]
    have hw (w : V) (hw : w ∈ G.neighborFinset y) : forwardWeight G y w = 2 := by
      have h := forwardWeight_add_one hw
      have h3 := hd w (neighbors_left hb hy hw)
      omega
    calc
      _ = ∑ v ∈ G.neighborFinset y,
          ∑ _w ∈ (G.neighborFinset y).erase v, 2 := by
        apply Finset.sum_congr rfl
        intro v hv
        apply Finset.sum_congr rfl
        intro w hw'
        exact hw w (Finset.mem_of_mem_erase hw')
      _ = ∑ _v ∈ G.neighborFinset y, 2 * (G.degree y - 1) := by
        apply Finset.sum_congr rfl
        intro v hv
        simp [Finset.card_erase_of_mem hv, SimpleGraph.card_neighborFinset_eq_degree,
          Nat.mul_comm]
      _ = _ := by simp [SimpleGraph.card_neighborFinset_eq_degree]; ring
  have hpaths : (threePaths G L).card =
      ∑ y ∈ R, 2 * G.degree y * (G.degree y - 1) := by
    rw [← hL, three_paths_card_eq_sum_local hb]
    exact Finset.sum_congr rfl hl
  have h := one_three_paths_card_le_rectangle L (Finset.Subset.refl L) hb hg
  rw [one_paths_card_eq_three_mul L hd, hpaths] at h
  exact h

private theorem degree_slices_sum (S : Finset V)
    (h : ∀ y ∈ S, G.degree y ≤ 3) (f : ℕ → ℕ) :
    (∑ y ∈ S, f (G.degree y)) =
      (degreeSlice G S 0).card * f 0 + (degreeSlice G S 1).card * f 1 +
      (degreeSlice G S 2).card * f 2 + (degreeSlice G S 3).card * f 3 := by
  have hp (y : V) (hy : y ∈ S) :
      f (G.degree y) = (if G.degree y = 0 then f 0 else 0) +
        (if G.degree y = 1 then f 1 else 0) +
        (if G.degree y = 2 then f 2 else 0) +
        (if G.degree y = 3 then f 3 else 0) := by
    have hh := h y hy
    interval_cases hj : G.degree y <;> simp [hj]
  rw [Finset.sum_congr rfl hp]
  simp only [Finset.sum_add_distrib]
  simp [degreeSlice, ← Finset.sum_filter]

private theorem side_spectrum
    (hb : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hd : ∀ x ∈ L, G.degree x = 3)
    (hr : ∀ y ∈ R, G.degree y ≤ 3) (hg : (8 : ℕ∞) ≤ G.egirth) :
    (degreeSlice G R 0).card + (degreeSlice G R 1).card +
        (degreeSlice G R 2).card + (degreeSlice G R 3).card = R.card ∧
      (degreeSlice G R 1).card + 2 * (degreeSlice G R 2).card +
        3 * (degreeSlice G R 3).card = 3 * L.card ∧
      3 * L.card + 4 * (degreeSlice G R 2).card +
        12 * (degreeSlice G R 3).card ≤ L.card * R.card := by
  have hc := degree_slices_sum R hr (fun _ => 1)
  have he := SimpleGraph.isBipartiteWith_sum_degrees_eq (s := L) (t := R) hb
  have hL : (∑ x ∈ L, G.degree x) = 3 * L.card := by
    rw [Finset.sum_congr rfl hd]
    simp [Nat.mul_comm]
  rw [hL, degree_slices_sum R hr (fun d => d)] at he
  have hp := side_path_bound hb hd hg
  rw [degree_slices_sum R hr (fun d => 2 * d * (d - 1))] at hp
  simp only [mul_one, mul_zero, zero_add, id_eq] at hc he hp
  norm_num at hp
  exact ⟨by simpa using hc.symm, by omega, by omega⟩

private theorem small_side_cases
    (hb : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hd : ∀ x ∈ L, G.degree x = 3)
    (hr : ∀ y ∈ R, G.degree y ≤ 3) (hg : (8 : ℕ∞) ≤ G.egirth)
    (hcard : R.card = L.card + 2) :
    L.card = 0 ∨ L.card = 1 ∨ L.card = 11 ∨ L.card = 12 ∨ 13 ≤ L.card := by
  obtain ⟨hc, he, hp⟩ := side_spectrum hb hd hr hg
  have hpoly : 13 * L.card + 12 * (degreeSlice G R 0).card +
      4 * (degreeSlice G R 1).card ≤ L.card * L.card + 24 := by
    rw [hcard] at hc hp
    nlinarith
  by_cases hbig : 13 ≤ L.card
  · exact Or.inr (Or.inr (Or.inr (Or.inr hbig)))
  have h2 : L.card ≠ 2 := by
    intro h2
    have hz : (degreeSlice G R 3).card = 0 := by
      apply Finset.card_eq_zero.mpr
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro y hy
      obtain ⟨hyR, hy3⟩ := Finset.mem_filter.mp hy
      have hh := Finset.card_le_card (neighbors_left hb hyR)
      rw [SimpleGraph.card_neighborFinset_eq_degree, hy3, h2] at hh
      omega
    simp only [hcard, h2, hz] at hc he hp
    omega
  interval_cases hh : L.card <;> omega

private theorem singleton_three_paths (x : V) :
    (threePaths G {x}).card =
      ∑ y ∈ G.neighborFinset x, ∑ z ∈ (G.neighborFinset y).erase x,
        ((G.neighborFinset z).erase y).card := by
  let S := (G.neighborFinset x).sigma fun y =>
    ((G.neighborFinset y).erase x).sigma fun z => (G.neighborFinset z).erase y
  have hh : (threePaths G {x}).card = S.card := by
    apply Finset.card_bij (fun q _ => ⟨q.first, q.second, q.endpoint⟩)
    · intro q hq
      have h : q.root = x ∧ G.Adj q.root q.first ∧ G.Adj q.first q.second ∧
          G.Adj q.second q.endpoint ∧ q.root ≠ q.second ∧ q.first ≠ q.endpoint := by
        simpa [threePaths] using hq
      rcases h with ⟨rfl, hxy, hyz, hzt, hxz, hyt⟩
      exact Finset.mem_sigma.mpr ⟨(G.mem_neighborFinset _ _).mpr hxy,
        Finset.mem_sigma.mpr ⟨Finset.mem_erase.mpr
          ⟨hxz.symm, (G.mem_neighborFinset _ _).mpr hyz⟩,
          Finset.mem_erase.mpr ⟨hyt.symm, (G.mem_neighborFinset _ _).mpr hzt⟩⟩⟩
    · intro q hq q' hq' he
      have hroot : q.root = x := by simpa [threePaths] using (Finset.mem_filter.mp hq).2.1
      have hroot' : q'.root = x := by simpa [threePaths] using (Finset.mem_filter.mp hq').2.1
      have hy := congrArg (fun t : Σ _y : V, Σ _z : V, V => t.1) he
      have hz := congrArg (fun t : Σ _y : V, Σ _z : V, V => t.2.1) he
      have ht := congrArg (fun t : Σ _y : V, Σ _z : V, V => t.2.2) he
      cases q; cases q'; simp_all
    · rintro ⟨y, z, t⟩ h
      obtain ⟨hy, hzt⟩ := Finset.mem_sigma.mp h
      obtain ⟨hz, ht⟩ := Finset.mem_sigma.mp hzt
      refine ⟨⟨x, y, z, t⟩, ?_, rfl⟩
      simp only [threePaths, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_singleton]
      exact ⟨(G.mem_neighborFinset _ _).mp hy,
        (G.mem_neighborFinset _ _).mp (Finset.mem_erase.mp hz).2,
        (G.mem_neighborFinset _ _).mp (Finset.mem_erase.mp ht).2,
        (Finset.mem_erase.mp hz).1.symm, (Finset.mem_erase.mp ht).1.symm⟩
  simpa [S, Finset.card_sigma] using hh

private theorem high_neighbors_le_two
    (hb : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hd : ∀ x ∈ L, G.degree x = 3) (hg : (8 : ℕ∞) ≤ G.egirth)
    (hR : R.card < 15) {x : V} (hx : x ∈ L) :
    (degreeThree G (G.neighborFinset x)).card ≤ 2 := by
  have hdeg := hd x hx
  have hc : (G.neighborFinset x).card = 3 := by
    rw [SimpleGraph.card_neighborFinset_eq_degree, hdeg]
  have hle := Finset.card_le_card (Finset.filter_subset
    (fun y => G.degree y = 3) (G.neighborFinset x))
  by_contra hnot
  have hall : degreeThree G (G.neighborFinset x) = G.neighborFinset x :=
    Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by omega)
  have hy3 (y : V) (hy : y ∈ G.neighborFinset x) : G.degree y = 3 :=
    (Finset.mem_filter.mp (show y ∈ degreeThree G (G.neighborFinset x) from by
      rw [hall]; exact hy)).2
  have hz3 (y z : V) (hy : y ∈ G.neighborFinset x)
      (hz : z ∈ G.neighborFinset y) : G.degree z = 3 := by
    have hyR := hb.mem_of_mem_adj hx ((G.mem_neighborFinset _ _).mp hy)
    exact hd z (neighbors_left hb hyR hz)
  have hp : (threePaths G {x}).card = 12 := by
    rw [singleton_three_paths]
    have he (y : V) (hy : y ∈ G.neighborFinset x) :
        (∑ z ∈ (G.neighborFinset y).erase x,
          ((G.neighborFinset z).erase y).card) = 4 := by
      have hxy : x ∈ G.neighborFinset y :=
        (G.mem_neighborFinset _ _).mpr ((G.mem_neighborFinset _ _).mp hy).symm
      have hz (z : V) (hz : z ∈ (G.neighborFinset y).erase x) :
          ((G.neighborFinset z).erase y).card = 2 := by
        have hzy := (G.mem_neighborFinset _ _).mp (Finset.mem_of_mem_erase hz)
        have hyz : y ∈ G.neighborFinset z := (G.mem_neighborFinset _ _).mpr hzy.symm
        rw [Finset.card_erase_of_mem hyz, SimpleGraph.card_neighborFinset_eq_degree,
          hz3 y z hy (Finset.mem_of_mem_erase hz)]
      rw [Finset.sum_congr rfl hz]
      simp [Finset.card_erase_of_mem hxy, SimpleGraph.card_neighborFinset_eq_degree, hy3 y hy]
    rw [Finset.sum_congr rfl he]
    simp [hc]
  have h := one_three_paths_card_le_rectangle {x}
    (Finset.singleton_subset_iff.mpr hx) hb hg
  rw [one_paths_card_eq_three_mul {x} (by simpa using hdeg), hp] at h
  simp only [Finset.card_singleton, mul_one, one_mul] at h
  omega

private theorem twelve_side_structure
    (hb : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hd : ∀ x ∈ L, G.degree x = 3)
    (hr : ∀ y ∈ R, G.degree y ≤ 3) (hg : (8 : ℕ∞) ≤ G.egirth)
    (hL : L.card = 12) (hR : R.card = 14) :
    (∀ y ∈ R, G.degree y = 2 ∨ G.degree y = 3) ∧
      (degreeThree G R).card = 8 ∧ (degreeTwo G R).card = 6 ∧
      ∀ x ∈ L, (degreeThree G (G.neighborFinset x)).card = 2 := by
  obtain ⟨hc, he, hp⟩ := side_spectrum hb hd hr hg
  have hsum := sum_high_neighbors hb.symm
  have hle (x : V) (hx : x ∈ L) := high_neighbors_le_two hb hd hg (by omega) hx
  have hbound : 3 * (degreeSlice G R 3).card ≤ 24 := by
    have h := Finset.sum_le_sum hle
    rw [hsum] at h
    simpa [degreeThree, degreeSlice, hL] using h
  have hn0 : (degreeSlice G R 0).card = 0 := by nlinarith
  have hn1 : (degreeSlice G R 1).card = 0 := by nlinarith
  have hn3 : (degreeSlice G R 3).card = 8 := by omega
  have hn2 : (degreeSlice G R 2).card = 6 := by omega
  refine ⟨?_, hn3, hn2, ?_⟩
  · intro y hy
    have h0 : G.degree y ≠ 0 := by
      intro h
      have hh : y ∈ degreeSlice G R 0 := Finset.mem_filter.mpr ⟨hy, h⟩
      rw [Finset.card_eq_zero.mp hn0] at hh
      exact Finset.notMem_empty _ hh
    have h1 : G.degree y ≠ 1 := by
      intro h
      have hh : y ∈ degreeSlice G R 1 := Finset.mem_filter.mpr ⟨hy, h⟩
      rw [Finset.card_eq_zero.mp hn1] at hh
      exact Finset.notMem_empty _ hh
    have hh := hr y hy
    omega
  · intro x hx
    have hh := Finset.sum_erase_add L
      (fun z => (degreeThree G (G.neighborFinset z)).card) hx
    have hrest : (∑ z ∈ L.erase x,
        (degreeThree G (G.neighborFinset z)).card) ≤ 22 := by
      calc
        _ ≤ ∑ _z ∈ L.erase x, 2 :=
          Finset.sum_le_sum fun z hz => hle z (Finset.mem_of_mem_erase hz)
        _ = 22 := by simp [Finset.card_erase_of_mem hx, hL]
    have htotal : (∑ z ∈ L, (degreeThree G (G.neighborFinset z)).card) = 24 := by
      have hn3' : (degreeThree G R).card = 8 := hn3
      simpa only [hn3'] using hsum
    have hxle := hle x hx
    omega

private theorem eleven_side_spectrum
    (hb : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hd : ∀ x ∈ L, G.degree x = 3)
    (hr : ∀ y ∈ R, G.degree y ≤ 3) (hg : (8 : ℕ∞) ≤ G.egirth)
    (hL : L.card = 11) (hR : R.card = 13) :
    (∀ y ∈ R, G.degree y = 2 ∨ G.degree y = 3) ∧
      (degreeThree G R).card = 7 ∧ (degreeTwo G R).card = 6 := by
  obtain ⟨hc, he, hp⟩ := side_spectrum hb hd hr hg
  have hn0 : (degreeSlice G R 0).card = 0 := by nlinarith
  have hn1 : (degreeSlice G R 1).card = 0 := by nlinarith
  have hn3 : (degreeSlice G R 3).card = 7 := by omega
  have hn2 : (degreeSlice G R 2).card = 6 := by omega
  refine ⟨?_, hn3, hn2⟩
  intro y hy
  have h0 : G.degree y ≠ 0 := by
    intro h
    have hh : y ∈ degreeSlice G R 0 := Finset.mem_filter.mpr ⟨hy, h⟩
    rw [Finset.card_eq_zero.mp hn0] at hh
    exact Finset.notMem_empty _ hh
  have h1 : G.degree y ≠ 1 := by
    intro h
    have hh : y ∈ degreeSlice G R 1 := Finset.mem_filter.mpr ⟨hy, h⟩
    rw [Finset.card_eq_zero.mp hn1] at hh
    exact Finset.notMem_empty _ hh
  have hh := hr y hy
  omega

private theorem eleven_left_structure
    (hb : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hd : ∀ x ∈ L, G.degree x = 3) (hg : (8 : ℕ∞) ≤ G.egirth)
    (hL : L.card = 11) (hR : R.card = 13)
    (hhigh : (degreeThree G R).card = 7) :
    ∃ r ∈ L, (degreeThree G (G.neighborFinset r)).card = 1 ∧
      ∀ x ∈ L, x ≠ r → (degreeThree G (G.neighborFinset x)).card = 2 := by
  let k (x : V) := (degreeThree G (G.neighborFinset x)).card
  have hk (x : V) (hx : x ∈ L) : k x ≤ 2 := high_neighbors_le_two hb hd hg (by omega) hx
  have hs : (∑ x ∈ L, k x) = 21 := by
    simpa only [hhigh] using sum_high_neighbors hb.symm
  obtain ⟨r, hr, hkr⟩ : ∃ r ∈ L, k r ≠ 2 := by
    by_contra h
    have hh : ∀ r ∈ L, k r = 2 := by simpa using h
    have he := Finset.sum_congr rfl hh
    simp [hL, hs] at he
  have hrle := hk r hr
  have hrest := Finset.sum_erase_add L k hr
  have hrestle : (∑ x ∈ L.erase r, k x) ≤ 20 := by
    calc
      _ ≤ ∑ _x ∈ L.erase r, 2 :=
        Finset.sum_le_sum fun x hx => hk x (Finset.mem_of_mem_erase hx)
      _ = 20 := by simp [Finset.card_erase_of_mem hr, hL]
  have hrone : k r = 1 := by omega
  refine ⟨r, hr, hrone, ?_⟩
  have heq : (∑ x ∈ L.erase r, k x) = ∑ _x ∈ L.erase r, 2 := by
    simp only [Finset.sum_const, smul_eq_mul, Finset.card_erase_of_mem hr, hL]
    omega
  have hall := (Finset.sum_eq_sum_iff_of_le
    (fun x hx => hk x (Finset.mem_of_mem_erase hx))).mp heq
  intro x hx hxr
  exact hall x (Finset.mem_erase.mpr ⟨hxr, hx⟩)

end D5.S3.Combinatorics.Graph.HypercubeCritical.SixBoundarySideGap
