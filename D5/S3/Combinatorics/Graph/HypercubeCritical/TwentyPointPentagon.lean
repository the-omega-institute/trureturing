/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/TwentyPointPentagon
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/TwentyPointPentagon
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Matching]
   utility: none
   digest: Actual perfect matching and complementary pentagons in the twenty-point slice. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyPointSymmetric
import D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyPointGeometry

/-! Actual matching coordinates and the complementary five-cycle relation. -/

set_option autoImplicit false
set_option linter.style.longLine false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyPointPentagon

open SimpleGraph GirthSliceCounting
open D5.S3.Combinatorics.Graph.Hypercube
open BalancedCriticalSpectrum (Q flip IsBalanced)
open private SideHigh compressed compressed_degree from
  D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyPointCompression
open private side_high_neighbors_card from
  D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyPointTheta
open private compressed_distance diff_self diff_symm diff_triangle_card from
  D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyPointGeometry
open private diff diff_flip from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CubeSmallSupport
open private adjacent_exists_flip from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeGirth
open private three_walk_endpoint_injective from
  D5.S3.Combinatorics.Graph.HypercubeCritical.GirthSliceCounting

attribute [local instance] Classical.propDecidable

private theorem cycle_five_degree (i : Fin 5) : (cycleGraph 5).degree i = 2 := by
  revert i
  decide +kernel

private theorem cycle_degree_two {V : Type*} [Fintype V] [DecidableEq V]
    {H : SimpleGraph V} (e : cycleGraph 5 ≃g H) (x : V) : H.degree x = 2 := by
  obtain ⟨i, rfl⟩ := e.surjective x
  exact (e.degree_eq i).trans (cycle_five_degree i)

private theorem paired_cycle_matching
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {L R : Finset V}
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3)
    (hlow : ∀ {v w}, G.Adj v w → G.degree v = 2 → G.degree w = 2 → False)
    (hg : (8 : ℕ∞) ≤ G.egirth)
    (eL : cycleGraph 5 ≃g compressed G L) (eR : cycleGraph 5 ≃g compressed G R) :
    ∃ f : SideHigh G L ≃ SideHigh G R,
      ∀ x y, G.Adj x.val y.val ↔ f x = y := by
  have huniq {P T : Finset V} (hp : G.IsBipartiteWith (P : Set V) (T : Set V))
      (e : cycleGraph 5 ≃g compressed G P) (x : SideHigh G P) :
      ∃! y : SideHigh G T, G.Adj x.val y.val := by
    have hd := compressed_degree hp hdeg hlow hg x
    rw [cycle_degree_two e] at hd
    have hc := side_high_neighbors_card hp (Finset.mem_filter.mp x.property).1
    have hh : (degreeThree G (G.neighborFinset x.val)).card = 1 := by omega
    rw [hh] at hc
    obtain ⟨y, hy⟩ := Finset.card_eq_one.mp hc
    have hiff (z : SideHigh G T) : G.Adj x.val z.val ↔ z = y := by
      have hm : z ∈ (Finset.univ.filter (fun z : SideHigh G T => G.Adj x.val z.val)) ↔ z = y := by
        rw [hy, Finset.mem_singleton]
      simpa using hm
    exact ⟨y, (hiff y).mpr rfl, fun z hz => (hiff z).mp hz⟩
  let f : SideHigh G L → SideHigh G R := fun x => (huniq hpart eL x).choose
  have hf (x : SideHigh G L) : G.Adj x.val (f x).val := (huniq hpart eL x).choose_spec.1
  have hinj : Function.Injective f := by
    intro x y hxy
    have hu := (huniq hpart.symm eR (f x)).choose_spec.2
    exact (hu x (hf x).symm).trans (hu y (by rw [hxy]; exact (hf y).symm)).symm
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨x, hx, _⟩ := huniq hpart.symm eR y
    exact ⟨x, ((huniq hpart eL x).choose_spec.2 y hx.symm).symm⟩
  refine ⟨Equiv.ofBijective f ⟨hinj, hsurj⟩, ?_⟩
  intro x y
  constructor
  · intro hxy
    exact ((huniq hpart eL x).choose_spec.2 y hxy).symm
  · intro hxy
    change f x = y at hxy
    rw [← hxy]
    exact hf x

private theorem matched_compressed_disjoint
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {L R : Finset V}
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hg : (8 : ℕ∞) ≤ G.egirth)
    (f : SideHigh G L ≃ SideHigh G R)
    (hf : ∀ x y, G.Adj x.val y.val ↔ f x = y)
    {x y : SideHigh G L} (hxy : (compressed G L).Adj x y) :
    ¬ (compressed G R).Adj (f x) (f y) := by
  rintro ⟨_, k, hk2, hxk, hyk⟩
  obtain ⟨hne, m, hm2, hxm, hym⟩ := hxy
  have hx3 := (Finset.mem_filter.mp x.property).2
  have hy3 := (Finset.mem_filter.mp y.property).2
  have hxfy : x.val ≠ y.val := fun he => hne (Subtype.ext he)
  have hmy : m ≠ (f y).val := by
    intro he
    have hh := (Finset.mem_filter.mp (f y).property).2
    rw [← he] at hh
    omega
  have hxk' : x.val ≠ k := by intro he; rw [← he] at hk2; omega
  have hff : (f x).val ≠ (f y).val := by
    intro he
    exact hne (f.injective (Subtype.ext he))
  have hh := three_walk_endpoint_injective hpart hg
    (Finset.mem_filter.mp x.property).1 (Finset.mem_filter.mp x.property).1
    hxm hym.symm ((hf y (f y)).mpr rfl)
    ((hf x (f x)).mpr rfl) hxk hyk.symm hxfy hmy hxk' hff ⟨rfl, rfl⟩
  have hm3 := (Finset.mem_filter.mp (f x).property).2
  rw [← hh.2.1] at hm3
  omega

private theorem paired_cycle_labels
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {L R : Finset V}
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3)
    (hlow : ∀ {v w}, G.Adj v w → G.degree v = 2 → G.degree w = 2 → False)
    (hg : (8 : ℕ∞) ≤ G.egirth)
    (eL : cycleGraph 5 ≃g compressed G L) (eR : cycleGraph 5 ≃g compressed G R) :
    ∃ f : SideHigh G L ≃ SideHigh G R,
      (∀ x y, G.Adj x.val y.val ↔ f x = y) ∧
      ∀ i j, (compressed G R).Adj (f (eL i)) (f (eL j)) ↔
        i ≠ j ∧ ¬ (cycleGraph 5).Adj i j := by
  obtain ⟨f, hf⟩ := paired_cycle_matching hpart hdeg hlow hg eL eR
  refine ⟨f, hf, ?_⟩
  intro i
  let N := Finset.univ.filter (fun j => (compressed G R).Adj (f (eL i)) (f (eL j)))
  let T := Finset.univ.filter (fun j => i ≠ j ∧ ¬ (cycleGraph 5).Adj i j)
  have hT : T.card = 2 := by
    change (Finset.univ.filter (fun j => i ≠ j ∧ ¬ (cycleGraph 5).Adj i j)).card = 2
    revert i
    decide +kernel
  have hN : N.card = 2 := by
    calc
      N.card = ((compressed G R).neighborFinset (f (eL i))).card := by
        apply Finset.card_bij (fun j _ => f (eL j))
        · intro j hj
          exact (SimpleGraph.mem_neighborFinset _ _ _).mpr (Finset.mem_filter.mp hj).2
        · intro j _ k _ he
          exact eL.injective (f.injective he)
        · intro y hy
          refine ⟨eL.symm (f.symm y), ?_, by simp⟩
          simpa [N] using (SimpleGraph.mem_neighborFinset _ _ _).mp hy
      _ = 2 := cycle_degree_two eR _
  have hsub : N ⊆ T := by
    intro j hj
    have hadj := (Finset.mem_filter.mp hj).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩
    · intro he; subst j; exact (compressed G R).ne_of_adj hadj rfl
    · intro he
      exact matched_compressed_disjoint hpart hg f hf (eL.map_rel_iff.mpr he) hadj
  have he : N = T := Finset.eq_of_subset_of_card_le hsub (by omega)
  intro j
  have hh : j ∈ N ↔ j ∈ T := by rw [he]
  simpa [N, T] using hh

private theorem direction_avoids_two_step {n : ℕ} {x y : Q n} {i : Fin n}
    (hxy : hammingDist x y = 2) (hno : ¬ (hypercube n).Adj (flip x i) y) :
    x i = y i := by
  by_contra hne
  have hi : i ∈ diff x y := by simp [diff, hne]
  apply hno
  change (diff (flip x i) y).card = 1
  rw [diff_flip, if_pos hi, Finset.card_erase_of_mem hi]
  change (diff x y).card = 2 at hxy
  omega

private theorem matching_direction_bit {n : ℕ}
    (A B : Fin 5 → Q n) (c : Fin 5 → Fin n)
    (hflip : ∀ i, B i = flip (A i) (c i))
    (hno : ∀ i j, i ≠ j → ¬ (hypercube n).Adj (A i) (B j))
    (hA : ∀ i j, (cycleGraph 5).Adj i j → hammingDist (A i) (A j) = 2)
    (hB : ∀ i j, i ≠ j → ¬ (cycleGraph 5).Adj i j →
      hammingDist (B i) (B j) = 2) :
    ∀ i j : Fin 5, i ≠ j →
      (A i (c i) = A j (c i) ↔ (cycleGraph 5).Adj i j ∨ c i = c j) := by
  intro i j hij
  by_cases he : (cycleGraph 5).Adj i j
  · have h := direction_avoids_two_step (hA i j he) (by
      rw [← hflip i]
      exact fun hh => hno j i hij.symm hh.symm)
    simp [he, h]
  · have hBi := direction_avoids_two_step (hB i j hij he) (by
      rw [hflip i, BalancedCriticalSpectrum.flip_flip]
      exact hno i j hij)
    rw [hflip i, hflip j] at hBi
    by_cases hc : c i = c j
    · simp [hc, BalancedCriticalSpectrum.flip] at hBi
      simp [he, hc, hBi]
    · have hci : c j ≠ c i := Ne.symm hc
      simp only [BalancedCriticalSpectrum.flip_apply_same,
        BalancedCriticalSpectrum.flip, Function.update_of_ne hci] at hBi
      have hn : A i (c i) ≠ A j (c i) := by
        cases ha : A i (c i) <;> cases hb : A j (c i) <;> simp_all
      simp [he, hc, hn]

private theorem direction_fiber_dichotomy {n : ℕ}
    (A B : Fin 5 → Q n) (c : Fin 5 → Fin n)
    (hflip : ∀ i, B i = flip (A i) (c i))
    (hno : ∀ i j, i ≠ j → ¬ (hypercube n).Adj (A i) (B j))
    (hA : ∀ i j, (cycleGraph 5).Adj i j → hammingDist (A i) (A j) = 2)
    (hB : ∀ i j, i ≠ j → ¬ (cycleGraph 5).Adj i j →
      hammingDist (B i) (B j) = 2) :
    (∀ i, c i = c 0) ∨ Function.Injective c := by
  have hbit := matching_direction_bit A B c hflip hno hA hB
  have hmodule (t : Fin n) :
      ∀ i ∈ Finset.univ.filter (fun i => c i = t),
        ∀ j ∈ Finset.univ.filter (fun j => c j = t),
          ∀ k ∉ Finset.univ.filter (fun k => c k = t),
            (cycleGraph 5).Adj i k ↔ (cycleGraph 5).Adj j k := by
    intro i hi j hj k hk
    have hi' : c i = t := (Finset.mem_filter.mp hi).2
    have hj' : c j = t := (Finset.mem_filter.mp hj).2
    have hk' : c k ≠ t := by simpa using hk
    have hik : i ≠ k := by intro he; subst k; exact hk' hi'
    have hjk : j ≠ k := by intro he; subst k; exact hk' hj'
    have hijbit : A i t = A j t := by
      by_cases hij : i = j
      · rw [hij]
      · have hh := (hbit i j hij).mpr (Or.inr (hi'.trans hj'.symm))
        simpa only [hi'] using hh
    have hh1 := hbit i k hik
    have hh2 := hbit j k hjk
    rw [hi'] at hh1
    rw [hj', ← hijbit] at hh2
    simpa [hi', hj', hk'.symm] using hh1.symm.trans hh2
  have hprime : ∀ T : Finset (Fin 5),
      (∀ i ∈ T, ∀ j ∈ T, ∀ k ∉ T,
        (cycleGraph 5).Adj i k ↔ (cycleGraph 5).Adj j k) →
      T.card ≤ 1 ∨ T = Finset.univ := by
    decide +kernel
  by_cases hinj : Function.Injective c
  · exact Or.inr hinj
  · left
    obtain ⟨i, j, hce, hij⟩ := Function.not_injective_iff.mp hinj
    let T := Finset.univ.filter (fun k => c k = c i)
    have hi : i ∈ T := by simp [T]
    have hj : j ∈ T := by simp [T, hce]
    have htwo : 2 ≤ T.card := by
      have hh := Finset.card_le_card (show ({i, j} : Finset (Fin 5)) ⊆ T from by
        intro k hk
        rcases (show k = i ∨ k = j by simpa only [Finset.mem_insert, Finset.mem_singleton] using hk) with rfl | rfl
        · exact hi
        · exact hj)
      simpa [hij] using hh
    rcases hprime T (hmodule (c i)) with hsmall | hall
    · omega
    · have ht (k : Fin 5) : c k = c i := by
        have hk : k ∈ T := by rw [hall]; exact Finset.mem_univ _
        exact (Finset.mem_filter.mp hk).2
      intro k
      exact (ht k).trans (ht 0).symm

private theorem paired_cycle_direction_data {n : ℕ} {S : Finset (Q n)}
    {L R : Finset (S : Set (Q n))}
    (hpart : ((hypercube n).induce (S : Set (Q n))).IsBipartiteWith
      (L : Set (S : Set (Q n))) (R : Set (S : Set (Q n))))
    (hdeg : ∀ v, ((hypercube n).induce (S : Set (Q n))).degree v = 2 ∨
      ((hypercube n).induce (S : Set (Q n))).degree v = 3)
    (hlow : ∀ {v w}, ((hypercube n).induce (S : Set (Q n))).Adj v w →
      ((hypercube n).induce (S : Set (Q n))).degree v = 2 →
      ((hypercube n).induce (S : Set (Q n))).degree w = 2 → False)
    (hbal : IsBalanced S)
    (eL : cycleGraph 5 ≃g compressed ((hypercube n).induce (S : Set (Q n))) L)
    (eR : cycleGraph 5 ≃g compressed ((hypercube n).induce (S : Set (Q n))) R) :
    ∃ f : SideHigh ((hypercube n).induce (S : Set (Q n))) L ≃
        SideHigh ((hypercube n).induce (S : Set (Q n))) R,
      ∃ c : Fin 5 → Fin n,
        (∀ x y, (hypercube n).Adj x.val.val y.val.val ↔ f x = y) ∧
        (∀ i j, (compressed ((hypercube n).induce (S : Set (Q n))) R).Adj
          (f (eL i)) (f (eL j)) ↔ i ≠ j ∧ ¬ (cycleGraph 5).Adj i j) ∧
        (∀ i, (f (eL i)).val.val = flip (eL i).val.val (c i)) ∧
        ((∀ i, c i = c 0) ∨ Function.Injective c) := by
  obtain ⟨f, hf, hc⟩ := paired_cycle_labels hpart hdeg hlow
    (BalancedCubeGirth.eight_le_egirth S hbal) eL eR
  have hedge (i : Fin 5) : (hypercube n).Adj (eL i).val.val (f (eL i)).val.val :=
    (hf (eL i) (f (eL i))).mpr rfl
  choose c hflip using fun i => adjacent_exists_flip (hedge i)
  refine ⟨f, c, hf, hc, hflip, ?_⟩
  apply direction_fiber_dichotomy (fun i => (eL i).val.val)
    (fun i => (f (eL i)).val.val) c hflip
  · intro i j hij hadj
    have he : f (eL i) = f (eL j) := (hf _ _).mp hadj
    exact hij (eL.injective (f.injective he))
  · intro i j hij
    exact compressed_distance (eL.map_rel_iff.mpr hij)
  · intro i j hij hno
    exact compressed_distance ((hc i j).mpr ⟨hij, hno⟩)

#print axioms paired_cycle_direction_data

end D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyPointPentagon
