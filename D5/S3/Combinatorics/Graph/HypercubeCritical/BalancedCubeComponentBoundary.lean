/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCubeComponentBoundary
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/BalancedCubeComponentBoundary
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: Joint exterior-neighbor bound for two separated balanced cubic cube restrictions. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeGirth
import D5.S3.Combinatorics.Graph.HypercubeCritical.SupportedEigenSaturation
import Batteries.Tactic.OpenPrivate

/-! Two disjoint, nonadjacent, balanced cubic restrictions of the nine-cube have
at most six neighbors in total at an exterior vertex meeting both restrictions.
The proof uses exterior Huang eigenvector cancellation and finite sets of coordinate
directions; it assumes no connectivity and performs no enumeration of the cube. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeComponentBoundary

open scoped BigOperators
open D5.S3.Combinatorics.Graph.Hypercube
open BalancedCriticalSpectrum (Q flip IsBalanced switchingVector)
open private huangMatrix from D5.S3.Combinatorics.Graph.HypercubeSubQuorum
open private matrix_support from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCriticalSpectrum
open private flip_comm adjacent_exists_flip from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeGirth
open private selected_neighbor_card from
  D5.S3.Combinatorics.Graph.HypercubeCritical.SupportedEigenSaturation

open Classical in
def directions {n : Nat} (C : Finset (Q n)) (x : Q n) : Finset (Fin n) :=
  Finset.univ.filter fun i => BalancedCriticalSpectrum.flip x i ∈ C

@[simp] private theorem mem_directions {n : Nat} (C : Finset (Q n)) (x : Q n)
    (i : Fin n) : i ∈ directions C x ↔ flip x i ∈ C := by
  simp [directions]

open Classical in
private theorem flip_injective {n : Nat} (x : Q n) : Function.Injective (flip x) := by
  intro i j he
  by_contra hij
  have h := congrFun he i
  cases hxi : x i <;> simp [BalancedCriticalSpectrum.flip, hij, hxi] at h

open Classical in
private theorem directions_card {n : Nat} (C : Finset (Q n)) (x : Q n) :
    (directions C x).card = (C.filter fun y => (hypercube n).Adj x y).card := by
  apply Finset.card_bij (fun i _ => flip x i)
  · intro i hi
    exact Finset.mem_filter.mpr ⟨(mem_directions C x i).mp hi,
      BalancedCriticalSpectrum.flip_adj x i⟩
  · intro i _ j _ he
    exact flip_injective x he
  · intro y hy
    obtain ⟨i, rfl⟩ := adjacent_exists_flip (Finset.mem_filter.mp hy).2
    exact ⟨i, (mem_directions C x i).mpr (Finset.mem_filter.mp hy).1, rfl⟩

open Classical in
theorem regular_directions {n : Nat} (C : Finset (Q n))
    (hr : ((hypercube n).induce (C : Set _)).IsRegularOfDegree 3)
    {x : Q n} (hx : x ∈ C) : (directions C x).card = 3 := by
  rw [directions_card]
  have hf : C.filter (fun y => (hypercube n).Adj x y) =
      (hypercube n).neighborFinset x ∩ C := by
    ext y
    simp [SimpleGraph.mem_neighborFinset, and_comm]
  rw [hf, selected_neighbor_card hx, hr.degree_eq]

open Classical in
private theorem signed_sum_even {α : Type*} (N : Finset α) (a : α → Real)
    (ha : ∀ x ∈ N, a x = 1 ∨ a x = -1) (hz : ∑ x ∈ N, a x = 0) :
    Even N.card := by
  let P := N.filter fun x => a x = 1
  have hp : ∀ x ∈ N, a x = (if a x = 1 then (2 : Real) else 0) - 1 := by
    intro x hx
    rcases ha x hx with h | h <;> norm_num [h]
  have hsum : ∑ x ∈ N, a x = 2 * (P.card : Real) - (N.card : Real) := by
    calc
      ∑ x ∈ N, a x = ∑ x ∈ N, ((if a x = 1 then (2 : Real) else 0) - 1) :=
        Finset.sum_congr rfl hp
      _ = _ := by simp [Finset.sum_sub_distrib, Finset.sum_ite, P, mul_comm]
  have hc : (N.card : Real) = (P.card : Real) + (P.card : Real) := by linarith
  have hn : N.card = P.card + P.card := by exact_mod_cast hc
  exact ⟨P.card, hn⟩

open Classical in
theorem exterior_even (C : Finset (Q 9))
    (hr : ((hypercube 9).induce (C : Set _)).IsRegularOfDegree 3)
    (hb : IsBalanced C) (v : Q 9) (hv : v ∉ C) :
    Even (directions C v).card := by
  obtain ⟨sigma, hs⟩ := hb
  let z := switchingVector C sigma
  let N := C.filter fun x => (hypercube 9).Adj v x
  let a := fun x => huangMatrix 9 v x * z x
  have he := BalancedCriticalSpectrum.ambient_eigenvector (d := 3) C sigma hr hs
  have hrow := SupportedEigenSaturation.selected_eigen_row (d := 3) C z
    (fun x hx => by simp [z, switchingVector, hx]) he v
  have hsumC : ∑ x ∈ C, a x = 0 := by
    simpa [a, z, switchingVector, hv] using hrow
  have hsumN : ∑ x ∈ N, a x = 0 := by
    calc
      ∑ x ∈ N, a x = ∑ x ∈ C, a x := by
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro x hx hxn
        have hna : ¬ (hypercube 9).Adj v x := by
          intro h
          exact hxn (Finset.mem_filter.mpr ⟨hx, h⟩)
        have hm : huangMatrix 9 v x = 0 := by
          apply abs_eq_zero.mp
          rw [matrix_support, ite_eq_right hna]
        simp [a, hm]
      _ = 0 := hsumC
  have ha : ∀ x ∈ N, a x = 1 ∨ a x = -1 := by
    intro x hx
    obtain ⟨hxC, hxadj⟩ := Finset.mem_filter.mp hx
    have hm : |huangMatrix 9 v x| = 1 := by rw [matrix_support, ite_eq_left hxadj]
    have hm' : huangMatrix 9 v x = 1 ∨ huangMatrix 9 v x = -1 := by
      rcases le_total 0 (huangMatrix 9 v x) with h | h
      · left
        rwa [abs_of_nonneg h] at hm
      · right
        rw [abs_of_nonpos h] at hm
        linarith
    rcases hm' with hm' | hm' <;> rcases hs.1 x hxC with hσ | hσ <;>
      simp [a, z, switchingVector, hxC, hm', hσ]
  rw [directions_card]
  exact signed_sum_even N a ha hsumN

open Classical in
private theorem flip_cancel_middle {n : Nat} (v : Q n) (i j : Fin n) :
    flip (flip (flip v i) j) i = flip v j := by
  rw [flip_comm (flip v i) j i, BalancedCriticalSpectrum.flip_flip]

open Classical in
private theorem flip_three_swap {n : Nat} (v : Q n) (i t j : Fin n) :
    flip (flip (flip v i) t) j = flip (flip (flip v j) t) i := by
  rw [flip_comm (flip v i) t j, flip_comm v i j, flip_comm (flip v j) i t]

open Classical in
private theorem cross_two_not_mem {n : Nat} (C D : Finset (Q n))
    (hc : ∀ x ∈ C, ∀ y ∈ D, ¬ (hypercube n).Adj x y)
    (v : Q n) (i j : Fin n) (hj : flip v j ∈ D) :
    flip (flip v i) j ∉ C := by
  intro h
  apply hc _ h _ hj
  rw [flip_comm v i j]
  exact (BalancedCriticalSpectrum.flip_adj (flip v j) i).symm

open Classical in
private def link {n : Nat} (C : Finset (Q n)) (v : Q n)
    (S : Finset (Fin n)) (i : Fin n) : Finset (Fin n) :=
  (S.erase i).filter fun k => flip (flip v i) k ∈ C

open Classical in
private theorem link_subset {n : Nat} (C : Finset (Q n)) (v : Q n)
    (S : Finset (Fin n)) (i : Fin n) : link C v S i ⊆ S.erase i :=
  Finset.filter_subset _ _

open Classical in
private theorem direction_subset {n : Nat} (C D : Finset (Q n))
    (hc : ∀ x ∈ C, ∀ y ∈ D, ¬ (hypercube n).Adj x y)
    (v : Q n) (hv : v ∉ C) (S T : Finset (Fin n)) (t : Fin n)
    (hT : ∀ j ∈ T, flip v j ∈ D)
    (hcover : ∀ k, k ∈ S ∨ k ∈ T ∨ k = t) (i : Fin n) :
    directions C (flip v i) ⊆ insert t (link C v S i) := by
  intro k hk
  have hkm : flip (flip v i) k ∈ C := (mem_directions _ _ _).mp hk
  have hki : k ≠ i := by
    intro he
    subst k
    exact hv (by simpa only [BalancedCriticalSpectrum.flip_flip] using hkm)
  rcases hcover k with hkS | hkT | rfl
  · apply Finset.mem_insert_of_mem
    exact Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hki, hkS⟩, hkm⟩
  · exact (cross_two_not_mem C D hc v i k (hT k hkT) hkm).elim
  · exact Finset.mem_insert_self _ _

open Classical in
private theorem four_degree_two {α : Type*} (S : Finset α) (H : α → Finset α)
    (hS : S.card = 4) (hsub : ∀ i ∈ S, H i ⊆ S.erase i)
    (htri : ∀ i ∈ S, ∀ j ∈ H i, ∀ k ∈ H j, k ∉ H i)
    (hmin : ∀ i ∈ S, 2 ≤ (H i).card) : ∀ i ∈ S, (H i).card = 2 := by
  intro i hi
  have he : (S.erase i).card = 3 := by simp [Finset.card_erase_of_mem hi, hS]
  have hu := Finset.card_le_card (hsub i hi)
  by_contra hn
  have hd : (H i).card = 3 := by
    have := hmin i hi
    omega
  have hall : H i = S.erase i :=
    Finset.eq_of_subset_of_card_le (hsub i hi) (by omega)
  obtain ⟨j, hj⟩ := Finset.card_pos.mp (show 0 < (H i).card by omega)
  have hjS : j ∈ S := (Finset.mem_erase.mp (hsub i hi hj)).2
  have hjsub : H j ⊆ {i} := by
    intro k hk
    apply Finset.mem_singleton.mpr
    by_contra hki
    have hkS : k ∈ S := (Finset.mem_erase.mp (hsub j hjS hk)).2
    have hki' : k ∈ H i := by rw [hall]; exact Finset.mem_erase.mpr ⟨hki, hkS⟩
    exact htri i hi j hj k hk hki'
  have huj := Finset.card_le_card hjsub
  have hlj := hmin j hjS
  simp only [Finset.card_singleton] at huj
  omega

open Classical in
private theorem small_side_impossible {n : Nat} (C D : Finset (Q n))
    (hr : ((hypercube n).induce (C : Set _)).IsRegularOfDegree 3)
    (hc : ∀ x ∈ C, ∀ y ∈ D, ¬ (hypercube n).Adj x y)
    (v : Q n) (hv : v ∉ C) (S T : Finset (Fin n)) (t : Fin n)
    (hS : ∀ i ∈ S, flip v i ∈ C) (hT : ∀ j ∈ T, flip v j ∈ D)
    (hcover : ∀ k, k ∈ S ∨ k ∈ T ∨ k = t) (hcard : S.card = 2) : False := by
  obtain ⟨i, hi⟩ := Finset.card_pos.mp (show 0 < S.card by omega)
  have hthree := regular_directions C hr (hS i hi)
  have hle := Finset.card_le_card (direction_subset C D hc v hv S T t hT hcover i)
  have hle' := Finset.card_insert_le t (link C v S i)
  have hlink := Finset.card_le_card (link_subset C v S i)
  have he : (S.erase i).card = 1 := by simp [Finset.card_erase_of_mem hi, hcard]
  omega

open Classical in
private theorem four_structure {n : Nat} (C D : Finset (Q n))
    (hr : ((hypercube n).induce (C : Set _)).IsRegularOfDegree 3)
    (hb : IsBalanced C)
    (hc : ∀ x ∈ C, ∀ y ∈ D, ¬ (hypercube n).Adj x y)
    (v : Q n) (hv : v ∉ C) (S T : Finset (Fin n)) (t : Fin n)
    (hS : ∀ i ∈ S, flip v i ∈ C) (hT : ∀ j ∈ T, flip v j ∈ D)
    (hcover : ∀ k, k ∈ S ∨ k ∈ T ∨ k = t) (hcard : S.card = 4) :
    (∀ i ∈ S, (link C v S i).card = 2) ∧
      (∀ i ∈ S, flip (flip v i) t ∈ C) := by
  have hmin : ∀ i ∈ S, 2 ≤ (link C v S i).card := by
    intro i hi
    have hthree := regular_directions C hr (hS i hi)
    have hle := Finset.card_le_card (direction_subset C D hc v hv S T t hT hcover i)
    have hle' := Finset.card_insert_le t (link C v S i)
    omega
  have htri : ∀ i ∈ S, ∀ j ∈ link C v S i,
      ∀ k ∈ link C v S j, k ∉ link C v S i := by
    intro i hi j hj k hk hki
    obtain ⟨hje, hjC⟩ := Finset.mem_filter.mp hj
    obtain ⟨hke, hkC⟩ := Finset.mem_filter.mp hk
    obtain ⟨hkie, hkiC⟩ := Finset.mem_filter.mp hki
    obtain ⟨hji, hjS⟩ := Finset.mem_erase.mp hje
    obtain ⟨hkj, _⟩ := Finset.mem_erase.mp hke
    obtain ⟨hki', hkS⟩ := Finset.mem_erase.mp hkie
    have he :
        flip (flip (flip (flip v i) j) i) k =
          flip (flip (flip (flip v i) k) i) j := by
      simpa only [flip_cancel_middle] using flip_comm v j k
    have hfirst : j = k :=
      BalancedCubeGirth.three_step_first_direction_eq hb
        hji hki'.symm hki' hji.symm (hS i hi) hjC
        (by simpa only [flip_cancel_middle] using hS j hjS)
        (by simpa only [flip_cancel_middle] using hkC)
        hkiC
        (by simpa only [flip_cancel_middle] using hS k hkS)
        (by simpa only [flip_cancel_middle, flip_comm v k j] using hkC) he
    exact hkj hfirst.symm
  have hdegree : ∀ i ∈ S, (link C v S i).card = 2 :=
    four_degree_two S (link C v S) hcard
      (fun i _ => by
        simpa only [Finset.subset_iff, Finset.mem_erase] using link_subset C v S i)
      htri hmin
  refine ⟨hdegree, ?_⟩
  intro i hi
  by_contra hn
  have hsub : directions C (flip v i) ⊆ link C v S i := by
    intro k hk
    rcases Finset.mem_insert.mp (direction_subset C D hc v hv S T t hT hcover i hk)
        with hkt | hkH
    · subst k
      exact (hn ((mem_directions _ _ _).mp hk)).elim
    · exact hkH
  have hle := Finset.card_le_card hsub
  have hthree := regular_directions C hr (hS i hi)
  have htwo := hdegree i hi
  omega

open Classical in
private theorem four_four_impossible {n : Nat} (C D : Finset (Q n))
    (hrC : ((hypercube n).induce (C : Set _)).IsRegularOfDegree 3)
    (hrD : ((hypercube n).induce (D : Set _)).IsRegularOfDegree 3)
    (hbC : IsBalanced C) (hbD : IsBalanced D)
    (hc : ∀ x ∈ C, ∀ y ∈ D, ¬ (hypercube n).Adj x y)
    (v : Q n) (hvC : v ∉ C) (hvD : v ∉ D)
    (S T : Finset (Fin n)) (t : Fin n)
    (hS : ∀ i, i ∈ S ↔ flip v i ∈ C)
    (hT : ∀ j, j ∈ T ↔ flip v j ∈ D)
    (hcover : ∀ k, k ∈ S ∨ k ∈ T ∨ k = t)
    (htS : t ∉ S) (hcardS : S.card = 4) (hcardT : T.card = 4) : False := by
  have hc' : ∀ x ∈ D, ∀ y ∈ C, ¬ (hypercube n).Adj x y := by
    intro x hx y hy hxy
    exact hc y hy x hx hxy.symm
  obtain ⟨hdegree, hforceC⟩ := four_structure C D hrC hbC hc v hvC S T t
    (fun i hi => (hS i).mp hi) (fun j hj => (hT j).mp hj) hcover hcardS
  obtain ⟨_, hforceD⟩ := four_structure D C hrD hbD hc' v hvD T S t
    (fun j hj => (hT j).mp hj) (fun i hi => (hS i).mp hi)
    (fun k => (hcover k).elim (fun h => Or.inr (Or.inl h))
      (fun h => h.elim Or.inl (fun he => Or.inr (Or.inr he)))) hcardT
  obtain ⟨i, hi⟩ := Finset.card_pos.mp (show 0 < S.card by omega)
  let u := flip (flip v i) t
  have hu : u ∈ C := hforceC i hi
  have hvt : flip v t ∉ C := fun h => htS ((hS t).mpr h)
  have hsub : directions C u ⊆ insert t ((S.erase i) \ link C v S i) := by
    intro k hk
    have hkC : flip (flip (flip v i) t) k ∈ C := (mem_directions C u k).mp hk
    by_cases hkt : k = t
    · exact Finset.mem_insert.mpr (Or.inl hkt)
    rcases hcover k with hkS | hkT | hkt'
    · have hki : k ≠ i := by
        intro he
        subst k
        exact hvt (by simpa only [flip_cancel_middle] using hkC)
      have hkH : k ∉ link C v S i := by
        intro hkH
        have hxk : flip (flip v i) k ∈ C := (Finset.mem_filter.mp hkH).2
        have hn := BalancedCubeGirth.no_selected_square hbC hkt
          ((hS i).mp hi) hxk (hforceC i hi)
        apply hn
        simpa only [flip_comm (flip v i) t k] using hkC
      exact Finset.mem_insert_of_mem
        (Finset.mem_sdiff.mpr ⟨Finset.mem_erase.mpr ⟨hki, hkS⟩, hkH⟩)
    · exfalso
      apply hc _ hkC _ (hforceD k hkT)
      rw [flip_three_swap v i t k]
      exact (BalancedCriticalSpectrum.flip_adj (flip (flip v k) t) i).symm
    · exact (hkt hkt').elim
  have he : (S.erase i).card = 3 := by simp [Finset.card_erase_of_mem hi, hcardS]
  have hdiff : ((S.erase i) \ link C v S i).card = 1 := by
    rw [Finset.card_sdiff_of_subset (link_subset C v S i), he, hdegree i hi]
  have hle := Finset.card_le_card hsub
  have hle' := Finset.card_insert_le t ((S.erase i) \ link C v S i)
  have hthree := regular_directions C hrC hu
  omega

open Classical in
/-- Two separated balanced cubic restrictions meeting an exterior vertex have
at most six actual cube neighbors at that vertex in total. -/
theorem neighbor_card_add_le_six
    (C D : Finset (BalancedCriticalSpectrum.Q 9))
    (hrC : ((hypercube 9).induce (C : Set _)).IsRegularOfDegree 3)
    (hrD : ((hypercube 9).induce (D : Set _)).IsRegularOfDegree 3)
    (hbC : BalancedCriticalSpectrum.IsBalanced C)
    (hbD : BalancedCriticalSpectrum.IsBalanced D)
    (hdisj : Disjoint C D)
    (hcross : ∀ x ∈ C, ∀ y ∈ D, ¬ (hypercube 9).Adj x y)
    (v : BalancedCriticalSpectrum.Q 9)
    (hvC : v ∉ C) (hvD : v ∉ D)
    (hposC : 0 < (C.filter (fun x => (hypercube 9).Adj v x)).card)
    (hposD : 0 < (D.filter (fun x => (hypercube 9).Adj v x)).card) :
    (C.filter (fun x => (hypercube 9).Adj v x)).card +
      (D.filter (fun x => (hypercube 9).Adj v x)).card ≤ 6 := by
  let I := directions C v
  let J := directions D v
  have hI : ∀ i, i ∈ I ↔ flip v i ∈ C := fun i => mem_directions C v i
  have hJ : ∀ j, j ∈ J ↔ flip v j ∈ D := fun j => mem_directions D v j
  have hIpos : 0 < I.card := by simpa only [I, directions_card] using hposC
  have hJpos : 0 < J.card := by simpa only [J, directions_card] using hposD
  have hIeven : Even I.card := exterior_even C hrC hbC v hvC
  have hJeven : Even J.card := exterior_even D hrD hbD v hvD
  have hIJ : Disjoint I J := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    exact Finset.disjoint_left.mp hdisj ((hI i).mp hi) ((hJ i).mp hj)
  have hbound : I.card + J.card ≤ 9 := by
    calc
      I.card + J.card = (I ∪ J).card := (Finset.card_union_of_disjoint hIJ).symm
      _ ≤ (Finset.univ : Finset (Fin 9)).card :=
        Finset.card_le_card (Finset.subset_univ _)
      _ = 9 := by simp
  rw [← directions_card C v, ← directions_card D v]
  change I.card + J.card ≤ 6
  by_contra hbad
  obtain ⟨a, ha⟩ := hIeven
  obtain ⟨b, hb⟩ := hJeven
  have hsum : I.card + J.card = 8 := by omega
  have hcomp : ((Finset.univ : Finset (Fin 9)) \ (I ∪ J)).card = 1 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
      Fintype.card_fin, Finset.card_union_of_disjoint hIJ, hsum]
  obtain ⟨t, ht⟩ := Finset.card_eq_one.mp hcomp
  have htout : t ∉ I ∧ t ∉ J := by
    have hm : t ∈ (Finset.univ : Finset (Fin 9)) \ (I ∪ J) := by rw [ht]; simp
    simpa only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_union,
      not_or] using hm
  have hcover : ∀ k, k ∈ I ∨ k ∈ J ∨ k = t := by
    intro k
    by_cases hkI : k ∈ I
    · exact Or.inl hkI
    by_cases hkJ : k ∈ J
    · exact Or.inr (Or.inl hkJ)
    have hm : k ∈ (Finset.univ : Finset (Fin 9)) \ (I ∪ J) :=
      Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, by simp [hkI, hkJ]⟩
    rw [ht] at hm
    exact Or.inr (Or.inr (Finset.mem_singleton.mp hm))
  have hcases : I.card = 2 ∨ J.card = 2 ∨ (I.card = 4 ∧ J.card = 4) := by omega
  rcases hcases with htwoI | htwoJ | ⟨hfourI, hfourJ⟩
  · exact small_side_impossible C D hrC hcross v hvC I J t
      (fun i hi => (hI i).mp hi) (fun j hj => (hJ j).mp hj) hcover htwoI
  · have hc' : ∀ x ∈ D, ∀ y ∈ C, ¬ (hypercube 9).Adj x y := by
      intro x hx y hy hxy
      exact hcross y hy x hx hxy.symm
    apply small_side_impossible D C hrD hc' v hvD J I t
      (fun j hj => (hJ j).mp hj) (fun i hi => (hI i).mp hi) _ htwoJ
    intro k
    rcases hcover k with hkI | hkJ | hkt
    · exact Or.inr (Or.inl hkI)
    · exact Or.inl hkJ
    · exact Or.inr (Or.inr hkt)
  · exact four_four_impossible C D hrC hrD hbC hbD hcross v hvC hvD I J t
      hI hJ hcover htout.1 hfourI hfourJ

end D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeComponentBoundary
