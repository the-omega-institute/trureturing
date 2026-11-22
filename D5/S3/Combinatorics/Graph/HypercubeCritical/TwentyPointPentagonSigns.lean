/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/TwentyPointPentagonSigns
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/TwentyPointPentagonSigns
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.InformationTheory.Hamming]
   utility: none
   digest: Common centers and odd signed cycles for actual pentagon embeddings. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyPointPentagon
import D5.S3.Combinatorics.Graph.HypercubeCritical.HuangCubeCovariance

/-! Pairwise distance-two actual cube vertices and their Huang signs. -/

set_option autoImplicit false
set_option linter.style.longLine false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyPointPentagonSigns

open SimpleGraph GirthSliceCounting
open D5.S3.Combinatorics.Graph.Hypercube
open BalancedCriticalSpectrum (Q flip IsBalanced)
open private diff diff_flip diff_of_adj_flip from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CubeSmallSupport
open private diff_injective diff_self diff_symm diff_triangle_card inter_card low_not_three from
  D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyPointGeometry
open BalancedCubeGirth (flip_comm)
open private adjacent_exists_flip switching_ne_zero from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeGirth
open private huangMatrix huangMatrix_symmetric from
  D5.S3.Combinatorics.Graph.HypercubeSubQuorum

attribute [local instance] Classical.propDecidable

private theorem pair_mem {α : Type*} [DecidableEq α] {x a b : α} :
    x ∈ ({a, b} : Finset α) ↔ x = a ∨ x = b := by simp

private theorem pair_meeting_two {α : Type*} [DecidableEq α]
    {T : Finset α} {a b c : α} (hbc : b ≠ c) (hT : T.card = 2)
    (h1 : (T ∩ {a, b}).Nonempty) (h2 : (T ∩ {a, c}).Nonempty) :
    a ∈ T ∨ T = {b, c} := by
  by_cases ha : a ∈ T
  · exact Or.inl ha
  · right
    obtain ⟨u, hu⟩ := h1
    obtain ⟨v, hv⟩ := h2
    have hb : b ∈ T := by
      have h := Finset.mem_inter.mp hu
      rcases pair_mem.mp h.2 with rfl | rfl
      · exact (ha h.1).elim
      · exact h.1
    have hc : c ∈ T := by
      have h := Finset.mem_inter.mp hv
      rcases pair_mem.mp h.2 with rfl | rfl
      · exact (ha h.1).elim
      · exact h.1
    exact (Finset.eq_of_subset_of_card_le (by
      simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
      exact ⟨hb, hc⟩) (by simp [hT, hbc])).symm

private theorem four_pairs_common {α : Type*} [DecidableEq α]
    (F : Fin 4 → Finset α) (hinj : Function.Injective F)
    (hcard : ∀ i, (F i).card = 2)
    (hinter : ∀ i j, i ≠ j → (F i ∩ F j).card = 1) :
    ∃ a, ∀ i, a ∈ F i := by
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp (hinter 0 1 (by decide))
  have ha0 : a ∈ F 0 := (Finset.mem_inter.mp (show a ∈ F 0 ∩ F 1 by rw [ha]; simp)).1
  have ha1 : a ∈ F 1 := (Finset.mem_inter.mp (show a ∈ F 0 ∩ F 1 by rw [ha]; simp)).2
  have hrest (i : Fin 4) (hai : a ∈ F i) : ∃ b, b ≠ a ∧ F i = {a, b} := by
    obtain ⟨b, hb⟩ := Finset.card_eq_one.mp
      (show ((F i).erase a).card = 1 by rw [Finset.card_erase_of_mem hai, hcard])
    have hbmem : b ∈ (F i).erase a := by rw [hb]; simp
    refine ⟨b, (Finset.mem_erase.mp hbmem).1, ?_⟩
    rw [← Finset.insert_erase hai, hb]
  obtain ⟨b, hba, h0⟩ := hrest 0 ha0
  obtain ⟨c, hca, h1⟩ := hrest 1 ha1
  have hbc : b ≠ c := by
    intro he
    have hh : F 0 = F 1 := by rw [h0, h1, he]
    have := hinj hh
    norm_num at this
  have hmeet (i j : Fin 4) : (F i ∩ F j).Nonempty := by
    by_cases he : i = j
    · subst j; rw [Finset.inter_self]; exact Finset.card_pos.mp (by rw [hcard]; omega)
    · exact Finset.card_pos.mp (by rw [hinter i j he]; omega)
  have hform (i : Fin 4) : a ∈ F i ∨ F i = {b, c} := by
    exact pair_meeting_two hbc (hcard i) (h0 ▸ hmeet i 0) (h1 ▸ hmeet i 1)
  by_cases hall : ∀ i, a ∈ F i
  · exact ⟨a, hall⟩
  · push Not at hall
    obtain ⟨k, hk⟩ := hall
    have hkform : F k = {b, c} := (hform k).resolve_left hk
    have hthree (i : Fin 4) : F i ∈ ({F 0, F 1, F k} : Finset (Finset α)) := by
      rcases hform i with hai | hi
      · obtain ⟨x, hxa, hix⟩ := hrest i hai
        obtain ⟨y, hy⟩ := hmeet i k
        rw [hix, hkform] at hy
        have h := Finset.mem_inter.mp hy
        have hya : y ≠ a := by
          rcases pair_mem.mp h.2 with rfl | rfl <;> assumption
        have hyx : y = x := (pair_mem.mp h.1).resolve_left hya
        rcases pair_mem.mp h.2 with hyb | hyc
        · have hx : x = b := hyx.symm.trans hyb
          have he : F i = F 0 := by rw [hix, h0, hx]
          simp [he]
        · have hx : x = c := hyx.symm.trans hyc
          have he : F i = F 1 := by rw [hix, h1, hx]
          simp [he]
      · have he : F i = F k := hi.trans hkform.symm
        simp [he]
    have hbound := Finset.card_le_card
      (show Finset.univ.image F ⊆ ({F 0, F 1, F k} : Finset (Finset α)) by
        intro X hX; obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hX; exact hthree i)
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin] at hbound
    have hle : ({F 0, F 1, F k} : Finset (Finset α)).card ≤ 3 := by
      exact (Finset.card_insert_le _ _).trans (by
        have := Finset.card_insert_le (F 1) {F k}
        simp only [Finset.card_singleton] at this
        omega)
    omega

private theorem five_distance_two_center {n : ℕ} (A : Fin 5 → Q n)
    (hinj : Function.Injective A)
    (hdist : ∀ i j, i ≠ j → hammingDist (A i) (A j) = 2) :
    ∃ z : Q n, ∀ i, (hypercube n).Adj z (A i) := by
  let F : Fin 4 → Finset (Fin n) := fun i => diff (A i.succ) (A 0)
  have hcard (i : Fin 4) : (F i).card = 2 := hdist i.succ 0 (Fin.succ_ne_zero _)
  have hinter (i j : Fin 4) (hij : i ≠ j) : (F i ∩ F j).card = 1 := by
    have hh := inter_card (hcard i) (hcard j)
      (hdist i.succ j.succ (fun he => hij (Fin.succ_injective _ he)))
    dsimp [F] at *
    omega
  have hf : Function.Injective F := by
    intro i j he
    apply Fin.succ_injective 4
    exact hinj (diff_injective (A 0) he)
  obtain ⟨t, ht⟩ := four_pairs_common F hf hcard hinter
  refine ⟨flip (A 0) t, ?_⟩
  intro i
  induction i using Fin.cases with
  | zero => exact (BalancedCriticalSpectrum.flip_adj _ _).symm
  | succ i =>
      change (diff (flip (A 0) t) (A i.succ)).card = 1
      have hmem : t ∈ diff (A 0) (A i.succ) := by
        rw [diff_symm]; exact ht i
      rw [diff_flip, if_pos hmem, Finset.card_erase_of_mem hmem, diff_symm]
      have hh := hcard i
      change (diff (A i.succ) (A 0)).card = 2 at hh
      omega

private theorem five_star_negative {n : ℕ} {S : Finset (Q n)}
    (hbal : IsBalanced S) (A P : Fin 5 → (S : Set (Q n)))
    (hinj : Function.Injective A)
    (hAP : ∀ i, (hypercube n).Adj (A i).val (P i).val)
    (hPA : ∀ i, (hypercube n).Adj (A (i + 1)).val (P i).val)
    {z : Q n} (hz : ∀ i, (hypercube n).Adj z (A i).val)
    (hPz : ∀ i, (P i).val ≠ z) : False := by
  choose d hd using fun i => adjacent_exists_flip (hz i)
  have hd' : Function.Injective d := by
    intro i j he
    apply hinj
    apply Subtype.ext
    rw [hd i, hd j, he]
  have hnext (i : Fin 5) : i ≠ i + 1 := by revert i; decide +kernel
  have hmiddle (i : Fin 5) : (P i).val = flip (flip z (d i)) (d (i + 1)) := by
    have h1 := diff_of_adj_flip (hPz i).symm (d i) (by rw [← hd i]; exact hAP i)
    have h2 := diff_of_adj_flip (hPz i).symm (d (i + 1)) (by rw [← hd (i + 1)]; exact hPA i)
    have hdd : d i ≠ d (i + 1) := hd'.ne (hnext i)
    have he : diff z (P i).val = {d i, d (i + 1)} := by
      exact (Finset.eq_of_subset_of_card_le (by
        simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
        exact ⟨h1.1, h2.1⟩)
        (by simp [h1.2, hdd])).symm
    apply diff_injective z
    change diff (P i).val z = diff (flip (flip z (d i)) (d (i + 1))) z
    rw [diff_symm (P i).val z, he, diff_flip, diff_flip, diff_self]
    simp [hdd, Ne.symm hdd, Finset.pair_comm]
  obtain ⟨sigma, hs⟩ := hbal
  let q : Fin 5 → Real := fun i => huangMatrix n z (A i).val * sigma (A i).val
  have hrel (i : Fin 5) : q i = -q (i + 1) := by
    have hh := congrFun (BalancedCubeGirth.gamma_anticommute
      (hd'.ne (hnext i)) (fun _ => (1 : Real))) z
    simp only [Pi.neg_apply, BalancedCriticalSpectrum.gamma_apply, mul_one] at hh
    have hreverse : flip (flip z (d (i + 1))) (d i) = (P i).val := by
      rw [flip_comm, ← hmiddle]
    rw [← hmiddle i, hreverse, ← hd i, ← hd (i + 1)] at hh
    rw [hs.2 (A i).val (A i).property (P i).val (P i).property (hAP i),
      hs.2 (A (i + 1)).val (A (i + 1)).property (P i).val (P i).property (hPA i)] at hh
    have hn := switching_ne_zero hs (P i).property
    apply mul_right_cancel₀ hn
    dsimp [q]
    linear_combination hh
  have hzero : q 0 = 0 := by
    have h0 := hrel 0
    have h1 := hrel 1
    have h2 := hrel 2
    have h3 := hrel 3
    have h4 := hrel 4
    norm_num at h0 h1 h2 h3 h4
    linarith
  have hsq := SupportedEigenSaturation.matrix_sq_of_adj (hz 0)
  have hmat : huangMatrix n z (A 0).val ≠ 0 := by
    intro he; rw [he] at hsq; norm_num at hsq
  exact mul_ne_zero hmat (switching_ne_zero hs (A 0).property) hzero

#print axioms five_star_negative

end D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyPointPentagonSigns
