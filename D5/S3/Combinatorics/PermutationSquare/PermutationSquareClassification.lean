/- GID: D5/S3/Combinatorics/PermutationSquare/PermutationSquareClassification
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PermutationSquare/PermutationSquareClassification
   mirror-E: none(waiver:first-entry-four-and-complete-indecomposable-classification)
   anchors: []
   utility: none
   digest: Tail types, middle avoidance, first-entry-four cases, and full classification. -/

import D5.S3.Combinatorics.PermutationSquare.PermutationSquareFamilies

/-! Tail structure, middle-segment pattern avoidance, first-entry-four classification across all
    sizes `n ≥ 4`, and the complete seven-family classification for `n ≥ 9`. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.PermutationSquare.PermutationSquareClassification

open D5.S3.Combinatorics Nonnesting NonnestingBasicSum
open PermutationSquareDefs PermutationSquareStructure PermutationSquareFamilies

private theorem sublist_map_getD_drop (p : List ℕ) : ∀ (is : List ℕ) (c : ℕ), is.Pairwise (· < ·) → (∀ i ∈ is, c ≤ i ∧ i < p.length) → (is.map fun i => p.getD i 0).Sublist (p.drop c)
  | [], _, _, _ => List.nil_sublist _
  | i :: rest, c, hpw, hb => by
    have hic := hb i (by simp)
    have hrest := sublist_map_getD_drop p rest (i + 1) (List.pairwise_cons.mp hpw).2
      fun k hk => ⟨(List.pairwise_cons.mp hpw).1 k hk, (hb k (List.mem_cons_of_mem i hk)).2⟩
    have hcons : ((i :: rest).map fun k => p.getD k 0).Sublist (p.drop i) := by
      rw [List.map_cons, List.getD_eq_getElem p 0 hic.2, List.drop_eq_getElem_cons hic.2]
      exact List.Sublist.cons_cons _ hrest
    rw [show p.drop i = (p.drop c).drop (i - c) by rw [List.drop_drop, Nat.add_sub_of_le hic.1]] at hcons
    exact hcons.trans (List.drop_sublist _ _)
private theorem occurs_mono_sublist {σ u w : List ℕ} (h : NonnestingDefs.Occurs σ u) (hsub : u.Sublist w) : NonnestingDefs.Occurs σ w := by
  rcases h with ⟨x, hmono, hmem, hs, _⟩; exact ⟨x, hmono, fun r h1 h2 => hsub.subset (hmem r h1 h2), hs.trans hsub, by simp⟩
private theorem occurs_312_of_indices {p : List ℕ} {i j k : ℕ} (hij : i < j) (hjk : j < k) (hk : k < p.length) (h1 : p.getD j 0 < p.getD k 0) (h2 : p.getD k 0 < p.getD i 0) : NonnestingDefs.Occurs [3, 1, 2] p := by
  let x : ℕ → ℕ := fun r => if r = 1 then p.getD j 0 else if r = 2 then p.getD k 0 else p.getD i 0
  have hsub : [x 3, x 1, x 2].Sublist p := (by simpa [x] using sublist_map_getD_drop p [i, j, k] 0 (by simp; omega) (by simp; omega)); refine ⟨x, fun r _ hr => ?_, fun r _ hr => ?_, hsub, by simp⟩
  · change r < 3 at hr; rcases (by omega : r = 1 ∨ r = 2) with rfl | rfl <;> assumption
  · change r ≤ 3 at hr; apply hsub.subset; rcases (by omega : r = 1 ∨ r = 2 ∨ r = 3) with rfl | rfl | rfl <;> simp
private theorem occurs_132_of_indices {p : List ℕ} {i j k : ℕ} (hij : i < j) (hjk : j < k) (hk : k < p.length) (h1 : p.getD i 0 < p.getD k 0) (h2 : p.getD k 0 < p.getD j 0) : NonnestingDefs.Occurs [1, 3, 2] p := by
  let x : ℕ → ℕ := fun r => if r = 1 then p.getD i 0 else if r = 2 then p.getD k 0 else p.getD j 0
  have hsub : [x 1, x 3, x 2].Sublist p := (by simpa [x] using sublist_map_getD_drop p [i, j, k] 0 (by simp; omega) (by simp; omega)); refine ⟨x, fun r _ hr => ?_, fun r _ hr => ?_, hsub, by simp⟩
  · change r < 3 at hr; rcases (by omega : r = 1 ∨ r = 2) with rfl | rfl <;> assumption
  · change r ≤ 3 at hr; apply hsub.subset; rcases (by omega : r = 1 ∨ r = 2 ∨ r = 3) with rfl | rfl | rfl <;> simp
private theorem occurs_321_iff (p : List ℕ) : NonnestingDefs.Occurs [3, 2, 1] p ↔ ∃ i j k : ℕ, i < j ∧ j < k ∧ k < p.length ∧ p.getD k 0 < p.getD j 0 ∧ p.getD j 0 < p.getD i 0 := by
  constructor
  · rintro ⟨x, hmono, _, hsub, _⟩; change [x 3, x 2, x 1].Sublist p at hsub
    obtain ⟨emb, hemb⟩ := List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp hsub; let i0 := emb ⟨0, by simp⟩; let i1 := emb ⟨1, by simp⟩; let i2 := emb ⟨2, by simp⟩; have he0 : p.getD i0.val 0 = x 3 := (by rw [List.getD_eq_getElem p 0 i0.isLt]; exact (hemb ⟨0, by simp⟩).symm); have he1 : p.getD i1.val 0 = x 2 := (by rw [List.getD_eq_getElem p 0 i1.isLt]; exact (hemb ⟨1, by simp⟩).symm)
    have he2 : p.getD i2.val 0 = x 1 := (by rw [List.getD_eq_getElem p 0 i2.isLt]; exact (hemb ⟨2, by simp⟩).symm); have hx12 : x 1 < x 2 := hmono 1 (by omega) (by change 1 < 3; omega); have hx23 : x 2 < x 3 := hmono 2 (by omega) (by change 2 < 3; omega)
    exact ⟨i0.val, i1.val, i2.val, emb.strictMono (by change (0 : ℕ) < 1; omega),
      emb.strictMono (by change (1 : ℕ) < 2; omega), i2.isLt, by omega, by omega⟩
  · rintro ⟨i, j, k, hij, hjk, hk, h1, h2⟩
    let x : ℕ → ℕ := fun r => if r = 1 then p.getD k 0 else if r = 2 then p.getD j 0 else p.getD i 0
    have hsub : [x 3, x 2, x 1].Sublist p := (by simpa [x] using sublist_map_getD_drop p [i, j, k] 0 (by simp; omega) (by simp; omega)); refine ⟨x, fun r _ hr => ?_, fun r _ hr => ?_, hsub, by simp⟩
    · change r < 3 at hr; rcases (by omega : r = 1 ∨ r = 2) with rfl | rfl <;> assumption
    · change r ≤ 3 at hr; apply hsub.subset; rcases (by omega : r = 1 ∨ r = 2 ∨ r = 3) with rfl | rfl | rfl <;> simp
private theorem occurs_54321_of_indices {p : List ℕ} {i₁ i₂ i₃ i₄ i₅ : ℕ} (h12 : i₁ < i₂) (h23 : i₂ < i₃) (h34 : i₃ < i₄) (h45 : i₄ < i₅) (h5 : i₅ < p.length) (hv45 : p.getD i₅ 0 < p.getD i₄ 0) (hv34 : p.getD i₄ 0 < p.getD i₃ 0) (hv23 : p.getD i₃ 0 < p.getD i₂ 0) (hv12 : p.getD i₂ 0 < p.getD i₁ 0) : NonnestingDefs.Occurs [5, 4, 3, 2, 1] p := by
  let x : ℕ → ℕ := fun r =>
    if r = 1 then p.getD i₅ 0 else if r = 2 then p.getD i₄ 0 else
    if r = 3 then p.getD i₃ 0 else if r = 4 then p.getD i₂ 0 else p.getD i₁ 0
  have hsub : [x 5, x 4, x 3, x 2, x 1].Sublist p := (by simpa [x] using sublist_map_getD_drop p [i₁, i₂, i₃, i₄, i₅] 0 (by simp; omega) (by simp; omega)); refine ⟨x, fun r _ hr => ?_, fun r _ hr => ?_, hsub, by simp⟩
  · change r < 5 at hr; rcases (by omega : r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4) with rfl | rfl | rfl | rfl <;> assumption
  · change r ≤ 5 at hr; apply hsub.subset; rcases (by omega : r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5) with rfl | rfl | rfl | rfl | rfl <;> simp
private theorem perm_bounds {n : ℕ} {p : List ℕ} (hperm : p.Perm (List.range' 1 n)) {v : ℕ} (hv : v ∈ p) : 1 ≤ v ∧ v ≤ n := by
  have hr := hperm.mem_iff.mp hv; simp only [List.mem_range', Nat.one_mul] at hr; obtain ⟨k, hk, rfl⟩ := hr; omega
private theorem perm_getD_bounds {n : ℕ} {p : List ℕ} (hperm : p.Perm (List.range' 1 n)) {i : ℕ} (hi : i < n) : 1 ≤ p.getD i 0 ∧ p.getD i 0 ≤ n := by
  have hlen : p.length = n := (by simpa using hperm.length_eq); rw [List.getD_eq_getElem p 0 (by omega)]; exact perm_bounds hperm (List.getElem_mem (by omega))
private theorem perm_getD_inj {n : ℕ} {p : List ℕ} (hperm : p.Perm (List.range' 1 n)) {i j : ℕ} (hi : i < n) (hj : j < n) (heq : p.getD i 0 = p.getD j 0) : i = j := by
  have hlen : p.length = n := (by simpa using hperm.length_eq); have hnd : p.Nodup := hperm.nodup_iff.mpr (List.nodup_range' 1); rw [List.getD_eq_getElem p 0 (by omega), List.getD_eq_getElem p 0 (by omega)] at heq; exact hnd.getElem_inj_iff.mp heq
private theorem ne_val_of_getD {n : ℕ} {p : List ℕ} (hperm : p.Perm (List.range' 1 n)) {i j v : ℕ} (hi : i < n) (hj : j < n) (hne : i ≠ j) (hv : p.getD j 0 = v) : p.getD i 0 ≠ v := fun h => hne (perm_getD_inj hperm hi hj (h.trans hv.symm))
private theorem perm_idxOf_spec {n : ℕ} {p : List ℕ} (hperm : p.Perm (List.range' 1 n)) (v : ℕ) (hv1 : 1 ≤ v) (hvn : v ≤ n) : p.idxOf v < n ∧ p.getD (p.idxOf v) 0 = v := by
  have hlen : p.length = n := (by simpa using hperm.length_eq)
  have hmem : v ∈ p := hperm.mem_iff.mpr (by
    simp only [List.mem_range', Nat.one_mul]; exact ⟨v - 1, by omega, by omega⟩)
  have hlt : p.idxOf v < p.length := List.idxOf_lt_length_of_mem hmem; exact ⟨by omega, by rw [List.getD_eq_getElem p 0 hlt, List.getElem_idxOf hlt]⟩
private theorem perm_idxOf_getD {n : ℕ} {p : List ℕ} (hperm : p.Perm (List.range' 1 n)) {i : ℕ} (hi : i < n) : p.idxOf (p.getD i 0) = i := by
  have hb := perm_getD_bounds hperm hi; exact perm_getD_inj hperm (perm_idxOf_spec hperm _ hb.1 hb.2).1 hi (perm_idxOf_spec hperm _ hb.1 hb.2).2
private theorem idxOf_ne_of_getD {n : ℕ} {p : List ℕ} (hperm : p.Perm (List.range' 1 n)) (v j : ℕ) (hv1 : 1 ≤ v) (hvn : v ≤ n) (hne : p.getD j 0 ≠ v) : p.idxOf v ≠ j := fun h => hne (h ▸ (perm_idxOf_spec hperm v hv1 hvn).2)
private theorem square_perm_and_getD {n : ℕ} {p : List ℕ} (hperm : p.Perm (List.range' 1 n)) : (square p).Perm (List.range' 1 n) ∧ ∀ i < n, (square p).getD i 0 = p.getD (p.getD i 0 - 1) 0 := by
  have hlen : p.length = n := (by simpa using hperm.length_eq); refine ⟨?_, fun i hi => ?_⟩
  · have hmap : (List.range' 1 n).map (fun v => p.getD (v - 1) 0) = p := by
      apply List.ext_getElem (by simp [hlen]); intro i hi1 hi2; simp only [List.getElem_map, List.getElem_range', Nat.one_mul, Nat.add_sub_cancel_left]; exact List.getD_eq_getElem p 0 hi2
    unfold square; have hp' := hperm.map (fun v => p.getD (v - 1) 0); rw [hmap] at hp'; exact hp'.trans hperm
  · unfold square; rw [List.getD_eq_getElem _ 0 (by simp [hlen, hi]), List.getElem_map,
      ← List.getD_eq_getElem p 0 (by omega)]
private theorem getD_of_sq_eq {n : ℕ} {p : List ℕ} (hperm : p.Perm (List.range' 1 n)) (i v : ℕ) (hi : i < n) (hv1 : 1 ≤ v) (hvn : v ≤ n) (hq : (square p).getD i 0 = v) : p.getD i 0 = p.idxOf v + 1 := by
  have hsq := (square_perm_and_getD hperm).2 i hi; rw [hq] at hsq; have hb := perm_getD_bounds hperm hi; have hs := perm_idxOf_spec hperm v hv1 hvn; have := perm_getD_inj hperm (by omega : p.getD i 0 - 1 < n) hs.1 (hsq.symm.trans hs.2.symm); omega
private theorem left_bound_of_avoids_312 {n : ℕ} {p : List ℕ} (hperm : p.Perm (List.range' 1 n)) (hav312 : ¬ NonnestingDefs.Occurs [3, 1, 2] p) (hend : p.getD (n - 1) 0 = 1) {idx later : ℕ} (h1 : idx < later) (h2 : later < n) (hsmall : 2 ≤ p.getD idx 0) (hlt : p.getD idx 0 < p.getD later 0) : idx + 3 ≤ p.getD later 0 := by
  have hlen : p.length = n := (by simpa using hperm.length_eq)
  have hinj : Set.InjOn (fun i => p.getD i 0) (Finset.range idx) := fun x hx y hy hxy => by
    rw [Finset.mem_coe, Finset.mem_range] at hx hy; exact perm_getD_inj hperm (by omega) (by omega) hxy
  have hsub : (Finset.range idx).image (fun i => p.getD i 0) ⊆
      (Finset.Icc 2 (p.getD later 0 - 1)).erase (p.getD idx 0) := by
    intro v hv; obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hv; rw [Finset.mem_range] at hi; have hb := perm_getD_bounds hperm (by omega : i < n); have hne1 := ne_val_of_getD hperm (by omega) (by omega) (by omega : i ≠ n - 1) hend; have hnes := ne_val_of_getD hperm (by omega) (by omega) (by omega : i ≠ idx) rfl; have hnev := ne_val_of_getD hperm (by omega) h2 (by omega : i ≠ later) rfl
    have hle : p.getD i 0 < p.getD later 0 := (by by_contra hgt; exact hav312 (occurs_312_of_indices hi h1 (by omega) hlt (by omega))); exact Finset.mem_erase.mpr ⟨hnes, Finset.mem_Icc.mpr ⟨by omega, by omega⟩⟩
  have hc := Finset.card_le_card hsub
  rw [Finset.card_image_of_injOn hinj, Finset.card_range,
    Finset.card_erase_of_mem (Finset.mem_Icc.mpr ⟨hsmall, by omega⟩), Nat.card_Icc] at hc; omega
private theorem lemma61_tail (n : ℕ) (hn : 4 ≤ n) (p : List ℕ) (hp : p ∈ indecomposableAvoiders n) (hm : p.getD 0 0 = 4) : ((square p).drop (n - 4)).Perm [1, 2, 3, 4] ∧ (square p).getD (n - 1) 0 = 4 ∧ ({p.getD (n - 4) 0, p.getD (n - 3) 0, p.getD (n - 2) 0} : Set ℕ) = {n, p.idxOf 2 + 1, p.idxOf 3 + 1} := by
  rcases hp with ⟨hpne, ⟨hperm, hav312, hav54321, hav132⟩, hind⟩; have hlen : p.length = n := (by simpa using hperm.length_eq); have hsq := square_perm_and_getD hperm; have hqlen : (square p).length = n := (by simpa using hsq.1.length_eq); have hsh := indecomposable_shape_and_prefix_iff.2.2.2.2 n (by omega) p ⟨hpne, ⟨hperm, hav312, hav54321, hav132⟩, hind⟩; have hend : p.getD (n - 1) 0 = 1 := hsh.1.1
  have hqn : (square p).getD (n - 1) 0 = 4 := hsh.2.2.1.2.1.trans hm; clear hsh; have hs1 := perm_idxOf_spec hsq.1 1 (by omega) (by omega); have hs2 := perm_idxOf_spec hsq.1 2 (by omega) (by omega); have hs3 := perm_idxOf_spec hsq.1 3 (by omega) (by omega); have hne1 : (square p).idxOf 1 ≠ n - 1 := idxOf_ne_of_getD hsq.1 1 (n - 1) (by omega) (by omega) (by omega)
  have hne2 : (square p).idxOf 2 ≠ n - 1 := idxOf_ne_of_getD hsq.1 2 (n - 1) (by omega) (by omega) (by omega); have hne3 : (square p).idxOf 3 ≠ n - 1 := idxOf_ne_of_getD hsq.1 3 (n - 1) (by omega) (by omega) (by omega)
  have hright_le4 : ∀ k ∈ ({1, 2, 3} : Set ℕ), ∀ j, (square p).idxOf k ≤ j → j < n → (square p).getD j 0 ≤ 4 := by
    intro k hk j hkj hj; have hsk := perm_idxOf_spec hsq.1 k (by simp at hk; omega) (by simp at hk; omega); rcases (by omega : j = (square p).idxOf k ∨ ((square p).idxOf k < j ∧ j < n - 1) ∨ j = n - 1) with rfl | ⟨h1, h2⟩ | rfl
    · simp at hk; omega
    · by_contra hgt; exact hav132 (occurs_132_of_indices h1 h2 (by omega) (by simp at hk; omega) (by omega))
    · omega
  obtain ⟨P, hP_def⟩ : ∃ P, P = min ((square p).idxOf 1) (min ((square p).idxOf 2) ((square p).idxOf 3)) := ⟨_, rfl⟩; have hP_or : (P = (square p).idxOf 1 ∨ P = (square p).idxOf 2 ∨ P = (square p).idxOf 3) ∧
      P ≤ (square p).idxOf 1 ∧ P ≤ (square p).idxOf 2 ∧ P ≤ (square p).idxOf 3 := by omega
  clear hP_def
  have hP_le4 : ∀ j, P ≤ j → j < n → 1 ≤ (square p).getD j 0 ∧ (square p).getD j 0 ≤ 4 := fun j hPj hj => by
    refine ⟨(perm_getD_bounds hsq.1 hj).1, ?_⟩; rcases hP_or.1 with h1 | h2 | h3
    · exact hright_le4 1 (by simp) j (by omega) hj
    · exact hright_le4 2 (by simp) j (by omega) hj
    · exact hright_le4 3 (by simp) j (by omega) hj
  have hP_ge : n - 4 ≤ P := by
    have hinj : Set.InjOn (fun j => (square p).getD j 0) (Finset.Ico P n) := fun x hx y hy hxy => by
      rw [Finset.mem_coe, Finset.mem_Ico] at hx hy; exact perm_getD_inj hsq.1 hx.2 hy.2 hxy
    have hsub : (Finset.Ico P n).image (fun j => (square p).getD j 0) ⊆ Finset.Icc 1 4 := (by intro v hv; obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hv; rw [Finset.mem_Ico] at hj; exact Finset.mem_Icc.mpr (hP_le4 j hj.1 hj.2))
    have hc := Finset.card_le_card hsub; rw [Finset.card_image_of_injOn hinj, Nat.card_Ico, Nat.card_Icc] at hc; omega
  have h12 : (square p).idxOf 1 ≠ (square p).idxOf 2 := fun h => by have := hs1.2; rw [h, hs2.2] at this; omega
  have h13 : (square p).idxOf 1 ≠ (square p).idxOf 3 := fun h => by have := hs1.2; rw [h, hs3.2] at this; omega
  have h23 : (square p).idxOf 2 ≠ (square p).idxOf 3 := fun h => by have := hs2.2; rw [h, hs3.2] at this; omega
  have hP_eq : P = n - 4 := (by omega)
  have hd_perm : ((square p).drop (n - 4)).Perm [1, 2, 3, 4] := by
    have hnd : ((square p).drop (n - 4)).Nodup := (hsq.1.nodup_iff.mpr (List.nodup_range' 1)).sublist (List.drop_sublist _ _)
    have hsub : ∀ v ∈ (square p).drop (n - 4), v ∈ ([1, 2, 3, 4] : List ℕ) := by
      intro v hv; obtain ⟨idx, hidx, rfl⟩ := List.getElem_of_mem hv; have hj : n - 4 + idx < n := (by rw [List.length_drop, hqlen] at hidx; omega); have hb := hP_le4 (n - 4 + idx) (by omega) hj; have hge : ((square p).drop (n - 4))[idx]'hidx = (square p).getD (n - 4 + idx) 0 := (by rw [List.getElem_drop, List.getD_eq_getElem (square p) 0 (by rw [hqlen]; omega)]); rw [hge]; simp only [List.mem_cons, List.not_mem_nil, or_false]; omega
    exact (hnd.subperm hsub).perm_of_length_le (by simp [hqlen]; omega)
  refine ⟨hd_perm, hqn, ?_⟩; have hi1 : p.idxOf 1 = n - 1 := (by have h := perm_idxOf_getD hperm (i := n - 1) (by omega); rwa [hend] at h); have hp_at : ∀ j, n - 4 ≤ j → j < n - 1 →
      p.getD j 0 = n ∨ p.getD j 0 = p.idxOf 2 + 1 ∨ p.getD j 0 = p.idxOf 3 + 1 := fun j hj1 hj2 => by
    have hb := hP_le4 j (by omega) (by omega); have hne4 := ne_val_of_getD hsq.1 (by omega) (by omega) (by omega : j ≠ n - 1) hqn; rcases (by omega : (square p).getD j 0 = 1 ∨ (square p).getD j 0 = 2 ∨ (square p).getD j 0 = 3) with h1 | h2 | h3
    · left; have := getD_of_sq_eq hperm j 1 (by omega) le_rfl (by omega) h1; omega
    · right; left; exact getD_of_sq_eq hperm j 2 (by omega) (by omega) (by omega) h2
    · right; right; exact getD_of_sq_eq hperm j 3 (by omega) (by omega) (by omega) h3
  ext v; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; constructor
  · rintro (rfl | rfl | rfl)
    · exact hp_at (n - 4) le_rfl (by omega)
    · exact hp_at (n - 3) (by omega) (by omega)
    · exact hp_at (n - 2) (by omega) (by omega)
  · have hj1 := getD_of_sq_eq hperm ((square p).idxOf 1) 1 hs1.1 le_rfl (by omega) hs1.2
    have hj2 := getD_of_sq_eq hperm ((square p).idxOf 2) 2 hs2.1 (by omega) (by omega) hs2.2; have hj3 := getD_of_sq_eq hperm ((square p).idxOf 3) 3 hs3.1 (by omega) (by omega) hs3.2; rw [hi1, show n - 1 + 1 = n by omega] at hj1; rintro (hvn | h | h)
    · rw [hvn]
      rcases (by omega : (square p).idxOf 1 = n - 4 ∨ (square p).idxOf 1 = n - 3 ∨ (square p).idxOf 1 = n - 2) with h1 | h1 | h1 <;>
        [exact Or.inl (by rw [← h1, hj1]); exact Or.inr (Or.inl (by rw [← h1, hj1])); exact Or.inr (Or.inr (by rw [← h1, hj1]))]
    · rw [h]
      rcases (by omega : (square p).idxOf 2 = n - 4 ∨ (square p).idxOf 2 = n - 3 ∨ (square p).idxOf 2 = n - 2) with h2 | h2 | h2 <;>
        [exact Or.inl (by rw [← h2, hj2]); exact Or.inr (Or.inl (by rw [← h2, hj2])); exact Or.inr (Or.inr (by rw [← h2, hj2]))]
    · rw [h]
      rcases (by omega : (square p).idxOf 3 = n - 4 ∨ (square p).idxOf 3 = n - 3 ∨ (square p).idxOf 3 = n - 2) with h3 | h3 | h3 <;>
        [exact Or.inl (by rw [← h3, hj3]); exact Or.inr (Or.inl (by rw [← h3, hj3])); exact Or.inr (Or.inr (by rw [← h3, hj3]))]
private theorem lemma62_second_and_tail (n : ℕ) (hn : 5 ≤ n) (p : List ℕ) (hp : p ∈ indecomposableAvoiders n) (hm : p.getD 0 0 = 4) : p.getD 1 0 = 3 ∧ ((p.getD (n - 4) 0, p.getD (n - 3) 0, p.getD (n - 2) 0) = (n, n - 1, 2) ∨ (p.getD (n - 4) 0, p.getD (n - 3) 0, p.getD (n - 2) 0) = (n - 1, n, 2) ∨ (p.getD (n - 4) 0, p.getD (n - 3) 0, p.getD (n - 2) 0) = (n - 2, 2, n)) := by
  have h61 := lemma61_tail n (by omega) p hp hm; rcases hp with ⟨hpne, ⟨hperm, hav312, hav54321, hav132⟩, hind⟩; have hlen : p.length = n := (by simpa using hperm.length_eq); have hsq := square_perm_and_getD hperm; have hqlen : (square p).length = n := (by simpa using hsq.1.length_eq); have hsh := indecomposable_shape_and_prefix_iff.2.2.2.2 n (by omega) p ⟨hpne, ⟨hperm, hav312, hav54321, hav132⟩, hind⟩
  have hend : p.getD (n - 1) 0 = 1 := hsh.1.1; let i3 := p.idxOf 3; let i2 := p.idxOf 2; have hs3 : i3 < n ∧ p.getD i3 0 = 3 := perm_idxOf_spec hperm 3 (by omega) (by omega); have hs2 : i2 < n ∧ p.getD i2 0 = 2 := perm_idxOf_spec hperm 2 (by omega) (by omega); have hord := hsh.2.1.2.2 2 3 le_rfl (by omega) (by omega); clear hsh; have hi2_ne : i2 ≠ n - 1 := idxOf_ne_of_getD hperm 2 (n - 1) (by omega) (by omega) (by omega)
  have hb32 : 1 ≤ i3 ∧ i3 < i2 ∧ i2 ≤ n - 2 := ⟨by omega, by omega, by omega⟩
  have hqdrop : ∀ j < n - 4, 5 ≤ (square p).getD j 0 := fun j hj => by
    have hb := perm_getD_bounds hsq.1 (by omega : j < n); by_contra hlt
    have hmem : (square p).getD j 0 ∈ (square p).drop (n - 4) :=
      h61.1.mem_iff.mpr (by simp only [List.mem_cons, List.not_mem_nil, or_false]; omega)
    obtain ⟨idx, hidx, heq⟩ := List.getElem_of_mem hmem; have hidx_lt : n - 4 + idx < n := (by rw [List.length_drop, hqlen] at hidx; omega); rw [List.getElem_drop, ← List.getD_eq_getElem (square p) 0 (by rw [hqlen]; omega)] at heq; have := perm_getD_inj hsq.1 hidx_lt (by omega : j < n) heq; omega
  have hj3_mem : i3 + 1 ∈ ({p.getD (n - 4) 0, p.getD (n - 3) 0, p.getD (n - 2) 0} : Set ℕ) := (by rw [h61.2.2]; simp [i3]); have hj2_mem : i2 + 1 ∈ ({p.getD (n - 4) 0, p.getD (n - 3) 0, p.getD (n - 2) 0} : Set ℕ) := (by rw [h61.2.2]; simp [i2])
  have hi3_eq1 : i3 = 1 := by
    by_contra hne1
    obtain ⟨j3, hj3_bnd, hj3_val⟩ : ∃ j3, n - 4 ≤ j3 ∧ j3 ≤ n - 2 ∧ p.getD j3 0 = i3 + 1 := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hj3_mem; rcases hj3_mem with h | h | h
      · exact ⟨n - 4, le_rfl, by omega, h.symm⟩
      · exact ⟨n - 3, by omega, by omega, h.symm⟩
      · exact ⟨n - 2, by omega, le_rfl, h.symm⟩
    by_cases hge3 : 3 ≤ i3
    · rcases (by omega : i3 < j3 ∨ j3 = i3 ∨ j3 < i3) with hlt | heq | hgt
      · have hinj : Set.InjOn (fun r => p.getD r 0) (Finset.range i3) := fun x hx y hy hxy => by
          rw [Finset.mem_coe, Finset.mem_range] at hx hy; exact perm_getD_inj hperm (by omega) (by omega) hxy
        have hsub : (Finset.range i3).image (fun r => p.getD r 0) ⊆ Finset.Icc 4 i3 := by
          intro v hv; obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hv; rw [Finset.mem_range] at hr; have hb := perm_getD_bounds hperm (by omega : r < n); have c1 := ne_val_of_getD hperm (by omega) (by omega) (by omega : r ≠ n - 1) hend; have c2 := ne_val_of_getD hperm (by omega) hs2.1 (by omega : r ≠ i2) hs2.2; have c3 := ne_val_of_getD hperm (by omega) hs3.1 (by omega : r ≠ i3) hs3.2
          have c4 := ne_val_of_getD hperm (by omega) (by omega) (by omega : r ≠ j3) hj3_val.2; have hle : p.getD r 0 < i3 + 1 := (by by_contra hge; exact hav312 (occurs_312_of_indices hr hlt (by rw [hlen]; omega) (by omega) (by omega))); exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
        have hc := Finset.card_le_card hsub; rw [Finset.card_image_of_injOn hinj, Finset.card_range, Nat.card_Icc] at hc; omega
      · have := hs3.2; rw [← heq, hj3_val.2] at this; omega
      · have h3_val : i3 = n - 3 ∧ i2 = n - 2 ∧ j3 = n - 4 := by omega
        have hn_mem : n ∈ ({p.getD (n - 4) 0, p.getD (n - 3) 0, p.getD (n - 2) 0} : Set ℕ) := (by rw [h61.2.2]; simp); simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hn_mem; have hp_n4 : p.getD (n - 4) 0 = n - 2 := (by rw [← h3_val.2.2, hj3_val.2]; omega); have hp_n3 : p.getD (n - 3) 0 = 3 := (by rw [← h3_val.1]; exact hs3.2); have hp_n2 : p.getD (n - 2) 0 = 2 := (by rw [← h3_val.2.1]; exact hs2.2)
        rcases hn_mem with h | h | h <;> omega
    · have hi3_2 : i3 = 2 := by omega
      have hp2 : p.getD 2 0 = 3 := (by rw [← hi3_2]; exact hs3.2); have hq2 : (square p).getD 2 0 = 3 := (by rw [hsq.2 2 (by omega), hp2]; exact hp2); have hn_le6 : n ≤ 6 := (by by_contra hgt; have := hqdrop 2 (by omega); omega)
      have hv_bnd : 5 ≤ p.getD 1 0 ∧ p.getD 1 0 ≤ n := (by have hb := perm_getD_bounds hperm (by omega : 1 < n); have := ne_val_of_getD hperm (by omega) (by omega) (by omega : 1 ≠ n - 1) hend; have := ne_val_of_getD hperm (by omega) hs2.1 (by omega : 1 ≠ i2) hs2.2; have := ne_val_of_getD hperm (by omega) (by omega) (by omega : 1 ≠ 2) hp2; have := ne_val_of_getD hperm (by omega) (by omega) (by omega : 1 ≠ 0) hm; omega)
      rcases (by omega : n = 5 ∨ n = 6) with rfl | rfl
      · have hp1 : p.getD 1 0 = 5 := by omega
        have hq1 : (square p).getD 1 0 = 1 := (by rw [hsq.2 1 (by omega), hp1]; exact hend); have hq3_bnd := perm_getD_bounds hsq.1 (by omega : 3 < 5); have c0 := hqdrop 0 (by omega); have c1 := ne_val_of_getD hsq.1 (by omega) (by omega) (by omega : 3 ≠ 1) hq1; have c2 := ne_val_of_getD hsq.1 (by omega) (by omega) (by omega : 3 ≠ 2) hq2; have c4 := ne_val_of_getD hsq.1 (by omega) (by omega) (by omega : 3 ≠ 4) h61.2.1
        have c5 : (square p).getD 3 0 ≠ 5 := fun h => by
          have := perm_getD_inj hsq.1 (by omega : 3 < 5) (by omega : 0 < 5) (h.trans (by
            have hb0 := perm_getD_bounds hsq.1 (by omega : 0 < 5); omega : (square p).getD 0 0 = 5).symm)
          omega
        exact hav132 (occurs_132_of_indices (i := 1) (j := 2) (k := 3) (by omega) (by omega) (by omega) (by omega) (by omega))
      · have hp1 : p.getD 1 0 = 5 := by
          by_contra hne5; have hp1_6 : p.getD 1 0 = 6 := (by omega); have hs5 := perm_idxOf_spec hperm 5 (by omega) (by omega); have := idxOf_ne_of_getD hperm 5 0 (by omega) (by omega) (by omega); have := idxOf_ne_of_getD hperm 5 1 (by omega) (by omega) (by omega); have := idxOf_ne_of_getD hperm 5 2 (by omega) (by omega) (by omega)
          exact hav312 (occurs_312_of_indices (i := 1) (j := 2) (k := p.idxOf 5) (by omega) (by omega) (by omega) (by omega) (by omega))
        have hq0_ge := hqdrop 0 (by omega); have hq1_ge := hqdrop 1 (by omega); have hq0_ub := perm_getD_bounds hsq.1 (by omega : 0 < 6); have hq1_ub := perm_getD_bounds hsq.1 (by omega : 1 < 6); have hq1_eq : (square p).getD 1 0 = p.getD 4 0 := (by rw [hsq.2 1 (by omega), hp1]); have hq0_eq : (square p).getD 0 0 = p.getD 3 0 := (by rw [hsq.2 0 (by omega), hm])
        have hp4_ne5 := ne_val_of_getD hperm (by omega) (by omega) (by omega : 4 ≠ 1) hp1; have hp3_ne5 := ne_val_of_getD hperm (by omega) (by omega) (by omega : 3 ≠ 1) hp1
        have hq01_ne : (square p).getD 0 0 ≠ (square p).getD 1 0 := fun h => by
          have := perm_getD_inj hsq.1 (by omega : 0 < 6) (by omega : 1 < 6) h; omega
        omega
  have hp1_3 : p.getD 1 0 = 3 := (by rw [← hi3_eq1]; exact hs3.2); refine ⟨hp1_3, ?_⟩
  obtain ⟨j2, hj2_bnd, hj2_val⟩ : ∃ j2, n - 4 ≤ j2 ∧ j2 ≤ n - 2 ∧ p.getD j2 0 = i2 + 1 := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hj2_mem; rcases hj2_mem with h | h | h
    · exact ⟨n - 4, le_rfl, by omega, h.symm⟩
    · exact ⟨n - 3, by omega, by omega, h.symm⟩
    · exact ⟨n - 2, by omega, le_rfl, h.symm⟩
  have hj2_lt : j2 < i2 := by
    rcases (by omega : i2 < j2 ∨ i2 = j2 ∨ j2 < i2) with hlt | heq | hgt
    · have := left_bound_of_avoids_312 hperm hav312 hend hlt (by omega) (by omega) (by omega); omega
    · have := hs2.2; rw [heq, hj2_val.2] at this; omega
    · exact hgt
  have hset : ({p.getD (n - 4) 0, p.getD (n - 3) 0, p.getD (n - 2) 0} : Set ℕ) = {n, i2 + 1, 2} := (by simpa [i2, i3, hi3_eq1] using h61.2.2); have hn_mem : n ∈ ({p.getD (n - 4) 0, p.getD (n - 3) 0, p.getD (n - 2) 0} : Set ℕ) := (by rw [hset]; simp); simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hn_mem; have hdist_tail : p.getD (n - 4) 0 ≠ p.getD (n - 3) 0 ∧ p.getD (n - 4) 0 ≠ p.getD (n - 2) 0 ∧
      p.getD (n - 3) 0 ≠ p.getD (n - 2) 0 :=
    ⟨ne_val_of_getD hperm (by omega) (by omega) (by omega) rfl,
     ne_val_of_getD hperm (by omega) (by omega) (by omega) rfl,
     ne_val_of_getD hperm (by omega) (by omega) (by omega) rfl⟩
  rcases (by omega : i2 = n - 2 ∨ (i2 = n - 3 ∧ j2 = n - 4)) with hi2_a | ⟨hi2_b, hj2_b⟩
  · have hp_n2 : p.getD (n - 2) 0 = 2 := by rw [← hi2_a]; exact hs2.2
    have hp_j2 : p.getD j2 0 = n - 1 := (by rw [hj2_val.2, hi2_a]; omega); rcases (by omega : j2 = n - 4 ∨ j2 = n - 3) with rfl | rfl
    · right; left; rcases hn_mem with h | h | h <;> [omega; exact Prod.ext hp_j2 (Prod.ext h.symm hp_n2); omega]
    · left; rcases hn_mem with h | h | h <;> [exact Prod.ext h.symm (Prod.ext hp_j2 hp_n2); omega; omega]
  · right; right; have hp_n3 : p.getD (n - 3) 0 = 2 := (by rw [← hi2_b]; exact hs2.2); have hp_n4 : p.getD (n - 4) 0 = n - 2 := (by rw [← hj2_b, hj2_val.2, hi2_b]; omega); rcases hn_mem with h | h | h <;> [omega; omega; exact Prod.ext hp_n4 (Prod.ext hp_n3 h.symm)]
private theorem mid_mem_iff {n : ℕ} {p : List ℕ} (hlen : p.length = n) (hn : 7 ≤ n) (v : ℕ) : v ∈ (p.drop 2).take (n - 6) ↔ ∃ i, 2 ≤ i ∧ i < n - 4 ∧ p.getD i 0 = v := by
  constructor
  · intro hv; obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hv; have hk_lt : k < n - 6 := (by simp [hlen] at hk; omega); refine ⟨k + 2, by omega, by omega, ?_⟩; rw [List.getElem_take, List.getElem_drop, ← List.getD_eq_getElem p 0 (by omega)]; simp [Nat.add_comm]
  · rintro ⟨i, hi1, hi2, rfl⟩; have hk : i - 2 < ((p.drop 2).take (n - 6)).length := (by simp [hlen]; omega); have hge : ((p.drop 2).take (n - 6))[i - 2]'hk = p.getD i 0 := (by rw [List.getElem_take, List.getElem_drop, ← List.getD_eq_getElem p 0 (by omega), show 2 + (i - 2) = i by omega]); rw [← hge]; exact List.getElem_mem hk
private theorem lemma63_middle (n : ℕ) (hn : 7 ≤ n) (p : List ℕ) (hp : p ∈ indecomposableAvoiders n) (hm : p.getD 0 0 = 4) : let M := (p.drop 2).take (n - 6); ¬ NonnestingDefs.Occurs [3, 1, 2] M ∧ ¬ NonnestingDefs.Occurs [3, 2, 1] M ∧ (((p.getD (n - 4) 0, p.getD (n - 3) 0, p.getD (n - 2) 0) = (n, n - 1, 2) ∨ (p.getD (n - 4) 0, p.getD (n - 3) 0, p.getD (n - 2) 0) = (n - 1, n, 2)) → {v : ℕ | v ∈ M} = {v : ℕ | 5 ≤ v ∧ v ≤ n - 2}) ∧ ((p.getD (n - 4) 0, p.getD (n - 3) 0, p.getD (n - 2) 0) = (n - 2, 2, n) → {v : ℕ | v ∈ M} = ({v : ℕ | 5 ≤ v ∧ v ≤ n - 3} ∪ {n - 1}) ∧ p.getD (n - 5) 0 = n - 1) := by
  have h62 := lemma62_second_and_tail n (by omega) p hp hm; rcases hp with ⟨hpne, ⟨hperm, hav312, hav54321, hav132⟩, hind⟩; have hlen : p.length = n := (by simpa using hperm.length_eq); have hsh := indecomposable_shape_and_prefix_iff.2.2.2.2 n (by omega) p ⟨hpne, ⟨hperm, hav312, hav54321, hav132⟩, hind⟩; have hend : p.getD (n - 1) 0 = 1 := hsh.1.1; dsimp only; let M := (p.drop 2).take (n - 6)
  have hM_sub : M.Sublist p := (List.take_sublist _ _).trans (List.drop_sublist _ _); have hM_len : M.length = n - 6 := (by simp [M, hlen]; omega)
  have hM_get : ∀ k < n - 6, M.getD k 0 = p.getD (k + 2) 0 := fun k hk => by
    rw [List.getD_eq_getElem M 0 (by omega), List.getElem_take, List.getElem_drop,
      ← List.getD_eq_getElem p 0 (by omega), Nat.add_comm]
  have havM312 : ¬ NonnestingDefs.Occurs [3, 1, 2] M := fun h => hav312 (occurs_mono_sublist h hM_sub)
  have havM321 : ¬ NonnestingDefs.Occurs [3, 2, 1] M := by
    rw [occurs_321_iff]; rintro ⟨a, b, c, hab, hbc, hc, h1, h2⟩; rw [hM_len] at hc; rw [hM_get a (by omega)] at h2; rw [hM_get b (by omega)] at h1 h2; rw [hM_get c hc] at h1
    obtain ⟨i2, hi2_1, hi2_2, hi2_val⟩ : ∃ i2, n - 3 ≤ i2 ∧ i2 < n - 1 ∧ p.getD i2 0 = 2 := by
      rcases h62.2 with h | h | h
      · exact ⟨n - 2, by omega, by omega, by injection h with _ h'; injection h'⟩
      · exact ⟨n - 2, by omega, by omega, by injection h with _ h'; injection h'⟩
      · exact ⟨n - 3, le_rfl, by omega, by injection h with _ h'; injection h'⟩
    have hpc_ge3 : 3 ≤ p.getD (c + 2) 0 := (by have hb := perm_getD_bounds hperm (by omega : c + 2 < n); have := ne_val_of_getD hperm (by omega) (by omega) (by omega : c + 2 ≠ n - 1) hend; have := ne_val_of_getD hperm (by omega) (by omega) (by omega : c + 2 ≠ i2) hi2_val; omega)
    exact hav54321 (occurs_54321_of_indices (i₁ := a + 2) (i₂ := b + 2) (i₃ := c + 2) (i₄ := i2) (i₅ := n - 1)
      (by omega) (by omega) (by omega) hi2_2 (by rw [hlen]; omega) (by omega) (by omega) h1 h2)
  have hT12 : ((p.getD (n - 4) 0, p.getD (n - 3) 0, p.getD (n - 2) 0) = (n, n - 1, 2) ∨
      (p.getD (n - 4) 0, p.getD (n - 3) 0, p.getD (n - 2) 0) = (n - 1, n, 2)) →
      {v : ℕ | v ∈ M} = {v : ℕ | 5 ≤ v ∧ v ≤ n - 2} := fun htail => by
    have htail_vals : (p.getD (n - 4) 0 = n ∧ p.getD (n - 3) 0 = n - 1 ∧ p.getD (n - 2) 0 = 2) ∨
        (p.getD (n - 4) 0 = n - 1 ∧ p.getD (n - 3) 0 = n ∧ p.getD (n - 2) 0 = 2) := by
      rcases htail with h | h <;> [left; right] <;>
        (injection h with h1 h'; injection h' with h2 h3; exact ⟨h1, h2, h3⟩)
    ext v; change v ∈ (p.drop 2).take (n - 6) ↔ 5 ≤ v ∧ v ≤ n - 2; rw [mid_mem_iff hlen hn]; constructor
    · rintro ⟨i, hi1, hi2, rfl⟩
      have hb := perm_getD_bounds hperm (by omega : i < n); have := ne_val_of_getD hperm (by omega) (by omega) (by omega : i ≠ 0) hm; have := ne_val_of_getD hperm (by omega) (by omega) (by omega : i ≠ 1) h62.1; have := ne_val_of_getD hperm (by omega) (by omega) (by omega : i ≠ n - 1) hend; have := ne_val_of_getD hperm (by omega) (by omega) (by omega : i ≠ n - 4) rfl
      have := ne_val_of_getD hperm (by omega) (by omega) (by omega : i ≠ n - 3) rfl; have := ne_val_of_getD hperm (by omega) (by omega) (by omega : i ≠ n - 2) rfl; omega
    · rintro ⟨hv1, hv2⟩
      have hs := perm_idxOf_spec hperm v (by omega) (by omega); have := idxOf_ne_of_getD hperm v 0 (by omega) (by omega) (by omega); have := idxOf_ne_of_getD hperm v 1 (by omega) (by omega) (by omega); have := idxOf_ne_of_getD hperm v (n - 4) (by omega) (by omega) (by omega); have := idxOf_ne_of_getD hperm v (n - 3) (by omega) (by omega) (by omega); have := idxOf_ne_of_getD hperm v (n - 2) (by omega) (by omega) (by omega)
      have := idxOf_ne_of_getD hperm v (n - 1) (by omega) (by omega) (by omega); exact ⟨p.idxOf v, by omega, by omega, hs.2⟩
  have hT3 : (p.getD (n - 4) 0, p.getD (n - 3) 0, p.getD (n - 2) 0) = (n - 2, 2, n) →
      {v : ℕ | v ∈ M} = ({v : ℕ | 5 ≤ v ∧ v ≤ n - 3} ∪ {n - 1}) ∧ p.getD (n - 5) 0 = n - 1 := fun h => by
    injection h with hp_n4 h'; injection h' with hp_n3 hp_n2
    have hV : {v : ℕ | v ∈ M} = ({v : ℕ | 5 ≤ v ∧ v ≤ n - 3} ∪ {n - 1}) := by
      ext v; change v ∈ (p.drop 2).take (n - 6) ↔ (5 ≤ v ∧ v ≤ n - 3) ∨ v = n - 1; rw [mid_mem_iff hlen hn]; constructor
      · rintro ⟨i, hi1, hi2, rfl⟩
        have hb := perm_getD_bounds hperm (by omega : i < n); have := ne_val_of_getD hperm (by omega) (by omega) (by omega : i ≠ 0) hm; have := ne_val_of_getD hperm (by omega) (by omega) (by omega : i ≠ 1) h62.1; have := ne_val_of_getD hperm (by omega) (by omega) (by omega : i ≠ n - 4) hp_n4; have := ne_val_of_getD hperm (by omega) (by omega) (by omega : i ≠ n - 3) hp_n3
        have := ne_val_of_getD hperm (by omega) (by omega) (by omega : i ≠ n - 2) hp_n2; have := ne_val_of_getD hperm (by omega) (by omega) (by omega : i ≠ n - 1) hend; omega
      · intro hv
        have hs := perm_idxOf_spec hperm v (by omega) (by omega); have := idxOf_ne_of_getD hperm v 0 (by omega) (by omega) (by omega); have := idxOf_ne_of_getD hperm v 1 (by omega) (by omega) (by omega); have := idxOf_ne_of_getD hperm v (n - 4) (by omega) (by omega) (by omega); have := idxOf_ne_of_getD hperm v (n - 3) (by omega) (by omega) (by omega); have := idxOf_ne_of_getD hperm v (n - 2) (by omega) (by omega) (by omega)
        have := idxOf_ne_of_getD hperm v (n - 1) (by omega) (by omega) (by omega); exact ⟨p.idxOf v, by omega, by omega, hs.2⟩
    refine ⟨hV, ?_⟩; have hmem_n1 : n - 1 ∈ {v : ℕ | v ∈ M} := (by rw [hV]; right; rfl); obtain ⟨i, hi1, hi2, hi_val⟩ := (mid_mem_iff hlen hn (n - 1)).mp hmem_n1
    by_cases hieq : i = n - 5
    · rwa [← hieq]
    · have hm5 : p.getD (n - 5) 0 ∈ {v : ℕ | v ∈ M} := (mid_mem_iff hlen hn _).mpr ⟨n - 5, by omega, by omega, rfl⟩
      rw [hV] at hm5; change (5 ≤ p.getD (n - 5) 0 ∧ p.getD (n - 5) 0 ≤ n - 3) ∨ p.getD (n - 5) 0 = n - 1 at hm5; have hne_n1 := ne_val_of_getD hperm (by omega) (by omega) (fun h => hieq h.symm : n - 5 ≠ i) hi_val
      have hm5_bnd : 5 ≤ p.getD (n - 5) 0 ∧ p.getD (n - 5) 0 ≤ n - 3 := (by omega)
      exact False.elim (hav312 (occurs_312_of_indices (i := i) (j := n - 5) (k := n - 4)
        (by omega) (by omega) (by rw [hlen]; omega) (by omega) (by omega)))
  exact ⟨havM312, havM321, hT12, hT3⟩
/-- Tail permutation of the square, second entry and tail types, and middle-segment avoidance and
    value sets for indecomposable square-avoiders with first entry four. -/
theorem first_entry_four_structure :
    (∀ n : ℕ, 4 ≤ n → ∀ p ∈ indecomposableAvoiders n, p.getD 0 0 = 4 →
      ((square p).drop (n - 4)).Perm [1, 2, 3, 4] ∧ (square p).getD (n - 1) 0 = 4 ∧
      ({p.getD (n - 4) 0, p.getD (n - 3) 0, p.getD (n - 2) 0} : Set ℕ) =
        {n, p.idxOf 2 + 1, p.idxOf 3 + 1}) ∧
    (∀ n : ℕ, 5 ≤ n → ∀ p ∈ indecomposableAvoiders n, p.getD 0 0 = 4 →
      p.getD 1 0 = 3 ∧
      ((p.getD (n - 4) 0, p.getD (n - 3) 0, p.getD (n - 2) 0) = (n, n - 1, 2) ∨
       (p.getD (n - 4) 0, p.getD (n - 3) 0, p.getD (n - 2) 0) = (n - 1, n, 2) ∨
       (p.getD (n - 4) 0, p.getD (n - 3) 0, p.getD (n - 2) 0) = (n - 2, 2, n))) ∧
    (∀ n : ℕ, 7 ≤ n → ∀ p ∈ indecomposableAvoiders n, p.getD 0 0 = 4 →
      let M := (p.drop 2).take (n - 6)
      ¬ NonnestingDefs.Occurs [3, 1, 2] M ∧ ¬ NonnestingDefs.Occurs [3, 2, 1] M ∧
      (((p.getD (n - 4) 0, p.getD (n - 3) 0, p.getD (n - 2) 0) = (n, n - 1, 2) ∨
        (p.getD (n - 4) 0, p.getD (n - 3) 0, p.getD (n - 2) 0) = (n - 1, n, 2)) →
        {v : ℕ | v ∈ M} = {v : ℕ | 5 ≤ v ∧ v ≤ n - 2}) ∧
      ((p.getD (n - 4) 0, p.getD (n - 3) 0, p.getD (n - 2) 0) = (n - 2, 2, n) →
        {v : ℕ | v ∈ M} = ({v : ℕ | 5 ≤ v ∧ v ≤ n - 3} ∪ {n - 1}) ∧
        p.getD (n - 5) 0 = n - 1)) :=
  ⟨lemma61_tail, lemma62_second_and_tail, lemma63_middle⟩
private theorem strictMono_Ico_eq {a b v₀ : ℕ} {f : ℕ → ℕ} (hbnd : ∀ i, a ≤ i → i < b → v₀ ≤ f i ∧ f i < v₀ + (b - a)) (hmono : ∀ i j, a ≤ i → i < j → j < b → f i < f j) : ∀ i, a ≤ i → i < b → f i = v₀ + (i - a) := by
  have hlow : ∀ t, a + t < b → v₀ + t ≤ f (a + t) := fun t ht => by
    induction t with
    | zero => simpa using (hbnd a le_rfl (by simpa using ht)).1
    | succ t ih => have := ih (by omega); have := hmono (a + t) (a + (t + 1)) (by omega) (by omega) ht; omega
  have hhigh : ∀ t, a + t < b → f (b - 1 - t) + t < v₀ + (b - a) := fun t ht => by
    induction t with
    | zero => simpa using (hbnd (b - 1) (by omega) (by omega)).2
    | succ t ih => have := ih (by omega); have := hmono (b - 1 - (t + 1)) (b - 1 - t) (by omega) (by omega) (by omega); omega
  intro i hai hib; have h1 := hlow (i - a) (by omega); have h2 := hhigh (b - 1 - i) (by omega); rw [show a + (i - a) = i by omega] at h1; rw [show b - 1 - (b - 1 - i) = i by omega] at h2; omega
private theorem strictMono_skip1_eq {a b x v₀ : ℕ} {f : ℕ → ℕ} (hx : a ≤ x ∧ x < b) (hbnd : ∀ i, a ≤ i → i < b → i ≠ x → v₀ ≤ f i ∧ f i < v₀ + (b - 1 - a)) (hmono : ∀ i j, a ≤ i → i < j → j < b → i ≠ x → j ≠ x → f i < f j) : (∀ i, a ≤ i → i < x → f i = v₀ + (i - a)) ∧ (∀ i, x < i → i < b → f i = v₀ + (i - 1 - a)) := by
  let g : ℕ → ℕ := fun i => if i < x then f i else f (i + 1)
  have hg := strictMono_Ico_eq (a := a) (b := b - 1) (v₀ := v₀) (f := g)
    (fun i hai hib => by dsimp [g]; split <;> exact hbnd _ (by omega) (by omega) (by omega))
    (fun i j hai hij hjb => by
      dsimp [g]; by_cases c1 : i < x <;> by_cases c2 : j < x <;> simp only [c1, c2, ↓reduceIte]
      · exact hmono _ _ (by omega) (by omega) (by omega) (by omega) (by omega)
      · exact hmono _ _ (by omega) (by omega) (by omega) (by omega) (by omega)
      · omega
      · exact hmono _ _ (by omega) (by omega) (by omega) (by omega) (by omega))
  refine ⟨fun i hai hix => ?_, fun i hxi hib => ?_⟩
  · have h := hg i hai (by omega); dsimp [g] at h; simpa [hix] using h
  · have h := hg (i - 1) (by omega) (by omega); dsimp [g] at h; have hnot : ¬ i - 1 < x := (by omega); simp only [hnot, ↓reduceIte, show i - 1 + 1 = i by omega] at h; exact h
private theorem list_eq_of_getD {n : ℕ} {p q : List ℕ} (hp : p.length = n) (hq : q.length = n) (h : ∀ i < n, p.getD i 0 = q.getD i 0) : p = q := by
  apply List.ext_getElem (hp.trans hq.symm); intro i hi₁ hi₂; have h1 := h i (by omega); rwa [List.getD_eq_getElem p 0 hi₁, List.getD_eq_getElem q 0 hi₂] at h1
private theorem getD_app_left {a b : List ℕ} {i : ℕ} (h : i < a.length) : (a ++ b).getD i 0 = a.getD i 0 := List.getD_append a b 0 i h
private theorem getD_app_right {a b : List ℕ} {i : ℕ} (h : a.length ≤ i) : (a ++ b).getD i 0 = b.getD (i - a.length) 0 := List.getD_append_right a b 0 i h
private theorem flatMap_pair_length (m c₁ c₂ : ℕ) : ((List.range m).flatMap fun r => [2 * r + c₁, 2 * r + c₂]).length = 2 * m := by
  induction m with
  | zero => rfl
  | succ m ih => rw [List.range_succ, List.flatMap_append, List.length_append, ih]; simp; omega
private theorem flatMap_pair_getD (m c₁ c₂ k : ℕ) (hk : k < 2 * m) : ((List.range m).flatMap fun r => [2 * r + c₁, 2 * r + c₂]).getD k 0 = if k % 2 = 0 then k + c₁ else k - 1 + c₂ := by
  induction m generalizing k with
  | zero => omega
  | succ m ih =>
    rw [List.range_succ, List.flatMap_append]
    have hlen : ((List.range m).flatMap fun r => [2 * r + c₁, 2 * r + c₂]).length = 2 * m :=
      flatMap_pair_length m c₁ c₂
    by_cases hlt : k < 2 * m
    · rw [getD_app_left (by omega), ih k hlt]
    · rw [getD_app_right (by omega), hlen]; simp only [List.flatMap_singleton]
      rcases (by omega : k = 2 * m ∨ k = 2 * m + 1) with rfl | rfl
      · rw [Nat.sub_self]; change 2 * m + c₁ = _; split <;> omega
      · rw [Nat.add_sub_cancel_left]; change 2 * m + c₂ = _; split <;> omega
private theorem getD_range' (s l i : ℕ) (hi : i < l) : (List.range' s l).getD i 0 = s + i := by
  rw [List.getD_eq_getElem _ 0 (by simp [hi])]; simp
private theorem familyA_len_getD (n : ℕ) (hn : 6 ≤ n) : (familyA n).length = n ∧ ∀ i < n, (familyA n).getD i 0 = if i = 0 then 4 else if i = 1 then 3 else if i < n - 2 then i + 3 else if i = n - 2 then 2 else 1 := by
  refine ⟨by unfold familyA; simp; omega, fun i hi => ?_⟩
  unfold familyA; by_cases h2 : i < 2
  · rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> rfl
  by_cases h : i < n - 2
  · rw [List.append_assoc, getD_app_right (by simp; omega), getD_app_left (by simp; omega)]; change (List.range' 5 (n - 4)).getD (i - 2) 0 = _; rw [getD_range' 5 (n - 4) (i - 2) (by omega)]; repeat' (split <;> try omega)
  · rw [getD_app_right (by simp; omega)]
    have hlen : ([4, 3] ++ List.range' 5 (n - 4)).length = n - 2 := (by simp; omega); rw [hlen]; rcases (by omega : i = n - 2 ∨ i = n - 1) with rfl | rfl
    · rw [Nat.sub_self]; change 2 = _; repeat' (split <;> try omega)
    · rw [show n - 1 - (n - 2) = 1 by omega]; change 1 = _; repeat' (split <;> try omega)
private theorem familyB_len_getD (n : ℕ) (hn : 7 ≤ n) : (familyB n).length = n ∧ ∀ i < n, (familyB n).getD i 0 = if i = 0 then 4 else if i = 1 then 3 else if i = 2 then 5 else if i < 3 + 2 * ((n - 5) / 2) then (if i % 2 = 1 then i + 4 else i + 2) else if n % 2 = 1 then (if i = n - 2 then 2 else 1) else (if i = n - 3 then 2 else if i = n - 2 then n else 1) := by
  let mid := (List.range ((n - 5) / 2)).flatMap fun r => [2 * r + 7, 2 * r + 6]
  have hmid : mid.length = 2 * ((n - 5) / 2) := flatMap_pair_length ((n - 5) / 2) 7 6; refine ⟨by unfold familyB; by_cases hp : n % 2 = 1 <;> simp [hp, mid, hmid] <;> omega, fun i hi => ?_⟩
  unfold familyB; change ([4, 3, 5] ++ mid ++ (if n % 2 = 1 then [2, 1] else [2, n, 1])).getD i 0 = _
  by_cases h3 : i < 3
  · rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;> rfl
  by_cases hm : i < 3 + 2 * ((n - 5) / 2)
  · rw [getD_app_left (by simp [hmid]; omega), getD_app_right (by simp; omega)]; change mid.getD (i - 3) 0 = _; rw [flatMap_pair_getD ((n - 5) / 2) 7 6 (i - 3) (by omega)]; repeat' (split <;> try omega)
  · rw [getD_app_right (by simp [hmid]; omega)]
    have hlen : ([4, 3, 5] ++ mid).length = 3 + 2 * ((n - 5) / 2) := (by simp [hmid]; omega); rw [hlen]; by_cases hp : n % 2 = 1
    · simp only [hp, ↓reduceIte, show 3 + 2 * ((n - 5) / 2) = n - 2 by omega]
      rcases (by omega : i = n - 2 ∨ i = n - 1) with rfl | rfl
      · rw [Nat.sub_self]; change 2 = _; repeat' (split <;> try omega)
      · rw [show n - 1 - (n - 2) = 1 by omega]; change 1 = _; repeat' (split <;> try omega)
    · simp only [hp, ↓reduceIte, show 3 + 2 * ((n - 5) / 2) = n - 3 by omega]
      rcases (by omega : i = n - 3 ∨ i = n - 2 ∨ i = n - 1) with rfl | rfl | rfl
      · rw [Nat.sub_self]; change 2 = _; repeat' (split <;> try omega)
      · rw [show n - 2 - (n - 3) = 1 by omega]; change n = _; repeat' (split <;> try omega)
      · rw [show n - 1 - (n - 3) = 2 by omega]; change 1 = _; repeat' (split <;> try omega)
private theorem familyC_len_getD (n : ℕ) (hn : 4 ≤ n) : (familyC n).length = n ∧ ∀ i < n, (familyC n).getD i 0 = if i = 0 then 4 else if i = 1 then 3 else if i < 2 + 2 * ((n - 4) / 2) then (if i % 2 = 0 then i + 4 else i + 2) else if n % 2 = 0 then (if i = n - 2 then 2 else 1) else (if i = n - 3 then 2 else if i = n - 2 then n else 1) := by
  let mid := (List.range ((n - 4) / 2)).flatMap fun r => [2 * r + 6, 2 * r + 5]
  have hmid : mid.length = 2 * ((n - 4) / 2) := flatMap_pair_length ((n - 4) / 2) 6 5; refine ⟨by unfold familyC; by_cases hp : n % 2 = 0 <;> simp [hp, mid, hmid] <;> omega, fun i hi => ?_⟩
  unfold familyC; change ([4, 3] ++ mid ++ (if n % 2 = 0 then [2, 1] else [2, n, 1])).getD i 0 = _
  by_cases h2 : i < 2
  · rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> rfl
  by_cases hm : i < 2 + 2 * ((n - 4) / 2)
  · rw [getD_app_left (by simp [hmid]; omega), getD_app_right (by simp; omega)]; change mid.getD (i - 2) 0 = _; rw [flatMap_pair_getD ((n - 4) / 2) 6 5 (i - 2) (by omega)]; repeat' (split <;> try omega)
  · rw [getD_app_right (by simp [hmid]; omega)]
    have hlen : ([4, 3] ++ mid).length = 2 + 2 * ((n - 4) / 2) := (by simp [hmid]; omega); rw [hlen]; by_cases hp : n % 2 = 0
    · simp only [hp, ↓reduceIte, show 2 + 2 * ((n - 4) / 2) = n - 2 by omega]
      rcases (by omega : i = n - 2 ∨ i = n - 1) with rfl | rfl
      · rw [Nat.sub_self]; change 2 = _; repeat' (split <;> try omega)
      · rw [show n - 1 - (n - 2) = 1 by omega]; change 1 = _; repeat' (split <;> try omega)
    · simp only [hp, ↓reduceIte, show 2 + 2 * ((n - 4) / 2) = n - 3 by omega]
      rcases (by omega : i = n - 3 ∨ i = n - 2 ∨ i = n - 1) with rfl | rfl | rfl
      · rw [Nat.sub_self]; change 2 = _; repeat' (split <;> try omega)
      · rw [show n - 2 - (n - 3) = 1 by omega]; change n = _; repeat' (split <;> try omega)
      · rw [show n - 1 - (n - 3) = 2 by omega]; change 1 = _; repeat' (split <;> try omega)
private theorem familyD_len_getD (n : ℕ) (hn : 9 ≤ n) : (familyD n).length = n ∧ ∀ i < n, (familyD n).getD i 0 = if i = 0 then 4 else if i = 1 then 3 else if i = 2 then 6 else if i = 3 then 7 else if i = 4 then 5 else if i < n - 2 then i + 3 else if i = n - 2 then 2 else 1 := by
  refine ⟨by unfold familyD; simp; omega, fun i hi => ?_⟩
  unfold familyD; by_cases h5 : i < 5
  · rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl | rfl <;> rfl
  by_cases h : i < n - 2
  · rw [List.append_assoc, getD_app_right (by simp; omega), getD_app_left (by simp; omega)]; change (List.range' 8 (n - 7)).getD (i - 5) 0 = _; rw [getD_range' 8 (n - 7) (i - 5) (by omega)]; repeat' (split <;> try omega)
  · rw [getD_app_right (by simp; omega)]
    have hlen : ([4, 3, 6, 7, 5] ++ List.range' 8 (n - 7)).length = n - 2 := (by simp; omega); rw [hlen]; rcases (by omega : i = n - 2 ∨ i = n - 1) with rfl | rfl
    · rw [Nat.sub_self]; change 2 = _; repeat' (split <;> try omega)
    · rw [show n - 1 - (n - 2) = 1 by omega]; change 1 = _; repeat' (split <;> try omega)
private theorem prop64_prefix_and_sq {n : ℕ} (hn : 8 ≤ n) {p : List ℕ} (hp : p ∈ indecomposableAvoiders n) (hm : p.getD 0 0 = 4) : p.getD 1 0 = 3 ∧ p.getD (n - 1) 0 = 1 ∧ 2 ≤ p.idxOf 5 ∧ p.idxOf 5 ≤ n - 5 ∧ ((p.getD (n - 4) 0, p.getD (n - 3) 0, p.getD (n - 2) 0) = (n - 2, 2, n) → p.idxOf 5 ≤ n - 6) ∧ (∀ i, 2 ≤ i → i < p.idxOf 5 → p.getD i 0 = i + 4) ∧ (∀ j < n - 4, 5 ≤ (square p).getD j 0 ∧ (square p).getD j 0 ≤ n) ∧ (square p).idxOf 5 < n - 4 ∧ (square p).getD ((square p).idxOf 5) 0 = 5 ∧ (∀ i j, (square p).idxOf 5 < i → i < j → j < n - 4 → (square p).getD i 0 < (square p).getD j 0) := by
  have h61 := lemma61_tail n (by omega) p hp hm; have h62 := lemma62_second_and_tail n (by omega) p hp hm; have h63 := lemma63_middle n (by omega) p hp hm; dsimp only at h63; rcases hp with ⟨hpne, ⟨hperm, hav312, hav54321, hav132⟩, hind⟩; have hlen : p.length = n := (by simpa using hperm.length_eq); have hsq := square_perm_and_getD hperm; have hqlen : (square p).length = n := (by simpa using hsq.1.length_eq)
  have hsh := indecomposable_shape_and_prefix_iff.2.2.2.2 n (by omega) p ⟨hpne, ⟨hperm, hav312, hav54321, hav132⟩, hind⟩; have hend : p.getD (n - 1) 0 = 1 := hsh.1.1; let M := (p.drop 2).take (n - 6); have hM_len : M.length = n - 6 := (by simp [M, hlen]; omega)
  have hM_get : ∀ k < n - 6, M.getD k 0 = p.getD (k + 2) 0 := fun k hk => by
    rw [List.getD_eq_getElem M 0 (by omega), List.getElem_take, List.getElem_drop,
      ← List.getD_eq_getElem p 0 (by omega), Nat.add_comm]
  have h5_mem : 5 ∈ M := by
    rcases h62.2 with h1 | h2 | h3
    · have hv := h63.2.2.1 (Or.inl h1); change 5 ∈ {v | v ∈ M}; rw [hv]; change 5 ≤ 5 ∧ 5 ≤ n - 2; omega
    · have hv := h63.2.2.1 (Or.inr h2); change 5 ∈ {v | v ∈ M}; rw [hv]; change 5 ≤ 5 ∧ 5 ≤ n - 2; omega
    · have hv := (h63.2.2.2 h3).1; change 5 ∈ {v | v ∈ M}; rw [hv]; left; change 5 ≤ 5 ∧ 5 ≤ n - 3; omega
  obtain ⟨i5, hi5_1, hi5_2, hi5_eq⟩ := (mid_mem_iff hlen (by omega) 5).mp h5_mem; have hiw_eq : p.idxOf 5 = i5 := (by rw [← hi5_eq]; exact perm_idxOf_getD hperm (by omega)); let iw := p.idxOf 5; have hiw_bnd : 2 ≤ iw ∧ iw ≤ n - 5 := ⟨by omega, by omega⟩
  have hiw_T3 : (p.getD (n - 4) 0, p.getD (n - 3) 0, p.getD (n - 2) 0) = (n - 2, 2, n) → iw ≤ n - 6 := fun h => by
    have hn5 := (h63.2.2.2 h).2; have hne : iw ≠ n - 5 := idxOf_ne_of_getD hperm 5 (n - 5) (by omega) (by omega) (by omega); omega
  have hs5 : iw < n ∧ p.getD iw 0 = 5 := perm_idxOf_spec hperm 5 (by omega) (by omega); have hpre_val : ∀ i, 2 ≤ i → i < iw → 6 ≤ p.getD i 0 ∧ p.getD i 0 ≤ n - 2 ∧
      ((p.getD (n - 4) 0, p.getD (n - 3) 0, p.getD (n - 2) 0) = (n - 2, 2, n) → p.getD i 0 ≤ n - 3) := by
    intro i hi1 hi2; have hmem : p.getD i 0 ∈ {v | v ∈ M} := (mid_mem_iff hlen (by omega) _).mpr ⟨i, hi1, by omega, rfl⟩; have hne5 := ne_val_of_getD hperm (by omega) hs5.1 (by omega : i ≠ iw) hs5.2; rcases h62.2 with h1 | h2 | h3
    · rw [h63.2.2.1 (Or.inl h1)] at hmem; change 5 ≤ p.getD i 0 ∧ p.getD i 0 ≤ n - 2 at hmem; refine ⟨by omega, by omega, fun h => ?_⟩; rw [h1] at h; injection h with h'; omega
    · rw [h63.2.2.1 (Or.inr h2)] at hmem; change 5 ≤ p.getD i 0 ∧ p.getD i 0 ≤ n - 2 at hmem; refine ⟨by omega, by omega, fun h => ?_⟩; rw [h2] at h; injection h with h'; omega
    · have ht := h63.2.2.2 h3; rw [ht.1] at hmem; change (5 ≤ p.getD i 0 ∧ p.getD i 0 ≤ n - 3) ∨ p.getD i 0 = n - 1 at hmem; have := hiw_T3 h3; have hne_n1 := ne_val_of_getD hperm (by omega) (by omega) (by omega : i ≠ n - 5) ht.2; omega
  have hpre_mono : ∀ i j, 2 ≤ i → i < j → j < iw → p.getD i 0 < p.getD j 0 := by
    intro i j hi1 hij hj2; have hne := ne_val_of_getD hperm (by omega) (by omega) (by omega : i ≠ j) rfl; have hj_ge6 := (hpre_val j (by omega) hj2).1; by_contra hnot; refine h63.2.1 ((occurs_321_iff M).mpr ⟨i - 2, j - 2, iw - 2, by omega, by omega, by rw [hM_len]; omega, ?_, ?_⟩)
    · rw [hM_get (iw - 2) (by omega), hM_get (j - 2) (by omega), show iw - 2 + 2 = iw by omega,
        show j - 2 + 2 = j by omega]; omega
    · rw [hM_get (j - 2) (by omega), hM_get (i - 2) (by omega), show j - 2 + 2 = j by omega,
        show i - 2 + 2 = i by omega]; omega
  have hpre_ub : ∀ i, 2 ≤ i → i < iw → p.getD i 0 < 6 + (iw - 2) := fun i hi1 hi2 => by
    have hv := hpre_val i hi1 hi2
    have hinj : Set.InjOn (fun e => p.idxOf e) (Finset.Icc 6 (p.getD i 0)) := fun x hx y hy hxy => by
      rw [Finset.mem_coe, Finset.mem_Icc] at hx hy; have sx := (perm_idxOf_spec hperm x (by omega) (by omega)).2; have sy := (perm_idxOf_spec hperm y (by omega) (by omega)).2; dsimp only at hxy; rw [← sx, hxy, sy]
    have hsub : (Finset.Icc 6 (p.getD i 0)).image (fun e => p.idxOf e) ⊆ Finset.Ico 2 iw := by
      intro idx hidx; obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hidx; rw [Finset.mem_Icc] at he
      have heM : e ∈ {v | v ∈ M} := by
        rcases h62.2 with h1 | h2 | h3
        · rw [h63.2.2.1 (Or.inl h1)]; change 5 ≤ e ∧ e ≤ n - 2; omega
        · rw [h63.2.2.1 (Or.inr h2)]; change 5 ≤ e ∧ e ≤ n - 2; omega
        · rw [(h63.2.2.2 h3).1]; left; change 5 ≤ e ∧ e ≤ n - 3; have := hv.2.2 h3; omega
      obtain ⟨je, hje1, hje2, hje_eq⟩ := (mid_mem_iff hlen (by omega) e).mp heM; have hid_eq : p.idxOf e = je := (by rw [← hje_eq]; exact perm_idxOf_getD hperm (by omega)); rw [hid_eq, Finset.mem_Ico]; refine ⟨hje1, ?_⟩; have hne_iw : je ≠ iw := fun h => by rw [h, hs5.2] at hje_eq; omega
      by_cases hev : e = p.getD i 0
      · have := perm_getD_inj hperm (by omega) (by omega) (hje_eq.trans hev); omega
      · by_contra hgt; exact hav312 (occurs_312_of_indices (i := i) (j := iw) (k := je) hi2 (by omega) (by rw [hlen]; omega) (by omega) (by omega))
    have hc := Finset.card_le_card hsub; rw [Finset.card_image_of_injOn hinj, Nat.card_Icc, Nat.card_Ico] at hc; omega
  have hpre_eq : ∀ i, 2 ≤ i → i < iw → p.getD i 0 = i + 4 := fun i hi1 hi2 => by
    have := strictMono_Ico_eq (a := 2) (b := iw) (v₀ := 6) (f := fun k => p.getD k 0)
      (fun k hk1 hk2 => ⟨(hpre_val k hk1 hk2).1, hpre_ub k hk1 hk2⟩) hpre_mono i hi1 hi2
    omega
  have hqbnd : ∀ j < n - 4, 5 ≤ (square p).getD j 0 ∧ (square p).getD j 0 ≤ n := fun j hj => by
    have hb := perm_getD_bounds hsq.1 (by omega : j < n); refine ⟨?_, hb.2⟩; by_contra hlt
    have hmem : (square p).getD j 0 ∈ (square p).drop (n - 4) :=
      h61.1.mem_iff.mpr (by simp only [List.mem_cons, List.not_mem_nil, or_false]; omega)
    obtain ⟨idx, hidx, heq⟩ := List.getElem_of_mem hmem; have hidx_lt : n - 4 + idx < n := (by rw [List.length_drop, hqlen] at hidx; omega); rw [List.getElem_drop, ← List.getD_eq_getElem (square p) 0 (by rw [hqlen]; omega)] at heq; have := perm_getD_inj hsq.1 hidx_lt (by omega : j < n) heq; omega
  have hsq5 := perm_idxOf_spec hsq.1 5 (by omega) (by omega)
  have hsq5_lt : (square p).idxOf 5 < n - 4 := by
    by_contra hge; have hk : (square p).idxOf 5 - (n - 4) < ((square p).drop (n - 4)).length := (by simp [hqlen]; omega)
    have hmem : ((square p).drop (n - 4))[(square p).idxOf 5 - (n - 4)]'hk ∈ ([1, 2, 3, 4] : List ℕ) :=
      h61.1.mem_iff.mp (List.getElem_mem hk)
    rw [List.getElem_drop, ← List.getD_eq_getElem (square p) 0 (by rw [hqlen]; omega),
      show n - 4 + ((square p).idxOf 5 - (n - 4)) = (square p).idxOf 5 by omega, hsq5.2] at hmem
    simp at hmem
  have hq_mono : ∀ i j, (square p).idxOf 5 < i → i < j → j < n - 4 → (square p).getD i 0 < (square p).getD j 0 := by
    intro i j hi hij hj; have hne := ne_val_of_getD hsq.1 (by omega) (by omega) (by omega : i ≠ j) rfl; have := (hqbnd i (by omega)).1; have := (hqbnd j hj).1; have := ne_val_of_getD hsq.1 (by omega) hsq5.1 (by omega : i ≠ (square p).idxOf 5) hsq5.2; have := ne_val_of_getD hsq.1 (by omega) hsq5.1 (by omega : j ≠ (square p).idxOf 5) hsq5.2; by_contra hnot
    exact hav132 (occurs_132_of_indices hi hij (by rw [hqlen]; omega) (by omega) (by omega))
  exact ⟨h62.1, hend, hiw_bnd.1, hiw_bnd.2, hiw_T3, hpre_eq, hqbnd, hsq5_lt, hsq5.2, hq_mono⟩
private theorem prop64_w4 {n : ℕ} (hn : 8 ≤ n) {p : List ℕ} (hp : p ∈ indecomposableAvoiders n) (hm : p.getD 0 0 = 4) (hiw : p.idxOf 5 = 3) : p = familyC n := by
  have hpre := prop64_prefix_and_sq hn hp hm; have h62 := lemma62_second_and_tail n (by omega) p hp hm; rcases hp with ⟨_, ⟨hperm, _⟩, _⟩; have hlen : p.length = n := (by simpa using hperm.length_eq); have hsq := square_perm_and_getD hperm; have hp2 : p.getD 2 0 = 6 := (by have := hpre.2.2.2.2.2.1 2 le_rfl (by omega); omega); have hp3 : p.getD 3 0 = 5 := (by rw [← hiw]; exact (perm_idxOf_spec hperm 5 (by omega) (by omega)).2)
  have hq0 : (square p).getD 0 0 = 5 := (by rw [hsq.2 0 (by omega), hm]; exact hp3); have hix5 : (square p).idxOf 5 = 0 := (by rw [← hq0]; exact perm_idxOf_getD hsq.1 (by omega))
  have hq_eq : ∀ i < n - 4, (square p).getD i 0 = i + 5 := fun i hi => by
    by_cases hi0 : i = 0
    · subst i; exact hq0
    · have h := strictMono_Ico_eq (a := 1) (b := n - 4) (v₀ := 6) (f := fun k => (square p).getD k 0)
        (fun k hk1 hk2 => by
          have hb := hpre.2.2.2.2.2.2.1 k hk2
          have := ne_val_of_getD hsq.1 (by omega) (by omega) (by omega : k ≠ 0) hq0; omega)
        (fun i j hi1 hij hj2 => hpre.2.2.2.2.2.2.2.2.2 i j (by omega) hij hj2) i (by omega) hi
      omega
  have hpair : ∀ r, 2 * r + 3 ≤ n - 3 → p.getD (2 * r + 2) 0 = 2 * r + 6 ∧ p.getD (2 * r + 3) 0 = 2 * r + 5 := by
    intro r hr; induction r with
    | zero => exact ⟨hp2, hp3⟩
    | succ r ih =>
      obtain ⟨h1, h2⟩ := ih (by omega); have qa := hq_eq (2 * r + 2) (by omega); have qb := hq_eq (2 * r + 3) (by omega); have sa := hsq.2 (2 * r + 2) (by omega); rw [qa, h1, show 2 * r + 6 - 1 = 2 * (r + 1) + 3 by omega] at sa; have sb := hsq.2 (2 * r + 3) (by omega); rw [qb, h2, show 2 * r + 5 - 1 = 2 * (r + 1) + 2 by omega] at sb; exact ⟨sb.symm, sa.symm⟩
  have hC := familyC_len_getD n (by omega); refine list_eq_of_getD hlen hC.1 fun i hi => ?_
  rw [hC.2 i hi]
  by_cases hp_ev : n % 2 = 0
  · have hend_pair := hpair ((n - 6) / 2) (by omega)
    rw [show 2 * ((n - 6) / 2) + 2 = n - 4 by omega, show 2 * ((n - 6) / 2) + 6 = n by omega] at hend_pair; have hp_n2 : p.getD (n - 2) 0 = 2 := (by rcases h62.2 with h | h | h <;> (injection h with h1 h'; injection h' with h2 h3; try omega))
    by_cases h01 : i < 2
    · rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> [exact hm; exact hpre.1]
    by_cases hm_i : i < n - 2
    · by_cases hi_ev : i % 2 = 0
      · have := (hpair ((i - 2) / 2) (by omega)).1; rw [show 2 * ((i - 2) / 2) + 2 = i by omega] at this; simp only [hp_ev, hi_ev, ↓reduceIte]; repeat' (split <;> try omega)
      · have := (hpair ((i - 3) / 2) (by omega)).2; rw [show 2 * ((i - 3) / 2) + 3 = i by omega] at this; simp only [hp_ev, hi_ev, ↓reduceIte]; repeat' (split <;> try omega)
    · have hend := hpre.2.1
      rcases (by omega : i = n - 2 ∨ i = n - 1) with rfl | rfl <;>
        (simp only [hp_ev, ↓reduceIte]; repeat' (split <;> try omega))
  · have hend_pair := hpair ((n - 7) / 2) (by omega)
    rw [show 2 * ((n - 7) / 2) + 3 = n - 4 by omega, show 2 * ((n - 7) / 2) + 5 = n - 2 by omega] at hend_pair; have htail : p.getD (n - 3) 0 = 2 ∧ p.getD (n - 2) 0 = n := (by rcases h62.2 with h | h | h <;> (injection h with h1 h'; injection h' with h2 h3; try omega))
    by_cases h01 : i < 2
    · rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> [exact hm; exact hpre.1]
    by_cases hm_i : i < n - 3
    · by_cases hi_ev : i % 2 = 0
      · have := (hpair ((i - 2) / 2) (by omega)).1; rw [show 2 * ((i - 2) / 2) + 2 = i by omega] at this; simp only [hp_ev, hi_ev, ↓reduceIte]; repeat' (split <;> try omega)
      · have := (hpair ((i - 3) / 2) (by omega)).2; rw [show 2 * ((i - 3) / 2) + 3 = i by omega] at this; simp only [hp_ev, hi_ev, ↓reduceIte]; repeat' (split <;> try omega)
    · have hend := hpre.2.1
      rcases (by omega : i = n - 3 ∨ i = n - 2 ∨ i = n - 1) with rfl | rfl | rfl <;>
        (simp only [hp_ev, ↓reduceIte]; repeat' (split <;> try omega))
private theorem prop64_w3 {n : ℕ} (hn : 8 ≤ n) {p : List ℕ} (hp : p ∈ indecomposableAvoiders n) (hm : p.getD 0 0 = 4) (hiw : p.idxOf 5 = 2) : p = familyA n ∨ p = familyB n := by
  have hpre := prop64_prefix_and_sq hn hp hm; have h62 := lemma62_second_and_tail n (by omega) p hp hm; have ⟨_, ⟨hperm, hav312, _, _⟩, _⟩ := hp; have hlen : p.length = n := (by simpa using hperm.length_eq); have hsq := square_perm_and_getD hperm; have hp2 : p.getD 2 0 = 5 := (by rw [← hiw]; exact (perm_idxOf_spec hperm 5 (by omega) (by omega)).2); have hq1 : (square p).getD 1 0 = 5 := (by rw [hsq.2 1 (by omega), hpre.1]; exact hp2)
  have hix5 : (square p).idxOf 5 = 1 := (by rw [← hq1]; exact perm_idxOf_getD hsq.1 (by omega)); have hq0_eq : (square p).getD 0 0 = p.getD 3 0 := (by rw [hsq.2 0 (by omega), hm]); have hh_bnd : 6 ≤ p.getD 3 0 ∧ p.getD 3 0 ≤ n := (by have hb := hpre.2.2.2.2.2.2.1 0 (by omega); have := ne_val_of_getD hsq.1 (by omega) (by omega) (by omega : 0 ≠ 1) hq1; omega)
  by_cases hh6 : p.getD 3 0 = 6
  · left
    have hq_eq : ∀ i, 2 ≤ i → i < n - 4 → (square p).getD i 0 = i + 5 := fun i hi1 hi2 => by
      have h := strictMono_Ico_eq (a := 2) (b := n - 4) (v₀ := 7) (f := fun k => (square p).getD k 0)
        (fun k hk1 hk2 => by
          have hb := hpre.2.2.2.2.2.2.1 k hk2; have := ne_val_of_getD hsq.1 (by omega) (by omega) (by omega : k ≠ 0) (hq0_eq.trans hh6)
          have := ne_val_of_getD hsq.1 (by omega) (by omega) (by omega : k ≠ 1) hq1; omega)
        (fun i j hi1 hij hj2 => hpre.2.2.2.2.2.2.2.2.2 i j (by omega) hij hj2) i hi1 hi2
      omega
    have hrun : ∀ d, 2 + d ≤ n - 3 → p.getD (2 + d) 0 = d + 5 := fun d hd => by
      induction d using Nat.twoStepInduction with
      | zero => exact hp2
      | one => exact hh6
      | more d ih0 _ =>
        have hp_d := ih0 (by omega); have hq_d := hq_eq (2 + d) (by omega) (by omega); have hs := hsq.2 (2 + d) (by omega); rw [hq_d, hp_d, show d + 5 - 1 = 2 + (d + 2) by omega] at hs; omega
    have hp_n3 : p.getD (n - 3) 0 = n := (by have := hrun (n - 5) (by omega); rw [show 2 + (n - 5) = n - 3 by omega] at this; omega); have hp_n2 : p.getD (n - 2) 0 = 2 := (by rcases h62.2 with h | h | h <;> (injection h with h1 h'; injection h' with h2 h3; try omega))
    have hA := familyA_len_getD n (by omega); refine list_eq_of_getD hlen hA.1 fun i hi => ?_
    rw [hA.2 i hi]
    by_cases h01 : i < 2
    · rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> [exact hm; exact hpre.1]
    by_cases hmid : i < n - 2
    · have := hrun (i - 2) (by omega); rw [show 2 + (i - 2) = i by omega] at this; repeat' (split <;> try omega)
    · have hend := hpre.2.1; rcases (by omega : i = n - 2 ∨ i = n - 1) with rfl | rfl <;> repeat' (split <;> try omega)
  · right
    have hsq6 := perm_idxOf_spec hsq.1 6 (by omega) (by omega)
    have hsq6_lt : (square p).idxOf 6 < n - 4 := by
      by_contra hge; have h61 := lemma61_tail n (by omega) p hp hm; have hqlen : (square p).length = n := (by simpa using hsq.1.length_eq); have hk : (square p).idxOf 6 - (n - 4) < ((square p).drop (n - 4)).length := (by simp [hqlen]; omega); have hmem := h61.1.mem_iff.mp (List.getElem_mem hk)
      rw [List.getElem_drop, ← List.getD_eq_getElem (square p) 0 (by rw [hqlen]; omega),
        show n - 4 + ((square p).idxOf 6 - (n - 4)) = (square p).idxOf 6 by omega, hsq6.2] at hmem
      simp at hmem
    have hsq6_ge2 : 2 ≤ (square p).idxOf 6 := (by have := idxOf_ne_of_getD hsq.1 6 0 (by omega) (by omega) (by omega); have := idxOf_ne_of_getD hsq.1 6 1 (by omega) (by omega) (by omega); omega)
    have hq2 : (square p).getD 2 0 = 6 := by
      by_cases he : (square p).idxOf 6 = 2
      · rw [← he]; exact hsq6.2
      · have hlt := hpre.2.2.2.2.2.2.2.2.2 2 ((square p).idxOf 6) (by omega) (by omega) hsq6_lt; have hb2 := hpre.2.2.2.2.2.2.1 2 (by omega); have := ne_val_of_getD hsq.1 (by omega) (by omega) (by omega : 2 ≠ 1) hq1; omega
    have hp4 : p.getD 4 0 = 6 := (by have hs := hsq.2 2 (by omega); rw [hq2, hp2] at hs; exact hs.symm)
    have hp3 : p.getD 3 0 = 7 := by
      by_contra hne7; have hs7 := perm_idxOf_spec hperm 7 (by omega) (by omega); have := idxOf_ne_of_getD hperm 7 0 (by omega) (by omega) (by omega); have := idxOf_ne_of_getD hperm 7 1 (by omega) (by omega) (by omega); have := idxOf_ne_of_getD hperm 7 2 (by omega) (by omega) (by omega); have := idxOf_ne_of_getD hperm 7 3 (by omega) (by omega) (by omega); have := idxOf_ne_of_getD hperm 7 4 (by omega) (by omega) (by omega)
      exact hav312 (occurs_312_of_indices (i := 3) (j := 4) (k := p.idxOf 7) (by omega) (by omega) (by rw [hlen]; omega) (by omega) (by omega))
    have hq_eq : ∀ i, 3 ≤ i → i < n - 4 → (square p).getD i 0 = i + 5 := fun i hi1 hi2 => by
      have h := strictMono_Ico_eq (a := 3) (b := n - 4) (v₀ := 8) (f := fun k => (square p).getD k 0)
        (fun k hk1 hk2 => by
          have hb := hpre.2.2.2.2.2.2.1 k hk2; have := ne_val_of_getD hsq.1 (by omega) (by omega) (by omega : k ≠ 0) (hq0_eq.trans hp3); have := ne_val_of_getD hsq.1 (by omega) (by omega) (by omega : k ≠ 1) hq1
          have := ne_val_of_getD hsq.1 (by omega) (by omega) (by omega : k ≠ 2) hq2; omega)
        (fun i j hi1 hij hj2 => hpre.2.2.2.2.2.2.2.2.2 i j (by omega) hij hj2) i hi1 hi2
      omega
    have hpair : ∀ r, 2 * r + 4 ≤ n - 3 → p.getD (2 * r + 3) 0 = 2 * r + 7 ∧ p.getD (2 * r + 4) 0 = 2 * r + 6 := by
      intro r hr; induction r with
      | zero => exact ⟨hp3, hp4⟩
      | succ r ih =>
        obtain ⟨h1, h2⟩ := ih (by omega); have qa := hq_eq (2 * r + 3) (by omega) (by omega); have qb := hq_eq (2 * r + 4) (by omega) (by omega); have sa := hsq.2 (2 * r + 3) (by omega); rw [qa, h1, show 2 * r + 7 - 1 = 2 * (r + 1) + 4 by omega] at sa; have sb := hsq.2 (2 * r + 4) (by omega); rw [qb, h2, show 2 * r + 6 - 1 = 2 * (r + 1) + 3 by omega] at sb; exact ⟨sb.symm, sa.symm⟩
    have hB := familyB_len_getD n (by omega); refine list_eq_of_getD hlen hB.1 fun i hi => ?_
    rw [hB.2 i hi]
    by_cases hp_od : n % 2 = 1
    · have hend_pair := hpair ((n - 7) / 2) (by omega)
      rw [show 2 * ((n - 7) / 2) + 3 = n - 4 by omega, show 2 * ((n - 7) / 2) + 7 = n by omega] at hend_pair; have hp_n2 : p.getD (n - 2) 0 = 2 := (by rcases h62.2 with h | h | h <;> (injection h with h1 h'; injection h' with h2 h3; try omega))
      by_cases h02 : i < 3
      · rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;> [exact hm; exact hpre.1; exact hp2]
      by_cases hm_i : i < n - 2
      · by_cases hi_od : i % 2 = 1
        · have := (hpair ((i - 3) / 2) (by omega)).1; rw [show 2 * ((i - 3) / 2) + 3 = i by omega] at this; simp only [hp_od, hi_od, ↓reduceIte]; repeat' (split <;> try omega)
        · have := (hpair ((i - 4) / 2) (by omega)).2; rw [show 2 * ((i - 4) / 2) + 4 = i by omega] at this; simp only [hp_od, hi_od, ↓reduceIte]; repeat' (split <;> try omega)
      · have hend := hpre.2.1
        rcases (by omega : i = n - 2 ∨ i = n - 1) with rfl | rfl <;>
          (simp only [hp_od, ↓reduceIte]; repeat' (split <;> try omega))
    · have hend_pair := hpair ((n - 8) / 2) (by omega)
      rw [show 2 * ((n - 8) / 2) + 4 = n - 4 by omega, show 2 * ((n - 8) / 2) + 6 = n - 2 by omega] at hend_pair; have htail : p.getD (n - 3) 0 = 2 ∧ p.getD (n - 2) 0 = n := (by rcases h62.2 with h | h | h <;> (injection h with h1 h'; injection h' with h2 h3; try omega))
      by_cases h02 : i < 3
      · rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;> [exact hm; exact hpre.1; exact hp2]
      by_cases hm_i : i < n - 3
      · by_cases hi_od : i % 2 = 1
        · have := (hpair ((i - 3) / 2) (by omega)).1; rw [show 2 * ((i - 3) / 2) + 3 = i by omega] at this; simp only [hp_od, hi_od, ↓reduceIte]; repeat' (split <;> try omega)
        · have := (hpair ((i - 4) / 2) (by omega)).2; rw [show 2 * ((i - 4) / 2) + 4 = i by omega] at this; simp only [hp_od, hi_od, ↓reduceIte]; repeat' (split <;> try omega)
      · have hend := hpre.2.1
        rcases (by omega : i = n - 3 ∨ i = n - 2 ∨ i = n - 1) with rfl | rfl | rfl <;>
          (simp only [hp_od, ↓reduceIte]; repeat' (split <;> try omega))
private theorem prop64_w5 {n : ℕ} (hn : 8 ≤ n) {p : List ℕ} (hp : p ∈ indecomposableAvoiders n) (hm : p.getD 0 0 = 4) (hiw : p.idxOf 5 = 4) : 9 ≤ n ∧ p = familyD n := by
  have hpre := prop64_prefix_and_sq hn hp hm; have h62 := lemma62_second_and_tail n (by omega) p hp hm; rcases hp with ⟨_, ⟨hperm, _, _, hav132⟩, _⟩; have hlen : p.length = n := (by simpa using hperm.length_eq); have hsq := square_perm_and_getD hperm; have hqlen : (square p).length = n := (by simpa using hsq.1.length_eq); have hn9 : 9 ≤ n := (by omega)
  have hp2 : p.getD 2 0 = 6 := (by have := hpre.2.2.2.2.2.1 2 le_rfl (by omega); omega); have hp3 : p.getD 3 0 = 7 := (by have := hpre.2.2.2.2.2.1 3 (by omega) (by omega); omega); have hp4 : p.getD 4 0 = 5 := (by rw [← hiw]; exact (perm_idxOf_spec hperm 5 (by omega) (by omega)).2); have hq0 : (square p).getD 0 0 = 7 := (by rw [hsq.2 0 (by omega), hm]; exact hp3)
  have hq1 : (square p).getD 1 0 = 6 := (by rw [hsq.2 1 (by omega), hpre.1]; exact hp2); have hq4 : (square p).getD 4 0 = 5 := (by rw [hsq.2 4 (by omega), hp4]; exact hp4); have hskip := strictMono_skip1_eq (a := 2) (b := n - 4) (x := 4) (v₀ := 8)
    (f := fun k => (square p).getD k 0) ⟨by omega, by omega⟩
    (fun k hk1 hk2 hne4 => by
      have hb := hpre.2.2.2.2.2.2.1 k hk2; have := ne_val_of_getD hsq.1 (by omega) (by omega) (by omega : k ≠ 0) hq0; have := ne_val_of_getD hsq.1 (by omega) (by omega) (by omega : k ≠ 1) hq1
      have := ne_val_of_getD hsq.1 (by omega) (by omega) hne4 hq4; omega)
    (fun i j hi1 hij hj2 hni hnj => by
      have hne := ne_val_of_getD hsq.1 (by omega) (by omega) (by omega : i ≠ j) rfl; have bi := hpre.2.2.2.2.2.2.1 i (by omega); have bj := hpre.2.2.2.2.2.2.1 j hj2; have := ne_val_of_getD hsq.1 (by omega) (by omega) (by omega : i ≠ 0) hq0; have := ne_val_of_getD hsq.1 (by omega) (by omega) (by omega : i ≠ 1) hq1; have := ne_val_of_getD hsq.1 (by omega) (by omega) hni hq4
      have := ne_val_of_getD hsq.1 (by omega) (by omega) (by omega : j ≠ 0) hq0; have := ne_val_of_getD hsq.1 (by omega) (by omega) (by omega : j ≠ 1) hq1; have := ne_val_of_getD hsq.1 (by omega) (by omega) hnj hq4; by_contra hnot
      exact hav132 (occurs_132_of_indices (i := 1) (j := i) (k := j) (by omega) hij (by rw [hqlen]; omega) (by omega) (by omega)))
  have hp5 : p.getD 5 0 = 8 := (by have hs := hsq.2 2 (by omega); rw [hskip.1 2 le_rfl (by omega), hp2] at hs; exact hs.symm); have hp6 : p.getD 6 0 = 9 := (by have hs := hsq.2 3 (by omega); rw [hskip.1 3 (by omega) (by omega), hp3] at hs; exact hs.symm)
  have hrun : ∀ d, 5 + d ≤ n - 3 → p.getD (5 + d) 0 = d + 8 := fun d hd => by
    induction d using Nat.twoStepInduction with
    | zero => exact hp5
    | one => exact hp6
    | more d ih0 _ =>
      have hp_d := ih0 (by omega); have hq_d := hskip.2 (5 + d) (by omega) (by omega); have hs := hsq.2 (5 + d) (by omega); rw [hq_d, hp_d, show d + 8 - 1 = 5 + (d + 2) by omega] at hs; omega
  have hp_n3 : p.getD (n - 3) 0 = n := (by have := hrun (n - 8) (by omega); rw [show 5 + (n - 8) = n - 3 by omega] at this; omega); have hp_n2 : p.getD (n - 2) 0 = 2 := (by rcases h62.2 with h | h | h <;> (injection h with h1 h'; injection h' with h2 h3; try omega))
  have hD := familyD_len_getD n hn9; refine ⟨hn9, list_eq_of_getD hlen hD.1 fun i hi => ?_⟩
  rw [hD.2 i hi]
  by_cases h5 : i < 5
  · rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl | rfl <;>
      [exact hm; exact hpre.1; exact hp2; exact hp3; exact hp4]
  by_cases hmid : i < n - 2
  · have := hrun (i - 5) (by omega); rw [show 5 + (i - 5) = i by omega] at this; repeat' (split <;> try omega)
  · have hend := hpre.2.1; rcases (by omega : i = n - 2 ∨ i = n - 1) with rfl | rfl <;> repeat' (split <;> try omega)
private theorem prop64_ge6 {n : ℕ} (hn : 8 ≤ n) {p : List ℕ} (hp : p ∈ indecomposableAvoiders n) (hm : p.getD 0 0 = 4) (hiw : 5 ≤ p.idxOf 5) : False := by
  have hpre := prop64_prefix_and_sq hn hp hm; have h62 := lemma62_second_and_tail n (by omega) p hp hm; rcases hp with ⟨_, ⟨hperm, _, _, hav132⟩, _⟩; have hlen : p.length = n := (by simpa using hperm.length_eq); have hsq := square_perm_and_getD hperm; have hqlen : (square p).length = n := (by simpa using hsq.1.length_eq); let iw := p.idxOf 5; have hp2 : p.getD 2 0 = 6 := (by have := hpre.2.2.2.2.2.1 2 le_rfl (by omega); omega)
  have hp3 : p.getD 3 0 = 7 := (by have := hpre.2.2.2.2.2.1 3 (by omega) (by omega); omega); have hp4 : p.getD 4 0 = 8 := (by have := hpre.2.2.2.2.2.1 4 (by omega) (by omega); omega); have hpiw : p.getD iw 0 = 5 := (perm_idxOf_spec hperm 5 (by omega) (by omega)).2; have hq1 : (square p).getD 1 0 = 6 := (by rw [hsq.2 1 (by omega), hpre.1]; exact hp2); have hqiw : (square p).getD iw 0 = 8 := (by rw [hsq.2 iw (by omega), hpiw]; exact hp4)
  by_cases hiw6 : 6 ≤ iw
  · have hp5 : p.getD 5 0 = 9 := by have := hpre.2.2.2.2.2.1 5 (by omega) (by omega); omega
    have hq2 : (square p).getD 2 0 = 9 := (by rw [hsq.2 2 (by omega), hp2]; exact hp5); exact hav132 (occurs_132_of_indices (i := 1) (j := 2) (k := iw) (by omega) (by omega) (by omega) (by omega) (by omega))
  · have hiw5 : iw = 5 := by omega
    have hn10 : 10 ≤ n := (by omega)
    obtain ⟨i2, hi2_ge, hi2_lt, hi2_val⟩ : ∃ i2, n - 3 ≤ i2 ∧ i2 < n - 1 ∧ p.getD i2 0 = 2 := by
      rcases h62.2 with h | h | h
      · exact ⟨n - 2, by omega, by omega, by injection h with _ h'; injection h'⟩
      · exact ⟨n - 2, by omega, by omega, by injection h with _ h'; injection h'⟩
      · exact ⟨n - 3, le_rfl, by omega, by injection h with _ h'; injection h'⟩
    have hp6_ge9 : 9 ≤ p.getD 6 0 := by
      have hb := perm_getD_bounds hperm (by omega : 6 < n); have := ne_val_of_getD hperm (by omega) (by omega) (by omega : 6 ≠ n - 1) hpre.2.1; have := ne_val_of_getD hperm (by omega) (by omega) (by omega : 6 ≠ i2) hi2_val; have := ne_val_of_getD hperm (by omega) (by omega) (by omega : 6 ≠ 1) hpre.1; have := ne_val_of_getD hperm (by omega) (by omega) (by omega : 6 ≠ 0) hm
      have := ne_val_of_getD hperm (by omega) (by omega) (by omega : 6 ≠ iw) hpiw; have := ne_val_of_getD hperm (by omega) (by omega) (by omega : 6 ≠ 2) hp2; have := ne_val_of_getD hperm (by omega) (by omega) (by omega : 6 ≠ 3) hp3; have := ne_val_of_getD hperm (by omega) (by omega) (by omega : 6 ≠ 4) hp4; omega
    have hq3 : (square p).getD 3 0 = p.getD 6 0 := (by rw [hsq.2 3 (by omega), hp3]); exact hav132 (occurs_132_of_indices (i := 1) (j := 3) (k := iw) (by omega) (by omega) (by omega) (by omega) (by omega))
private theorem prop65_small {n : ℕ} (hn4 : 4 ≤ n) (hn7 : n ≤ 7) {p : List ℕ} (hp : p ∈ indecomposableAvoiders n) (hm : p.getD 0 0 = 4) : p = familyC n ∨ (6 ≤ n ∧ p = familyA n) ∨ (7 ≤ n ∧ p = familyB n) := by
  have hsh := indecomposable_shape_and_prefix_iff.2.2.2.2 n (by omega) p hp; dsimp only at hsh; have hend : p.getD (n - 1) 0 = 1 := hsh.1.1; have hperm := hp.2.1.1; have hlen : p.length = n := (by simpa using hperm.length_eq); rcases (by omega : n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7) with rfl | rfl | rfl | rfl
  · left; simp only [Nat.reduceSub] at hend
    have hord := hsh.2.1.2.2 2 3 le_rfl (by omega) (by omega); have hs3 := perm_idxOf_spec hperm 3 (by omega) (by omega); have hs2 := perm_idxOf_spec hperm 2 (by omega) (by omega); have := idxOf_ne_of_getD hperm 2 3 (by omega) (by omega) (by omega); have hi3 : p.idxOf 3 = 1 := (by omega); have hi2 : p.idxOf 2 = 2 := (by omega); have hp1 : p.getD 1 0 = 3 := (by rw [← hi3]; exact hs3.2)
    have hp2 : p.getD 2 0 = 2 := (by simpa [hi2] using hs2.2); refine list_eq_of_getD hlen (by rfl) fun i hi => ?_
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;>
      [exact hm; exact hp1; exact hp2; exact hend]
  · left; simp only [Nat.reduceSub] at hend
    have h62 := lemma62_second_and_tail 5 le_rfl p hp hm; simp only [Nat.reduceSub] at h62; rcases h62.2 with h | h | h <;> (injection h with h1 h'; injection h' with h2 h3; try omega)
    refine list_eq_of_getD hlen (by rfl) fun i hi => ?_
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl | rfl <;>
      [exact hm; exact h1; exact h2; exact h3; exact hend]
  · simp only [Nat.reduceSub] at hend
    have h62 := lemma62_second_and_tail 6 (by omega) p hp hm; simp only [Nat.reduceSub] at h62; rcases h62.2 with h | h | h
    · left; injection h with h2 h'; injection h' with h3 h4
      refine list_eq_of_getD hlen (by rfl) fun i hi => ?_
      rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with rfl | rfl | rfl | rfl | rfl | rfl <;>
        [exact hm; exact h62.1; exact h2; exact h3; exact h4; exact hend]
    · right; left; refine ⟨le_rfl, ?_⟩
      injection h with h2 h'; injection h' with h3 h4; refine list_eq_of_getD hlen (by rfl) fun i hi => ?_
      rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with rfl | rfl | rfl | rfl | rfl | rfl <;>
        [exact hm; exact h62.1; exact h2; exact h3; exact h4; exact hend]
    · injection h with h2 _; have := perm_getD_inj hperm (by omega : 2 < 6) (by omega : 0 < 6) (h2.trans hm.symm); omega
  · simp only [Nat.reduceSub] at hend
    have h62 := lemma62_second_and_tail 7 (by omega) p hp hm; simp only [Nat.reduceSub] at h62; have h63 := lemma63_middle 7 le_rfl p hp hm; dsimp only at h63; simp only [Nat.reduceSub] at h63; have hm2 : p.getD 2 0 ∈ (p.drop 2).take 1 := (mid_mem_iff hlen le_rfl _).mpr ⟨2, le_rfl, by omega, rfl⟩; rcases h62.2 with h | h | h
    · right; right; refine ⟨le_rfl, ?_⟩
      have hv := h63.2.2.1 (Or.inl h); change p.getD 2 0 ∈ {v | v ∈ (p.drop 2).take 1} at hm2; rw [hv] at hm2; change 5 ≤ p.getD 2 0 ∧ p.getD 2 0 ≤ 7 - 2 at hm2; have hp2 : p.getD 2 0 = 5 := (by omega); injection h with h3 h'; injection h' with h4 h5; refine list_eq_of_getD hlen (by rfl) fun i hi => ?_
      rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        [exact hm; exact h62.1; exact hp2; exact h3; exact h4; exact h5; exact hend]
    · right; left; refine ⟨by omega, ?_⟩
      have hv := h63.2.2.1 (Or.inr h); change p.getD 2 0 ∈ {v | v ∈ (p.drop 2).take 1} at hm2; rw [hv] at hm2; change 5 ≤ p.getD 2 0 ∧ p.getD 2 0 ≤ 7 - 2 at hm2; have hp2 : p.getD 2 0 = 5 := (by omega); injection h with h3 h'; injection h' with h4 h5; refine list_eq_of_getD hlen (by rfl) fun i hi => ?_
      rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        [exact hm; exact h62.1; exact hp2; exact h3; exact h4; exact h5; exact hend]
    · left; have hp2 : p.getD 2 0 = 6 := (h63.2.2.2 h).2
      injection h with h3 h'; injection h' with h4 h5; refine list_eq_of_getD hlen (by rfl) fun i hi => ?_
      rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        [exact hm; exact h62.1; exact hp2; exact h3; exact h4; exact h5; exact hend]
section FirstEntryFourClass
attribute [local instance 2000] Classical.propDecidable
/-- Complete classification and exact count of indecomposable square-avoiders with first entry four
    for every `n ≥ 4`. -/
theorem first_entry_four_classification :
    ∀ n : ℕ, 4 ≤ n →
      (∀ p : List ℕ, (p ∈ indecomposableAvoiders n ∧ p.getD 0 0 = 4) ↔
        (p = familyC n ∨ (6 ≤ n ∧ p = familyA n) ∨
          (7 ≤ n ∧ p = familyB n) ∨ (9 ≤ n ∧ p = familyD n))) ∧
      {p ∈ indecomposableAvoiders n | p.getD 0 0 = 4}.ncard =
        (if n ≤ 5 then 1 else if n = 6 then 2 else if n ≤ 8 then 3 else 4) := by
  classical
  intro n hn
  have hdist := seven_families_admissible_and_distinct
  have hiff : ∀ p : List ℕ, (p ∈ indecomposableAvoiders n ∧ p.getD 0 0 = 4) ↔
      (p = familyC n ∨ (6 ≤ n ∧ p = familyA n) ∨ (7 ≤ n ∧ p = familyB n) ∨ (9 ≤ n ∧ p = familyD n)) := by
    intro p; constructor
    · rintro ⟨hp, hm⟩
      by_cases h7 : n ≤ 7
      · rcases prop65_small hn h7 hp hm with h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inl h))
      · have hn8 : 8 ≤ n := by omega
        have hpre := prop64_prefix_and_sq hn8 hp hm; rcases (by omega : p.idxOf 5 = 2 ∨ p.idxOf 5 = 3 ∨ p.idxOf 5 = 4 ∨ 5 ≤ p.idxOf 5) with h2 | h3 | h4 | h5
        · rcases prop64_w3 hn8 hp hm h2 with rfl | rfl
          · exact Or.inr (Or.inl ⟨by omega, rfl⟩)
          · exact Or.inr (Or.inr (Or.inl ⟨by omega, rfl⟩))
        · exact Or.inl (prop64_w4 hn8 hp hm h3)
        · exact Or.inr (Or.inr (Or.inr (prop64_w5 hn8 hp hm h4)))
        · exact False.elim (prop64_ge6 hn8 hp hm h5)
    · rintro (rfl | ⟨h6, rfl⟩ | ⟨h7, rfl⟩ | ⟨h9, rfl⟩)
      · exact ⟨hdist.2.2.2.2.2.1 n hn, rfl⟩
      · exact ⟨hdist.2.2.2.1 n h6, rfl⟩
      · exact ⟨hdist.2.2.2.2.1 n h7, rfl⟩
      · exact ⟨hdist.2.2.2.2.2.2.1 n h9, rfl⟩
  refine ⟨hiff, ?_⟩; have h4 := hdist.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2; have hAB : 7 ≤ n → familyA n ≠ familyB n := h4.1 n; have hAC : 6 ≤ n → familyA n ≠ familyC n := h4.2.1 n; have hAD : 9 ≤ n → familyA n ≠ familyD n := h4.2.2.1 n; have hBC : 7 ≤ n → familyB n ≠ familyC n := h4.2.2.2.1 n; have hBD : 9 ≤ n → familyB n ≠ familyD n := h4.2.2.2.2.1 n; have hCD : 9 ≤ n → familyC n ≠ familyD n := h4.2.2.2.2.2 n
  by_cases hle5 : n ≤ 5
  · simp only [hle5, ↓reduceIte]
    have hset : {p ∈ indecomposableAvoiders n | p.getD 0 0 = 4} = {familyC n} := by
      ext p; change (p ∈ indecomposableAvoiders n ∧ p.getD 0 0 = 4) ↔ p = familyC n; rw [hiff]; constructor
      · rintro (h | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩) <;> [exact h; omega; omega; omega]
      · exact Or.inl
    rw [hset, Set.ncard_singleton]
  by_cases heq6 : n = 6
  · subst n; simp only [show ¬ (6 : ℕ) ≤ 5 by omega, ↓reduceIte]; let F : Finset (List ℕ) := insert (familyC 6) {familyA 6}; have hset : {p ∈ indecomposableAvoiders 6 | p.getD 0 0 = 4} = (F : Set (List ℕ)) := (by ext p; change (p ∈ indecomposableAvoiders 6 ∧ p.getD 0 0 = 4) ↔ p ∈ (F : Set (List ℕ)); rw [hiff]; simp [F]); rw [hset, Set.ncard_coe_finset, Finset.card_insert_of_notMem (by simp [(hAC le_rfl).symm])]; rfl
  by_cases hle8 : n ≤ 8
  · have hn7 : 7 ≤ n := by omega
    simp only [hle5, heq6, hle8, ↓reduceIte]; let F : Finset (List ℕ) := insert (familyC n) (insert (familyA n) {familyB n})
    have hset : {p ∈ indecomposableAvoiders n | p.getD 0 0 = 4} = (F : Set (List ℕ)) := by
      ext p; change (p ∈ indecomposableAvoiders n ∧ p.getD 0 0 = 4) ↔ p ∈ (F : Set (List ℕ)); rw [hiff]; simp only [F, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff]; constructor
      · rintro (h | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, _⟩)
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
        · omega
      · rintro (h | h | h)
        · exact Or.inl h
        · exact Or.inr (Or.inl ⟨by omega, h⟩)
        · exact Or.inr (Or.inr (Or.inl ⟨hn7, h⟩))
    rw [hset, Set.ncard_coe_finset, Finset.card_insert_of_notMem (by simp [(hAC (by omega)).symm, (hBC hn7).symm]),
      Finset.card_insert_of_notMem (by simp [hAB hn7])]; rfl
  · have hn9 : 9 ≤ n := by omega
    simp only [hle5, heq6, hle8, ↓reduceIte]; let F : Finset (List ℕ) := insert (familyC n) (insert (familyA n) (insert (familyB n) {familyD n}))
    have hset : {p ∈ indecomposableAvoiders n | p.getD 0 0 = 4} = (F : Set (List ℕ)) := by
      ext p; change (p ∈ indecomposableAvoiders n ∧ p.getD 0 0 = 4) ↔ p ∈ (F : Set (List ℕ)); rw [hiff]; simp only [F, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff]; constructor
      · rintro (h | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩)
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inr (Or.inr (Or.inr h))
      · rintro (h | h | h | h)
        · exact Or.inl h
        · exact Or.inr (Or.inl ⟨by omega, h⟩)
        · exact Or.inr (Or.inr (Or.inl ⟨by omega, h⟩))
        · exact Or.inr (Or.inr (Or.inr ⟨hn9, h⟩))
    rw [hset, Set.ncard_coe_finset,
      Finset.card_insert_of_notMem (by simp [(hAC (by omega)).symm, (hBC (by omega)).symm, hCD hn9]),
      Finset.card_insert_of_notMem (by simp [hAB (by omega), hAD hn9]),
      Finset.card_insert_of_notMem (by simp [hBD hn9])]; rfl
end FirstEntryFourClass
/-- Complete classification of nonempty sum-indecomposable square-avoiders for `n ≥ 9` into the
    seven explicit families. -/
theorem indecomposable_classification_ge_nine :
    ∀ n : ℕ, 9 ≤ n → ∀ p : List ℕ,
      p ∈ indecomposableAvoiders n ↔
        (p = familyI n ∨ p = familyJ n ∨ (∃ j ≤ (n - 6) / 2, p = familyK n j) ∨
          p = familyA n ∨ p = familyD n ∨ p = familyB n ∨ p = familyC n) := by
  intro n hn p
  have hdist := seven_families_admissible_and_distinct
  constructor
  · intro hp
    have hsh := indecomposable_shape_and_prefix_iff.2.2.2.2 n (by omega) p hp
    have hbnd : 2 ≤ p.getD 0 0 ∧ p.getD 0 0 ≤ 4 := ⟨hsh.2.1.1, hsh.2.1.2.1⟩
    rcases (by omega : p.getD 0 0 = 2 ∨ p.getD 0 0 = 3 ∨ p.getD 0 0 = 4) with h2 | h3 | h4
    · rcases (first_entry_two_and_three_classification.1 n (by omega)).1 p |>.mp ⟨hp, h2⟩ with
        h | ⟨_, h⟩ | ⟨_, h⟩
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
    · exact False.elim (first_entry_two_and_three_classification.2 n (by omega) p hp h3)
    · rcases (first_entry_four_classification n (by omega)).1 p |>.mp ⟨hp, h4⟩ with
        h | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · rintro (rfl | rfl | ⟨j, hj, rfl⟩ | rfl | rfl | rfl | rfl)
    · exact hdist.1 n (by omega)
    · exact hdist.2.1 n (by omega)
    · exact hdist.2.2.1 n j (by omega) hj
    · exact hdist.2.2.2.1 n (by omega)
    · exact hdist.2.2.2.2.2.2.1 n hn
    · exact hdist.2.2.2.2.1 n (by omega)
    · exact hdist.2.2.2.2.2.1 n (by omega)
end D5.S3.Combinatorics.PermutationSquare.PermutationSquareClassification
