/- GID: D5/S3/Combinatorics/PermutationSquare/PermutationSquareFamilies
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PermutationSquare/PermutationSquareFamilies
   mirror-E: none(waiver:indecomposable-square-avoider-families-and-first-entry-two-three)
   anchors: []
   utility: none
   digest: Seven explicit families, shape bounds, and first-entry two and three classifications. -/

import D5.S3.Combinatorics.PermutationSquare.PermutationSquareCounting
/-! Seven explicit families of sum-indecomposable square-avoiders, shape bounds, and complete
    classifications for first entry two and first entry three. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.PermutationSquare.PermutationSquareFamilies
open D5.S3.Combinatorics Nonnesting NonnestingBasicSum
open PermutationSquareDefs PermutationSquareStructure
/-- Nonempty sum-indecomposable permutations of `[n]` avoiding `312` and `54321` whose square avoids `132`. -/
def indecomposableAvoiders (n : ℕ) : Set (List ℕ) := {p | p ≠ [] ∧ p ∈ avoiders n ∧ sumIndecomposable p}
/-- Number `b_n` of nonempty sum-indecomposable square-avoiders of length `n`. -/
noncomputable def b (n : ℕ) : ℕ := (indecomposableAvoiders n).ncard
/-- Family `I_n = 2 3 ⋯ n 1` for `n ≥ 2`. -/
def familyI (n : ℕ) : List ℕ := List.range' 2 (n - 1) ++ [1]
/-- Family `J_n = 2 4 3 5 6 ⋯ n 1` for `n ≥ 5`. -/
def familyJ (n : ℕ) : List ℕ := [2, 4, 3] ++ List.range' 5 (n - 4) ++ [1]
/-- Family `K_{n,j} = 2 5 4 (7 6) ⋯ (2j+5, 2j+4) 3 (2j+6) ⋯ n 1` for `n ≥ 6`, `0 ≤ j ≤ (n - 6) / 2`. -/
def familyK (n j : ℕ) : List ℕ := [2] ++ ((List.range (j + 1)).flatMap fun r => [2 * r + 5, 2 * r + 4]) ++ [3] ++ List.range' (2 * j + 6) (n - (2 * j + 5)) ++ [1]
/-- Family `A_n = 4 3 5 6 ⋯ n 2 1` for `n ≥ 6`. -/
def familyA (n : ℕ) : List ℕ := [4, 3] ++ List.range' 5 (n - 4) ++ [2, 1]
/-- Family `B_n` for `n ≥ 7`, ending in `2 1` for odd `n` and `2 n 1` for even `n`. -/
def familyB (n : ℕ) : List ℕ := [4, 3, 5] ++ ((List.range ((n - 5) / 2)).flatMap fun r => [2 * r + 7, 2 * r + 6]) ++ (if n % 2 = 1 then [2, 1] else [2, n, 1])
/-- Family `C_n` for `n ≥ 4`, ending in `2 1` for even `n` and `2 n 1` for odd `n`. -/
def familyC (n : ℕ) : List ℕ := [4, 3] ++ ((List.range ((n - 4) / 2)).flatMap fun r => [2 * r + 6, 2 * r + 5]) ++ (if n % 2 = 0 then [2, 1] else [2, n, 1])
/-- Family `D_n = 4 3 6 7 5 8 9 ⋯ n 2 1` for `n ≥ 9`. -/
def familyD (n : ℕ) : List ℕ := [4, 3, 6, 7, 5] ++ List.range' 8 (n - 7) ++ [2, 1]
private theorem sublist_map_getD_drop (p : List ℕ) : ∀ (is : List ℕ) (c : ℕ), is.Pairwise (· < ·) → (∀ i ∈ is, c ≤ i ∧ i < p.length) → (is.map fun i => p.getD i 0).Sublist (p.drop c)
  | [], _, _, _ => List.nil_sublist _
  | i :: rest, c, hpw, hb => by
    have hic := hb i (by simp); have hrest := sublist_map_getD_drop p rest (i + 1) (List.pairwise_cons.mp hpw).2 fun k hk => ⟨(List.pairwise_cons.mp hpw).1 k hk, (hb k (List.mem_cons_of_mem i hk)).2⟩
    have hcons : ((i :: rest).map fun k => p.getD k 0).Sublist (p.drop i) := (by rw [List.map_cons, List.getD_eq_getElem p 0 hic.2, List.drop_eq_getElem_cons hic.2]; exact List.Sublist.cons_cons _ hrest)
    have hdrop : p.drop i = (p.drop c).drop (i - c) := (by rw [List.drop_drop, Nat.add_sub_of_le hic.1]); rw [hdrop] at hcons; exact hcons.trans (List.drop_sublist _ _)
private theorem occurs_312_iff (p : List ℕ) : NonnestingDefs.Occurs [3, 1, 2] p ↔ ∃ i j k : ℕ, i < j ∧ j < k ∧ k < p.length ∧ p.getD j 0 < p.getD k 0 ∧ p.getD k 0 < p.getD i 0 := by
  constructor
  · rintro ⟨x, hmono, _, hsub, _⟩; change [x 3, x 1, x 2].Sublist p at hsub; obtain ⟨emb, hemb⟩ := List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp hsub; let i0 := emb ⟨0, by simp⟩; let i1 := emb ⟨1, by simp⟩; let i2 := emb ⟨2, by simp⟩
    have he0 : p.getD i0.val 0 = x 3 := (by rw [List.getD_eq_getElem p 0 i0.isLt]; exact (hemb ⟨0, by simp⟩).symm); have he1 : p.getD i1.val 0 = x 1 := (by rw [List.getD_eq_getElem p 0 i1.isLt]; exact (hemb ⟨1, by simp⟩).symm)
    have he2 : p.getD i2.val 0 = x 2 := (by rw [List.getD_eq_getElem p 0 i2.isLt]; exact (hemb ⟨2, by simp⟩).symm); have hx12 : x 1 < x 2 := hmono 1 (by omega) (by change 1 < 3; omega); have hx23 : x 2 < x 3 := hmono 2 (by omega) (by change 2 < 3; omega)
    exact ⟨i0.val, i1.val, i2.val, emb.strictMono (by change (0 : ℕ) < 1; omega), emb.strictMono (by change (1 : ℕ) < 2; omega), i2.isLt, by omega, by omega⟩
  · rintro ⟨i, j, k, hij, hjk, hk, h1, h2⟩; let x : ℕ → ℕ := fun r => if r = 1 then p.getD j 0 else if r = 2 then p.getD k 0 else p.getD i 0
    have hsub : [x 3, x 1, x 2].Sublist p := (by simpa [x] using sublist_map_getD_drop p [i, j, k] 0 (by simp; omega) (by simp; omega)); refine ⟨x, fun r _ hr => ?_, fun r _ hr => ?_, hsub, by simp⟩
    · change r < 3 at hr; rcases (by omega : r = 1 ∨ r = 2) with rfl | rfl <;> assumption
    · change r ≤ 3 at hr; apply hsub.subset; rcases (by omega : r = 1 ∨ r = 2 ∨ r = 3) with rfl | rfl | rfl <;> simp
private theorem occurs_132_iff (p : List ℕ) : NonnestingDefs.Occurs [1, 3, 2] p ↔ ∃ i j k : ℕ, i < j ∧ j < k ∧ k < p.length ∧ p.getD i 0 < p.getD k 0 ∧ p.getD k 0 < p.getD j 0 := by
  constructor
  · rintro ⟨x, hmono, _, hsub, _⟩; change [x 1, x 3, x 2].Sublist p at hsub; obtain ⟨emb, hemb⟩ := List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp hsub; let i0 := emb ⟨0, by simp⟩; let i1 := emb ⟨1, by simp⟩; let i2 := emb ⟨2, by simp⟩
    have he0 : p.getD i0.val 0 = x 1 := (by rw [List.getD_eq_getElem p 0 i0.isLt]; exact (hemb ⟨0, by simp⟩).symm); have he1 : p.getD i1.val 0 = x 3 := (by rw [List.getD_eq_getElem p 0 i1.isLt]; exact (hemb ⟨1, by simp⟩).symm)
    have he2 : p.getD i2.val 0 = x 2 := (by rw [List.getD_eq_getElem p 0 i2.isLt]; exact (hemb ⟨2, by simp⟩).symm); have hx12 : x 1 < x 2 := hmono 1 (by omega) (by change 1 < 3; omega); have hx23 : x 2 < x 3 := hmono 2 (by omega) (by change 2 < 3; omega)
    exact ⟨i0.val, i1.val, i2.val, emb.strictMono (by change (0 : ℕ) < 1; omega), emb.strictMono (by change (1 : ℕ) < 2; omega), i2.isLt, by omega, by omega⟩
  · rintro ⟨i, j, k, hij, hjk, hk, h1, h2⟩; let x : ℕ → ℕ := fun r => if r = 1 then p.getD i 0 else if r = 2 then p.getD k 0 else p.getD j 0
    have hsub : [x 1, x 3, x 2].Sublist p := (by simpa [x] using sublist_map_getD_drop p [i, j, k] 0 (by simp; omega) (by simp; omega)); refine ⟨x, fun r _ hr => ?_, fun r _ hr => ?_, hsub, by simp⟩
    · change r < 3 at hr; rcases (by omega : r = 1 ∨ r = 2) with rfl | rfl <;> assumption
    · change r ≤ 3 at hr; apply hsub.subset; rcases (by omega : r = 1 ∨ r = 2 ∨ r = 3) with rfl | rfl | rfl <;> simp
private theorem occurs_54321_of_indices {p : List ℕ} {i₁ i₂ i₃ i₄ i₅ : ℕ} (h12 : i₁ < i₂) (h23 : i₂ < i₃) (h34 : i₃ < i₄) (h45 : i₄ < i₅) (h5 : i₅ < p.length) (hv45 : p.getD i₅ 0 < p.getD i₄ 0) (hv34 : p.getD i₄ 0 < p.getD i₃ 0) (hv23 : p.getD i₃ 0 < p.getD i₂ 0) (hv12 : p.getD i₂ 0 < p.getD i₁ 0) :
    NonnestingDefs.Occurs [5, 4, 3, 2, 1] p := by
  let x : ℕ → ℕ := fun r => if r = 1 then p.getD i₅ 0 else if r = 2 then p.getD i₄ 0 else if r = 3 then p.getD i₃ 0 else if r = 4 then p.getD i₂ 0 else p.getD i₁ 0
  have hsub : [x 5, x 4, x 3, x 2, x 1].Sublist p := (by simpa [x] using sublist_map_getD_drop p [i₁, i₂, i₃, i₄, i₅] 0 (by simp; omega) (by simp; omega)); refine ⟨x, fun r _ hr => ?_, fun r _ hr => ?_, hsub, by simp⟩
  · change r < 5 at hr; rcases (by omega : r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4) with rfl | rfl | rfl | rfl <;> assumption
  · change r ≤ 5 at hr; apply hsub.subset
    rcases (by omega : r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5) with
      rfl | rfl | rfl | rfl | rfl <;> simp
private theorem not_occurs_54321_of_three_smaller (p : List ℕ) (h : ∀ i < p.length, ∃ a c d : ℕ, ∀ j, i < j → j < p.length → p.getD j 0 < p.getD i 0 → p.getD j 0 = a ∨ p.getD j 0 = c ∨ p.getD j 0 = d) : ¬ NonnestingDefs.Occurs [5, 4, 3, 2, 1] p := by
  rintro ⟨x, hmono, _, hsub, _⟩; change [x 5, x 4, x 3, x 2, x 1].Sublist p at hsub; obtain ⟨emb, hemb⟩ := List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp hsub; let e0 := emb ⟨0, by simp⟩; let e1 := emb ⟨1, by simp⟩; let e2 := emb ⟨2, by simp⟩; let e3 := emb ⟨3, by simp⟩; let e4 := emb ⟨4, by simp⟩
  have h0 : p.getD e0.val 0 = x 5 := (by rw [List.getD_eq_getElem p 0 e0.isLt]; exact (hemb ⟨0, by simp⟩).symm); have h1 : p.getD e1.val 0 = x 4 := (by rw [List.getD_eq_getElem p 0 e1.isLt]; exact (hemb ⟨1, by simp⟩).symm)
  have h2 : p.getD e2.val 0 = x 3 := (by rw [List.getD_eq_getElem p 0 e2.isLt]; exact (hemb ⟨2, by simp⟩).symm); have h3 : p.getD e3.val 0 = x 2 := (by rw [List.getD_eq_getElem p 0 e3.isLt]; exact (hemb ⟨3, by simp⟩).symm)
  have h4 : p.getD e4.val 0 = x 1 := (by rw [List.getD_eq_getElem p 0 e4.isLt]; exact (hemb ⟨4, by simp⟩).symm); have hx12 : x 1 < x 2 := hmono 1 (by omega) (by change 1 < 5; omega); have hx23 : x 2 < x 3 := hmono 2 (by omega) (by change 2 < 5; omega)
  have hx34 : x 3 < x 4 := hmono 3 (by omega) (by change 3 < 5; omega); have hx45 : x 4 < x 5 := hmono 4 (by omega) (by change 4 < 5; omega); obtain ⟨a, c, d, habc⟩ := h e0.val e0.isLt; have c1 := habc e1.val (emb.strictMono (by change (0 : ℕ) < 1; omega)) e1.isLt (by omega)
  have c2 := habc e2.val (emb.strictMono (by change (0 : ℕ) < 2; omega)) e2.isLt (by omega); have c3 := habc e3.val (emb.strictMono (by change (0 : ℕ) < 3; omega)) e3.isLt (by omega); have c4 := habc e4.val (emb.strictMono (by change (0 : ℕ) < 4; omega)) e4.isLt (by omega); omega
private theorem perm_bounds {n : ℕ} {p : List ℕ} (hperm : p.Perm (List.range' 1 n)) {v : ℕ} (hv : v ∈ p) : 1 ≤ v ∧ v ≤ n := by have hr := hperm.mem_iff.mp hv; simp only [List.mem_range', Nat.one_mul] at hr; obtain ⟨k, hk, rfl⟩ := hr; omega
private theorem perm_getD_bounds {n : ℕ} {p : List ℕ} (hperm : p.Perm (List.range' 1 n)) {i : ℕ} (hi : i < n) : 1 ≤ p.getD i 0 ∧ p.getD i 0 ≤ n := by have hlen : p.length = n := (by simpa using hperm.length_eq); rw [List.getD_eq_getElem p 0 (by omega)]; exact perm_bounds hperm (List.getElem_mem (by omega))
private theorem perm_getD_inj {n : ℕ} {p : List ℕ} (hperm : p.Perm (List.range' 1 n)) {i j : ℕ} (hi : i < n) (hj : j < n) (heq : p.getD i 0 = p.getD j 0) : i = j := by
  have hlen : p.length = n := (by simpa using hperm.length_eq); rw [List.getD_eq_getElem p 0 (by omega), List.getD_eq_getElem p 0 (by omega)] at heq; exact (List.Nodup.getElem_inj_iff (hperm.nodup_iff.mpr (List.nodup_range' 1))).mp heq
private theorem ne_val_of_getD {n i j v : ℕ} {p : List ℕ} (hperm : p.Perm (List.range' 1 n)) (hi : i < n) (hj : j < n) (hij : i ≠ j) (hv : p.getD j 0 = v) : p.getD i 0 ≠ v := fun h => hij (perm_getD_inj hperm hi hj (h.trans hv.symm))
private theorem perm_idxOf_spec {n : ℕ} {p : List ℕ} (hperm : p.Perm (List.range' 1 n)) (v : ℕ) (hv1 : 1 ≤ v) (hvn : v ≤ n) : p.idxOf v < n ∧ p.getD (p.idxOf v) 0 = v := by
  have hlen : p.length = n := by simpa using hperm.length_eq
  have hmem : v ∈ p := hperm.mem_iff.mpr (by
    simp only [List.mem_range', Nat.one_mul]; exact ⟨v - 1, by omega, by omega⟩)
  have hlt : p.idxOf v < p.length := List.idxOf_lt_length_iff.mpr hmem; exact ⟨by omega, by rw [List.getD_eq_getElem p 0 hlt]; exact List.getElem_idxOf hlt⟩
private theorem idxOf_ne_of_getD {n : ℕ} {p : List ℕ} (hperm : p.Perm (List.range' 1 n)) (v i : ℕ) (hv1 : 1 ≤ v) (hvn : v ≤ n) (h : p.getD i 0 ≠ v) : p.idxOf v ≠ i := fun he => h (he ▸ (perm_idxOf_spec hperm v hv1 hvn).2)
private theorem perm_idxOf_getD {n : ℕ} {p : List ℕ} (hperm : p.Perm (List.range' 1 n)) {i : ℕ} (hi : i < n) : p.idxOf (p.getD i 0) = i := by have hb := perm_getD_bounds hperm hi; have hs := perm_idxOf_spec hperm _ hb.1 hb.2; exact perm_getD_inj hperm hs.1 hi hs.2
private theorem square_perm_and_getD {n : ℕ} {p : List ℕ} (hperm : p.Perm (List.range' 1 n)) : (square p).Perm (List.range' 1 n) ∧ ∀ i < n, (square p).getD i 0 = p.getD (p.getD i 0 - 1) 0 := by
  have hlen : p.length = n := (by simpa using hperm.length_eq); refine ⟨?_, fun i hi => ?_⟩
  · have hmap : (List.range' 1 n).map (fun x => p.getD (x - 1) 0) = p := by
      apply List.ext_getElem (by simp [hlen]); intro i _ hp; simp only [List.getElem_map, List.getElem_range', Nat.one_mul]; rw [show 1 + i - 1 = i by omega]; exact List.getD_eq_getElem p 0 hp
    have hm := hperm.map (fun x => p.getD (x - 1) 0); rw [hmap] at hm; exact hm.trans hperm
  · rw [List.getD_eq_getElem (square p) 0 (by simp [square, hlen, hi])]; simp only [square, List.getElem_map]; rw [← List.getD_eq_getElem p 0 (by omega)]
private theorem getD_of_sq_eq {n : ℕ} {p : List ℕ} (hperm : p.Perm (List.range' 1 n)) (x v : ℕ) (hx : x < n) (hv1 : 1 ≤ v) (hvn : v ≤ n) (hsqv : (square p).getD x 0 = v) : p.getD x 0 = p.idxOf v + 1 := by
  have hs := perm_idxOf_spec hperm v hv1 hvn; have hb := perm_getD_bounds hperm hx; have h1 : p.getD (p.getD x 0 - 1) 0 = p.getD (p.idxOf v) 0 := (by rw [← (square_perm_and_getD hperm).2 x hx, hsqv, hs.2]); have := perm_getD_inj hperm (by omega) hs.1 h1; omega
private theorem ending_in_one_indecomposable (n : ℕ) (p : List ℕ) (hn : 1 ≤ n) (hperm : p.Perm (List.range' 1 n)) (hlast : p.getLast? = some 1) : sumIndecomposable p := by
  have hlen : p.length = n := (by simpa using hperm.length_eq); have hend : p.getD (n - 1) 0 = 1 := (by obtain ⟨init, rfl⟩ := List.getLast?_eq_some_iff.mp hlast; have hi : init.length = n - 1 := (by simp at hlen; omega); rw [List.getD_append_right _ _ _ _ (by omega), hi, Nat.sub_self]; rfl)
  intro k hkpos; have htl : 0 < (p.take k.val).length := (by simp [hlen]; omega); have hdl : n - 1 - k.val < (p.drop k.val).length := (by simp [hlen]; omega); refine ⟨⟨0, htl⟩, ⟨n - 1 - k.val, hdl⟩, ?_⟩
  have h1 : (p.drop k.val).get ⟨n - 1 - k.val, hdl⟩ = 1 := (by rw [List.get_eq_getElem, List.getElem_drop]; dsimp only; rw [← List.getD_eq_getElem p 0 (by omega), show k.val + (n - 1 - k.val) = n - 1 by omega]; exact hend)
  have h2 := (perm_bounds hperm (List.mem_of_mem_take (List.get_mem (p.take k.val) ⟨0, htl⟩))).1; omega
private theorem prefix_image_iff (n : ℕ) (p : List ℕ) (hperm : p.Perm (List.range' 1 n)) : sumIndecomposable p ↔ ¬ ∃ k : ℕ, 1 ≤ k ∧ k < n ∧ (Finset.Icc 1 k).image (fun i => p.getD (i - 1) 0) = Finset.Icc 1 k := by
  have hlen : p.length = n := (by simpa using hperm.length_eq); let f : ℕ → ℕ := fun i => p.getD (i - 1) 0; constructor
  · intro hind ⟨k, hk1, hkn, himg⟩; let kfin : Fin p.length := ⟨k, by omega⟩
    obtain ⟨i, j, hle⟩ := hind kfin (by change 0 < k; omega); have hi_lt : i.val < k := (by simpa [kfin, hlen, Nat.min_eq_left (by omega : k ≤ n)] using i.isLt); have hj_lt : j.val < n - k := (by simpa [kfin, hlen] using j.isLt)
    have hai : (p.take kfin.val).get i = f (i.val + 1) := (by simp only [kfin, f, Nat.add_sub_cancel, List.get_eq_getElem, List.getElem_take]; rw [List.getD_eq_getElem p 0 (by omega)])
    have hbj : (p.drop kfin.val).get j = p.getD (k + j.val) 0 := (by simp only [kfin, List.get_eq_getElem, List.getElem_drop]; rw [List.getD_eq_getElem p 0 (by omega)])
    have ha_le : (p.take kfin.val).get i ≤ k := (by have hm : f (i.val + 1) ∈ Finset.Icc 1 k := (by rw [← himg]; exact Finset.mem_image_of_mem f (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)); rw [hai]; exact (Finset.mem_Icc.mp hm).2)
    have hb_gt : k < (p.drop kfin.val).get j := by
      by_contra hnot; have hm : p.getD (k + j.val) 0 ∈ (Finset.Icc 1 k).image f := (by rw [himg, Finset.mem_Icc]; exact ⟨(perm_getD_bounds hperm (by omega : k + j.val < n)).1, by rw [hbj] at hnot; omega⟩)
      obtain ⟨r, hr, hrf⟩ := Finset.mem_image.mp hm; have hr' := Finset.mem_Icc.mp hr; have := perm_getD_inj hperm (by omega) (by omega) hrf; omega
    omega
  · intro hno; by_contra hnot; simp only [sumIndecomposable, not_forall, not_exists, not_le] at hnot; obtain ⟨k, hkpos, hsep⟩ := hnot; apply hno; refine ⟨k.val, by omega, by omega, ?_⟩
    have hinj : Set.InjOn f (Finset.Icc 1 k.val) := fun x hx y hy hxy => (by have hx' := Finset.mem_Icc.mp hx; have hy' := Finset.mem_Icc.mp hy; have := perm_getD_inj hperm (by omega) (by omega) hxy; omega); have hcard := Finset.card_image_of_injOn hinj
    have hsub : (Finset.Icc 1 k.val).image f ⊆ Finset.Icc 1 k.val := by
      intro v hv; obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hv; have hr' := Finset.mem_Icc.mp hr; refine Finset.mem_Icc.mpr ⟨(perm_getD_bounds hperm (by omega : r - 1 < n)).1, ?_⟩; by_contra hgt
      have hall : Finset.Icc 1 k.val ⊆ (Finset.Icc 1 k.val).image f := by
        intro u hu; have hu' := Finset.mem_Icc.mp hu; have hus := perm_idxOf_spec hperm u hu'.1 (by omega); by_cases hidx : p.idxOf u < k.val
        · exact Finset.mem_image.mpr ⟨p.idxOf u + 1, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by change p.getD (p.idxOf u + 1 - 1) 0 = u; rw [Nat.add_sub_cancel]; exact hus.2⟩
        · have htl : r - 1 < (p.take k.val).length := (by simp [hlen]; omega); have hdl : p.idxOf u - k.val < (p.drop k.val).length := (by simp [hlen]; omega); have hlt := hsep ⟨r - 1, htl⟩ ⟨p.idxOf u - k.val, hdl⟩
          have h1 : (p.take k.val).get ⟨r - 1, htl⟩ = f r := (by simp only [f, List.get_eq_getElem, List.getElem_take]; rw [List.getD_eq_getElem p 0 (by omega)])
          have h2 : (p.drop k.val).get ⟨p.idxOf u - k.val, hdl⟩ = u := (by rw [List.get_eq_getElem, List.getElem_drop]; dsimp only; rw [← List.getD_eq_getElem p 0 (by omega), show k.val + (p.idxOf u - k.val) = p.idxOf u by omega]; exact hus.2); omega
      have hle := Finset.card_le_card (Finset.insert_subset_iff.mpr ⟨hv, hall⟩); rw [Finset.card_insert_of_notMem (by rw [Finset.mem_Icc]; omega), hcard] at hle; omega
    exact Finset.eq_of_subset_of_card_le hsub (by rw [hcard])
/-- Basic counts, prefix-image characterization, ending-in-one criterion, and shape constraints for indecomposable square-avoiders. -/
theorem indecomposable_shape_and_prefix_iff : b 0 = 0 ∧ (∀ n : ℕ, 1 ≤ n → indecomposableAvoiders n = {p | p ∈ avoiders n ∧ sumIndecomposable p} ∧ b n = {p | p ∈ avoiders n ∧ sumIndecomposable p}.ncard) ∧
    (∀ (n : ℕ) (p : List ℕ), p.Perm (List.range' 1 n) → (sumIndecomposable p ↔ ¬ ∃ k : ℕ, 1 ≤ k ∧ k < n ∧ (Finset.Icc 1 k).image (fun i => p.getD (i - 1) 0) = Finset.Icc 1 k)) ∧
    (∀ (n : ℕ) (p : List ℕ), 1 ≤ n → p.Perm (List.range' 1 n) → p.getLast? = some 1 → sumIndecomposable p) ∧ (∀ n : ℕ, 2 ≤ n → ∀ p ∈ indecomposableAvoiders n, let m := p.getD 0 0; let posN := p.idxOf n + 1; let q := square p;
      (p.getD (n - 1) 0 = 1 ∧ p.getLast? = some 1) ∧ (2 ≤ m ∧ m ≤ 4 ∧ ∀ u v : ℕ, 2 ≤ u → u < v → v ≤ m - 1 → 1 < p.idxOf v + 1 ∧ p.idxOf v + 1 < p.idxOf u + 1) ∧
      (q.getD (posN - 1) 0 = 1 ∧ q.getD (n - 1) 0 = m ∧ (∀ i j : ℕ, posN + 1 ≤ i → i < j → j ≤ n → q.getD (i - 1) 0 < q.getD (j - 1) 0) ∧ n + 1 ≤ posN + m ∧ n - m + 1 ≤ posN ∧ (m = 2 → posN = n - 1)) ∧
      (∀ i j : ℕ, posN + 1 ≤ i → i < j → j ≤ n → p.getD (j - 1) 0 < p.getD (i - 1) 0) ∧
      (∀ u : ℕ, 2 ≤ u → u ≤ m - 1 → 1 < p.idxOf u + 1) ∧ n - 3 ≤ posN ∧ posN ≤ n - 1) := by
  refine ⟨?_, ?_, prefix_image_iff, ending_in_one_indecomposable, ?_⟩
  · have hemp : indecomposableAvoiders 0 = ∅ := by
      ext p; refine ⟨fun ⟨hp, ⟨hperm, _⟩, _⟩ => hp (List.perm_nil.mp (by simpa using hperm)), ?_⟩; intro h; cases h
    simp [b, hemp]
  · intro n hn; have heq : indecomposableAvoiders n = {p | p ∈ avoiders n ∧ sumIndecomposable p} := (by ext p; refine ⟨fun h => h.2, fun h => ?_⟩; have hlen : p.length = n := (by simpa using h.1.1.length_eq); exact ⟨List.length_pos_iff.mp (by omega), h⟩); exact ⟨heq, by simp [b, heq]⟩
  · intro n hn p ⟨hpne, ⟨hperm, hav312, hav54321, hav132⟩, hind⟩; dsimp only; have hlen : p.length = n := (by simpa using hperm.length_eq); have hsq := square_perm_and_getD hperm; have hqlen : (square p).length = n := (by simpa using hsq.1.length_eq)
    have hlast : p.getLast? = some 1 := component_ends_one p hpne (by simpa [hlen] using hperm) hind hav312
    have hend : p.getD (n - 1) 0 = 1 := (by obtain ⟨init, heq⟩ := List.getLast?_eq_some_iff.mp hlast; have hi : init.length = n - 1 := (by rw [heq] at hlen; simp at hlen; omega); rw [heq, List.getD_append_right _ _ _ _ (by omega), hi, Nat.sub_self]; rfl)
    have hm_bounds := perm_getD_bounds hperm (by omega : 0 < n); have hm_ge2 : 2 ≤ p.getD 0 0 := (by have := ne_val_of_getD hperm (by omega) (by omega) (by omega : 0 ≠ n - 1) hend; omega)
    have hdec_small : ∀ u v : ℕ, 2 ≤ u → u < v → v ≤ p.getD 0 0 - 1 →
        1 < p.idxOf v + 1 ∧ p.idxOf v + 1 < p.idxOf u + 1 := by
      intro u v hu huv hvm; have hsu := perm_idxOf_spec hperm u (by omega) (by omega); have hsv := perm_idxOf_spec hperm v (by omega) (by omega); have hv0 := idxOf_ne_of_getD hperm v 0 (by omega) (by omega) (by omega)
      have hu0 := idxOf_ne_of_getD hperm u 0 (by omega) (by omega) (by omega); refine ⟨by omega, ?_⟩; by_contra hnot; have hne : p.idxOf u ≠ p.idxOf v := fun heq => (by rw [heq] at hsu; omega); exact hav312 ((occurs_312_iff p).mpr ⟨0, p.idxOf u, p.idxOf v, by omega, by omega, by omega, by omega, by omega⟩)
    have hm_le4 : p.getD 0 0 ≤ 4 := by
      by_contra hgt; have h23 := hdec_small 2 3 (by omega) (by omega) (by omega); have h34 := hdec_small 3 4 (by omega) (by omega) (by omega); have hs2 := perm_idxOf_spec hperm 2 (by omega) (by omega)
      have hs3 := perm_idxOf_spec hperm 3 (by omega) (by omega); have hs4 := perm_idxOf_spec hperm 4 (by omega) (by omega); have h2n := idxOf_ne_of_getD hperm 2 (n - 1) (by omega) (by omega) (by omega)
      exact hav54321 (occurs_54321_of_indices (i₁ := 0) (i₂ := p.idxOf 4) (i₃ := p.idxOf 3) (i₄ := p.idxOf 2) (i₅ := n - 1) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))
    have hsn := perm_idxOf_spec hperm n (by omega) le_rfl; have hqp0 : (square p).getD (p.idxOf n) 0 = 1 := (by rw [hsq.2 (p.idxOf n) hsn.1, hsn.2, hend])
    have hqp : (square p).getD (p.idxOf n + 1 - 1) 0 = 1 := (by rwa [Nat.add_sub_cancel]); have hqn : (square p).getD (n - 1) 0 = p.getD 0 0 := (by rw [hsq.2 (n - 1) (by omega), hend])
    have hq_inc : ∀ i j : ℕ, p.idxOf n + 1 + 1 ≤ i → i < j → j ≤ n →
        (square p).getD (i - 1) 0 < (square p).getD (j - 1) 0 := by
      intro i j hi hij hj; have hbj := perm_getD_bounds hsq.1 (by omega : j - 1 < n); have hne : (square p).getD (i - 1) 0 ≠ (square p).getD (j - 1) 0 := fun heq => (by have := perm_getD_inj hsq.1 (by omega) (by omega) heq; omega)
      have hne1 := ne_val_of_getD hsq.1 (by omega) hsn.1 (by omega : j - 1 ≠ p.idxOf n) hqp0; by_contra hnot; exact hav132 ((occurs_132_iff (square p)).mpr ⟨p.idxOf n, i - 1, j - 1, by omega, by omega, by omega, by rw [hqp0]; omega, by omega⟩)
    have hpn_ne := idxOf_ne_of_getD hperm n (n - 1) (by omega) le_rfl (by omega)
    have hpos_bound : n + 1 ≤ (p.idxOf n + 1) + p.getD 0 0 := by
      by_contra hnot
      have hstep : ∀ t ≤ n - (p.idxOf n + 2), 2 + t ≤ (square p).getD (p.idxOf n + 1 + t) 0 := by
        intro t ht; induction t with
        | zero => simp only [Nat.add_zero]; have hb := perm_getD_bounds hsq.1 (by omega : p.idxOf n + 1 < n); have := ne_val_of_getD hsq.1 (by omega) hsn.1 (by omega : p.idxOf n + 1 ≠ p.idxOf n) hqp0; omega
        | succ t ih => have hprev := ih (by omega); have hlt := hq_inc (p.idxOf n + 2 + t) (p.idxOf n + 3 + t) (by omega) (by omega) (by omega); rw [show p.idxOf n + 2 + t - 1 = p.idxOf n + 1 + t by omega, show p.idxOf n + 3 + t - 1 = p.idxOf n + 1 + (t + 1) by omega] at hlt; omega
      have hend_bound := hstep (n - (p.idxOf n + 2)) le_rfl; rw [show p.idxOf n + 1 + (n - (p.idxOf n + 2)) = n - 1 by omega, hqn] at hend_bound; omega
    have hp_dec : ∀ i j : ℕ, p.idxOf n + 1 + 1 ≤ i → i < j → j ≤ n →
        p.getD (j - 1) 0 < p.getD (i - 1) 0 := by
      intro i j hi hij hj; have hbj := perm_getD_bounds hperm (by omega : j - 1 < n); have hne : p.getD (i - 1) 0 ≠ p.getD (j - 1) 0 := fun heq => (by have := perm_getD_inj hperm (by omega) (by omega) heq; omega)
      have hnen := ne_val_of_getD hperm (by omega) hsn.1 (by omega : j - 1 ≠ p.idxOf n) hsn.2; by_contra hnot; exact hav312 ((occurs_312_iff p).mpr ⟨p.idxOf n, i - 1, j - 1, by omega, by omega, by omega, by omega, by rw [hsn.2]; omega⟩)
    have hright_small : ∀ u : ℕ, 2 ≤ u → u ≤ p.getD 0 0 - 1 → 1 < p.idxOf u + 1 := fun u hu hum => by
      have hu0 := idxOf_ne_of_getD hperm u 0 (by omega) (by omega) (by omega); omega
    exact ⟨⟨hend, hlast⟩, ⟨hm_ge2, hm_le4, hdec_small⟩,
      ⟨hqp, hqn, hq_inc, hpos_bound, by omega, fun hm2 => by have := hsn.1; omega⟩, hp_dec,
      hright_small, by omega, by have := hsn.1; omega⟩
private theorem getD_app_left {a c : List ℕ} {i : ℕ} (h : i < a.length) : (a ++ c).getD i 0 = a.getD i 0 := List.getD_append a c 0 i h
private theorem getD_app_right {a c : List ℕ} {i : ℕ} (h : a.length ≤ i) : (a ++ c).getD i 0 = c.getD (i - a.length) 0 := List.getD_append_right a c 0 i h
private theorem flatMap_pair_length (m a c : ℕ) : ((List.range m).flatMap fun r => [2 * r + a, 2 * r + c]).length = 2 * m := by
  induction m with
  | zero => rfl
  | succ m ih => rw [List.range_succ, List.flatMap_append, List.length_append, ih]; simp; omega
private theorem flatMap_pair_getD (m a c idx : ℕ) (h : idx < 2 * m) : ((List.range m).flatMap fun r => [2 * r + a, 2 * r + c]).getD idx 0 = if idx % 2 = 0 then idx + a else idx - 1 + c := by
  induction m with
  | zero => omega
  | succ m ih =>
    rw [List.range_succ, List.flatMap_append]; by_cases hlt : idx < 2 * m
    · rw [getD_app_left (by rw [flatMap_pair_length]; exact hlt), ih hlt]
    · rw [getD_app_right (by rw [flatMap_pair_length]; omega), flatMap_pair_length]; rcases (by omega : idx = 2 * m ∨ idx = 2 * m + 1) with rfl | rfl
      · rw [Nat.sub_self]; change 2 * m + a = _; split <;> omega
      · rw [show 2 * m + 1 - 2 * m = 1 by omega]; change 2 * m + c = _; split <;> omega
private theorem getD_range' (s len idx : ℕ) (h : idx < len) : (List.range' s len).getD idx 0 = s + idx := by rw [List.getD_eq_getElem _ 0 (by simp [h])]; simp
private theorem admissible_of_spec {n : ℕ} (hn : 2 ≤ n) (f : List ℕ) (entry sq : ℕ → ℕ) (hlen : f.length = n) (hend : entry (n - 1) = 1) (hget : ∀ i < n, f.getD i 0 = entry i) (hsurj : ∀ v, 1 ≤ v → v ≤ n → ∃ i < n, entry i = v) (hsq : ∀ i < n, ∀ v, entry i = v → entry (v - 1) = sq i)
    (hdec3 : ∀ i < n, ∃ ja jc jd : ℕ, ja ≤ jc ∧ jc ≤ jd ∧ entry jd ≤ entry jc ∧ entry jc ≤ entry ja ∧ ∀ j, i < j → j < n → entry j < entry i → j = ja ∨ j = jc ∨ j = jd)
    (h132 : ∀ j k, j < k → k < n → sq k < sq j → ∀ i < j, sq k ≤ sq i) :
    f ∈ indecomposableAvoiders n := by
  have hsub : List.range' 1 n ⊆ f := fun v hv => by
    simp only [List.mem_range', Nat.one_mul] at hv; obtain ⟨k, hk, rfl⟩ := hv; obtain ⟨i, hi, hei⟩ := hsurj (1 + k) (by omega) (by omega); have hgi := hget i hi; rw [List.getD_eq_getElem f 0 (by omega)] at hgi; rw [← hei, ← hgi]; exact List.getElem_mem (by omega)
  have hperm : f.Perm (List.range' 1 n) := (((List.nodup_range' 1).subperm hsub).perm_of_length_le (by simp [hlen])).symm
  have hlast : f.getLast? = some 1 := (by rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)]; have h1 := hget (n - 1) (by omega); rw [List.getD_eq_getElem f 0 (by omega), hend] at h1; simpa [hlen] using h1)
  have hav312 : ¬ NonnestingDefs.Occurs [3, 1, 2] f := by
    rw [occurs_312_iff]; rintro ⟨i, j, k, hij, hjk, hk, h1, h2⟩; rw [hlen] at hk; rw [hget i (by omega)] at h2; rw [hget j (by omega)] at h1; rw [hget k hk] at h1 h2; obtain ⟨ja, jc, jd, ha1, ha2, ha3, ha4, hspec⟩ := hdec3 i (by omega)
    rcases hspec j hij (by omega) (by omega) with rfl | rfl | rfl <;> rcases hspec k (by omega) hk h2 with rfl | rfl | rfl <;> omega
  have hav54321 : ¬ NonnestingDefs.Occurs [5, 4, 3, 2, 1] f := by
    apply not_occurs_54321_of_three_smaller; intro i hi; rw [hlen] at hi; obtain ⟨ja, jc, jd, _, _, _, _, hspec⟩ := hdec3 i hi; refine ⟨entry ja, entry jc, entry jd, fun j hij hj hlt => ?_⟩; rw [hlen] at hj; rw [hget i hi, hget j hj] at hlt; rw [hget j hj]; rcases hspec j hij hj hlt with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  have hsq_get : ∀ i < n, (square f).getD i 0 = sq i := fun i hi => (by have hb := perm_getD_bounds hperm hi; rw [(square_perm_and_getD hperm).2 i hi, hget i hi, hget (entry i - 1) (by rw [← hget i hi]; omega), hsq i hi _ rfl])
  have hav132 : ¬ NonnestingDefs.Occurs [1, 3, 2] (square f) := by
    rw [occurs_132_iff]; rintro ⟨i, j, k, hij, hjk, hk, h1, h2⟩; have hsqlen : (square f).length = n := (by simp [square, hlen]); rw [hsqlen] at hk; rw [hsq_get i (by omega)] at h1; rw [hsq_get j (by omega)] at h2; rw [hsq_get k hk] at h1 h2; have := h132 j k hjk hk h2 i hij; omega
  exact ⟨List.length_pos_iff.mp (by omega), ⟨hperm, hav312, hav54321, hav132⟩, ending_in_one_indecomposable n f (by omega) hperm hlast⟩
private theorem familyI_getD (n i : ℕ) (hn : 2 ≤ n) (hi : i < n) : (familyI n).getD i 0 = if i < n - 1 then i + 2 else 1 := by
  unfold familyI; by_cases h : i < n - 1
  · rw [getD_app_left (by simp [h]), getD_range' 2 (n - 1) i h]; split <;> omega
  · obtain rfl : i = n - 1 := (by omega); rw [getD_app_right (by simp), List.length_range', Nat.sub_self]; change 1 = _; split <;> omega
private theorem familyJ_getD (n i : ℕ) (hn : 5 ≤ n) (hi : i < n) : (familyJ n).getD i 0 = if i = 0 then 2 else if i = 1 then 4 else if i = 2 then 3 else if i < n - 1 then i + 2 else 1 := by
  unfold familyJ; rw [List.append_assoc]; by_cases h3 : i < 3
  · rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;> rfl
  · rw [getD_app_right (by simp; omega)]; change (List.range' 5 (n - 4) ++ [1]).getD (i - 3) 0 = _; by_cases h : i < n - 1
    · rw [getD_app_left (by simp; omega), getD_range' 5 (n - 4) (i - 3) (by omega)]; repeat' (split <;> try omega)
    · obtain rfl : i = n - 1 := (by omega); rw [getD_app_right (by simp; omega), List.length_range', show n - 1 - 3 - (n - 4) = 0 by omega]; change 1 = _; repeat' (split <;> try omega)
private theorem familyK_getD (n j i : ℕ) (hn : 6 ≤ n) (_hj : j ≤ (n - 6) / 2) (hi : i < n) : (familyK n j).getD i 0 = if i = 0 then 2 else if i ≤ 2 * j + 2 then (if i % 2 = 1 then i + 4 else i + 2) else if i = 2 * j + 3 then 3 else if i < n - 1 then i + 2 else 1 := by
  unfold familyK; let mid := (List.range (j + 1)).flatMap fun r => [2 * r + 5, 2 * r + 4]; have hmid : mid.length = 2 * j + 2 := (by simpa [mid, Nat.mul_add] using flatMap_pair_length (j + 1) 5 4); change ([2] ++ mid ++ [3] ++ List.range' (2 * j + 6) (n - (2 * j + 5)) ++ [1]).getD i 0 = _; by_cases h0 : i = 0
  · subst i; rfl
  by_cases h1 : i ≤ 2 * j + 2
  · rw [List.append_assoc ([2] ++ mid), List.append_assoc ([2] ++ mid), getD_app_left (by simp [hmid]; omega), getD_app_right (by simp; omega)]; change mid.getD (i - 1) 0 = _; rw [flatMap_pair_getD (j + 1) 5 4 (i - 1) (by omega)]; repeat' (split <;> try omega)
  by_cases h2 : i = 2 * j + 3
  · subst i; rw [List.append_assoc ([2] ++ mid ++ [3]), getD_app_left (by simp [hmid]), getD_app_right (by simp [hmid])]; have hsub : 2 * j + 3 - ([2] ++ mid).length = 0 := (by simp [hmid]); rw [hsub]; change 3 = _; repeat' (split <;> try omega)
  by_cases h3 : i < n - 1
  · rw [getD_app_left (by simp [hmid]; omega), getD_app_right (by simp [hmid]; omega)]; have hlen : ([2] ++ mid ++ [3]).length = 2 * j + 4 := (by simp [hmid]); rw [hlen, getD_range' (2 * j + 6) (n - (2 * j + 5)) (i - (2 * j + 4)) (by omega)]; repeat' (split <;> try omega)
  · obtain rfl : i = n - 1 := (by omega); rw [getD_app_right (by simp [hmid]; omega)]; have hsub : n - 1 - ([2] ++ mid ++ [3] ++ List.range' (2 * j + 6) (n - (2 * j + 5))).length = 0 := (by simp [hmid]; omega); rw [hsub]; change 1 = _; repeat' (split <;> try omega)
private theorem familyA_getD (n i : ℕ) (hn : 6 ≤ n) (hi : i < n) : (familyA n).getD i 0 = if i = 0 then 4 else if i = 1 then 3 else if i < n - 2 then i + 3 else if i = n - 2 then 2 else 1 := by
  unfold familyA; by_cases h2 : i < 2
  · rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> rfl
  by_cases h : i < n - 2
  · rw [List.append_assoc, getD_app_right (by simp; omega), getD_app_left (by simp; omega)]; change (List.range' 5 (n - 4)).getD (i - 2) 0 = _; rw [getD_range' 5 (n - 4) (i - 2) (by omega)]; repeat' (split <;> try omega)
  · rw [getD_app_right (by simp; omega)]; have hlen : ([4, 3] ++ List.range' 5 (n - 4)).length = n - 2 := (by simp; omega); rw [hlen]; rcases (by omega : i = n - 2 ∨ i = n - 1) with rfl | rfl
    · rw [Nat.sub_self]; change 2 = _; repeat' (split <;> try omega)
    · rw [show n - 1 - (n - 2) = 1 by omega]; change 1 = _; repeat' (split <;> try omega)
private theorem familyB_getD (n i : ℕ) (hn : 7 ≤ n) (hi : i < n) : (familyB n).getD i 0 = if i = 0 then 4 else if i = 1 then 3 else if i = 2 then 5 else if i < 3 + 2 * ((n - 5) / 2) then (if i % 2 = 1 then i + 4 else i + 2) else if n % 2 = 1 then (if i = n - 2 then 2 else 1)
      else (if i = n - 3 then 2 else if i = n - 2 then n else 1) := by
  unfold familyB; let mid := (List.range ((n - 5) / 2)).flatMap fun r => [2 * r + 7, 2 * r + 6]; have hmid : mid.length = 2 * ((n - 5) / 2) := flatMap_pair_length ((n - 5) / 2) 7 6; change ([4, 3, 5] ++ mid ++ (if n % 2 = 1 then [2, 1] else [2, n, 1])).getD i 0 = _; by_cases h3 : i < 3
  · rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;> rfl
  by_cases hm : i < 3 + 2 * ((n - 5) / 2)
  · rw [getD_app_left (by simp [hmid]; omega), getD_app_right (by simp; omega)]; change mid.getD (i - 3) 0 = _; rw [flatMap_pair_getD ((n - 5) / 2) 7 6 (i - 3) (by omega)]; repeat' (split <;> try omega)
  · rw [getD_app_right (by simp [hmid]; omega)]; have hlen : ([4, 3, 5] ++ mid).length = 3 + 2 * ((n - 5) / 2) := (by simp [hmid]; omega); rw [hlen]; by_cases hp : n % 2 = 1
    · simp only [hp, ↓reduceIte, show 3 + 2 * ((n - 5) / 2) = n - 2 by omega]
      rcases (by omega : i = n - 2 ∨ i = n - 1) with rfl | rfl
      · rw [Nat.sub_self]; change 2 = _; repeat' (split <;> try omega)
      · rw [show n - 1 - (n - 2) = 1 by omega]; change 1 = _; repeat' (split <;> try omega)
    · simp only [hp, ↓reduceIte, show 3 + 2 * ((n - 5) / 2) = n - 3 by omega]
      rcases (by omega : i = n - 3 ∨ i = n - 2 ∨ i = n - 1) with rfl | rfl | rfl
      · rw [Nat.sub_self]; change 2 = _; repeat' (split <;> try omega)
      · rw [show n - 2 - (n - 3) = 1 by omega]; change n = _; repeat' (split <;> try omega)
      · rw [show n - 1 - (n - 3) = 2 by omega]; change 1 = _; repeat' (split <;> try omega)
private theorem familyC_getD (n i : ℕ) (hn : 4 ≤ n) (hi : i < n) : (familyC n).getD i 0 = if i = 0 then 4 else if i = 1 then 3 else if i < 2 + 2 * ((n - 4) / 2) then (if i % 2 = 0 then i + 4 else i + 2) else if n % 2 = 0 then (if i = n - 2 then 2 else 1)
      else (if i = n - 3 then 2 else if i = n - 2 then n else 1) := by
  unfold familyC; let mid := (List.range ((n - 4) / 2)).flatMap fun r => [2 * r + 6, 2 * r + 5]; have hmid : mid.length = 2 * ((n - 4) / 2) := flatMap_pair_length ((n - 4) / 2) 6 5; change ([4, 3] ++ mid ++ (if n % 2 = 0 then [2, 1] else [2, n, 1])).getD i 0 = _; by_cases h2 : i < 2
  · rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> rfl
  by_cases hm : i < 2 + 2 * ((n - 4) / 2)
  · rw [getD_app_left (by simp [hmid]; omega), getD_app_right (by simp; omega)]; change mid.getD (i - 2) 0 = _; rw [flatMap_pair_getD ((n - 4) / 2) 6 5 (i - 2) (by omega)]; repeat' (split <;> try omega)
  · rw [getD_app_right (by simp [hmid]; omega)]; have hlen : ([4, 3] ++ mid).length = 2 + 2 * ((n - 4) / 2) := (by simp [hmid]; omega); rw [hlen]; by_cases hp : n % 2 = 0
    · simp only [hp, ↓reduceIte, show 2 + 2 * ((n - 4) / 2) = n - 2 by omega]
      rcases (by omega : i = n - 2 ∨ i = n - 1) with rfl | rfl
      · rw [Nat.sub_self]; change 2 = _; repeat' (split <;> try omega)
      · rw [show n - 1 - (n - 2) = 1 by omega]; change 1 = _; repeat' (split <;> try omega)
    · simp only [hp, ↓reduceIte, show 2 + 2 * ((n - 4) / 2) = n - 3 by omega]
      rcases (by omega : i = n - 3 ∨ i = n - 2 ∨ i = n - 1) with rfl | rfl | rfl
      · rw [Nat.sub_self]; change 2 = _; repeat' (split <;> try omega)
      · rw [show n - 2 - (n - 3) = 1 by omega]; change n = _; repeat' (split <;> try omega)
      · rw [show n - 1 - (n - 3) = 2 by omega]; change 1 = _; repeat' (split <;> try omega)
private theorem familyD_getD (n i : ℕ) (hn : 9 ≤ n) (hi : i < n) : (familyD n).getD i 0 = if i = 0 then 4 else if i = 1 then 3 else if i = 2 then 6 else if i = 3 then 7 else if i = 4 then 5 else if i < n - 2 then i + 3 else if i = n - 2 then 2 else 1 := by
  unfold familyD; by_cases h5 : i < 5
  · rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl | rfl <;> rfl
  by_cases h : i < n - 2
  · rw [List.append_assoc, getD_app_right (by simp; omega), getD_app_left (by simp; omega)]; change (List.range' 8 (n - 7)).getD (i - 5) 0 = _; rw [getD_range' 8 (n - 7) (i - 5) (by omega)]; repeat' (split <;> try omega)
  · rw [getD_app_right (by simp; omega)]; have hlen : ([4, 3, 6, 7, 5] ++ List.range' 8 (n - 7)).length = n - 2 := (by simp; omega); rw [hlen]; rcases (by omega : i = n - 2 ∨ i = n - 1) with rfl | rfl
    · rw [Nat.sub_self]; change 2 = _; repeat' (split <;> try omega)
    · rw [show n - 1 - (n - 2) = 1 by omega]; change 1 = _; repeat' (split <;> try omega)
private theorem familyI_mem (n : ℕ) (hn : 2 ≤ n) : familyI n ∈ indecomposableAvoiders n := by
  refine admissible_of_spec hn (familyI n) (fun i => if i < n - 1 then i + 2 else 1) (fun i => if i < n - 2 then i + 3 else if i = n - 2 then 1 else 2) (by simp [familyI]; omega) (by split <;> omega) (fun i hi => familyI_getD n i hn hi) ?_ ?_ ?_ ?_
  · intro v hv1 hvn; by_cases hv : v = 1
    · exact ⟨n - 1, by omega, by split <;> omega⟩
    · exact ⟨v - 2, by omega, by split <;> omega⟩
  · intro i hi v hv; repeat' (split at hv <;> try omega); all_goals subst v; repeat' (split <;> try omega)
  · intro i hi; refine ⟨n - 1, n - 1, n - 1, le_rfl, le_rfl, le_rfl, le_rfl, ?_⟩; intro j hij hj hlt; repeat' (split at hlt <;> try omega)
  · intro j k hjk hk hlt; have : (k = n - 2 ∨ k = n - 1) ∧ j < n - 2 := (by repeat' (split at hlt <;> try omega)); intro i hij; repeat' (split <;> try omega)
private theorem familyJ_mem (n : ℕ) (hn : 5 ≤ n) : familyJ n ∈ indecomposableAvoiders n := by
  refine admissible_of_spec (by omega) (familyJ n) (fun i => if i = 0 then 2 else if i = 1 then 4 else if i = 2 then 3 else if i < n - 1 then i + 2 else 1) (fun i => if i = 0 then 4 else if i = 1 then 5 else if i = 2 then 3 else if i < n - 2 then i + 3 else if i = n - 2 then 1 else 2)
    (by simp [familyJ]; omega) (by repeat' (split <;> try omega))
    (fun i hi => familyJ_getD n i hn hi) ?_ ?_ ?_ ?_
  · intro v hv1 hvn; rcases (by omega : v = 1 ∨ v = 2 ∨ v = 3 ∨ v = 4 ∨ 5 ≤ v) with rfl | rfl | rfl | rfl | _
    · exact ⟨n - 1, by omega, by repeat' (split <;> try omega)⟩
    · exact ⟨0, by omega, rfl⟩
    · exact ⟨2, by omega, rfl⟩
    · exact ⟨1, by omega, rfl⟩
    · exact ⟨v - 2, by omega, by repeat' (split <;> try omega)⟩
  · intro i hi v hv; repeat' (split at hv <;> try omega); all_goals subst v; repeat' (split <;> try omega)
  · intro i hi; refine ⟨2, n - 1, n - 1, by omega, le_rfl, le_rfl, by repeat' (split <;> try omega), ?_⟩
    intro j hij hj hlt; repeat' (split at hlt <;> try omega)
  · intro j k hjk hk hlt; have hk_bnd : (k = 2 ∧ j ≤ 1) ∨ ((k = n - 2 ∨ k = n - 1) ∧ j < n - 2) := (by repeat' (split at hlt <;> try omega)); intro i hij; rcases hk_bnd with ⟨rfl, _⟩ | ⟨rfl | rfl, _⟩ <;> repeat' (split <;> try omega)
private theorem familyK_mem (n j : ℕ) (hn : 6 ≤ n) (hj : j ≤ (n - 6) / 2) : familyK n j ∈ indecomposableAvoiders n := by
  have hmid : ((List.range (j + 1)).flatMap fun r => [2 * r + 5, 2 * r + 4]).length = 2 * j + 2 := by simpa [Nat.mul_add] using flatMap_pair_length (j + 1) 5 4
  refine admissible_of_spec (by omega) (familyK n j) (fun i => if i = 0 then 2 else if i ≤ 2 * j + 2 then (if i % 2 = 1 then i + 4 else i + 2) else if i = 2 * j + 3 then 3 else if i < n - 1 then i + 2 else 1)
    (fun i => if i ≤ 2 * j + 1 then i + 5 else if i = 2 * j + 2 then 3 else if i = 2 * j + 3 then 4 else if i < n - 2 then i + 3 else if i = n - 2 then 1 else 2)
    (by unfold familyK; simp [hmid]; omega) (by repeat' (split <;> try omega))
    (fun i hi => familyK_getD n j i hn hj hi) ?_ ?_ ?_ ?_
  · intro v hv1 hvn; rcases (by omega : v = 1 ∨ v = 2 ∨ v = 3 ∨ (4 ≤ v ∧ v ≤ 2 * j + 5 ∧ v % 2 = 1) ∨ (4 ≤ v ∧ (2 * j + 6 ≤ v ∨ v % 2 = 0))) with rfl | rfl | rfl | ⟨_, _, _⟩ | ⟨_, _⟩
    · exact ⟨n - 1, by omega, by repeat' (split <;> try omega)⟩
    · exact ⟨0, by omega, rfl⟩
    · exact ⟨2 * j + 3, by omega, by repeat' (split <;> try omega)⟩
    · exact ⟨v - 4, by omega, by repeat' (split <;> try omega)⟩
    · exact ⟨v - 2, by omega, by repeat' (split <;> try omega)⟩
  · intro i hi v hv; repeat' (split at hv <;> try omega); all_goals subst v; repeat' (split <;> try omega)
  · intro i hi; by_cases hip : 1 ≤ i ∧ i ≤ 2 * j + 2 ∧ i % 2 = 1
    · refine ⟨i + 1, 2 * j + 3, n - 1, by omega, by omega, by repeat' (split <;> try omega), by repeat' (split <;> try omega), ?_⟩
      intro k hik hk hlt; repeat' (split at hlt <;> try omega)
    · refine ⟨2 * j + 3, 2 * j + 3, n - 1, le_rfl, by omega, by repeat' (split <;> try omega), le_rfl, ?_⟩
      intro k hik hk hlt; repeat' (split at hlt <;> try omega)
  · intro j' k hjk hk hlt; have hk_bnd : ((k = 2 * j + 2 ∨ k = 2 * j + 3) ∧ j' ≤ 2 * j + 1) ∨ ((k = n - 2 ∨ k = n - 1) ∧ j' < n - 2) := (by repeat' (split at hlt <;> try omega)); intro i hij; rcases hk_bnd with ⟨rfl | rfl, _⟩ | ⟨rfl | rfl, _⟩ <;> repeat' (split <;> try omega)
private theorem familyA_mem (n : ℕ) (hn : 6 ≤ n) : familyA n ∈ indecomposableAvoiders n := by
  refine admissible_of_spec (by omega) (familyA n) (fun i => if i = 0 then 4 else if i = 1 then 3 else if i < n - 2 then i + 3 else if i = n - 2 then 2 else 1)
    (fun i => if i = 0 then 6 else if i = 1 then 5 else if i < n - 4 then i + 5 else if i = n - 4 then 2 else if i = n - 3 then 1 else if i = n - 2 then 3 else 4)
    (by simp [familyA]; omega) (by repeat' (split <;> try omega))
    (fun i hi => familyA_getD n i hn hi) ?_ ?_ ?_ ?_
  · intro v hv1 hvn; rcases (by omega : v = 1 ∨ v = 2 ∨ v = 3 ∨ v = 4 ∨ 5 ≤ v) with rfl | rfl | rfl | rfl | _
    · exact ⟨n - 1, by omega, by repeat' (split <;> try omega)⟩
    · exact ⟨n - 2, by omega, by repeat' (split <;> try omega)⟩
    · exact ⟨1, by omega, rfl⟩
    · exact ⟨0, by omega, rfl⟩
    · exact ⟨v - 3, by omega, by repeat' (split <;> try omega)⟩
  · intro i hi v hv; repeat' (split at hv <;> try omega); all_goals subst v; repeat' (split <;> try omega)
  · intro i hi; refine ⟨1, n - 2, n - 1, by omega, by omega, by repeat' (split <;> try omega), by repeat' (split <;> try omega), ?_⟩
    intro j hij hj hlt; repeat' (split at hlt <;> try omega)
  · intro j k hjk hk hlt; have hk_bnd : (j = 0 ∧ k = 1) ∨ ((k = n - 4 ∨ k = n - 3 ∨ k = n - 2 ∨ k = n - 1) ∧ j < n - 4) ∨ (k = n - 3 ∧ j = n - 4) := (by repeat' (split at hlt <;> try omega)); intro i hij; rcases hk_bnd with ⟨rfl, rfl⟩ | ⟨rfl | rfl | rfl | rfl, _⟩ | ⟨rfl, rfl⟩ <;> repeat' (split <;> try omega)
private theorem familyB_odd_mem (n : ℕ) (hn : 7 ≤ n) (hp : n % 2 = 1) : familyB n ∈ indecomposableAvoiders n := by
  have hmid : ((List.range ((n - 5) / 2)).flatMap fun r => [2 * r + 7, 2 * r + 6]).length = 2 * ((n - 5) / 2) := flatMap_pair_length ((n - 5) / 2) 7 6; have hb : 3 + 2 * ((n - 5) / 2) = n - 2 := (by omega)
  refine admissible_of_spec (by omega) (familyB n) (fun i => if i < 2 then 4 - i else if i = 2 then 5 else if i < n - 2 then (if i % 2 = 1 then i + 4 else i + 2) else n - i) (fun i => if i = 0 then 7 else if i < 3 then i + 4 else if i < n - 4 then i + 5 else i + 5 - n)
    (by unfold familyB; simp [hp, hmid]; omega) (by repeat' (split <;> try omega))
    (fun i hi => by rw [familyB_getD n i hn hi]; simp only [hp, hb, ↓reduceIte]; repeat' (split <;> try omega)) ?_ ?_ ?_ ?_
  · intro v hv1 hvn
    rcases (by omega : v = 1 ∨ v = 2 ∨ v = 3 ∨ v = 4 ∨ v = 5 ∨
        (6 ≤ v ∧ v % 2 = 1) ∨ (6 ≤ v ∧ v % 2 = 0)) with
      rfl | rfl | rfl | rfl | rfl | ⟨_, _⟩ | ⟨_, _⟩
    · exact ⟨n - 1, by omega, by repeat' (split <;> try omega)⟩
    · exact ⟨n - 2, by omega, by repeat' (split <;> try omega)⟩
    · exact ⟨1, by omega, rfl⟩
    · exact ⟨0, by omega, rfl⟩
    · exact ⟨2, by omega, rfl⟩
    · exact ⟨v - 4, by omega, by repeat' (split <;> try omega)⟩
    · exact ⟨v - 2, by omega, by repeat' (split <;> try omega)⟩
  · intro i hi v hv; repeat' (split at hv <;> try omega); all_goals subst v; repeat' (split <;> try omega)
  · intro i hi; by_cases hi0 : i = 0
    · subst i; refine ⟨1, n - 2, n - 1, by omega, by omega, by repeat' (split <;> try omega), by repeat' (split <;> try omega), ?_⟩
      intro j hij hj hlt; repeat' (split at hlt <;> try omega)
    by_cases hip : 3 ≤ i ∧ i < n - 2 ∧ i % 2 = 1
    · refine ⟨i + 1, n - 2, n - 1, by omega, by omega, by repeat' (split <;> try omega), by repeat' (split <;> try omega), ?_⟩
      intro j hij hj hlt; repeat' (split at hlt <;> try omega)
    · refine ⟨n - 2, n - 2, n - 1, le_rfl, by omega, by repeat' (split <;> try omega), le_rfl, ?_⟩
      intro j hij hj hlt; repeat' (split at hlt <;> try omega)
  · intro j k hjk hk hlt; have hk_bnd : (j = 0 ∧ (k = 1 ∨ k = 2)) ∨ (n - 4 ≤ k ∧ j < n - 4) := (by repeat' (split at hlt <;> try omega)); intro i hij; rcases hk_bnd with ⟨rfl, _⟩ | ⟨_, _⟩ <;> repeat' (split <;> try omega)
private def bEvenEntry (n i : ℕ) : ℕ := if i < 2 then 4 - i else if i = 2 then 5 else if i < n - 3 then (if i % 2 = 1 then i + 4 else i + 2) else if i = n - 3 then 2 else if i = n - 2 then n else 1
private def bEvenSq (n i : ℕ) : ℕ := if i = 0 then 7 else if i < 3 then i + 4 else if i < n - 4 then i + 5 else if i < n - 2 then i + 6 - n else if i = n - 2 then 1 else 4
private theorem bEven_sq_step (n : ℕ) (hn : 7 ≤ n) (hp : ¬ n % 2 = 1) : ∀ i < n, ∀ v, bEvenEntry n i = v → bEvenEntry n (v - 1) = bEvenSq n i := by intro i hi v hv; unfold bEvenEntry at hv; unfold bEvenEntry bEvenSq; repeat' (split at hv <;> try omega); all_goals subst v; repeat' (split <;> try omega)
private theorem bEven_dec3 (n : ℕ) (hn : 7 ≤ n) (hp : ¬ n % 2 = 1) : ∀ i < n, ∃ ja jc jd, ja ≤ jc ∧ jc ≤ jd ∧ bEvenEntry n jd ≤ bEvenEntry n jc ∧ bEvenEntry n jc ≤ bEvenEntry n ja ∧ ∀ j, i < j → j < n → bEvenEntry n j < bEvenEntry n i → j = ja ∨ j = jc ∨ j = jd := by
  have he3 : bEvenEntry n (n - 3) = 2 := (by unfold bEvenEntry; repeat' (split <;> try omega)); have he1 : bEvenEntry n (n - 1) = 1 := (by unfold bEvenEntry; repeat' (split <;> try omega)); intro i hi; by_cases hi0 : i = 0
  · subst i; refine ⟨1, n - 3, n - 1, by omega, by omega, by rw [he3, he1]; omega, by rw [he3]; change 2 ≤ 3; omega, ?_⟩
    intro j hij hj hlt; change bEvenEntry n j < 4 at hlt; unfold bEvenEntry at hlt; repeat' (split at hlt <;> try omega)
  by_cases hip : 3 ≤ i ∧ i < n - 3 ∧ i % 2 = 1
  · have hei : bEvenEntry n i = i + 4 := (by unfold bEvenEntry; repeat' (split <;> try omega)); have hei1 : bEvenEntry n (i + 1) = i + 3 := (by unfold bEvenEntry; repeat' (split <;> try omega)); refine ⟨i + 1, n - 3, n - 1, by omega, by omega, by rw [he3, he1]; omega, by rw [he3, hei1]; omega, ?_⟩
    intro j hij hj hlt; rw [hei] at hlt; unfold bEvenEntry at hlt; repeat' (split at hlt <;> try omega)
  · refine ⟨n - 3, n - 3, n - 1, le_rfl, by omega, by rw [he3, he1]; omega, le_rfl, ?_⟩
    obtain ⟨ei, rfl_ei⟩ : ∃ ei, ei = bEvenEntry n i := ⟨_, rfl⟩; have hei : (i < n - 3 ∧ ei ≤ i + 3) ∨ (i = n - 3 ∧ ei = 2) ∨ n - 2 ≤ i := (by subst rfl_ei; unfold bEvenEntry; repeat' (split <;> try omega))
    intro j hij hj hlt; rw [← rfl_ei] at hlt; clear rfl_ei; unfold bEvenEntry at hlt; repeat' (split at hlt <;> try omega)
private theorem familyB_even_mem (n : ℕ) (hn : 7 ≤ n) (hp : ¬ n % 2 = 1) : familyB n ∈ indecomposableAvoiders n := by
  have hmid : ((List.range ((n - 5) / 2)).flatMap fun r => [2 * r + 7, 2 * r + 6]).length = 2 * ((n - 5) / 2) := flatMap_pair_length ((n - 5) / 2) 7 6; have hb : 3 + 2 * ((n - 5) / 2) = n - 3 := (by omega); have he3 : bEvenEntry n (n - 3) = 2 := (by unfold bEvenEntry; repeat' (split <;> try omega))
  have he1 : bEvenEntry n (n - 1) = 1 := by unfold bEvenEntry; repeat' (split <;> try omega)
  refine admissible_of_spec (by omega) (familyB n) (bEvenEntry n) (bEvenSq n) (by unfold familyB; simp [hp, hmid]; omega) he1
    (fun i hi => by unfold bEvenEntry; rw [familyB_getD n i hn hi]; simp only [hp, hb, ↓reduceIte]; repeat' (split <;> try omega))
    ?_ (bEven_sq_step n hn hp) (bEven_dec3 n hn hp) ?_
  · intro v hv1 hvn
    rcases (by omega : v = 1 ∨ v = 2 ∨ v = 3 ∨ v = 4 ∨ v = 5 ∨ v = n ∨
        (6 ≤ v ∧ v < n ∧ v % 2 = 1) ∨ (6 ≤ v ∧ v < n ∧ v % 2 = 0)) with
      rfl | rfl | rfl | rfl | rfl | hvn_eq | ⟨_, _, _⟩ | ⟨_, _, _⟩
    · exact ⟨n - 1, by omega, he1⟩
    · exact ⟨n - 3, by omega, he3⟩
    · exact ⟨1, by omega, rfl⟩
    · exact ⟨0, by omega, rfl⟩
    · exact ⟨2, by omega, rfl⟩
    · refine ⟨n - 2, by omega, ?_⟩; subst v; unfold bEvenEntry; repeat' (split <;> try omega)
    · exact ⟨v - 4, by omega, by unfold bEvenEntry; repeat' (split <;> try omega)⟩
    · exact ⟨v - 2, by omega, by unfold bEvenEntry; repeat' (split <;> try omega)⟩
  · intro j k hjk hk hlt; unfold bEvenSq at hlt ⊢; have hk_bnd : (j = 0 ∧ (k = 1 ∨ k = 2)) ∨ (n - 4 ≤ k ∧ j < n - 4) ∨ k = n - 2 := (by repeat' (split at hlt <;> try omega)); intro i hij; rcases hk_bnd with ⟨rfl, _⟩ | ⟨_, _⟩ | rfl <;> repeat' (split <;> try omega)
private theorem familyB_mem (n : ℕ) (hn : 7 ≤ n) : familyB n ∈ indecomposableAvoiders n := by
  by_cases hp : n % 2 = 1
  · exact familyB_odd_mem n hn hp
  · exact familyB_even_mem n hn hp
private theorem familyC_even_mem (n : ℕ) (hn : 4 ≤ n) (hp : n % 2 = 0) : familyC n ∈ indecomposableAvoiders n := by
  have hmid : ((List.range ((n - 4) / 2)).flatMap fun r => [2 * r + 6, 2 * r + 5]).length = 2 * ((n - 4) / 2) := flatMap_pair_length ((n - 4) / 2) 6 5; have hb : 2 + 2 * ((n - 4) / 2) = n - 2 := (by omega)
  refine admissible_of_spec (by omega) (familyC n) (fun i => if i < 2 then 4 - i else if i < n - 2 then (if i % 2 = 0 then i + 4 else i + 2) else n - i) (fun i => if i < n - 4 then i + 5 else i + 5 - n) (by unfold familyC; simp [hp, hmid]; omega) (by repeat' (split <;> try omega))
    (fun i hi => by rw [familyC_getD n i hn hi]; simp only [hp, hb, ↓reduceIte]; repeat' (split <;> try omega)) ?_ ?_ ?_ ?_
  · intro v hv1 hvn
    rcases (by omega : v = 1 ∨ v = 2 ∨ v = 3 ∨ v = 4 ∨
        (5 ≤ v ∧ v % 2 = 0) ∨ (5 ≤ v ∧ v % 2 = 1)) with
      rfl | rfl | rfl | rfl | ⟨_, _⟩ | ⟨_, _⟩
    · exact ⟨n - 1, by omega, by repeat' (split <;> try omega)⟩
    · exact ⟨n - 2, by omega, by repeat' (split <;> try omega)⟩
    · exact ⟨1, by omega, rfl⟩
    · exact ⟨0, by omega, rfl⟩
    · exact ⟨v - 4, by omega, by repeat' (split <;> try omega)⟩
    · exact ⟨v - 2, by omega, by repeat' (split <;> try omega)⟩
  · intro i hi v hv; repeat' (split at hv <;> try omega); all_goals subst v; repeat' (split <;> try omega)
  · intro i hi; by_cases hi0 : i = 0
    · subst i; refine ⟨1, n - 2, n - 1, by omega, by omega, by repeat' (split <;> try omega), by repeat' (split <;> try omega), ?_⟩
      intro j hij hj hlt; repeat' (split at hlt <;> try omega)
    by_cases hip : 2 ≤ i ∧ i < n - 2 ∧ i % 2 = 0
    · refine ⟨i + 1, n - 2, n - 1, by omega, by omega, by repeat' (split <;> try omega), by repeat' (split <;> try omega), ?_⟩
      intro j hij hj hlt; repeat' (split at hlt <;> try omega)
    · refine ⟨n - 2, n - 2, n - 1, le_rfl, by omega, by repeat' (split <;> try omega), le_rfl, ?_⟩
      intro j hij hj hlt; repeat' (split at hlt <;> try omega)
  · intro j k hjk hk hlt; have hk_bnd : n - 4 ≤ k ∧ j < n - 4 := (by repeat' (split at hlt <;> try omega)); intro i hij; repeat' (split <;> try omega)
private theorem familyC_odd_mem (n : ℕ) (hn : 4 ≤ n) (hp : ¬ n % 2 = 0) : familyC n ∈ indecomposableAvoiders n := by
  have hmid : ((List.range ((n - 4) / 2)).flatMap fun r => [2 * r + 6, 2 * r + 5]).length = 2 * ((n - 4) / 2) := flatMap_pair_length ((n - 4) / 2) 6 5; have hb : 2 + 2 * ((n - 4) / 2) = n - 3 := (by omega)
  refine admissible_of_spec (by omega) (familyC n) (fun i => if i < 2 then 4 - i else if i < n - 3 then (if i % 2 = 0 then i + 4 else i + 2) else if i = n - 3 then 2 else if i = n - 2 then n else 1) (fun i => if i < n - 4 then i + 5 else if i < n - 2 then i + 6 - n else if i = n - 2 then 1 else 4)
    (by unfold familyC; simp [hp, hmid]; omega) (by repeat' (split <;> try omega))
    (fun i hi => by rw [familyC_getD n i hn hi]; simp only [hp, hb, ↓reduceIte]; repeat' (split <;> try omega)) ?_ ?_ ?_ ?_
  · intro v hv1 hvn
    rcases (by omega : v = 1 ∨ v = 2 ∨ v = 3 ∨ v = 4 ∨ v = n ∨
        (5 ≤ v ∧ v < n ∧ v % 2 = 0) ∨ (5 ≤ v ∧ v < n ∧ v % 2 = 1)) with
      rfl | rfl | rfl | rfl | hvn_eq | ⟨_, _, _⟩ | ⟨_, _, _⟩
    · exact ⟨n - 1, by omega, by repeat' (split <;> try omega)⟩
    · exact ⟨n - 3, by omega, by repeat' (split <;> try omega)⟩
    · exact ⟨1, by omega, rfl⟩
    · exact ⟨0, by omega, rfl⟩
    · refine ⟨n - 2, by omega, ?_⟩; subst v; repeat' (split <;> try omega)
    · exact ⟨v - 4, by omega, by repeat' (split <;> try omega)⟩
    · exact ⟨v - 2, by omega, by repeat' (split <;> try omega)⟩
  · intro i hi v hv; repeat' (split at hv <;> try omega); all_goals subst v; repeat' (split <;> try omega)
  · intro i hi; by_cases hi0 : i = 0
    · subst i; refine ⟨1, n - 3, n - 1, by omega, by omega, by repeat' (split <;> try omega), by repeat' (split <;> try omega), ?_⟩
      intro j hij hj hlt; repeat' (split at hlt <;> try omega)
    by_cases hip : 2 ≤ i ∧ i < n - 3 ∧ i % 2 = 0
    · refine ⟨i + 1, n - 3, n - 1, by omega, by omega, by repeat' (split <;> try omega), by repeat' (split <;> try omega), ?_⟩
      intro j hij hj hlt; repeat' (split at hlt <;> try omega)
    · refine ⟨n - 3, n - 3, n - 1, le_rfl, by omega, by repeat' (split <;> try omega), le_rfl, ?_⟩
      intro j hij hj hlt; repeat' (split at hlt <;> try omega)
  · intro j k hjk hk hlt; have hk_bnd : (n - 4 ≤ k ∧ j < n - 4) ∨ k = n - 2 := (by repeat' (split at hlt <;> try omega)); intro i hij; rcases hk_bnd with ⟨_, _⟩ | rfl <;> repeat' (split <;> try omega)
private theorem familyC_mem (n : ℕ) (hn : 4 ≤ n) : familyC n ∈ indecomposableAvoiders n := by
  by_cases hp : n % 2 = 0
  · exact familyC_even_mem n hn hp
  · exact familyC_odd_mem n hn hp
private theorem familyD_mem (n : ℕ) (hn : 9 ≤ n) : familyD n ∈ indecomposableAvoiders n := by
  refine admissible_of_spec (by omega) (familyD n) (fun i => if i < 2 then 4 - i else if i < 4 then i + 4 else if i = 4 then 5 else if i < n - 2 then i + 3 else n - i)
    (fun i => if i < 2 then 7 - i else if i < 4 then i + 6 else if i = 4 then 5 else if i < n - 4 then i + 5 else if i < n - 2 then n - 2 - i else i + 5 - n)
    (by simp [familyD]; omega) (by repeat' (split <;> try omega))
    (fun i hi => by rw [familyD_getD n i hn hi]; repeat' (split <;> try omega)) ?_ ?_ ?_ ?_
  · intro v hv1 hvn
    rcases (by omega : v = 1 ∨ v = 2 ∨ v = 3 ∨ v = 4 ∨ v = 5 ∨ v = 6 ∨ v = 7 ∨ 8 ≤ v) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | _
    · exact ⟨n - 1, by omega, by repeat' (split <;> try omega)⟩
    · exact ⟨n - 2, by omega, by repeat' (split <;> try omega)⟩
    · exact ⟨1, by omega, rfl⟩
    · exact ⟨0, by omega, rfl⟩
    · exact ⟨4, by omega, rfl⟩
    · exact ⟨2, by omega, rfl⟩
    · exact ⟨3, by omega, rfl⟩
    · exact ⟨v - 3, by omega, by repeat' (split <;> try omega)⟩
  · intro i hi v hv; repeat' (split at hv <;> try omega); all_goals subst v; repeat' (split <;> try omega)
  · intro i hi; by_cases hi0 : i = 0
    · subst i; refine ⟨1, n - 2, n - 1, by omega, by omega, by repeat' (split <;> try omega), by repeat' (split <;> try omega), ?_⟩
      intro j hij hj hlt; repeat' (split at hlt <;> try omega)
    · refine ⟨4, n - 2, n - 1, by omega, by omega, by repeat' (split <;> try omega), by repeat' (split <;> try omega), ?_⟩
      intro j hij hj hlt; repeat' (split at hlt <;> try omega)
  · intro j k hjk hk hlt; have hk_bnd : (j = 0 ∧ k = 1) ∨ (k = 4 ∧ j ≤ 3) ∨ (n - 4 ≤ k ∧ j < n - 4) ∨ k = n - 3 := (by repeat' (split at hlt <;> try omega)); intro i hij; rcases hk_bnd with ⟨rfl, rfl⟩ | ⟨rfl, _⟩ | ⟨_, _⟩ | rfl <;> repeat' (split <;> try omega)
private theorem ne_of_getD_ne {l₁ l₂ : List ℕ} (i : ℕ) (h : l₁.getD i 0 ≠ l₂.getD i 0) : l₁ ≠ l₂ := fun heq => h (heq ▸ rfl)
/-- Admissibility in `indecomposableAvoiders n`, parameter injectivity of `familyK`, and pairwise distinctness of all seven families on their valid domains. -/
theorem seven_families_admissible_and_distinct : (∀ n : ℕ, 2 ≤ n → familyI n ∈ indecomposableAvoiders n) ∧ (∀ n : ℕ, 5 ≤ n → familyJ n ∈ indecomposableAvoiders n) ∧ (∀ n j : ℕ, 6 ≤ n → j ≤ (n - 6) / 2 → familyK n j ∈ indecomposableAvoiders n) ∧
    (∀ n : ℕ, 6 ≤ n → familyA n ∈ indecomposableAvoiders n) ∧ (∀ n : ℕ, 7 ≤ n → familyB n ∈ indecomposableAvoiders n) ∧ (∀ n : ℕ, 4 ≤ n → familyC n ∈ indecomposableAvoiders n) ∧ (∀ n : ℕ, 9 ≤ n → familyD n ∈ indecomposableAvoiders n) ∧
    (∀ n j₁ j₂ : ℕ, 6 ≤ n → j₁ ≤ (n - 6) / 2 → j₂ ≤ (n - 6) / 2 → familyK n j₁ = familyK n j₂ → j₁ = j₂) ∧ (∀ n : ℕ, 5 ≤ n → familyI n ≠ familyJ n) ∧ (∀ n j : ℕ, 6 ≤ n → j ≤ (n - 6) / 2 → familyI n ≠ familyK n j) ∧
    (∀ n : ℕ, 6 ≤ n → familyI n ≠ familyA n) ∧ (∀ n : ℕ, 7 ≤ n → familyI n ≠ familyB n) ∧ (∀ n : ℕ, 4 ≤ n → familyI n ≠ familyC n) ∧ (∀ n : ℕ, 9 ≤ n → familyI n ≠ familyD n) ∧
    (∀ n j : ℕ, 6 ≤ n → j ≤ (n - 6) / 2 → familyJ n ≠ familyK n j) ∧ (∀ n : ℕ, 6 ≤ n → familyJ n ≠ familyA n) ∧ (∀ n : ℕ, 7 ≤ n → familyJ n ≠ familyB n) ∧ (∀ n : ℕ, 5 ≤ n → familyJ n ≠ familyC n) ∧ (∀ n : ℕ, 9 ≤ n → familyJ n ≠ familyD n) ∧ (∀ n j : ℕ, 6 ≤ n → j ≤ (n - 6) / 2 → familyK n j ≠ familyA n) ∧
    (∀ n j : ℕ, 7 ≤ n → j ≤ (n - 6) / 2 → familyK n j ≠ familyB n) ∧ (∀ n j : ℕ, 6 ≤ n → j ≤ (n - 6) / 2 → familyK n j ≠ familyC n) ∧ (∀ n j : ℕ, 9 ≤ n → j ≤ (n - 6) / 2 → familyK n j ≠ familyD n) ∧ (∀ n : ℕ, 7 ≤ n → familyA n ≠ familyB n) ∧ (∀ n : ℕ, 6 ≤ n → familyA n ≠ familyC n) ∧
    (∀ n : ℕ, 9 ≤ n → familyA n ≠ familyD n) ∧ (∀ n : ℕ, 7 ≤ n → familyB n ≠ familyC n) ∧
    (∀ n : ℕ, 9 ≤ n → familyB n ≠ familyD n) ∧ (∀ n : ℕ, 9 ≤ n → familyC n ≠ familyD n) := by
  refine ⟨familyI_mem, familyJ_mem, familyK_mem, familyA_mem, familyB_mem, familyC_mem, familyD_mem, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun _ _ => ne_of_getD_ne 0 (by change 2 ≠ 4; decide), fun _ _ => ne_of_getD_ne 0 (by change 2 ≠ 4; decide),
    fun _ _ => ne_of_getD_ne 0 (by change 2 ≠ 4; decide), fun _ _ => ne_of_getD_ne 0 (by change 2 ≠ 4; decide), fun _ _ _ _ => ne_of_getD_ne 0 (by change 2 ≠ 4; decide), fun _ _ _ _ => ne_of_getD_ne 0 (by change 2 ≠ 4; decide),
    fun _ _ _ _ => ne_of_getD_ne 0 (by change 2 ≠ 4; decide), fun _ _ _ _ => ne_of_getD_ne 0 (by change 2 ≠ 4; decide), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n j₁ j₂ hn hj₁ hj₂ heq; by_contra hne; rcases lt_trichotomy j₁ j₂ with hlt | h | hgt
    · have h1 := familyK_getD n j₁ (2 * j₁ + 3) hn hj₁ (by omega); have h2 := familyK_getD n j₂ (2 * j₁ + 3) hn hj₂ (by omega); rw [heq] at h1; repeat' (split at h1 <;> try omega); repeat' (split at h2 <;> try omega)
    · exact hne h
    · have h1 := familyK_getD n j₁ (2 * j₂ + 3) hn hj₁ (by omega); have h2 := familyK_getD n j₂ (2 * j₂ + 3) hn hj₂ (by omega); rw [heq] at h1; repeat' (split at h1 <;> try omega); repeat' (split at h2 <;> try omega)
  · intro n hn; apply ne_of_getD_ne 1; rw [familyI_getD n 1 (by omega) (by omega)]; change _ ≠ 4; split <;> omega
  · intro n j hn hj; apply ne_of_getD_ne 1; rw [familyI_getD n 1 (by omega) (by omega), familyK_getD n j 1 hn hj (by omega)]; repeat' (split <;> try omega)
  · intro n hn; apply ne_of_getD_ne 0; rw [familyI_getD n 0 (by omega) (by omega)]; change _ ≠ 4; split <;> omega
  · intro n hn; apply ne_of_getD_ne 0; rw [familyI_getD n 0 (by omega) (by omega)]; change _ ≠ 4; split <;> omega
  · intro n hn; apply ne_of_getD_ne 0; rw [familyI_getD n 0 (by omega) (by omega)]; change _ ≠ 4; split <;> omega
  · intro n hn; apply ne_of_getD_ne 0; rw [familyI_getD n 0 (by omega) (by omega)]; change _ ≠ 4; split <;> omega
  · intro n j hn hj; apply ne_of_getD_ne 1; rw [familyK_getD n j 1 hn hj (by omega)]; change 4 ≠ _; repeat' (split <;> try omega)
  · intro n hn; apply ne_of_getD_ne 3; rw [familyA_getD n 3 (by omega) (by omega), familyB_getD n 3 hn (by omega)]; repeat' (split <;> try omega)
  · intro n hn; apply ne_of_getD_ne 2; rw [familyA_getD n 2 hn (by omega), familyC_getD n 2 (by omega) (by omega)]; repeat' (split <;> try omega)
  · intro n hn; apply ne_of_getD_ne 2; rw [familyA_getD n 2 (by omega) (by omega)]; change _ ≠ 6; repeat' (split <;> try omega)
  · intro n hn; apply ne_of_getD_ne 2; rw [familyC_getD n 2 (by omega) (by omega)]; change 5 ≠ _; repeat' (split <;> try omega)
  · exact fun _ _ => ne_of_getD_ne 2 (by change 5 ≠ 6; decide)
  · intro n hn; apply ne_of_getD_ne 3; rw [familyC_getD n 3 (by omega) (by omega)]; change _ ≠ 7; repeat' (split <;> try omega)
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
private theorem strictMono_skip1_eq {a b x v₀ : ℕ} {f : ℕ → ℕ} (hx : a ≤ x ∧ x < b) (hbnd : ∀ i, a ≤ i → i < b → i ≠ x → v₀ ≤ f i ∧ f i < v₀ + (b - 1 - a)) (hmono : ∀ i j, a ≤ i → i < j → j < b → i ≠ x → j ≠ x → f i < f j) : (∀ i, a ≤ i → i < x → f i = v₀ + (i - a)) ∧
      (∀ i, x < i → i < b → f i = v₀ + (i - 1 - a)) := by
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
private theorem strictMono_skip2_eq {a b u w v₀ : ℕ} {f : ℕ → ℕ} (huw : a ≤ u ∧ u < w ∧ w < b) (hbnd : ∀ i, a ≤ i → i < b → i ≠ u → i ≠ w → v₀ ≤ f i ∧ f i < v₀ + (b - 2 - a)) (hmono : ∀ i j, a ≤ i → i < j → j < b → i ≠ u → i ≠ w → j ≠ u → j ≠ w → f i < f j) :
    (∀ i, a ≤ i → i < u → f i = v₀ + (i - a)) ∧ (∀ i, u < i → i < w → f i = v₀ + (i - 1 - a)) ∧
      (∀ i, w < i → i < b → f i = v₀ + (i - 2 - a)) := by
  let g : ℕ → ℕ := fun i => if i < u then f i else if i + 1 < w then f (i + 1) else f (i + 2)
  have hg := strictMono_Ico_eq (a := a) (b := b - 2) (v₀ := v₀) (f := g)
    (fun i hai hib => by dsimp [g]; by_cases c1 : i < u <;> by_cases c2 : i + 1 < w <;> simp only [c1, c2, ↓reduceIte] <;> exact hbnd _ (by omega) (by omega) (by omega) (by omega))
    (fun i j hai hij hjb => by
      dsimp [g]; by_cases c1 : i < u <;> by_cases c2 : i + 1 < w <;> by_cases d1 : j < u <;> by_cases d2 : j + 1 < w <;> simp only [c1, c2, d1, d2, ↓reduceIte]
      all_goals first
        | omega
        | exact hmono _ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))
  refine ⟨fun i hai hiu => ?_, fun i hui hiw => ?_, fun i hwi hib => ?_⟩
  · have h := hg i hai (by omega); dsimp [g] at h; simpa [hiu] using h
  · have h := hg (i - 1) (by omega) (by omega); dsimp [g] at h; have c1 : ¬ i - 1 < u := (by omega); rw [show i - 1 + 1 = i by omega] at h; simpa [c1, hiw] using h
  · have h := hg (i - 2) (by omega) (by omega); dsimp [g] at h; have c1 : ¬ i - 2 < u := (by omega); have c2 : ¬ i - 2 + 1 < w := (by omega); simp only [c1, c2, ↓reduceIte, show i - 2 + 2 = i by omega] at h; exact h
private theorem left_bound_of_avoids_312 {n : ℕ} {p : List ℕ} (hperm : p.Perm (List.range' 1 n)) (hav312 : ¬ NonnestingDefs.Occurs [3, 1, 2] p) (hend : p.getD (n - 1) 0 = 1) {idx later : ℕ} (h1 : idx < later) (h2 : later < n) (hsmall : 2 ≤ p.getD idx 0)
    (hlt : p.getD idx 0 < p.getD later 0) : idx + 3 ≤ p.getD later 0 := by
  have hinj : Set.InjOn (fun i => p.getD i 0) (Finset.range idx) := fun x hx y hy hxy => (by rw [Finset.mem_coe, Finset.mem_range] at hx hy; exact perm_getD_inj hperm (by omega) (by omega) hxy)
  have hsub : (Finset.range idx).image (fun i => p.getD i 0) ⊆
      (Finset.Icc 2 (p.getD later 0 - 1)).erase (p.getD idx 0) := by
    intro v hv; obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hv; rw [Finset.mem_range] at hi; have hb := perm_getD_bounds hperm (by omega : i < n); have hne1 := ne_val_of_getD hperm (by omega) (by omega) (by omega : i ≠ n - 1) hend; have hnes := ne_val_of_getD hperm (by omega) (by omega) (by omega : i ≠ idx) rfl
    have hnev := ne_val_of_getD hperm (by omega) h2 (by omega : i ≠ later) rfl; have hlev : p.getD i 0 ≤ p.getD later 0 := (by by_contra hgt; exact hav312 ((occurs_312_iff p).mpr ⟨i, idx, later, hi, h1, by simpa [hperm.length_eq] using h2, hlt, by omega⟩))
    rw [Finset.mem_erase, Finset.mem_Icc]; exact ⟨hnes, by omega, by omega⟩
  have hcard1 := Finset.card_le_card hsub; rw [Finset.card_image_of_injOn hinj, Finset.card_range, Finset.card_erase_of_mem (Finset.mem_Icc.mpr ⟨hsmall, by omega⟩), Nat.card_Icc] at hcard1; omega
private theorem list_eq_of_getD {n : ℕ} {p q : List ℕ} (hp : p.length = n) (hq : q.length = n) (h : ∀ i < n, p.getD i 0 = q.getD i 0) : p = q := by apply List.ext_getElem (hp.trans hq.symm); intro i hi₁ hi₂; have h1 := h i (by omega); rwa [List.getD_eq_getElem p 0 hi₁, List.getD_eq_getElem q 0 hi₂] at h1
private theorem first_entry_two_g5 {n : ℕ} (hn : 4 ≤ n) {p : List ℕ} (hp : p ∈ indecomposableAvoiders n) (hm : p.getD 0 0 = 2) (hg5 : p.getD 1 0 = 5) : 6 ≤ n ∧ ∃ j ≤ (n - 6) / 2, p = familyK n j := by
  rcases hp with ⟨hpne, ⟨hperm, hav312, hav54321, hav132⟩, hind⟩; have hlen : p.length = n := (by simpa using hperm.length_eq); have hsq := square_perm_and_getD hperm; have hqlen : (square p).length = n := (by simpa using hsq.1.length_eq)
  have hsh := indecomposable_shape_and_prefix_iff.2.2.2.2 n (by omega) p ⟨hpne, ⟨hperm, hav312, hav54321, hav132⟩, hind⟩; have hend : p.getD (n - 1) 0 = 1 := hsh.1.1; have hipn : p.idxOf n = n - 2 := (by have := hsh.2.2.1.2.2.2.2.2 hm; omega)
  have hpn2 : p.getD (n - 2) 0 = n := (by have hs := (perm_idxOf_spec hperm n (by omega) le_rfl).2; rwa [hipn] at hs); have hqn2 : (square p).getD (n - 2) 0 = 1 := (by have h1 := hsh.2.2.1.1; rwa [hipn, Nat.add_sub_cancel] at h1); have hqn1 : (square p).getD (n - 1) 0 = 2 := hsh.2.2.1.2.1.trans hm
  have hqbnd : ∀ i < n - 2, 3 ≤ (square p).getD i 0 ∧ (square p).getD i 0 ≤ n := fun i hi => by
    have := perm_getD_bounds hsq.1 (by omega : i < n); have := ne_val_of_getD hsq.1 (by omega) (by omega) (by omega : i ≠ n - 2) hqn2; have := ne_val_of_getD hsq.1 (by omega) (by omega) (by omega : i ≠ n - 1) hqn1; omega
  have hpbnd : ∀ i, 1 ≤ i → i < n - 2 → 3 ≤ p.getD i 0 ∧ p.getD i 0 ≤ n - 1 := fun i hi1 hi2 => by
    have := perm_getD_bounds hperm (by omega : i < n); have := ne_val_of_getD hperm (by omega) (by omega) (by omega : i ≠ 0) hm; have := ne_val_of_getD hperm (by omega) (by omega) (by omega : i ≠ n - 2) hpn2; have := ne_val_of_getD hperm (by omega) (by omega) (by omega : i ≠ n - 1) hend; omega
  have hg_bnd : 3 ≤ p.getD 1 0 ∧ p.getD 1 0 ≤ n - 1 := hpbnd 1 le_rfl (by omega); have hq0 : (square p).getD 0 0 = 5 := (by rw [hsq.2 0 (by omega), hm]; exact hg5)
  have hL : ∀ i j, 1 ≤ i → i < j → j < n - 2 → 5 < (square p).getD i 0 →
      5 < (square p).getD j 0 → (square p).getD i 0 < (square p).getD j 0 := by
    intro i j hi1 hij hj2 hgi hgj; have hne : (square p).getD i 0 ≠ (square p).getD j 0 := fun heq => (by have := perm_getD_inj hsq.1 (by omega) (by omega) heq; omega); by_contra hnot; exact hav132 ((occurs_132_iff (square p)).mpr ⟨0, i, j, by omega, hij, by omega, by rwa [hq0], by omega⟩)
  refine ⟨by omega, ?_⟩; let ia := p.idxOf 4; let ib := p.idxOf 3; let ix := (square p).idxOf 4
  let iy := (square p).idxOf 3; have hsa : ia < n ∧ p.getD ia 0 = 4 := perm_idxOf_spec hperm 4 (by omega) (by omega); have hsb : ib < n ∧ p.getD ib 0 = 3 := perm_idxOf_spec hperm 3 (by omega) (by omega); have hsx : ix < n ∧ (square p).getD ix 0 = 4 := perm_idxOf_spec hsq.1 4 (by omega) (by omega)
  have hsy : iy < n ∧ (square p).getD iy 0 = 3 := perm_idxOf_spec hsq.1 3 (by omega) (by omega)
  have hia_bnd : 2 ≤ ia ∧ ia ≤ n - 3 := by
    have := idxOf_ne_of_getD hperm 4 0 (by omega) (by omega) (by omega); have := idxOf_ne_of_getD hperm 4 1 (by omega) (by omega) (by omega); have := idxOf_ne_of_getD hperm 4 (n - 2) (by omega) (by omega) (by omega); have := idxOf_ne_of_getD hperm 4 (n - 1) (by omega) (by omega) (by omega); omega
  have hib_bnd : 2 ≤ ib ∧ ib ≤ n - 3 := by
    have := idxOf_ne_of_getD hperm 3 0 (by omega) (by omega) (by omega); have := idxOf_ne_of_getD hperm 3 1 (by omega) (by omega) (by omega); have := idxOf_ne_of_getD hperm 3 (n - 2) (by omega) (by omega) (by omega); have := idxOf_ne_of_getD hperm 3 (n - 1) (by omega) (by omega) (by omega); omega
  have hia_lt_ib : ia < ib := (by have hne : ia ≠ ib := fun he => (by have h := hsa.2; rw [he, hsb.2] at h; omega); by_contra hnot; exact hav312 ((occurs_312_iff p).mpr ⟨1, ib, ia, by omega, by omega, by omega, by omega, by omega⟩))
  have hix_bnd : 1 ≤ ix ∧ ix ≤ n - 3 := (by have := idxOf_ne_of_getD hsq.1 4 0 (by omega) (by omega) (by rw [hq0]; decide); have := idxOf_ne_of_getD hsq.1 4 (n - 2) (by omega) (by omega) (by omega); have := idxOf_ne_of_getD hsq.1 4 (n - 1) (by omega) (by omega) (by omega); omega)
  have hiy_bnd : 1 ≤ iy ∧ iy ≤ n - 3 := (by have := idxOf_ne_of_getD hsq.1 3 0 (by omega) (by omega) (by rw [hq0]; decide); have := idxOf_ne_of_getD hsq.1 3 (n - 2) (by omega) (by omega) (by omega); have := idxOf_ne_of_getD hsq.1 3 (n - 1) (by omega) (by omega) (by omega); omega)
  have hxy_ne : ix ≠ iy := fun he => (by have h := hsx.2; rw [he, hsy.2] at h; omega); have hp_ix : p.getD ix 0 = ia + 1 := getD_of_sq_eq hperm ix 4 hsx.1 (by omega) (by omega) hsx.2
  have hp_iy : p.getD iy 0 = ib + 1 := getD_of_sq_eq hperm iy 3 hsy.1 (by omega) (by omega) hsy.2; obtain ⟨u, hu_def⟩ : ∃ u, u = min ix iy := ⟨_, rfl⟩; obtain ⟨w, hw_def⟩ : ∃ w, w = max ix iy := ⟨_, rfl⟩; have huw_or : (ix < iy ∧ u = ix ∧ w = iy) ∨ (iy < ix ∧ u = iy ∧ w = ix) := (by omega)
  clear hu_def hw_def; have huw : 1 ≤ u ∧ u < w ∧ w < n - 2 := ⟨by omega, by omega, by omega⟩
  have hq_skip := strictMono_skip2_eq (a := 1) (b := n - 2) (u := u) (w := w) (v₀ := 6) (f := fun i => (square p).getD i 0) huw
    (fun i hi1 hi2 hnu hnw => by have := hqbnd i hi2; have := ne_val_of_getD hsq.1 (by omega) (by omega) (by omega : i ≠ 0) hq0; have := ne_val_of_getD hsq.1 (by omega) hsx.1 (by omega : i ≠ ix) hsx.2; have := ne_val_of_getD hsq.1 (by omega) hsy.1 (by omega : i ≠ iy) hsy.2; omega)
    (fun i j hi1 hij hj2 hniu hniw hnju hnjw => by
      have := hqbnd i (by omega); have := hqbnd j hj2; have := ne_val_of_getD hsq.1 (by omega) (by omega) (by omega : i ≠ 0) hq0; have := ne_val_of_getD hsq.1 (by omega) (by omega) (by omega : j ≠ 0) hq0; have := ne_val_of_getD hsq.1 (by omega) hsx.1 (by omega : i ≠ ix) hsx.2
      have := ne_val_of_getD hsq.1 (by omega) hsx.1 (by omega : j ≠ ix) hsx.2; have := ne_val_of_getD hsq.1 (by omega) hsy.1 (by omega : i ≠ iy) hsy.2; have := ne_val_of_getD hsq.1 (by omega) hsy.1 (by omega : j ≠ iy) hsy.2; exact hL i j hi1 hij hj2 (by omega) (by omega))
  have hM : iy < ix → ix = iy + 1 := fun hyx => (by by_contra hne; have hu_eq : u = iy := (by omega); have hw_eq : w = ix := (by omega); have hqm := hq_skip.2.1 (iy + 1) (by omega) (by omega); exact hav132 ((occurs_132_iff (square p)).mpr ⟨iy, iy + 1, ix, by omega, by omega, by omega, by omega, by omega⟩))
  have hia_eq2 : ia = 2 := by
    by_contra hia_ne2; have hc_bnd := hpbnd 2 (by omega) (by omega); have hc3 := ne_val_of_getD hperm (by omega) hsb.1 (by omega : 2 ≠ ib) hsb.2; have hc4 := ne_val_of_getD hperm (by omega) hsa.1 (by omega : 2 ≠ ia) hsa.2; have hc5 := ne_val_of_getD hperm (by omega) (by omega) (by omega : 2 ≠ 1) hg5
    have hc_eq6 : p.getD 2 0 = 6 := by
      by_contra hne6; have hs6 := perm_idxOf_spec hperm 6 (by omega) (by omega); have := idxOf_ne_of_getD hperm 6 0 (by omega) (by omega) (by omega); have := idxOf_ne_of_getD hperm 6 1 (by omega) (by omega) (by omega); have := idxOf_ne_of_getD hperm 6 2 (by omega) (by omega) (by omega)
      have h6a : p.idxOf 6 < ia := (by have hne : p.idxOf 6 ≠ ia := fun h => (by have h' := hs6.2; rw [h, hsa.2] at h'; omega); by_contra hgt; exact hav312 ((occurs_312_iff p).mpr ⟨2, ia, p.idxOf 6, by omega, by omega, by omega, by omega, by omega⟩))
      exact hav54321 (occurs_54321_of_indices (i₁ := 2) (i₂ := p.idxOf 6) (i₃ := ia) (i₄ := ib) (i₅ := n - 1) (by omega) h6a hia_lt_ib (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))
    have hi6 : p.idxOf 6 = 2 := (by rw [← hc_eq6]; exact perm_idxOf_getD hperm (by omega)); by_cases hx1 : ix = 1
    · have hia4 : ia = 4 := (by have h := hp_ix; rw [hx1] at h; omega); by_cases hy2 : iy = 2
      · have hib5 : ib = 5 := (by have h := hp_iy; rw [hy2, hc_eq6] at h; omega); have hq3 : (square p).getD 3 0 = 6 := (by have := hq_skip.2.2 3 (by omega) (by omega); omega); have hp3 := getD_of_sq_eq hperm 3 6 (by omega) (by omega) (by omega) hq3; rw [hi6] at hp3
        have := perm_getD_inj hperm (by omega : 3 < n) hsb.1 (hp3.trans hsb.2.symm); omega
      · have hq2 : (square p).getD 2 0 = 6 := (by have := hq_skip.2.1 2 (by omega) (by omega); omega); have hp2 := getD_of_sq_eq hperm 2 6 (by omega) (by omega) (by omega) hq2; rw [hi6, hc_eq6] at hp2; omega
    · by_cases hy1 : iy = 1
      · have hib4 : ib = 4 := (by have h := hp_iy; rw [hy1] at h; omega); have hx2 : ix = 2 := (by have := hM (by omega); omega); have h := hp_ix; rw [hx2, hc_eq6] at h; omega
      · have hq1 : (square p).getD 1 0 = 6 := (by have := hq_skip.1 1 le_rfl (by omega); omega); have hp1 := getD_of_sq_eq hperm 1 6 (by omega) (by omega) (by omega) hq1; rw [hi6] at hp1; omega
  have hp2 : p.getD 2 0 = 4 := (by rw [← hia_eq2]; exact hsa.2); have hix_eq_ib : ix = ib := (by have hqb : (square p).getD ib 0 = 4 := (by rw [hsq.2 ib hsb.1, hsb.2]; exact hp2); exact perm_getD_inj hsq.1 hsx.1 hsb.1 (hsx.2.trans hqb.symm))
  have hiy_lt_ib : iy < ib := (by by_contra hge; have := left_bound_of_avoids_312 hperm hav312 hend (idx := ib) (later := iy) (by omega) hsy.1 (by omega) (by omega); omega); have hiy_eq : iy = ib - 1 := (by have := hM (by omega); omega); have hu_eq : u = ib - 1 := (by omega); have hw_eq : w = ib := (by omega)
  have hpair : ∀ r, 2 * r + 2 ≤ ib →
      p.getD (2 * r + 1) 0 = 2 * r + 5 ∧ p.getD (2 * r + 2) 0 = 2 * r + 4 := fun r hr => by
    induction r with
    | zero => exact ⟨hg5, hp2⟩
    | succ r ih =>
      obtain ⟨h1, h2⟩ := ih (by omega); have hqa : (square p).getD (2 * r + 2) 0 = 2 * r + 7 := (by have := hq_skip.1 (2 * r + 2) (by omega) (by omega); omega)
      have hqb : (square p).getD (2 * r + 1) 0 = 2 * r + 6 := (by have := hq_skip.1 (2 * r + 1) (by omega) (by omega); omega); have hsa1 := hsq.2 (2 * r + 2) (by omega); rw [hqa, h2, show 2 * r + 4 - 1 = 2 * (r + 1) + 1 by omega] at hsa1
      have hsb1 := hsq.2 (2 * r + 1) (by omega); rw [hqb, h1, show 2 * r + 5 - 1 = 2 * (r + 1) + 2 by omega] at hsb1; exact ⟨hsa1.symm, hsb1.symm⟩
  have hib_odd : ib % 2 = 1 := (by by_contra hev; have := (hpair ((ib - 2) / 2) (by omega)).2; rw [show 2 * ((ib - 2) / 2) + 2 = ib by omega, hsb.2] at this; omega); let j := (ib - 3) / 2; have hib_j : ib = 2 * j + 3 := (by omega); have hj_bnd : j ≤ (n - 6) / 2 := (by omega)
  have htail : ∀ d, 2 * j + 4 + d ≤ n - 2 →
      p.getD (2 * j + 4 + d) 0 = 2 * j + 6 + d := fun d hd => by
    induction d with
    | zero =>
      simp only [Nat.add_zero]; have hp_odd := (hpair j (by omega)).1; have hq_odd : (square p).getD (2 * j + 1) 0 = 2 * j + 6 := (by have := hq_skip.1 (2 * j + 1) (by omega) (by omega); omega)
      have h := hsq.2 (2 * j + 1) (by omega); rw [hq_odd, hp_odd, show 2 * j + 5 - 1 = 2 * j + 4 by omega] at h; exact h.symm
    | succ d ih => have hprev := ih (by omega); have hqd : (square p).getD (2 * j + 4 + d) 0 = 2 * j + 7 + d := (by have := hq_skip.2.2 (2 * j + 4 + d) (by omega) (by omega); omega); have h := hsq.2 (2 * j + 4 + d) (by omega); rw [hqd, hprev, show 2 * j + 6 + d - 1 = 2 * j + 4 + (d + 1) by omega] at h; omega
  refine ⟨j, hj_bnd, list_eq_of_getD hlen ?_ fun i hi => ?_⟩
  · have hmid : ((List.range (j + 1)).flatMap fun r => [2 * r + 5, 2 * r + 4]).length = 2 * j + 2 := (by simpa [Nat.mul_add] using flatMap_pair_length (j + 1) 5 4); unfold familyK; simp [hmid]; omega
  · rw [familyK_getD n j i (by omega) hj_bnd hi]; by_cases h0 : i = 0
    · subst i; simp only [↓reduceIte]; exact hm
    by_cases h1 : i ≤ 2 * j + 2
    · simp only [h0, h1, ↓reduceIte]; by_cases hodd : i % 2 = 1
      · simp only [hodd, ↓reduceIte]; have := (hpair ((i - 1) / 2) (by omega)).1; rw [show 2 * ((i - 1) / 2) + 1 = i by omega] at this; omega
      · simp only [hodd, ↓reduceIte]; have := (hpair ((i - 2) / 2) (by omega)).2; rw [show 2 * ((i - 2) / 2) + 2 = i by omega] at this; omega
    by_cases h2 : i = 2 * j + 3
    · subst i; simp only [h0, h1, ↓reduceIte]; rw [← hib_j]; exact hsb.2
    by_cases h3 : i < n - 1
    · simp only [h0, h1, h2, h3, ↓reduceIte]; have := htail (i - (2 * j + 4)) (by omega); rw [show 2 * j + 4 + (i - (2 * j + 4)) = i by omega] at this; omega
    · obtain rfl : i = n - 1 := (by omega); repeat' (split <;> try omega)
private theorem first_entry_two_classify {n : ℕ} (hn : 4 ≤ n) {p : List ℕ} (hp : p ∈ indecomposableAvoiders n) (hm : p.getD 0 0 = 2) : p = familyI n ∨ (5 ≤ n ∧ p = familyJ n) ∨ (6 ≤ n ∧ ∃ j ≤ (n - 6) / 2, p = familyK n j) := by
  rcases hp with ⟨hpne, ⟨hperm, hav312, hav54321, hav132⟩, hind⟩; have hlen : p.length = n := (by simpa using hperm.length_eq); have hsq := square_perm_and_getD hperm; have hqlen : (square p).length = n := (by simpa using hsq.1.length_eq)
  have hsh := indecomposable_shape_and_prefix_iff.2.2.2.2 n (by omega) p ⟨hpne, ⟨hperm, hav312, hav54321, hav132⟩, hind⟩; have hend : p.getD (n - 1) 0 = 1 := hsh.1.1; have hipn : p.idxOf n = n - 2 := (by have := hsh.2.2.1.2.2.2.2.2 hm; omega)
  have hpn2 : p.getD (n - 2) 0 = n := (by have hs := (perm_idxOf_spec hperm n (by omega) le_rfl).2; rwa [hipn] at hs); have hqn2 : (square p).getD (n - 2) 0 = 1 := (by have h1 := hsh.2.2.1.1; rwa [hipn, Nat.add_sub_cancel] at h1); have hqn1 : (square p).getD (n - 1) 0 = 2 := hsh.2.2.1.2.1.trans hm
  have hqbnd : ∀ i < n - 2, 3 ≤ (square p).getD i 0 ∧ (square p).getD i 0 ≤ n := fun i hi => by
    have hb := perm_getD_bounds hsq.1 (by omega : i < n); have h1 := ne_val_of_getD hsq.1 (by omega) (by omega) (by omega : i ≠ n - 2) hqn2; have h2 := ne_val_of_getD hsq.1 (by omega) (by omega) (by omega : i ≠ n - 1) hqn1; omega
  have hpbnd : ∀ i, 1 ≤ i → i < n - 2 → 3 ≤ p.getD i 0 ∧ p.getD i 0 ≤ n - 1 := fun i hi1 hi2 => by
    have hb := perm_getD_bounds hperm (by omega : i < n); have h1 := ne_val_of_getD hperm (by omega) (by omega) (by omega : i ≠ 0) hm; have h2 := ne_val_of_getD hperm (by omega) (by omega) (by omega : i ≠ n - 2) hpn2; have h3 := ne_val_of_getD hperm (by omega) (by omega) (by omega : i ≠ n - 1) hend; omega
  let g := p.getD 1 0; have hg_bnd : 3 ≤ g ∧ g ≤ n - 1 := hpbnd 1 le_rfl (by omega); have hq0 : (square p).getD 0 0 = g := (by rw [hsq.2 0 (by omega), hm])
  have hL : ∀ i j, 1 ≤ i → i < j → j < n - 2 → g < (square p).getD i 0 →
      g < (square p).getD j 0 → (square p).getD i 0 < (square p).getD j 0 := by
    intro i j hi1 hij hj2 hgi hgj; have hne : (square p).getD i 0 ≠ (square p).getD j 0 := fun heq => (by have := perm_getD_inj hsq.1 (by omega) (by omega) heq; omega); by_contra hnot; exact hav132 ((occurs_132_iff (square p)).mpr ⟨0, i, j, by omega, hij, by omega, by rwa [hq0], by omega⟩)
  have hg_le5 : g ≤ 5 := by
    by_contra hgt; have hs3 := perm_idxOf_spec hperm 3 (by omega) (by omega); have hs4 := perm_idxOf_spec hperm 4 (by omega) (by omega); have hs5 := perm_idxOf_spec hperm 5 (by omega) (by omega)
    have h30 := idxOf_ne_of_getD hperm 3 0 (by omega) (by omega) (by omega); have h31 := idxOf_ne_of_getD hperm 3 1 (by omega) (by omega) (by change g ≠ 3; omega)
    have h3n := idxOf_ne_of_getD hperm 3 (n - 1) (by omega) (by omega) (by omega); have h40 := idxOf_ne_of_getD hperm 4 0 (by omega) (by omega) (by omega)
    have h41 := idxOf_ne_of_getD hperm 4 1 (by omega) (by omega) (by change g ≠ 4; omega); have h4n := idxOf_ne_of_getD hperm 4 (n - 1) (by omega) (by omega) (by omega)
    have h50 := idxOf_ne_of_getD hperm 5 0 (by omega) (by omega) (by omega); have h51 := idxOf_ne_of_getD hperm 5 1 (by omega) (by omega) (by change g ≠ 5; omega); have h5n := idxOf_ne_of_getD hperm 5 (n - 1) (by omega) (by omega) (by omega)
    have h43 : p.idxOf 4 < p.idxOf 3 := (by have hne : p.idxOf 3 ≠ p.idxOf 4 := fun he => (by rw [he] at hs3; omega); by_contra h; exact hav312 ((occurs_312_iff p).mpr ⟨1, p.idxOf 3, p.idxOf 4, by omega, by omega, by omega, by omega, by change p.getD (p.idxOf 4) 0 < g; omega⟩))
    have h54 : p.idxOf 5 < p.idxOf 4 := (by have hne : p.idxOf 4 ≠ p.idxOf 5 := fun he => (by rw [he] at hs4; omega); by_contra h; exact hav312 ((occurs_312_iff p).mpr ⟨1, p.idxOf 4, p.idxOf 5, by omega, by omega, by omega, by omega, by change p.getD (p.idxOf 5) 0 < g; omega⟩))
    exact hav54321 (occurs_54321_of_indices (i₁ := 1) (i₂ := p.idxOf 5) (i₃ := p.idxOf 4) (i₄ := p.idxOf 3) (i₅ := n - 1) (by omega) h54 h43 (by omega) (by omega) (by omega) (by omega) (by omega) (by change p.getD (p.idxOf 5) 0 < g; omega))
  rcases (by omega : g = 3 ∨ g = 4 ∨ g = 5) with hg3 | hg4 | hg5
  · left
    have hq_rest := strictMono_Ico_eq (a := 1) (b := n - 2) (v₀ := 4) (f := fun i => (square p).getD i 0)
      (fun i hi1 hi2 => by have := hqbnd i hi2; have := ne_val_of_getD hsq.1 (by omega) (by omega) (by omega : i ≠ 0) (hq0.trans hg3); omega)
      (fun i j hi1 hij hj2 => by have := hqbnd i (by omega); have := hqbnd j hj2; have := ne_val_of_getD hsq.1 (by omega) (by omega) (by omega : i ≠ 0) (hq0.trans hg3); have := ne_val_of_getD hsq.1 (by omega) (by omega) (by omega : j ≠ 0) (hq0.trans hg3); exact hL i j hi1 hij hj2 (by omega) (by omega))
    have hp_init : ∀ i ≤ n - 2, p.getD i 0 = i + 2 := fun i hi => by
      induction i with
      | zero => exact hm
      | succ i ih =>
        have hi' := ih (by omega)
        have hqi : (square p).getD i 0 = i + 3 := by
          by_cases h0 : i = 0
          · subst i; exact hq0.trans hg3
          · have := hq_rest i (by omega) (by omega); omega
        have hsqi := hsq.2 i (by omega); rw [hi', show i + 2 - 1 = i + 1 by omega] at hsqi; omega
    apply list_eq_of_getD hlen (by simp [familyI]; omega); intro i hi; rw [familyI_getD n i (by omega) hi]; split
    · exact hp_init i (by omega)
    · obtain rfl : i = n - 1 := (by omega); exact hend
  · right; left; refine ⟨by omega, ?_⟩; let ib := p.idxOf 3; let ix := (square p).idxOf 3; have hsb : ib < n ∧ p.getD ib 0 = 3 := perm_idxOf_spec hperm 3 (by omega) (by omega); have hsx : ix < n ∧ (square p).getD ix 0 = 3 := perm_idxOf_spec hsq.1 3 (by omega) (by omega)
    have hib_bnd : 2 ≤ ib ∧ ib ≤ n - 3 := by
      have h0 : ib ≠ 0 := idxOf_ne_of_getD hperm 3 0 (by omega) (by omega) (by omega); have h1 : ib ≠ 1 := idxOf_ne_of_getD hperm 3 1 (by omega) (by omega) (by change g ≠ 3; omega)
      have hn2 : ib ≠ n - 2 := idxOf_ne_of_getD hperm 3 (n - 2) (by omega) (by omega) (by omega); have hn1 : ib ≠ n - 1 := idxOf_ne_of_getD hperm 3 (n - 1) (by omega) (by omega) (by omega); omega
    have hix_bnd : 1 ≤ ix ∧ ix ≤ n - 3 := by
      have h0 : ix ≠ 0 := idxOf_ne_of_getD hsq.1 3 0 (by omega) (by omega) (by rw [hq0, hg4]; decide); have hn2 : ix ≠ n - 2 := idxOf_ne_of_getD hsq.1 3 (n - 2) (by omega) (by omega) (by omega); have hn1 : ix ≠ n - 1 := idxOf_ne_of_getD hsq.1 3 (n - 1) (by omega) (by omega) (by omega); omega
    have hp_ix : p.getD ix 0 = ib + 1 := getD_of_sq_eq hperm ix 3 hsx.1 (by omega) (by omega) hsx.2
    have hq_skip := strictMono_skip1_eq (a := 1) (b := n - 2) (x := ix) (v₀ := 5) (f := fun i => (square p).getD i 0) ⟨hix_bnd.1, by omega⟩
      (fun i hi1 hi2 hne => by have := hqbnd i hi2; have := ne_val_of_getD hsq.1 (by omega) (by omega) (by omega : i ≠ 0) (hq0.trans hg4); have := ne_val_of_getD hsq.1 (by omega) hsx.1 hne hsx.2; omega)
      (fun i j hi1 hij hj2 hnei hnej => by
        have := hqbnd i (by omega); have := hqbnd j hj2; have := ne_val_of_getD hsq.1 (by omega) (by omega) (by omega : i ≠ 0) (hq0.trans hg4); have := ne_val_of_getD hsq.1 (by omega) (by omega) (by omega : j ≠ 0) (hq0.trans hg4); have := ne_val_of_getD hsq.1 (by omega) hsx.1 hnei hsx.2
        have := ne_val_of_getD hsq.1 (by omega) hsx.1 hnej hsx.2; exact hL i j hi1 hij hj2 (by omega) (by omega))
    have hix_le_ib : ix ≤ ib := by
      by_contra hgt; have hne2 : ib ≠ 2 := fun h2 => (by have : p.getD ix 0 = p.getD ib 0 := (by rw [hp_ix, hsb.2, h2]); have := perm_getD_inj hperm hsx.1 hsb.1 this; omega); have := left_bound_of_avoids_312 hperm hav312 hend (idx := ib) (later := ix) (by omega) hsx.1 (by omega) (by omega); omega
    have hix_ne1 : ix ≠ 1 := by
      intro h1; have hib3 : ib = 3 := (by have h := hp_ix; rw [h1] at h; change g = ib + 1 at h; omega); have hp3_eq3 : p.getD 3 0 = 3 := hib3 ▸ hsb.2; have hq2 : (square p).getD 2 0 = 5 := (by have := hq_skip.2 2 (by omega) (by omega); omega)
      have hs5 := perm_idxOf_spec hperm 5 (by omega) (by omega); have hp2 : p.getD 2 0 = p.idxOf 5 + 1 := getD_of_sq_eq hperm 2 5 (by omega) (by omega) (by omega) hq2
      have hc0 := idxOf_ne_of_getD hperm 5 0 (by omega) (by omega) (by omega); have hc1 := idxOf_ne_of_getD hperm 5 1 (by omega) (by omega) (by change g ≠ 5; omega); have hc2 : p.idxOf 5 ≠ 2 := fun h => (by rw [h] at hs5; omega); have hc3 := idxOf_ne_of_getD hperm 5 3 (by omega) (by omega) (by omega)
      have hc4 : p.idxOf 5 ≠ 4 := fun h => (by rw [h] at hp2 hs5; have := perm_getD_inj hperm (by omega) (by omega) (hp2.trans hs5.2.symm); omega); exact hav312 ((occurs_312_iff p).mpr ⟨2, 3, p.idxOf 5, by omega, by omega, by omega, by omega, by omega⟩)
    have hix_eq2 : ix = 2 := by
      by_contra hne2; have hix_ge3 : 3 ≤ ix := (by omega)
      have hib_ge4 : 4 ≤ ib := by
        by_cases he : ix = ib
        · have h := hp_ix; rw [he, hsb.2] at h; omega
        · omega
      have hq1 : (square p).getD 1 0 = 5 := (by have := hq_skip.1 1 le_rfl (by omega); omega); have hp3 : p.getD 3 0 = 5 := (by have h := hsq.2 1 (by omega); change (square p).getD 1 0 = p.getD (g - 1) 0 at h; rw [hq1, hg4] at h; exact h.symm)
      have hq2 : (square p).getD 2 0 = 6 := (by have := hq_skip.1 2 (by omega) (by omega); omega); have hs6 := perm_idxOf_spec hperm 6 (by omega) (by omega); have hp2 : p.getD 2 0 = p.idxOf 6 + 1 := getD_of_sq_eq hperm 2 6 (by omega) (by omega) (by omega) hq2
      have hc0 := idxOf_ne_of_getD hperm 6 0 (by omega) (by omega) (by omega); have hc1 := idxOf_ne_of_getD hperm 6 1 (by omega) (by omega) (by change g ≠ 6; omega); have hc2 : p.idxOf 6 ≠ 2 := fun h => (by rw [h] at hs6; omega); have hc3 := idxOf_ne_of_getD hperm 6 3 (by omega) (by omega) (by omega)
      have hc4 : p.idxOf 6 ≠ 4 := fun h => (by rw [h] at hp2; have := perm_getD_inj hperm (by omega) (by omega) (hp2.trans hp3.symm); omega); have hc5 : p.idxOf 6 ≠ 5 := fun h => (by rw [h] at hp2 hs6; have := perm_getD_inj hperm (by omega) (by omega) (hp2.trans hs6.2.symm); omega)
      exact hav312 ((occurs_312_iff p).mpr ⟨2, 3, p.idxOf 6, by omega, by omega, by omega, by omega, by omega⟩)
    have hp_tail : ∀ d, 3 + d ≤ n - 2 → p.getD (3 + d) 0 = 5 + d := fun d hd => by
      induction d with
      | zero => simp only [Nat.add_zero]; have hq1 : (square p).getD 1 0 = 5 := (by have := hq_skip.1 1 le_rfl (by omega); omega); have h := hsq.2 1 (by omega); change (square p).getD 1 0 = p.getD (g - 1) 0 at h; rw [hq1, hg4] at h; exact h.symm
      | succ d ih => have hprev := ih (by omega); have hqd : (square p).getD (3 + d) 0 = 6 + d := (by have := hq_skip.2 (3 + d) (by omega) (by omega); omega); have h := hsq.2 (3 + d) (by omega); rw [hqd, hprev, show 5 + d - 1 = 3 + (d + 1) by omega] at h; omega
    have hp2 : p.getD 2 0 = 3 := (by have hib2 : ib = 2 := (by by_contra hne; have := hp_tail (ib - 3) (by omega); rw [show 3 + (ib - 3) = ib by omega, hsb.2] at this; omega); rw [← hib2]; exact hsb.2)
    apply list_eq_of_getD hlen (by simp [familyJ]; omega); intro i hi; rw [familyJ_getD n i (by omega) hi]; by_cases h0 : i = 0
    · subst i; simp only [↓reduceIte]; exact hm
    by_cases h1 : i = 1
    · subst i; simp only [show (1 : ℕ) ≠ 0 by decide, ↓reduceIte]; exact hg4
    by_cases h2 : i = 2
    · subst i; simp only [show (2 : ℕ) ≠ 0 by decide, show (2 : ℕ) ≠ 1 by decide, ↓reduceIte]
      exact hp2
    by_cases h3 : i < n - 1
    · simp only [h0, h1, h2, h3, ↓reduceIte]; have := hp_tail (i - 3) (by omega); rw [show 3 + (i - 3) = i by omega] at this; omega
    · obtain rfl : i = n - 1 := (by omega); repeat' (split <;> try omega)
  · right; right; exact first_entry_two_g5 hn ⟨hpne, ⟨hperm, hav312, hav54321, hav132⟩, hind⟩ hm hg5
private theorem first_entry_three_impossible (n : ℕ) (hn : 5 ≤ n) (p : List ℕ) (hp : p ∈ indecomposableAvoiders n) : p.getD 0 0 ≠ 3 := by
  intro hm; rcases hp with ⟨hpne, ⟨hperm, hav312, hav54321, hav132⟩, hind⟩; have hsq := square_perm_and_getD hperm; have hqlen : (square p).length = n := (by simpa using hsq.1.length_eq)
  have hsh := indecomposable_shape_and_prefix_iff.2.2.2.2 n (by omega) p ⟨hpne, ⟨hperm, hav312, hav54321, hav132⟩, hind⟩; have hend : p.getD (n - 1) 0 = 1 := hsh.1.1; let ip := p.idxOf n
  let it := p.idxOf 2; have hsp : ip < n ∧ p.getD ip 0 = n := perm_idxOf_spec hperm n (by omega) le_rfl; have hst : it < n ∧ p.getD it 0 = 2 := perm_idxOf_spec hperm 2 (by omega) (by omega); have hip_ne : ip ≠ n - 1 := idxOf_ne_of_getD hperm n (n - 1) (by omega) le_rfl (by omega)
  have hip_ge : n - 3 ≤ ip := (by have := hsh.2.2.1.2.2.2.2.1; omega); have hqp : (square p).getD ip 0 = 1 := (by have h := hsh.2.2.1.1; rwa [Nat.add_sub_cancel] at h); have hqn : (square p).getD (n - 1) 0 = 3 := hsh.2.2.1.2.1.trans hm
  have hit_bnd : 1 ≤ it ∧ it ≤ n - 2 := (by have h0 : it ≠ 0 := idxOf_ne_of_getD hperm 2 0 (by omega) (by omega) (by omega); have hn1 : it ≠ n - 1 := idxOf_ne_of_getD hperm 2 (n - 1) (by omega) (by omega) (by omega); omega); rcases (by omega : ip = n - 2 ∨ ip = n - 3) with hip2 | hip3
  · let i2 := (square p).idxOf 2; have hs2 : i2 < n ∧ (square p).getD i2 0 = 2 := perm_idxOf_spec hsq.1 2 (by omega) (by omega)
    have hi2_le : i2 ≤ n - 3 := (by have h1 : i2 ≠ n - 2 := idxOf_ne_of_getD hsq.1 2 (n - 2) (by omega) (by omega) (by rw [← hip2, hqp]; decide); have h2 : i2 ≠ n - 1 := idxOf_ne_of_getD hsq.1 2 (n - 1) (by omega) (by omega) (by omega); omega)
    have hi2_eq : i2 = n - 3 := by
      by_contra hne; have hb := perm_getD_bounds hsq.1 (by omega : n - 3 < n); have c1 := ne_val_of_getD hsq.1 (by omega) hsp.1 (by omega : n - 3 ≠ ip) hqp; have c2 := ne_val_of_getD hsq.1 (by omega) hs2.1 (by omega : n - 3 ≠ i2) hs2.2
      have c3 := ne_val_of_getD hsq.1 (by omega) (by omega) (by omega : n - 3 ≠ n - 1) hqn; exact hav132 ((occurs_132_iff (square p)).mpr ⟨i2, n - 3, n - 1, by omega, by omega, by omega, by omega, by omega⟩)
    have hq_n3 : (square p).getD (n - 3) 0 = 2 := (by rw [← hi2_eq]; exact hs2.2); have hp_n3 : p.getD (n - 3) 0 = it + 1 := getD_of_sq_eq hperm (n - 3) 2 (by omega) (by omega) (by omega) hq_n3
    have hit_lt : it < n - 3 := (by have hne_n2 : it ≠ n - 2 := fun h => (by have h' := hst.2; rw [h, ← hip2, hsp.2] at h'; omega); have hne_n3 : it ≠ n - 3 := fun h => (by have h' := hst.2; rw [h, hp_n3] at h'; omega); omega)
    have hit_ge2 : 2 ≤ it := (by by_contra h1; have h1' : it = 1 := (by omega); have ha : p.getD (n - 3) 0 = 2 := (by rw [hp_n3, h1']); have hb : p.getD 1 0 = 2 := (by rw [← h1']; exact hst.2); have := perm_getD_inj hperm (by omega : n - 3 < n) (by omega : 1 < n) (ha.trans hb.symm); omega)
    have := left_bound_of_avoids_312 hperm hav312 hend (idx := it) (later := n - 3) hit_lt (by omega) (by omega) (by omega); omega
  · have hq_n2 : (square p).getD (n - 2) 0 = 2 := by
      have hlt := hsh.2.2.1.2.2.1 (n - 1) n (by omega) (by omega) le_rfl; rw [show n - 1 - 1 = n - 2 by omega, hqn] at hlt; have hb := perm_getD_bounds hsq.1 (by omega : n - 2 < n); have hne1 := ne_val_of_getD hsq.1 (by omega) hsp.1 (by omega : n - 2 ≠ ip) hqp; omega
    have hp_n2 : p.getD (n - 2) 0 = it + 1 := getD_of_sq_eq hperm (n - 2) 2 (by omega) (by omega) (by omega) hq_n2; have hit_lt : it < n - 2 := (by have hne : it ≠ n - 2 := fun h => (by have h' := hst.2; rw [h, hp_n2] at h'; omega); omega)
    have hit_ge2 : 2 ≤ it := (by by_contra h1; have h1' : it = 1 := (by omega); have ha : p.getD (n - 2) 0 = 2 := (by rw [hp_n2, h1']); have hb : p.getD 1 0 = 2 := (by rw [← h1']; exact hst.2); have := perm_getD_inj hperm (by omega : n - 2 < n) (by omega : 1 < n) (ha.trans hb.symm); omega)
    have := left_bound_of_avoids_312 hperm hav312 hend (idx := it) (later := n - 2) hit_lt (by omega) (by omega) (by omega); omega
/-- Complete classification and count of indecomposable square-avoiders with first entry two for `n ≥ 4`, and impossibility of first entry three for `n ≥ 5`. -/
theorem first_entry_two_and_three_classification : (∀ n : ℕ, 4 ≤ n → (∀ p : List ℕ, (p ∈ indecomposableAvoiders n ∧ p.getD 0 0 = 2) ↔ (p = familyI n ∨ (5 ≤ n ∧ p = familyJ n) ∨ (6 ≤ n ∧ ∃ j ≤ (n - 6) / 2, p = familyK n j))) ∧ {p ∈ indecomposableAvoiders n | p.getD 0 0 = 2}.ncard = (if n = 4 then 1 else n / 2)) ∧
    (∀ n : ℕ, 5 ≤ n → ∀ p ∈ indecomposableAvoiders n, p.getD 0 0 ≠ 3) := by
  classical
  refine ⟨fun n hn => ?_, first_entry_three_impossible⟩
  have hiff : ∀ p : List ℕ, (p ∈ indecomposableAvoiders n ∧ p.getD 0 0 = 2) ↔ (p = familyI n ∨ (5 ≤ n ∧ p = familyJ n) ∨
        (6 ≤ n ∧ ∃ j ≤ (n - 6) / 2, p = familyK n j)) := fun p => by
    refine ⟨fun ⟨hp, hm⟩ => first_entry_two_classify hn hp hm, ?_⟩; rintro (rfl | ⟨h5, rfl⟩ | ⟨h6, j, hj, rfl⟩)
    · refine ⟨familyI_mem n (by omega), ?_⟩; rw [familyI_getD n 0 (by omega) (by omega)]; split <;> omega
    · exact ⟨familyJ_mem n h5, rfl⟩
    · exact ⟨familyK_mem n j h6 hj, rfl⟩
  refine ⟨hiff, ?_⟩; have hdist := seven_families_admissible_and_distinct; by_cases hn4 : n = 4
  · subst n; simp only [↓reduceIte]; have hset : {p ∈ indecomposableAvoiders 4 | p.getD 0 0 = 2} = {familyI 4} := (by ext p; change (p ∈ indecomposableAvoiders 4 ∧ p.getD 0 0 = 2) ↔ p = familyI 4; rw [hiff]; simp); rw [hset, Set.ncard_singleton]
  by_cases hn5 : n = 5
  · subst n; simp only [show (5 : ℕ) ≠ 4 by decide, ↓reduceIte]
    let F : Finset (List ℕ) := insert (familyI 5) {familyJ 5}; have hset : {p ∈ indecomposableAvoiders 5 | p.getD 0 0 = 2} = (F : Set (List ℕ)) := (by ext p; change (p ∈ indecomposableAvoiders 5 ∧ p.getD 0 0 = 2) ↔ p ∈ (F : Set (List ℕ)); rw [hiff]; simp [F])
    rw [hset, Set.ncard_coe_finset, Finset.card_insert_of_notMem]
    · rfl
    · simp [hdist.2.2.2.2.2.2.2.2.1 5 le_rfl]
  · have hn6 : 6 ≤ n := (by omega); simp only [hn4, ↓reduceIte]; let Ks : Finset (List ℕ) := (Finset.range ((n - 6) / 2 + 1)).image (familyK n); let F : Finset (List ℕ) := insert (familyI n) (insert (familyJ n) Ks)
    have hset : {p ∈ indecomposableAvoiders n | p.getD 0 0 = 2} = (F : Set (List ℕ)) := by
      ext p; change (p ∈ indecomposableAvoiders n ∧ p.getD 0 0 = 2) ↔ p ∈ (F : Set (List ℕ)); rw [hiff]; simp only [F, Ks, Finset.coe_insert, Finset.coe_image, Finset.coe_range, Set.mem_insert_iff, Set.mem_image, Set.mem_Iio]; constructor
      · rintro (h | ⟨_, h⟩ | ⟨_, j, hj, h⟩)
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr ⟨j, by omega, h.symm⟩)
      · rintro (h | h | ⟨j, hj, h⟩)
        · exact Or.inl h
        · exact Or.inr (Or.inl ⟨by omega, h⟩)
        · exact Or.inr (Or.inr ⟨hn6, j, by omega, h.symm⟩)
    have hI_not : familyI n ∉ insert (familyJ n) Ks := (by simp only [Ks, Finset.mem_insert, Finset.mem_image, Finset.mem_range, not_or, not_exists, not_and]; refine ⟨hdist.2.2.2.2.2.2.2.2.1 n (by omega), fun j hj he => ?_⟩; exact hdist.2.2.2.2.2.2.2.2.2.1 n j hn6 (by omega) he.symm)
    have hJ_not : familyJ n ∉ Ks := (by simp only [Ks, Finset.mem_image, Finset.mem_range, not_exists, not_and]; intro j hj he; exact hdist.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 n j hn6 (by omega) he.symm)
    have hK_inj : Set.InjOn (familyK n) (Finset.range ((n - 6) / 2 + 1)) := (by intro j₁ hj₁ j₂ hj₂ heq; rw [Finset.mem_coe, Finset.mem_range] at hj₁ hj₂; exact hdist.2.2.2.2.2.2.2.1 n j₁ j₂ hn6 (by omega) (by omega) heq)
    rw [hset, Set.ncard_coe_finset, Finset.card_insert_of_notMem hI_not, Finset.card_insert_of_notMem hJ_not, Finset.card_image_of_injOn hK_inj, Finset.card_range]; omega
end D5.S3.Combinatorics.PermutationSquare.PermutationSquareFamilies
