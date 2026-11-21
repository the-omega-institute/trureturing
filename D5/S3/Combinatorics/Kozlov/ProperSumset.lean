/- GID: D5/S3/Combinatorics/Kozlov/ProperSumset
   generality: G
   mirror-B: none(waiver:scoped-proof-probe)
   mirror-E: none(waiver:literal-equal-shift-counting)
   anchors: [mathlib/module/Mathlib.Combinatorics.SetFamily.KruskalKatona]
   utility: none
   digest: Every literal proper sum has a chained proper representative at zero shifts. -/

import D5.S3.Combinatorics.Kozlov.LexPositionShadow
import D5.S3.Combinatorics.Kozlov.ProperModel
import Mathlib.Data.List.GetD

set_option autoImplicit false

open Finset D5.S3.Combinatorics.Kozlov.LexCompression
open scoped BigOperators FinsetFamily

namespace D5.S3.Combinatorics.Kozlov

private def degrees (r k : ℕ) : List ℤ := List.replicate r (k : ℤ)

private theorem degrees_sorted (r k : ℕ) : (degrees r k).Pairwise (· ≥ ·) := by
  simp [degrees]

private theorem degrees_succ (r k : ℕ) :
    (degrees r k).map (· + 1) = degrees r (k + 1) := by
  simp [degrees]

private theorem sum_list_ofFn {r : ℕ} (f : Fin r → ℕ) :
    (List.ofFn f).sum = ∑ i, f i := by
  induction r with
  | zero => simp
  | succ r ih => rw [List.ofFn_succ, List.sum_cons, Fin.sum_univ_succ, ih]

private theorem input_components {n r : ℕ} (D : Fin r → Family n) (k : ℕ) :
    List.Forall₂ Component (degrees r k) (List.ofFn fun i => missing (D i) k) := by
  apply List.forall₂_of_length_eq_of_get (by simp [degrees])
  intro i hi hi'
  simp only [List.get_eq_getElem, degrees, List.getElem_replicate, List.getElem_ofFn]
  refine ⟨?_, by omega⟩
  intro t ht
  simpa using mem_layer.mp (mem_sdiff.mp ht).1

private theorem mass_le_capacity {n : ℕ} {ks : List ℤ} {M : List (Family n)}
    (h : List.Forall₂ Component ks M) :
    (M.map card).sum ≤ (ks.map (capZ n)).sum := by
  induction h with
  | nil => simp
  | cons hc _ ih =>
    simpa only [List.map_cons, List.sum_cons] using Nat.add_le_add hc.card_le ih

private theorem shadow_mass_le {n r : ℕ} (D : Fin r → Family n)
    (hD : ∀ i, IsComplex (D i)) (k : ℕ) :
    ((List.ofFn fun i => missing (D i) k).map fun A => #(∂⁺ A)).sum ≤
      ((List.ofFn fun i => missing (D i) (k + 1)).map card).sum := by
  rw [List.map_ofFn, List.map_ofFn, sum_list_ofFn, sum_list_ofFn]
  exact Finset.sum_le_sum fun i _ => card_le_card (missing_upShadow_subset (hD i))

private theorem at_list_length {n r k : ℕ} {L : List (Family n)}
    (h : List.Forall₂ Component (degrees r k) L) : L.length = r := by
  simpa [degrees] using h.length_eq.symm

private theorem layer_of_component {n r k : ℕ} {L : List (Family n)}
    (h : List.Forall₂ Component (degrees r k) L) (i : Fin r) :
    L.getD i.val ∅ ⊆ layer n k := by
  have hi : i.val < L.length := by rw [at_list_length h]; exact i.isLt
  have hi' : i.val < (degrees r k).length := by simp [degrees]
  have hc := h.get hi' hi
  rw [← List.getD_eq_get L ∅ ⟨i.val, hi⟩] at hc
  simp only [List.get_eq_getElem, degrees, List.getElem_replicate] at hc
  intro t ht
  simpa using hc.1 ht

private theorem sum_getD {n r : ℕ} {L : List (Family n)} (h : L.length = r) :
    (L.map card).sum = ∑ i : Fin r, #(L.getD i.val ∅) := by
  subst r
  have he : List.ofFn (fun i : Fin L.length => L.getD i.val ∅) = L := by
    convert List.ofFn_get L using 1
    congr
    funext i
    simp
  conv_lhs => rw [← he]
  simp only [List.map_ofFn, sum_list_ofFn, Function.comp_apply]

private theorem top_lt_of_full_missing_layer {n k : ℕ} {D : Family n}
    (hD : IsComplex D) (h : layer n k ⊆ missing D k) : top (fVector D) < (k : ℤ) := by
  apply top_lt_of_vanish
  intro j hj
  unfold fVector fEntry
  apply card_eq_zero.mpr
  apply eq_empty_iff_forall_notMem.mpr
  intro t ht
  obtain ⟨htD, ht⟩ := mem_filter.mp ht
  obtain ⟨s, hst, hs⟩ := exists_subset_card_eq (show k ≤ #t by omega)
  have hsD := hD.down htD hst
  have hsM := h (mem_layer.mpr hs)
  exact (mem_sdiff.mp hsM).2 hsD

/-- Each literal equal-shift sum of proper f-vectors admits a chained tuple of the same rank. -/
theorem proper_sumset_surjOn (n r : ℕ) :
    Set.SurjOn (sumTuple (n := n) (r := r))
      {s | (∀ i, s i ∈ SnF n) ∧ Chained s} (properSumset n r) := by
  classical
  rintro x ⟨s, hs, rfl⟩
  choose D hD hsD using hs
  let A (k : ℕ) : List (Family n) := List.ofFn fun i => missing (D i) k
  let mass (k : ℕ) : ℕ := ((A k).map card).sum
  have hC (k : ℕ) : List.Forall₂ Component (degrees r k) (A k) := input_components D k
  choose L hL using fun k : ℕ => exists_isLexFSeg n (degrees r k) (mass k)
  have hcount (k : ℕ) : ((L k).map card).sum = mass k := by
    rw [(hL k).card_sum, tailCap_zero, min_eq_left (mass_le_capacity (hC k))]
  have hLC (k : ℕ) : List.Forall₂ Component (degrees r k) (L k) :=
    (hL k).1.imp fun _ _ h => h.1
  have hpref (k : ℕ) : IsLexFInitial n (degrees r k) (L k) := by
    apply isLexFInitial_iff.mpr
    rw [hcount]
    exact hL k
  let M (i : Fin r) (k : ℕ) : Family n := (L k).getD i.val ∅
  have hsub (i : Fin r) (k : ℕ) : M i k ⊆ layer n k := layer_of_component (hLC k) i
  have hshadow (k : ℕ) : List.Forall₂ (fun X Y => ∂⁺ X ⊆ Y) (L k) (L (k + 1)) := by
    apply lem_lexF_shadow_subset (degrees_sorted r k) (hL k)
    · rw [degrees_succ]
      exact hL (k + 1)
    · rw [(hL k).shadow_sum, hcount]
      exact (module_shadow_ge_greedy _ (degrees_sorted r k) _ (hC k)).trans
        (shadow_mass_le D hD k)
  have hMshadow (i : Fin r) (k : ℕ) : ∂⁺ (M i k) ⊆ M i (k + 1) := by
    have hl (j : ℕ) : i.val < (L j).length := by
      rw [at_list_length (hLC j)]
      exact i.isLt
    simpa only [M, List.getD_eq_get _ _ ⟨i.val, hl _⟩] using (hshadow k).get (hl k) (hl (k + 1))
  have hMcount (k : ℕ) : (∑ i, #(M i k)) = ∑ i, #(missing (D i) k) := by
    rw [← sum_getD (at_list_length (hLC k)), hcount]
    simp only [mass, A, List.map_ofFn, sum_list_ofFn, Function.comp_apply]
  have hempty (k : ℕ) (hk : ∀ i, missing (D i) k = ∅) (i : Fin r) : M i k = ∅ := by
    have hz : (∑ i, #(M i k)) = 0 := by simp [hMcount, hk]
    exact card_eq_zero.mp (by
      have := Finset.single_le_sum (f := fun i => #(M i k))
        (fun _ _ => Nat.zero_le _) (mem_univ i)
      omega)
  let E (i : Fin r) := fromMissing (M i)
  have hE (i : Fin r) : IsComplex (E i) :=
    fromMissing_isComplex (hMshadow i) (hempty 0 (fun j => missing_zero (hD j)) i)
      (hempty 1 (fun j => missing_one (hD j)) i)
  have heq (i : Fin r) (k : ℕ) : missing (E i) k = M i k := missing_fromMissing (hsub i k)
  refine ⟨fun i => fVector (E i), ⟨fun i => ⟨_, hE i, rfl⟩, ?_⟩, ?_⟩
  · intro i j hij
    change top (fVector (E i)) < (indeg (fVector (E j)) : ℤ)
    rcases indeg_eq_sentinel_or_missing (fVector (E j)) with ht | ⟨k, hk, hmiss⟩
    · rw [ht]
      have hle := top_le (fVector (E i))
      omega
    · rw [← hk]
      have hcard := fEntry_add_card_missing (E j) k.val
      rw [heq] at hcard
      have hp : 0 < #(M j k.val) := by
        change fEntry (E j) k.val < n.choose k.val at hmiss
        omega
      obtain ⟨v, hv⟩ := card_pos.mp hp
      apply top_lt_of_full_missing_layer (hE i)
      intro u hu
      rw [heq]
      have hlt : i.val < (degrees r k.val).length := by simp [degrees]
      exact (hpref k.val).2 (i := i.val) (l := j.val) (u := u) (v := v) hv hlt
        (by simp [degrees])
        (by simpa [degrees, List.getD_eq_getElem _ _ hlt] using mem_layer.mp hu)
        (Or.inl (by omega))
  · funext k
    change (∑ i, fEntry (E i) k.val) = ∑ i, s i k
    have hE' (i : Fin r) := fEntry_add_card_missing (E i) k.val
    have hD' (i : Fin r) := fEntry_add_card_missing (D i) k.val
    simp only [heq] at hE'
    have h1 := Finset.sum_congr (s₁ := (univ : Finset (Fin r))) rfl (fun i _ => hE' i)
    have h2 := Finset.sum_congr (s₁ := (univ : Finset (Fin r))) rfl (fun i _ => hD' i)
    rw [Finset.sum_add_distrib, hMcount] at h1
    rw [Finset.sum_add_distrib] at h2
    have h3 : (∑ i, fEntry (D i) k.val) = ∑ i, s i k :=
      Finset.sum_congr rfl fun i _ => congrFun (hsD i) k
    omega

/-- This is the same surjection for the zero-extended sum read in absolute degrees. -/
theorem proper_sumset_zero_shift_surjOn (n r : ℕ) :
    Set.SurjOn (fun s : Fin r → FVector n => fun k : ℕ => ∑ i, extend (s i) k)
      {s | (∀ i, s i ∈ SnF n) ∧ Chained s}
      (extend '' properSumset n r) := by
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨s, hs, rfl⟩ := proper_sumset_surjOn n r hx
  exact ⟨s, hs, funext fun k => (extend_sumTuple s k).symm⟩

end D5.S3.Combinatorics.Kozlov
