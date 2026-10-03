/- GID: D5/S1/Words/Permutations/MamedeExtremalOrientation
   generality: G
   mirror-B: D5/B/S1/Words/Permutations/MamedeExtremalOrientation
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Generator extrema force endpoint orientation for reduced consecutive words. -/

import D5.S1.Words.Permutations.MamedeCrossing
import Mathlib.Data.Finset.Max

namespace D5.S1.Words.Permutations.MamedeExtremalOrientation

open D5.S1.Words.Permutations.MamedeAdjacentWords
open D5.S1.Words.Permutations.MamedeCrossing
open D5.S1.Words.Permutations.MamedeGuardedWalk

theorem extremal_orientation (n : Nat) (w : List Nat)
    (hr : reducedWord n w) (hc : consecutive w) (hne : w ≠ []) :
    let σ := wordProduct n w
    ∃ m M, 1 ≤ m ∧ m ≤ M ∧ M ≤ n ∧ m ∈ w ∧ M ∈ w ∧
      (∀ k ∈ w, m ≤ k ∧ k ≤ M) ∧
      (∀ x : Fin (n + 1), x.val + 1 < m ∨ M + 1 < x.val + 1 → σ x = x) ∧
      ((σ (position n m) = position n (M + 1) ∧
        ∃ p q, w = p ++ descending M m ++ q ∧
          (∀ k ∈ p, k < M) ∧ (∀ k ∈ q, m < k)) ∨
       (σ (position n (M + 1)) = position n m ∧
        ∃ p q, w = p ++ ascending m M ++ q ∧
          (∀ k ∈ p, m < k) ∧ (∀ k ∈ q, k < M))) := by
  have hfin : w.toFinset.Nonempty := by simpa using hne
  let m := w.toFinset.min' hfin
  let M := w.toFinset.max' hfin
  have hm : m ∈ w := List.mem_toFinset.mp (Finset.min'_mem _ _)
  have hM : M ∈ w := List.mem_toFinset.mp (Finset.max'_mem _ _)
  have hb (k : Nat) (hk : k ∈ w) : m ≤ k ∧ k ≤ M :=
    ⟨Finset.min'_le _ k (List.mem_toFinset.mpr hk),
      Finset.le_max' _ k (List.mem_toFinset.mpr hk)⟩
  have hm1 := (hr.1 m hm).1
  have hMn := (hr.1 M hM).2
  have hmM := (hb m hm).2
  have pos_val (t : Nat) (ht : 1 ≤ t ∧ t ≤ n + 1) :
      (position n t).val = t - 1 := by
    simp [position, Nat.mod_eq_of_lt (show t - 1 < n + 1 by omega)]
  have exterior (v : List Nat) (hv : validWord n v)
      (hvb : ∀ k ∈ v, m ≤ k ∧ k ≤ M)
      (x : Fin (n + 1)) (hx : x.val + 1 < m ∨ M + 1 < x.val + 1) :
      wordProduct n v x = x := by
    induction v with
    | nil => simp [wordProduct]
    | cons k v ih =>
      have hk := hv k (by simp)
      have hkb := hvb k (by simp)
      have htail : wordProduct n v x = x := ih
        (fun l hl => hv l (by simp [hl]))
        (fun l hl => hvb l (by simp [hl]))
      have ha : x ≠ position n k := by
        intro h
        have := congrArg Fin.val h
        rw [pos_val k ⟨hk.1, by omega⟩] at this
        rcases hx with hx | hx <;> omega
      have hb' : x ≠ position n (k + 1) := by
        intro h
        have := congrArg Fin.val h
        rw [pos_val (k + 1) ⟨by omega, by omega⟩] at this
        rcases hx with hx | hx <;> omega
      change (adjacent n k * wordProduct n v) x = x
      rw [Equiv.Perm.mul_apply, htail]
      simpa [adjacent, position] using Equiv.swap_apply_of_ne_of_ne ha hb'
  refine ⟨m, M, hm1, hmM, hMn, hm, hM, hb, exterior w hr.1 hb, ?_⟩
  -- The endpoint of the largest strand is extracted from the permutation.
  have max_run (v : List Nat) (hvr : reducedWord n v) (hvc : consecutive v)
      (hvM : M ∈ v) (hvb : ∀ k ∈ v, m ≤ k ∧ k ≤ M) :
      ∃ i p q, m ≤ i ∧ i ≤ M ∧
        v = p ++ descending M i ++ q ∧
        (∀ k ∈ p, k < M) ∧ (∀ k ∈ q, i < k) ∧
        wordProduct n v (position n i) = position n (M + 1) := by
    let σ := wordProduct n v
    let x := σ⁻¹ (position n (M + 1))
    let i := x.val + 1
    have hi : 1 ≤ i ∧ i ≤ n + 1 := ⟨by dsimp [i]; omega, x.isLt⟩
    have hix : position n i = x := by
      apply Fin.ext
      rw [pos_val i hi]
      simp [i]
    have he : σ (position n i) = position n (M + 1) := by
      rw [hix]
      simp [x]
    have hib : m ≤ i ∧ i ≤ M + 1 := by
      by_contra! h
      have hout : i < m ∨ M + 1 < i := by omega
      have hfix := exterior v hvr.1 hvb x (by simpa [i] using hout)
      have hxval := congrArg Fin.val (hfix.symm.trans (by simpa [hix] using he))
      rw [pos_val (M + 1) ⟨by omega, by omega⟩] at hxval
      dsimp [i] at hout
      omega
    have guard : ∀ r : Fin (n + 1), r.val + 1 < i →
        (σ r).val < (position n (M + 1)).val := by
      intro r hri
      rw [pos_val (M + 1) ⟨by omega, by omega⟩]
      by_contra! hnot
      by_cases heq : (σ r).val = M
      · have heq' : σ r = position n (M + 1) := by
          apply Fin.ext
          simpa [pos_val (M + 1) ⟨by omega, by omega⟩] using heq
        have hri' := congrArg Fin.val (σ.injective (heq'.trans he.symm))
        rw [pos_val i hi] at hri'
        omega
      · have hfix := exterior v hvr.1 hvb (σ r) (Or.inr (by omega))
        have hrr : σ r = r := σ.injective hfix
        have := congrArg Fin.val hrr
        omega
    have walk := guarded_walk_endpoint n i (M + 1) (position n (M + 1)) v
      hi ⟨by omega, by omega⟩
      (by rw [pos_val (M + 1) ⟨by omega, by omega⟩]; omega)
      rfl hvr he guard
    have trace_hit (t : Nat) (u : List Nat) (htu : t ≤ M + 1) (hu : M ∈ u) :
        traceEnd t u ≤ M := by
      induction u generalizing t with
      | nil => simp at hu
      | cons k u ih =>
        rcases List.mem_cons.mp hu with rfl | hu
        · have hs : leftStep t M ≤ M := by unfold leftStep; split <;> omega
          exact (traceEnd_le (leftStep t M) u).trans hs
        · apply ih (leftStep t k) (by unfold leftStep; split <;> omega) hu
    have hiM : i ≤ M := by
      rw [← walk.2]
      exact trace_hit (M + 1) v (by omega) hvM
    obtain ⟨p, q, hv, hp, hq⟩ := forced_descent v i M hiM hvc walk.1 walk.2
    exact ⟨i, p, q, hib.1, hiM, hv, hp, hq, he⟩
  have rev_product (v : List Nat) : wordProduct n v.reverse = (wordProduct n v)⁻¹ := by
    simp only [wordProduct, List.map_reverse, List.prod_reverse_noncomm, List.map_map]
    congr 1
  have hrr : reducedWord n w.reverse := by
    refine ⟨fun k hk => hr.1 k (List.mem_reverse.mp hk), ?_⟩
    intro v hv he
    have he' : wordProduct n v.reverse = wordProduct n w := by
      rw [rev_product, he, rev_product, inv_inv]
    simpa using hr.2 v.reverse (fun k hk => hv k (List.mem_reverse.mp hk)) he'
  have chain (v : List Nat) :
      consecutive v ↔ v.IsChain (fun a b => a + 1 = b ∨ b + 1 = a) := by
    induction v with
    | nil => simp [consecutive]
    | cons a v ih => cases v <;> simp_all [consecutive, List.isChain_cons_cons]
  have hrc : consecutive w.reverse := by
    rw [chain, List.isChain_reverse]
    exact (chain w).mp hc |>.imp (fun _ _ h => h.symm)
  obtain ⟨i, p, q, hmi, hiM, hw, hp, hq, he⟩ := max_run w hr hc hM hb
  by_cases him : i = m
  · exact Or.inl ⟨him ▸ he, p, q, him ▸ hw, hp, him ▸ hq⟩
  obtain ⟨j, s, t, hmj, hjM, hwr, hs, ht, her⟩ := max_run w.reverse hrr hrc
    (List.mem_reverse.mpr hM) (fun k hk => hb k (List.mem_reverse.mp hk))
  have hjm : j = m := by
    by_contra hjm
    have hdesc (z : Nat) (hz : z ∈ descending M i) : i ≤ z := by
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hz
      have := List.mem_range.mp ha
      omega
    have hdesc' (z : Nat) (hz : z ∈ descending M j) : j ≤ z := by
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hz
      have := List.mem_range.mp ha
      omega
    have hmp : m ∈ p := by
      rw [hw] at hm
      simp only [List.mem_append] at hm
      rcases hm with (hm | hm) | hm
      · exact hm
      · have := hdesc m hm; omega
      · have := hq m hm; omega
    have hMdesc : M ∈ descending M i := by
      exact List.mem_map.mpr ⟨0, List.mem_range.mpr (by omega), by simp⟩
    have hnotm : m ∉ t.reverse ++ (descending M j).reverse := by
      intro h
      simp only [List.mem_append, List.mem_reverse] at h
      rcases h with h | h
      · have := ht m h; omega
      · have := hdesc' m h; omega
    have heq : p ++ (descending M i ++ q) =
        (t.reverse ++ (descending M j).reverse) ++ s.reverse := by
      rw [← List.append_assoc, ← hw]
      simpa [List.reverse_append, List.append_assoc] using congrArg List.reverse hwr
    have comp := List.append_eq_append_iff.mp heq
    rcases comp with ⟨u, hpre, hpost⟩ | ⟨u, hpre, hpost⟩
    · have : m ∈ t.reverse ++ (descending M j).reverse := by rw [hpre]; simp [hmp]
      exact hnotm this
    · have : M ∈ s.reverse := by
        rw [hpost]
        simp [hMdesc]
      have := hs M (List.mem_reverse.mp this)
      omega
  right
  have hinv : (wordProduct n w)⁻¹ (position n m) = position n (M + 1) := by
    simpa [rev_product, hjm] using her
  have := congrArg (wordProduct n w) hinv
  refine ⟨by simpa using this.symm, t.reverse, s.reverse, ?_, ?_, ?_⟩
  · have hasc : (descending M m).reverse = ascending m M := by
      unfold descending ascending
      apply List.ext_getElem
      · simp
      · intro r hr hr'
        have hrange : r < M - m + 1 := by simpa using hr'
        simp only [List.getElem_reverse, List.getElem_map, List.getElem_range,
          List.length_map, List.length_range]
        omega
    simpa [List.reverse_append, hjm, hasc, List.append_assoc] using
      congrArg List.reverse hwr
  · intro k hk
    simpa [hjm] using ht k (List.mem_reverse.mp hk)
  · intro k hk
    exact hs k (List.mem_reverse.mp hk)

#print axioms extremal_orientation

end D5.S1.Words.Permutations.MamedeExtremalOrientation
