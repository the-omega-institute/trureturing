/- GID: D5/S1/Words/Permutations/MamedeNonoscSourceEndpoints
   generality: G
   mirror-B: D5/B/S1/Words/Permutations/MamedeNonoscSourceEndpoints
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Nonoscillating first-orientation words have strict interior source endpoints. -/

import D5.S1.Words.Permutations.MamedeEndpointUniqueness

namespace D5.S1.Words.Permutations.MamedeNonoscSourceEndpoints

open D5.S1.Words.Permutations.MamedeAdjacentWords
open D5.S1.Words.Permutations.MamedeCrossing
open D5.S1.Words.Permutations.MamedeGuardedWalk
open D5.S1.Words.Permutations.MamedeEndpointUniqueness

/-- An attained first-orientation extremal map yields both strict interior
    strands, without assuming a source shape or either remaining map. -/
theorem first_orientation_strict_endpoints (n m M : Nat)
    (σ : Equiv.Perm (Fin (n + 1))) (a : List Nat)
    (ha : singletonWord n σ a) (hmem : m ∈ a) (hMem : M ∈ a)
    (hm : 1 ≤ m) (hmM : m ≤ M) (hMn : M ≤ n)
    (hb : ∀ k ∈ a, m ≤ k ∧ k ≤ M)
    (hmax : σ (position n (M + 1)) = position n m)
    (hnon : ¬ oscillation a) :
    m < M ∧ ∃ i j, m < i ∧ i < M ∧ m < j ∧ j < M ∧
      σ (position n m) = position n (j + 1) ∧
      σ (position n i) = position n (M + 1) ∧
      (∀ x : Fin (n + 1),
        x.val + 1 < m ∨ M + 1 < x.val + 1 → σ x = x) := by
  have hlt : m < M := by
    by_contra h
    have heq : m = M := by omega
    cases a with
    | nil => simp at hmem
    | cons k a =>
      have hk : k = m := by have := hb k (by simp); omega
      apply hnon
      apply extremal_endpoint_oscillation n m (k :: a) ha.1 ha.2.1
      · exact Or.inl (by simp [hk])
      · exact Or.inr (fun t ht => (hb t ht).1)
  obtain ⟨lo, hi, _, _, _, hlo, hhi, hbounds, hfixed, _⟩ :=
    D5.S1.Words.Permutations.MamedeExtremalOrientation.extremal_orientation
      n a ha.1 ha.2.1 (by intro he; simp [he] at hmem)
  have hlo_eq : lo = m := by
    have := hb lo hlo
    have := hbounds m hmem
    omega
  have hhi_eq : hi = M := by
    have := hb hi hhi
    have := hbounds M hMem
    omega
  subst lo
  subst hi
  have hfixedσ : ∀ x : Fin (n + 1),
      x.val + 1 < m ∨ M + 1 < x.val + 1 → σ x = x := by
    simpa [ha.2.2] using hfixed
  have pos_val (t : Nat) (ht : 1 ≤ t ∧ t ≤ n + 1) :
      (position n t).val = t - 1 := by
    simp [position, Nat.mod_eq_of_lt (show t - 1 < n + 1 by omega)]
  let x := σ⁻¹ (position n (M + 1))
  let i := x.val + 1
  have hi : 1 ≤ i ∧ i ≤ n + 1 := ⟨by dsimp [i]; omega, x.isLt⟩
  have hix : position n i = x := by
    apply Fin.ext
    rw [pos_val i hi]
    simp [i]
  have himap : σ (position n i) = position n (M + 1) := by
    rw [hix]
    simp [x]
  have hib : m ≤ i ∧ i ≤ M + 1 := by
    by_contra! h
    have hout : i < m ∨ M + 1 < i := by omega
    have hfix := hfixedσ x (by simpa [i] using hout)
    have hv := congrArg Fin.val (hfix.symm.trans (by simpa [hix] using himap))
    rw [pos_val (M + 1) ⟨by omega, by omega⟩] at hv
    dsimp [i] at hout
    omega
  have hiM : i ≤ M := by
    by_contra h
    have hieq : i = M + 1 := by omega
    have hsame : σ (position n (M + 1)) = position n (M + 1) := by
      simpa [hieq] using himap
    have hv := congrArg Fin.val (hsame.symm.trans hmax)
    rw [pos_val (M + 1) ⟨by omega, by omega⟩,
      pos_val m ⟨hm, by omega⟩] at hv
    omega
  have hmi : m < i := by
    by_contra h
    have hieq : i = m := by omega
    have hmin : σ (position n m) = position n (M + 1) := hieq ▸ himap
    exact hnon (opposite_extremal_maps_oscillation n m M σ a ha hmem hMem
      hm hmM hMn hb hmax hmin)
  have hguard_i : ∀ r : Fin (n + 1), r.val + 1 < i →
      (σ r).val < (position n (M + 1)).val := by
    intro r hri
    rw [pos_val (M + 1) ⟨by omega, by omega⟩]
    by_contra! hnot
    by_cases heq : (σ r).val = M
    · have heq' : σ r = position n (M + 1) := by
        apply Fin.ext
        simpa [pos_val (M + 1) ⟨by omega, by omega⟩] using heq
      have hri' := congrArg Fin.val (σ.injective (heq'.trans himap.symm))
      rw [pos_val i hi] at hri'
      omega
    · have hfix := hfixedσ (σ r) (Or.inr (by omega))
      have hrr : σ r = r := σ.injective hfix
      have := congrArg Fin.val hrr
      omega
  have hwalk_i := guarded_walk_endpoint n i (M + 1) (position n (M + 1)) a
    hi ⟨by omega, by omega⟩
    (by rw [pos_val (M + 1) ⟨by omega, by omega⟩]; omega)
    rfl ha.1 (by simpa [ha.2.2] using himap)
    (by simpa [ha.2.2] using hguard_i)
  have hiLt : i < M := by
    by_contra h
    have hieq : i = M := by omega
    obtain ⟨p, q, hword, hp, hq⟩ :=
      forced_descent a i M hiM ha.2.1 hwalk_i.1 hwalk_i.2
    have hqnil : q = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro k hk
      have := hq k hk
      have : k ∈ a := by rw [hword]; simp [hk]
      have := (hb k this).2
      omega
    have hend : a.getLast? = some M := by
      rw [hword, hieq, hqnil]
      simp [descending]
    exact hnon (extremal_endpoint_oscillation n M a ha.1 ha.2.1
      (Or.inr hend) (Or.inl (fun t ht => (hb t ht).2)))
  let y := σ (position n m)
  let j := y.val
  have hypos : position n (j + 1) = y := by
    apply Fin.ext
    rw [pos_val (j + 1) ⟨by omega, by dsimp [j, y]; omega⟩]
    simp [j]
  have hjmap : σ (position n m) = position n (j + 1) := hypos.symm
  have hyb : m ≤ j + 1 ∧ j + 1 ≤ M + 1 := by
    by_contra! h
    have hout : j + 1 < m ∨ M + 1 < j + 1 := by omega
    have hfix := hfixedσ y (by simpa [j] using hout)
    have heq : y = position n m := σ.injective (hfix.trans (by rfl))
    have hv := congrArg Fin.val heq
    rw [pos_val m ⟨hm, by omega⟩] at hv
    dsimp [j] at hout
    omega
  have hjM : j < M := by
    by_contra h
    have hjeq : j + 1 = M + 1 := by omega
    have hmin : σ (position n m) = position n (M + 1) := by
      rw [hjmap, hjeq]
    exact hnon (opposite_extremal_maps_oscillation n m M σ a ha hmem hMem
      hm hmM hMn hb hmax hmin)
  have hmj : m ≤ j := by
    by_contra h
    have hjeq : j + 1 = m := by omega
    have he : σ (position n m) = position n m := by rw [hjmap, hjeq]
    have hmeq := σ.injective (he.trans hmax.symm)
    have hv := congrArg Fin.val hmeq
    rw [pos_val m ⟨hm, by omega⟩, pos_val (M + 1) ⟨by omega, by omega⟩] at hv
    omega
  have hmj' : m < j := by
    by_contra h
    have hjeq : j = m := by omega
    have hguard_m : ∀ r : Fin (n + 1), r.val + 1 < m →
        (σ r).val < (position n (m + 1)).val := by
      intro r hr
      have hfix : σ r = r := hfixedσ r (Or.inl hr)
      rw [hfix, pos_val (m + 1) ⟨by omega, by omega⟩]
      omega
    have hwalk_m := guarded_walk_endpoint n m (m + 1) (position n (m + 1)) a
      ⟨hm, by omega⟩ ⟨by omega, by omega⟩
      (by rw [pos_val (m + 1) ⟨by omega, by omega⟩]; omega)
      rfl ha.1 (by simpa [ha.2.2, hjeq] using hjmap)
      (by simpa [ha.2.2] using hguard_m)
    obtain ⟨p, q, hword, hp, hq⟩ :=
      forced_descent a m m (by omega) ha.2.1 hwalk_m.1 hwalk_m.2
    have hpnil : p = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro k hk
      have := hp k hk
      have hka : k ∈ a := by rw [hword]; simp [hk]
      have := (hb k hka).1
      omega
    have hstart : a.head? = some m := by
      rw [hword, hpnil]
      simp [descending]
    exact hnon (extremal_endpoint_oscillation n m a ha.1 ha.2.1
      (Or.inl hstart) (Or.inr (fun t ht => (hb t ht).1)))
  exact ⟨hlt, i, j, hmi, hiLt, hmj', hjM, hjmap, himap, hfixedσ⟩

#print axioms first_orientation_strict_endpoints

end D5.S1.Words.Permutations.MamedeNonoscSourceEndpoints
