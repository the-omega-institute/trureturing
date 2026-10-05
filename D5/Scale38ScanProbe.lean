import D5.S3.Arith.FibonacciAtomic.RawEndpointPeeling

open D5.S3.Arith.FibonacciAtomic
open GenealogicalFiberTransport (Source)
open ActualTreeReadoutAcquisition (Address readout leaves vector chi)
open ActualJointResponseCostCore (survivors)
open RawEndpointPeeling (Peels)

set_option autoImplicit false

theorem safe_scan {m n : Nat} (F : Fin m → Source) (z : Fin m)
    (q : Nat → Address) (exit : Fin m → Nat)
    (leaf : ∀ t < n, q t ∈ leaves (F z) ∧ chi (readout (q t) (F z)) = 0)
    (before : ∀ i t, t < n → t < exit i → readout (q t) (F i) = readout (q t) (F z))
    (nonleaf : ∀ i, i ≠ z → exit i < n ∧ chi (readout (q (exit i)) (F i)) = 1)
    (unique : ∀ i j, i ≠ z → j ≠ z → exit i = exit j →
      readout (q (exit i)) (F i) = readout (q (exit j)) (F j) → i = j) :
    Peels F z Finset.univ ((List.range n).map q) := by
  classical
  let S := fun t : Nat => Finset.univ.filter (fun i => i = z ∨ t ≤ exit i)
  have loop : ∀ r t, t + r = n →
      Peels F z (S t) ((List.range' t r).map q) := by
    intro r
    induction r with
    | zero =>
      intro t ht i hi
      have hit : i = z ∨ t ≤ exit i := (Finset.mem_filter.mp hi).2
      apply Finset.mem_singleton.mpr
      rcases hit with hit | hit
      · exact hit
      · by_contra h
        have hlt := (nonleaf i h).1
        omega
    | succ r ih =>
      intro t ht
      have htn : t < n := by omega
      have target_zero := (leaf t htn).2
      have at_exit (i : Fin m) (hi : i ∈ S t)
          (y : ActualTreeReadoutAcquisition.Reply) (hy : chi y = 1)
          (hiy : readout (q t) (F i) = y) : i ≠ z ∧ exit i = t := by
        have hiz : i ≠ z := by
          intro h
          subst i
          rw [hiy, hy] at target_zero
          omega
        have hti : t ≤ exit i := ((Finset.mem_filter.mp hi).2).resolve_left hiz
        have he : exit i = t := by
          by_contra h
          have hb := before i t htn (by omega)
          rw [hiy] at hb
          have hc := congrArg chi hb
          rw [hy, target_zero] at hc
          omega
        exact ⟨hiz, he⟩
      have group (y : ActualTreeReadoutAcquisition.Reply) (hy : chi y = 1) :
          (survivors (S t) (vector F (q t)) y).card ≤ 1 := by
        apply Finset.card_le_one.mpr
        intro i hi j hj
        obtain ⟨his, hiy⟩ := Finset.mem_filter.mp hi
        obtain ⟨hjs, hjy⟩ := Finset.mem_filter.mp hj
        change readout (q t) (F i) = y at hiy
        change readout (q t) (F j) = y at hjy
        obtain ⟨hiz, hei⟩ := at_exit i his y hy hiy
        obtain ⟨hjz, hej⟩ := at_exit j hjs y hy hjy
        apply unique i j hiz hjz (hei.trans hej.symm)
        simpa only [hei, hej] using hiy.trans hjy.symm
      have next : survivors (S t) (vector F (q t)) (readout (q t) (F z)) = S (t+1) := by
        apply Finset.ext
        intro i
        change (i ∈ (Finset.univ.filter (fun j => j = z ∨ t ≤ exit j)).filter
          (fun j => readout (q t) (F j) = readout (q t) (F z))) ↔
          i ∈ Finset.univ.filter (fun j => j = z ∨ t+1 ≤ exit j)
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨hit, he⟩
          rcases hit with hit | hit
          · exact Or.inl hit
          · by_cases hiz : i = z
            · exact Or.inl hiz
            · right
              have hne : exit i ≠ t := by
                intro h
                have hn := (nonleaf i hiz).2
                rw [h, he, target_zero] at hn
                omega
              omega
        · intro hit
          rcases hit with hit | hit
          · subst i
            exact ⟨Or.inl rfl, rfl⟩
          · exact ⟨Or.inr (by omega), before i t htn (by omega)⟩
      rw [List.range'_succ, List.map_cons]
      change q t ∈ leaves (F z) ∧ _ ∧ _ ∧ _
      refine ⟨(leaf t htn).1, group .branch rfl, group .absent rfl, ?_⟩
      rw [next]
      exact ih (t+1) (by omega)
  simpa only [S, Nat.zero_le, or_true, Finset.filter_true, ← List.range_eq_range'] using
    loop n 0 (by omega)
