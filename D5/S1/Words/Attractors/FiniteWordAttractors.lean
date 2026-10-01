/- GID: D5/S1/Words/Attractors/FiniteWordAttractors
   generality: G
   mirror-B: D5/B/S1/Words/Attractors/FiniteWordAttractors
   mirror-E: none(waiver:structural-word-proof)
   anchors: []
   utility: none
   digest: Unrestricted finite-word attractors, attained minima and factor transport. -/

import Mathlib

namespace D5.S1.Words.Attractors


/-- Every nonempty factor has an occurrence intersecting this same set of positions.
    Both occurrences are wholly inside the given finite word. -/
def IsAttractor {α : Type*} (w : List α) (S : Finset Nat) : Prop :=
  S ⊆ Finset.range w.length ∧
    ∀ (a l : Nat), 0 < l → a + l ≤ w.length →
      ∃ (b p : Nat), b + l ≤ w.length ∧ p ∈ S ∧ b ≤ p ∧ p < b + l ∧
        (w.drop a).take l = (w.drop b).take l

/-- The unrestricted attained minimum, defaulting to zero only if no set exists. -/
noncomputable def gamma {α : Type*} (w : List α) : Nat :=
  sInf {n : Nat | ∃ S : Finset Nat, IsAttractor w S ∧ S.card = n}

/-- The unrestricted minimum exists; singleton factors force the alphabet bound. -/
theorem attractor_minimum {α : Type*} [DecidableEq α] (w : List α) :
    (∃ S : Finset Nat, IsAttractor w S ∧ S.card = gamma w) ∧
      (∀ S : Finset Nat, IsAttractor w S → gamma w ≤ S.card) ∧
      w.toFinset.card ≤ gamma w := by
  classical
  have full : IsAttractor w (Finset.range w.length) := by
    refine ⟨Finset.Subset.refl _, ?_⟩
    intro a l hl hal
    exact ⟨a, a, hal, Finset.mem_range.mpr (by omega), le_rfl, by omega, rfl⟩
  have nonempty : {n : Nat | ∃ S : Finset Nat, IsAttractor w S ∧ S.card = n}.Nonempty :=
    ⟨w.length, Finset.range w.length, full, Finset.card_range _⟩
  have attained := Nat.sInf_mem nonempty
  have minimal (S : Finset Nat) (hS : IsAttractor w S) : gamma w ≤ S.card :=
    Nat.sInf_le ⟨S, hS, rfl⟩
  refine ⟨attained, minimal, ?_⟩
  obtain ⟨S, hS, hcard⟩ := attained
  by_cases hw : w = []
  · simp [hw]
  let letter (p : Nat) : α := w[p]?.getD (w.head hw)
  have cover : w.toFinset ⊆ S.image letter := by
    intro x hx
    obtain ⟨a, ha, hax⟩ := List.getElem_of_mem (List.mem_toFinset.mp hx)
    obtain ⟨b, p, hb, hp, hbp, hpb, heq⟩ := hS.2 a 1 (by omega) (by omega)
    have hpa : p = b := by omega
    subst p
    have hbl : b < w.length := by omega
    have hx' : w[b] = x := by
      have he := congrArg (fun xs : List α => xs[0]?) heq
      simpa [List.getElem?_eq_getElem, ha, hbl, hax] using he.symm
    apply Finset.mem_image.mpr
    exact ⟨b, hp, by simp [letter, hbl, hx']⟩
  calc
    w.toFinset.card ≤ (S.image letter).card := Finset.card_le_card cover
    _ ≤ S.card := Finset.card_image_le
    _ = gamma w := hcard

/-- An actual replacement window transports every factor inside the same word.
    The two reduction modes are periodic extension and a literal suffix-prefix copy. -/
theorem attractor_window_transfer {α : Type*} (w : List α)
    (N q p B : Nat) (S : Finset Nat)
    (hN : 0 < N) (hNw : N ≤ w.length)
    (hq : 0 < q) (hqp : q ≤ p) (hpN : p ≤ N)
    (hqB : q ≤ B) (hBN : B ≤ N - 1)
    (hwindow : (w.drop (p - q)).take B = w.take B)
    (hwindow_bound : p - q + B ≤ w.length)
    (hold : IsAttractor (w.take (N - 1)) S)
    (hqS : q - 1 ∈ S)
    (hcut : B = N - 1 ∨ B ∈ S.erase (q - 1))
    (hreduce : (p = N ∧ List.HasPeriod w N) ∨ w.drop p <+: w.take B) :
    IsAttractor w (insert (p - 1) (S.erase (q - 1))) ∧
      (insert (p - 1) (S.erase (q - 1))).card ≤ S.card := by
  classical
  have hplen : 0 < p := hq.trans_le hqp
  have oldlen : (w.take (N - 1)).length = N - 1 := by
    simp only [List.length_take, Nat.min_eq_left (by omega : N - 1 ≤ w.length)]
  have cutlen : (w.take B).length = B := by
    simp only [List.length_take, Nat.min_eq_left (by omega : B ≤ w.length)]
  have slice_take (a l t : Nat) (hat : a + l ≤ t) :
      ((w.take t).drop a).take l = (w.drop a).take l := by
    rw [List.drop_take, List.take_take]
    have hlt : l ≤ t - a := by omega
    simp only [Nat.min_eq_left hlt]
  have slice_prefix (u v : List α) (h : u <+: v) (a l : Nat)
      (hau : a + l ≤ u.length) : (u.drop a).take l = (v.drop a).take l := by
    apply ((h.drop a).take l).eq_of_length
    have hv := h.length_le
    simp only [List.length_take, List.length_drop]
    rw [Nat.min_eq_left (by omega : l ≤ u.length - a),
      Nat.min_eq_left (by omega : l ≤ v.length - a)]
  have reduced (a l : Nat) (hal : a + l ≤ w.length) :
      ∃ b, b + l ≤ w.length ∧ (w.drop a).take l = (w.drop b).take l ∧
        ((b ≤ p - 1 ∧ p - 1 < b + l) ∨ b + l ≤ N - 1) := by
    rcases hreduce with ⟨hp, hper⟩ | hsuffix
    · let b := a % N
      have hb : b < N := Nat.mod_lt _ hN
      have hba : b ≤ a := Nat.mod_le _ _
      have hbl : b + l ≤ w.length := by omega
      have heq : (w.drop a).take l = (w.drop b).take l := by
        apply List.ext_getElem?
        intro i
        simp only [List.getElem?_take, List.getElem?_drop]
        split_ifs with hi
        · rw [← hper.getElem?_mod N (a + i) w (by omega),
            ← hper.getElem?_mod N (b + i) w (by omega)]
          dsimp [b]
          rw [Nat.mod_add_mod]
        · rfl
      refine ⟨b, hbl, heq, ?_⟩
      by_cases hcross : N - 1 < b + l
      · left; subst p; omega
      · right; omega
    · by_cases hcross : a ≤ p - 1 ∧ p - 1 < a + l
      · exact ⟨a, hal, rfl, Or.inl hcross⟩
      by_cases hleft : a + l ≤ p - 1
      · exact ⟨a, hal, rfl, Or.inr (by omega)⟩
      have hpa : p ≤ a := by omega
      have hslen := hsuffix.length_le
      simp only [List.length_drop, cutlen] at hslen
      have hcutbound : a - p + l ≤ B := by omega
      refine ⟨a - p, by omega, ?_, Or.inr (by omega)⟩
      calc
        (w.drop a).take l = ((w.drop p).drop (a - p)).take l := by
          rw [List.drop_drop, Nat.add_sub_of_le hpa]
        _ = ((w.take B).drop (a - p)).take l :=
          slice_prefix _ _ hsuffix _ _ (by simp only [List.length_drop]; omega)
        _ = (w.drop (a - p)).take l := slice_take _ _ _ hcutbound
  have valid : insert (p - 1) (S.erase (q - 1)) ⊆ Finset.range w.length := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact Finset.mem_range.mpr (by omega)
    · have hxold := hold.1 (Finset.mem_of_mem_erase hx)
      rw [Finset.mem_range, oldlen] at hxold
      exact Finset.mem_range.mpr (by omega)
  refine ⟨⟨valid, ?_⟩, ?_⟩
  · intro a l hl hal
    obtain ⟨a', ha', heq, hcross | hshort⟩ := reduced a l hal
    · exact ⟨a', p - 1, ha', Finset.mem_insert_self _ _, hcross.1, hcross.2, heq⟩
    have haold : a' + l ≤ (w.take (N - 1)).length := by omega
    obtain ⟨b, x, hb, hx, hbx, hxb, heold⟩ := hold.2 a' l hl haold
    have hb' : b + l ≤ N - 1 := by omega
    have he : (w.drop a).take l = (w.drop b).take l := by
      calc
        (w.drop a).take l = (w.drop a').take l := heq
        _ = ((w.take (N - 1)).drop a').take l := (slice_take _ _ _ hshort).symm
        _ = ((w.take (N - 1)).drop b).take l := heold
        _ = (w.drop b).take l := slice_take _ _ _ hb'
    by_cases hret : ∃ y ∈ S.erase (q - 1), b ≤ y ∧ y < b + l
    · obtain ⟨y, hy, hby, hyb⟩ := hret
      exact ⟨b, y, by omega, Finset.mem_insert_of_mem hy, hby, hyb, he⟩
    have hxq : x = q - 1 := by
      by_contra hne
      exact hret ⟨x, Finset.mem_erase.mpr ⟨hne, hx⟩, hbx, hxb⟩
    subst x
    have hbB : b + l ≤ B := by
      rcases hcut with hcut | hcut
      · omega
      · by_contra hnot
        exact hret ⟨B, hcut, by omega, by omega⟩
    have transport : (w.drop b).take l = (w.drop (p - q + b)).take l := by
      have hw := congrArg (fun v : List α => (v.drop b).take l) hwindow
      rw [List.drop_take, List.drop_drop, List.take_take,
        Nat.min_eq_left (by omega : l ≤ B - b)] at hw
      exact (slice_take b l B hbB).symm.trans hw.symm
    refine ⟨p - q + b, p - 1, by omega, Finset.mem_insert_self _ _, by omega,
      by omega, he.trans transport⟩
  · have hscard : 0 < S.card := Finset.card_pos.mpr ⟨q - 1, hqS⟩
    have hi := Finset.card_insert_le (p - 1) (S.erase (q - 1))
    rw [Finset.card_erase_of_mem hqS] at hi
    omega

/-- Periodic extension adds one original position to an attractor of the interior. -/
theorem periodic_attractor_extension {α : Type*} (w : List α) (N : Nat) (S : Finset Nat)
    (hN : 0 < N) (hNw : N ≤ w.length) (hper : List.HasPeriod w N)
    (hold : IsAttractor (w.take (N - 1)) S) :
    IsAttractor w (insert (N - 1) S) := by
  classical
  have oldlen : (w.take (N - 1)).length = N - 1 := by
    simp only [List.length_take, Nat.min_eq_left (by omega : N - 1 ≤ w.length)]
  refine ⟨?_, ?_⟩
  · intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact Finset.mem_range.mpr (by omega)
    · have hx' := hold.1 hx
      rw [Finset.mem_range, oldlen] at hx'
      exact Finset.mem_range.mpr (by omega)
  · intro a l hl hal
    let b := a % N
    have hb : b < N := Nat.mod_lt _ hN
    have hba : b ≤ a := Nat.mod_le _ _
    have hbl : b + l ≤ w.length := by omega
    have heq : (w.drop a).take l = (w.drop b).take l := by
      apply List.ext_getElem?
      intro i
      simp only [List.getElem?_take, List.getElem?_drop]
      split_ifs with hi
      · rw [← hper.getElem?_mod N (a + i) w (by omega),
          ← hper.getElem?_mod N (b + i) w (by omega)]
        dsimp [b]
        rw [Nat.mod_add_mod]
      · rfl
    by_cases hcross : N - 1 < b + l
    · exact ⟨b, N - 1, hbl, Finset.mem_insert_self _ _, by omega, hcross, heq⟩
    have hshort : b + l ≤ N - 1 := by omega
    obtain ⟨t, p, ht, hp, htp, hpt, heold⟩ := hold.2 b l hl (by omega)
    have ht' : t + l ≤ N - 1 := by omega
    have he : (w.drop b).take l = (w.drop t).take l := by
      have hbTake : ((w.take (N - 1)).drop b).take l = (w.drop b).take l := by
        rw [List.drop_take, List.take_take, Nat.min_eq_left (by omega : l ≤ N - 1 - b)]
      have htTake : ((w.take (N - 1)).drop t).take l = (w.drop t).take l := by
        rw [List.drop_take, List.take_take, Nat.min_eq_left (by omega : l ≤ N - 1 - t)]
      rw [hbTake, htTake] at heold
      exact heold
    exact ⟨t, p, by omega, Finset.mem_insert_of_mem hp, htp, hpt, heq.trans he⟩

end D5.S1.Words.Attractors
