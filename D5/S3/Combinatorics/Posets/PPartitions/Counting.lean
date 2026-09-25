/- GID: D5/S3/Combinatorics/Posets/PPartitions/Counting
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Posets/PPartitions/Counting
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.Fintype.Powerset]
   utility: none
   digest: Chamber gap compression gives the all-bound labelled P-partition count. -/

import D5.S3.Combinatorics.Posets.PPartitions.Chambers
import Mathlib.Data.Fintype.Powerset

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Posets.PPartitions

open scoped BigOperators
noncomputable section

universe u

variable {α : Type u} [Fintype α] [PartialOrder α]

private def Increasing (n m : ℕ) := {f : Fin n → Fin m // StrictMono f}

private noncomputable instance (n m : ℕ) : Fintype (Increasing n m) :=
  Fintype.ofInjective (fun f => f.1) fun _ _ h => Subtype.ext h

private noncomputable def increasingEquivFinset (n m : ℕ) :
    Increasing n m ≃ {s : Finset (Fin m) // s.card = n} where
  toFun f := ⟨Finset.univ.image f.1, by
    rw [Finset.card_image_of_injective _ f.2.injective]
    simp⟩
  invFun s := ⟨s.1.orderEmbOfFin s.2, (s.1.orderEmbOfFin s.2).strictMono⟩
  left_inv f := by
    apply Subtype.ext
    exact (Finset.orderEmbOfFin_unique (by
      rw [Finset.card_image_of_injective _ f.2.injective]
      simp)
      (fun i => Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩) f.2).symm
  right_inv s := by
    apply Subtype.ext
    ext x
    simp

private def nonDescentBefore (ω : α → ℕ) (e : EnumeratingExtension α)
    (i : Fin (Fintype.card α)) : ℕ :=
  ((Finset.univ \ descentFinset ω e).filter fun k => k.val < i.val).card

private theorem nonDescentBefore_le_index (ω : α → ℕ) (e : EnumeratingExtension α)
    (i : Fin (Fintype.card α)) : nonDescentBefore ω e i ≤ i.val := by
  calc
    nonDescentBefore ω e i ≤ (Finset.range i.val).card := by
      apply Finset.card_le_card_of_injOn (fun k : Fin (Fintype.card α - 1) => k.val)
      · intro k hk
        have hk' : k ∈ ((Finset.univ \ descentFinset ω e).filter fun k => k.val < i.val) := hk
        rw [Finset.mem_filter] at hk'
        exact Finset.mem_range.mpr hk'.2
      · intro x hx y hy h
        exact Fin.ext h
    _ = i.val := Finset.card_range _

open Classical in
private theorem nonDescentBefore_succ (ω : α → ℕ) (e : EnumeratingExtension α)
    (i : Fin (Fintype.card α - 1)) :
    nonDescentBefore ω e ⟨i.val + 1, by omega⟩ =
      nonDescentBefore ω e ⟨i.val, by omega⟩ + if descent ω e i then 0 else 1 := by
  classical
  by_cases hd : descent ω e i
  · simp only [hd, if_true, add_zero]
    apply congrArg Finset.card
    ext x
    simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hx, hlt⟩
      exact ⟨hx, by
        have hne : x ≠ i := fun h => hx (by simpa [descentFinset, hd, h])
        omega⟩
    · rintro ⟨hx, hlt⟩
      exact ⟨hx, by omega⟩
  · simp only [hd, if_false]
    let A := (Finset.univ \ descentFinset ω e).filter fun k => k.val < i.val
    have hi : i ∈ Finset.univ \ descentFinset ω e := by
      simp [descentFinset, hd]
    have hi' : i ∉ descentFinset ω e := by simpa using hi
    have hEq : ((Finset.univ \ descentFinset ω e).filter fun k => k.val < i.val + 1) =
        insert i A := by
      ext k
      simp only [A, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and,
        Finset.mem_insert]
      constructor
      · rintro ⟨hk, hlt⟩
        by_cases hki : k = i
        · exact Or.inl hki
        · exact Or.inr ⟨hk, by omega⟩
      · rintro (rfl | ⟨hk, hlt⟩)
        · exact ⟨hi', by omega⟩
        · exact ⟨hk, by omega⟩
    rw [nonDescentBefore, nonDescentBefore, hEq, Finset.card_insert_of_notMem]
    simp [A]

private theorem index_le_of_strictMono {n m : ℕ} {f : Fin n → Fin m}
    (hf : StrictMono f) (i : Fin n) : i.val ≤ (f i).val := by
  have aux : ∀ k : ℕ, ∀ i : Fin n, i.val = k → k ≤ (f i).val := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro i hi
      by_cases hk : k = 0
      · omega
      · let j : Fin n := ⟨k - 1, by omega⟩
        have hjval : j.val < i.val := by
          change k - 1 < i.val
          omega
        have hj : j < i := Fin.mk_lt_mk.mpr hjval
        have hfj := hf hj
        have hprev := ih (k - 1) (by omega) j (by simp [j])
        omega
  exact aux i.val i rfl

private theorem strictMono_upper {n m : ℕ} {f : Fin n → Fin m}
    (hf : StrictMono f) (i : Fin n) : (f i).val + n ≤ m + i.val := by
  have aux : ∀ t : ℕ, ∀ i : Fin n, n - 1 - i.val = t →
      (f i).val + n ≤ m + i.val := by
    intro t
    induction t using Nat.strong_induction_on with
    | h t ih =>
      intro i hi
      by_cases hlast : i.val + 1 = n
      · omega
      · let j : Fin n := ⟨i.val + 1, by omega⟩
        have hij : i < j := Fin.mk_lt_mk.mpr (by simp [j])
        have hfj := hf hij
        have hnext := ih (n - 1 - j.val) (by simp [j]; omega) j (by simp [j])
        have hjval : j.val = i.val + 1 := rfl
        omega
  exact aux (n - 1 - i.val) i rfl

private theorem index_le_descent_add_nonDescent (ω : α → ℕ)
    (e : EnumeratingExtension α) (i : Fin (Fintype.card α)) :
    i.val ≤ descentCard ω e + nonDescentBefore ω e i := by
  classical
  let B : Finset (Fin (Fintype.card α - 1)) := Finset.univ.filter fun k => k.val < i.val
  have hB : B.card = i.val := by
    apply Finset.card_eq_of_bijective (fun k hk => (⟨k, by omega⟩ : Fin (Fintype.card α - 1)))
    · intro a ha
      have ha' : a.val < i.val := by simpa [B] using ha
      exact ⟨a.val, ha', Fin.ext rfl⟩
    · intro k hk
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩
    · intro x y hx hy hxy
      exact congrArg Fin.val hxy
  have hpart := Finset.card_filter_add_card_filter_not
    (s := B) (p := fun k => k ∈ descentFinset ω e)
  have hdesc : (B.filter fun k => k ∈ descentFinset ω e).card ≤ descentCard ω e := by
    exact Finset.card_le_card fun k hk => (Finset.mem_filter.mp hk).2
  have hnondesc : (B.filter fun k => k ∉ descentFinset ω e).card =
      nonDescentBefore ω e i := by
    apply congrArg Finset.card
    ext k
    simp [B, nonDescentBefore, and_comm]
  omega

private noncomputable def chamberToIncreasing (ω : α → ℕ) (e : EnumeratingExtension α)
    (q : ℕ) (hq : descentCard ω e ≤ q) :
    Chamber ω e (q + 1) → Increasing (Fintype.card α)
      (q + Fintype.card α - descentCard ω e) := fun s => by
  let f : Fin (Fintype.card α) → Fin (q + Fintype.card α - descentCard ω e) :=
    fun i => ⟨q - s.1 i + nonDescentBefore ω e i, by
      have hr : nonDescentBefore ω e i ≤
          Fintype.card α - 1 - descentCard ω e := by
        calc
          _ ≤ (Finset.univ \ descentFinset ω e).card :=
            Finset.card_le_card (Finset.filter_subset _ _)
          _ = _ := by rw [Finset.card_sdiff]; simp [descentCard]
      have hd : descentCard ω e ≤ Fintype.card α - 1 :=
        by simpa [descentCard] using (descentFinset ω e).card_le_univ
      have hN := i.isLt
      omega⟩
  refine ⟨f, ?_⟩
  by_cases hN : Fintype.card α = 0
  · intro i
    exact Fin.elim0 (Fin.cast hN i)
  · have hn : Fintype.card α - 1 + 1 = Fintype.card α := by omega
    have hg : StrictMono (fun i : Fin (Fintype.card α - 1 + 1) =>
        f (Fin.cast hn i)) := by
      apply Fin.strictMono_iff_lt_succ.mpr
      intro i
      have hi := i.isLt
      let i0 : Fin (Fintype.card α) := ⟨i.val, by omega⟩
      let i1 : Fin (Fintype.card α) := ⟨i.val + 1, by omega⟩
      have hs := s.2.1 (show i0 ≤ i1 by simp [i0, i1])
      have hr := nonDescentBefore_succ ω e i
      by_cases hd : descent ω e i
      · simp only [hd, if_true, add_zero] at hr
        have hstrict := s.2.2 i hd
        change q - s.1 i0 + nonDescentBefore ω e i0 <
          q - s.1 i1 + nonDescentBefore ω e i1
        simp only [i0, i1] at hs hstrict hr ⊢
        omega
      · simp only [hd, if_false] at hr
        change q - s.1 i0 + nonDescentBefore ω e i0 <
          q - s.1 i1 + nonDescentBefore ω e i1
        simp only [i0, i1] at hs hr ⊢
        omega
    convert hg.comp (Fin.cast_strictMono hn.symm) using 1
    funext i
    simp

private noncomputable def increasingToChamber (ω : α → ℕ) (e : EnumeratingExtension α)
    (q : ℕ) (hq : descentCard ω e ≤ q) :
    Increasing (Fintype.card α) (q + Fintype.card α - descentCard ω e) →
      Chamber ω e (q + 1) := fun f => by
  let s : Fin (Fintype.card α) → Fin (q + 1) := fun i =>
    ⟨q + nonDescentBefore ω e i - f.1 i, by
      have hlo := index_le_of_strictMono f.2 i
      have hr := nonDescentBefore_le_index ω e i
      omega⟩
  refine ⟨s, ?_, ?_⟩
  · by_cases hN : Fintype.card α = 0
    · intro i
      exact Fin.elim0 (Fin.cast hN i)
    · have hn : Fintype.card α - 1 + 1 = Fintype.card α := by omega
      have hg : Monotone (fun i : Fin (Fintype.card α - 1 + 1) =>
          OrderDual.toDual (s (Fin.cast hn i))) := by
        apply Fin.monotone_iff_le_succ.mpr
        intro i
        have hi := i.isLt
        let i0 : Fin (Fintype.card α) := ⟨i.val, by omega⟩
        let i1 : Fin (Fintype.card α) := ⟨i.val + 1, by omega⟩
        have hf := f.2 (show i0 < i1 by simp [i0, i1])
        have hlo0 := index_le_of_strictMono f.2 i0
        have hlo1 := index_le_of_strictMono f.2 i1
        have hup0 := strictMono_upper f.2 i0
        have hup1 := strictMono_upper f.2 i1
        have hidx0 := index_le_descent_add_nonDescent ω e i0
        have hidx1 := index_le_descent_add_nonDescent ω e i1
        have hr := nonDescentBefore_succ ω e i
        change q + nonDescentBefore ω e i1 - f.1 i1 ≤
          q + nonDescentBefore ω e i0 - f.1 i0
        simp only [i0, i1] at hf hlo0 hlo1 hup0 hup1 hidx0 hidx1 hr ⊢
        split at hr <;> omega
      change Monotone (fun i => OrderDual.toDual (s i))
      convert hg.comp (Fin.cast_strictMono hn.symm).monotone using 1
      funext i
      simp
  · intro i hd
    have hi := i.isLt
    let i0 : Fin (Fintype.card α) := ⟨i.val, by omega⟩
    let i1 : Fin (Fintype.card α) := ⟨i.val + 1, by omega⟩
    have hf := f.2 (show i0 < i1 by simp [i0, i1])
    have hlo0 := index_le_of_strictMono f.2 i0
    have hlo1 := index_le_of_strictMono f.2 i1
    have hup0 := strictMono_upper f.2 i0
    have hup1 := strictMono_upper f.2 i1
    have hidx0 := index_le_descent_add_nonDescent ω e i0
    have hidx1 := index_le_descent_add_nonDescent ω e i1
    have hr := nonDescentBefore_succ ω e i
    change q + nonDescentBefore ω e i1 - f.1 i1 <
      q + nonDescentBefore ω e i0 - f.1 i0
    simp only [i0, i1, hd, if_true, add_zero] at hf hlo0 hlo1 hup0 hup1 hidx0 hidx1 hr ⊢
    omega

private noncomputable def chamberIncreasingEquiv (ω : α → ℕ) (e : EnumeratingExtension α)
    (q : ℕ) (hq : descentCard ω e ≤ q) :
    Chamber ω e (q + 1) ≃ Increasing (Fintype.card α)
      (q + Fintype.card α - descentCard ω e) where
  toFun := chamberToIncreasing ω e q hq
  invFun := increasingToChamber ω e q hq
  left_inv s := by
    apply Subtype.ext
    funext i
    simp only [chamberToIncreasing, increasingToChamber]
    have hr := nonDescentBefore_le_index ω e i
    apply Fin.ext
    change q + nonDescentBefore ω e i -
      (q - s.1 i + nonDescentBefore ω e i) = s.1 i
    omega
  right_inv f := by
    apply Subtype.ext
    funext i
    simp only [chamberToIncreasing, increasingToChamber]
    have hlo := index_le_of_strictMono f.2 i
    have hr := nonDescentBefore_le_index ω e i
    have hup := strictMono_upper f.2 i
    have hidx := index_le_descent_add_nonDescent ω e i
    have hd : descentCard ω e ≤ Fintype.card α - 1 :=
      by simpa [descentCard] using (descentFinset ω e).card_le_univ
    apply Fin.ext
    change q - (q + nonDescentBefore ω e i - f.1 i) +
      nonDescentBefore ω e i = f.1 i
    omega

theorem chamber_card (ω : α → ℕ) (e : EnumeratingExtension α) (q : ℕ) :
    Fintype.card (Chamber ω e (q + 1)) =
      Nat.choose (q + Fintype.card α - descentCard ω e) (Fintype.card α) := by
  by_cases hq : descentCard ω e ≤ q
  · rw [Fintype.card_congr (chamberIncreasingEquiv ω e q hq)]
    rw [Fintype.card_congr (increasingEquivFinset _ _)]
    simpa using (Fintype.card_finset_len
      (α := Fin (q + Fintype.card α - descentCard ω e)) (Fintype.card α))
  · have hzero : Fintype.card (Chamber ω e (q + 1)) = 0 := by
      rw [Fintype.card_eq_zero_iff]
      constructor
      intro s
      let hinc := chamberToIncreasing ω e (descentCard ω e)
        (le_refl _) ⟨fun i => ⟨s.1 i, by omega⟩, s.2⟩
      have hlast : descentCard ω e ≤ Fintype.card α - 1 :=
        by simpa [descentCard] using (descentFinset ω e).card_le_univ
      have hN : 0 < Fintype.card α := by omega
      let i0 : Fin (Fintype.card α) := ⟨0, hN⟩
      have hM : descentCard ω e + Fintype.card α - descentCard ω e =
          Fintype.card α := by omega
      let g : Fin (Fintype.card α) → Fin (Fintype.card α) :=
        fun i => Fin.cast hM (hinc.1 i)
      have hg : StrictMono g := (Fin.cast_strictMono hM).comp hinc.2
      have hid := congrFun hg.eq_id i0
      have hz : nonDescentBefore ω e i0 = 0 := by
        simp [nonDescentBefore, i0]
      have hidval := congrArg Fin.val hid
      simp only [g, Fin.val_cast, id_eq, i0] at hidval
      have hincval : (hinc.1 i0).val =
          descentCard ω e - s.1 i0 + nonDescentBefore ω e i0 := rfl
      rw [hincval] at hidval
      omega
    rw [hzero, Nat.choose_eq_zero_of_lt]
    have hd : descentCard ω e ≤ Fintype.card α - 1 :=
      by simpa [descentCard] using (descentFinset ω e).card_le_univ
    omega

/-- The all-bound order-polynomial formula for injectively labelled finite posets. -/
theorem pPartition_card (ω : α → ℕ) (hω : Function.Injective ω) (q : ℕ) :
    Fintype.card (PPartition ω (q + 1)) =
      ∑ e : EnumeratingExtension α,
        Nat.choose (q + Fintype.card α - descentCard ω e) (Fintype.card α) := by
  rw [Fintype.card_congr (chamberEquiv ω hω), Fintype.card_sigma]
  exact Finset.sum_congr rfl fun e _ => chamber_card ω e q

end

end D5.S3.Combinatorics.Posets.PPartitions
