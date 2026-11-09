/- GID: D5/S3/Combinatorics/CircularWords/ThreeSpecifiedDeletions
   generality: G
   mirror-B: D5/B/S3/Combinatorics/CircularWords/ThreeSpecifiedDeletions
   mirror-E: none(waiver:research-draft)
   anchors: []
   utility: none
   digest: Three preselected erasures reconstruct every supported nodup oriented circle. -/

import D5.S3.Combinatorics.CircularWords.DeletionReadoutReconstruction

/-! Exact reconstruction and sharp observation counts for actual supported oriented circles. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.CircularWords.ThreeSpecifiedDeletions
open CircularDeletionTransport CyclicInsertionGap DeletionReadoutReconstruction
universe u
variable {α : Type u} [DecidableEq α]

/-- A live auxiliary inference: three erasures distinguish linear words of any length,
including words with repeated letters. -/
private theorem list_three_erasures (S : Finset α) (hS : 3 ≤ S.card)
    {L K : List α}
    (h : ∀ x ∈ S, L.filter (fun y => decide (y ≠ x)) =
      K.filter (fun y => decide (y ≠ x))) : L = K := by
  induction L generalizing K with
  | nil =>
    cases K with
    | nil => rfl
    | cons k K =>
      obtain ⟨x, hxS, hxk⟩ : ∃ x ∈ S, x ≠ k := by
        by_contra hn
        have hs : S ⊆ {k} := by
          intro x hx
          by_contra hk
          exact hn ⟨x, hx, by simpa using hk⟩
        have hc := Finset.card_le_card hs
        simp only [Finset.card_singleton] at hc
        omega
      have he := h x hxS
      simp [Ne.symm hxk] at he
  | cons l L ih =>
    cases K with
    | nil =>
      obtain ⟨x, hxS, hxl⟩ : ∃ x ∈ S, x ≠ l := by
        by_contra hn
        have hs : S ⊆ {l} := by
          intro x hx
          by_contra hl
          exact hn ⟨x, hx, by simpa using hl⟩
        have hc := Finset.card_le_card hs
        simp only [Finset.card_singleton] at hc
        omega
      have he := h x hxS
      simp [Ne.symm hxl] at he
    | cons k K =>
      obtain ⟨x, hxS, hx⟩ : ∃ x ∈ S, x ∉ ({l,k} : Finset α) := by
        by_contra hn
        have hs : S ⊆ {l,k} := by
          intro x hx
          by_contra hk
          exact hn ⟨x, hx, hk⟩
        have hc := Finset.card_le_card hs
        have ht : ({l,k} : Finset α).card ≤ 2 := Finset.card_le_two
        omega
      have hlx : l ≠ x := by intro e; exact hx (by simp [e])
      have hkx : k ≠ x := by intro e; exact hx (by simp [e])
      have he := h x hxS
      simp only [List.filter_cons, decide_eq_true hlx, decide_eq_true hkx,
        ↓reduceIte, List.cons.injEq] at he
      have hlk : l = k := he.1
      subst l
      congr 1
      apply ih
      intro y hy
      have ht := h y hy
      by_cases hk : k = y
      · simpa [hk] using ht
      · simpa [hk] using ht

/-- Any three specified distinct labels suffice; the labels are fixed before seeing
C and D. Cycle is the rotation quotient and keeps orientation. -/
theorem reconstruct_three {A : Finset α} (hA : 4 ≤ A.card)
    {a b c : α} (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    {C D : Cycle α} (hC : C.Nodup) (hD : D.Nodup)
    (sC : C.toFinset = A) (sD : D.toFinset = A)
    (da : delete a C = delete a D) (db : delete b C = delete b D)
    (dc : delete c C = delete c D) : C = D := by
  let S : Finset α := {a,b,c}
  have hS : S.card = 3 := by simp [S, hab, hac, hbc]
  obtain ⟨r, hrA, hrS⟩ : ∃ r ∈ A, r ∉ S := by
    by_contra hn
    have hs : A ⊆ S := by
      intro r hr
      by_contra hs
      exact hn ⟨r, hr, hs⟩
    have := Finset.card_le_card hs
    omega
  have rC : r ∈ C := by
    have h : r ∈ C.toFinset := sC.symm ▸ hrA
    induction C using Quotient.inductionOn with
    | _ L => exact Cycle.mem_coe_iff.mpr (List.mem_toFinset.mp h)
  have rD : r ∈ D := by
    have h : r ∈ D.toFinset := sD.symm ▸ hrA
    induction D using Quotient.inductionOn with
    | _ L => exact Cycle.mem_coe_iff.mpr (List.mem_toFinset.mp h)
  obtain ⟨L, rfl⟩ := rooted rC
  obtain ⟨K, rfl⟩ := rooted rD
  have he : ∀ x ∈ S, delete x (r :: L : Cycle α) = delete x (r :: K : Cycle α) := by
    intro x hx
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact da
    · exact db
    · exact dc
  have hlk : L = K := by
    apply list_three_erasures S (by omega)
    intro x hx
    have hrx : r ≠ x := by intro e; exact hrS (by simpa [e] using hx)
    have hd := he x hx
    change (((r :: L).filter (fun y => decide (y ≠ x))) : Cycle α) =
      (((r :: K).filter (fun y => decide (y ≠ x))) : Cycle α) at hd
    simp only [List.filter_cons, decide_eq_true hrx, ↓reduceIte] at hd
    have hn : (r :: L.filter (fun y => decide (y ≠ x))).Nodup := by
      simpa only [List.filter_cons, decide_eq_true hrx, ↓reduceIte] using
        (Cycle.nodup_coe_iff.mp hC).filter (fun y => decide (y ≠ x))
    exact anchored_coe_injective hn hd
  apply reconstruct hA hC hD sC sD
  intro x hx
  rw [hlk]

/-- For every prescribed pair of distinct labels on the same fixed support,
two actual deletions fail to distinguish some distinct states. -/
theorem two_deletions_insufficient {A : Finset α} (hA : 4 ≤ A.card)
    {a b : α} (ha : a ∈ A) (hb : b ∈ A) (hab : a ≠ b) :
    ∃ C D : Cycle α, C.Nodup ∧ D.Nodup ∧ C.toFinset = A ∧ D.toFinset = A ∧
      C ≠ D ∧ delete a C = delete a D ∧ delete b C = delete b D := by
  obtain ⟨r, hrA, hr⟩ : ∃ r ∈ A, r ∉ ({a,b} : Finset α) := by
    by_contra hn
    have hs : A ⊆ {a,b} := by
      intro x hx
      by_contra ht
      exact hn ⟨x, hx, ht⟩
    have hh := Finset.card_le_card hs
    have ht : ({a,b} : Finset α).card ≤ 2 := Finset.card_le_two
    omega
  have hra : r ≠ a := by intro e; exact hr (by simp [e])
  have hrb : r ≠ b := by intro e; exact hr (by simp [e])
  let L := ((A.erase r).erase a |>.erase b).toList
  have memL (x : α) : x ∈ L ↔ x ∈ A ∧ x ≠ r ∧ x ≠ a ∧ x ≠ b := by
    simp only [L, Finset.mem_toList, Finset.mem_erase]
    tauto
  have hnC : (r :: a :: b :: L).Nodup := by
    simp [List.nodup_cons, L, Finset.mem_toList, Finset.mem_erase,
      hra, hrb, hab, Finset.nodup_toList]
  have hnD : (r :: b :: a :: L).Nodup := by
    simp [List.nodup_cons, L, Finset.mem_toList, Finset.mem_erase,
      hra, hrb, hab, Ne.symm hab, Finset.nodup_toList]
  have supC : (r :: a :: b :: L : Cycle α).toFinset = A := by
    ext x
    simp only [Cycle.coe_toFinset, List.toFinset_cons, Finset.mem_insert,
      List.mem_toFinset, memL]
    by_cases hxr : x = r <;> by_cases hxa : x = a <;> by_cases hxb : x = b <;>
      simp_all
  have supD : (r :: b :: a :: L : Cycle α).toFinset = A := by
    ext x
    simp only [Cycle.coe_toFinset, List.toFinset_cons, Finset.mem_insert,
      List.mem_toFinset, memL]
    by_cases hxr : x = r <;> by_cases hxa : x = a <;> by_cases hxb : x = b <;>
      simp_all
  refine ⟨(r :: a :: b :: L : Cycle α), (r :: b :: a :: L : Cycle α),
    Cycle.nodup_coe_iff.mpr hnC, Cycle.nodup_coe_iff.mpr hnD, supC, supD, ?_, ?_, ?_⟩
  · intro eq
    have ht := anchored_coe_injective hnC eq
    exact hab (List.cons.inj ht).1
  · change (((r :: a :: b :: L).filter (fun y => decide (y ≠ a))) : Cycle α) =
      (((r :: b :: a :: L).filter (fun y => decide (y ≠ a))) : Cycle α)
    simp [hra, Ne.symm hab]
  · change (((r :: a :: b :: L).filter (fun y => decide (y ≠ b))) : Cycle α) =
      (((r :: b :: a :: L).filter (fun y => decide (y ≠ b))) : Cycle α)
    simp [hrb, hab]

#check @list_three_erasures
#print axioms list_three_erasures
#check @reconstruct_three
#check @two_deletions_insufficient
#print axioms reconstruct_three
#print axioms two_deletions_insufficient
end D5.S3.Combinatorics.CircularWords.ThreeSpecifiedDeletions
