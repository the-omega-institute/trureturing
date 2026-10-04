/- GID: D5/S3/Combinatorics/Scarf/Incidence
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Scarf/Incidence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Convex.StdSimplex]
   utility: none
   digest: Maximal points in the disjoint M sets construct and exhaust two distinct incident rooms in all four branches. -/
/- proof_shape: internal_door_two_rooms: content
   admission_basis: escape-witness
   escape_witness: Maximal points in the disjoint M sets construct and exhaust two distinct incident rooms in all four branches.
   Source: https://github.com/math-xmum/Brouwer/blob/f9dc162170e8711f78059a87edcd38ffc44a1bfb/Gametheory/Scarf.lean
   No mathematical novelty claim. -/
/-
MIT License

Copyright (c) 2025 Math_XMUM

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

import D5.S3.Combinatorics.Scarf.Dominance
open Classical Finset
set_option quotPrecheck false
namespace D5.S3.Combinatorics.Scarf
variable {T : Type*} {I : Type*} [Inhabited T] [DecidableEq T] [DecidableEq I]
variable [IST : IndexedLOrder I T]
local notation lhs "<[" i "]" rhs => (IST.IST i).lt lhs rhs
local notation lhs "≤[" i "]" rhs => (IST.IST i).le lhs rhs
namespace IndexedLOrder
theorem internal_door_two_rooms [Fintype T] (τ : Finset T) (D : Finset I)
    (h_int_door : IST.isInternalDoor τ D) :
    ∃ (σ₁ σ₂ : Finset T) (C₁ C₂ : Finset I),
      (σ₁, C₁) ≠ (σ₂, C₂) ∧
      IST.isRoom σ₁ C₁ ∧
      IST.isRoom σ₂ C₂ ∧
      isDoorof τ D σ₁ C₁ ∧
      isDoorof τ D σ₂ C₂ ∧
      (∀ σ C, IST.isRoom σ C → isDoorof τ D σ C →
       (σ = σ₁ ∧ C = C₁) ∨ (σ = σ₂ ∧ C = C₂)) := by
  classical
  let maxAt (τ : Finset T) (D : Finset I) (i : I) (h_nonempty : τ.Nonempty)
      (h : (M_set τ D i h_nonempty).Nonempty) : T :=
    @Finset.max' T (IST.IST i) (M_set τ D i h_nonempty).toFinset
      (Set.toFinset_nonempty.mpr h)
  let minAt {σ : Finset T} (h2 : σ.Nonempty) (i : I) : T :=
    @Finset.min' T (IST.IST i) σ h2
  have keylemma_of_dominant {σ : Finset T} {C: Finset I} (h1 : IST.isDominant σ C) (h2: σ.Nonempty): σ  = C.image (minAt h2)  :=
    by
      ext a
      constructor
      · intro ha
        rw [mem_image]
        by_contra  hm
        push Not at hm
        obtain ⟨i,hi1,hi2⟩ := h1 a
        replace hm := hm i hi1
        dsimp [minAt] at hm
        have ha1 := @Finset.le_min' _ (IST.IST i) _ h2 a hi2
        have ha2 := @Finset.min'_le _ (IST.IST i) _ _ ha
        apply hm
        refine @eq_of_le_of_ge _ (IST.IST i).toPartialOrder _ _ ha2 ha1
      · suffices h: ∀ x ∈ C, minAt h2 x = a → a ∈ σ from
        by simp;exact h
        intro _ _ ha
        simp [minAt,<-ha,Finset.min'_mem]
  have m_element_is_maximal (τ : Finset T) (D : Finset I) (i : I) (h_nonempty : τ.Nonempty)
      (h : (M_set τ D i h_nonempty).Nonempty) :
      is_maximal_in_M_set τ D i h_nonempty (maxAt τ D i h_nonempty h) := by
    unfold is_maximal_in_M_set maxAt
    let s_finset := (M_set τ D i h_nonempty).toFinset
    have h_nonempty_finset: s_finset.Nonempty := Set.toFinset_nonempty.mpr h
    constructor
    · rw [←Set.mem_toFinset]
      exact @Finset.max'_mem _ (IST.IST i) s_finset h_nonempty_finset
    · intros y hy
      rw [←Set.mem_toFinset] at hy
      apply @Finset.le_max' _ (IST.IST i)
      exact hy
  have mini_insert_eq_old_or_new (τ : Finset T) (h_nonempty : τ.Nonempty)
      (x : T) (i : I) :
      minAt (Finset.insert_nonempty x τ) i = minAt h_nonempty i ∨
        minAt (Finset.insert_nonempty x τ) i = x := by
    let := IST.IST i
    change (insert x τ).min' _ = τ.min' h_nonempty ∨ (insert x τ).min' _ = x
    have hmin : (insert x τ).min' (Finset.insert_nonempty x τ) =
        min x (τ.min' h_nonempty) := by
      convert (@Finset.min'_insert T (IST.IST i) x τ h_nonempty) using 1
      apply le_antisymm
      · apply Finset.le_min'
        intro y hy
        apply Finset.min'_le
        simpa using hy
      · apply Finset.le_min'
        intro y hy
        apply Finset.min'_le
        simpa using hy
    rw [hmin]
    rcases le_total x (τ.min' h_nonempty) with h | h
    · exact Or.inr (min_eq_left h)
    · exact Or.inl (min_eq_right h)
  have isDominant_insert_iff_maximal_in_M_set
      (τ : Finset T) (D : Finset I) (x : T)
      (h_door : IST.isDoor τ D) (h_nonempty : τ.Nonempty) (h_not_mem : x ∉ τ)
      (a b : I) (ha : a ∈ D) (hb : b ∈ D) (hab : a ≠ b)
      (h_eq : minAt h_nonempty a = minAt h_nonempty b) :
      IST.isDominant (insert x τ) D ↔
      (∃ i ∈ ({a, b} : Finset I), (M_set τ D i h_nonempty).Nonempty ∧
       is_maximal_in_M_set τ D i h_nonempty x) := by
    constructor
    · intro h_dominant
      have h_insert_nonempty : (insert x τ).Nonempty := Finset.insert_nonempty x τ
      have h_min_eq_image : D.image (minAt h_insert_nonempty) = insert x τ := by
        convert (keylemma_of_dominant h_dominant h_insert_nonempty).symm
      have h_x_is_min : ∃ i ∈ D, minAt h_insert_nonempty i = x := by
        have h_x_in_image : x ∈ D.image (minAt h_insert_nonempty) := by
          rw [h_min_eq_image]
          exact Finset.mem_insert_self x τ
        exact Finset.mem_image.mp h_x_in_image
      obtain ⟨i, hi_mem, hi_eq⟩ := h_x_is_min
      have h_is_room : isRoom (insert x τ) D := by
        unfold isRoom
        constructor
        · exact h_dominant
        · rw [Finset.card_insert_of_notMem h_not_mem, h_door.2]
      have h_inj_insert : Set.InjOn (minAt h_insert_nonempty) (D : Set I) := by
        apply Finset.injOn_of_card_image_eq
        rw [h_min_eq_image, h_is_room.2]
      have h_mini_lt_x : ∀ k ∈ D, k ≠ i → minAt h_nonempty k <[k] x := by
        intros k hk_mem hk_ne_i
        have h_mini_cases :
            minAt h_insert_nonempty k = minAt h_nonempty k ∨ minAt h_insert_nonempty k = x := by
          simpa only using mini_insert_eq_old_or_new τ h_nonempty x k
        have h_mini_neq_x : minAt h_insert_nonempty k ≠ x := by
          intro h_eq
          have h_inj : Set.InjOn (minAt h_insert_nonempty) (D : Set I) := h_inj_insert
          have hi_mem_D : i ∈ D := hi_mem
          have hk_mem_D : k ∈ D := hk_mem
          have h_mini_i_eq_x : minAt h_insert_nonempty i = x := hi_eq
          exact hk_ne_i (h_inj hi_mem_D hk_mem_D (h_mini_i_eq_x.trans h_eq.symm)).symm
        let := IST.IST k
        have h_mini_eq_k : minAt h_insert_nonempty k = minAt h_nonempty k := by
          cases h_mini_cases with
          | inl h => exact h
          | inr h => exact absurd h h_mini_neq_x
        apply lt_of_le_of_ne
        · have h_le : minAt h_insert_nonempty k ≤[k] x := by
            apply @Finset.min'_le _ (IST.IST k)
            exact Finset.mem_insert_self x τ
          rw [h_mini_eq_k] at h_le
          exact h_le
        · exact fun h_eq_x => h_not_mem (h_eq_x ▸ Finset.min'_mem τ h_nonempty)
      have h_x_le_mini_i : x ≤[i] minAt h_nonempty i := by
        let := IST.IST i
        rw [← hi_eq]
        unfold minAt
        apply Finset.min'_le
        · exact Finset.mem_insert_of_mem (Finset.min'_mem _ h_nonempty)
      have h_i_in_ab : i ∈ ({a, b} : Finset I) := by
        by_cases hik : i = a ∨ i = b
        · simp [hik]
        · push Not at hik
          obtain ⟨hia, hib⟩ := hik
          have h_mini_eq_for_ne_i : ∀ k ∈ D, k ≠ i → minAt h_insert_nonempty k = minAt h_nonempty k := by
            intros k hk_mem hk_ne_i
            have h_cases :
                minAt h_insert_nonempty k = minAt h_nonempty k ∨ minAt h_insert_nonempty k = x := by
              simpa only using mini_insert_eq_old_or_new τ h_nonempty x k
            have h_mini_neq_x : minAt h_insert_nonempty k ≠ x := by
              intro h_eq_k_x
              exact hk_ne_i (h_inj_insert hk_mem hi_mem (h_eq_k_x.trans hi_eq.symm))
            cases h_cases with
            | inl h => exact h
            | inr h => exact absurd h h_mini_neq_x
          have h_mini_a_eq : minAt h_insert_nonempty a = minAt h_nonempty a := h_mini_eq_for_ne_i a ha (Ne.symm hia)
          have h_mini_b_eq : minAt h_insert_nonempty b = minAt h_nonempty b := h_mini_eq_for_ne_i b hb (Ne.symm hib)
          have h_contr : minAt h_insert_nonempty a = minAt h_insert_nonempty b := by
            rw [h_mini_a_eq, h_mini_b_eq, h_eq]
          exact (hab (h_inj_insert ha hb h_contr)).elim
      use i, h_i_in_ab
      constructor
      · have h_nonempty_M : (M_set τ D i h_nonempty).Nonempty := by
          use x
          unfold M_set
          apply Set.mem_ofPred.mpr
          intro k hk_mem hk_ne_i
          exact h_mini_lt_x k hk_mem hk_ne_i
        exact h_nonempty_M
      · unfold is_maximal_in_M_set
        constructor
        · unfold M_set
          apply Set.mem_ofPred.mpr
          intro k hk_mem hk_ne_i
          exact h_mini_lt_x k hk_mem hk_ne_i
        · intros y hy
          let := IST.IST i
          unfold M_set at hy
          simp at hy
          obtain ⟨k, hk_in_D, h_y_le_all⟩ := h_dominant y
          by_cases hik : k = i
          · subst hik
            exact h_y_le_all x (Finset.mem_insert_self x τ)
          · have h_lt_y : minAt h_nonempty k <[k] y := hy k hk_in_D hik
            have h_mini_mem : minAt h_nonempty k ∈ τ := by
              unfold minAt
              exact @Finset.min'_mem _ (IST.IST k) _ h_nonempty
            have h_mini_mem_insert : minAt h_nonempty k ∈ insert x τ := Finset.mem_insert_of_mem h_mini_mem
            have h_le_m : y ≤[k] minAt h_nonempty k := h_y_le_all (minAt h_nonempty k) h_mini_mem_insert
            let := IST.IST k
            exact absurd (lt_of_lt_of_le h_lt_y h_le_m) (lt_irrefl _)
    · rintro ⟨i, hi_mem_ab, h_M_nonempty, h_x_is_max⟩
      have h_x_in_M : x ∈ M_set τ D i h_nonempty := h_x_is_max.1
      unfold isDominant
      intro y
      have h_dom_tau := h_door.1
      obtain ⟨k, hk_in_D, hk_dom⟩ := h_dom_tau y
      by_cases h_k_eq_i : k = i
      · subst h_k_eq_i
        have hk_in_D : k ∈ D := by
          cases Finset.mem_insert.mp hi_mem_ab with
          | inl hk_eq_a => rwa [hk_eq_a]
          | inr hk_eq_b => have : k = b := Finset.mem_singleton.mp hk_eq_b; rw [this]; exact hb
        let := IST.IST k
        by_cases h_y_le_x : y ≤[k] x
        · use k, hk_in_D
          intro z hz
          cases Finset.mem_insert.mp hz with
          | inl h_z_eq_x => rw [h_z_eq_x]; exact h_y_le_x
          | inr h_z_in_tau => exact hk_dom z h_z_in_tau
        · have h_x_lt_y : x <[k] y := lt_of_not_ge h_y_le_x
          have h_y_not_in_M : y ∉ M_set τ D k h_nonempty := by
            intro h_y_in_M
            have h_y_le_x : y ≤[k] x := h_x_is_max.2 y h_y_in_M
            exact not_le.mpr h_x_lt_y h_y_le_x
          simp [M_set] at h_y_not_in_M
          push Not at h_y_not_in_M
          obtain ⟨j, hj_in_D, hj_ne_k, hj_not_lt⟩ := h_y_not_in_M
          use j, hj_in_D
          intro z hz
          cases Finset.mem_insert.mp hz with
          | inl h_z_eq_x =>
            rw [h_z_eq_x]
            let := IST.IST j
            have h_mini_lt_x : minAt h_nonempty j <[j] x := h_x_in_M j hj_in_D hj_ne_k
            have h_y_le_mini : y ≤[j] minAt h_nonempty j := le_of_not_gt hj_not_lt
            exact le_of_lt (lt_of_le_of_lt h_y_le_mini h_mini_lt_x)
          | inr h_z_in_tau =>
            let := IST.IST j
            have h_y_le_mini : y ≤[j] minAt h_nonempty j := le_of_not_gt hj_not_lt
            have h_mini_le_z : minAt h_nonempty j ≤[j] z := Finset.min'_le τ z h_z_in_tau
            exact le_trans h_y_le_mini h_mini_le_z
      · use k, hk_in_D
        intro z hz
        cases Finset.mem_insert.mp hz with
        | inl h_z_eq_x =>
          rw [h_z_eq_x]
          let := IST.IST k
          have h_y_le_mini : y ≤[k] minAt h_nonempty k := hk_dom (minAt h_nonempty k) (Finset.min'_mem τ h_nonempty)
          have h_mini_lt_x : minAt h_nonempty k <[k] x := h_x_in_M k hk_in_D h_k_eq_i
          exact le_of_lt (lt_of_le_of_lt h_y_le_mini h_mini_lt_x)
        | inr h_z_in_tau =>
          exact hk_dom z h_z_in_tau
  have M_sets_disjoint (τ : Finset T) (D : Finset I) (a b : I)
      (h_nonempty : τ.Nonempty) (h_door : IST.isDoor τ D)
      (ha : a ∈ D) (hb : b ∈ D) (hab : a ≠ b)
      (h_eq : minAt h_nonempty a = minAt h_nonempty b) :
      M_set τ D a h_nonempty ∩ M_set τ D b h_nonempty = ∅ := by
    ext y
    simp only [Set.mem_inter_iff, Set.mem_empty_iff_false]
    constructor
    · intro ⟨h_in_a, h_in_b⟩
      unfold M_set at h_in_a h_in_b
      have h_b_ne_a : b ≠ a := hab.symm
      have h_mini_b_lt_y : minAt h_nonempty b <[b] y := h_in_a b hb h_b_ne_a
      have h_mini_a_lt_y : minAt h_nonempty a <[a] y := h_in_b a ha hab
      rw [h_eq] at h_mini_a_lt_y
      obtain ⟨k, hk_in_D, hk_dom⟩ := h_door.1 y
      have h_mini_b_mem : minAt h_nonempty b ∈ τ := by
        unfold minAt
        exact @Finset.min'_mem _ (IST.IST b) _ h_nonempty
      have h_y_le_mini_b : y ≤[k] minAt h_nonempty b := hk_dom (minAt h_nonempty b) h_mini_b_mem
      by_cases hk_eq_a : k = a
      · subst hk_eq_a
        let := IST.IST k
        exact not_le.mpr h_mini_a_lt_y h_y_le_mini_b
      · by_cases hk_eq_b : k = b
        · subst hk_eq_b
          let := IST.IST k
          exact not_le.mpr h_mini_b_lt_y h_y_le_mini_b
        · have h_mini_k_lt_y : minAt h_nonempty k <[k] y := h_in_a k hk_in_D hk_eq_a
          have h_mini_k_mem : minAt h_nonempty k ∈ τ := by
            unfold minAt
            exact @Finset.min'_mem _ (IST.IST k) _ h_nonempty
          have h_y_le_mini_k : y ≤[k] minAt h_nonempty k := hk_dom (minAt h_nonempty k) h_mini_k_mem
          let := IST.IST k
          exact not_le.mpr h_mini_k_lt_y h_y_le_mini_k
    · intro h
      exact False.elim h
  have m_element_not_in_tau (τ : Finset T) (D : Finset I) (i a b : I)
      (h_door : IST.isDoor τ D) (h_nonempty : τ.Nonempty)
      (ha_mem : a ∈ D) (hb_mem : b ∈ D) (hab : a ≠ b)
      (h_eq_mini : minAt h_nonempty a = minAt h_nonempty b)
      (h_M_nonempty : (M_set τ D i h_nonempty).Nonempty)
      (h_i_is : i = a ∨ i = b) :
      maxAt τ D i h_nonempty h_M_nonempty ∉ τ := by
    let m_i := maxAt τ D i h_nonempty h_M_nonempty
    have h_max : is_maximal_in_M_set τ D i h_nonempty m_i :=
      m_element_is_maximal τ D i h_nonempty h_M_nonempty
    intro h_m_in_tau
    obtain ⟨k, hk_mem, hk_dom⟩ := h_door.1 m_i
    by_cases hk_eq_i : k = i
    · subst hk_eq_i
      have h_m_le_mini : m_i ≤[k] minAt h_nonempty k := hk_dom (minAt h_nonempty k) (by
        unfold minAt
        exact @Finset.min'_mem _ (IST.IST k) _ h_nonempty)
      have h_m_eq_mini : m_i = minAt h_nonempty k := by
        let := IST.IST k
        have h_mini_le_m : minAt h_nonempty k ≤[k] m_i := Finset.min'_le τ m_i h_m_in_tau
        exact le_antisymm h_m_le_mini h_mini_le_m
      have h_m_in_M : m_i ∈ M_set τ D k h_nonempty := h_max.1
      unfold M_set at h_m_in_M
      cases h_i_is with
      | inl hi_eq_a =>
        subst hi_eq_a
        have h_mini_b_lt_m : minAt h_nonempty b <[b] m_i := h_m_in_M b hb_mem hab.symm
        rw [h_m_eq_mini, h_eq_mini] at h_mini_b_lt_m
        let := IST.IST b
        exact lt_irrefl (minAt h_nonempty b) h_mini_b_lt_m
      | inr hi_eq_b =>
        subst hi_eq_b
        have h_mini_a_lt_m : minAt h_nonempty a <[a] m_i := h_m_in_M a ha_mem hab
        rw [h_m_eq_mini, ← h_eq_mini] at h_mini_a_lt_m
        let := IST.IST a
        exact lt_irrefl (minAt h_nonempty a) h_mini_a_lt_m
    · have h_m_in_M : m_i ∈ M_set τ D i h_nonempty := h_max.1
      unfold M_set at h_m_in_M
      have h_mini_k_lt_m : minAt h_nonempty k <[k] m_i := h_m_in_M k hk_mem hk_eq_i
      have h_m_le_mini_k : m_i ≤[k] minAt h_nonempty k := hk_dom (minAt h_nonempty k) (by
        unfold minAt
        exact @Finset.min'_mem _ (IST.IST k) _ h_nonempty)
      let := IST.IST k
      exact not_le.mpr h_mini_k_lt_m h_m_le_mini_k
  have odoor_index_in_pair (τ : Finset T) (D : Finset I) (C : Finset I)
      (a b j : I) (_h_door : IST.isDoor τ D) (h_nonempty : τ.Nonempty)
      (ha_mem : a ∈ D) (hb_mem : b ∈ D) (hab : a ≠ b)
      (h_eq_mini : minAt h_nonempty a = minAt h_nonempty b)
      (h_dom : IST.isDominant τ C) (h_room_card : C.card = τ.card)
      (_hj_not_mem : j ∉ C) (hc_eq : D = insert j C) :
      j ∈ ({a, b} : Finset I) := by
    by_contra h_not_in
    simp only [Finset.mem_insert, Finset.mem_singleton] at h_not_in
    push Not at h_not_in
    obtain ⟨hj_ne_a, hj_ne_b⟩ := h_not_in
    have ha_in_C : a ∈ C := by
      have ha_in_D : a ∈ D := ha_mem
      rw [hc_eq] at ha_in_D
      cases Finset.mem_insert.mp ha_in_D with
      | inl h_eq => exact absurd h_eq (Ne.symm hj_ne_a)
      | inr h_mem => exact h_mem
    have hb_in_C : b ∈ C := by
      have hb_in_D : b ∈ D := hb_mem
      rw [hc_eq] at hb_in_D
      cases Finset.mem_insert.mp hb_in_D with
      | inl h_eq => exact absurd h_eq (Ne.symm hj_ne_b)
      | inr h_mem => exact h_mem
    have h_inj_C : Set.InjOn (minAt h_nonempty) (C : Set I) := by
      apply Finset.injOn_of_card_image_eq
      have h_tau_eq_C_image : τ = C.image (minAt h_nonempty) := by
        convert keylemma_of_dominant h_dom h_nonempty
      rw [←h_tau_eq_C_image]
      exact h_room_card.symm
    exact hab (h_inj_C ha_in_C hb_in_C h_eq_mini)
  have maximal_element_unique (τ : Finset T) (D : Finset I) (i : I)
      (h_nonempty : τ.Nonempty) (h_M_nonempty : (M_set τ D i h_nonempty).Nonempty)
      (x : T) (h_x_max : is_maximal_in_M_set τ D i h_nonempty x) :
      x = maxAt τ D i h_nonempty h_M_nonempty := by
    let m_i := maxAt τ D i h_nonempty h_M_nonempty
    have h_mi_max : is_maximal_in_M_set τ D i h_nonempty m_i :=
      m_element_is_maximal τ D i h_nonempty h_M_nonempty
    let := IST.IST i
    have h_x_in_M : x ∈ M_set τ D i h_nonempty := h_x_max.1
    have h_mi_in_M : m_i ∈ M_set τ D i h_nonempty := h_mi_max.1
    have h_x_le_mi : x ≤[i] m_i := h_mi_max.2 x h_x_in_M
    have h_mi_le_x : m_i ≤[i] x := h_x_max.2 m_i h_mi_in_M
    exact le_antisymm h_x_le_mi h_mi_le_x
  have room_and_door_of_M_nonempty
      (τ : Finset T) (D : Finset I) (a b i : I)
      (h_door : IST.isDoor τ D) (h_nonempty : τ.Nonempty)
      (ha_mem : a ∈ D) (hb_mem : b ∈ D) (hab : a ≠ b)
      (h_eq_mini : minAt h_nonempty a = minAt h_nonempty b)
      (hi : i = a ∨ i = b) (hMi : (M_set τ D i h_nonempty).Nonempty) :
      IST.isRoom (insert (maxAt τ D i h_nonempty hMi) τ) D ∧
        isDoorof τ D (insert (maxAt τ D i h_nonempty hMi) τ) D := by
    have hmi_not_mem : maxAt τ D i h_nonempty hMi ∉ τ :=
      m_element_not_in_tau τ D i a b h_door h_nonempty ha_mem hb_mem hab
        h_eq_mini hMi hi
    have hi_pair : i ∈ ({a, b} : Finset I) := by
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hi
    have hdom :
        IST.isDominant (insert (maxAt τ D i h_nonempty hMi) τ) D :=
      (isDominant_insert_iff_maximal_in_M_set τ D (maxAt τ D i h_nonempty hMi)
        h_door h_nonempty
        hmi_not_mem a b ha_mem hb_mem hab h_eq_mini).2
        ⟨i, hi_pair, hMi, m_element_is_maximal τ D i h_nonempty hMi⟩
    have hroom : IST.isRoom (insert (maxAt τ D i h_nonempty hMi) τ) D := by
      refine ⟨hdom, ?_⟩
      rw [Finset.card_insert_of_notMem hmi_not_mem, h_door.2]
    exact ⟨hroom, isDoorof.idoor hdom h_door _ hmi_not_mem rfl rfl⟩
  have room_and_door_of_M_empty
      (τ : Finset T) (D : Finset I) (a b i : I)
      (h_door : IST.isDoor τ D) (h_nonempty : τ.Nonempty)
      (ha_mem : a ∈ D) (hb_mem : b ∈ D) (hab : a ≠ b)
      (h_eq_mini : minAt h_nonempty a = minAt h_nonempty b)
      (hi_mem : i ∈ D) (hi : i = a ∨ i = b)
      (hMi : M_set τ D i h_nonempty = ∅) :
      IST.isRoom τ (D.erase i) ∧ isDoorof τ D τ (D.erase i) := by
    have hdom : IST.isDominant τ (D.erase i) :=
      (isDominant_erase_iff_M_set_empty τ D h_door h_nonempty i hi_mem).2
        ⟨a, b, ha_mem, hb_mem, hab, h_eq_mini, hi, hMi⟩
    have hroom : IST.isRoom τ (D.erase i) := by
      refine ⟨hdom, ?_⟩
      rw [Finset.card_erase_of_mem hi_mem, h_door.2]
      omega
    exact ⟨hroom, isDoorof.odoor hdom h_door i (Finset.notMem_erase i D) rfl
      (Finset.insert_erase hi_mem).symm⟩
  have incident_room_classification
      (τ : Finset T) (D : Finset I) (a b : I)
      (h_door : IST.isDoor τ D) (h_nonempty : τ.Nonempty)
      (ha_mem : a ∈ D) (hb_mem : b ∈ D) (hab : a ≠ b)
      (h_eq_mini : minAt h_nonempty a = minAt h_nonempty b)
      (σ : Finset T) (C : Finset I) (h_room : IST.isRoom σ C)
      (h_door_rel : isDoorof τ D σ C) :
      (∃ x i, x ∉ τ ∧ i ∈ ({a, b} : Finset I) ∧
        (M_set τ D i h_nonempty).Nonempty ∧
        is_maximal_in_M_set τ D i h_nonempty x ∧
        σ = insert x τ ∧ C = D) ∨
      (∃ i, i ∈ ({a, b} : Finset I) ∧ M_set τ D i h_nonempty = ∅ ∧
        σ = τ ∧ C = D.erase i) := by
    cases h_door_rel with
    | idoor hdom _ x hx_not_mem h_insert h_colors =>
        have hdom' : IST.isDominant (insert x τ) D := by
          simpa only [h_insert, h_colors] using hdom
        obtain ⟨i, hi_pair, hMi, hmax⟩ :=
          (isDominant_insert_iff_maximal_in_M_set τ D x h_door h_nonempty hx_not_mem
            a b ha_mem hb_mem hab
            h_eq_mini).1 hdom'
        exact Or.inl ⟨x, i, hx_not_mem, hi_pair, hMi, hmax, h_insert.symm, h_colors.symm⟩
    | odoor hdom _ i hi_not_mem h_tau h_insert =>
        have hdom' : IST.isDominant τ C := by
          simpa only [h_tau] using hdom
        have hcard : C.card = τ.card := by
          simpa only [h_tau] using h_room.2
        have hi_mem : i ∈ D := by
          rw [h_insert]
          exact Finset.mem_insert_self i C
        have hi_pair : i ∈ ({a, b} : Finset I) :=
          odoor_index_in_pair τ D C a b i h_door h_nonempty ha_mem hb_mem hab
            h_eq_mini hdom' hcard hi_not_mem h_insert
        have hC : C = D.erase i := by
          rw [h_insert]
          exact (Finset.erase_insert hi_not_mem).symm
        have hdom_erase : IST.isDominant τ (D.erase i) := by
          simpa only [← hC] using hdom'
        obtain ⟨_, _, _, _, _, _, _, hMi⟩ :=
          (isDominant_erase_iff_M_set_empty τ D h_door h_nonempty i hi_mem).1 hdom_erase
        exact Or.inr ⟨i, hi_pair, hMi, h_tau.symm, hC⟩
  have incident_room_eq_of_both_M_nonempty
      (τ : Finset T) (D : Finset I) (a b : I)
      (h_door : IST.isDoor τ D) (h_nonempty : τ.Nonempty)
      (ha_mem : a ∈ D) (hb_mem : b ∈ D) (hab : a ≠ b)
      (h_eq_mini : minAt h_nonempty a = minAt h_nonempty b)
      (hMa : (M_set τ D a h_nonempty).Nonempty)
      (hMb : (M_set τ D b h_nonempty).Nonempty)
      (σ : Finset T) (C : Finset I) (h_room : IST.isRoom σ C)
      (h_door_rel : isDoorof τ D σ C) :
      (σ = insert (maxAt τ D a h_nonempty hMa) τ ∧ C = D) ∨
        (σ = insert (maxAt τ D b h_nonempty hMb) τ ∧ C = D) := by
    rcases incident_room_classification τ D a b h_door h_nonempty ha_mem hb_mem hab
        h_eq_mini σ C h_room h_door_rel with hInner | hOuter
    · obtain ⟨x, i, _, hi, _, hmax, hσ, hC⟩ := hInner
      rcases Finset.mem_insert.mp hi with hi | hi
      · subst i
        left
        exact ⟨by simpa only [maximal_element_unique τ D a h_nonempty hMa x hmax] using hσ, hC⟩
      · have hi : i = b := Finset.mem_singleton.mp hi
        subst i
        right
        exact ⟨by simpa only [maximal_element_unique τ D b h_nonempty hMb x hmax] using hσ, hC⟩
    · obtain ⟨i, hi, hMi, _, _⟩ := hOuter
      rcases Finset.mem_insert.mp hi with hi | hi
      · subst i
        exact ((Set.not_nonempty_iff_eq_empty.mpr hMi) hMa).elim
      · have hi : i = b := Finset.mem_singleton.mp hi
        subst i
        exact ((Set.not_nonempty_iff_eq_empty.mpr hMi) hMb).elim
  have incident_room_eq_of_left_M_nonempty
      (τ : Finset T) (D : Finset I) (a b : I)
      (h_door : IST.isDoor τ D) (h_nonempty : τ.Nonempty)
      (ha_mem : a ∈ D) (hb_mem : b ∈ D) (hab : a ≠ b)
      (h_eq_mini : minAt h_nonempty a = minAt h_nonempty b)
      (hMa : (M_set τ D a h_nonempty).Nonempty)
      (hMb : M_set τ D b h_nonempty = ∅)
      (σ : Finset T) (C : Finset I) (h_room : IST.isRoom σ C)
      (h_door_rel : isDoorof τ D σ C) :
      (σ = insert (maxAt τ D a h_nonempty hMa) τ ∧ C = D) ∨
        (σ = τ ∧ C = D.erase b) := by
    rcases incident_room_classification τ D a b h_door h_nonempty ha_mem hb_mem hab
        h_eq_mini σ C h_room h_door_rel with hInner | hOuter
    · obtain ⟨x, i, _, hi, hMi, hmax, hσ, hC⟩ := hInner
      rcases Finset.mem_insert.mp hi with hi | hi
      · subst i
        left
        exact ⟨by simpa only [maximal_element_unique τ D a h_nonempty hMa x hmax] using hσ, hC⟩
      · have hi : i = b := Finset.mem_singleton.mp hi
        subst i
        exact ((Set.not_nonempty_iff_eq_empty.mpr hMb) hMi).elim
    · obtain ⟨i, hi, hMi, hσ, hC⟩ := hOuter
      rcases Finset.mem_insert.mp hi with hi | hi
      · subst i
        exact ((Set.not_nonempty_iff_eq_empty.mpr hMi) hMa).elim
      · have hi : i = b := Finset.mem_singleton.mp hi
        subst i
        exact Or.inr ⟨hσ, hC⟩
  have incident_room_eq_of_right_M_nonempty
      (τ : Finset T) (D : Finset I) (a b : I)
      (h_door : IST.isDoor τ D) (h_nonempty : τ.Nonempty)
      (ha_mem : a ∈ D) (hb_mem : b ∈ D) (hab : a ≠ b)
      (h_eq_mini : minAt h_nonempty a = minAt h_nonempty b)
      (hMa : M_set τ D a h_nonempty = ∅)
      (hMb : (M_set τ D b h_nonempty).Nonempty)
      (σ : Finset T) (C : Finset I) (h_room : IST.isRoom σ C)
      (h_door_rel : isDoorof τ D σ C) :
      (σ = insert (maxAt τ D b h_nonempty hMb) τ ∧ C = D) ∨
        (σ = τ ∧ C = D.erase a) := by
    rcases incident_room_classification τ D a b h_door h_nonempty ha_mem hb_mem hab
        h_eq_mini σ C h_room h_door_rel with hInner | hOuter
    · obtain ⟨x, i, _, hi, hMi, hmax, hσ, hC⟩ := hInner
      rcases Finset.mem_insert.mp hi with hi | hi
      · subst i
        exact ((Set.not_nonempty_iff_eq_empty.mpr hMa) hMi).elim
      · have hi : i = b := Finset.mem_singleton.mp hi
        subst i
        left
        exact ⟨by simpa only [maximal_element_unique τ D b h_nonempty hMb x hmax] using hσ, hC⟩
    · obtain ⟨i, hi, hMi, hσ, hC⟩ := hOuter
      rcases Finset.mem_insert.mp hi with hi | hi
      · subst i
        exact Or.inr ⟨hσ, hC⟩
      · have hi : i = b := Finset.mem_singleton.mp hi
        subst i
        exact ((Set.not_nonempty_iff_eq_empty.mpr hMi) hMb).elim
  have incident_room_eq_of_both_M_empty
      (τ : Finset T) (D : Finset I) (a b : I)
      (h_door : IST.isDoor τ D) (h_nonempty : τ.Nonempty)
      (ha_mem : a ∈ D) (hb_mem : b ∈ D) (hab : a ≠ b)
      (h_eq_mini : minAt h_nonempty a = minAt h_nonempty b)
      (hMa : M_set τ D a h_nonempty = ∅)
      (hMb : M_set τ D b h_nonempty = ∅)
      (σ : Finset T) (C : Finset I) (h_room : IST.isRoom σ C)
      (h_door_rel : isDoorof τ D σ C) :
      (σ = τ ∧ C = D.erase a) ∨ (σ = τ ∧ C = D.erase b) := by
    rcases incident_room_classification τ D a b h_door h_nonempty ha_mem hb_mem hab
        h_eq_mini σ C h_room h_door_rel with hInner | hOuter
    · obtain ⟨_, i, _, hi, hMi, _, _, _⟩ := hInner
      rcases Finset.mem_insert.mp hi with hi | hi
      · subst i
        exact ((Set.not_nonempty_iff_eq_empty.mpr hMa) hMi).elim
      · have hi : i = b := Finset.mem_singleton.mp hi
        subst i
        exact ((Set.not_nonempty_iff_eq_empty.mpr hMb) hMi).elim
    · obtain ⟨i, hi, _, hσ, hC⟩ := hOuter
      rcases Finset.mem_insert.mp hi with hi | hi
      · subst i
        exact Or.inl ⟨hσ, hC⟩
      · have hi : i = b := Finset.mem_singleton.mp hi
        subst i
        exact Or.inr ⟨hσ, hC⟩
  obtain ⟨h_door, h_nonempty⟩ := h_int_door
  have h_card : D.card = τ.card + 1 := h_door.2
  have h_image_card : D.card = (D.image (minAt h_nonempty)).card + 1 := by
    have h_dominant : IST.isDominant τ D := h_door.1
    have h_image_eq : D.image (minAt h_nonempty) = τ := by
      convert (keylemma_of_dominant h_dominant h_nonempty).symm
    rw [h_card, h_image_eq]
  have h_collision : ∃ a b, a ∈ D ∧ b ∈ D ∧
      (minAt h_nonempty) a = (minAt h_nonempty) b ∧ a ≠ b ∧
      Set.InjOn (minAt h_nonempty) ((D : Set I) \ ({a, b} : Set I)) := by
    obtain ⟨t, hts, hinj, himage⟩ :=
      Finset.exists_subset_injOn_image_eq_of_surjOn (D : Set I) (D.image (minAt h_nonempty))
        (by intro y hy; exact Finset.mem_image.mp hy)
    have ht : t ⊆ D := hts
    have hcard : t.card = (D.image (minAt h_nonempty)).card := by
      rw [← himage, Finset.card_image_of_injOn hinj]
    have hdiff : (D \ t).card = 1 := by
      rw [Finset.card_sdiff_of_subset ht, h_image_card, ← hcard]
      omega
    obtain ⟨b, hb⟩ := Finset.card_eq_one.mp hdiff
    have hbs : b ∈ D := (Finset.mem_sdiff.mp (hb.symm ▸ Finset.mem_singleton_self b)).1
    have hbnt : b ∉ t := (Finset.mem_sdiff.mp (hb.symm ▸ Finset.mem_singleton_self b)).2
    have hfb : minAt h_nonempty b ∈ t.image (minAt h_nonempty) := by
      rw [himage]
      exact Finset.mem_image.mpr ⟨b, hbs, rfl⟩
    obtain ⟨a, ha, hab⟩ := Finset.mem_image.mp hfb
    refine ⟨a, b, ht ha, hbs, hab, ?_, ?_⟩
    · intro heq
      exact hbnt (heq ▸ ha)
    · apply hinj.mono
      intro x hx
      rcases hx with ⟨hxs, hxab⟩
      have hxnb : x ≠ b := by
        intro hxb
        apply hxab
        simp [hxb]
      by_contra hxnt
      have hxb : x ∈ D \ t := Finset.mem_sdiff.mpr ⟨hxs, hxnt⟩
      rw [hb] at hxb
      exact hxnb (Finset.mem_singleton.mp hxb)
  obtain ⟨a, b, ha_mem, hb_mem, h_eq_mini, hab, _⟩ := h_collision
  have h_disjoint : M_set τ D a h_nonempty ∩ M_set τ D b h_nonempty = ∅ :=
    M_sets_disjoint τ D a b h_nonempty h_door ha_mem hb_mem hab h_eq_mini
  by_cases h_Ma_nonempty : (M_set τ D a h_nonempty).Nonempty
  · by_cases h_Mb_nonempty : (M_set τ D b h_nonempty).Nonempty
    · let m_a := maxAt τ D a h_nonempty h_Ma_nonempty
      let m_b := maxAt τ D b h_nonempty h_Mb_nonempty
      have h_ma_max : is_maximal_in_M_set τ D a h_nonempty m_a :=
        m_element_is_maximal τ D a h_nonempty h_Ma_nonempty
      have h_mb_max : is_maximal_in_M_set τ D b h_nonempty m_b :=
        m_element_is_maximal τ D b h_nonempty h_Mb_nonempty
      have h_ma_ne_mb : m_a ≠ m_b := by
        intro h_eq
        have h_ma_in_Ma : m_a ∈ M_set τ D a h_nonempty := h_ma_max.1
        have h_mb_in_Mb : m_b ∈ M_set τ D b h_nonempty := h_mb_max.1
        rw [h_eq] at h_ma_in_Ma
        have h_in_inter : m_b ∈ M_set τ D a h_nonempty ∩ M_set τ D b h_nonempty :=
          ⟨h_ma_in_Ma, h_mb_in_Mb⟩
        rw [h_disjoint] at h_in_inter
        exact Set.notMem_empty m_b h_in_inter
      have h_ma_not_mem : m_a ∉ τ :=
        m_element_not_in_tau τ D a a b h_door h_nonempty ha_mem hb_mem hab h_eq_mini h_Ma_nonempty (Or.inl rfl)
      have h_mb_not_mem : m_b ∉ τ :=
        m_element_not_in_tau τ D b a b h_door h_nonempty ha_mem hb_mem hab h_eq_mini h_Mb_nonempty (Or.inr rfl)
      obtain ⟨h_room_a, h_door_a⟩ :=
        room_and_door_of_M_nonempty τ D a b a h_door h_nonempty ha_mem hb_mem hab
          h_eq_mini (Or.inl rfl) h_Ma_nonempty
      obtain ⟨h_room_b, h_door_b⟩ :=
        room_and_door_of_M_nonempty τ D a b b h_door h_nonempty ha_mem hb_mem hab
          h_eq_mini (Or.inr rfl) h_Mb_nonempty
      use insert m_a τ, insert m_b τ, D, D
      constructor
      · intro h_pair_eq
        have h_eq : insert m_a τ = insert m_b τ := congr_arg Prod.fst h_pair_eq
        have : m_a = m_b := by
          have h_ma_in : m_a ∈ insert m_a τ := Finset.mem_insert_self m_a τ
          rw [h_eq] at h_ma_in
          cases Finset.mem_insert.mp h_ma_in with
          | inl h => exact h
          | inr h => exact absurd h h_ma_not_mem
        exact h_ma_ne_mb this
      constructor
      · exact h_room_a
      constructor
      · exact h_room_b
      constructor
      · exact h_door_a
      constructor
      · exact h_door_b
      · intros σ C h_room h_door_rel
        simpa only [m_a, m_b] using
          incident_room_eq_of_both_M_nonempty τ D a b h_door h_nonempty ha_mem hb_mem
            hab h_eq_mini h_Ma_nonempty h_Mb_nonempty σ C h_room h_door_rel
    · let m_a := maxAt τ D a h_nonempty h_Ma_nonempty
      have h_ma_max : is_maximal_in_M_set τ D a h_nonempty m_a :=
        m_element_is_maximal τ D a h_nonempty h_Ma_nonempty
      have h_ma_not_mem : m_a ∉ τ :=
        m_element_not_in_tau τ D a a b h_door h_nonempty ha_mem hb_mem hab h_eq_mini h_Ma_nonempty (Or.inl rfl)
      have h_Mb_empty : M_set τ D b h_nonempty = ∅ := Set.not_nonempty_iff_eq_empty.mp h_Mb_nonempty
      obtain ⟨h_room_a, h_door_a⟩ :=
        room_and_door_of_M_nonempty τ D a b a h_door h_nonempty ha_mem hb_mem hab
          h_eq_mini (Or.inl rfl) h_Ma_nonempty
      obtain ⟨h_room_b, h_door_b⟩ :=
        room_and_door_of_M_empty τ D a b b h_door h_nonempty ha_mem hb_mem hab
          h_eq_mini hb_mem (Or.inr rfl) h_Mb_empty
      use insert m_a τ, τ, D, D.erase b
      constructor
      · intro h_pair_eq
        have h_eq : insert m_a τ = τ := congr_arg Prod.fst h_pair_eq
        have h_ma_in : m_a ∈ insert m_a τ := Finset.mem_insert_self m_a τ
        rw [h_eq] at h_ma_in
        exact h_ma_not_mem h_ma_in
      constructor
      · exact h_room_a
      constructor
      · exact h_room_b
      constructor
      · exact h_door_a
      constructor
      · exact h_door_b
      · intros σ C h_room h_door_rel
        simpa only [m_a] using
          incident_room_eq_of_left_M_nonempty τ D a b h_door h_nonempty ha_mem hb_mem
            hab h_eq_mini h_Ma_nonempty h_Mb_empty σ C h_room h_door_rel
  · have h_Ma_empty : M_set τ D a h_nonempty = ∅ := Set.not_nonempty_iff_eq_empty.mp h_Ma_nonempty
    by_cases h_Mb_nonempty : (M_set τ D b h_nonempty).Nonempty
    · let m_b := maxAt τ D b h_nonempty h_Mb_nonempty
      have h_mb_max : is_maximal_in_M_set τ D b h_nonempty m_b :=
        m_element_is_maximal τ D b h_nonempty h_Mb_nonempty
      have h_mb_not_mem : m_b ∉ τ :=
        m_element_not_in_tau τ D b a b h_door h_nonempty ha_mem hb_mem hab h_eq_mini h_Mb_nonempty (Or.inr rfl)
      obtain ⟨h_room_b, h_door_b⟩ :=
        room_and_door_of_M_nonempty τ D a b b h_door h_nonempty ha_mem hb_mem hab
          h_eq_mini (Or.inr rfl) h_Mb_nonempty
      obtain ⟨h_room_a, h_door_a⟩ :=
        room_and_door_of_M_empty τ D a b a h_door h_nonempty ha_mem hb_mem hab
          h_eq_mini ha_mem (Or.inl rfl) h_Ma_empty
      use insert m_b τ, τ, D, D.erase a
      constructor
      · intro h_pair_eq
        have h_eq : insert m_b τ = τ := congr_arg Prod.fst h_pair_eq
        have h_mb_in : m_b ∈ insert m_b τ := Finset.mem_insert_self m_b τ
        rw [h_eq] at h_mb_in
        exact h_mb_not_mem h_mb_in
      constructor
      · exact h_room_b
      constructor
      · exact h_room_a
      constructor
      · exact h_door_b
      constructor
      · exact h_door_a
      · intros σ C h_room h_door_rel
        simpa only [m_b] using
          incident_room_eq_of_right_M_nonempty τ D a b h_door h_nonempty ha_mem hb_mem
            hab h_eq_mini h_Ma_empty h_Mb_nonempty σ C h_room h_door_rel
    · have h_Mb_empty : M_set τ D b h_nonempty = ∅ := Set.not_nonempty_iff_eq_empty.mp h_Mb_nonempty
      obtain ⟨h_room_b, h_door_b⟩ :=
        room_and_door_of_M_empty τ D a b b h_door h_nonempty ha_mem hb_mem hab
          h_eq_mini hb_mem (Or.inr rfl) h_Mb_empty
      obtain ⟨h_room_a, h_door_a⟩ :=
        room_and_door_of_M_empty τ D a b a h_door h_nonempty ha_mem hb_mem hab
          h_eq_mini ha_mem (Or.inl rfl) h_Ma_empty
      use τ, τ, D.erase b, D.erase a
      constructor
      · intro h_pair_eq
        have h_erasure_eq : D.erase b = D.erase a := congr_arg Prod.snd h_pair_eq
        have h_a_in_erase_b : a ∈ D.erase b := Finset.mem_erase.mpr ⟨hab, ha_mem⟩
        rw [h_erasure_eq] at h_a_in_erase_b
        exact (Finset.notMem_erase a D) h_a_in_erase_b
      constructor
      · exact h_room_b
      constructor
      · exact h_room_a
      constructor
      · exact h_door_b
      constructor
      · exact h_door_a
      · intros σ C h_room h_door_rel
        rcases incident_room_eq_of_both_M_empty τ D a b h_door h_nonempty ha_mem
            hb_mem hab h_eq_mini h_Ma_empty h_Mb_empty σ C h_room h_door_rel with
          hA | hB
        · exact Or.inr hA
        · exact Or.inl hB
end IndexedLOrder
end D5.S3.Combinatorics.Scarf
