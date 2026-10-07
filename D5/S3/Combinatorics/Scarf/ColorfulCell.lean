/- GID: D5/S3/Combinatorics/Scarf/ColorfulCell
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Scarf/ColorfulCell
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Convex.StdSimplex]
   utility: none
   digest: Singleton exterior incidence and both internal-door and noncolorful-room fiber counts yield an odd colorful contribution. -/
/- proof_shape: Scarf: content
   admission_basis: escape-witness
   escape_witness: Singleton exterior incidence and both internal-door and noncolorful-room fiber counts yield an odd colorful contribution.
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

import D5.S3.Combinatorics.Scarf.ColorfulDoors
open Classical Finset
set_option quotPrecheck false
namespace D5.S3.Combinatorics.Scarf
variable {T : Type*} {I : Type*} [Inhabited T] [DecidableEq T] [DecidableEq I]
variable [IST : IndexedLOrder I T]
local notation lhs "<[" i "]" rhs => (IST.IST i).lt lhs rhs
local notation lhs "≤[" i "]" rhs => (IST.IST i).le lhs rhs
namespace IndexedLOrder
variable [Fintype T] [Fintype I] [Inhabited I]
variable (c : T → I)
noncomputable abbrev colorful := Finset.filter (fun (x : Finset T× Finset I) =>  IST.isColorful c x.1 x.2) univ
noncomputable abbrev doubleCountingSet (i : I) :=
  Finset.filter (fun x : (Finset T × Finset I) × (Finset T × Finset I) =>
    isTypedNC c i x.1.1 x.1.2 ∧ isDoorof x.1.1 x.1.2 x.2.1 x.2.2) univ
theorem Scarf (c : T → I) : (IST.colorful c).Nonempty := by
  classical
  have Nonempty_of_Dominant {σ : Finset T} {C : Finset I} (h : IST.isDominant σ C) : C.Nonempty := by
    obtain ⟨j,hj⟩ := h default
    exact ⟨j, hj.1⟩
  have sigma_nonempty_of_room {σ : Finset T} {C : Finset I} (h : isRoom σ C) : σ.Nonempty  := by
    have hC : C.Nonempty := Nonempty_of_Dominant h.1
    have hCpos : 0 < C.card := Finset.card_pos.2 hC
    have h_card : σ.card = C.card := h.2.symm
    have hpos : 0 < σ.card := by rwa [h_card]
    exact Finset.card_pos.1 hpos
  have isRoom_of_Door {σ : Finset T} {τ : Finset T} {C : Finset I} {D : Finset I} (h1 : isDoorof τ D σ C) : IST.isRoom σ C := by
    cases h1
    · rename_i h0 h2 x h3 h4 h5
      constructor
      · exact h0
      · simp only [<-h5, h2.2, <-h4, h3, not_false_eq_true, Finset.card_insert_of_notMem]
    · rename_i h0 h2 x h3 h4 h5
      constructor
      · exact h0
      · have h6 := Finset.card_insert_of_notMem h3
        subst h4
        replace h5 : D.card = (insert x C).card := by rw [h5]
        rw [h6] at h5
        rw [h2.2] at h5
        exact Eq.symm $ (add_left_inj _).1 h5
  have outsidedoor_singleton (i : I) : IST.isOutsideDoor Finset.empty {i} := by
    constructor
    · rw [isDoor,isCell,isDominant]
      constructor
      · intro y; use i
        constructor
        · exact Finset.mem_singleton.2 (rfl)
        · intro x hx
          contradiction
      · simp only [Finset.card_singleton]
        rfl
    · rfl
  have outsidedoor_is_singleton {τ : Finset T} {D : Finset I} (h : IST.isOutsideDoor τ  D) :  τ = Finset.empty ∧  ∃ i, D = {i} := by
    obtain ⟨h1, h2⟩ := h
    subst h2
    obtain ⟨_,h3⟩ := h1
    replace h4 : D.card = 1 := by
      simp_all
      rfl
    exact ⟨rfl, Finset.card_eq_one.1 h4⟩
  have not_colorful_of_TypedNC {σ : Finset T} {C : Finset I} {c : T → I} {i : I} (h1 : isTypedNC c i σ C) : ¬ IST.isColorful c σ C := by
    intro h
    unfold isTypedNC at h1
    unfold isColorful at h
    have h_diff := h1.2
    have h_ne : σ.image c ≠ C := by
      intro h_eq
      rw [←h_eq, Finset.sdiff_self] at h_diff
      have h_singleton_nonempty : ({i} : Finset I).Nonempty := Finset.singleton_nonempty i
      rw [←h_diff] at h_singleton_nonempty
      exact Finset.not_nonempty_empty h_singleton_nonempty
    exact h_ne h.2
  have NC_of_TNC {σ : Finset T} {C : Finset I} {c : T → I} {i : I} (h1 : isTypedNC c i σ C) : isNearlyColorful c σ C := by
    have hcell := h1.1
    have heq := h1.2
    constructor
    · exact hcell
    · rw [heq]
      have h_eq : C \ image c σ = {i} := by
        rw [heq]
      rw [←heq, h_eq]
      exact Finset.card_singleton i
  have NC_of_outsidedoor {σ : Finset T} {C : Finset I} {c : T → I} (h : isOutsideDoor σ C) : isNearlyColorful c σ C  := by
    cases h with
    | intro hd he =>
      unfold isNearlyColorful
      unfold isCell
      constructor
      · exact hd.1
      · rw [he]
        have h_img : Finset.image c Finset.empty = Finset.empty := Finset.image_empty c
        rw [h_img]
        have h_disj : Disjoint C Finset.empty := Finset.disjoint_empty_right C
        have h_sdiff : C \ Finset.empty = C := Finset.sdiff_eq_self_of_disjoint h_disj
        rw [h_sdiff]
        unfold isDoor at hd
        have h1 := hd.2
        rw [he] at h1
        exact h1
  have NC_or_C_of_door {σ : Finset T} {τ : Finset T} {C : Finset I} {D : Finset I} {c : T → I} {i : I} (h1 : isTypedNC c i τ D) (h2 : isDoorof τ D σ C) : isTypedNC c i σ C ∨ isColorful c σ C := by
    unfold isTypedNC at h1 ⊢
    unfold isColorful
    have h1_cell := h1.left
    have h1_eq := h1.right
    have h_sigma_cell : isCell σ C := by
      cases h2 with
      | idoor h0 _ _ _ _ _ => exact h0
      | odoor h0 _ _ _ _ _ => exact h0
    have step1_subset : C \ (σ.image c) ⊆ D \ (τ.image c) := by
      intro y hy
      simp only [Finset.mem_sdiff] at hy ⊢
      obtain ⟨y_in_C, y_notin_img_sigma⟩ := hy
      constructor
      · cases h2
        · rename_i h_D_eq; rw [h_D_eq]; exact y_in_C
        · rename_i h_D_eq; rw [h_D_eq]; exact Finset.mem_insert_of_mem y_in_C
      · cases h2 with
        | idoor h0 hdoor x h_x_notin h_sigma_eq h_D_eq =>
          rw [← h_sigma_eq, Finset.image_insert] at y_notin_img_sigma
          simp only [Finset.mem_insert, not_or] at y_notin_img_sigma
          exact y_notin_img_sigma.2
        | odoor h0 hdoor j h_j_notin h_sigma_eq h_D_eq =>
          rw [← h_sigma_eq] at y_notin_img_sigma
          exact y_notin_img_sigma
    have step2_D_card : (D \ (τ.image c)).card = 1 := by
      have D_sdiff_eq_i : D \ (τ.image c) = {i} := by
        rw [h1_eq]
      rw [D_sdiff_eq_i, Finset.card_singleton]
    have step3_C_card_le : (C \ σ.image c).card ≤ 1 := by
      rw [← step2_D_card]
      exact Finset.card_le_card step1_subset
    by_cases h : (C \ σ.image c).card = 0
    · right
      constructor
      · exact h_sigma_cell
      · have h_C_subset_img : C ⊆ σ.image c := by
          rw [Finset.subset_iff]
          intro x hx
          by_contra hxn
          have : x ∈ C \ σ.image c := by simp [hx, hxn]
          have : (C \ σ.image c).Nonempty := ⟨x, this⟩
          have : 0 < (C \ σ.image c).card := Finset.card_pos.2 this
          linarith [h]
        have h_room: isRoom σ C := isRoom_of_Door h2
        have h_card_eq : C.card = σ.card := h_room.2
        have h_img_le_C_card : (σ.image c).card ≤ C.card := by
          calc (σ.image c).card
            ≤ σ.card := Finset.card_image_le
            _ = C.card := h_card_eq.symm
        exact (Finset.eq_of_subset_of_card_le h_C_subset_img h_img_le_C_card).symm
    · left
      constructor
      · exact h_sigma_cell
      · have h_card_one : (C \ σ.image c).card = 1 := by omega
        have h_subset_singleton : C \ σ.image c ⊆ {i} := by
          have D_sdiff_eq_i : D \ (τ.image c) = {i} := by
            rw [h1_eq]
          rw [← D_sdiff_eq_i]
          exact step1_subset
        have C_sdiff_eq_i : C \ σ.image c = {i} :=
          Finset.eq_of_subset_of_card_le h_subset_singleton (by rw [h_card_one, Finset.card_singleton])
        have h_i_notin_img : i ∉ σ.image c := by
          have h_i_in_sdiff : i ∈ C \ σ.image c := by rw [C_sdiff_eq_i]; simp
          exact (Finset.mem_sdiff.mp h_i_in_sdiff).2
        exact C_sdiff_eq_i
  have isTypedNC_of_isNearlyColorful_of_isDoorof_isTypedNC {σ : Finset T} {τ : Finset T} {C : Finset I} {D : Finset I} {c : T → I} {i : I} (h_nc : isNearlyColorful c τ D) (h_door : isDoorof τ D σ C) (h_room_typed : isTypedNC c i σ C) : isTypedNC c i τ D := by
    constructor
    · exact h_nc.1
    · have h_subset : C \ image c σ ⊆ D \ image c τ := by
        intro y hy
        simp only [Finset.mem_sdiff] at hy ⊢
        obtain ⟨y_in_C, y_notin_img_sigma⟩ := hy
        constructor
        · cases h_door with
          | idoor h0 _ _ _ _ h_D_eq => rw [h_D_eq]; exact y_in_C
          | odoor h0 _ _ _ _ h_D_eq => rw [h_D_eq]; exact Finset.mem_insert_of_mem y_in_C
        · cases h_door with
          | idoor h0 _ x _ h_sigma_eq _ =>
            rw [← h_sigma_eq, Finset.image_insert] at y_notin_img_sigma
            simp only [Finset.mem_insert, not_or] at y_notin_img_sigma
            exact y_notin_img_sigma.2
          | odoor h0 _ _ _ h_sigma_eq _ =>
            rw [← h_sigma_eq] at y_notin_img_sigma
            exact y_notin_img_sigma
      have h_i_in_diff : i ∈ D \ image c τ := h_subset (h_room_typed.2 ▸ Finset.mem_singleton_self i)
      have h_card_one : (D \ image c τ).card = 1 := h_nc.2
      obtain ⟨j, hj⟩ := Finset.card_eq_one.mp h_card_one
      have hij : i = j := Finset.mem_singleton.mp (by simpa [hj] using h_i_in_diff)
      simpa [hij] using hj
  have exists_filter_isOutsideDoor_eq_singleton (c : T → I) (i : I) :
      ∃ x, filter (fun x => isOutsideDoor x.1.1 x.1.2) (doubleCountingSet c i) = {x} := by
    classical
    have h_T_nonempty : Nonempty T := ⟨(default : T)⟩
    have h_T_univ_nonempty : (Finset.univ : Finset T).Nonempty := Finset.univ_nonempty_iff.mpr h_T_nonempty
    let x_max_i : T := @Finset.max' T (IST.IST i) Finset.univ h_T_univ_nonempty
    let σ_u : Finset T := {x_max_i}
    let C_u : Finset I := {i}
    let τ_u : Finset T := Finset.empty
    let D_u : Finset I := {i}
    let x_unique : (Finset T × Finset I) × (Finset T × Finset I) := ((τ_u, D_u), (σ_u, C_u))
    have h_outside_door_τu_Du : isOutsideDoor τ_u D_u := outsidedoor_singleton i
    have h_typed_nc : isTypedNC c i τ_u D_u := by
      constructor
      · exact (NC_of_outsidedoor (c := c) h_outside_door_τu_Du).1
      · simp only [τ_u]
        constructor
    have h_door_relation : isDoorof τ_u D_u σ_u C_u := by
      apply isDoorof.idoor
      · intro y
        use i
        constructor
        · simp only [C_u, Finset.mem_singleton]
        · intro x hx
          simp only [σ_u] at hx
          simp only [Finset.mem_singleton] at hx
          rw [hx]
          exact @Finset.le_max' T (IST.IST i) Finset.univ y (Finset.mem_univ y)
      · exact h_outside_door_τu_Du.1
      · simp only [τ_u]
        exact Finset.notMem_empty x_max_i
      · simp only [τ_u, σ_u]
        rfl
      · rfl
    use x_unique
    ext x_gen
    simp only [mem_filter, mem_univ, mem_singleton]
    constructor
    · intro h_in_filter
      simp at h_in_filter
      obtain ⟨h_in_db, h_outside⟩ := h_in_filter
      obtain ⟨h_typed, h_door⟩ := h_in_db
      obtain ⟨h_is_door, h_empty⟩ := h_outside
      have h_empty_image : (x_gen.1.1).image c = ∅ := by
        rw [h_empty]
        exact Finset.image_empty c
      have h_x_gen_1_2_eq : x_gen.1.2 = {i} := by
        have h_eq := h_typed.2
        rw [h_empty_image] at h_eq
        simp at h_eq
        exact h_eq
      obtain ⟨_, h_D_singleton⟩ := outsidedoor_is_singleton ⟨h_is_door, h_empty⟩
      obtain ⟨j, h_D_eq⟩ := h_D_singleton
      have h_j_eq_i : j = i := by
        have h_eq_j : x_gen.1.2 = {j} := h_D_eq
        rw [h_x_gen_1_2_eq] at h_eq_j
        have : j ∈ {j} := Finset.mem_singleton_self j
        rw [←h_eq_j] at this
        exact Finset.eq_of_mem_singleton this
      cases h_door with
      | idoor h_cell_σC h_door_τD x h_x_notin h_insert_eq h_D_eq_C =>
        have h_σ_eq : x_gen.2.1 = {x} := by
          rw [←h_insert_eq, h_empty]
          rfl
        have h_x_eq_max : x = x_max_i := by
          have h_dom : ∀ y, y ≤[i] x := by
            intro y
            obtain ⟨j_dom, hj_in, hj_dom⟩ := h_cell_σC y
            rw [←h_D_eq_C, h_x_gen_1_2_eq] at hj_in
            simp at hj_in
            subst hj_in
            apply hj_dom
            rw [h_σ_eq]
            simp
          have h1 : x ≤[i] x_max_i := @Finset.le_max' T (IST.IST i) Finset.univ x (Finset.mem_univ x)
          have h2 : x_max_i ≤[i] x := h_dom x_max_i
          exact @le_antisymm T (IST.IST i).toPartialOrder x x_max_i h1 h2
        apply Prod.ext
        · apply Prod.ext
          · exact h_empty
          · rw [h_x_gen_1_2_eq]
        · apply Prod.ext
          · rw [h_σ_eq, h_x_eq_max]
          · rw [←h_D_eq_C, h_x_gen_1_2_eq]
      | odoor h_cell_σC h_door_τD j h_j_notin h_τ_eq h_D_insert =>
        exfalso
        have h_σ_empty : x_gen.2.1 = ∅ := by
          rw [←h_τ_eq, h_empty]
          rfl
        let h_door_constructed : isDoorof x_gen.1.1 x_gen.1.2 x_gen.2.1 x_gen.2.2 :=
          isDoorof.odoor h_cell_σC ⟨h_is_door.1, h_is_door.2⟩ j h_j_notin h_τ_eq h_D_insert
        have h_room : IST.isRoom x_gen.2.1 x_gen.2.2 := isRoom_of_Door h_door_constructed
        have h_σ_nonempty : x_gen.2.1.Nonempty := sigma_nonempty_of_room h_room
        rw [h_σ_empty] at h_σ_nonempty
        exact Finset.not_nonempty_empty h_σ_nonempty
    · intro h_eq
      rw [h_eq]
      simp only [true_and]
      constructor
      · constructor
        · exact h_typed_nc
        · exact h_door_relation
      · exact h_outside_door_τu_Du
  have odd_card_filter_isOutsideDoor (c : T → I) (i : I) :
      Odd (filter (fun x => isOutsideDoor x.1.1 x.1.2) (doubleCountingSet c i)).card := by
    have h_card_one :
        (filter (fun x => isOutsideDoor x.1.1 x.1.2) (doubleCountingSet c i)).card = 1 := by
      obtain ⟨x, hx⟩ := exists_filter_isOutsideDoor_eq_singleton c i
      simp [hx]
    rw [h_card_one]
    exact odd_one
  have card_internalDoor_fiber_eq_two (c : T → I) (i : I) (y : Finset T × Finset I)
      (hy_internal : IST.isInternalDoor y.1 y.2) (hy_typed : isTypedNC c i y.1 y.2) :
      let s := filter (fun x => ¬ isOutsideDoor x.1.1 x.1.2) (doubleCountingSet c i)
      let f := fun (x : (Finset T × Finset I) × Finset T × Finset I) => x.1
      (filter (fun a => f a = y) s).card = 2 := by
    obtain ⟨σ₁, σ₂, C₁, C₂, h_ne, h_room₁, h_room₂, h_door₁, h_door₂, h_unique⟩ :=
      internal_door_two_rooms y.1 y.2 hy_internal
    let s := filter (fun x => ¬ isOutsideDoor x.1.1 x.1.2) (doubleCountingSet c i)
    let f := fun (x : (Finset T × Finset I) × Finset T × Finset I) => x.1
    let elem1 : (Finset T × Finset I) × Finset T × Finset I := (y, (σ₁, C₁))
    let elem2 : (Finset T × Finset I) × Finset T × Finset I := (y, (σ₂, C₂))
    have elem1_in_s : elem1 ∈ s := by
      simp only [elem1, s, mem_filter]
      constructor
      · simp only [mem_univ, true_and]
        exact ⟨hy_typed, h_door₁⟩
      · intro h_outside
        exact (Finset.nonempty_iff_ne_empty.mp hy_internal.2) h_outside.2
    have elem2_in_s : elem2 ∈ s := by
      simp only [elem2, s, mem_filter]
      constructor
      · simp only [mem_univ, true_and]
        exact ⟨hy_typed, h_door₂⟩
      · intro h_outside
        exact (Finset.nonempty_iff_ne_empty.mp hy_internal.2) h_outside.2
    have elems_distinct : elem1 ≠ elem2 := by
      intro h_eq
      injection h_eq with _ h_pair_eq
      exact h_ne h_pair_eq
    have fiber_eq : filter (fun a => f a = y) s = {elem1, elem2} := by
      ext x
      constructor
      · intro hx
        rw [mem_filter] at hx
        obtain ⟨hx_s, hx_eq⟩ := hx
        rw [mem_filter] at hx_s
        obtain ⟨hx_db, _⟩ := hx_s
        rw [mem_filter] at hx_db
        obtain ⟨_, hx_typed_x, hx_door_x⟩ := hx_db
        have h_x_form : x = (y, x.2) := Prod.ext_iff.mpr ⟨hx_eq, rfl⟩
        have h_room_x2 : IST.isRoom x.2.1 x.2.2 := isRoom_of_Door hx_door_x
        have hx_door_y : isDoorof y.1 y.2 x.2.1 x.2.2 :=
          hx_eq ▸ hx_door_x
        obtain h_case1 | h_case2 := h_unique x.2.1 x.2.2 h_room_x2 hx_door_y
        · simp only [mem_insert, mem_singleton]
          left
          rw [h_x_form]
          apply Prod.ext
          · rfl
          · apply Prod.ext
            · exact h_case1.1
            · exact h_case1.2
        · simp only [mem_insert, mem_singleton]
          right
          rw [h_x_form]
          apply Prod.ext
          · rfl
          · apply Prod.ext
            · exact h_case2.1
            · exact h_case2.2
      · intro hx
        simp only [mem_insert, mem_singleton] at hx
        cases hx with
        | inl h =>
          rw [h, mem_filter]
          exact ⟨elem1_in_s, by simp [f, elem1]⟩
        | inr h =>
          rw [h, mem_filter]
          exact ⟨elem2_in_s, by simp [f, elem2]⟩
    apply Eq.trans (congrArg Finset.card fiber_eq)
    exact Finset.card_pair elems_distinct
  have even_card_filter_not_isOutsideDoor (c : T → I) (i : I) :
      Even (filter (fun x => ¬ isOutsideDoor x.1.1 x.1.2) (doubleCountingSet c i)).card := by
    let s := filter (fun x => ¬ isOutsideDoor x.1.1 x.1.2) (doubleCountingSet c i)
    let t := filter (fun (x : Finset T × Finset I) => IST.isInternalDoor x.1 x.2 ∧ isTypedNC c i x.1 x.2) univ
    let f := fun (x : (Finset T × Finset I) × Finset T × Finset I) => x.1
    have fs_in_t : ∀ x ∈ s, f x ∈ t := by
      intro x hx
      rw [mem_filter] at hx
      obtain ⟨hx_db, hx_not_outside⟩ := hx
      rw [mem_filter] at hx_db
      obtain ⟨_, hx_typed, hx_door⟩ := hx_db
      rw [mem_filter]
      simp only [mem_univ, true_and]
      constructor
      · unfold isInternalDoor
        constructor
        · cases hx_door with
          | idoor h0 h1 y h_notin h_eq h_D_eq_C => exact h1
          | odoor h0 h1 j h_notin h_eq h_D_eq => exact h1
        · by_contra h_empty
          have h_outside : isOutsideDoor x.1.1 x.1.2 := by
            constructor
            · cases hx_door with
              | idoor h0 h1 y h_notin h_eq h_D_eq_C => exact h1
              | odoor h0 h1 j h_notin h_eq h_D_eq => exact h1
            · exact Finset.not_nonempty_iff_eq_empty.mp h_empty
          exact hx_not_outside h_outside
      · exact hx_typed
    have fiber_size_two : ∀ y ∈ t, (filter (fun a=> f a = y) s).card = 2 := by
      intro y hy
      rw [mem_filter] at hy
      obtain ⟨_, hy_internal, hy_typed⟩ := hy
      exact card_internalDoor_fiber_eq_two c i y hy_internal hy_typed
    have counteq := Finset.card_eq_sum_card_fiberwise fs_in_t
    have sumeq := Finset.sum_const_nat fiber_size_two
    rw [sumeq] at counteq
    rw [counteq]
    simp only [even_two, Even.mul_left]
  have isTypedNC_of_isDoorof_of_not_isColorful {σ : Finset T} {τ : Finset T} {C : Finset I} {D : Finset I} {c : T → I} {i : I} (h1 : isTypedNC c i τ D)
      (h2 : isDoorof τ D σ C) :
      ¬ isColorful c σ C → isTypedNC c i σ C := by
    intro h_not_colorful
    obtain h_typed | h_colorful := NC_or_C_of_door h1 h2
    · exact h_typed
    · contradiction
  have card_doubleCountingSet_fiber_eq_two {σ : Finset T} {C : Finset I} {c : T → I} {i : I} (h0 : isRoom σ C) (h1 : isTypedNC c i σ C) :
    (filter (fun (x : (Finset T× Finset I)× Finset T × Finset I) => x.2 = (σ,C)) (doubleCountingSet c i)).card = 2 := by
      obtain ⟨door1, door2, h_ne, h_doors_eq⟩ := doors_of_NCroom h0 (NC_of_TNC h1)
      have h_filter_eq : filter (fun (x : (Finset T× Finset I)× Finset T × Finset I) => x.2 = (σ,C)) (doubleCountingSet c i) =
                         {(door1, (σ,C)), (door2, (σ,C))} := by
        ext x
        constructor
        · intro hx
          rw [mem_filter] at hx
          obtain ⟨h_db, h_eq⟩ := hx
          rw [mem_filter] at h_db
          obtain ⟨_, h_typed, h_door⟩ := h_db
          have h_x_form : x = (x.1, (σ,C)) := by
            rw [Prod.ext_iff]
            exact ⟨rfl, h_eq⟩
          rw [h_x_form]
          simp
          have h_x1_in_doors : x.1 ∈ NCdoors c σ C := by
            simp [NCdoors]
            have h_sigma : x.2.1 = σ := by rw [h_eq]
            have h_C : x.2.2 = C := by rw [h_eq]
            rw [h_sigma, h_C] at h_door
            exact ⟨NC_of_TNC h_typed, h_door⟩
          rw [h_doors_eq] at h_x1_in_doors
          simp at h_x1_in_doors
          exact h_x1_in_doors
        · intro hx
          simp at hx
          cases hx with
          | inl h =>
            rw [h, mem_filter]
            constructor
            · rw [mem_filter]
              have h_door1_in_doors : door1 ∈ NCdoors c σ C := by
                rw [h_doors_eq]
                exact Set.mem_insert door1 {door2}
              simp [NCdoors] at h_door1_in_doors
              exact ⟨by simp, isTypedNC_of_isNearlyColorful_of_isDoorof_isTypedNC h_door1_in_doors.1 h_door1_in_doors.2 h1, h_door1_in_doors.2⟩
            · rfl
          | inr h =>
            rw [h, mem_filter]
            constructor
            · rw [mem_filter]
              have h_door2_in_doors : door2 ∈ NCdoors c σ C := by
                rw [h_doors_eq]
                exact Set.mem_insert_of_mem door1 (Set.mem_singleton door2)
              simp [NCdoors] at h_door2_in_doors
              exact ⟨by simp, isTypedNC_of_isNearlyColorful_of_isDoorof_isTypedNC h_door2_in_doors.1 h_door2_in_doors.2 h1, h_door2_in_doors.2⟩
            · rfl
      rw [h_filter_eq]
      simp [h_ne]
  have even_card_filter_not_isColorful (c : T → I) (i : I) :
      Even (filter (fun x => ¬isColorful c x.2.1 x.2.2) (doubleCountingSet c i)).card := by
    let s := filter (fun x => ¬isColorful c x.2.1 x.2.2) (doubleCountingSet c i)
    let t := filter (fun (x : Finset T × Finset I) => IST.isRoom x.1 x.2 ∧ isTypedNC c i x.1 x.2 ) univ
    let f := fun (x : (Finset T × Finset I)× Finset T × Finset I) => x.2
    have fs_in_t : ∀ x ∈ s, f x ∈ t := by
      intro x hx;
      show x.2 ∈ t
      rw [mem_filter] at hx
      obtain ⟨hx1,hx2⟩ := hx
      rw [mem_filter] at hx1
      rw [mem_filter]
      refine ⟨by simp, isRoom_of_Door hx1.2.2,?_⟩
      apply isTypedNC_of_isDoorof_of_not_isColorful hx1.2.1 hx1.2.2 hx2
    have counteq := Finset.card_eq_sum_card_fiberwise fs_in_t
    have fiber_sizetwo :∀ y ∈ t, #(filter (fun a=> f a = y) s) = 2  :=
      by
        intro y hy
        rw [Finset.mem_filter] at hy
        obtain ⟨_,hy1,hy2⟩ := hy
        unfold s
        rw [filter_filter]
        have f2 := card_doubleCountingSet_fiber_eq_two hy1 hy2
        rw [<-f2]
        congr 1
        apply filter_congr
        intro x hx
        rw [mem_filter] at hx
        obtain ⟨hx1,hx2,hx3⟩ := hx
        unfold f
        constructor
        · simp
        · intro h
          simp_rw [h,and_true]
          exact not_colorful_of_TypedNC hy2
    have sumeq := Finset.sum_const_nat fiber_sizetwo
    rw [sumeq] at counteq
    rw [counteq]
    simp only [even_two, Even.mul_left]
  have odd_of_odd_add_even_eq_add_even {a b c d : ℕ}
      (h1 : Odd a) (h2 : Even b) (h3 : Even d) (h4 : a + b = c + d) : Odd c := by
    by_contra h0
    replace h0 := Nat.not_odd_iff_even.1 h0
    have oddab := Even.odd_add h2 h1
    rw [h4] at oddab
    have evencd := Even.add h0 h3
    exact Nat.not_odd_iff_even.2 evencd oddab
  have odd_card_filter_isColorful (c : T → I) (i : I) : Odd (Finset.filter (fun (x: (Finset T× Finset I) × Finset T × Finset I) =>  isColorful c x.2.1 x.2.2) (doubleCountingSet c i)).card
  := by
    let s := doubleCountingSet c i
    have cardeq' :=
      (Finset.card_filter_add_card_filter_not (s := s)
        (fun x => isOutsideDoor x.1.1 x.1.2)).symm
    have cardeq :=
      (Finset.card_filter_add_card_filter_not (s := s)
        (fun x => isColorful c x.2.1 x.2.2)).symm
    apply odd_of_odd_add_even_eq_add_even (odd_card_filter_isOutsideDoor c i)
      (even_card_filter_not_isOutsideDoor c i) (even_card_filter_not_isColorful c i)
    rw [<-cardeq',<-cardeq]
  have cardpos := Odd.pos $ odd_card_filter_isColorful c default
  replace nonempty:= Finset.card_pos.1 cardpos
  obtain ⟨x,hx⟩ := nonempty
  replace hx := (Finset.mem_filter.1 hx).2
  use x.2
  simp only [mem_filter, mem_univ, hx, and_self]
end IndexedLOrder
end D5.S3.Combinatorics.Scarf
