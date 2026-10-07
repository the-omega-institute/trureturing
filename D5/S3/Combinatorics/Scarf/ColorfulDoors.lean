/- GID: D5/S3/Combinatorics/Scarf/ColorfulDoors
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Scarf/ColorfulDoors
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Convex.StdSimplex]
   utility: none
   digest: The injective-color and one-collision cases construct and exhaust two distinct nearly colorful doors. -/
/- proof_shape: doors_of_NCroom: content
   admission_basis: escape-witness
   escape_witness: The injective-color and one-collision cases construct and exhaust two distinct nearly colorful doors.
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

import D5.S3.Combinatorics.Scarf.Incidence
open Classical Finset
set_option quotPrecheck false
namespace D5.S3.Combinatorics.Scarf
variable {T : Type*} {I : Type*} [Inhabited T] [DecidableEq T] [DecidableEq I]
variable [IST : IndexedLOrder I T]
local notation lhs "<[" i "]" rhs => (IST.IST i).lt lhs rhs
local notation lhs "≤[" i "]" rhs => (IST.IST i).le lhs rhs
namespace IndexedLOrder
variable (c : T → I) (σ : Finset T) (C : Finset I)
def isColorful : Prop := IST.isCell σ C ∧ σ.image c   = C
def isNearlyColorful : Prop := IST.isCell σ C ∧ (C \ σ.image c).card = 1
def isTypedNC (i : I) (σ : Finset T) (C : Finset I): Prop := IST.isCell σ C ∧ (C \ (σ.image c)) = {i}
abbrev NCdoors := {(τ,D) | isNearlyColorful c τ D ∧ isDoorof τ D σ C }
variable {c σ C}
lemma doors_of_NCroom {σ : Finset T} {C : Finset I} {c : T → I} [DecidableEq T] (h_room : isRoom σ C) (h_nc : isNearlyColorful c σ C) :
  ∃ door1 door2, door1 ≠ door2 ∧ NCdoors c σ C = {door1, door2} := by
  classical
  let minAt {σ : Finset T} (h2 : σ.Nonempty) (i : I) : T :=
    @Finset.min' T (IST.IST i) σ h2
  have Dominant_of_subset (σ τ : Finset T) (C : Finset I) :
    τ ⊆ σ → isDominant σ C  → isDominant τ C := by
      intro h1 h2 y
      obtain ⟨j,hj⟩:= h2 y
      use j,hj.1
      intro x hx
      exact hj.2 x (h1 hx)
  have Dominant_of_supset (σ : Finset T) (C D: Finset I) :
    C ⊆ D → isDominant σ C  → isDominant σ D := by
      intro h1 h2 y
      obtain ⟨j,hj⟩:= h2 y
      use j,(h1 hj.1)
      intro x hx
      exact hj.2 x hx
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
  have card_le_of_isDominant {σ : Finset T} {C: Finset I} (h1 : IST.isDominant σ C) : σ.card  ≤  C.card  := by
    by_cases h2 : σ.Nonempty
    · rw [keylemma_of_dominant h1 h2]
      apply Finset.card_image_le
    · rw [not_nonempty_iff_eq_empty] at h2
      simp only [h2, card_empty, zero_le]
  have card_of_NCcell {σ : Finset T} {D : Finset I} {c : T → I} (h : isNearlyColorful c σ D) : #σ = #(image c σ)  ∨  #σ = #(image c σ) + 1 := by
    unfold isNearlyColorful at h
    rcases h with ⟨h_cell, h_nc_card⟩
    let img := image c σ
    have h_card_le_D : σ.card ≤ D.card := card_le_of_isDominant h_cell
    have h_D_card_eq := (Finset.card_sdiff_add_card_inter D img).symm
    rw [h_nc_card] at h_D_card_eq
    have h_inter_le_img : (D ∩ img).card ≤ img.card := card_le_card (Finset.inter_subset_right)
    have h_D_le : D.card ≤ 1 + img.card := by
      linarith [h_D_card_eq, h_inter_le_img]
    have h_img_le_sigma : img.card ≤ σ.card := card_image_le
    have h_sigma_le_plus_one : σ.card ≤ img.card + 1 := by
      linarith [h_card_le_D, h_D_le]
    have h_or : σ.card ≤ img.card ∨ σ.card = img.card + 1 := by
      apply Nat.le_or_eq_of_le_succ
      exact h_sigma_le_plus_one
    cases h_or with
    | inl h_le =>
      left
      exact le_antisymm h_le h_img_le_sigma
    | inr h_eq =>
      right
      exact h_eq
  have image_erase_eq_erase_image_of_unique
    (σ : Finset T) (c : T → I) {z : T}
    (_ : z ∈ σ)
    (uniq : ∀ ⦃w⦄, w ∈ σ → c w = c z → w = z) :
    (σ.erase z).image c = (σ.image c).erase (c z) := by
    ext i
    constructor
    · intro hi
      rcases Finset.mem_image.mp hi with ⟨w, hw_in_erase, rfl⟩
      rcases Finset.mem_erase.mp hw_in_erase with ⟨hw_ne_z, hw_in_σ⟩
      have h_ne_color : c w ≠ c z := by
        intro h_eq
        have := uniq hw_in_σ h_eq
        exact hw_ne_z this
      exact Finset.mem_erase.mpr ⟨h_ne_color, Finset.mem_image.mpr ⟨w, hw_in_σ, rfl⟩⟩
    · intro hi
      rcases Finset.mem_erase.mp hi with ⟨h_i_ne, hi_img⟩
      rcases Finset.mem_image.mp hi_img with ⟨w, hw_in_σ, rfl⟩
      have hw_ne_z : w ≠ z := by
        intro h_eq
        apply h_i_ne
        simp [h_eq]
      exact Finset.mem_image.mpr ⟨w, Finset.mem_erase.mpr ⟨hw_ne_z, hw_in_σ⟩, rfl⟩
  have three_collision_card_bound (σ : Finset T) (c : T → I)
      (a b z : T) (ha_in_σ : a ∈ σ) (hb_in_σ : b ∈ σ) (hz_in_σ : z ∈ σ)
      (hab_ne : a ≠ b) (haz_ne : a ≠ z) (hbz_ne : b ≠ z)
      (hc_eq : c a = c b) (hcz_eq : c b = c z) :
      σ.card ≥ (σ.image c).card + 2 := by
    let σ_rest := σ \ {a, b, z}
    have h_three_subset_sigma : {a, b, z} ⊆ σ := by
      intro w hw; simp at hw; rcases hw with (rfl | rfl | rfl);
      · exact ha_in_σ
      · exact hb_in_σ
      · exact hz_in_σ
    have h_partition : σ = {a, b, z} ∪ σ_rest :=
      (Finset.union_sdiff_of_subset h_three_subset_sigma).symm
    have h_disjoint : Disjoint ({a, b, z} : Finset T) σ_rest :=
      Finset.disjoint_sdiff
    have h_card_partition : σ.card = ({a, b, z} : Finset T).card + σ_rest.card := by
      rw [h_partition, Finset.card_union_of_disjoint h_disjoint]
    have h_triple_card : ({a, b, z} : Finset T).card = 3 := by
      rw [Finset.card_eq_three]
      exact ⟨a, b, z, hab_ne, haz_ne, hbz_ne, rfl⟩
    have h_image_bound : (σ.image c).card ≤ σ_rest.card + 1 := by
      have h_image_union : σ.image c = insert (c a) (σ_rest.image c) := by
        ext i; simp only [Finset.mem_image, Finset.mem_insert]
        constructor
        · rintro ⟨t, ht_in_σ, rfl⟩
          by_cases h_t_abz : t ∈ ({a, b, z} : Finset T)
          · simp at h_t_abz; rcases h_t_abz with (rfl | rfl | rfl)
            · left; rfl
            · left; exact hc_eq.symm
            · left; exact (hc_eq.trans hcz_eq).symm
          · right; use t; simp [σ_rest, ht_in_σ, h_t_abz]
        · rintro (rfl | ⟨t, ht_in_rest, rfl⟩)
          · use a
          · use t; exact ⟨(Finset.mem_sdiff.mp ht_in_rest).1, rfl⟩
      rw [h_image_union]
      linarith [Finset.card_insert_le (c a) (σ_rest.image c), Finset.card_image_le (f := c) (s := σ_rest)]
    calc σ.card
        = 3 + σ_rest.card           := by rw [h_card_partition, h_triple_card]
      _ = σ_rest.card + 3           := by ring
      _ = (σ_rest.card + 1) + 2     := by ring
      _ ≥ (σ.image c).card + 2      := by omega
  have image_erase_eq_of_exists_other (σ : Finset T) (c : T → I)
      (x y : T) (_hx_in_σ : x ∈ σ) (hy_in_σ : y ∈ σ) (hxy_ne : x ≠ y)
      (hcxy_eq : c x = c y) :
      (σ.erase x).image c = σ.image c := by
    ext z
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨w, hw_in_erased, rfl⟩
      exact ⟨w, (Finset.mem_erase.mp hw_in_erased).2, rfl⟩
    · rintro ⟨w, hw_in_σ, rfl⟩
      by_cases hwx : w = x
      · subst w
        exact ⟨y, Finset.mem_erase.mpr ⟨hxy_ne.symm, hy_in_σ⟩, hcxy_eq.symm⟩
      · exact ⟨w, Finset.mem_erase.mpr ⟨hwx, hw_in_σ⟩, rfl⟩
  have image_erase_collision_preserves (σ : Finset T) (c : T → I)
      (x y : T) (hx_in_σ : x ∈ σ) (hy_in_σ : y ∈ σ) (hxy_ne : x ≠ y) (hcxy_eq : c x = c y) :
      (σ.erase x).image c = σ.image c ∧ (σ.erase y).image c = σ.image c := by
    exact ⟨
      image_erase_eq_of_exists_other σ c x y hx_in_σ hy_in_σ hxy_ne hcxy_eq,
      image_erase_eq_of_exists_other σ c y x hy_in_σ hx_in_σ hxy_ne.symm hcxy_eq.symm⟩
  have isDoorof_erase_of_isRoom (σ : Finset T) (C : Finset I)
      (x : T) (h_room : isRoom σ C) (hx_in_σ : x ∈ σ) :
      isDoorof (σ.erase x) C σ C := by
    apply isDoorof.idoor h_room.1
    · constructor
      · exact Dominant_of_subset σ (σ.erase x) C (Finset.erase_subset x σ) h_room.1
      · rw [h_room.2]
        rw [Finset.card_erase_of_mem hx_in_σ]
        exact (Nat.sub_add_cancel (Finset.card_pos.mpr ⟨x, hx_in_σ⟩)).symm
    · exact Finset.notMem_erase x σ
    · exact Finset.insert_erase hx_in_σ
    · rfl
  have image_subset_of_NCroom_of_card_image_add_one {σ : Finset T} {C : Finset I} {c : T → I}
      (h_room : isRoom σ C) (h_nc : isNearlyColorful c σ C)
      (h_card : σ.card = (σ.image c).card + 1) :
      σ.image c ⊆ C := by
    have h_C_card_img : C.card = (σ.image c).card + 1 := by
      rw [h_room.2, h_card]
    have h_C_card_form :
        C.card = (C \ σ.image c).card + (C ∩ σ.image c).card :=
      (Finset.card_sdiff_add_card_inter C (σ.image c)).symm
    rw [h_nc.2] at h_C_card_form
    have h_img_eq_inter_card : (σ.image c).card = (C ∩ σ.image c).card := by
      omega
    have h_inter_eq_img : C ∩ σ.image c = σ.image c :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by rw [h_img_eq_inter_card])
    rwa [Finset.inter_eq_right] at h_inter_eq_img
  have h_cases := card_of_NCcell h_nc
  have h_card_eq : C.card = σ.card := h_room.2
  have h_cell : isCell σ C := h_room.1
  let img := image c σ
  cases h_cases with
  | inl h_eq =>
    have h_inj_on_σ : Set.InjOn c ↑σ := (Finset.card_image_iff).mp h_eq.symm
    have h_img_C_card_1 : (img \ C).card = 1 := by
      have h_card_eq' : C.card = img.card := by linarith [h_card_eq, h_eq]
      have h_C_sdiff := Finset.card_sdiff_add_card_inter C img
      rw [h_nc.2, h_card_eq'] at h_C_sdiff
      have h_img_sdiff := Finset.card_sdiff_add_card_inter img C
      rw [Finset.inter_comm] at h_C_sdiff
      linarith [h_C_sdiff, h_img_sdiff]
    obtain ⟨c_y, h_img_C_eq⟩ := Finset.card_eq_one.mp h_img_C_card_1
    have h_c_y_in_img : c_y ∈ img := by
      have : c_y ∈ img \ C := by rw [h_img_C_eq]; simp
      exact (Finset.mem_sdiff.mp this).1
    have h_c_y_notin_C : c_y ∉ C := by
      have : c_y ∈ img \ C := by rw [h_img_C_eq]; simp
      exact (Finset.mem_sdiff.mp this).2
    obtain ⟨y, h_y_in_σ, h_c_y_eq⟩ := Finset.mem_image.mp h_c_y_in_img
    subst h_c_y_eq
    have h_y_unique : ∀ ⦃z⦄, z ∈ σ → c z = c y → z = y :=
      λ z hz hcz => h_inj_on_σ hz h_y_in_σ hcz
    let door1 := (σ.erase y, C)
    let door2 := (σ, insert (c y) C)
    use door1, door2
    constructor
    · intro h_eq_doors; simp [Prod.ext_iff] at h_eq_doors;
      have this := h_eq_doors.1
      have : y ∉ σ := Finset.erase_eq_self.mp this
      exact this h_y_in_σ
    · ext ⟨τ, D⟩; constructor
      · intro h
        rcases h with ⟨h_nc_door, h_is_door⟩
        cases h_is_door with
        | idoor h0 h_door x hx_notin_τ h_insert_x h_D_eq_C =>
          subst h_D_eq_C
          have h_nc_card := h_nc_door.2
          have h_x_in_σ : x ∈ σ := by rw [←h_insert_x]; exact Finset.mem_insert_self x τ
          have h_τ_eq_erase : τ = σ.erase x := by rw [←Finset.erase_insert hx_notin_τ, h_insert_x]
          have h_x_unique : ∀ ⦃w⦄, w ∈ σ → c w = c x → w = x := by
            intro w hw hcw
            exact h_inj_on_σ hw h_x_in_σ hcw
          have h_img_erase : (τ.image c) = img.erase (c x) := by
            rw [h_τ_eq_erase]
            exact image_erase_eq_erase_image_of_unique σ c h_x_in_σ h_x_unique
          rw [h_img_erase] at h_nc_card
          by_cases h_x_eq_y : x = y
          · subst h_x_eq_y
            simp [h_τ_eq_erase, door1]
          · have h_cx_in_D : c x ∈ D := by
              by_contra h_cx_notin_C
              have h_cx_in_img_diff_D : c x ∈ img \ D := Finset.mem_sdiff.mpr ⟨Finset.mem_image_of_mem c h_x_in_σ, h_cx_notin_C⟩
              rw [h_img_C_eq, Finset.mem_singleton] at h_cx_in_img_diff_D
              have h_c_eq : c x = c y := by rw [h_cx_in_img_diff_D]
              have x_in_sigma : x ∈ σ := by
                have : x ∈ insert x τ := Finset.mem_insert_self x τ
                have : x ∈ σ := by
                  rw [←h_insert_x]
                  exact Finset.mem_insert_self x τ
                exact this
              have := h_y_unique x_in_sigma h_c_eq
              exact h_x_eq_y this
            exfalso
            have h_card_2 : (D \ (img.erase (c x))).card = 2 := by
              have h_cx_not_in_diff : c x ∉ D \ img := by
                intro h
                exact (Finset.mem_sdiff.mp h).2 (Finset.mem_image_of_mem c h_x_in_σ)
              rw [Finset.sdiff_erase h_cx_in_D,
                Finset.card_insert_of_notMem h_cx_not_in_diff, h_nc.2]
            rw [h_card_2] at h_nc_card; linarith
           | odoor h0 h_door j hj_notin_C h_τ_eq_σ h_D_eq_insert =>
            subst h_τ_eq_σ; subst h_D_eq_insert
            have h_nc_card := h_nc_door.2
            by_cases h_j_eq_cy : j = c y
            · subst h_j_eq_cy; simp; right; rfl
            · exfalso
              have h_j_notin_img : j ∉ img := by
                intro h_j_in_img
                have h_j_in_img_diff_C : j ∈ img \ C := Finset.mem_sdiff.mpr ⟨h_j_in_img, hj_notin_C⟩
                rw [h_img_C_eq, Finset.mem_singleton] at h_j_in_img_diff_C
                exact h_j_eq_cy h_j_in_img_diff_C
              have h_card_2 : ((insert j C) \ img).card = 2 := by
                have h_j_notin_diff : j ∉ C \ img := fun h =>
                  hj_notin_C (Finset.mem_sdiff.mp h).1
                rw [Finset.insert_sdiff_of_notMem C h_j_notin_img,
                  Finset.card_insert_of_notMem h_j_notin_diff, h_nc.2]
              rw [h_card_2] at h_nc_card; linarith
      · intro h
        simp at h
        rcases h with (h_eq1 | h_eq2)
        · have ⟨h_τ_eq, h_D_eq⟩ : τ = σ.erase y ∧ D = C := Prod.mk.inj h_eq1
          subst h_τ_eq h_D_eq
          constructor
          · unfold isNearlyColorful
            constructor
            · unfold isCell
              exact Dominant_of_subset _ _ D (Finset.erase_subset y σ) h_cell
            · rw [image_erase_eq_erase_image_of_unique σ c h_y_in_σ h_y_unique]
              have h_eq_diff : D \ (image c σ).erase (c y) = D \ image c σ := by
                ext z
                constructor
                · intro h
                  simp only [Finset.mem_sdiff, Finset.mem_erase] at h ⊢
                  exact ⟨h.1, fun h_in => h.2 ⟨fun h_eq => h_c_y_notin_C (h_eq ▸ h.1), h_in⟩⟩
                · intro h
                  simp only [Finset.mem_sdiff, Finset.mem_erase] at h ⊢
                  exact ⟨h.1, fun ⟨_, h_in⟩ => h.2 h_in⟩
              rw [h_eq_diff, h_nc.2]
          · apply isDoorof.idoor
            · exact h_cell
            · constructor
              · unfold isCell
                exact Dominant_of_subset _ _ D (Finset.erase_subset y σ) h_cell
              · rw [Finset.card_erase_of_mem h_y_in_σ, h_card_eq]
                exact (Nat.sub_add_cancel (Finset.card_pos.mpr ⟨y, h_y_in_σ⟩)).symm
            · exact Finset.notMem_erase y σ
            · exact Finset.insert_erase h_y_in_σ
            · rfl
        · have ⟨h_τ_eq, h_D_eq⟩ : τ = σ ∧ D = insert (c y) C := Prod.mk.inj h_eq2
          subst h_τ_eq h_D_eq
          constructor
          · unfold isNearlyColorful
            constructor
            · unfold isCell
              unfold isDominant
              intro z
              obtain ⟨i, hi_in_C, hi_dom⟩ := h_cell z
              use i, Finset.mem_insert_of_mem hi_in_C
            · have h_j_in_img : c y ∈ img := Finset.mem_image_of_mem c h_y_in_σ
              have h_sdiff_insert : (insert (c y) C) \ img = C \ img := by
                rw [Finset.insert_sdiff_of_mem _ h_j_in_img]
              rw [h_sdiff_insert, h_nc.2]
          · apply isDoorof.odoor
            · exact h_cell
            · constructor
              · apply Dominant_of_supset τ C (insert (c y) C)
                · exact Finset.subset_insert (c y) C
                · exact h_cell
              · rw [Finset.card_insert_of_notMem h_c_y_notin_C, h_card_eq]
            · exact h_c_y_notin_C
            · rfl
            · rfl
  | inr h_inj =>
    have h_img_subset_C : image c σ ⊆ C :=
      image_subset_of_NCroom_of_card_image_add_one h_room h_nc h_inj
    unfold isNearlyColorful at h_nc
    obtain ⟨h_cell, h_missing_card⟩ := h_nc
    have h_collision : ∃ x y, x ∈ σ ∧ y ∈ σ ∧ c x = c y ∧ x ≠ y ∧
        Set.InjOn c (↑(σ \ ({x, y} : Finset T)) : Set T) := by
      obtain ⟨t, hts, hinj, himage⟩ :=
        Finset.exists_subset_injOn_image_eq_of_surjOn (σ : Set T) (σ.image c)
          (by intro y hy; exact Finset.mem_image.mp hy)
      have ht : t ⊆ σ := hts
      have hcard : t.card = (σ.image c).card := by
        rw [← himage, Finset.card_image_of_injOn hinj]
      have hdiff : (σ \ t).card = 1 := by
        rw [Finset.card_sdiff_of_subset ht, h_inj, ← hcard]
        omega
      obtain ⟨b, hb⟩ := Finset.card_eq_one.mp hdiff
      have hbs : b ∈ σ := (Finset.mem_sdiff.mp (hb.symm ▸ Finset.mem_singleton_self b)).1
      have hbnt : b ∉ t := (Finset.mem_sdiff.mp (hb.symm ▸ Finset.mem_singleton_self b)).2
      have hfb : c b ∈ t.image c := by
        rw [himage]
        exact Finset.mem_image.mpr ⟨b, hbs, rfl⟩
      obtain ⟨a, ha, hab⟩ := Finset.mem_image.mp hfb
      refine ⟨a, b, ht ha, hbs, hab, ?_, ?_⟩
      · intro heq
        exact hbnt (heq ▸ ha)
      · apply hinj.mono
        intro x hx
        rcases Finset.mem_sdiff.mp hx with ⟨hxs, hxab⟩
        have hxnb : x ≠ b := by
          intro hxb
          apply hxab
          simp [hxb]
        by_contra hxnt
        have hxb : x ∈ σ \ t := Finset.mem_sdiff.mpr ⟨hxs, hxnt⟩
        rw [hb] at hxb
        exact hxnb (Finset.mem_singleton.mp hxb)
    obtain ⟨x, y, h_x_in_σ, h_y_in_σ, h_cxy_eq, h_xy_ne, h_inj_outside⟩ := h_collision
    let τ₁ := σ.erase x
    let τ₂ := σ.erase y
    let door1 := (τ₁, C)
    let door2 := (τ₂, C)
    have h_door1_valid : isDoorof τ₁ C σ C :=
      isDoorof_erase_of_isRoom σ C x h_room h_x_in_σ
    have h_door2_valid : isDoorof τ₂ C σ C :=
      isDoorof_erase_of_isRoom σ C y h_room h_y_in_σ
    have h_imgs_preserved := image_erase_collision_preserves σ c x y h_x_in_σ h_y_in_σ h_xy_ne h_cxy_eq
    have h_door1_nc : isNearlyColorful c τ₁ C := by
      unfold isNearlyColorful
      constructor
      · exact Dominant_of_subset σ τ₁ C (Finset.erase_subset x σ) h_cell
      · rw [h_imgs_preserved.1, h_missing_card]
    have h_door2_nc : isNearlyColorful c τ₂ C := by
      unfold isNearlyColorful
      constructor
      · exact Dominant_of_subset σ τ₂ C (Finset.erase_subset y σ) h_cell
      · rw [h_imgs_preserved.2, h_missing_card]
    have h_doors_distinct : door1 ≠ door2 := by
      simp [door1, door2, τ₁, τ₂]
      intro h_eq
      have h_y_mem : y ∈ σ.erase x := by
        rw [Finset.mem_erase]
        exact ⟨h_xy_ne.symm, h_y_in_σ⟩
      rw [h_eq] at h_y_mem
      have h_y_not_mem : y ∉ σ.erase y := by
        rw [Finset.mem_erase]
        simp
      exact h_y_not_mem h_y_mem
    have h_exactly_two : NCdoors c σ C = {door1, door2} := by
      ext ⟨τ, D⟩
      simp [NCdoors]
      constructor
      · intro ⟨h_nc_τD, h_door_τD⟩
        cases h_door_τD with
        | idoor h_cell_σC h_door_τD z h_z_notin_τ h_insert_eq h_D_eq_C =>
          rw [h_D_eq_C]
          have h_τ_eq : τ = σ.erase z := by
            rw [←Finset.erase_insert h_z_notin_τ, h_insert_eq]
          rw [h_τ_eq]
          have h_z_in_σ : z ∈ σ := by
            rw [←h_insert_eq]
            exact Finset.mem_insert_self z τ
          by_cases h_z_cases : z = x ∨ z = y
          · rcases h_z_cases with h_z_eq_x | h_z_eq_y
            · left; simp [door1, τ₁, h_z_eq_x]
            · right; simp [door2, τ₂, h_z_eq_y]
          · exfalso
            push Not at h_z_cases
            have h_card_is_one : (C \ (σ.erase z).image c).card = 1 := by rw [←h_D_eq_C, ←h_τ_eq]; exact h_nc_τD.2
            have h_card_is_two : (C \ (σ.erase z).image c).card = 2 := by
              have h_uniq_z : ∀ w ∈ σ, c w = c z → w = z := by
                intro w hw hcw
                have hw_not_pair : w ∉ ({x, y} : Finset T) := by
                  intro hw_pair
                  have hcyz : c y = c z := by
                    simp only [Finset.mem_insert, Finset.mem_singleton] at hw_pair
                    rcases hw_pair with rfl | rfl
                    · exact h_cxy_eq.symm.trans hcw
                    · exact hcw
                  have h_card_ge_img_add_2 :
                      σ.card ≥ (σ.image c).card + 2 :=
                    three_collision_card_bound σ c x y z h_x_in_σ h_y_in_σ h_z_in_σ
                      h_xy_ne h_z_cases.1.symm h_z_cases.2.symm h_cxy_eq hcyz
                  omega
                have hw_sdiff : w ∈ σ \ {x, y} :=
                  Finset.mem_sdiff.mpr ⟨hw, hw_not_pair⟩
                have hz_sdiff : z ∈ σ \ {x, y} :=
                  Finset.mem_sdiff.mpr ⟨h_z_in_σ, by simpa using h_z_cases⟩
                exact h_inj_outside (by simpa using hw_sdiff) (by simpa using hz_sdiff) hcw
              have h_img_erase : (σ.erase z).image c = (σ.image c).erase (c z) :=
                image_erase_eq_erase_image_of_unique σ c h_z_in_σ h_uniq_z
              have h_cz_in_C : c z ∈ C := h_img_subset_C (mem_image_of_mem c h_z_in_σ)
              have h_cz_not_in_diff : c z ∉ C \ image c σ := by simp [mem_image_of_mem c h_z_in_σ]
              rw [h_img_erase, Finset.sdiff_erase h_cz_in_C,
                Finset.card_insert_of_notMem h_cz_not_in_diff, h_missing_card]
            rw [h_card_is_two] at h_card_is_one
            norm_num at h_card_is_one
        | odoor h_cell_σC h_door_τD j h_j_notin_C h_τ_eq_σ h_D_eq =>
          exfalso
          have h_card_is_one : ((insert j C) \ σ.image c).card = 1 := by
            rw [← h_D_eq, ← h_τ_eq_σ]
            exact h_nc_τD.2
          have h_j_notin_img : j ∉ image c σ := fun h => h_j_notin_C (h_img_subset_C h)
          have h_card_is_two : ((insert j C) \ σ.image c).card = 2 := by
            have h_j_notin_diff : j ∉ C \ σ.image c := fun h =>
              h_j_notin_C (Finset.mem_sdiff.mp h).1
            rw [Finset.insert_sdiff_of_notMem C h_j_notin_img,
              Finset.card_insert_of_notMem h_j_notin_diff, h_missing_card]
          rw [h_card_is_two] at h_card_is_one
          norm_num at h_card_is_one
      · intro h_or
        cases h_or with
        | inl h_eq =>
          have : τ = τ₁ ∧ D = C := Prod.mk.inj h_eq
          rw [this.1, this.2]
          exact ⟨h_door1_nc, h_door1_valid⟩
        | inr h_eq =>
          have : τ = τ₂ ∧ D = C := Prod.mk.inj h_eq
          rw [this.1, this.2]
          exact ⟨h_door2_nc, h_door2_valid⟩
    use door1, door2
end IndexedLOrder
end D5.S3.Combinatorics.Scarf
