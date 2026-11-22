/- GID: D5/S3/Combinatorics/Lattices/Tamari/BooleanRows
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Lattices/Tamari/BooleanRows
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Maximum Boolean antichains of bracketing functions are laminar interval rows. -/

import D5.S3.Combinatorics.Lattices.Tamari.BracketRows
import Mathlib.Data.Finset.Max

/-! # Maximum Boolean antichains and laminar interval rows -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Lattices.Tamari

noncomputable section

variable {n : ℕ}

abbrev Brackets (n : ℕ) := BracketingFunctions (n + 1)

/-- Garber et al., equation (2.a), with all subsets and empty meet equal to top. -/
def IsBooleanFamily {α : Type*} [CompleteLattice α] (C : Set α) : Prop :=
  IsAntichain (· ≤ ·) C ∧ (⊤ : α) ∉ C ∧
  ∀ S T : Set α, S ⊆ C → T ⊆ C → sInf S ⊔ sInf T = sInf (S ∩ T)

abbrev BooleanFamily (C : Set (Brackets n)) : Prop := IsBooleanFamily C

/-- One-based interval nesting: if the later interval reaches the earlier
right endpoint, then it contains the earlier interval. -/
def Laminar (A : (s : RowIndex n) → LeftEndpoint s) : Prop :=
  ∀ s t, s.val < t.val → (A t).val ≤ s.val → (A t).val ≤ (A s).val

private def atIndex (s : RowIndex n) : Fin (n + 1) :=
  ((rowIndexEquiv n).symm s).castSucc

private theorem atIndex_val (s : RowIndex n) : (atIndex s).val + 1 = s.val :=
  Nat.sub_add_cancel s.property.1

private def fromCoord (i : Fin (n + 1)) (hi : i < Fin.last n) : RowIndex n :=
  ⟨i.val + 1, by omega, Nat.succ_le_of_lt hi⟩

private theorem atIndex_fromCoord (i : Fin (n + 1)) (hi : i < Fin.last n) :
    atIndex (fromCoord i hi) = i :=
  Fin.ext (Nat.add_sub_cancel_right _ _)

private theorem row_le_of_coord {b : Brackets n} {s : RowIndex n} {a : LeftEndpoint s}
    (h : ∀ i : Fin (n + 1), a.val ≤ i.val + 1 → i.val + 1 ≤ s.val →
      (b.val i).val + 1 ≤ s.val) : b ≤ row s a := by
  intro i
  change (b.val i).val ≤ ((row s a).val i).val
  have hv := row_value_oneBased s a i
  have hi := (b.val i).isLt
  split at hv
  · rename_i hm
    have := h i hm.1 hm.2
    omega
  · omega

private theorem row_coord_of_le {s : RowIndex n} {a : LeftEndpoint s}
    {b : Brackets n} (i : Fin (n + 1)) (h : (row s a).val i ≤ b.val i)
    (hi : (b.val i).val < n) :
    a.val ≤ i.val + 1 ∧ i.val + 1 ≤ s.val ∧ s.val ≤ (b.val i).val + 1 := by
  have hle : ((row s a).val i).val ≤ (b.val i).val := h
  have hv := row_value_oneBased s a i
  split at hv
  · rename_i hm
    exact ⟨hm.1, hm.2, by omega⟩
  · omega

private theorem proper_has_fixed {b : Brackets n} (hb : b ≠ ⊤) :
    ∃ s : RowIndex n, b.val (atIndex s) = atIndex s := by
  have h : ∃ i : Fin (n + 1), b.val i < Fin.last n := by
    by_contra! h
    apply hb
    apply Subtype.ext
    funext i
    rw [top_coord]
    exact le_antisymm (Fin.le_last _) (h i)
  obtain ⟨i, hi⟩ := h
  refine ⟨fromCoord (b.val i) hi, ?_⟩
  rw [atIndex_fromCoord]
  exact le_antisymm (b.property.2 i _ (b.property.1 i) le_rfl) (b.property.1 _)

private theorem fixed_unique {C : Set (Brackets n)} (hC : BooleanFamily C)
    {b c : C} {s : RowIndex n}
    (hb : b.val.val (atIndex s) = atIndex s) (hc : c.val.val (atIndex s) = atIndex s) :
    b = c := by
  by_contra hne
  let d := row s (⟨s.val, s.property.1, le_rfl⟩ : LeftEndpoint s)
  have below (e : Brackets n) (he : e.val (atIndex s) = atIndex s) : e ≤ d := by
    apply row_le_of_coord
    intro i hi hs
    change s.val ≤ i.val + 1 at hi
    have hi' : i = atIndex s := Fin.ext (by have := atIndex_val s; omega)
    subst i
    rw [he, atIndex_val]
  have hd : d ≠ ⊤ := by
    intro ht
    have hv := row_value_oneBased s (⟨s.val, s.property.1, le_rfl⟩ : LeftEndpoint s) (atIndex s)
    change (d.val (atIndex s)).val + 1 = _ at hv
    rw [atIndex_val, ite_eq_left ⟨le_rfl, le_rfl⟩, ht, top_coord, Fin.val_last] at hv
    have := s.property.2
    omega
  have hvne : b.val ≠ c.val := fun h => hne (Subtype.ext h)
  have hempty : ({b.val} : Set (Brackets n)) ∩ {c.val} = ∅ := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
    rintro ⟨rfl, h⟩
    exact hvne h
  have h := hC.2.2 {b.val} {c.val} (Set.singleton_subset_iff.mpr b.property)
    (Set.singleton_subset_iff.mpr c.property)
  rw [hempty, sInf_empty, sInf_singleton, sInf_singleton] at h
  apply hd
  exact top_le_iff.mp (h ▸ sup_le (below _ hb) (below _ hc))

private def selectedFixed {C : Set (Brackets n)} (hC : BooleanFamily C) (b : C) : RowIndex n :=
  (proper_has_fixed fun hb => hC.2.1 (hb ▸ b.property)).choose

private theorem selectedFixed_spec {C : Set (Brackets n)} (hC : BooleanFamily C) (b : C) :
    b.val.val (atIndex (selectedFixed hC b)) = atIndex (selectedFixed hC b) :=
  (proper_has_fixed fun hb => hC.2.1 (hb ▸ b.property)).choose_spec

private theorem selectedFixed_inj {C : Set (Brackets n)} (hC : BooleanFamily C) :
    Function.Injective (selectedFixed hC) := by
  intro b c heq
  exact fixed_unique hC (selectedFixed_spec hC b) (heq ▸ selectedFixed_spec hC c)

private theorem booleanFamily_card_le {C : Set (Brackets n)} (hC : BooleanFamily C) : C.ncard ≤ n := by
  have : Finite (RowIndex n) := Finite.of_equiv _ (rowIndexEquiv n)
  calc
    C.ncard = Nat.card C := (Nat.card_coe_set_eq C).symm
    _ ≤ Nat.card (RowIndex n) := Nat.card_le_card_of_injective _ (selectedFixed_inj hC)
    _ = n := Nat.card_eq_of_equiv_fin (rowIndexEquiv n).symm

private theorem row_of_unique_fixed {b : Brackets n} {s : RowIndex n}
    (hs : b.val (atIndex s) = atIndex s)
    (hu : ∀ t : RowIndex n, b.val (atIndex t) = atIndex t → t = s) :
    ∃ a : LeftEndpoint s, b = row s a := by
  classical
  have existsDeficit : ∃ k : ℕ, ∃ i : Fin (n + 1), i.val = k ∧ b.val i = atIndex s :=
    ⟨(atIndex s).val, atIndex s, rfl, hs⟩
  obtain ⟨i₀, hi₀, hval₀⟩ := Nat.find_spec existsDeficit
  let a : LeftEndpoint s :=
    ⟨i₀.val + 1, by omega, by
      have hlow := b.property.1 i₀
      rw [hval₀] at hlow
      change i₀.val ≤ (atIndex s).val at hlow
      have := atIndex_val s
      omega⟩
  have isDeficit (i : Fin (n + 1)) (hi : b.val i < Fin.last n) :
      b.val i = atIndex s := by
    have hfix : b.val (b.val i) = b.val i :=
      le_antisymm (b.property.2 i _ (b.property.1 i) le_rfl) (b.property.1 _)
    have h := hu (fromCoord (b.val i) hi) (by rwa [atIndex_fromCoord])
    rw [← h, atIndex_fromCoord]
  refine ⟨a, Subtype.ext (funext fun i => Fin.ext ?_)⟩
  have hv := row_value_oneBased s a i
  change (b.val i).val = ((row s a).val i).val
  have ha : a.val = i₀.val + 1 := rfl
  have hsi := atIndex_val s
  split at hv
  · rename_i hm
    have hlo : i₀ ≤ i := Fin.le_def.mpr (by omega)
    have hhi : i ≤ b.val i₀ := by rw [hval₀]; exact Fin.le_def.mpr (by omega)
    have hle := b.property.2 i₀ i hlo hhi
    rw [hval₀] at hle
    have hlt : b.val i < Fin.last n :=
      hle.trans_lt (Fin.castSucc_lt_last _)
    have hd := congrArg Fin.val (isDeficit i hlt)
    omega
  · rename_i hm
    have htop : b.val i = Fin.last n := by
      by_contra h
      have hi := isDeficit i (lt_of_le_of_ne (Fin.le_last _) h)
      have hmin := Nat.find_min' existsDeficit (m := i.val) ⟨i, rfl, hi⟩
      have hb := b.property.1 i
      rw [hi] at hb
      change i.val ≤ (atIndex s).val at hb
      exact hm ⟨by omega, by omega⟩
    rw [htop, Fin.val_last]
    omega

private theorem maximum_boolean_is_rowFamily {C : Set (Brackets n)} (hC : BooleanFamily C)
    (hcard : C.ncard = n) :
    ∃ A : (s : RowIndex n) → LeftEndpoint s, C = Set.range (rowFamily A) := by
  classical
  have : Finite (RowIndex n) := Finite.of_equiv _ (rowIndexEquiv n)
  have hbij := (selectedFixed_inj hC).bijective_of_nat_card_le
    (by rw [Nat.card_eq_of_equiv_fin (rowIndexEquiv n).symm, Nat.card_coe_set_eq, hcard])
  let e : C ≃ RowIndex n := Equiv.ofBijective (selectedFixed hC) hbij
  have hex (s : RowIndex n) : ∃ a : LeftEndpoint s, (e.symm s).val = row s a := by
    have he : selectedFixed hC (e.symm s) = s := e.apply_symm_apply s
    apply row_of_unique_fixed
    · have hf := selectedFixed_spec hC (e.symm s)
      rwa [he] at hf
    · intro t ht
      obtain ⟨c, hc⟩ := hbij.2 t
      have hfix := selectedFixed_spec hC c
      rw [hc] at hfix
      have h := fixed_unique hC ht hfix
      rw [← he, h, hc]
  choose A hA using hex
  refine ⟨A, ?_⟩
  ext b
  constructor
  · intro hb
    refine ⟨e ⟨b, hb⟩, ?_⟩
    rw [rowFamily, ← hA, e.symm_apply_apply]
  · rintro ⟨s, rfl⟩
    rw [rowFamily, ← hA]
    exact (e.symm s).property

private theorem meet_row_witness (A : (s : RowIndex n) → LeftEndpoint s)
    {S : Set (Brackets n)} (hS : S ⊆ Set.range (rowFamily A)) {u : Brackets n}
    (h : sInf S ≤ u) (i : Fin (n + 1)) (hi : (u.val i).val < n) :
    ∃ s : RowIndex n, rowFamily A s ∈ S ∧
      (A s).val ≤ i.val + 1 ∧ i.val + 1 ≤ s.val ∧ s.val ≤ (u.val i).val + 1 := by
  have hui : (sInf S).val i ≤ u.val i := h i
  rcases sInf_coord_eq_or S i with ht | ⟨x, hx, he⟩
  · rw [ht] at hui
    exact False.elim (Nat.not_le_of_gt hi hui)
  · obtain ⟨s, rfl⟩ := hS hx
    rw [he] at hui
    exact ⟨s, hx, row_coord_of_le i hui hi⟩

private theorem laminar_join_meets (A : (s : RowIndex n) → LeftEndpoint s) (hA : Laminar A)
    {S T : Set (Brackets n)} (hS : S ⊆ Set.range (rowFamily A))
    (hT : T ⊆ Set.range (rowFamily A)) :
    sInf S ⊔ sInf T = sInf (S ∩ T) := by
  classical
  apply le_antisymm
  · exact sup_le (sInf_le_sInf Set.inter_subset_left) (sInf_le_sInf Set.inter_subset_right)
  · rw [sup_eq_inf_upper]
    apply le_sInf
    intro u hu
    obtain ⟨huS, huT⟩ := hu
    intro i
    change (sInf (S ∩ T)).val i ≤ u.val i
    by_cases hi : (u.val i).val < n
    · let : Finite (RowIndex n) := Finite.of_equiv _ (rowIndexEquiv n)
      let _ : Fintype (RowIndex n) := Fintype.ofFinite _
      let good (s : RowIndex n) : Prop :=
        (rowFamily A s ∈ S ∪ T) ∧ (A s).val ≤ i.val + 1 ∧ i.val + 1 ≤ s.val ∧
          s.val ≤ (u.val i).val + 1
      let candidates := Finset.univ.filter good
      have mem_candidates (s : RowIndex n) : s ∈ candidates ↔ good s := by simp [candidates]
      obtain ⟨r, hr, hra, hri, hru⟩ := meet_row_witness A hS huS i hi
      obtain ⟨s, hs, hmax⟩ := Finset.exists_max_image candidates Subtype.val
        ⟨r, (mem_candidates r).mpr ⟨Or.inl hr, hra, hri, hru⟩⟩
      obtain ⟨hmem, hsa, hsi, hsu⟩ := (mem_candidates s).mp hs
      have advance {V : Set (Brackets n)} (hV : V ⊆ Set.range (rowFamily A))
          (huV : sInf V ≤ u) (hVU : V ⊆ S ∪ T) (hsV : rowFamily A s ∉ V) : False := by
        have his : i ≤ atIndex s := Fin.le_def.mpr (by have := atIndex_val s; omega)
        have hsu' : atIndex s ≤ u.val i := Fin.le_def.mpr (by have := atIndex_val s; omega)
        have hnest := u.property.2 i (atIndex s) his hsu'
        have hnest' : (u.val (atIndex s)).val ≤ (u.val i).val := hnest
        obtain ⟨t, ht, hta, hts, htu⟩ :=
          meet_row_witness A hV huV (atIndex s) (lt_of_le_of_lt hnest' hi)
        rw [atIndex_val] at hta hts
        have hne : s.val ≠ t.val := fun he => hsV
          (show rowFamily A s ∈ V from (Subtype.ext he : s = t).symm ▸ ht)
        have hlt := lt_of_le_of_ne hts hne
        have hgood : good t :=
          ⟨hVU ht, (hA s t hlt hta).trans hsa, hsi.trans hts, by omega⟩
        exact hlt.not_ge (hmax t ((mem_candidates t).mpr hgood))
      have hsS : rowFamily A s ∈ S := by
        by_contra h
        exact advance hS huS Set.subset_union_left h
      have hsT : rowFamily A s ∈ T := by
        by_contra h
        exact advance hT huT Set.subset_union_right h
      have hrow := row_value_oneBased s (A s) i
      rw [ite_eq_left ⟨hsa, hsi⟩] at hrow
      have hru' : ((row s (A s)).val i).val ≤ (u.val i).val := by omega
      exact (sInf_le (show rowFamily A s ∈ S ∩ T from ⟨hsS, hsT⟩) i).trans
        (Fin.le_def.mpr hru')
    · have hm := Fin.le_last ((sInf (S ∩ T)).val i)
      exact hm.trans (show Fin.last n ≤ u.val i from Nat.le_of_not_gt hi)

private theorem boolean_rows_laminar (A : (s : RowIndex n) → LeftEndpoint s)
    (h : BooleanFamily (Set.range (rowFamily A))) : Laminar A := by
  intro s t hst hta
  by_contra! hsa
  have has := (A s).property.1
  let p : RowIndex n := ⟨(A t).val - 1, by omega, by have := t.property.2; omega⟩
  let c : LeftEndpoint t := ⟨p.val, p.property.1, by change (A t).val - 1 ≤ t.val; omega⟩
  let S : Set (Brackets n) := {rowFamily A s, rowFamily A t}
  let T : Set (Brackets n) := {rowFamily A p, rowFamily A t}
  have hp : p.val + 1 = (A t).val := by change (A t).val - 1 + 1 = _; omega
  have hps : p.val < s.val := by omega
  have hne : rowFamily A s ≠ rowFamily A p := fun he =>
    hps.ne ((congrArg Subtype.val (rowFamily_injective A he)).symm)
  have hSt : rowFamily A t ∈ S := by simp [S]
  have hTt : rowFamily A t ∈ T := by simp [T]
  have hS : S ⊆ Set.range (rowFamily A) := by simp [S, Set.insert_subset_iff]
  have hT : T ⊆ Set.range (rowFamily A) := by simp [T, Set.insert_subset_iff]
  have hEq := h.2.2 S T hS hT
  have hInter : S ∩ T = {rowFamily A t} := by
    ext x
    simp only [S, T, Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hs | hs, ht | ht⟩
      · exact (hne (hs.symm.trans ht)).elim
      · exact ht
      · exact hs
      · exact hs
    · exact fun hx => ⟨Or.inr hx, Or.inr hx⟩
  rw [hInter, sInf_singleton] at hEq
  have below {V : Set (Brackets n)} (ht : rowFamily A t ∈ V) {k : RowIndex n}
      (hk : rowFamily A k ∈ V) (hka : (A k).val ≤ p.val) (hkp : p.val ≤ k.val)
      (hkt : k.val ≤ t.val) : sInf V ≤ row t c := by
    apply row_le_of_coord
    intro i hic hit
    change p.val ≤ i.val + 1 at hic
    by_cases hi : (A t).val ≤ i.val + 1
    · have hl : ((sInf V).val i).val ≤ ((row t (A t)).val i).val := sInf_le ht i
      have hv := row_value_oneBased t (A t) i
      rw [ite_eq_left ⟨hi, hit⟩] at hv
      omega
    · have hip : i.val + 1 = p.val := by omega
      have hl : ((sInf V).val i).val ≤ ((row k (A k)).val i).val := sInf_le hk i
      have hv := row_value_oneBased k (A k) i
      rw [ite_eq_left ⟨hip ▸ hka, hip ▸ hkp⟩] at hv
      omega
  have hle : rowFamily A t ≤ row t c := by
    rw [← hEq]
    exact sup_le
      (below hSt (show rowFamily A s ∈ S by simp [S]) (by omega) hps.le hst.le)
      (below hTt (show rowFamily A p ∈ T by simp [T]) (A p).property.2 le_rfl
        (hps.le.trans hst.le))
  have hc : (A t).val ≤ p.val :=
    ((row_le_row_iff t t (A t) c).mp hle).2
  omega

theorem boolean_rowFamily_iff_laminar (A : (s : RowIndex n) → LeftEndpoint s) :
    BooleanFamily (Set.range (rowFamily A)) ↔ Laminar A := by
  refine ⟨boolean_rows_laminar A, fun hA => ⟨?_, ?_, fun _ _ => laminar_join_meets A hA⟩⟩
  · rintro _ ⟨s, rfl⟩ _ ⟨t, rfl⟩ hne hle
    have he := ((row_le_row_iff s t (A s) (A t)).mp hle).1
    exact hne (congrArg (rowFamily A) he)
  · rintro ⟨s, hs⟩
    have hv := row_value_oneBased s (A s) (atIndex s)
    rw [atIndex_val, ite_eq_left ⟨(A s).property.2, le_rfl⟩] at hv
    change (((rowFamily A s).val (atIndex s)).val + 1) = s.val at hv
    rw [hs, top_coord, Fin.val_last] at hv
    have := s.property.2
    omega

theorem booleanFamily_maximum (n : ℕ) :
    IsGreatest {k : ℕ | ∃ C : Set (Brackets n), BooleanFamily C ∧ C.ncard = k} n := by
  refine ⟨?_, ?_⟩
  · let A (s : RowIndex n) : LeftEndpoint s := ⟨s.val, s.property.1, le_rfl⟩
    exact ⟨Set.range (rowFamily A),
      (boolean_rowFamily_iff_laminar A).2 (fun _ _ hst hi => (hst.not_ge hi).elim),
      rowFamily_ncard A⟩
  · rintro k ⟨C, hC, rfl⟩
    exact booleanFamily_card_le hC

theorem maximum_boolean_iff_laminar_rows (C : Set (Brackets n)) :
    BooleanFamily C ∧ C.ncard = n ↔
      ∃ A : (s : RowIndex n) → LeftEndpoint s, Laminar A ∧ C = Set.range (rowFamily A) := by
  constructor
  · rintro ⟨hC, hc⟩
    obtain ⟨A, rfl⟩ := maximum_boolean_is_rowFamily hC hc
    exact ⟨A, (boolean_rowFamily_iff_laminar A).mp hC, rfl⟩
  · rintro ⟨A, hA, rfl⟩
    exact ⟨(boolean_rowFamily_iff_laminar A).mpr hA, rowFamily_ncard A⟩

end

end D5.S3.Combinatorics.Lattices.Tamari
