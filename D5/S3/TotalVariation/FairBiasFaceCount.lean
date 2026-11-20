/- GID: D5/S3/TotalVariation/FairBiasFaceCount
   generality: G
   mirror-B: D5/B/S3/TotalVariation/FairBiasFaceCount
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Complement-spanning supports determine the face counts of the fair-bias link. -/

import D5.S3.TotalVariation.FairBiasLink

/-! Face counts and an Euler characteristic formula for the signed fair-bias complex. -/

set_option autoImplicit false

open scoped BigOperators

namespace D5.S3.TotalVariation.FairBiasFaceCount

open D5.S3.TotalVariation.FairBiasLink

universe u v

variable {A : Type u} {L : Type v} [AddCommGroup A] [Fintype L] [DecidableEq L]

private def spansComplement (c : L → A) (S : Finset L) : Prop :=
  AddSubgroup.closure (c '' {i | i ∉ S}) = AddSubgroup.closure (Set.range c)

private abbrev Faces (c : L → A) (k : ℕ) :=
  {S : Finset (L × Bool) // S ∈ signedComplex c ∧ S.card = k}

private abbrev Supports (c : L → A) (k : ℕ) :=
  {S : Finset L // spansComplement c S ∧ S.card = k}

private theorem mem_image_fst (S : Finset (L × Bool)) (i : L) :
    i ∈ S.image Prod.fst ↔ ∃ b : Bool, (i, b) ∈ S := by
  constructor
  · intro h
    obtain ⟨⟨j, b⟩, hmem, he⟩ := Finset.mem_image.mp h
    change j = i at he
    subst j
    exact ⟨b, hmem⟩
  · rintro ⟨b, hb⟩
    exact Finset.mem_image.mpr ⟨(i, b), hb, rfl⟩

private theorem fst_injOn {S : Finset (L × Bool)}
    (hS : ∀ i, (i, true) ∈ S → (i, false) ∉ S) : Set.InjOn Prod.fst (S : Set (L × Bool)) := by
  rintro ⟨i, b⟩ hi ⟨j, d⟩ hj he
  change i = j at he
  subst j
  cases b <;> cases d
  · rfl
  · exact (hS i hj hi).elim
  · exact (hS i hi hj).elim
  · rfl

private noncomputable def supportOf (c : L → A) (k : ℕ) (S : Faces c k) : Supports c k := by
  have hSign : ∀ i, (i, true) ∈ S.val → (i, false) ∉ S.val := S.property.1.2.1
  have hSpan : spansComplement c (S.val.image Prod.fst) := by
    have he : {i : L | i ∉ S.val.image Prod.fst} = {i | ∀ b : Bool, (i, b) ∉ S.val} := by
      ext i
      simp [mem_image_fst]
    unfold spansComplement
    rw [he]
    exact S.property.1.2.2
  exact ⟨S.val.image Prod.fst, hSpan, (Finset.card_image_of_injOn (fst_injOn hSign)).trans S.property.2⟩

private def assignSigns (S : Finset L) (e : S → Bool) : Finset (L × Bool) :=
  S.attach.map ⟨fun i => (i.val, e i), fun _ _ he => Subtype.ext (congrArg Prod.fst he)⟩

private theorem mem_assignSigns (S : Finset L) (e : S → Bool) (i : L) (b : Bool) :
    (i, b) ∈ assignSigns S e ↔ ∃ hi : i ∈ S, e ⟨i, hi⟩ = b := by
  simp only [assignSigns, Finset.mem_map, Finset.mem_attach, true_and, Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨⟨j, hj⟩, he⟩
    have h : j = i := congrArg Prod.fst he
    subst j
    exact ⟨hj, congrArg Prod.snd he⟩
  · rintro ⟨hi, rfl⟩
    exact ⟨⟨i, hi⟩, rfl⟩

private theorem assignSigns_card (S : Finset L) (e : S → Bool) :
    (assignSigns S e).card = S.card := by simp [assignSigns]

private noncomputable def faceOf (c : L → A) (k : ℕ) (hk : 0 < k)
    (S : Supports c k) (e : S.val → Bool) : Faces c k := by
  have hcard := (assignSigns_card S.val e).trans S.property.2
  refine ⟨assignSigns S.val e, ⟨Finset.card_pos.mp (by rwa [hcard]), ?_, ?_⟩, hcard⟩
  · intro i hb hd
    obtain ⟨hi, ht⟩ := (mem_assignSigns S.val e i true).mp hb
    obtain ⟨_, hf⟩ := (mem_assignSigns S.val e i false).mp hd
    have h := ht.symm.trans hf
    contradiction
  · have he : {i : L | ∀ b : Bool, (i, b) ∉ assignSigns S.val e} = {i | i ∉ S.val} := by
      ext i
      constructor
      · intro h hi
        exact h (e ⟨i, hi⟩) ((mem_assignSigns S.val e i _).mpr ⟨hi, rfl⟩)
      · intro h b hb
        exact h ((mem_assignSigns S.val e i b).mp hb).choose
    change AddSubgroup.closure (c '' {i | ∀ b : Bool, (i, b) ∉ assignSigns S.val e}) = _
    rw [he]
    exact S.property.1

private theorem support_faceOf (c : L → A) (k : ℕ) (hk : 0 < k)
    (S : Supports c k) (e : S.val → Bool) :
    supportOf c k (faceOf c k hk S e) = S := by
  apply Subtype.ext
  ext i
  change i ∈ (assignSigns S.val e).image Prod.fst ↔ i ∈ S.val
  rw [mem_image_fst]
  constructor
  · rintro ⟨b, hb⟩
    exact ((mem_assignSigns S.val e i b).mp hb).choose
  · intro hi
    exact ⟨e ⟨i, hi⟩, (mem_assignSigns S.val e i _).mpr ⟨hi, rfl⟩⟩

private theorem faceOf_injective (c : L → A) (k : ℕ) (hk : 0 < k) :
    Function.Injective (fun p : Σ S : Supports c k, S.val → Bool => faceOf c k hk p.1 p.2) := by
  rintro ⟨S, e⟩ ⟨T, f⟩ he
  have hST := congrArg (supportOf c k) he
  rw [support_faceOf, support_faceOf] at hST
  cases hST
  have hef : e = f := by
    funext i
    have hmem : (i.val, e i) ∈ (faceOf c k hk S e).val :=
      (mem_assignSigns S.val e i.val _).mpr ⟨i.property, rfl⟩
    change faceOf c k hk S e = faceOf c k hk S f at he
    rw [he] at hmem
    exact ((mem_assignSigns S.val f i.val _).mp hmem).choose_spec.symm
  cases hef
  rfl

private theorem faceOf_surjective (c : L → A) (k : ℕ) (hk : 0 < k) :
    Function.Surjective (fun p : Σ S : Supports c k, S.val → Bool => faceOf c k hk p.1 p.2) := by
  classical
  intro F
  let S := supportOf c k F
  have h (i : S.val) : ∃ b : Bool, (i.val, b) ∈ F.val :=
    (mem_image_fst F.val i.val).mp i.property
  let e (i : S.val) := (h i).choose
  refine ⟨⟨S, e⟩, Subtype.ext ?_⟩
  apply Finset.eq_of_subset_of_card_le
  · rintro ⟨i, b⟩ hb
    obtain ⟨hi, he⟩ := (mem_assignSigns S.val e i b).mp hb
    rw [← he]
    exact (h ⟨i, hi⟩).choose_spec
  · exact F.property.2.le.trans (faceOf c k hk S e).property.2.ge

/-- Each eligible k-label support gives exactly two to the k signed faces. -/
theorem card_signed_faces (c : L → A) (k : ℕ) (hk : 0 < k) :
    Nat.card {S : Finset (L × Bool) // S ∈ signedComplex c ∧ S.card = k} =
      2 ^ k * Nat.card {S : Finset L //
        AddSubgroup.closure (c '' {i | i ∉ S}) = AddSubgroup.closure (Set.range c) ∧ S.card = k} := by
  classical
  let S := Supports c k
  let _ : Fintype S := Fintype.ofFinite _
  let _ : Fintype (Faces c k) := Fintype.ofFinite _
  let eqv : (Σ s : S, s.val → Bool) ≃ Faces c k :=
    Equiv.ofBijective _ ⟨faceOf_injective c k hk, faceOf_surjective c k hk⟩
  change Nat.card (Faces c k) = 2 ^ k * Nat.card S
  have hf (s : S) : Fintype.card (s.val → Bool) = 2 ^ k := by
    rw [← Nat.card_eq_fintype_card, Nat.card_fun,
      Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool, Nat.card_eq_fintype_card,
      Fintype.card_coe, s.property.2]
  rw [← Nat.card_congr eqv, Nat.card_eq_fintype_card, Fintype.card_sigma]
  simp only [hf, Finset.sum_const, Finset.card_univ, Nat.nsmul_eq_mul, Nat.card_eq_fintype_card,
    mul_comm]

/-- Reduced Euler characteristic, with contribution minus one from the empty face. -/
noncomputable def reducedEuler (c : L → A) : ℚ := by
  classical
  exact -1 - ∑ S : Finset (L × Bool) with S ∈ signedComplex c, (-1 : ℚ) ^ S.card

private theorem sum_by_card {V : Type*} [Fintype V]
    (p : Finset V → Prop) [DecidablePred p] (n : ℕ) (z : ℚ)
    (h : ∀ S, p S → S.card ≤ n) :
    (∑ S : Finset V with p S, z ^ S.card) =
      ∑ k ∈ Finset.range (n + 1), z ^ k * (Nat.card {S : Finset V // p S ∧ S.card = k} : ℚ) := by
  classical
  let F := (Finset.univ : Finset (Finset V)).filter p
  have hmap (S : Finset V) (hS : S ∈ F) : S.card ∈ Finset.range (n + 1) :=
    Finset.mem_range.mpr (Nat.lt_succ_of_le (h S (Finset.mem_filter.mp hS).2))
  rw [← Finset.sum_fiberwise_of_maps_to hmap]
  apply Finset.sum_congr rfl
  intro k _
  let _ : Fintype {S : Finset V // p S ∧ S.card = k} := Fintype.ofFinite _
  have hc : Nat.card {S : Finset V // p S ∧ S.card = k} = (F.filter (·.card = k)).card := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_of_subtype _ (by intro S; simp [F])
  rw [hc]
  calc
    _ = ∑ _ ∈ F.filter (·.card = k), z ^ k := by
      exact Finset.sum_congr rfl (fun S hS => congrArg (z ^ ·) (Finset.mem_filter.mp hS).2)
    _ = _ := by simp [nsmul_eq_mul, mul_comm]

open Classical in
private theorem euler_eq_support_sum (c : L → A) :
    reducedEuler c = -∑ S : Finset L with spansComplement c S, (-2 : ℚ) ^ S.card := by
  classical
  let n := Fintype.card L
  have hf (S : Finset (L × Bool)) (hS : S ∈ signedComplex c) : S.card ≤ n := by
    have he := Finset.card_image_of_injOn (fst_injOn hS.2.1)
    simpa only [he] using Finset.card_le_univ (S.image Prod.fst)
  have hzeroF : Nat.card (Faces c 0) = 0 := by
    let _ : IsEmpty (Faces c 0) :=
      ⟨fun x => (Finset.card_pos.mpr x.property.1.1).ne' x.property.2⟩
    exact Nat.card_of_isEmpty
  have hzeroU : Nat.card (Supports c 0) = 1 := by
    have hempty : spansComplement c (∅ : Finset L) := by
      simp [spansComplement, Set.image_univ]
    let _ : Unique (Supports c 0) :=
      ⟨⟨⟨∅, hempty, rfl⟩⟩, fun S => Subtype.ext (Finset.card_eq_zero.mp S.property.2)⟩
    exact Nat.card_unique
  have he (k : ℕ) : (-1 : ℚ) ^ (k + 1) * (Nat.card (Faces c (k + 1)) : ℚ) =
      (-2 : ℚ) ^ (k + 1) * (Nat.card (Supports c (k + 1)) : ℚ) := by
    have h := card_signed_faces c (k + 1) (Nat.zero_lt_succ _)
    change Nat.card (Faces c (k + 1)) = 2 ^ (k + 1) * Nat.card (Supports c (k + 1)) at h
    rw [h, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, ← mul_assoc, ← mul_pow]
    norm_num
  unfold reducedEuler
  rw [sum_by_card (· ∈ signedComplex c) n (-1) hf,
    sum_by_card (spansComplement c) n (-2) (fun S _ => Finset.card_le_univ S)]
  change -1 - (∑ k ∈ Finset.range (n + 1), (-1 : ℚ) ^ k * (Nat.card (Faces c k) : ℚ)) =
    -(∑ k ∈ Finset.range (n + 1), (-2 : ℚ) ^ k * (Nat.card (Supports c k) : ℚ))
  simp only [Finset.sum_range_succ', hzeroF, hzeroU, Nat.cast_zero, Nat.cast_one,
    pow_zero, mul_zero, one_mul, add_zero, he]
  ring

section Rank
variable [Finite A] [Module (ZMod 2) A]

private def columnSpan (c : L → A) (S : Finset L) : Submodule (ZMod 2) A :=
  Submodule.span (ZMod 2) (c '' (S : Set L))

/-- Rank-subset evaluation of the Tutte polynomial of the labelled binary columns. -/
noncomputable def columnTutte (c : L → A) (x y : ℚ) : ℚ :=
  let h := Module.finrank (ZMod 2) (columnSpan c Finset.univ)
  ∑ S : Finset L,
    let r := Module.finrank (ZMod 2) (columnSpan c S)
    (x - 1) ^ (h - r) * (y - 1) ^ (S.card - r)

private theorem span_as_closure (s : Set A) :
    (Submodule.span (ZMod 2) s).toAddSubgroup = AddSubgroup.closure s := by
  apply le_antisymm
  · change Submodule.span (ZMod 2) s ≤ AddSubgroup.toZModSubmodule 2 (AddSubgroup.closure s)
    exact Submodule.span_le.mpr AddSubgroup.subset_closure
  · exact (AddSubgroup.closure_le _).mpr Submodule.subset_span

private theorem rank_eq_iff_spans (c : L → A) (S : Finset L) :
    Module.finrank (ZMod 2) (columnSpan c S) =
      Module.finrank (ZMod 2) (columnSpan c Finset.univ) ↔ spansComplement c Sᶜ := by
  have hle : columnSpan c S ≤ columnSpan c Finset.univ :=
    Submodule.span_mono (Set.image_mono (by simp))
  have he : columnSpan c S = columnSpan c Finset.univ ↔ spansComplement c Sᶜ := by
    rw [← (AddSubgroup.toZModSubmodule 2).symm.injective.eq_iff]
    change (columnSpan c S).toAddSubgroup = (columnSpan c Finset.univ).toAddSubgroup ↔ _
    simp [columnSpan, span_as_closure, spansComplement, Set.image_univ]
  exact ⟨fun h => he.mp (Submodule.eq_of_le_of_finrank_eq hle h),
    fun h => congrArg (fun V : Submodule (ZMod 2) A => Module.finrank (ZMod 2) V) (he.mpr h)⟩

/-- The reduced Euler characteristic is the rank-subset Tutte evaluation at one and one half,
with the sign and power determined by the nullity of the whole family. -/
theorem reducedEuler_eq_tutte (c : L → A) :
    let h := Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range c))
    reducedEuler c =
      -(-2 : ℚ) ^ (Fintype.card L - h) * columnTutte c 1 (1 / 2) := by
  classical
  let h := Module.finrank (ZMod 2) (columnSpan c Finset.univ)
  let n := Fintype.card L
  have hrange : columnSpan c Finset.univ = Submodule.span (ZMod 2) (Set.range c) := by
    simp [columnSpan, Set.image_univ]
  change reducedEuler c = -(-2 : ℚ) ^ (n - Module.finrank (ZMod 2)
    (Submodule.span (ZMod 2) (Set.range c))) * columnTutte c 1 (1 / 2)
  rw [← hrange, euler_eq_support_sum, neg_mul]
  congr 1
  let e : Finset L ≃ Finset L :=
    ⟨Compl.compl, Compl.compl, compl_compl, compl_compl⟩
  calc
    _ = ∑ B : Finset L with spansComplement c Bᶜ, (-2 : ℚ) ^ (n - B.card) := by
      apply Finset.sum_equiv e
      · intro S
        simp [e]
      · intro S _
        change (-2 : ℚ) ^ S.card = (-2 : ℚ) ^ (n - Sᶜ.card)
        rw [Finset.card_compl]
        congr 1
        have := Finset.card_le_univ S
        omega
    _ = ∑ B : Finset L, (-2 : ℚ) ^ (n - h) *
        ((1 - 1) ^ (h - Module.finrank (ZMod 2) (columnSpan c B)) *
          (1 / 2 - 1) ^ (B.card - Module.finrank (ZMod 2) (columnSpan c B))) := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro B _
      let r := Module.finrank (ZMod 2) (columnSpan c B)
      have hr : r ≤ h := Submodule.finrank_mono (Submodule.span_mono (Set.image_mono (by simp)))
      by_cases hB : spansComplement c Bᶜ
      · have he : r = h := (rank_eq_iff_spans c B).mpr hB
        rw [ite_eq_left hB]
        change (-2 : ℚ) ^ (n - B.card) =
          (-2 : ℚ) ^ (n - h) * ((1 - 1) ^ (h - r) * (1 / 2 - 1) ^ (B.card - r))
        rw [he, Nat.sub_self, pow_zero, one_mul]
        have hcard : h ≤ B.card := by
          let f : B → A := fun i => c i.val
          have hf : Set.range f = c '' (B : Set L) := by
            ext a
            constructor
            · rintro ⟨i, rfl⟩
              exact ⟨i.val, i.property, rfl⟩
            · rintro ⟨i, hi, rfl⟩
              exact ⟨⟨i, hi⟩, rfl⟩
          have hh := finrank_range_le_card (R := ZMod 2) f
          rw [hf, Fintype.card_coe] at hh
          exact he ▸ hh
        have hle := Finset.card_le_univ B
        have hexp : n - B.card = n - h - (B.card - h) := by omega
        rw [hexp, pow_sub₀ _ (by norm_num) (show B.card - h ≤ n - h by omega), ← inv_pow]
        norm_num
      · have hn : r ≠ h := fun he => hB ((rank_eq_iff_spans c B).mp he)
        rw [ite_eq_right hB]
        change 0 = (-2 : ℚ) ^ (n - h) * ((1 - 1) ^ (h - r) * (1 / 2 - 1) ^ (B.card - r))
        simp [zero_pow (show h - r ≠ 0 by omega)]
    _ = _ := by simp only [columnTutte, Finset.mul_sum, h]

end Rank

end D5.S3.TotalVariation.FairBiasFaceCount
