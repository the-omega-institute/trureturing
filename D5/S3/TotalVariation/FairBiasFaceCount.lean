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
  refine ⟨assignSigns S.val e, ⟨Finset.card_pos.mp (hcard ▸ hk), ?_, ?_⟩, hcard⟩
  · intro i hb hd
    obtain ⟨hi, ht⟩ := (mem_assignSigns S.val e i true).mp hb
    obtain ⟨_, hf⟩ := (mem_assignSigns S.val e i false).mp hd
    exact Bool.true_ne_false (ht.symm.trans hf)
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

end D5.S3.TotalVariation.FairBiasFaceCount
