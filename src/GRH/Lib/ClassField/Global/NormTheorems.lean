import GRH.Lib.ClassField.Global.ArtinReciprocity
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Global class field theory: Albert–Brauer–Hasse–Noether, reciprocity, existence, norms
(known result; see Lib.ClassField.Global.AlbertBrauerHasseNoether).

This file: Surjectivity of Artin map, cyclic norm group, Hasse norm theorem for totally positive
elements. -/


open Subgroup QZChar QuotientGroup Set Module Function IsScalarTower Algebra
variable (Γ : Type) {K L : Type} [Group Γ] [TopologicalSpace Γ] [Field K] [EmbeddedNumberField K]
  [MulSemiringAction Γ Ω] [IsProGalois Γ K Ω] (χ :
  QZChar Γ) [Field L] [EmbeddedNumberField L] [Algebra K L]

/-- The global Artin map from the finite ideles of the number field K to the abelianisation of
its absolute Galois group Γ is surjective. -/
lemma artinMap_surjective : Surjective (artinMap Γ) :=
  Quot.ind (let H := idelesUnitOff ∅ ⊔ (artinMap Γ).ker
  have := finiteIndex_idele_subgroup_of_isOpen H (isOpen_mono le_sup_left (isOpen_idelesUnitOff _))
    fun _ ↦ mem_sup_right ∘ artinMap_principalIdele
  mem_of_forall_abelianLift (H :=
    (artinMap Γ).range) (image_univ.subst (by simpa [H, univ_eq_iUnion_smul H,
    image_iUnion, image_smul_distrib, ← coe_map, Subgroup.map_sup] using! (isCompact_iUnion fun _ ↦
    (isCompact_idelesUnitOff_empty.image_auto _).smul _).isClosed)) ⟦·⟧ fun ψ e ↦ let U := ker ψ
    (U.index_eq_one.1 (by
      rcases (@hasPrimeDensity_const K _ _ U.index).re_le_re (hasPrimeDensity_card_degree_one
        (fixedFieldOf U) 1), (have O := FinPlace.isPlaceOver_placeOver ·
        have D := (O.artinAt_trivial_iff_decompGroup_le ψ).1 (by simp [e, ← artinMap_locIdele])
        And.intro (O.split_completely D) (relIndex_eq_one.2 D ▸ O.ncard_above_mul_relIndex U))
      simp_all [U, ← finrank_fixedFieldOf, and_iff_left_of_imp, finrank_pos.ne',
        le_iff_lt_or_eq])).ge ⟨⟩)

variable {Γ} [IsScalarTower K L Ω] [J : IsProGalois (ker χ) L Ω] [IsGalois K L]

/-- Let L/K be a cyclic extension of number fields inside an algebraic closure Ω of ℚ. There is
a continuous character χ : Gal(Ω/K) → ℚ/ℤ whose kernel acts on Ω as the Galois group of Ω/L. -/
lemma exists_char_of_isCyclic (c : IsCyclic Gal(L/K)) : ∃ χ : QZChar Gal(Ω/K), IsProGalois (ker χ) L
  Ω := (exists_galois_restrict _ _ (algebraMap L Ω) (by simp [← algebraMap_apply])).elim fun φ h ↦
  (exists_ker_eq_of_isCyclic ⟨⊥, by simp⟩ (quotientBot.isCyclic.2 c)).imp' (comap φ) fun _ e ↦
  .of_fixingSubgroup_eq (by ext; simpa [-AlgEquiv.smul_def, ← h, AlgEquiv.ext_iff,
  mem_fixingSubgroup_iff] using! congr(_ ∈ $e).symm)

omit [EmbeddedNumberField K] [EmbeddedNumberField L] in variable [NumberField K] [NumberField L] in
/-- Hasse's norm theorem. Let `L / K` be a cyclic extension of number fields. A totally positive
`x` in `K` that is a local norm (a limit of norms from `L`) at every finite place is a norm. -/
lemma hasse_norm [IsCyclic Gal(L/K)] (x : Kˣ) (H : ∀ v : FinPlace K,
  algebraMap K _ x ∈ closure (range fun y : L ↦ algebraMap K (LocField v) (norm K y))) (h :
  IsTotallyPositive x.1) : ∃ z : Lˣ, z.map (norm K) = x := by
  algebraize [Ω.fieldEmb L, (Ω.fieldEmb L).comp (algebraMap K L)]
  cases exists_char_of_isCyclic ‹_›
  exact (cyclicClass_eq_zero_iff_norm (J :=
    ‹_›) x).1 (h.exists_resH2_cyclicClass_eq_zero.choose_spec.elim (albert_brauer_hasse_noether _
    (·.abelianLift_artinAt_eq_one_iff.1 (abelianLift_artinAt_of_mem_closure (H _))) _))

omit [IsGalois K L] in
lemma index_ker_char_artinMap : ((abelianLift χ).comp (artinMap Γ)).ker.index = finrank K L :=
  eq_fixingSubgroup_of_isProGalois (J := J).2 ▸ ((abelianLift χ).ker.index_comap_of_surjective
  (artinMap_surjective _)).trans (index_comap_of_surjective _ (mk'_surjective _)).symm

/-- Let L/K be the extension cut out by the character χ. A finite idele a has χ(Art a) trivial
exactly when a is a totally positive element of K^× times the norm of a finite idele of L. -/
lemma char_artinMap_eq_one_iff a : abelianLift χ (artinMap Γ a) = 1 ↔ ∃ x y, IsTotallyPositive x.1 ∧
  a = principalIdele x * .map (adeleNorm K L) y := (second_inequality L (isOpen_of_mem_nhds ((⨅ φ :
  K →+* ℝ, (Units.posSubgroup ℝ).comap (Units.map φ)).map principalIdele ⊔ _)
  ((eventually_artinAt_eq_one χ).mono fun a ⟨m, t⟩ ↦ mem_sup_right (map_le_range _ _
  (mem_of_locIdele_mem (isCompact_idelesUnitOff_empty.image_auto _).isClosed
  ((FinPlace.comap_surjective _).forall.2
  ((exists_localNorm_of_abelianLift_artinAt (t _)).imp' _ fun y e ↦ ⟨locIdele_mem_idelesUnitOff
  (by simpa [mem_idelesUnitOff.1 m, ideleAt, le_antisymm_iff] using congr(‖$e.1‖ = 1)), e ▸
  adeleNorm_locIdele · y⟩)))))) (mem_sup_left ⟨·, mem_iInf.2 ·, rfl⟩) (mem_sup_right ⟨·, rfl⟩)).rec
  fun _ k ↦ by simpa [mem_sup, eq_comm] using! (congr(a ∈ $(eq_of_le_of_not_lt
  (by simpa [LE.le] using (by simp [artinMap_principalIdele (x := ·) ·]))
  (((index_ker_char_artinMap ..).trans_ge k.1).not_gt <| index_strictAnti ·))))
