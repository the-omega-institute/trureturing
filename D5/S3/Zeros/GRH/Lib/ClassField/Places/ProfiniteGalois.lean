/- GID: D5/S3/Zeros/GRH/Lib/ClassField/Places/ProfiniteGalois
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/ClassField/Places/ProfiniteGalois
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.ClassField.Places.ProfiniteGalois. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/ClassField/Places/ProfiniteGalois.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.ClassField.Places.LocalDefs
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Hilbert ramification theory for infinite Galois extensions; ideles and ideal classes
(known result; see Lib.ClassField.Places.LocalFrobenius).

This file: Infinite Galois theory for an abstract profinite group: fixed fields, restriction,
continuity. -/

open Function MulSemiringAction InfiniteGalois Subgroup Units IntermediateField IsScalarTower Module
  Fact Subtype DFunLike MulAction Topology algebraMap


instance {K : Type*} [Field K] [CharZero K] [Algebra K Ω] : IsAlgClosure K Ω :=
  ⟨inferInstance, .tower_top (K := ℚ) K⟩

/-- A chosen embedding of the number field K into Ω. -/
noncomputable def Ω.fieldEmb K [Field K] [NumberField K] : K →+* Ω := Classical.ofNonempty

variable {Γ K Ω : Type*} [Group Γ] [TopologicalSpace Γ] [Field K] [Field Ω] [Algebra K Ω]

section

variable (H U : Subgroup Γ) [h : @IsClosed Γ _ H] [Fact (@IsOpen Γ _ U)]

instance (U : OpenSubgroup Γ) : Fact (@IsOpen Γ _ U.1) := ⟨U.2⟩

instance [IsGalois K Ω] : IsProGalois Gal(Ω/K) K Ω := ⟨stabilizer_isOpen_of_isIntegral⟩

instance [ContinuousMul Γ] : @IsClosed Γ _ U := U.isClosed_of_isOpen out

instance [CompactSpace Γ] : CompactSpace H := h.isCompact.compactSpace

end

variable [MulSemiringAction Γ Ω] [G : IsProGalois Γ K Ω] (H U : Subgroup Γ) [h : @IsClosed Γ _ H]
  [Fact (@IsOpen Γ _ U)]

/-- A closed subgroup is the Galois group over its fixed field. -/
instance : @IsProGalois H (fixedFieldOf H) Ω _ _ _ inferInstance _ _ := ⟨(G.6 · |>.preimage_val)⟩

include G

lemma isLocallyConstant_smul x : IsLocallyConstant (· • x : Γ → Ω) :=
  @.of_discrete _ _ _ (QuotientGroup.discreteTopology (G.6 x)) (ofQuotientStabilizer Γ x)

/-- For x in Ω and any property P, the set of g in Γ such that gx has P is closed. -/
lemma isClosed_setOf_smul x (P : Ω → _) : IsClosed {g : Γ | P (g • x)} :=
  ⟨isLocallyConstant_smul x Pᶜ⟩

variable {Γ' L Ω'} [Group Γ'] [TopologicalSpace Γ'] [Field L] [Field Ω'] [Algebra L Ω']
  [MulSemiringAction Γ' Ω'] (j : Ω →+* Ω')

/-- Let Γ = Gal(Ω/K), Γ' = Gal(Ω'/L) and j : Ω → Ω' be a field embedding. Every map φ : Γ' → Γ
with j(φ(g)x) = g·j(x) for all g, x is continuous. -/
lemma continuous_of_equivariant_emb [IsProGalois Γ' L Ω'] {φ : Γ' → Γ} (e : ∀ g x, j (φ g • x) =
  g • j x := by tauto) : Continuous φ := let : UniformSpace Ω := ⊥
  ((continuous_pi (isLocallyConstant_smul · |>.continuous)).isClosedEmbedding
    fun _ _ ↦ G.faithful.1 ∘ congrFun).continuous_iff.2 (continuous_pi fun x ↦
    ((funext (e · x) ▸ isLocallyConstant_smul _).desc _ j j.injective).continuous)

variable (Γ Γ')

lemma toAlgAut_surjective : Surjective (toAlgAut Γ K Ω) := forall_imp (fixingSubgroup_fixedField
  ⟨MonoidHom.range _, (isCompact_range (continuous_of_equivariant_emb 1)).isClosed⟩).le
  (by aesop (add 1% forward (G.1.3.1)))

lemma DiscreteUnits.ofBase_bijective : Bijective (ofBase Γ Ω (K := K)) :=
  ⟨coind_injective _ (map_injective (by aesop_cat)), fun x ↦ (G.1.3.1 _ (congr($(x.2 ·).1))).rec
  (⟨mk0 · (by grind [ne_zero]), val_injective <| ext ·⟩)⟩

/-- Two embeddings j, j' of Ω in a field Ω' that agree on K differ by an element of Γ =
Gal(Ω/K): j'(x) = j(gx) for some g and all x. -/
lemma exists_smul_emb_eq j' (h : j.comp (algebraMap K Ω) = .comp j' (algebraMap ..)) :
    ∃ g : Γ, ∀ x, j (g • x) = j' x := by
  algebraize [j, j.comp (algebraMap K Ω)]
  simpa [ext_iff] using! (Normal.algHomEquivAut ..).symm.surjective.comp (toAlgAut_surjective Γ)
    ⟨_, ext_iff.1 h.symm⟩

/-- Let Γ = Gal(Ω/K), Γ' = Gal(Ω'/L), and j : Ω → Ω' a ring homomorphism such that Γ' fixes j(K)
pointwise. Then there is a continuous homomorphism φ : Γ' → Γ with j(φ(g)x) = g·j(x) for all g,
x. -/
lemma exists_galois_restrict [IsProGalois Γ' L Ω'] (h : ∀ (g : Γ') (x : K), g • j x =
  j x := by aesop) : ∃ φ : Γ' →ₜ* Γ, ∀ g x, j (φ g • x) = g • j x := by
  choose f h using fun g ↦ exists_smul_emb_eq Γ j (.comp (toRingHom ..) j) (RingHom.ext (h g)).symm
  use ⟨.mk' f fun _ _ ↦ G.faithful.1 (by simp [← j.injective.eq_iff, h, mul_smul]),
    continuous_of_equivariant_emb j h⟩, h

variable {Γ Γ'} [Algebra K L] [Algebra L Ω] [MulSemiringAction Γ' Ω] [IsScalarTower K L Ω]
  [J : IsProGalois Γ' L Ω] (φ : Γ' →* Γ)

/-- For K ⊂ L ⊂ Ω with Galois groups Γ and Γ', a homomorphism φ : Γ' → Γ compatible with the
actions on Ω is a closed embedding onto the subgroup fixing L, of index [L:K] (both 0 if
infinite). -/
lemma isClosedEmbedding_galois_restrict (e : ∀ g (x : Ω), φ g • x = g • x := by tauto) :
  IsClosedEmbedding φ ∧ φ.range = fixingSubgroup Γ (.range (algebraMap L Ω)) ∧ φ.range.index =
  finrank K L := by refine ⟨(continuous_of_equivariant_emb 1 e).isClosedEmbedding fun _ _ _ ↦
  J.faithful.1 (by simp_all [← e]),
  (and_iff_left_of_imp (by rw [·, (toAlgHom K L Ω).equivFieldRange.toLinearEquiv.finrank_eq,
  finrank_eq_fixingSubgroup_index, ← index_comap_of_surjective _ (toAlgAut_surjective Γ)]; rfl)).2
  (le_antisymm ?_ fun g _ ↦ (exists_smul_emb_eq _ 1 (toRingHom _ Ω g) ?_).imp fun _ _ ↦
  G.faithful.1 ?_)⟩ <;> simp_all [LE.le, mem_fixingSubgroup_iff, ext_iff]

/-- For K ⊂ L ⊂ Ω with L/K finite and Galois groups Γ and Γ', a homomorphism Γ' → Γ compatible
with the actions on Ω is an open embedding. -/
lemma isOpenEmbedding_galois_restrict (e : ∀ g (x : Ω), φ g • x = g • x) [Module.Finite K L] :
    IsOpenEmbedding φ := (isClosedEmbedding_galois_restrict φ e).rec fun ⟨a, b⟩ c ↦
  ⟨a, @isOpen_of_isClosed_of_finiteIndex _ _ _ _ _ ⟨c.2 ▸ finrank_pos.ne'⟩ b⟩

lemma fixedFieldOf_fixingSubgroup L : fixedFieldOf (fixingSubgroup Γ (SetLike.coe L)) = L :=
  .trans (by
  ext; simp [(toAlgAut_surjective Γ).forall, mem_fixingSubgroup_iff]) (fixedField_fixingSubgroup L)

/-- Let Γ = Gal(Ω/K) and K ⊆ L ⊆ Ω. A subgroup V of Γ that acts as the Galois group of Ω/L is
the subgroup fixing L pointwise, and its index is [L : K] (both read as 0 if infinite). -/
lemma eq_fixingSubgroup_of_isProGalois {V : Subgroup Γ} [J : IsProGalois V L Ω] : V =
  fixingSubgroup Γ (.range (algebraMap L Ω))
  ∧ V.index = finrank K L := V.range_subtype ▸ (isClosedEmbedding_galois_restrict _).2

/-- Galois correspondence: a closed subgroup H of the Galois group Γ of Ω/K is the subgroup
fixing the fixed field of H. -/
lemma fixingSubgroup_fixedFieldOf : fixingSubgroup Γ (SetLike.coe (fixedFieldOf H)) = H :=
  (fixedFieldOf H).fieldRange_val ▸ eq_fixingSubgroup_of_isProGalois.1.symm

lemma finrank_fixedFieldOf : finrank K (fixedFieldOf H) = H.index :=
  eq_fixingSubgroup_of_isProGalois.2.symm

instance finiteDimensional_fixedFieldOf : FiniteDimensional K (fixedFieldOf U) :=
  .of_finrank_pos (finrank_fixedFieldOf U ▸ (U.quotient_finite_of_isOpen out).card_pos)

instance [NumberField K] : NumberField (fixedFieldOf U) := .of_module_finite K _
