/- GID: D5/S3/Zeros/GRH/Lib/Shimura/Uniformisation/PeriodLattice
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/Shimura/Uniformisation/PeriodLattice
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.Shimura.Uniformisation.PeriodLattice. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/Shimura/Uniformisation/PeriodLattice.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.Shimura.Uniformisation.ModuliPoint
import D5.S3.Zeros.GRH.Lib.Adelic.Adeles.MatrixApprox
import D5.S3.Zeros.GRH.Lib.Adelic.Unitary.SpaceBasic
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Complex uniformisation of PEL abelian varieties; Appell–Humbert; finite class number
(known result; see Lib.Shimura.Uniformisation.AppellHumbert).

This file: Adelic frames give full lattices in (E⊗R)^n; density and compatibility lemmas. -/

open NumberField Matrix Function Submodule Set


section

variable {E n : Type} [Field E] [NumberField E] [Fintype n] {g g' : GL n (𝔸f E)} {V : Type}
  {S : AddSubgroup (AdelicTorsion E n)} {A : Matrix n n E} {y : n → E} [FinComplexSpace V]
  {Q : RealVectors E n ≃L[ℝ] V}
attribute [local simp] frameTorsionClass frameCoords LinearMap.compLeft comp_def RingHom.map_mulVec

lemma ker_frameTorsionClass_one : (frameTorsionClass (1 : GL n (𝔸f E))).ker =
  .pi ⊤ 1 := by simp [SetLike.ext_iff, @IsIntegralClosure.isIntegral_iff (𝓞 E)]

lemma denseRange_frameCoords : DenseRange (frameCoords g) := (MulAction.surjective
  g⁻¹).denseRange.comp (.piMap (const _ denseRange_algebraMap_finAdele)) (by fun_prop)

lemma frameTorsionClass_surjective : Surjective (frameTorsionClass g) :=
  (denseRange_frameCoords.exists_mem_open (isOpen_preimage_torsionClass {_}) <| Quot.exists_rep ·)

end

attribute [local simp] frameTorsionClass frameCoords LinearMap.compLeft comp_def RingHom.map_mulVec

variable {E n : Type} [Field E] [CMType E] [Fintype n] {g g' : GL n (𝔸f E)} {V : Type}
  {S : AddSubgroup (AdelicTorsion E n)} {A : Matrix n n E} {y : n → E} [FinComplexSpace V]
  {Q : RealVectors E n ≃L[ℝ] V}

omit [Fintype n] in
lemma toRealVectors_injective : Injective (@toRealVectors E n _ _) :=
  (@cmEmbedding E ..).injective.comp_left

omit [Fintype n] in
@[simp] lemma toRealVectors_smul (c : 𝓞 E) : toRealVectors (c • y) =
  cmEmbedding c.val • toRealVectors y := funext (cmEmbedding.map_mul _ <| y ·)

lemma mem_classLattice {x} : x ∈ classLattice g S Q ↔ ∃ y, frameTorsionClass g y ∈ S ∧
  Q (toRealVectors y) = x := .rfl

@[simp↓] lemma realVecAction_toRealVectors : realVecAction A (toRealVectors y) =
  toRealVectors (A *ᵥ y) := (funext (cmEmbedding.map_mulVec _ _)).symm

lemma realVecAction_mem_frameLattice {P} (h : ∀ i j, (g'⁻¹.1 * A.map (algebraMap ..) * g.1 :) i j ∈ Ô E) : P ∈ frameLattice g →
    realVecAction A P ∈ frameLattice g' | ⟨_, k, e⟩ => e ▸ ⟨_, by simpa using torsionClass_mulVec_eq_zero h k, realVecAction_toRealVectors.symm⟩

@[simp] lemma realVecAction_apply w i v : (A.map cmEmbedding *ᵥ w) i v =
  (A.map (Φ v) *ᵥ (w · v)) i := Finset.sum_apply ..

omit [Fintype n] in
lemma denseRange_toRealVectors : DenseRange (@toRealVectors E n _ _) :=
  .piMap (const _ denseRange_Φ)

instance : DiscreteTopology (classLattice g ⊥ Q) := continuous_subtype_val
  |>.discrete_of_tendsto_cofinite_cocompact (tendsto_cofinite_cocompact_iff.2 fun _ K ↦
  (((isCovolOneLattice_ratVectors.finite_preimage
  ((K.prod (isCompact_pi_infinite (const _ isCompact_Ô))).image_auto fun p i ↦
  (Q.symm p.1 i, mulVec g p.2 i))).image _).preimage injOn_subtype_val
  ).subset fun ⟨_, y, h, e⟩ H ↦ ⟨_, ⟨(_, _), ⟨H, torsionClass_eq_zero.1 h⟩, by aesop⟩, e⟩)

instance [DiscreteTopology (classLattice g S Q)] : IsZLattice ℝ (classLattice g S Q) :=
  ⟨eq_top_iff'.2 ((reindex_equiv Q).1.2 (isClosed_property denseRange_toRealVectors (comap ..
  ).closed_of_finiteDimensional fun y ↦ (exists_nsmul_adelicTorsion_eq_zero
  (frameTorsionClass g y)).elim fun m _ ↦ (smul_mem_iff (s := (m : ℝ)) _ (by aesop)).1
  (subset_span ⟨m • y, mod_cast by simp_all [-nsmul_eq_mul, -frameTorsionClass]⟩)))⟩
