/- GID: D5/S3/Arith/PrimeIdeals/NormResidue/IdealCongruenceCountCellGeometry
   generality: G
   mirror-B: D5/B/S3/Arith/PrimeIdeals/NormResidue/IdealCongruenceCountCellGeometry
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Per-cell residue estimates sum to a global cone count estimate. -/
module

public import D5.S3.Arith.PrimeIdeals.NormResidue.IdealCongruenceCountAlgebra

@[expose] public section

noncomputable section

namespace Chebotarev

open NumberField Set Submodule

open scoped NNReal nonZeroDivisors Pointwise

/-! ### The per-(orthant, coset) workhorse wrapper -/

/-- **Per-cell effective count with explicit constant.** Specialisation of the workhorse
`exists_card_coset_inter_smul_sub_volume_mul_rpow_le` to the `m`-sublattice `m • (T '' ℤ^ι)`
(realised as `T' '' ℤ^ι` with `T' = (m • ·) ∘ T`) and the orthant-cut region `D₀ ∩ orthant`, with
the leading constant stated as the explicit term `vol(Ds)/|det ((m·)∘T)|`. -/
theorem exists_card_cell_sub_mul_rpow_le_explicit {ι : Type*} [Fintype ι]
    (T : (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ)) (m : ℕ) (hm : (m : ℝ) ≠ 0) (D₀ : Set (ι → ℝ))
    (hbdd : Bornology.IsBounded D₀) (hmeas : MeasurableSet D₀)
    (hlip : ∃ (m : ℕ) (M : ℝ≥0) (φ : Fin m → (Fin (Fintype.card ι - 1) → ℝ) → (ι → ℝ)),
      (∀ j, LipschitzWith M (φ j)) ∧ frontier D₀ ⊆ ⋃ j, φ j '' Set.Icc 0 1)
    {κ : Type*} [Finite κ] (g : κ → ι) (s : Finset κ) :
    ∃ C : ℝ, ∀ ξ : ι → ℝ, ∀ t : ℝ, 1 ≤ t →
      |(Nat.card ↑((ξ +ᵥ
          (((LinearEquiv.smulOfNeZero ℝ (ι → ℝ) (m : ℝ) hm).trans T) ''
            (span ℤ (Set.range (Pi.basisFun ℝ ι)) : Set (ι → ℝ)))) ∩
            t • (D₀ ∩ {y : ι → ℝ | (∀ k ∈ s, y (g k) ≤ 0) ∧ (∀ k ∉ s, 0 ≤ y (g k))})) : ℝ)
          - (MeasureTheory.volume.real
              (D₀ ∩ {y : ι → ℝ | (∀ k ∈ s, y (g k) ≤ 0) ∧ (∀ k ∉ s, 0 ≤ y (g k))})
              / |LinearMap.det (((LinearEquiv.smulOfNeZero ℝ (ι → ℝ) (m : ℝ) hm).trans T
                : (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ)) : (ι → ℝ) →ₗ[ℝ] (ι → ℝ))|)
              * t ^ (Fintype.card ι)|
        ≤ C * t ^ (Fintype.card ι - 1 : ℕ) := by
  classical
  haveI : Fintype κ := Fintype.ofFinite κ
  set T' : (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ) := (LinearEquiv.smulOfNeZero ℝ (ι → ℝ) (m : ℝ) hm).trans T
  set Ds : Set (ι → ℝ) :=
    D₀ ∩ {y : ι → ℝ | (∀ k ∈ s, y (g k) ≤ 0) ∧ (∀ k ∉ s, 0 ≤ y (g k))}
  have hDsbdd : Bornology.IsBounded Ds := hbdd.subset Set.inter_subset_left
  have hOclosed : IsClosed {y : ι → ℝ | (∀ k ∈ s, y (g k) ≤ 0) ∧ (∀ k ∉ s, 0 ≤ y (g k))} := by
    classical
    rw [setOf_and]
    refine IsClosed.inter ?_ ?_
    · have h : {y : ι → ℝ | ∀ k ∈ s, y (g k) ≤ 0} = ⋂ k ∈ s, {y : ι → ℝ | y (g k) ≤ 0} := by
        ext y; simp
      rw [h]
      exact isClosed_biInter (fun k _ ↦ isClosed_le (continuous_apply (g k)) continuous_const)
    · have h : {y : ι → ℝ | ∀ k ∉ s, 0 ≤ y (g k)}
          = ⋂ k ∈ (sᶜ : Finset κ), {y : ι → ℝ | 0 ≤ y (g k)} := by ext y; simp
      rw [h]
      exact isClosed_biInter (fun k _ ↦ isClosed_le continuous_const (continuous_apply (g k)))
  have hDsmeas : MeasurableSet Ds := hmeas.inter hOclosed.measurableSet
  exact exists_card_coset_inter_smul_sub_volume_mul_rpow_le T' Ds hDsbdd hDsmeas
    (exists_frontier_cover_inter_orthant g s D₀ hbdd hlip)

/-! ### Effective residue count in an orthant cell -/

set_option maxHeartbeats 1600000 in
open NumberField.mixedEmbedding NumberField.mixedEmbedding.fundamentalCone
  NumberField.InfinitePlace Classical in
/-- **(STAGE A, fibre level) Per-(orthant, coset) effective residue count with explicit constant.**
The leading constant is explicit:
`if the cell carries residue b then vol((Φ''normLeOne)∩orthant)/|det ((m·)∘T)| else 0`. -/
theorem exists_card_residue_fibre_sub_mul_rpow_le_explicit {K : Type*} [Field K]
    [NumberField K] (m : ℕ) [NeZero m] (hm : (m : ℝ) ≠ 0) (b : ℕ) (J : (Ideal (𝓞 K))⁰)
    (T : (index K → ℝ) ≃ₗ[ℝ] (index K → ℝ))
    (hT : T '' (span ℤ (Set.range (Pi.basisFun ℝ (index K))) : Set (index K → ℝ))
        = ((mixedEmbedding.stdBasis K).equivFunL '' (mixedEmbedding.idealLattice K
            (FractionalIdeal.mk0 K J)) : Set (index K → ℝ)))
    (hcov : ∃ (mc : ℕ) (M : ℝ≥0) (φ : Fin mc → (Fin (Fintype.card (index K) - 1) → ℝ) →
        (index K → ℝ)), (∀ j, LipschitzWith M (φ j)) ∧
      frontier ((mixedEmbedding.stdBasis K).equivFunL '' (normLeOne K)) ⊆ ⋃ j, φ j '' Set.Icc 0 1)
    (s : Finset {w : InfinitePlace K // IsReal w}) (k : index K → ZMod m) :
    ∃ C : ℝ, ∀ t : ℝ, 1 ≤ t →
      |(Nat.card {a : idealSet K J //
          (mixedEmbedding.norm (a : mixedSpace K) ≤ t ^ Module.finrank ℚ K ∧
            ((intNorm (idealSetEquiv K J a).val : ZMod m) = (b : ZMod m))) ∧
          (Finset.univ.filter (fun w : {w : InfinitePlace K // IsReal w} ↦
            (a : mixedSpace K).1 w < 0) = s) ∧
          (fun i ↦ (round ((T.symm ((mixedEmbedding.stdBasis K).equivFunL
            (a : mixedSpace K))) i) : ZMod m)) = k} : ℝ)
          - (if (∃ a : idealSet K J,
              (Finset.univ.filter (fun w : {w : InfinitePlace K // IsReal w} ↦
                (a : mixedSpace K).1 w < 0) = s) ∧
              ((fun i ↦ (round ((T.symm ((mixedEmbedding.stdBasis K).equivFunL
                (a : mixedSpace K))) i) : ZMod m)) = k) ∧
              ((intNorm (idealSetEquiv K J a).val : ZMod m) = (b : ZMod m)))
            then MeasureTheory.volume.real
              ((mixedEmbedding.stdBasis K).equivFunL '' (normLeOne K) ∩
                {y : index K → ℝ | (∀ w ∈ s, y (Sum.inl w) ≤ 0) ∧ (∀ w ∉ s, 0 ≤ y (Sum.inl w))})
              / |LinearMap.det (((LinearEquiv.smulOfNeZero ℝ (index K → ℝ) (m : ℝ) hm).trans T
                : (index K → ℝ) ≃ₗ[ℝ] (index K → ℝ)) : (index K → ℝ) →ₗ[ℝ] (index K → ℝ))|
            else 0) * t ^ Module.finrank ℚ K|
        ≤ C * t ^ (Module.finrank ℚ K - 1 : ℕ) := by
  classical
  have sub_mem_nsmul_of_coord_eq
      (m : ℕ) (J : (Ideal (𝓞 K))⁰) (T : (index K → ℝ) ≃ₗ[ℝ] (index K → ℝ))
      (hT : T '' (span ℤ (Set.range (Pi.basisFun ℝ (index K))) : Set (index K → ℝ))
          = ((mixedEmbedding.stdBasis K).equivFunL '' (mixedEmbedding.idealLattice K
              (FractionalIdeal.mk0 K J)) : Set (index K → ℝ)))
      {x₁ x₂ : mixedSpace K}
      (hx₁ : x₁ ∈ mixedEmbedding.idealLattice K (FractionalIdeal.mk0 K J))
      (hx₂ : x₂ ∈ mixedEmbedding.idealLattice K (FractionalIdeal.mk0 K J))
      (hcos : ∀ i, ((round ((T.symm ((mixedEmbedding.stdBasis K).equivFunL x₁)) i) : ZMod m)) =
        ((round ((T.symm ((mixedEmbedding.stdBasis K).equivFunL x₂)) i) : ZMod m))) :
      x₁ - x₂ ∈
        (m : ℝ) • (mixedEmbedding.idealLattice K (FractionalIdeal.mk0 K J) : Set (mixedSpace K)) := by
    classical
    set Φ : mixedSpace K ≃L[ℝ] (index K → ℝ) := (mixedEmbedding.stdBasis K).equivFunL with hΦ
    have hspan (v : index K → ℝ) :
        v ∈ span ℤ (Set.range (Pi.basisFun ℝ (index K))) ↔
          ∀ i, ∃ n : ℤ, v i = (n : ℝ) := by
      letI : Fintype (index K) := Fintype.ofFinite _
      simp only [(Pi.basisFun ℝ (index K)).mem_span_iff_repr_mem ℤ v, Pi.basisFun_repr,
        Set.mem_range, eq_intCast, eq_comm]
    have hcoords (x : mixedSpace K)
        (hx : x ∈ mixedEmbedding.idealLattice K (FractionalIdeal.mk0 K J)) :
        ∀ i, ∃ n : ℤ, (T.symm (Φ x)) i = (n : ℝ) := by
      have hmem : Φ x ∈ T '' (span ℤ (Set.range (Pi.basisFun ℝ (index K)))) := by
        rw [hT]; exact ⟨x, hx, rfl⟩
      obtain ⟨v, hv, hveq⟩ := hmem
      have hsymm : T.symm (Φ x) = v := by rw [← hveq, LinearEquiv.symm_apply_apply]
      rw [hsymm]
      exact (hspan v).mp hv
    choose n₁ hn₁ using hcoords x₁ hx₁
    choose n₂ hn₂ using hcoords x₂ hx₂
    have hround : ∀ (x : mixedSpace K) (n : index K → ℤ),
        (∀ i, (T.symm (Φ x)) i = (n i : ℝ)) →
          ∀ i, round ((T.symm (Φ x)) i) = n i := fun x n h i ↦ by
      rw [h i, round_intCast]
    have hdvd : ∀ i, (m : ℤ) ∣ (n₁ i - n₂ i) := fun i ↦ by
      have h := hcos i
      rw [hround x₁ n₁ hn₁ i, hround x₂ n₂ hn₂ i] at h
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_sub, sub_eq_zero]
      exact h
    choose p hp using hdvd
    have hdiff : T.symm (Φ x₁) - T.symm (Φ x₂) = (m : ℝ) • (fun i ↦ (p i : ℝ)) := by
      funext i
      rw [Pi.sub_apply, Pi.smul_apply, hn₁ i, hn₂ i, smul_eq_mul]
      have hZ : (n₁ i - n₂ i : ℤ) = (m : ℤ) * p i := hp i
      have : (n₁ i : ℝ) - (n₂ i : ℝ) = (m : ℝ) * (p i : ℝ) := by exact_mod_cast hZ
      linarith
    have hpmem : (fun i ↦ (p i : ℝ)) ∈ span ℤ (Set.range (Pi.basisFun ℝ (index K))) :=
      (hspan _).mpr (fun i ↦ ⟨p i, rfl⟩)
    have hTp : T (fun i ↦ (p i : ℝ)) ∈ Φ '' (mixedEmbedding.idealLattice K
        (FractionalIdeal.mk0 K J) : Set (mixedSpace K)) := by
      rw [← hT]; exact ⟨_, hpmem, rfl⟩
    obtain ⟨z, hzmem, hzeq⟩ := hTp
    refine ⟨z, hzmem, ?_⟩
    have hkey : Φ (x₁ - x₂) = Φ ((m : ℝ) • z) := by
      rw [map_sub, map_smul]
      have h1 : Φ x₁ - Φ x₂ = T (T.symm (Φ x₁) - T.symm (Φ x₂)) := by
        rw [map_sub, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
      rw [h1, hdiff, map_smul, hzeq]
    exact (Φ.injective hkey).symm
  have mem_coset_iff_cos_eq
      (m : ℕ) [NeZero m] (hm : (m : ℝ) ≠ 0) (J : (Ideal (𝓞 K))⁰)
      (T : (index K → ℝ) ≃ₗ[ℝ] (index K → ℝ))
      (hT : T '' (span ℤ (Set.range (Pi.basisFun ℝ (index K))) : Set (index K → ℝ))
          = ((mixedEmbedding.stdBasis K).equivFunL '' (mixedEmbedding.idealLattice K
              (FractionalIdeal.mk0 K J)) : Set (index K → ℝ)))
      (k : index K → ZMod m) {x : mixedSpace K}
      (hx : x ∈ mixedEmbedding.idealLattice K (FractionalIdeal.mk0 K J)) :
      (mixedEmbedding.stdBasis K).equivFunL x ∈
          ((T (fun i ↦ ((k i).val : ℝ)) : index K → ℝ) +ᵥ
            (((LinearEquiv.smulOfNeZero ℝ (index K → ℝ) (m : ℝ) hm).trans T) ''
              (span ℤ (Set.range (Pi.basisFun ℝ (index K))) : Set (index K → ℝ)))) ↔
        (∀ i, ((round ((T.symm ((mixedEmbedding.stdBasis K).equivFunL x)) i) : ZMod m)) = k i) := by
    classical
    set Φ : mixedSpace K ≃L[ℝ] (index K → ℝ) := (mixedEmbedding.stdBasis K).equivFunL with hΦ
    have hspan (v : index K → ℝ) :
        v ∈ span ℤ (Set.range (Pi.basisFun ℝ (index K))) ↔
          ∀ i, ∃ n : ℤ, v i = (n : ℝ) := by
      letI : Fintype (index K) := Fintype.ofFinite _
      simp only [(Pi.basisFun ℝ (index K)).mem_span_iff_repr_mem ℤ v, Pi.basisFun_repr,
        Set.mem_range, eq_intCast, eq_comm]
    have hcoords : ∀ i, ∃ n : ℤ, (T.symm (Φ x)) i = (n : ℝ) := by
      have hmem : Φ x ∈ T '' (span ℤ (Set.range (Pi.basisFun ℝ (index K)))) := by
        rw [hT]; exact ⟨x, hx, rfl⟩
      obtain ⟨v, hv, hveq⟩ := hmem
      have hsymm : T.symm (Φ x) = v := by rw [← hveq, LinearEquiv.symm_apply_apply]
      rw [hsymm]
      exact (hspan v).mp hv
    choose n hn using hcoords
    have hround : ∀ i, round ((T.symm (Φ x)) i) = n i := fun i ↦ by rw [hn i, round_intCast]
    simp only [hround, Set.mem_vadd_set, Set.mem_image, SetLike.mem_coe]
    have hgoal : (∀ i, ((n i : ZMod m)) = k i) ↔ (∀ i, (m : ℤ) ∣ (n i - (k i).val)) := by
      refine forall_congr' fun i ↦ ?_
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_sub, sub_eq_zero, Int.cast_natCast,
        ZMod.natCast_zmod_val]
    rw [hgoal]
    have hkey : ∀ p : index K → ℤ,
        (T ((fun i ↦ ((k i).val : ℝ)) + (m : ℝ) • (fun i ↦ (p i : ℝ))) = Φ x) ↔
          (∀ i, n i = (k i).val + (m : ℤ) * p i) := fun p ↦ by
      rw [← (LinearEquiv.eq_symm_apply T)]
      constructor
      · intro heq i
        have hc := congrFun heq i
        rw [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hn i] at hc
        have : (n i : ℝ) = ((k i).val + (m : ℤ) * p i : ℤ) := by push_cast; linarith
        exact_mod_cast this
      · intro h
        funext i
        rw [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hn i]
        have := h i; push_cast [this]; ring
    constructor
    · rintro ⟨w, ⟨v, hv, rfl⟩, hweq⟩
      rw [LinearEquiv.trans_apply, LinearEquiv.smulOfNeZero_apply, vadd_eq_add, ← map_add] at hweq
      rw [hspan] at hv
      choose p hp using hv
      have hpp : v = (fun i ↦ (p i : ℝ)) := funext hp
      rw [hpp] at hweq
      exact fun i ↦ ⟨p i, by rw [(hkey p).mp hweq i]; ring⟩
    · intro h
      choose p hp using h
      refine ⟨(LinearEquiv.smulOfNeZero ℝ (index K → ℝ) (m : ℝ) hm).trans T (fun i ↦ (p i : ℝ)),
        ⟨_, (hspan _).mpr (fun i ↦ ⟨p i, rfl⟩), rfl⟩, ?_⟩
      rw [LinearEquiv.trans_apply, LinearEquiv.smulOfNeZero_apply, vadd_eq_add, ← map_add]
      exact (hkey p).mpr fun i ↦ by have := hp i; lia
  have mem_smul_cell_iff_norm_le_and_filter_eq
      (J : (Ideal (𝓞 K))⁰) (s : Finset {w : InfinitePlace K // IsReal w}) {t : ℝ} (ht : 1 ≤ t)
      {x : mixedSpace K} (hx : x ∈ idealSet K J) :
      (mixedEmbedding.stdBasis K).equivFunL x ∈ t • ((mixedEmbedding.stdBasis K).equivFunL ''
          (normLeOne K) ∩ {y : index K → ℝ |
            (∀ w ∈ s, y (Sum.inl w) ≤ 0) ∧ (∀ w ∉ s, 0 ≤ y (Sum.inl w))}) ↔
        (mixedEmbedding.norm x ≤ t ^ Module.finrank ℚ K ∧
          Finset.univ.filter (fun w : {w : InfinitePlace K // IsReal w} ↦ x.1 w < 0) = s) := by
    classical
    set Φ : mixedSpace K ≃L[ℝ] (index K → ℝ) := (mixedEmbedding.stdBasis K).equivFunL with hΦ
    set d := Module.finrank ℚ K
    have hΦreal : ∀ (x : mixedSpace K) (w : {w : InfinitePlace K // IsReal w}),
        Φ x (Sum.inl w) = x.1 w := fun x w ↦ by
      rw [hΦ, Module.Basis.equivFunL_apply, mixedEmbedding.stdBasis_apply_isReal]
    have hcone : {x : mixedSpace K | x ∈ fundamentalCone K ∧ mixedEmbedding.norm x ≤ t ^ d}
        = t • normLeOne K := by
      have htpos : (0 : ℝ) < t := lt_of_lt_of_le one_pos ht
      have htne : t ≠ 0 := htpos.ne'
      ext z
      simp only [Set.mem_setOf_eq, Set.mem_smul_set, normLeOne, Set.mem_inter_iff,
        Set.mem_setOf_eq]
      constructor
      · rintro ⟨hzc, hzn⟩
        refine ⟨t⁻¹ • z, ⟨(smul_mem_iff_mem (inv_ne_zero htne)).mpr hzc, ?_⟩, ?_⟩
        · rw [mixedEmbedding.norm_smul, abs_of_pos (inv_pos.mpr htpos), inv_pow,
            inv_mul_le_one₀ (by positivity)]
          exact hzn
        · rw [smul_smul, mul_inv_cancel₀ htne, one_smul]
      · rintro ⟨z', ⟨hzc, hzn⟩, rfl⟩
        refine ⟨(smul_mem_iff_mem htne).mpr hzc, ?_⟩
        rw [mixedEmbedding.norm_smul, abs_of_pos htpos]
        calc t ^ d * mixedEmbedding.norm z'
            ≤ t ^ d * 1 := mul_le_mul_of_nonneg_left hzn (by positivity)
          _ = t ^ d := mul_one _
    have ht0 : t ≠ 0 := (lt_of_lt_of_le one_pos ht).ne'
    have htinv : (0 : ℝ) < t⁻¹ := inv_pos.mpr (lt_of_lt_of_le one_pos ht)
    have himg : Φ '' (t • normLeOne K) = t • (Φ '' normLeOne K) :=
      Set.image_smul_comm Φ t _ (fun b ↦ map_smul Φ t b)
    have hnz : ∀ x ∈ t • normLeOne K, ∀ w : {w : InfinitePlace K // IsReal w}, x.1 w ≠ 0 := by
      rintro _ ⟨z, hz, rfl⟩ w
      intro h
      have hp := fundamentalCone.normAtPlace_pos_of_mem (smul_mem_of_mem hz.1 ht0) w.1
      rw [mixedEmbedding.normAtPlace_apply_of_isReal w.2] at hp
      simp [h] at hp
    rw [Set.smul_set_inter₀ ht0, Set.mem_inter_iff, ← himg]
    constructor
    · rintro ⟨hmem, horth⟩
      rw [Set.mem_image] at hmem
      obtain ⟨z, hz, hzeq⟩ := hmem
      have hxcone : x ∈ t • normLeOne K := by rwa [Φ.injective hzeq] at hz
      have hnorm : x ∈ {x | x ∈ fundamentalCone K ∧ mixedEmbedding.norm x ≤ t ^ d} := by
        rw [hcone]; exact hxcone
      refine ⟨hnorm.2, ?_⟩
      ext w
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [Set.mem_smul_set_iff_inv_smul_mem₀ ht0] at horth
      obtain ⟨hneg, hpos⟩ := horth
      refine ⟨fun hlt ↦ ?_, fun hw ↦ ?_⟩
      · by_contra hws
        have h2 := hpos w hws
        rw [Pi.smul_apply, smul_eq_mul, hΦreal] at h2
        nlinarith [h2, htinv, hlt]
      · have h2 := hneg w hw
        rw [Pi.smul_apply, smul_eq_mul, hΦreal] at h2
        rcases lt_or_gt_of_ne (hnz x hxcone w) with h | h
        · exact h
        · nlinarith [h2, htinv, h]
    · rintro ⟨hnorm, horth⟩
      have hxcone : x ∈ t • normLeOne K := by rw [← hcone]; exact ⟨hx.1, hnorm⟩
      refine ⟨⟨x, hxcone, rfl⟩, ?_⟩
      rw [Set.mem_smul_set_iff_inv_smul_mem₀ ht0]
      refine ⟨fun w hw ↦ ?_, fun w hw ↦ ?_⟩
      · rw [Pi.smul_apply, smul_eq_mul, hΦreal]
        have hlt : x.1 w < 0 := by
          have : w ∈ Finset.univ.filter (fun w ↦ x.1 w < 0) := horth ▸ hw
          simpa using this
        nlinarith [hlt, htinv]
      · rw [Pi.smul_apply, smul_eq_mul, hΦreal]
        have hxw : ¬ x.1 w < 0 := fun hlt ↦ hw (by
          have : w ∈ Finset.univ.filter (fun w ↦ x.1 w < 0) := by simpa using hlt
          rwa [horth] at this)
        nlinarith [not_lt.mp hxw, htinv]
  have card_fibre_eq_card_cell
      (m : ℕ) [NeZero m] (hm : (m : ℝ) ≠ 0) (J : (Ideal (𝓞 K))⁰)
      (T : (index K → ℝ) ≃ₗ[ℝ] (index K → ℝ))
      (hT : T '' (span ℤ (Set.range (Pi.basisFun ℝ (index K))) : Set (index K → ℝ))
          = ((mixedEmbedding.stdBasis K).equivFunL '' (mixedEmbedding.idealLattice K
              (FractionalIdeal.mk0 K J)) : Set (index K → ℝ)))
      (s : Finset {w : InfinitePlace K // IsReal w}) (k : index K → ZMod m)
      {t : ℝ} (ht : 1 ≤ t) :
      Nat.card {a : idealSet K J // mixedEmbedding.norm (a : mixedSpace K) ≤ t ^ Module.finrank ℚ K ∧
          (Finset.univ.filter (fun w : {w : InfinitePlace K // IsReal w} ↦
            (a : mixedSpace K).1 w < 0) = s) ∧
          (fun i ↦ (round ((T.symm ((mixedEmbedding.stdBasis K).equivFunL
            (a : mixedSpace K))) i) : ZMod m)) = k}
      = Nat.card ↑(((T (fun i ↦ ((k i).val : ℝ)) : index K → ℝ) +ᵥ
          (((LinearEquiv.smulOfNeZero ℝ (index K → ℝ) (m : ℝ) hm).trans T) ''
            (span ℤ (Set.range (Pi.basisFun ℝ (index K))) : Set (index K → ℝ)))) ∩
          t • ((mixedEmbedding.stdBasis K).equivFunL '' (normLeOne K) ∩
            {y : index K → ℝ | (∀ w ∈ s, y (Sum.inl w) ≤ 0) ∧ (∀ w ∉ s, 0 ≤ y (Sum.inl w))})) := by
    classical
    set Φ : mixedSpace K ≃L[ℝ] (index K → ℝ) := (mixedEmbedding.stdBasis K).equivFunL
    have hspan (v : index K → ℝ) :
        v ∈ span ℤ (Set.range (Pi.basisFun ℝ (index K))) ↔
          ∀ i, ∃ n : ℤ, v i = (n : ℝ) := by
      letI : Fintype (index K) := Fintype.ofFinite _
      simp only [(Pi.basisFun ℝ (index K)).mem_span_iff_repr_mem ℤ v, Pi.basisFun_repr,
        Set.mem_range, eq_intCast, eq_comm]
    set d := Module.finrank ℚ K
    set f : {a : idealSet K J // mixedEmbedding.norm (a : mixedSpace K) ≤ t ^ d ∧
        (Finset.univ.filter (fun w : {w : InfinitePlace K // IsReal w} ↦
          (a : mixedSpace K).1 w < 0) = s) ∧
        (fun i ↦ (round ((T.symm (Φ (a : mixedSpace K))) i) : ZMod m)) = k} → (index K → ℝ) :=
      fun a ↦ Φ (a.1 : mixedSpace K) with hf
    have hfinj : Function.Injective f := fun _ _ h ↦ Subtype.ext (Subtype.ext (Φ.injective h))
    have ht0 : t ≠ 0 := (lt_of_lt_of_le one_pos ht).ne'
    set Os : Set (index K → ℝ) :=
      {y : index K → ℝ | (∀ w ∈ s, y (Sum.inl w) ≤ 0) ∧ (∀ w ∉ s, 0 ≤ y (Sum.inl w))} with hOs
    have hreg : ∀ x : mixedSpace K, x ∈ idealSet K J →
        (Φ x ∈ t • ((mixedEmbedding.stdBasis K).equivFunL '' (normLeOne K) ∩ Os) ↔
          (mixedEmbedding.norm x ≤ t ^ d ∧
            Finset.univ.filter (fun w : {w : InfinitePlace K // IsReal w} ↦ x.1 w < 0) = s)) :=
      fun x hx ↦ mem_smul_cell_iff_norm_le_and_filter_eq J s ht hx
    have hsub : ((T (fun i ↦ ((k i).val : ℝ)) : index K → ℝ) +ᵥ
        (((LinearEquiv.smulOfNeZero ℝ (index K → ℝ) (m : ℝ) hm).trans T) ''
          (span ℤ (Set.range (Pi.basisFun ℝ (index K))) : Set (index K → ℝ))))
        ⊆ (Φ '' (mixedEmbedding.idealLattice K (FractionalIdeal.mk0 K J)) : Set (index K → ℝ)) := by
      rw [← hT]
      rintro _ ⟨w, ⟨v, hv, rfl⟩, rfl⟩
      simp only [LinearEquiv.trans_apply, LinearEquiv.smulOfNeZero_apply, vadd_eq_add]
      rw [← map_add]
      refine ⟨_, ?_, rfl⟩
      refine add_mem ((hspan _).mpr (fun i ↦ ⟨(k i).val, rfl⟩)) ?_
      rw [Nat.cast_smul_eq_nsmul]
      exact nsmul_mem hv _
    have hset : Set.range f =
        (((T (fun i ↦ ((k i).val : ℝ)) : index K → ℝ) +ᵥ
          (((LinearEquiv.smulOfNeZero ℝ (index K → ℝ) (m : ℝ) hm).trans T) ''
            (span ℤ (Set.range (Pi.basisFun ℝ (index K))) : Set (index K → ℝ)))) ∩
          t • ((mixedEmbedding.stdBasis K).equivFunL '' (normLeOne K) ∩ Os)) := by
      ext y
      simp only [hf, Set.mem_range, Subtype.exists, Set.mem_inter_iff]
      constructor
      · rintro ⟨a, ha, hP, rfl⟩
        refine ⟨(mem_coset_iff_cos_eq m hm J T hT k ha.2).mpr (fun i ↦ congrFun hP.2.2 i), ?_⟩
        exact hreg a ha |>.mpr ⟨hP.1, hP.2.1⟩
      · rintro ⟨hcoset, hregion⟩
        obtain ⟨z, hzlat, hzeq⟩ := hsub hcoset
        have hzcone : z ∈ idealSet K J := by
          have himg : Φ '' (t • normLeOne K) = t • (Φ '' normLeOne K) :=
            Set.image_smul_comm Φ t _ (fun u ↦ map_smul Φ t u)
          obtain ⟨hmem, _⟩ := (by
            rwa [Set.smul_set_inter₀ ht0, Set.mem_inter_iff] at hregion :
              y ∈ t • (Φ '' normLeOne K) ∧ y ∈ t • Os)
          rw [← himg, Set.mem_image] at hmem
          obtain ⟨z', hz', hz'eq⟩ := hmem
          have hzn : z ∈ t • normLeOne K := by
            rw [show z = z' from Φ.injective (by rw [hz'eq, hzeq])]; exact hz'
          exact ⟨(by obtain ⟨u, hu, rfl⟩ := hzn; exact smul_mem_of_mem hu.1 ht0), hzlat⟩
        refine ⟨z, hzcone, ⟨?_, ?_, ?_⟩, hzeq⟩
        · exact (hreg z hzcone |>.mp (by rw [hzeq]; exact hregion)).1
        · exact (hreg z hzcone |>.mp (by rw [hzeq]; exact hregion)).2
        · funext i
          exact (mem_coset_iff_cos_eq m hm J T hT k hzcone.2).mp (by rw [hzeq]; exact hcoset) i
    rw [← Nat.card_range_of_injective hfinj, hset]
  have residue_fibre_const_aux
      (m : ℕ) (b : ℕ) (J : (Ideal (𝓞 K))⁰)
      (T : (index K → ℝ) ≃ₗ[ℝ] (index K → ℝ))
      (hT : T '' (span ℤ (Set.range (Pi.basisFun ℝ (index K))) : Set (index K → ℝ))
          = ((mixedEmbedding.stdBasis K).equivFunL '' (mixedEmbedding.idealLattice K
              (FractionalIdeal.mk0 K J)) : Set (index K → ℝ)))
      (s : Finset {w : InfinitePlace K // IsReal w}) (k : index K → ZMod m)
      (a a' : idealSet K J)
      (horth : Finset.univ.filter (fun w : {w : InfinitePlace K // IsReal w} ↦
        (a : mixedSpace K).1 w < 0) = s)
      (hcos : (fun i ↦ (round ((T.symm ((mixedEmbedding.stdBasis K).equivFunL
        (a : mixedSpace K))) i) : ZMod m)) = k)
      (horth' : Finset.univ.filter (fun w : {w : InfinitePlace K // IsReal w} ↦
        (a' : mixedSpace K).1 w < 0) = s)
      (hcos' : (fun i ↦ (round ((T.symm ((mixedEmbedding.stdBasis K).equivFunL
        (a' : mixedSpace K))) i) : ZMod m)) = k) :
      (((intNorm (idealSetEquiv K J a).val : ZMod m) = (b : ZMod m)) ↔
        ((intNorm (idealSetEquiv K J a').val : ZMod m) = (b : ZMod m))) := by
    classical
    have hsign : ∀ c : idealSet K J,
        Finset.univ.filter (fun w : {w : InfinitePlace K // IsReal w} ↦
          (c : mixedSpace K).1 w < 0) = s →
        (((intNorm (idealSetEquiv K J c).val : ZMod m) = (b : ZMod m)) ↔
          (((-1) ^ s.card *
            (Algebra.norm ℤ (preimageOfMemIntegerSet (idealSetMap K J c) : 𝓞 K) : ℤ) : ℤ) :
            ZMod m) = (b : ZMod m)) := by
      intro c hc
      set gen : 𝓞 K := (preimageOfMemIntegerSet (idealSetMap K J c) : 𝓞 K)
      have hema : mixedEmbedding K (gen : K) = (c : mixedSpace K) := by
        rw [mixedEmbedding_preimageOfMemIntegerSet, idealSetMap_apply]
      have hneg : ∀ w ∈ s, (mixedEmbedding K (gen : K)).1 w < 0 := by
        intro w hw
        rw [hema]
        have : w ∈ Finset.univ.filter (fun w ↦ (c : mixedSpace K).1 w < 0) := hc ▸ hw
        simpa using this
      have hpos : ∀ w ∉ s, 0 < (mixedEmbedding K (gen : K)).1 w := by
        intro w hw
        rw [hema]
        have hcw : (c : mixedSpace K).1 w ≠ 0 := by
          intro h
          have hp := fundamentalCone.normAtPlace_pos_of_mem c.2.1 w.1
          rw [mixedEmbedding.normAtPlace_apply_of_isReal w.2] at hp
          simp [h] at hp
        have hge : ¬ (c : mixedSpace K).1 w < 0 := fun hlt ↦ hw (by
          have : w ∈ Finset.univ.filter (fun w ↦ (c : mixedSpace K).1 w < 0) := by simpa using hlt
          rwa [hc] at this)
        exact lt_of_le_of_ne (not_lt.mp hge) (Ne.symm hcw)
      have hnormProduct (y : K) :
          ((Algebra.norm ℚ y : ℝ)) =
            (∏ w : {w : InfinitePlace K // IsReal w}, embedding_of_isReal w.2 y) *
              (∏ w : {w : InfinitePlace K // IsComplex w}, ‖(w.1.embedding) y‖ ^ 2) := by
        have hcc : ((Algebra.norm ℚ y : ℝ) : ℂ) =
            ((∏ w : {w : InfinitePlace K // IsReal w}, embedding_of_isReal w.2 y : ℝ) : ℂ) *
              ((∏ w : {w : InfinitePlace K // IsComplex w}, ‖(w.1.embedding) y‖ ^ 2 : ℝ) : ℂ) := by
          have hperplace : ∀ w : InfinitePlace K,
              ∏ ψ ∈ Finset.univ.filter (fun ψ : K →+* ℂ ↦ mk ψ = w), ψ y =
                if hw : IsReal w then ((embedding_of_isReal hw y : ℝ) : ℂ)
                else (‖(embedding w) y‖ ^ 2 : ℝ) := by
            intro w
            have hfilter : Finset.univ.filter (fun ψ : K →+* ℂ ↦ mk ψ = w)
                = {embedding w, ComplexEmbedding.conjugate (embedding w)} := by
              ext ψ
              simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
                Finset.mem_singleton]
              conv_lhs => rw [← mk_embedding w, mk_eq_iff, ComplexEmbedding.conjugate,
                star_involutive.eq_iff]
            rw [hfilter]
            by_cases hw : IsReal w
            · rw [dif_pos hw, ComplexEmbedding.isReal_iff.mp (isReal_iff.mp hw),
                Finset.insert_eq_self.mpr (Finset.mem_singleton_self _), Finset.prod_singleton,
                embedding_of_isReal_apply hw]
            · rw [dif_neg hw, Finset.prod_pair]
              · rw [ComplexEmbedding.conjugate_coe_eq, Complex.mul_conj]
                norm_cast
                rw [Complex.normSq_eq_norm_sq]
              · rw [Ne, eq_comm, ← ComplexEmbedding.isReal_iff, ← isReal_iff]; exact hw
          have hemb : (algebraMap ℚ ℂ) (Algebra.norm ℚ y) = ∏ ψ : K →+* ℂ, ψ y := by
            rw [Algebra.norm_eq_prod_embeddings ℚ ℂ y]
            exact (Fintype.prod_equiv (RingHom.equivRatAlgHom K ℂ) (fun ψ : K →+* ℂ ↦ ψ y)
              (fun σ : K →ₐ[ℚ] ℂ ↦ σ y) (fun ψ ↦ by simp [RingHom.equivRatAlgHom_apply])).symm
          rw [show ((Algebra.norm ℚ y : ℝ) : ℂ) = (algebraMap ℚ ℂ) (Algebra.norm ℚ y) by
              rw [eq_ratCast (algebraMap ℚ ℂ), Complex.ofReal_ratCast], hemb,
            ← Finset.prod_fiberwise (g := fun ψ : K →+* ℂ ↦ mk ψ) (f := fun ψ ↦ ψ y) Finset.univ]
          simp_rw [hperplace]
          rw [prod_eq_prod_mul_prod]
          congr 1
          · rw [Finset.prod_congr rfl (fun w _ ↦ by rw [dif_pos w.2]), Complex.ofReal_prod]
          · rw [Finset.prod_congr rfl (fun w _ ↦ by rw [dif_neg (not_isReal_iff_isComplex.mpr w.2)]),
              Complex.ofReal_prod]
        exact_mod_cast hcc
      have hsignProduct (f : {w : InfinitePlace K // IsReal w} → ℝ)
          (hpos' : ∀ w ∉ s, 0 < f w) (hneg' : ∀ w ∈ s, f w < 0) :
          (∏ w, f w) = (-1) ^ s.card * (∏ w, |f w|) := by
        rw [← Finset.prod_mul_prod_compl s f, ← Finset.prod_mul_prod_compl s (fun w ↦ |f w|),
          show ((-1 : ℝ)) ^ s.card = ∏ w ∈ s, (-1 : ℝ) by rw [Finset.prod_const],
          ← mul_assoc, ← Finset.prod_mul_distrib]
        congr 1
        · exact Finset.prod_congr rfl (fun w hw ↦ by
            rw [neg_one_mul, abs_of_neg (hneg' w hw), neg_neg])
        · exact Finset.prod_congr rfl (fun w hw ↦
            (abs_of_pos (hpos' w (Finset.mem_compl.mp hw))).symm)
      have hnorm : ((Algebra.norm ℤ gen).natAbs : ℤ) =
          (-1) ^ s.card * (Algebra.norm ℤ gen : ℤ) := by
        have hcoe : ((Algebra.norm ℤ gen : ℤ) : ℝ) = Algebra.norm ℚ (gen : K) := by
          rw [← Algebra.coe_norm_int]; push_cast; ring
        have hcpx : 0 ≤
            (∏ w : {w : InfinitePlace K // IsComplex w}, ‖(w.1.embedding) (gen : K)‖ ^ 2) :=
          Finset.prod_nonneg (fun w _ ↦ sq_nonneg _)
        have hmix : ∀ w : {w : InfinitePlace K // IsReal w},
            embedding_of_isReal w.2 (gen : K) = (mixedEmbedding K (gen : K)).1 w := fun w ↦ by
          rw [mixedEmbedding_apply_isReal]
        have hneg' : ∀ w ∈ s, embedding_of_isReal w.2 (gen : K) < 0 := fun w hw ↦ by
          rw [hmix]; exact hneg w hw
        have hpos' : ∀ w ∉ s, 0 < embedding_of_isReal w.2 (gen : K) := fun w hw ↦ by
          rw [hmix]; exact hpos w hw
        have hsign := hsignProduct
          (fun w : {w : InfinitePlace K // IsReal w} ↦ embedding_of_isReal w.2 (gen : K))
          hpos' hneg'
        have hnf := hnormProduct (gen : K)
        have habs : |((Algebra.norm ℚ (gen : K) : ℝ))|
            = (∏ w : {w : InfinitePlace K // IsReal w}, |embedding_of_isReal w.2 (gen : K)|) *
              (∏ w : {w : InfinitePlace K // IsComplex w}, ‖(w.1.embedding) (gen : K)‖ ^ 2) := by
          rw [hnf, abs_mul, abs_of_nonneg hcpx, Finset.abs_prod]
        have hkeyR : ((Algebra.norm ℚ (gen : K) : ℝ))
            = (-1) ^ s.card * |((Algebra.norm ℚ (gen : K) : ℝ))| := by
          rw [habs]
          conv_lhs => rw [hnf, hsign]
          ring
        have hZ' : (Algebra.norm ℤ gen : ℤ) =
            (-1) ^ s.card * ((Algebra.norm ℤ gen).natAbs : ℤ) := by
          have hZ : ((Algebra.norm ℤ gen : ℤ) : ℝ)
              = ((-1) ^ s.card * ((Algebra.norm ℤ gen).natAbs : ℤ) : ℤ) := by
            push_cast
            rw [hcoe]
            exact hkeyR
          exact_mod_cast hZ
        conv_rhs => rw [hZ']
        rw [← mul_assoc, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul]
      have hRes : intNorm (idealSetEquiv K J c).val = (Algebra.norm ℤ gen).natAbs := rfl
      have hcast : ((intNorm (idealSetEquiv K J c).val : ℕ) : ZMod m) =
          (((-1) ^ s.card * (Algebra.norm ℤ gen : ℤ) : ℤ) : ZMod m) := by
        rw [hRes, ← hnorm, Int.cast_natCast]
      rw [hcast]
    rw [hsign a horth, hsign a' horth']
    have hnormeq : ((Algebra.norm ℤ (preimageOfMemIntegerSet (idealSetMap K J a) : 𝓞 K) : ℤ) :
          ZMod m) =
        ((Algebra.norm ℤ (preimageOfMemIntegerSet (idealSetMap K J a') : 𝓞 K) : ℤ) : ZMod m) := by
      let x : 𝓞 K := (preimageOfMemIntegerSet (idealSetMap K J a) : 𝓞 K)
      let y : 𝓞 K := (preimageOfMemIntegerSet (idealSetMap K J a') : 𝓞 K)
      change ((Algebra.norm ℤ x : ℤ) : ZMod m) = ((Algebra.norm ℤ y : ℤ) : ZMod m)
      have hsub : mixedEmbedding K (x : K) - mixedEmbedding K (y : K) ∈
          (m : ℝ) • (mixedEmbedding.idealLattice K (FractionalIdeal.mk0 K J) : Set (mixedSpace K)) := by
        simp only [x, y, mixedEmbedding_preimageOfMemIntegerSet, idealSetMap_apply]
        exact sub_mem_nsmul_of_coord_eq m J T hT a.2.2 a'.2.2 (fun i ↦ by
          rw [congrFun hcos i, congrFun hcos' i])
      obtain ⟨v, hv, hveq⟩ := hsub
      simp only at hveq
      rw [SetLike.mem_coe, mem_idealLattice] at hv
      obtain ⟨yK, hyK, hyeq⟩ := hv
      simp only [FractionalIdeal.coe_mk0] at hyK
      obtain ⟨w, _, hweq⟩ := hyK
      rw [Algebra.linearMap_apply] at hweq
      have hkey : mixedEmbedding K ((x - y : 𝓞 K) : K)
          = mixedEmbedding K (((m : 𝓞 K) * w : 𝓞 K) : K) := by
        push_cast
        rw [map_sub, ← hveq, ← hyeq, ← hweq, Nat.cast_smul_eq_nsmul, ← map_nsmul]
        congr 1
        rw [nsmul_eq_mul]
      have hxy : x - y = (m : 𝓞 K) * w :=
        RingOfIntegers.coe_injective (K := K) ((mixedEmbedding_injective K) hkey)
      have hx : x = y + (m : 𝓞 K) * w := by linear_combination hxy
      rw [hx]
      let basis := Module.Free.chooseBasis ℤ (𝓞 K)
      rw [Algebra.norm_eq_matrix_det basis, Algebra.norm_eq_matrix_det basis,
        Int.cast_det, Int.cast_det]
      congr 1
      rw [show (m : 𝓞 K) * w = m • w from (nsmul_eq_mul _ _).symm, map_add, map_nsmul]
      ext i j
      simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, Int.cast_add]
      rw [show (((m • (Algebra.leftMulMatrix basis) w i j) : ℤ) : ZMod m) = 0 by
        rw [nsmul_eq_mul, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, zero_mul], add_zero]
    push_cast
    rw [hnormeq]
  set Φ : mixedSpace K ≃L[ℝ] (index K → ℝ) := (mixedEmbedding.stdBasis K).equivFunL with hΦ
  have hcard : Fintype.card (index K) = Module.finrank ℚ K := by
    rw [← Module.finrank_eq_card_basis (mixedEmbedding.stdBasis K), mixedEmbedding.finrank]
  have hconst : ∀ a a' : idealSet K J,
      Finset.univ.filter (fun w : {w : InfinitePlace K // IsReal w} ↦ (a : mixedSpace K).1 w < 0)
        = s →
      (fun i ↦ (round ((T.symm (Φ (a : mixedSpace K))) i) : ZMod m)) = k →
      Finset.univ.filter (fun w : {w : InfinitePlace K // IsReal w} ↦ (a' : mixedSpace K).1 w < 0)
        = s →
      (fun i ↦ (round ((T.symm (Φ (a' : mixedSpace K))) i) : ZMod m)) = k →
      (((intNorm (idealSetEquiv K J a).val : ZMod m) = (b : ZMod m)) ↔
        ((intNorm (idealSetEquiv K J a').val : ZMod m) = (b : ZMod m))) :=
    fun a a' h1 h2 h3 h4 ↦ residue_fibre_const_aux m b J T hT s k a a' h1 h2 h3 h4
  by_cases hQ : ∃ a : idealSet K J,
      (Finset.univ.filter (fun w : {w : InfinitePlace K // IsReal w} ↦
        (a : mixedSpace K).1 w < 0) = s) ∧
      ((fun i ↦ (round ((T.symm (Φ (a : mixedSpace K))) i) : ZMod m)) = k) ∧
      ((intNorm (idealSetEquiv K J a).val : ZMod m) = (b : ZMod m))
  · obtain ⟨a₀, horth₀, hcos₀, hres₀⟩ := hQ
    obtain ⟨cellC, hcell⟩ := exists_card_cell_sub_mul_rpow_le_explicit T m hm
      (Φ '' (normLeOne K)) (Φ.toContinuousLinearMap.lipschitz.isBounded_image (isBounded_normLeOne K))
      ((Φ.toHomeomorph.toMeasurableEquiv).measurableSet_image.mpr (measurableSet_normLeOne K))
      hcov (Sum.inl : {w : InfinitePlace K // IsReal w} → index K) s
    refine ⟨cellC, fun t ht ↦ ?_⟩
    rw [if_pos ⟨a₀, horth₀, hcos₀, hres₀⟩]
    have hfibre : Nat.card {a : idealSet K J //
        (mixedEmbedding.norm (a : mixedSpace K) ≤ t ^ Module.finrank ℚ K ∧
          ((intNorm (idealSetEquiv K J a).val : ZMod m) = (b : ZMod m))) ∧
        (Finset.univ.filter (fun w : {w : InfinitePlace K // IsReal w} ↦
          (a : mixedSpace K).1 w < 0) = s) ∧
        (fun i ↦ (round ((T.symm (Φ (a : mixedSpace K))) i) : ZMod m)) = k}
        = Nat.card {a : idealSet K J //
          mixedEmbedding.norm (a : mixedSpace K) ≤ t ^ Module.finrank ℚ K ∧
          (Finset.univ.filter (fun w : {w : InfinitePlace K // IsReal w} ↦
            (a : mixedSpace K).1 w < 0) = s) ∧
          (fun i ↦ (round ((T.symm (Φ (a : mixedSpace K))) i) : ZMod m)) = k} := by
      refine Nat.card_congr (Equiv.subtypeEquivRight fun a ↦ ?_)
      constructor
      · rintro ⟨⟨hn, _⟩, ho, hc⟩; exact ⟨hn, ho, hc⟩
      · rintro ⟨hn, ho, hc⟩
        exact ⟨⟨hn, (hconst a a₀ ho hc horth₀ hcos₀).mpr hres₀⟩, ho, hc⟩
    rw [hfibre, card_fibre_eq_card_cell m hm J T hT s k ht]
    have hpow1 : t ^ Module.finrank ℚ K = t ^ Fintype.card (index K) := by rw [hcard]
    have hpow2 : t ^ (Module.finrank ℚ K - 1 : ℕ) = t ^ (Fintype.card (index K) - 1 : ℕ) := by
      rw [hcard]
    rw [hpow1, hpow2]
    exact hcell (T (fun i ↦ ((k i).val : ℝ))) t ht
  · refine ⟨0, fun t ht ↦ ?_⟩
    rw [if_neg hQ]
    have hempty : IsEmpty {a : idealSet K J //
        (mixedEmbedding.norm (a : mixedSpace K) ≤ t ^ Module.finrank ℚ K ∧
          ((intNorm (idealSetEquiv K J a).val : ZMod m) = (b : ZMod m))) ∧
        (Finset.univ.filter (fun w : {w : InfinitePlace K // IsReal w} ↦
          (a : mixedSpace K).1 w < 0) = s) ∧
        (fun i ↦ (round ((T.symm (Φ (a : mixedSpace K))) i) : ZMod m)) = k} :=
      ⟨fun a ↦ hQ ⟨a.1, a.2.2.1, a.2.2.2, a.2.1.2⟩⟩
    simp [Nat.card_of_isEmpty]

end Chebotarev
