/- GID: D5/S3/Arith/PrimeIdeals/NormResidue/IdealCongruenceCountDvdCell
   generality: G
   mirror-B: D5/B/S3/Arith/PrimeIdeals/NormResidue/IdealCongruenceCountDvdCell
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A bJ-cone residue cell equals a translated sublattice cell count. -/
module

public import D5.S3.Arith.PrimeIdeals.NormResidue.IdealCongruenceCountTransfer

@[expose] public section

noncomputable section

namespace Chebotarev

open NumberField Set Submodule

open scoped NNReal nonZeroDivisors Pointwise

open Ideal NumberField.mixedEmbedding NumberField.mixedEmbedding.fundamentalCone
  NumberField.InfinitePlace Submodule Pointwise Classical in
/-- **Sublattice cell count.** Partition the `𝔟J`-cone points by the *`J`*-lattice chart `T`
(legitimate since ideal multiplication gives `idealSet K (𝔟J) ⊆ idealSet K J`): for `gcd(N(𝔟), m) = 1`,
the `𝔟J`-cone points of norm `≤ t^d`, sign-orthant `s`, `J`-coset `k`, biject (via `Φ`) with a
single `m·Λ_{𝔟J}`-coset `ξ' +ᵥ m·(T' '' ℤ^ι)` inside `t·(D₀ ∩ orthant_s)`. This is
the chart bijection restricted to sublattice membership, using finite quotient multiplication. -/
theorem exists_card_fibre_dvd_eq_card_cell {K : Type*} [Field K] [NumberField K]
    (m : ℕ) [NeZero m] (hm : (m : ℝ) ≠ 0) (J 𝔟 : (Ideal (𝓞 K))⁰)
    (hcop : (Ideal.absNorm (𝔟 : Ideal (𝓞 K))).Coprime m)
    (T T' : (index K → ℝ) ≃ₗ[ℝ] (index K → ℝ))
    (hT : T '' (span ℤ (Set.range (Pi.basisFun ℝ (index K))) : Set (index K → ℝ))
        = ((mixedEmbedding.stdBasis K).equivFunL '' (mixedEmbedding.idealLattice K
            (FractionalIdeal.mk0 K J)) : Set (index K → ℝ)))
    (hT' : T' '' (span ℤ (Set.range (Pi.basisFun ℝ (index K))) : Set (index K → ℝ))
        = ((mixedEmbedding.stdBasis K).equivFunL '' (mixedEmbedding.idealLattice K
            (FractionalIdeal.mk0 K (𝔟 * J))) : Set (index K → ℝ)))
    (s : Finset {w : InfinitePlace K // IsReal w}) (k : index K → ZMod m)
    {t : ℝ} (ht : 1 ≤ t) :
    ∃ ξ' : index K → ℝ, Nat.card {a : idealSet K (𝔟 * J) //
        mixedEmbedding.norm (a : mixedSpace K) ≤ t ^ Module.finrank ℚ K ∧
        (Finset.univ.filter (fun w : {w : InfinitePlace K // IsReal w} ↦
          (a : mixedSpace K).1 w < 0) = s) ∧
        (fun i ↦ (round ((T.symm ((mixedEmbedding.stdBasis K).equivFunL
          (a : mixedSpace K))) i) : ZMod m)) = k}
      = Nat.card ↑((ξ' +ᵥ ((m : ℝ) • (span ℤ (Set.range ((Pi.basisFun ℝ (index K)).map T'))
          : Set (index K → ℝ)))) ∩
        t • ((mixedEmbedding.stdBasis K).equivFunL '' (normLeOne K) ∩
          {y : index K → ℝ | (∀ w ∈ s, y (Sum.inl w) ≤ 0) ∧ (∀ w ∉ s, 0 ≤ y (Sum.inl w))})) := by
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
  have span_image_basisFun_eq (T : ((index K) → ℝ) ≃ₗ[ℝ] ((index K) → ℝ)) :
      (span ℤ (⇑T '' ↑(span ℤ (Set.range (Pi.basisFun ℝ (index K))))) : Submodule ℤ ((index K) → ℝ))
        = span ℤ (Set.range ((Pi.basisFun ℝ (index K)).map T)) := by
    have h1 : (⇑T '' ↑(span ℤ (Set.range (Pi.basisFun ℝ (index K)))) : Set ((index K) → ℝ))
        = ↑(span ℤ (⇑T '' Set.range (Pi.basisFun ℝ (index K))) : Submodule ℤ ((index K) → ℝ)) :=
      by simpa using congrArg SetLike.coe (Submodule.map_span
        (T.restrictScalars ℤ).toLinearMap (Set.range (Pi.basisFun ℝ (index K))))
    rw [h1, span_coe_eq_restrictScalars, Submodule.restrictScalars_self]
    congr 1
    rw [Module.Basis.coe_map, Set.range_comp]
  have relIndex_mul_ideal_eq_absNorm
      (J 𝔟 : (Ideal (𝓞 K))⁰) :
      ((𝔟 * J : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)).toAddSubgroup.relIndex
          ((J : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)).toAddSubgroup
        = Ideal.absNorm (𝔟 : Ideal (𝓞 K)) := by
    classical
    have hle : ((𝔟 * J : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)).toAddSubgroup
        ≤ ((J : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)).toAddSubgroup := by
      rw [Submodule.toAddSubgroup_le]
      push_cast
      exact Ideal.mul_le_right
    have key := AddSubgroup.relIndex_mul_index hle
    rw [← Ideal.absNorm_eq_index, ← Ideal.absNorm_eq_index] at key
    have hNbJ : Ideal.absNorm ((𝔟 * J : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K))
        = Ideal.absNorm (𝔟 : Ideal (𝓞 K)) * Ideal.absNorm (J : Ideal (𝓞 K)) := by
      rw [Submonoid.coe_mul, map_mul]
    rw [hNbJ] at key
    exact Nat.eq_of_mul_eq_mul_right (Ideal.absNorm_pos_of_nonZeroDivisors J) key
  have idealLattice_mul_le
      (J 𝔟 : (Ideal (𝓞 K))⁰) :
      NumberField.mixedEmbedding.idealLattice K (FractionalIdeal.mk0 K (𝔟 * J))
        ≤ NumberField.mixedEmbedding.idealLattice K (FractionalIdeal.mk0 K J) := by
    intro x hx
    rw [NumberField.mixedEmbedding.mem_idealLattice] at hx ⊢
    obtain ⟨y, hy, rfl⟩ := hx
    refine ⟨y, ?_, rfl⟩
    have hsub : (FractionalIdeal.mk0 K (𝔟 * J) : FractionalIdeal (𝓞 K)⁰ K)
        ≤ (FractionalIdeal.mk0 K J : FractionalIdeal (𝓞 K)⁰ K) := by
      simp only [FractionalIdeal.coe_mk0]
      rw [FractionalIdeal.coeIdeal_le_coeIdeal]
      exact Ideal.mul_le_right
    exact hsub hy
  have idealLattice_toAddSubgroup_eq
      (J : (Ideal (𝓞 K))⁰) :
      (NumberField.mixedEmbedding.idealLattice K (FractionalIdeal.mk0 K J)).toAddSubgroup
        = ((J : Ideal (𝓞 K)).toAddSubgroup).map
            (((NumberField.mixedEmbedding K).toAddMonoidHom).comp
              (algebraMap (𝓞 K) K).toAddMonoidHom) := by
    ext x
    simp only [Submodule.mem_toAddSubgroup, NumberField.mixedEmbedding.mem_idealLattice,
      AddSubgroup.mem_map, AddMonoidHom.coe_comp, Function.comp_apply,
      RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe]
    constructor
    · rintro ⟨y, hy, rfl⟩
      simp only [FractionalIdeal.coe_mk0] at hy
      obtain ⟨z, hz, rfl⟩ := hy
      exact ⟨z, hz, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      refine ⟨algebraMap (𝓞 K) K z, ?_, rfl⟩
      simp only [FractionalIdeal.coe_mk0]
      exact ⟨z, hz, rfl⟩
  have relIndex_idealLattice_eq_absNorm
      (J 𝔟 : (Ideal (𝓞 K))⁰) :
      (NumberField.mixedEmbedding.idealLattice K
          (FractionalIdeal.mk0 K (𝔟 * J))).toAddSubgroup.relIndex
          (NumberField.mixedEmbedding.idealLattice K (FractionalIdeal.mk0 K J)).toAddSubgroup
        = Ideal.absNorm (𝔟 : Ideal (𝓞 K)) := by
    have hinj : Function.Injective
        (((NumberField.mixedEmbedding K).toAddMonoidHom).comp
          (algebraMap (𝓞 K) K).toAddMonoidHom) := by
      rw [AddMonoidHom.coe_comp]
      exact (NumberField.mixedEmbedding_injective K).comp (IsFractionRing.injective (𝓞 K) K)
    rw [idealLattice_toAddSubgroup_eq, idealLattice_toAddSubgroup_eq,
      AddSubgroup.relIndex_map_map_of_injective _ _ hinj, relIndex_mul_ideal_eq_absNorm]
  have chart_lattice_eq_map (J : (Ideal (𝓞 K))⁰)
      (T : (index K → ℝ) ≃ₗ[ℝ] (index K → ℝ))
      (hT : ⇑T '' ↑(span ℤ (Set.range (Pi.basisFun ℝ (index K))))
          = ((mixedEmbedding.stdBasis K).equivFunL '' (mixedEmbedding.idealLattice K
              (FractionalIdeal.mk0 K J)) : Set (index K → ℝ))) :
      (span ℤ (Set.range ((Pi.basisFun ℝ (index K)).map T)) : Submodule ℤ (index K → ℝ))
        = (mixedEmbedding.idealLattice K (FractionalIdeal.mk0 K J)).map
            (((mixedEmbedding.stdBasis K).equivFunL :
              mixedSpace K ≃ₗ[ℝ] (index K → ℝ)).restrictScalars ℤ).toLinearMap := by
    rw [← span_image_basisFun_eq, hT]
    have : ((mixedEmbedding.stdBasis K).equivFunL ''
          ((mixedEmbedding.idealLattice K (FractionalIdeal.mk0 K J)) : Set (mixedSpace K))
          : Set (index K → ℝ))
        = ↑((mixedEmbedding.idealLattice K (FractionalIdeal.mk0 K J)).map
            (((mixedEmbedding.stdBasis K).equivFunL :
              mixedSpace K ≃ₗ[ℝ] (index K → ℝ)).restrictScalars ℤ).toLinearMap) := by
      rw [Submodule.map_coe]
      rfl
    rw [this, span_coe_eq_restrictScalars, Submodule.restrictScalars_self]
  have chart_sublattice_le (J 𝔟 : (Ideal (𝓞 K))⁰)
      (T T' : (index K → ℝ) ≃ₗ[ℝ] (index K → ℝ))
      (hT : ⇑T '' ↑(span ℤ (Set.range (Pi.basisFun ℝ (index K))))
          = ((mixedEmbedding.stdBasis K).equivFunL '' (mixedEmbedding.idealLattice K
              (FractionalIdeal.mk0 K J)) : Set (index K → ℝ)))
      (hT' : ⇑T' '' ↑(span ℤ (Set.range (Pi.basisFun ℝ (index K))))
          = ((mixedEmbedding.stdBasis K).equivFunL '' (mixedEmbedding.idealLattice K
              (FractionalIdeal.mk0 K (𝔟 * J))) : Set (index K → ℝ))) :
      (span ℤ (Set.range ((Pi.basisFun ℝ (index K)).map T')) : Submodule ℤ (index K → ℝ))
        ≤ span ℤ (Set.range ((Pi.basisFun ℝ (index K)).map T)) := by
    rw [chart_lattice_eq_map J T hT, chart_lattice_eq_map (𝔟 * J) T' hT']
    exact Submodule.map_mono (idealLattice_mul_le J 𝔟)
  have relIndex_chart_eq_absNorm
      (J 𝔟 : (Ideal (𝓞 K))⁰)
      (T T' : (index K → ℝ) ≃ₗ[ℝ] (index K → ℝ))
      (hT : ⇑T '' ↑(span ℤ (Set.range (Pi.basisFun ℝ (index K))))
          = ((mixedEmbedding.stdBasis K).equivFunL '' (mixedEmbedding.idealLattice K
              (FractionalIdeal.mk0 K J)) : Set (index K → ℝ)))
      (hT' : ⇑T' '' ↑(span ℤ (Set.range (Pi.basisFun ℝ (index K))))
          = ((mixedEmbedding.stdBasis K).equivFunL '' (mixedEmbedding.idealLattice K
              (FractionalIdeal.mk0 K (𝔟 * J))) : Set (index K → ℝ))) :
      (span ℤ (Set.range ((Pi.basisFun ℝ (index K)).map T'))).toAddSubgroup.relIndex
          (span ℤ (Set.range ((Pi.basisFun ℝ (index K)).map T))).toAddSubgroup
        = Ideal.absNorm (𝔟 : Ideal (𝓞 K)) := by
    have hΦinj : Function.Injective
        (((mixedEmbedding.stdBasis K).equivFunL :
          mixedSpace K ≃ₗ[ℝ] (index K → ℝ)).restrictScalars ℤ).toLinearMap :=
      ((mixedEmbedding.stdBasis K).equivFunL : mixedSpace K ≃ₗ[ℝ] (index K → ℝ)).injective
    rw [chart_lattice_eq_map J T hT, chart_lattice_eq_map (𝔟 * J) T' hT',
      Submodule.map_toAddSubgroup, Submodule.map_toAddSubgroup,
      AddSubgroup.relIndex_map_map_of_injective _ _ hΦinj]
    exact relIndex_idealLattice_eq_absNorm J 𝔟
  classical
  have hsmul (T₀ : (index K → ℝ) ≃ₗ[ℝ] (index K → ℝ)) :
      (((LinearEquiv.smulOfNeZero ℝ (index K → ℝ) (m : ℝ) hm).trans T₀) ''
        (span ℤ (Set.range (Pi.basisFun ℝ (index K))) : Set (index K → ℝ))) =
        ((m : ℝ) • (span ℤ (Set.range ((Pi.basisFun ℝ (index K)).map T₀)) :
          Set (index K → ℝ))) := by
    have hLeq : (span ℤ (Set.range ((Pi.basisFun ℝ (index K)).map T₀)) :
        Set (index K → ℝ)) =
        T₀ '' (span ℤ (Set.range (Pi.basisFun ℝ (index K))) : Set (index K → ℝ)) := by
      have hmap : T₀ '' (span ℤ (Set.range (Pi.basisFun ℝ (index K))) : Set (index K → ℝ)) =
          (span ℤ (T₀ '' Set.range (Pi.basisFun ℝ (index K))) : Set (index K → ℝ)) := by
        simpa using congrArg SetLike.coe (Submodule.map_span
          (T₀.restrictScalars ℤ).toLinearMap (Set.range (Pi.basisFun ℝ (index K))))
      rw [hmap, Module.Basis.coe_map, Set.range_comp]
    ext z
    simp only [LinearEquiv.trans_apply, LinearEquiv.smulOfNeZero_apply, Set.mem_image,
      Set.mem_smul_set, SetLike.mem_coe, hLeq]
    constructor
    · rintro ⟨v, hv, rfl⟩; exact ⟨T₀ v, ⟨v, hv, rfl⟩, by rw [map_smul]⟩
    · rintro ⟨w, ⟨v, hv, rfl⟩, rfl⟩; exact ⟨v, hv, by rw [map_smul]⟩
  set Φ : mixedSpace K ≃L[ℝ] (index K → ℝ) := (mixedEmbedding.stdBasis K).equivFunL with hΦ
  set d := Module.finrank ℚ K with hd
  set Os : Set (index K → ℝ) :=
    {y : index K → ℝ | (∀ w ∈ s, y (Sum.inl w) ≤ 0) ∧ (∀ w ∉ s, 0 ≤ y (Sum.inl w))} with hOs
  set L : Submodule ℤ (index K → ℝ) := span ℤ (Set.range ((Pi.basisFun ℝ (index K)).map T))
    with hLdef
  set L' : Submodule ℤ (index K → ℝ) := span ℤ (Set.range ((Pi.basisFun ℝ (index K)).map T'))
    with hL'def
  have hrel : L'.toAddSubgroup.relIndex L.toAddSubgroup = Ideal.absNorm (𝔟 : Ideal (𝓞 K)) :=
    relIndex_chart_eq_absNorm J 𝔟 T T' hT hT'
  have hNB : 0 < Ideal.absNorm (𝔟 : Ideal (𝓞 K)) := absNorm_pos_of_nonZeroDivisors 𝔟
  haveI hfin : Finite (L.toAddSubgroup ⧸ L'.toAddSubgroup.addSubgroupOf L.toAddSubgroup) := by
    rw [← AddSubgroup.index_ne_zero_iff_finite]
    rw [show (L'.toAddSubgroup.addSubgroupOf L.toAddSubgroup).index
        = L'.toAddSubgroup.relIndex L.toAddSubgroup from rfl, hrel]
    exact hNB.ne'
  have hcopC : (Nat.card (L.toAddSubgroup ⧸
      L'.toAddSubgroup.addSubgroupOf L.toAddSubgroup)).Coprime m := by
    rw [show Nat.card (L.toAddSubgroup ⧸ L'.toAddSubgroup.addSubgroupOf L.toAddSubgroup)
        = L'.toAddSubgroup.relIndex L.toAddSubgroup from rfl, hrel]
    exact hcop
  have hLL' : L' ≤ L := chart_sublattice_le J 𝔟 T T' hT hT'
  have hmap (T₀ : (index K → ℝ) ≃ₗ[ℝ] (index K → ℝ)) :
      T₀ '' (span ℤ (Set.range (Pi.basisFun ℝ (index K))) : Set (index K → ℝ)) =
      (span ℤ (T₀ '' Set.range (Pi.basisFun ℝ (index K))) : Set (index K → ℝ)) := by
    simpa using congrArg SetLike.coe (Submodule.map_span
      (T₀.restrictScalars ℤ).toLinearMap (Set.range (Pi.basisFun ℝ (index K))))
  have hspan (v : index K → ℝ) :
      v ∈ span ℤ (Set.range (Pi.basisFun ℝ (index K))) ↔
        ∀ i, ∃ n : ℤ, v i = (n : ℝ) := by
    letI : Fintype (index K) := Fintype.ofFinite _
    simp only [(Pi.basisFun ℝ (index K)).mem_span_iff_repr_mem ℤ v, Pi.basisFun_repr,
      Set.mem_range, eq_intCast, eq_comm]
  have hξkL : (T (fun i ↦ ((k i).val : ℝ)) : index K → ℝ) ∈ L := by
    have hv : (fun i ↦ ((k i).val : ℝ)) ∈ span ℤ (Set.range (Pi.basisFun ℝ (index K))) := by
      rw [hspan]
      exact fun i ↦ ⟨((k i).val : ℤ), by push_cast; rfl⟩
    have hmem : (T (fun i ↦ ((k i).val : ℝ)) : index K → ℝ)
        ∈ ⇑T '' ↑(span ℤ (Set.range (Pi.basisFun ℝ (index K)))) := ⟨_, hv, rfl⟩
    rw [hmap T] at hmem
    rw [hLdef]
    rwa [← Set.range_comp, ← Module.Basis.coe_map] at hmem
  let ξ : index K → ℝ := T (fun i ↦ ((k i).val : ℝ))
  have hcrt : ∃ ξ' : index K → ℝ, ξ' ∈ L' ∧
      {a : index K → ℝ | a ∈ L' ∧ a ∈ ξ +ᵥ ((m : ℝ) • (L : Set (index K → ℝ)))}
        = (ξ' +ᵥ ((m : ℝ) • (L' : Set (index K → ℝ)))) := by
    have hmsmul : ∀ (M : Submodule ℤ (index K → ℝ)), ((m : ℝ) • (M : Set (index K → ℝ)))
        = {z | ∃ x ∈ M, z = m • x} := by
      intro M
      ext z
      simp only [Set.mem_smul_set, SetLike.mem_coe, Set.mem_setOf_eq]
      exact ⟨fun ⟨x, hx, h⟩ ↦ ⟨x, hx, by rw [← h, Nat.cast_smul_eq_nsmul]⟩,
        fun ⟨x, hx, h⟩ ↦ ⟨x, hx, by rw [h, Nat.cast_smul_eq_nsmul]⟩⟩
    have hbij := hcopC.nsmul_right_bijective
      (G := L.toAddSubgroup ⧸ L'.toAddSubgroup.addSubgroupOf L.toAddSubgroup)
    have hsurj : ∃ a' ∈ L'.toAddSubgroup, ∃ a ∈ L.toAddSubgroup, ξ = a' + m • a := by
      obtain ⟨q, hq⟩ := hbij.2 (QuotientAddGroup.mk (⟨ξ, hξkL⟩ : L.toAddSubgroup))
      obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective q
      simp only at hq
      rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf] at hq
      exact ⟨(-(m • (a : index K → ℝ)) + ξ), by simpa using hq, (a : index K → ℝ), a.2, by abel⟩
    obtain ⟨ξ', hξ'L', a₀, ha₀L, hξeq⟩ := hsurj
    refine ⟨ξ', hξ'L', ?_⟩
    have hinj2 : ∀ a : index K → ℝ, a ∈ L → m • a ∈ L' → a ∈ L' := by
      intro a ha hma
      have hzero : m • (QuotientAddGroup.mk (⟨a, ha⟩ : L.toAddSubgroup)
          : L.toAddSubgroup ⧸ L'.toAddSubgroup.addSubgroupOf L.toAddSubgroup)
          = (0 : L.toAddSubgroup ⧸ L'.toAddSubgroup.addSubgroupOf L.toAddSubgroup) := by
        rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
        simpa using hma
      have hq0 : (QuotientAddGroup.mk (⟨a, ha⟩ : L.toAddSubgroup)
          : L.toAddSubgroup ⧸ L'.toAddSubgroup.addSubgroupOf L.toAddSubgroup) = 0 :=
        hbij.1 (by simp only [hzero, smul_zero])
      rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf] at hq0
      simpa using hq0
    ext a
    simp only [Set.mem_setOf_eq, hmsmul, Set.mem_vadd_set, Set.mem_setOf_eq, vadd_eq_add]
    constructor
    · rintro ⟨haL', w, ⟨x, hxL, rfl⟩, hweq⟩
      rw [hξeq] at hweq
      have hmem : m • (a₀ + x) = a - ξ' := by
        rw [smul_add, ← hweq]
        abel
      refine ⟨a - ξ', ⟨a₀ + x, ?_, ?_⟩, by abel⟩
      · exact hinj2 _ (L.add_mem ha₀L hxL) (by rw [hmem]; exact L'.sub_mem haL' hξ'L')
      · rw [hmem]
    · rintro ⟨w, ⟨y, hyL', rfl⟩, rfl⟩
      refine ⟨L'.add_mem hξ'L' (L'.nsmul_mem hyL' m), m • (y - a₀),
        ⟨y - a₀, L.sub_mem (hLL' hyL') ha₀L, rfl⟩, ?_⟩
      rw [hξeq, smul_sub]
      abel
  obtain ⟨ξ', hξ'L', hcoset⟩ := hcrt
  refine ⟨ξ', ?_⟩
  have hΦΛ' : ((mixedEmbedding.stdBasis K).equivFunL '' (mixedEmbedding.idealLattice K
      (FractionalIdeal.mk0 K (𝔟 * J))) : Set (index K → ℝ)) = ↑L' := by
    rw [hL'def, ← hT', hmap T', Module.Basis.coe_map, Set.range_comp]
  have hincl : idealSet K (𝔟 * J) ⊆ idealSet K J := by
    intro x hx
    exact ⟨hx.1, idealLattice_mul_le J 𝔟 hx.2⟩
  have ht0 : t ≠ 0 := (lt_of_lt_of_le one_pos ht).ne'
  have hreg : ∀ x : mixedSpace K, x ∈ idealSet K J →
      (Φ x ∈ t • ((mixedEmbedding.stdBasis K).equivFunL '' (normLeOne K) ∩ Os) ↔
        (mixedEmbedding.norm x ≤ t ^ d ∧
          Finset.univ.filter (fun w : {w : InfinitePlace K // IsReal w} ↦ x.1 w < 0) = s)) :=
    fun x hx ↦ mem_smul_cell_iff_norm_le_and_filter_eq J s ht hx
  set f : {a : idealSet K (𝔟 * J) //
      mixedEmbedding.norm (a : mixedSpace K) ≤ t ^ d ∧
      (Finset.univ.filter (fun w : {w : InfinitePlace K // IsReal w} ↦
        (a : mixedSpace K).1 w < 0) = s) ∧
      (fun i ↦ (round ((T.symm (Φ (a : mixedSpace K))) i) : ZMod m)) = k} → (index K → ℝ) :=
    fun a ↦ Φ (a.1 : mixedSpace K) with hf
  have hfinj : Function.Injective f := fun _ _ h ↦ Subtype.ext (Subtype.ext (Φ.injective h))
  have hset : Set.range f =
      ((ξ' +ᵥ ((m : ℝ) • (L' : Set (index K → ℝ)))) ∩
        t • ((mixedEmbedding.stdBasis K).equivFunL '' (normLeOne K) ∩ Os)) := by
    ext y
    simp only [hf, Set.mem_range, Subtype.exists, Set.mem_inter_iff]
    constructor
    · rintro ⟨a, ha, hP, rfl⟩
      have haJ : a ∈ idealSet K J := hincl ha
      have haL' : Φ a ∈ L' := by
        have hmm : Φ a ∈ ((mixedEmbedding.stdBasis K).equivFunL '' (mixedEmbedding.idealLattice K
            (FractionalIdeal.mk0 K (𝔟 * J))) : Set (index K → ℝ)) := ⟨a, ha.2, rfl⟩
        rwa [hΦΛ'] at hmm
      have hcosetmem : Φ a ∈ (T (fun i ↦ ((k i).val : ℝ)) : index K → ℝ) +ᵥ
          (((LinearEquiv.smulOfNeZero ℝ (index K → ℝ) (m : ℝ) hm).trans T) ''
            (span ℤ (Set.range (Pi.basisFun ℝ (index K))) : Set (index K → ℝ))) :=
        (mem_coset_iff_cos_eq m hm J T hT k haJ.2).mpr (fun i ↦ congrFun hP.2.2 i)
      have hΦacoset : Φ a ∈ ξ' +ᵥ ((m : ℝ) • (L' : Set (index K → ℝ))) := by
        have hmemL : Φ a ∈ {b | b ∈ L' ∧ b ∈ (T (fun i ↦ ((k i).val : ℝ)) : index K → ℝ) +ᵥ
            ((m : ℝ) • (L : Set (index K → ℝ)))} := by
          refine ⟨haL', ?_⟩
          rw [hLdef, ← hsmul T]
          exact hcosetmem
        rwa [hcoset] at hmemL
      exact ⟨hΦacoset, (hreg a haJ).mpr ⟨hP.1, hP.2.1⟩⟩
    · rintro ⟨hcosetmem, hregion⟩
      have hyL' : y ∈ L' := by rw [hcoset.symm] at hcosetmem; exact hcosetmem.1
      have hyΛ' : y ∈ ((mixedEmbedding.stdBasis K).equivFunL '' (mixedEmbedding.idealLattice K
          (FractionalIdeal.mk0 K (𝔟 * J))) : Set (index K → ℝ)) := by rw [hΦΛ']; exact hyL'
      obtain ⟨z, hzlat, hzeq⟩ := hyΛ'
      have hzcone : z ∈ idealSet K (𝔟 * J) := by
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
      have hzJ : z ∈ idealSet K J := hincl hzcone
      have hcosetz : Φ z ∈ (T (fun i ↦ ((k i).val : ℝ)) : index K → ℝ) +ᵥ
          (((LinearEquiv.smulOfNeZero ℝ (index K → ℝ) (m : ℝ) hm).trans T) ''
            (span ℤ (Set.range (Pi.basisFun ℝ (index K))) : Set (index K → ℝ))) := by
        have hymem : y ∈ {a | a ∈ L' ∧ a ∈ (T (fun i ↦ ((k i).val : ℝ)) : index K → ℝ) +ᵥ
            ((m : ℝ) • (L : Set (index K → ℝ)))} := by rw [hcoset]; exact hcosetmem
        rw [hsmul T, ← hLdef, show (Φ z : index K → ℝ) = y from hzeq]
        exact hymem.2
      refine ⟨z, hzcone, ⟨?_, ?_, ?_⟩, hzeq⟩
      · exact ((hreg z hzJ).mp (by rw [hzeq]; exact hregion)).1
      · exact ((hreg z hzJ).mp (by rw [hzeq]; exact hregion)).2
      · funext i
        exact (mem_coset_iff_cos_eq m hm J T hT k hzJ.2).mp hcosetz i
  rw [← Nat.card_range_of_injective hfinj, hset]

end Chebotarev
