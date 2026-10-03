/- GID: D5/S3/Arith/PrimeIdeals/NormResidue/IdealCongruenceCountDvdFibre
   generality: G
   mirror-B: D5/B/S3/Arith/PrimeIdeals/NormResidue/IdealCongruenceCountDvdFibre
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Ideal-set cones for J and bJ share a scaled leading count constant. -/
module

public import D5.S3.Arith.PrimeIdeals.NormResidue.IdealCongruenceCountDvdCell

@[expose] public section

noncomputable section

namespace Chebotarev

open NumberField Set Submodule

open scoped NNReal nonZeroDivisors Pointwise

/-! ### Final assembly of (L2): the dvd-density is `κfull/N(𝔟)`

The four stages below assemble the geometry-of-numbers kernel
`cardNormLeResidueClassDvd_div_density` from the cell chain and the `𝔟J`-sublattice cruxes.
* **A** (`exists_card_cell_sub_mul_rpow_le_explicit`): the per-cell workhorse estimate with its
  leading constant `vol(Ds)/|det ((m·)∘T)|` made explicit.
* **B** (`exists_card_idealSet_residue_real_le_dvd`): the summed `𝔟J`-cone-point residue count
  with leading constant `κ_J/N(𝔟)`, `κ_J` the `J`-cone-point constant assembled from the per-cell
  constants of `exists_card_residue_fibre_sub_mul_rpow_le_explicit`. Per `(orthant, J-coset)` cell,
  case on whether the `J`-cell carries the residue `b`: if so the `𝔟J`-residue filter is vacuous
  (constancy on the `J`-coset), so the count is the gateway full cell count
  `vol(Ds)/|det ((m·)∘T')|·t^d`; if not, every `𝔟J`-point is a `J`-point of the wrong residue, so
  the count is `0`. The det ratio `|det ((m·)∘T')| = N(𝔟)·|det ((m·)∘T)|` makes the per-cell ratio
  exactly `N(𝔟)`.
* **C** (`card_principalize_dvd`, principalization): the `𝔟J`-cone count is the
  `𝔟`-and-`J`-divisible principal count (coprime `J,𝔟` ⟹ `J ∣ I ∧ 𝔟 ∣ I ⟺ 𝔟J ∣ I`), which through
  the ordinary principalization correspondence is
  `cardNormLeResidueClassDvd`.
* **D**: convergence of the normalized error + `tendsto_nhds_unique` against `hκfull`. -/

open Ideal NumberField.mixedEmbedding NumberField.mixedEmbedding.fundamentalCone
  NumberField.InfinitePlace Submodule Pointwise Classical in
set_option maxHeartbeats 2000000 in
/-- **(STAGE B, fibre level) Per-(orthant, coset) effective `𝔟J`-residue count.** The same cell
`(s, k)` of `idealSet K (𝔟J)`, filtered by residue `b`, has leading constant `L_J/N(𝔟)` where `L_J`
is the explicit `J`-cell constant of `exists_card_residue_fibre_sub_mul_rpow_le_explicit`. Case on
whether the `J`-cell carries residue `b`: if so the `𝔟J`-residue filter is vacuous (constancy on the
`J`-coset, using `idealLattice_mul_le` and norm congruence), so the count is the gateway full
cell count `exists_card_fibre_dvd_eq_card_cell` `≈ vol(Ds)/|det ((m·)∘T')|·t^d`, and the det ratio
the determinant product law gives `vol/|det ((m·)∘T')| = (vol/|det ((m·)∘T)|)/N(𝔟)`; if not, every
`𝔟J`-point is a `J`-point of the wrong residue, so the count is `0 = 0/N(𝔟)`. -/
theorem exists_card_fibre_dvd_residue_sub_mul_rpow_le {K : Type*} [Field K] [NumberField K]
    (m : ℕ) [NeZero m] (hm : (m : ℝ) ≠ 0) (b : ℕ) (J 𝔟 : (Ideal (𝓞 K))⁰)
    (hcop : (Ideal.absNorm (𝔟 : Ideal (𝓞 K))).Coprime m)
    (T T' : (index K → ℝ) ≃ₗ[ℝ] (index K → ℝ))
    (hT : T '' (span ℤ (Set.range (Pi.basisFun ℝ (index K))) : Set (index K → ℝ))
        = ((mixedEmbedding.stdBasis K).equivFunL '' (mixedEmbedding.idealLattice K
            (FractionalIdeal.mk0 K J)) : Set (index K → ℝ)))
    (hT' : T' '' (span ℤ (Set.range (Pi.basisFun ℝ (index K))) : Set (index K → ℝ))
        = ((mixedEmbedding.stdBasis K).equivFunL '' (mixedEmbedding.idealLattice K
            (FractionalIdeal.mk0 K (𝔟 * J))) : Set (index K → ℝ)))
    (hcov : ∃ (mc : ℕ) (M : ℝ≥0) (φ : Fin mc → (Fin (Fintype.card (index K) - 1) → ℝ) →
        (index K → ℝ)), (∀ j, LipschitzWith M (φ j)) ∧
      frontier ((mixedEmbedding.stdBasis K).equivFunL '' (normLeOne K)) ⊆ ⋃ j, φ j '' Set.Icc 0 1)
    (s : Finset {w : InfinitePlace K // IsReal w}) (k : index K → ZMod m) :
    ∃ C : ℝ, ∀ t : ℝ, 1 ≤ t →
      |(Nat.card {a : idealSet K (𝔟 * J) //
          (mixedEmbedding.norm (a : mixedSpace K) ≤ t ^ Module.finrank ℚ K ∧
            ((intNorm (idealSetEquiv K (𝔟 * J) a).val : ZMod m) = (b : ZMod m))) ∧
          (Finset.univ.filter (fun w : {w : InfinitePlace K // IsReal w} ↦
            (a : mixedSpace K).1 w < 0) = s) ∧
          (fun i ↦ (round ((T.symm ((mixedEmbedding.stdBasis K).equivFunL
            (a : mixedSpace K))) i) : ZMod m)) = k} : ℝ)
          - ((if (∃ a : idealSet K J,
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
            else 0) / (Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ℝ)) * t ^ Module.finrank ℚ K|
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
  have covolume_image_basisFun_eq_abs_det
      (T : ((index K) → ℝ) ≃ₗ[ℝ] ((index K) → ℝ)) :
      ZLattice.covolume (span ℤ (Set.range ((Pi.basisFun ℝ (index K)).map T)) : Submodule ℤ ((index K) → ℝ))
        = |LinearMap.det (T : ((index K) → ℝ) →ₗ[ℝ] ((index K) → ℝ))| := by
    classical
    have hli : LinearIndependent ℤ ⇑((Pi.basisFun ℝ (index K)).map T) :=
      ((Pi.basisFun ℝ (index K)).map T).linearIndependent.restrict_scalars (by
        simpa using (algebraMap ℤ ℝ).injective_int)
    set b : Module.Basis (index K) ℤ (span ℤ (Set.range ((Pi.basisFun ℝ (index K)).map T)) : Submodule ℤ ((index K) → ℝ)) :=
      Module.Basis.span hli with hbdef
    rw [ZLattice.covolume_eq_det _ b, show ((↑) ∘ b) = ⇑((Pi.basisFun ℝ (index K)).map T) from
        funext fun i ↦ by rw [Function.comp_apply, hbdef, Module.Basis.coe_span_apply],
      ← LinearMap.det_toMatrix (Pi.basisFun ℝ (index K)) (T : ((index K) → ℝ) →ₗ[ℝ] ((index K) → ℝ)),
      ← Matrix.det_transpose (LinearMap.toMatrix (Pi.basisFun ℝ (index K)) (Pi.basisFun ℝ (index K))
        (T : ((index K) → ℝ) →ₗ[ℝ] ((index K) → ℝ)))]
    have hmatrix :
        Matrix.of ⇑((Pi.basisFun ℝ (index K)).map T) =
          (LinearMap.toMatrix (Pi.basisFun ℝ (index K)) (Pi.basisFun ℝ (index K))
            (T : ((index K) → ℝ) →ₗ[ℝ] ((index K) → ℝ))).transpose := by
      ext i j
      simp only [Matrix.of_apply, Module.Basis.map_apply, Matrix.transpose_apply,
        LinearMap.toMatrix_apply, Pi.basisFun_repr]
      rfl
    simp only [hmatrix]
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
  have abs_det_latticeEquiv_mul
      (J 𝔟 : (Ideal (𝓞 K))⁰)
      (T T' : (index K → ℝ) ≃ₗ[ℝ] (index K → ℝ))
      (hT : ⇑T '' ↑(span ℤ (Set.range (Pi.basisFun ℝ (index K))))
          = ((mixedEmbedding.stdBasis K).equivFunL '' (mixedEmbedding.idealLattice K
              (FractionalIdeal.mk0 K J)) : Set (index K → ℝ)))
      (hT' : ⇑T' '' ↑(span ℤ (Set.range (Pi.basisFun ℝ (index K))))
          = ((mixedEmbedding.stdBasis K).equivFunL '' (mixedEmbedding.idealLattice K
              (FractionalIdeal.mk0 K (𝔟 * J))) : Set (index K → ℝ))) :
      |LinearMap.det (T' : (index K → ℝ) →ₗ[ℝ] (index K → ℝ))|
        = (Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ℝ)
          * |LinearMap.det (T : (index K → ℝ) →ₗ[ℝ] (index K → ℝ))| := by
    classical
    set L : Submodule ℤ (index K → ℝ) := span ℤ (Set.range ((Pi.basisFun ℝ (index K)).map T))
    set L' : Submodule ℤ (index K → ℝ) := span ℤ (Set.range ((Pi.basisFun ℝ (index K)).map T'))
    have hcov := ZLattice.covolume_div_covolume_eq_relIndex L' L
      (chart_sublattice_le J 𝔟 T T' hT hT')
    rw [relIndex_chart_eq_absNorm J 𝔟 T T' hT hT',
      covolume_image_basisFun_eq_abs_det, covolume_image_basisFun_eq_abs_det] at hcov
    have hdetJ : (0 : ℝ) < |LinearMap.det (T : (index K → ℝ) →ₗ[ℝ] (index K → ℝ))| :=
      abs_pos.mpr (LinearEquiv.isUnit_det' T).ne_zero
    field_simp at hcov
    linarith [hcov]
  have hsmul :
      (((LinearEquiv.smulOfNeZero ℝ (index K → ℝ) (m : ℝ) hm).trans T') ''
        (span ℤ (Set.range (Pi.basisFun ℝ (index K))) : Set (index K → ℝ))) =
        ((m : ℝ) • (span ℤ (Set.range ((Pi.basisFun ℝ (index K)).map T')) :
          Set (index K → ℝ))) := by
    have hLeq : (span ℤ (Set.range ((Pi.basisFun ℝ (index K)).map T')) :
        Set (index K → ℝ)) =
        T' '' (span ℤ (Set.range (Pi.basisFun ℝ (index K))) : Set (index K → ℝ)) := by
      have hmap : T' '' (span ℤ (Set.range (Pi.basisFun ℝ (index K))) : Set (index K → ℝ)) =
          (span ℤ (T' '' Set.range (Pi.basisFun ℝ (index K))) : Set (index K → ℝ)) := by
        simpa using congrArg SetLike.coe (Submodule.map_span
          (T'.restrictScalars ℤ).toLinearMap (Set.range (Pi.basisFun ℝ (index K))))
      rw [hmap, Module.Basis.coe_map, Set.range_comp]
    ext z
    simp only [LinearEquiv.trans_apply, LinearEquiv.smulOfNeZero_apply, Set.mem_image,
      Set.mem_smul_set, SetLike.mem_coe, hLeq]
    constructor
    · rintro ⟨v, hv, rfl⟩; exact ⟨T' v, ⟨v, hv, rfl⟩, by rw [map_smul]⟩
    · rintro ⟨w, ⟨v, hv, rfl⟩, rfl⟩; exact ⟨v, hv, by rw [map_smul]⟩
  set Φ : mixedSpace K ≃L[ℝ] (index K → ℝ) := (mixedEmbedding.stdBasis K).equivFunL with hΦ
  set d := Module.finrank ℚ K with hd
  set Os : Set (index K → ℝ) :=
    {y : index K → ℝ | (∀ w ∈ s, y (Sum.inl w) ≤ 0) ∧ (∀ w ∉ s, 0 ≤ y (Sum.inl w))} with hOs
  set NB : ℕ := Ideal.absNorm (𝔟 : Ideal (𝓞 K)) with hNBdef
  have hcard : Fintype.card (index K) = d := by
    rw [← Module.finrank_eq_card_basis (mixedEmbedding.stdBasis K), mixedEmbedding.finrank]
  obtain ⟨cellC', hcell'⟩ := exists_card_cell_sub_mul_rpow_le_explicit T' m hm
    (Φ '' (normLeOne K)) (Φ.toContinuousLinearMap.lipschitz.isBounded_image (isBounded_normLeOne K))
    ((Φ.toHomeomorph.toMeasurableEquiv).measurableSet_image.mpr (measurableSet_normLeOne K))
    hcov (Sum.inl : {w : InfinitePlace K // IsReal w} → index K) s
  have hdetratio : MeasureTheory.volume.real (Φ '' (normLeOne K) ∩ Os)
        / |LinearMap.det (((LinearEquiv.smulOfNeZero ℝ (index K → ℝ) (m : ℝ) hm).trans T'
          : (index K → ℝ) ≃ₗ[ℝ] (index K → ℝ)) : (index K → ℝ) →ₗ[ℝ] (index K → ℝ))|
      = MeasureTheory.volume.real (Φ '' (normLeOne K) ∩ Os)
          / |LinearMap.det (((LinearEquiv.smulOfNeZero ℝ (index K → ℝ) (m : ℝ) hm).trans T
            : (index K → ℝ) ≃ₗ[ℝ] (index K → ℝ)) : (index K → ℝ) →ₗ[ℝ] (index K → ℝ))| / NB := by
    have hdetScaled :
        |LinearMap.det ((((LinearEquiv.smulOfNeZero ℝ (index K → ℝ) (m : ℝ) hm).trans T'
          : (index K → ℝ) ≃ₗ[ℝ] (index K → ℝ)) : (index K → ℝ) →ₗ[ℝ] (index K → ℝ)))|
          = (Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ℝ)
            * |LinearMap.det ((((LinearEquiv.smulOfNeZero ℝ (index K → ℝ) (m : ℝ) hm).trans T
              : (index K → ℝ) ≃ₗ[ℝ] (index K → ℝ)) : (index K → ℝ) →ₗ[ℝ] (index K → ℝ)))| := by
      have hdet := abs_det_latticeEquiv_mul J 𝔟 T T' hT hT'
      rw [LinearEquiv.coe_trans, LinearEquiv.coe_trans, LinearMap.det_comp, LinearMap.det_comp,
        abs_mul, abs_mul, hdet]
      ring
    rw [hdetScaled, ← hNBdef, div_div, mul_comm (NB : ℝ), ← div_div]
  refine ⟨|cellC'|, fun t ht ↦ ?_⟩
  by_cases hQ : ∃ a : idealSet K J,
      (Finset.univ.filter (fun w : {w : InfinitePlace K // IsReal w} ↦
        (a : mixedSpace K).1 w < 0) = s) ∧
      ((fun i ↦ (round ((T.symm (Φ (a : mixedSpace K))) i) : ZMod m)) = k) ∧
      ((intNorm (idealSetEquiv K J a).val : ZMod m) = (b : ZMod m))
  · obtain ⟨a₀, horth₀, hcos₀, hres₀⟩ := hQ
    rw [if_pos ⟨a₀, horth₀, hcos₀, hres₀⟩]
    have hdrop : Nat.card {a : idealSet K (𝔟 * J) //
        (mixedEmbedding.norm (a : mixedSpace K) ≤ t ^ d ∧
          ((intNorm (idealSetEquiv K (𝔟 * J) a).val : ZMod m) = (b : ZMod m))) ∧
        (Finset.univ.filter (fun w : {w : InfinitePlace K // IsReal w} ↦
          (a : mixedSpace K).1 w < 0) = s) ∧
        (fun i ↦ (round ((T.symm (Φ (a : mixedSpace K))) i) : ZMod m)) = k}
        = Nat.card {a : idealSet K (𝔟 * J) //
          mixedEmbedding.norm (a : mixedSpace K) ≤ t ^ d ∧
          (Finset.univ.filter (fun w : {w : InfinitePlace K // IsReal w} ↦
            (a : mixedSpace K).1 w < 0) = s) ∧
          (fun i ↦ (round ((T.symm (Φ (a : mixedSpace K))) i) : ZMod m)) = k} := by
      refine Nat.card_congr (Equiv.subtypeEquivRight fun a ↦ ?_)
      constructor
      · rintro ⟨⟨hn, _⟩, ho, hc⟩; exact ⟨hn, ho, hc⟩
      · rintro ⟨hn, ho, hc⟩
        refine ⟨⟨hn, ?_⟩, ho, hc⟩
        have haJ : (a : mixedSpace K) ∈ idealSet K J :=
          ⟨a.2.1, idealLattice_mul_le J 𝔟 a.2.2⟩
        have hkey := residue_fibre_const_aux m b J T hT s k ⟨(a : mixedSpace K), haJ⟩ a₀ ho hc
          horth₀ hcos₀
        exact hkey.mpr hres₀
    obtain ⟨ξ', hξ'⟩ := exists_card_fibre_dvd_eq_card_cell m hm J 𝔟 hcop T T' hT hT' s k ht
    rw [hdrop, hξ']
    have hcell'' := hcell' ξ' t ht
    rw [hsmul] at hcell''
    rw [← hOs] at hcell''
    rw [hdetratio] at hcell''
    rw [hcard] at hcell''
    exact hcell''.trans (by gcongr; exact le_abs_self _)
  · rw [if_neg hQ, zero_div, zero_mul, sub_zero]
    have : IsEmpty {a : idealSet K (𝔟 * J) //
        (mixedEmbedding.norm (a : mixedSpace K) ≤ t ^ d ∧
          ((intNorm (idealSetEquiv K (𝔟 * J) a).val : ZMod m) = (b : ZMod m))) ∧
        (Finset.univ.filter (fun w : {w : InfinitePlace K // IsReal w} ↦
          (a : mixedSpace K).1 w < 0) = s) ∧
        (fun i ↦ (round ((T.symm (Φ (a : mixedSpace K))) i) : ZMod m)) = k} := by
      refine ⟨fun a ↦ hQ ⟨⟨(a.1 : mixedSpace K), a.1.2.1, idealLattice_mul_le J 𝔟 a.1.2.2⟩,
        a.2.2.1, a.2.2.2, ?_⟩⟩
      exact a.2.1.2
    rw [Nat.card_of_isEmpty, Nat.cast_zero, abs_zero]
    positivity

end Chebotarev
