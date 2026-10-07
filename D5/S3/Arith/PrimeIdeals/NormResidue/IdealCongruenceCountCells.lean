/- GID: D5/S3/Arith/PrimeIdeals/NormResidue/IdealCongruenceCountCells
   generality: G
   mirror-B: D5/B/S3/Arith/PrimeIdeals/NormResidue/IdealCongruenceCountCells
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Ideal-set cone points in a norm-residue class admit a power-error count. -/
module

public import D5.S3.Arith.PrimeIdeals.NormResidue.IdealCongruenceCountCellGeometry

@[expose] public section

noncomputable section

namespace Chebotarev

open NumberField Set Submodule

open scoped NNReal nonZeroDivisors Pointwise

open Ideal NumberField.mixedEmbedding NumberField.mixedEmbedding.fundamentalCone
  NumberField.InfinitePlace NumberField.Units Units dirichletUnitTheorem Classical in
/-- **Effective count of cone points of `idealSet K J` with a norm residue** (the Widmer / GRS
geometric core). For a fixed nonzero ideal `J`, a modulus `m` and a residue `b`, the number of
cone points `a ∈ idealSet K J` of `mixedEmbedding.norm ≤ N·N(J)` whose integer norm
`intNorm (idealSetEquiv K J a)` is `≡ b (mod m)` is `κ·N + O(N^{1-1/d})`, `d = [K:ℚ]`.

This is the substantive analytic input. Proof (Gun–Ramaré–Sivaraman, *Counting ideals in ray
classes*, JNT 243 (2023), §3, after Widmer, Trans. AMS 362 (2010)): transport the count to the
standard coordinate space `index K → ℝ` along the chart `Φ = (stdBasis K).equivFunL`
(`Submodule.map_span` carries `idealLattice K J` to a full lattice `Λ_J = T '' ℤ^ι`); the
norm-region `fundamentalCone ∩ {norm ≤ N·N(J)}` is the real dilation `t • normLeOne K` at
`t = (N·N(J))^{1/d}` (norm-homogeneity `mixedEmbedding.norm_smul` + cone `smul`-stability
`smul_mem_iff_mem`), so the count is the number of points of `Λ_J ∩ (t • Φ '' normLeOne K)`
carrying the residue. Partition by the sign pattern `s` of the real coordinates (the orthant
decomposition `plusPart`/`negAt`); on each orthant the signed product formula turns the
absolute residue `|Norm| ≡ b` into the signed residue `Norm ≡ ±b`, which is constant on cosets of
`m • Λ_J` by the determinant formula for the algebraic norm. Count each qualifying (orthant, coset) by the
workhorse `exists_card_coset_inter_smul_sub_volume_mul_rpow_le` (the frontier cover from
`normLeOne_frontier_lipschitz_cover_index` together with the bounded coordinate-hyperplane pieces
cut by the orthant), and sum the finitely many estimates: the leading terms give `κ·N` (with
`t^d = N·N(J)`) and the error terms `O(t^{d-1}) = O((N·N(J))^{1-1/d}) = O(N^{1-1/d})`
(`Real.rpow` algebra, `N(J) ≥ 1`). -/
theorem exists_card_idealSet_residue_le {K : Type*} [Field K] [NumberField K]
    (m : ℕ) [NeZero m] (b : ℕ) (J : (Ideal (𝓞 K))⁰) :
    ∃ κ C' : ℝ, ∀ N : ℕ, 1 ≤ N →
      |(Nat.card {a : idealSet K J // mixedEmbedding.norm (a : mixedSpace K) ≤
            ((N * Ideal.absNorm (J : Ideal (𝓞 K)) : ℕ) : ℝ) ∧
          ((intNorm (idealSetEquiv K J a).val : ZMod m) = (b : ZMod m))} : ℝ) - κ * N|
        ≤ C' * (N : ℝ) ^ (1 - (Module.finrank ℚ K : ℝ)⁻¹) := by
  classical
  have card_residue_sum_bound_aux
      (m : ℕ) [NeZero m] (b : ℕ) (I₀ : (Ideal (𝓞 K))⁰)
      (Tc : (index K → ℝ) ≃ₗ[ℝ] (index K → ℝ)) (S : ℝ) (hS : 1 ≤ S)
      (Lc Cc : Finset {w : InfinitePlace K // IsReal w} × (index K → ZMod m) → ℝ)
      (hcell : ∀ (p : Finset {w : InfinitePlace K // IsReal w} × (index K → ZMod m)) (tN : ℝ),
        1 ≤ tN →
        |(Nat.card {a : idealSet K I₀ //
            (mixedEmbedding.norm (a : mixedSpace K) ≤ tN ^ Module.finrank ℚ K ∧
              ((intNorm (idealSetEquiv K I₀ a).val : ZMod m) = (b : ZMod m))) ∧
            (Finset.univ.filter (fun w : {w : InfinitePlace K // IsReal w} ↦
              (a : mixedSpace K).1 w < 0) = p.1) ∧
            (fun i ↦ (round ((Tc.symm ((mixedEmbedding.stdBasis K).equivFunL
              (a : mixedSpace K))) i) : ZMod m)) = p.2} : ℝ) - Lc p * tN ^ Module.finrank ℚ K|
          ≤ Cc p * tN ^ (Module.finrank ℚ K - 1 : ℕ)) :
      |(Nat.card {a : idealSet K I₀ // mixedEmbedding.norm (a : mixedSpace K) ≤ S ∧
          ((intNorm (idealSetEquiv K I₀ a).val : ZMod m) = (b : ZMod m))} : ℝ)
          - (∑ p, Lc p) * S|
        ≤ (∑ p, Cc p) * S ^ (1 - (Module.finrank ℚ K : ℝ)⁻¹) := by
    classical
    have hpartition :
        Nat.card {a : idealSet K I₀ // mixedEmbedding.norm (a : mixedSpace K) ≤ S ∧
            ((intNorm (idealSetEquiv K I₀ a).val : ZMod m) = (b : ZMod m))}
          = ∑ p : Finset {w : InfinitePlace K // IsReal w} × (index K → ZMod m),
            Nat.card {a : idealSet K I₀ //
              (mixedEmbedding.norm (a : mixedSpace K) ≤ S ∧
                ((intNorm (idealSetEquiv K I₀ a).val : ZMod m) = (b : ZMod m))) ∧
              (Finset.univ.filter (fun w : {w : InfinitePlace K // IsReal w} ↦
                (a : mixedSpace K).1 w < 0) = p.1) ∧
              (fun i ↦ (round ((Tc.symm ((mixedEmbedding.stdBasis K).equivFunL
                (a : mixedSpace K))) i) : ZMod m)) = p.2} := by
      set Φ : mixedSpace K ≃L[ℝ] (index K → ℝ) := (mixedEmbedding.stdBasis K).equivFunL with hΦ
      let cls : {a : idealSet K I₀ // mixedEmbedding.norm (a : mixedSpace K) ≤ S ∧
          ((intNorm (idealSetEquiv K I₀ a).val : ZMod m) = (b : ZMod m))} →
          Finset {w : InfinitePlace K // IsReal w} × (index K → ZMod m) :=
        fun a ↦ (Finset.univ.filter (fun w ↦ (a.1 : mixedSpace K).1 w < 0),
          fun i ↦ (round ((Tc.symm (Φ (a.1 : mixedSpace K))) i) : ZMod m))
      have hfinbase : Finite {a : idealSet K I₀ //
          mixedEmbedding.norm (a : mixedSpace K) ≤ S} := by
        letI : Finite {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) ≤ ⌊S⌋₊} :=
          (Ideal.finite_setOf_absNorm_le₀ ⌊S⌋₊).to_subtype
        refine Finite.of_injective (β :=
            {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) ≤ ⌊S⌋₊} × torsion K)
          (fun a ↦ ⟨⟨(integerSetEquiv K (idealSetMap K I₀ a.1)).1.1, ?_⟩,
            (integerSetEquiv K (idealSetMap K I₀ a.1)).2⟩) ?_
        · have hnorm :
              Ideal.absNorm ((integerSetEquiv K (idealSetMap K I₀ a.1)).1.1 : Ideal (𝓞 K))
                = intNorm (idealSetMap K I₀ a.1) := by
            rw [integerSetEquiv_apply_fst, intNorm, absNorm_span_singleton]
          rw [hnorm]
          refine Nat.le_floor ?_
          rw [intNorm_coe, idealSetMap_apply]
          exact a.2
        · intro a a' h
          simp only [Prod.mk.injEq, Subtype.mk.injEq] at h
          have heq : integerSetEquiv K (idealSetMap K I₀ a.1) =
              integerSetEquiv K (idealSetMap K I₀ a'.1) :=
            Prod.ext (Subtype.ext h.1) h.2
          have hmap : idealSetMap K I₀ a.1 = idealSetMap K I₀ a'.1 :=
            (integerSetEquiv K).injective heq
          exact Subtype.ext (Subtype.ext (by
            have := congrArg (Subtype.val) hmap
            simpa [idealSetMap_apply] using this))
      have : ∀ p : Finset {w : InfinitePlace K // IsReal w} × (index K → ZMod m),
          Finite {a : idealSet K I₀ //
            (mixedEmbedding.norm (a : mixedSpace K) ≤ S ∧
              ((intNorm (idealSetEquiv K I₀ a).val : ZMod m) = (b : ZMod m))) ∧
            (Finset.univ.filter (fun w : {w : InfinitePlace K // IsReal w} ↦
              (a : mixedSpace K).1 w < 0) = p.1) ∧
            (fun i ↦ (round ((Tc.symm (Φ (a : mixedSpace K))) i) : ZMod m)) = p.2} := fun p ↦
        Finite.of_injective (fun a ↦ (⟨a.1, a.2.1.1⟩ : {a : idealSet K I₀ //
          mixedEmbedding.norm (a : mixedSpace K) ≤ S}))
          (fun x y h ↦ Subtype.ext (by simpa using h))
      rw [← Nat.card_sigma]
      refine Nat.card_congr ((Equiv.sigmaFiberEquiv cls).symm.trans (Equiv.sigmaCongrRight fun p ↦
        ?_))
      exact {
        toFun := fun a ↦ ⟨a.1.1, ⟨a.1.2, by
            have := a.2; simp only [cls, Prod.ext_iff] at this; exact ⟨this.1, this.2⟩⟩⟩
        invFun := fun a ↦ ⟨⟨a.1, a.2.1⟩, by
          simp only [cls, Prod.ext_iff]
          exact ⟨a.2.2.1, a.2.2.2⟩⟩
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl }
    set d := Module.finrank ℚ K with hd
    have hdpos : 0 < d := Module.finrank_pos
    have hdne : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hdpos.ne'
    set tN : ℝ := S ^ ((d : ℝ)⁻¹) with htN
    have hs0 : (0 : ℝ) < S := lt_of_lt_of_le one_pos hS
    have htN1 : 1 ≤ tN := Real.one_le_rpow hS (by positivity)
    have htNd : tN ^ d = S := by
      rw [htN, ← Real.rpow_natCast (S ^ ((d : ℝ)⁻¹)) d, ← Real.rpow_mul hs0.le,
        inv_mul_cancel₀ hdne, Real.rpow_one]
    have htNd1 : tN ^ (d - 1 : ℕ) = S ^ (1 - (d : ℝ)⁻¹) := by
      have hdcast : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
        rw [Nat.cast_sub hdpos]; simp
      rw [htN, ← Real.rpow_natCast (S ^ ((d : ℝ)⁻¹)) (d - 1), ← Real.rpow_mul hs0.le, hdcast]
      congr 1
      rw [inv_mul_eq_div, sub_div, div_self hdne, one_div]
    rw [hpartition, Nat.cast_sum]
    have hlead : (∑ p, Lc p) * S = ∑ p, Lc p * tN ^ d := by rw [← Finset.sum_mul, htNd]
    rw [hlead, ← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hbound : (∑ p, Cc p) * S ^ (1 - (d : ℝ)⁻¹) = ∑ p, Cc p * tN ^ (d - 1 : ℕ) := by
      simp_rw [htNd1, Finset.sum_mul]
    rw [hbound]
    refine Finset.sum_le_sum (fun p _ ↦ ?_)
    rw [← htNd]
    exact hcell p tN htN1
  set Φ : mixedSpace K ≃L[ℝ] (index K → ℝ) := (mixedEmbedding.stdBasis K).equivFunL with hΦ
  set d := Module.finrank ℚ K with hd
  have hdpos : 0 < d := Module.finrank_pos
  set NJ := Ideal.absNorm (J : Ideal (𝓞 K)) with hNJdef
  have hNJ : 0 < NJ := absNorm_pos_of_nonZeroDivisors J
  have hm : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne m)
  have latticeRepresentation (I₀ : (Ideal (𝓞 K))⁰) :
      ∃ T : (index K → ℝ) ≃ₗ[ℝ] (index K → ℝ),
        T '' (span ℤ (Set.range (Pi.basisFun ℝ (index K))) : Set (index K → ℝ))
          = ((mixedEmbedding.stdBasis K).equivFunL '' (mixedEmbedding.idealLattice K
              (FractionalIdeal.mk0 K I₀)) : Set (index K → ℝ)) := by
    set Ψ : mixedSpace K ≃L[ℝ] (index K → ℝ) := (mixedEmbedding.stdBasis K).equivFunL
    set I := FractionalIdeal.mk0 K I₀
    have e : Module.Free.ChooseBasisIndex ℤ I ≃ index K := by
      apply Fintype.equivOfCardEq
      rw [← Module.finrank_eq_card_chooseBasisIndex, NumberField.fractionalIdeal_rank,
        RingOfIntegers.rank, ← Module.finrank_eq_card_basis (mixedEmbedding.stdBasis K),
        mixedEmbedding.finrank]
    set c : Module.Basis (index K) ℝ (index K → ℝ) :=
      ((mixedEmbedding.fractionalIdealLatticeBasis K I).map Ψ.toLinearEquiv).reindex e with hc
    refine ⟨(Pi.basisFun ℝ (index K)).equiv c (Equiv.refl (index K)), ?_⟩
    have hcrange : Set.range c
        = Ψ '' (Set.range (mixedEmbedding.fractionalIdealLatticeBasis K I)) := by
      rw [hc, Module.Basis.range_reindex, ← Set.range_comp]; rfl
    have hmapc :
        ((Pi.basisFun ℝ (index K)).equiv c (Equiv.refl (index K))) ''
          (span ℤ (Set.range (Pi.basisFun ℝ (index K))) : Set (index K → ℝ)) =
        (span ℤ (((Pi.basisFun ℝ (index K)).equiv c (Equiv.refl (index K))) ''
          Set.range (Pi.basisFun ℝ (index K))) : Set (index K → ℝ)) := by
      simpa using congrArg SetLike.coe (Submodule.map_span
        (((Pi.basisFun ℝ (index K)).equiv c (Equiv.refl (index K))).restrictScalars ℤ).toLinearMap
        (Set.range (Pi.basisFun ℝ (index K))))
    rw [hmapc]
    have hrange : ((Pi.basisFun ℝ (index K)).equiv c (Equiv.refl (index K)))
        '' (Set.range (Pi.basisFun ℝ (index K))) = Set.range c := by
      rw [← Set.range_comp]
      congr 1; ext i
      simp only [Function.comp_apply, Module.Basis.equiv_apply, Equiv.refl_apply]
    rw [hrange, hcrange, ← mixedEmbedding.span_idealLatticeBasis K I]
    have hmapΨ :
        Ψ '' (span ℤ (Set.range (mixedEmbedding.fractionalIdealLatticeBasis K I)) :
          Set (mixedSpace K)) =
        (span ℤ (Ψ '' Set.range (mixedEmbedding.fractionalIdealLatticeBasis K I)) :
          Set (index K → ℝ)) := by
      simpa using congrArg SetLike.coe (Submodule.map_span
        (Ψ.toLinearEquiv.restrictScalars ℤ).toLinearMap
        (Set.range (mixedEmbedding.fractionalIdealLatticeBasis K I)))
    exact hmapΨ.symm
  obtain ⟨T, hT⟩ := latticeRepresentation J
  let clampUnit (c : {w : InfinitePlace K // w ≠ w₀} → ℝ) :
      {w : InfinitePlace K // w ≠ w₀} → ℝ :=
    fun i ↦ (Set.projIcc 0 1 zero_le_one (c i) : ℝ)


  have contDiff_expMapBasis {n : WithTop ℕ∞} : ContDiff ℝ n (⇑(expMapBasis (K := K))) := by
    classical
    rw [show ⇑(expMapBasis (K := K)) = fun x : realSpace K ↦
        Real.exp (x w₀) • fun w : InfinitePlace K ↦
          ∏ i : {w // w ≠ w₀}, w (fundSystem K (equivFinRank.symm i)) ^ x i from
      funext expMapBasis_apply']
    fun_prop (disch := exact fun x ↦ (InfinitePlace.pos_iff.mpr (by simp)).ne')

  let faceMapZero (c : {w : InfinitePlace K // w ≠ w₀} → ℝ) : realSpace K :=
    expMapBasis fun w ↦ if hw : w = w₀ then 0 else c ⟨w, hw⟩

  let faceMapSide (i : {w : InfinitePlace K // w ≠ w₀}) (a : ℝ)
      (c : {w : InfinitePlace K // w ≠ w₀} → ℝ) : realSpace K :=
    c i • expMapBasis fun w ↦ if hw : w = w₀ then 0 else if (⟨w, hw⟩ : {w // w ≠ w₀}) = i then a
      else c ⟨w, hw⟩

  have contDiff_faceMapZero : ContDiff ℝ 1 (faceMapZero) := by
    refine (contDiff_expMapBasis).comp (contDiff_pi.mpr fun w ↦ ?_)
    by_cases hw : w = w₀
    · simpa only [dif_pos hw] using contDiff_const
    · simpa only [dif_neg hw] using contDiff_apply ℝ ℝ _

  have contDiff_faceMapSide (i : {w : InfinitePlace K // w ≠ w₀}) (a : ℝ) :
      ContDiff ℝ 1 (faceMapSide i a) := by
    refine (contDiff_apply ℝ ℝ i).smul ((contDiff_expMapBasis).comp (contDiff_pi.mpr fun w ↦ ?_))
    by_cases hw : w = w₀
    · simpa only [dif_pos hw] using contDiff_const
    · simp only [dif_neg hw]
      by_cases hi : (⟨w, hw⟩ : {w // w ≠ w₀}) = i
      · simpa only [if_pos hi] using contDiff_const
      · simpa only [if_neg hi] using contDiff_apply ℝ ℝ _

  have expMapBasis_mem_iUnion_faceMapSide
      {y : realSpace K} {w : InfinitePlace K} (hwe : w ≠ w₀) (hw₀ : y w₀ ≤ 0)
      (hIcc : ∀ v : InfinitePlace K, v ≠ w₀ → y v ∈ Icc (0 : ℝ) 1) (ha : y w = 0 ∨ y w = 1) :
      (expMapBasis y : realSpace K) ∈
        ⋃ i : {w : InfinitePlace K // w ≠ w₀}, ⋃ a ∈ ({0, 1} : Set ℝ),
          faceMapSide i a '' Icc 0 1 := by
    set i : {w : InfinitePlace K // w ≠ w₀} := ⟨w, hwe⟩ with hi
    set c : {w : InfinitePlace K // w ≠ w₀} → ℝ :=
      fun j ↦ if j = i then Real.exp (y w₀) else y j.1 with hc
    have hcmem : c ∈ Icc (0 : {w : InfinitePlace K // w ≠ w₀} → ℝ) 1 := by
      refine ⟨fun j ↦ ?_, fun j ↦ ?_⟩ <;> simp only [hc] <;> split_ifs
      · exact Real.exp_nonneg _
      · exact (hIcc j.1 j.2).1
      · exact Real.exp_le_one_iff.mpr hw₀
      · exact (hIcc j.1 j.2).2
    have hkey : faceMapSide i (y w) c = expMapBasis y := by
      have hci : c i = Real.exp (y w₀) := by simp [hc]
      have hfun : (fun w' ↦ if hw' : w' = w₀ then (0 : ℝ) else
          if (⟨w', hw'⟩ : {w // w ≠ w₀}) = i then y w else c ⟨w', hw'⟩) =
          fun w' ↦ if w' = w₀ then 0 else y w' := by
        funext w'
        by_cases hw'₀ : w' = w₀
        · simp only [dif_pos hw'₀, if_pos hw'₀]
        · simp only [dif_neg hw'₀, if_neg hw'₀]
          by_cases hw'w : (⟨w', hw'₀⟩ : {w // w ≠ w₀}) = i
          · obtain rfl : w' = w := by rw [hi, Subtype.mk_eq_mk] at hw'w; exact hw'w
            simp only [if_pos hw'w]
          · simp only [hc, if_neg hw'w]
      simp only [faceMapSide]
      rw [expMapBasis_apply'' y, hci, hfun]
    refine Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion₂.mpr ⟨y w, ?_, ⟨c, hcmem, hkey⟩⟩⟩
    rcases ha with h | h <;> simp [h]

  have image_boundary_subset_faces :
      expMapBasis '' (closure (paramSet K) \ interior (paramSet K)) ⊆
        faceMapZero '' Icc 0 1 ∪
          ⋃ i : {w : InfinitePlace K // w ≠ w₀}, ⋃ a ∈ ({0, 1} : Set ℝ),
            faceMapSide i a '' Icc 0 1 := by
    classical
    rintro _ ⟨y, ⟨hyc, hyni⟩, rfl⟩
    rw [closure_paramSet, Set.mem_univ_pi] at hyc
    rw [interior_paramSet, Set.mem_univ_pi] at hyni
    push Not at hyni
    obtain ⟨w, hw⟩ := hyni
    have hw₀ : y w₀ ≤ 0 := by simpa using hyc w₀
    have hIcc : ∀ v : InfinitePlace K, v ≠ w₀ → y v ∈ Icc (0 : ℝ) 1 := fun v hv ↦ by
      simpa [hv] using hyc v
    by_cases hwe : w = w₀
    · rw [if_pos hwe, Set.mem_Iio, not_lt, hwe] at hw
      have hy0 : y w₀ = 0 := le_antisymm hw₀ hw
      refine Or.inl ⟨fun i ↦ y i.1, ⟨fun i ↦ (hIcc i.1 i.2).1, fun i ↦ (hIcc i.1 i.2).2⟩, ?_⟩
      simp only [faceMapZero]
      congr 1
      funext v
      by_cases hv : v = w₀
      · rw [dif_pos hv, hv, hy0]
      · simp only [dif_neg hv]
    · rw [if_neg hwe] at hw
      have h1 := hIcc w hwe
      rw [Set.mem_Ioo, not_and_or, not_lt, not_lt] at hw
      refine Or.inr (expMapBasis_mem_iUnion_faceMapSide hwe hw₀ hIcc ?_)
      rcases hw with h | h
      · exact Or.inl (le_antisymm h h1.1)
      · exact Or.inr (le_antisymm h1.2 h)

  let cubeRelabel (c : Fin (Fintype.card (InfinitePlace K) - 1) → ℝ) :
      {w : InfinitePlace K // w ≠ w₀} → ℝ :=
    fun j ↦ c (equivFinRank.symm j)

  let frontierCoverFamily :
      (Unit ⊕ Unit ⊕ ({w : InfinitePlace K // w ≠ w₀} × Bool)) →
        (Fin (Fintype.card (InfinitePlace K) - 1) → ℝ) → realSpace K :=
    Sum.elim (fun _ _ ↦ 0)
      (Sum.elim (fun _ ↦ faceMapZero ∘
        clampUnit ∘ cubeRelabel)
        fun p ↦ faceMapSide p.1 (if p.2 then 1 else 0) ∘
          clampUnit ∘ cubeRelabel)

  have exists_lipschitzWith_frontierCoverFamily :
      ∃ M : ℝ≥0, ∀ s, LipschitzWith M (frontierCoverFamily s) := by
    classical
    obtain ⟨M₀, hM₀⟩ :
        ∃ M : ℝ≥0, LipschitzWith M (faceMapZero ∘ clampUnit) := by
      have hl := (contDiff_faceMapZero).locallyLipschitz.locallyLipschitzOn
        (s := Icc (0 : {w : InfinitePlace K // w ≠ w₀} → ℝ) 1)
      obtain ⟨M, hM⟩ := hl.exists_lipschitzOnWith_of_compact isCompact_Icc
      refine ⟨M, ?_⟩
      intro c d
      have hc : clampUnit c ∈ Icc (0 : {w : InfinitePlace K // w ≠ w₀} → ℝ) 1 :=
        ⟨fun i ↦ (Set.projIcc 0 1 zero_le_one (c i)).2.1,
          fun i ↦ (Set.projIcc 0 1 zero_le_one (c i)).2.2⟩
      have hd : clampUnit d ∈ Icc (0 : {w : InfinitePlace K // w ≠ w₀} → ℝ) 1 :=
        ⟨fun i ↦ (Set.projIcc 0 1 zero_le_one (d i)).2.1,
          fun i ↦ (Set.projIcc 0 1 zero_le_one (d i)).2.2⟩
      refine (hM hc hd).trans ?_
      gcongr
      have hclamp : LipschitzWith 1 clampUnit :=
        LipschitzWith.of_edist_le fun c d ↦ by
          rw [edist_pi_def]
          exact Finset.sup_le fun i _ ↦ (Subtype.edist_eq _ _).symm.trans_le <|
            (((LipschitzWith.projIcc zero_le_one).edist_le_mul (c i) (d i)).trans_eq
              (one_mul _)).trans (edist_le_pi_edist c d i)
      simpa using hclamp.edist_le_mul c d
    choose Ms hMs using fun p : {w : InfinitePlace K // w ≠ w₀} × Bool ↦
      show ∃ M : ℝ≥0,
          LipschitzWith M (faceMapSide p.1 (if p.2 then 1 else 0) ∘ clampUnit) from by
        have hl := (contDiff_faceMapSide p.1 (if p.2 then 1 else 0)).locallyLipschitz.locallyLipschitzOn
          (s := Icc (0 : {w : InfinitePlace K // w ≠ w₀} → ℝ) 1)
        obtain ⟨M, hM⟩ := hl.exists_lipschitzOnWith_of_compact isCompact_Icc
        refine ⟨M, ?_⟩
        intro c d
        have hc : clampUnit c ∈ Icc (0 : {w : InfinitePlace K // w ≠ w₀} → ℝ) 1 :=
          ⟨fun i ↦ (Set.projIcc 0 1 zero_le_one (c i)).2.1,
            fun i ↦ (Set.projIcc 0 1 zero_le_one (c i)).2.2⟩
        have hd : clampUnit d ∈ Icc (0 : {w : InfinitePlace K // w ≠ w₀} → ℝ) 1 :=
          ⟨fun i ↦ (Set.projIcc 0 1 zero_le_one (d i)).2.1,
            fun i ↦ (Set.projIcc 0 1 zero_le_one (d i)).2.2⟩
        refine (hM hc hd).trans ?_
        gcongr
        have hclamp : LipschitzWith 1 clampUnit :=
          LipschitzWith.of_edist_le fun c d ↦ by
            rw [edist_pi_def]
            exact Finset.sup_le fun i _ ↦ (Subtype.edist_eq _ _).symm.trans_le <|
              (((LipschitzWith.projIcc zero_le_one).edist_le_mul (c i) (d i)).trans_eq
                (one_mul _)).trans (edist_le_pi_edist c d i)
        simpa using hclamp.edist_le_mul c d
    refine ⟨M₀ ⊔ Finset.univ.sup Ms, fun s ↦ ?_⟩
    rcases s with _ | _ | p
    · exact (LipschitzWith.const _).weaken zero_le
    · exact (hM₀.comp (LipschitzWith.of_edist_le fun c d ↦ by
        rw [edist_pi_def]
        exact Finset.sup_le fun j _ ↦ edist_le_pi_edist c d (equivFinRank.symm j))).weaken
          (by rw [mul_one]; exact le_sup_left)
    · exact ((hMs p).comp (LipschitzWith.of_edist_le fun c d ↦ by
        rw [edist_pi_def]
        exact Finset.sup_le fun j _ ↦ edist_le_pi_edist c d (equivFinRank.symm j))).weaken
        (by rw [mul_one]; exact le_sup_of_le_right (Finset.le_sup (Finset.mem_univ p)))

  have frontier_subset_frontierCoverFamily :
      frontier (normAtAllPlaces '' normLeOne K) ⊆
        ⋃ s, frontierCoverFamily s '' Icc 0 1 := by
    classical
    rw [normAtAllPlaces_normLeOne_eq_image]
    have hcl : closure (expMapBasis '' paramSet K) ⊆
        expMapBasis '' closure (paramSet K) ∪ {0} :=
      compactSet_eq_union K ▸ (isCompact_compactSet K).isClosed.closure_subset_iff.mpr
        ((Set.image_mono subset_closure).trans (expMapBasis_closure_subset_compactSet K))
    have hopen : IsOpenMap (⇑(expMapBasis (K := K))) :=
      fun _ hU ↦ expMapBasis.isOpen_image_of_subset_source hU (by simp [expMapBasis_source])
    have hfront : frontier (expMapBasis '' paramSet K) ⊆
        expMapBasis '' (closure (paramSet K) \ interior (paramSet K)) ∪ {0} := by
      refine (Set.sdiff_subset_sdiff hcl (hopen.image_interior_subset (paramSet K))).trans ?_
      rw [Set.union_sdiff_distrib, ← Set.image_sdiff (injective_expMapBasis K)]
      exact Set.union_subset_union_right _ Set.sdiff_subset
    refine hfront.trans
      (Set.union_subset ((image_boundary_subset_faces).trans (Set.union_subset ?_ ?_)) ?_)
    · rintro x ⟨c', hc', rfl⟩
      obtain ⟨c, hc, rfl⟩ :
          ∃ c ∈ Icc (0 : Fin (Fintype.card (InfinitePlace K) - 1) → ℝ) 1,
            cubeRelabel c = c' :=
        ⟨fun j ↦ c' (equivFinRank j), ⟨fun j ↦ hc'.1 _, fun j ↦ hc'.2 _⟩,
          funext fun j ↦ by simp [cubeRelabel]⟩
      refine Set.mem_iUnion.mpr ⟨Sum.inr (Sum.inl ()), c, hc, ?_⟩
      change faceMapZero (clampUnit (cubeRelabel c)) = faceMapZero (cubeRelabel c)
      have hclamp : clampUnit (cubeRelabel c) = cubeRelabel c := by
        funext j
        have hj : cubeRelabel c j ∈ Icc (0 : ℝ) 1 :=
          ⟨hc.1 (equivFinRank.symm j), hc.2 (equivFinRank.symm j)⟩
        change (Set.projIcc 0 1 zero_le_one (cubeRelabel c j) : ℝ) = cubeRelabel c j
        exact congrArg (fun x : Icc (0 : ℝ) 1 ↦ (x : ℝ))
          (Set.projIcc_of_mem zero_le_one hj)
      rw [hclamp]
    · rintro x hx
      simp only [Set.mem_iUnion] at hx
      obtain ⟨i, a, ha, c', hc', rfl⟩ := hx
      obtain ⟨c, hc, rfl⟩ :
          ∃ c ∈ Icc (0 : Fin (Fintype.card (InfinitePlace K) - 1) → ℝ) 1,
            cubeRelabel c = c' :=
        ⟨fun j ↦ c' (equivFinRank j), ⟨fun j ↦ hc'.1 _, fun j ↦ hc'.2 _⟩,
          funext fun j ↦ by simp [cubeRelabel]⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
      obtain ⟨b, rfl⟩ : ∃ b : Bool, (if b then (1 : ℝ) else 0) = a := by
        rcases ha with rfl | rfl
        · exact ⟨false, rfl⟩
        · exact ⟨true, rfl⟩
      refine Set.mem_iUnion.mpr ⟨Sum.inr (Sum.inr (i, b)), c, hc, ?_⟩
      change faceMapSide i (if b then (1 : ℝ) else 0) (clampUnit (cubeRelabel c)) = _
      have hclamp : clampUnit (cubeRelabel c) = cubeRelabel c := by
        funext j
        have hj : cubeRelabel c j ∈ Icc (0 : ℝ) 1 :=
          ⟨hc.1 (equivFinRank.symm j), hc.2 (equivFinRank.symm j)⟩
        change (Set.projIcc 0 1 zero_le_one (cubeRelabel c j) : ℝ) = cubeRelabel c j
        exact congrArg (fun x : Icc (0 : ℝ) 1 ↦ (x : ℝ))
          (Set.projIcc_of_mem zero_le_one hj)
      rw [hclamp]
    · rintro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact Set.mem_iUnion.mpr ⟨Sum.inl (), 0, ⟨le_rfl, fun _ ↦ zero_le_one⟩, rfl⟩

  have exists_phase_mem_Icc_mul_exp (z : ℂ) :
      ∃ θ : ℝ, θ ∈ Icc (0 : ℝ) 1 ∧
        (‖z‖ : ℂ) * Complex.exp ((2 * Real.pi * θ - Real.pi) * Complex.I) = z := by
    refine ⟨(z.arg + Real.pi) / (2 * Real.pi), ⟨?_, ?_⟩, ?_⟩
    · exact div_nonneg (by linarith [Complex.neg_pi_lt_arg z]) (by positivity)
    · rw [div_le_one (by positivity)]
      linarith [Complex.arg_le_pi z]
    · have hreal : (2 * Real.pi * ((z.arg + Real.pi) / (2 * Real.pi)) - Real.pi : ℝ) = z.arg := by
        field_simp
        ring
      rw [show ((2 : ℂ) * (Real.pi : ℂ) * (((z.arg + Real.pi) / (2 * Real.pi) : ℝ) : ℂ)
            - (Real.pi : ℂ))
          = ((2 * Real.pi * ((z.arg + Real.pi) / (2 * Real.pi)) - Real.pi : ℝ) : ℂ) by
            push_cast; ring, hreal]
      exact Complex.norm_mul_exp_arg_mul_I z

  let mixedCubeEquiv : Fin (Module.finrank ℚ K - 1)
      ≃ Fin (Fintype.card (InfinitePlace K) - 1) ⊕ {w : InfinitePlace K // IsComplex w} := by
    apply Fintype.equivOfCardEq
    rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]
    have h1 : Fintype.card (InfinitePlace K) = nrRealPlaces K + nrComplexPlaces K :=
      card_eq_nrRealPlaces_add_nrComplexPlaces K
    have h2 : nrRealPlaces K + 2 * nrComplexPlaces K = Module.finrank ℚ K :=
      card_add_two_mul_card_eq_rank K
    have hpos : 1 ≤ Fintype.card (InfinitePlace K) := Fintype.card_pos
    have h3 : nrComplexPlaces K = Fintype.card {w : InfinitePlace K // IsComplex w} := rfl
    lia

  let liftToMixed (ψ : (Fin (Fintype.card (InfinitePlace K) - 1) → ℝ) → realSpace K)
      (ε : {w : InfinitePlace K // IsReal w} → Bool)
      (c : Fin (Module.finrank ℚ K - 1) → ℝ) : mixedSpace K :=
    (fun w : {w : InfinitePlace K // IsReal w} ↦
        (if ε w then (1 : ℝ) else -1) * ψ (fun i ↦ c ((mixedCubeEquiv).symm (Sum.inl i))) w.1,
      fun w : {w : InfinitePlace K // IsComplex w} ↦
        (ψ (fun i ↦ c ((mixedCubeEquiv).symm (Sum.inl i))) w.1 : ℂ) *
          Complex.exp ((2 * Real.pi * c ((mixedCubeEquiv).symm (Sum.inr w)) - Real.pi) *
            Complex.I))

  have lipschitzWith_liftToMixed {ψ : (Fin (Fintype.card (InfinitePlace K) - 1) → ℝ) → realSpace K}
      {M₀ : ℝ≥0} {B : ℝ} (hψ : LipschitzWith M₀ ψ) (hB : ∀ c, ‖ψ c‖ ≤ B)
      (ε : {w : InfinitePlace K // IsReal w} → Bool) :
      LipschitzWith (M₀ + (B * (2 * Real.pi)).toNNReal) (liftToMixed ψ ε) := by
    have hdist_mul_exp_phase_le (a b θc θd : ℝ) :
        dist ((a : ℂ) * Complex.exp ((2 * (Real.pi : ℂ) * (θc : ℂ) - (Real.pi : ℂ)) * Complex.I))
            ((b : ℂ) * Complex.exp ((2 * (Real.pi : ℂ) * (θd : ℂ) - (Real.pi : ℂ)) * Complex.I))
          ≤ ‖(a : ℂ)‖ * (2 * Real.pi * dist θc θd) + dist (a : ℂ) (b : ℂ) := by
      set uc := Complex.exp ((2 * (Real.pi : ℂ) * (θc : ℂ) - (Real.pi : ℂ)) * Complex.I) with huc
      set ud := Complex.exp ((2 * (Real.pi : ℂ) * (θd : ℂ) - (Real.pi : ℂ)) * Complex.I) with hud
      have hproduct : dist ((a : ℂ) * uc) ((b : ℂ) * ud) ≤
          ‖(a : ℂ)‖ * dist uc ud + ‖ud‖ * dist (a : ℂ) (b : ℂ) := by
        rw [dist_eq_norm, dist_eq_norm, dist_eq_norm,
          show (a : ℂ) * uc - (b : ℂ) * ud =
            (a : ℂ) * (uc - ud) + ((a : ℂ) - (b : ℂ)) * ud by ring]
        refine (norm_add_le _ _).trans ?_
        rw [norm_mul, norm_mul, mul_comm ‖(a : ℂ) - (b : ℂ)‖ ‖ud‖]
      refine hproduct.trans ?_
      have hav : ‖ud‖ = 1 := by
        rw [hud, Complex.norm_exp, show ((2 * (Real.pi : ℂ) * (θd : ℂ) - (Real.pi : ℂ)) *
          Complex.I).re = 0 by simp, Real.exp_zero]
      have hphase : dist uc ud ≤ 2 * Real.pi * dist θc θd := by
        have haff : LipschitzWith (2 * Real.pi).toNNReal
            (fun t : ℝ ↦ 2 * Real.pi * t - Real.pi) := by
          refine LipschitzWith.of_dist_le_mul fun x y ↦ ?_
          rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ (by positivity),
            show 2 * Real.pi * x - Real.pi - (2 * Real.pi * y - Real.pi) =
              2 * Real.pi * (x - y) by ring, abs_mul,
            abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
        have hcircle : LipschitzWith 1
            (fun t : ℝ ↦ Complex.exp ((t : ℂ) * Complex.I)) := by
          rw [show (fun t : ℝ ↦ Complex.exp ((t : ℂ) * Complex.I)) = circleMap 0 1 from
            funext fun t ↦ by simp [circleMap]]
          simpa using lipschitzWith_circleMap 0 1
        have hcomp : (fun t : ℝ ↦
              Complex.exp ((2 * (Real.pi : ℂ) * (t : ℂ) - (Real.pi : ℂ)) * Complex.I))
            = (fun s : ℝ ↦ Complex.exp ((s : ℂ) * Complex.I))
              ∘ (fun t : ℝ ↦ 2 * Real.pi * t - Real.pi) := by
          funext t
          simp only [Function.comp_apply]
          push_cast
          ring_nf
        have hphaseLip : LipschitzWith (2 * Real.pi).toNNReal
            (fun t : ℝ ↦
              Complex.exp ((2 * (Real.pi : ℂ) * (t : ℂ) - (Real.pi : ℂ)) * Complex.I)) := by
          rw [hcomp, ← one_mul (2 * Real.pi).toNNReal]
          exact hcircle.comp haff
        have h := hphaseLip.dist_le_mul θc θd
        have hcoef : ((2 * Real.pi).toNNReal : ℝ) = 2 * Real.pi :=
          Real.coe_toNNReal _ (mul_nonneg (by norm_num) Real.pi_pos.le)
        simpa only [huc, hud, hcoef] using h
      rw [hav, one_mul]
      gcongr
    have hBnn : 0 ≤ B := le_trans (norm_nonneg _) (hB 0)
    set N : ℝ≥0 := M₀ + (B * (2 * Real.pi)).toNNReal with hN
    refine LipschitzWith.of_dist_le_mul fun c d ↦ ?_
    set yc : realSpace K := ψ (fun i ↦ c ((mixedCubeEquiv).symm (Sum.inl i))) with hyc
    set yd : realSpace K := ψ (fun i ↦ d ((mixedCubeEquiv).symm (Sum.inl i))) with hyd
    have hmod : dist yc yd ≤ M₀ * dist c d := by
      rw [hyc, hyd]
      refine (hψ.dist_le_mul _ _).trans ?_
      gcongr
      exact (dist_pi_le_iff dist_nonneg).mpr fun i ↦ dist_le_pi_dist c d _
    have hmodc : ∀ w : InfinitePlace K, dist (yc w) (yd w) ≤ M₀ * dist c d :=
      fun w ↦ (dist_le_pi_dist yc yd w).trans hmod
    have hyB : ∀ w : InfinitePlace K, ‖(yc w : ℂ)‖ ≤ B := fun w ↦ by
      rw [Complex.norm_real]
      exact (norm_le_pi_norm yc w).trans (hB _)
    simp only [liftToMixed]
    rw [Prod.dist_eq]
    refine max_le ((dist_pi_le_iff (by positivity)).mpr fun w ↦ ?_)
      ((dist_pi_le_iff (by positivity)).mpr fun w ↦ ?_)
    · have hsign : dist ((if ε w then (1 : ℝ) else -1) * yc w.1)
          ((if ε w then (1 : ℝ) else -1) * yd w.1) = dist (yc w.1) (yd w.1) := by
        rw [Real.dist_eq, Real.dist_eq, ← mul_sub, abs_mul]
        split_ifs <;> simp
      rw [hsign]
      refine (hmodc w.1).trans ?_
      gcongr
      rw [hN]
      exact_mod_cast le_self_add
    · refine (hdist_mul_exp_phase_le (yc w.1) (yd w.1) _ _).trans ?_
      have hmodcw : dist (yc w.1 : ℂ) (yd w.1 : ℂ) ≤ M₀ * dist c d := by
        rw [Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
          ← Real.dist_eq]
        exact hmodc w.1
      calc ‖(yc w.1 : ℂ)‖ * (2 * Real.pi * dist (c ((mixedCubeEquiv).symm (Sum.inr w)))
              (d ((mixedCubeEquiv).symm (Sum.inr w)))) + dist (yc w.1 : ℂ) (yd w.1 : ℂ)
          ≤ B * (2 * Real.pi * dist c d) + M₀ * dist c d := by
            gcongr
            · exact hyB w.1
            · exact dist_le_pi_dist c d _
        _ = (↑M₀ + ↑(B * (2 * Real.pi)).toNNReal) * dist c d := by
            rw [Real.coe_toNNReal _ (by positivity)]
            ring
        _ = ↑N * dist c d := by rw [hN, NNReal.coe_add]

  have exists_bound_frontierCoverFamily :
      ∃ B : ℝ, ∀ s c, ‖frontierCoverFamily s c‖ ≤ B := by
    classical
    have hbd : ∀ (g : ({w : InfinitePlace K // w ≠ w₀} → ℝ) → realSpace K),
        Continuous g → ∃ B : ℝ, ∀ c, ‖g (clampUnit (cubeRelabel c))‖ ≤ B := by
      intro g hg
      obtain ⟨B, hB⟩ := (isCompact_Icc.image hg).isBounded.subset_closedBall 0
      refine ⟨B, fun c ↦ ?_⟩
      have hmem : clampUnit (cubeRelabel c) ∈
          Icc (0 : {w : InfinitePlace K // w ≠ w₀} → ℝ) 1 :=
        ⟨fun i ↦ (Set.projIcc 0 1 zero_le_one ((cubeRelabel c) i)).2.1,
          fun i ↦ (Set.projIcc 0 1 zero_le_one ((cubeRelabel c) i)).2.2⟩
      have := hB (mem_image_of_mem g hmem)
      rwa [Metric.mem_closedBall, dist_zero_right] at this
    obtain ⟨B₀, hB₀⟩ := hbd _ (contDiff_faceMapZero).continuous
    choose Bs hBs using fun p : {w : InfinitePlace K // w ≠ w₀} × Bool ↦
      hbd _ (contDiff_faceMapSide p.1 (if p.2 then 1 else 0)).continuous
    refine ⟨↑(B₀.toNNReal ⊔ Finset.univ.sup fun p ↦ (Bs p).toNNReal), fun s c ↦ ?_⟩
    rcases s with _ | _ | p
    · simp only [frontierCoverFamily, Sum.elim_inl, norm_zero]
      positivity
    · refine (hB₀ c).trans <| (Real.le_coe_toNNReal B₀).trans ?_
      exact_mod_cast le_sup_left
    · refine (hBs p c).trans <| (Real.le_coe_toNNReal (Bs p)).trans ?_
      exact_mod_cast le_sup_of_le_right (Finset.le_sup (f := fun q ↦ (Bs q).toNNReal)
        (Finset.mem_univ p))

  have mem_iUnion_image_liftToMixed_of_eq
      {ψ : (Fin (Fintype.card (InfinitePlace K) - 1) → ℝ) → realSpace K}
      {c' : Fin (Fintype.card (InfinitePlace K) - 1) → ℝ} (hc' : c' ∈ Icc (0 : _) 1)
      {x : mixedSpace K} (hx : normAtAllPlaces x = ψ c') :
      x ∈ ⋃ ε : {w : InfinitePlace K // IsReal w} → Bool, liftToMixed ψ ε '' Icc 0 1 := by
    choose θ hθmem hθeq using fun w : {w : InfinitePlace K // IsComplex w} ↦
      exists_phase_mem_Icc_mul_exp (x.2 w)
    set ε : {w : InfinitePlace K // IsReal w} → Bool := fun w ↦ decide (0 ≤ x.1 w) with hε
    set c : Fin (Module.finrank ℚ K - 1) → ℝ :=
      fun k ↦ Sum.elim c' θ (mixedCubeEquiv k) with hc
    have hproj : (fun i ↦ c ((mixedCubeEquiv).symm (Sum.inl i))) = c' := by
      funext i
      simp [hc]
    have hck : ∀ k, c k ∈ Icc (0 : ℝ) 1 := fun k ↦ by
      change Sum.elim c' θ (mixedCubeEquiv k) ∈ Icc (0 : ℝ) 1
      rcases mixedCubeEquiv k with i | w
      · exact ⟨hc'.1 i, hc'.2 i⟩
      · exact hθmem w
    refine Set.mem_iUnion.mpr ⟨ε, c, ⟨fun k ↦ (hck k).1, fun k ↦ (hck k).2⟩, ?_⟩
    simp only [liftToMixed]
    rw [hproj]
    have hcph : ∀ w : {w : InfinitePlace K // IsComplex w},
        c ((mixedCubeEquiv).symm (Sum.inr w)) = θ w := fun w ↦ by rw [hc]; simp
    have hmodreal : ∀ w : {w : InfinitePlace K // IsReal w}, ψ c' w.1 = |x.1 w| := fun w ↦ by
      rw [← hx, normAtAllPlaces_apply, normAtPlace_apply_of_isReal w.2, ← Real.norm_eq_abs]
    have hmodcplx : ∀ w : {w : InfinitePlace K // IsComplex w}, ψ c' w.1 = ‖x.2 w‖ :=
      fun w ↦ by rw [← hx, normAtAllPlaces_apply, normAtPlace_apply_of_isComplex w.2]
    refine Prod.ext (funext fun w ↦ ?_) (funext fun w ↦ ?_)
    · simp only [hε, hmodreal w]
      by_cases hpos : 0 ≤ x.1 w
      · rw [decide_eq_true hpos, if_pos rfl, one_mul, abs_of_nonneg hpos]
      · rw [decide_eq_false hpos, if_neg (by simp), abs_of_neg (not_le.mp hpos)]
        ring
    · simp only [hcph w, hmodcplx w]
      exact hθeq w

  have frontier_normLeOne_subset_iUnion_image_liftToMixed_aux :
      frontier (normLeOne K) ⊆
        ⋃ p : (Unit ⊕ Unit ⊕ ({w : InfinitePlace K // w ≠ w₀} × Bool)) ×
          ({w : InfinitePlace K // IsReal w} → Bool),
          liftToMixed (frontierCoverFamily p.1) p.2 '' Icc 0 1 := by
    have hfrontier : frontier (normLeOne K) ⊆
        normAtAllPlaces ⁻¹' frontier (normAtAllPlaces '' normLeOne K) := by
      conv_lhs => rw [normLeOne_eq_preimage_image K]
      exact (continuous_normAtAllPlaces K).frontier_preimage_subset _
    refine hfrontier.trans ?_
    refine (Set.preimage_mono (frontier_subset_frontierCoverFamily)).trans ?_
    rw [Set.preimage_iUnion]
    refine Set.iUnion_subset fun s ↦ ?_
    rintro x ⟨c', hc', hxeq⟩
    obtain ⟨ε, hε⟩ := Set.mem_iUnion.mp
      (mem_iUnion_image_liftToMixed_of_eq (ψ := frontierCoverFamily s) (c' := c')
        (hc' := hc') (x := x) (hx := hxeq.symm))
    exact Set.mem_iUnion.mpr ⟨(s, ε), hε⟩

  have normLeOne_frontier_lipschitz_cover_mixedSpace :
      ∃ (m : ℕ) (M : ℝ≥0)
        (φ : Fin m → (Fin (Module.finrank ℚ K - 1) → ℝ) → mixedSpace K),
        (∀ j, LipschitzWith M (φ j)) ∧
          frontier (normLeOne K) ⊆ ⋃ j, φ j '' Icc 0 1 := by
    obtain ⟨M₀, hM₀⟩ := exists_lipschitzWith_frontierCoverFamily
    obtain ⟨B, hB⟩ := exists_bound_frontierCoverFamily
    set S := (Unit ⊕ Unit ⊕ ({w : InfinitePlace K // w ≠ w₀} × Bool)) ×
      ({w : InfinitePlace K // IsReal w} → Bool)
    set Φ : S → (Fin (Module.finrank ℚ K - 1) → ℝ) → mixedSpace K :=
      fun p ↦ liftToMixed (frontierCoverFamily p.1) p.2
    set e := Fintype.equivFin S
    refine ⟨_, M₀ + (B * (2 * Real.pi)).toNNReal, fun j ↦ Φ (e.symm j),
      fun j ↦ lipschitzWith_liftToMixed (hψ := hM₀ _) (hB := hB _) (ε := _), ?_⟩
    rw [e.symm.surjective.iUnion_comp fun p ↦ Φ p '' Icc 0 1]
    exact frontier_normLeOne_subset_iUnion_image_liftToMixed_aux

  have normLeOne_frontier_lipschitz_cover_index :
      ∃ (m : ℕ) (M : ℝ≥0)
        (φ : Fin m → (Fin (Fintype.card (index K) - 1) → ℝ) → (index K → ℝ)),
        (∀ j, LipschitzWith M (φ j)) ∧
          frontier ((mixedEmbedding.stdBasis K).equivFunL '' (normLeOne K)) ⊆
            ⋃ j, φ j '' Icc 0 1 := by
    obtain ⟨m, M, φ, hφ, hcov⟩ := normLeOne_frontier_lipschitz_cover_mixedSpace
    set Φ : mixedSpace K ≃L[ℝ] (index K → ℝ) := (mixedEmbedding.stdBasis K).equivFunL
    set g : Fin (Fintype.card (index K) - 1) ≃ Fin (Module.finrank ℚ K - 1) := finCongr (by
      rw [← Module.finrank_eq_card_basis (mixedEmbedding.stdBasis K), mixedEmbedding.finrank])
    refine ⟨m, ‖(Φ : mixedSpace K →L[ℝ] (index K → ℝ))‖₊ * (M * 1),
      fun j c ↦ Φ (φ j (fun a ↦ c (g.symm a))),
      fun j ↦ (Φ : mixedSpace K →L[ℝ] (index K → ℝ)).lipschitz.comp ((hφ j).comp
        (IsometryEquiv.piCongrLeft' (Y := fun _ ↦ ℝ) g).isometry.lipschitz), ?_⟩
    rw [← Φ.coe_toHomeomorph, ← Φ.toHomeomorph.image_frontier]
    refine (Set.image_mono hcov).trans ?_
    rw [Set.image_iUnion]
    refine Set.iUnion_subset fun j ↦ ?_
    rintro _ ⟨_, ⟨c, hc, rfl⟩, rfl⟩
    exact Set.mem_iUnion.mpr ⟨j, ⟨fun a ↦ c (g a), ⟨fun a ↦ hc.1 _, fun a ↦ hc.2 _⟩, by
      simp⟩⟩
  obtain ⟨mc, M, φ, hφ, hcovraw⟩ := normLeOne_frontier_lipschitz_cover_index
  have hcov : ∃ (mc : ℕ) (M : ℝ≥0) (φ : Fin mc → (Fin (Fintype.card (index K) - 1) → ℝ) →
      (index K → ℝ)), (∀ j, LipschitzWith M (φ j)) ∧
      frontier (Φ '' (normLeOne K)) ⊆ ⋃ j, φ j '' Set.Icc 0 1 := ⟨mc, M, φ, hφ, hcovraw⟩
  choose C hLC using fun p : Finset {w : InfinitePlace K // IsReal w} × (index K → ZMod m) ↦
    exists_card_residue_fibre_sub_mul_rpow_le_explicit m hm b J T hT hcov p.1 p.2
  let L : Finset {w : InfinitePlace K // IsReal w} × (index K → ZMod m) → ℝ := fun p ↦
    if (∃ a : idealSet K J,
        (Finset.univ.filter (fun w : {w : InfinitePlace K // IsReal w} ↦
          (a : mixedSpace K).1 w < 0) = p.1) ∧
        ((fun i ↦ (round ((T.symm ((mixedEmbedding.stdBasis K).equivFunL
          (a : mixedSpace K))) i) : ZMod m)) = p.2) ∧
        ((intNorm (idealSetEquiv K J a).val : ZMod m) = (b : ZMod m)))
      then MeasureTheory.volume.real
        ((mixedEmbedding.stdBasis K).equivFunL '' (normLeOne K) ∩
          {y : index K → ℝ | (∀ w ∈ p.1, y (Sum.inl w) ≤ 0) ∧
            (∀ w ∉ p.1, 0 ≤ y (Sum.inl w))})
        / |LinearMap.det (((LinearEquiv.smulOfNeZero ℝ (index K → ℝ) (m : ℝ) hm).trans T
          : (index K → ℝ) ≃ₗ[ℝ] (index K → ℝ)) :
            (index K → ℝ) →ₗ[ℝ] (index K → ℝ))|
      else 0
  refine ⟨(∑ p, L p) * NJ, (∑ p, |C p|) * (NJ : ℝ) ^ (1 - (d : ℝ)⁻¹), fun N hN ↦ ?_⟩
  have hNN1 : 1 ≤ ((N * NJ : ℕ) : ℝ) := by
    rw [Nat.one_le_cast]
    exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (Nat.one_le_iff_ne_zero.mp hN) hNJ.ne')
  have hbase := card_residue_sum_bound_aux m b J T ((N * NJ : ℕ) : ℝ) hNN1 L (fun p ↦ |C p|)
    (fun p tN htN ↦ (hLC p tN htN).trans (by gcongr; exact le_abs_self _))
  rw [show (∑ p, L p) * NJ * (N : ℝ) = (∑ p, L p) * ((N * NJ : ℕ) : ℝ) by push_cast; ring]
  refine hbase.trans (le_of_eq ?_)
  rw [Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg N) (Nat.cast_nonneg NJ),
    mul_comm ((N : ℝ) ^ _) ((NJ : ℝ) ^ _), ← mul_assoc]

end Chebotarev
