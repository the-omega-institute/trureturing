/- GID: D5/S3/Zeros/GRH/New/Filling/LinkPairing
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/Filling/LinkPairing
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.Filling.LinkPairing. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Filling/LinkPairing.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.New.Filling.BoxPartition
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Incoherent and degenerate pairs are negligible (see New.Filling.CrudeEnergy).

This file: Bordered determinant bounds the discriminant of the lattice of lifts of a link.
Discriminant gain for congruent terms with differing links, via lattices of lifts. -/
seal Finset.univ Finset.sum Finset.prod

open Fin Module Equiv Fintype MatMul Matrix Pointwise Submodule Sum

namespace Filling

variable {E} [Field E] [CMType E] {𝔰} {S : Filling E 𝔰} {c c' j} {γ :
  S.G E} {τ : Type}

section

attribute [local simp] paddedLeading forall_fin_succ' init is_le IsHermUnit.conjTranspose_eq
  Matrix.map_add mulVec Matrix.mul_apply
  Units.smul_def abs_norm_eq_prod_norm_sq dotProduct leadingMinor mul_pow

/-- Let γ have level j. The Gram matrix of (e_a for a ≤ ϱ; γe_a for a ≤ j; e*_a for a > j; z;
γz), with N added on the diagonal at the last three groups, has determinant of absolute norm
(N^(2f)·`Filling.minorNorm` j γ)². -/
lemma HasLevel.abs_norm_bordered_det (h :
  S.HasLevel j γ) : let r := sumCompl (@val _ · < j); let m := isotropicFramePair γ
    let f := .map r (r ∘ inl); let s := (diagonal 1).submatrix id (inr ∘ inr ∘ r ∘ inr)
      let p := (framePair γ).submatrix id (.map (fun () ↦ 𝔰.top) fun () ↦ 𝔰.top); let P :=
          ((m.submatrix id f).fromCols
          (s.fromCols p)); let M := Pᴴ * S.ratGram * P + fromBlocks 0 0 0 ((S.N : E) • 1)
          genIndex (finAdeleMat M).det = (S.N ^ (2 * numInfPlaces E) * S.minorNorm j γ) ^ 2 := by
  intro r _ _ _ _ P M; let A :=
    (paddedLeading j (S.frameProducts γ⁻¹)).updateRow 𝔰.top (S.frameProducts γ⁻¹ 𝔰.top)
  erw [← RingHom.map_det, ← (?_ : |↑(Algebra.norm ℚ A.det)| = _ * _)]
  · let g := finSuccEquivLast.trans (r.symm.optionCongr.trans (optionEquivSumPUnit _))
    have d := M.det_reindex_self ((sumAssoc ..).symm.trans (((sumAssoc ..).sumCongr
      (.refl _)).trans (sumSumSumComm ..))) ▸ det_permute (sumComm ..) _
    rw [(Matrix.ext (Sum.rec (Function.swap (Sum.rec ?_ fun _ _ ↦ by rfl)) ?_) : submatrix _ _ _ =
      fromBlocks (reindex g g A) (of _) 0 (reindex g g Aᴴ))] at d
    · simpa [sq] using congr(|(Algebra.norm ℚ $d.symm : ℝ)|)
    all_goals simp +zetaDelta [splitGram, middleGram, frameGram, apply_ite star]; grind
  cases' j using lastCases with j
  · simp [show A = S.frameProducts γ⁻¹ by simp [A, ← ext_iff], minorNorm, field]
  choose w e using h.inv.exists_shared_frame_vector j.le_last
  erw [← cramer_transpose_apply, ← det_smul_inv_vecMul_eq_cramer_transpose _ _
    (by simpa [↓det_paddedLeading] using h.inv.2.1),
    Pi.smul_apply, congr($det_paddedLeading • $(frameProducts_mulVec_of_frameImage_eq e) _)]
  obtain ⟨⟩ := (congr(‖Φ · $(star_mul_last_eq_of_frameImage_eq
    e)‖)), congr(diag $h.inv.paddedLeading_mul_inv 𝔰.top)
  simp_all [tsub_eq_zero_of_le, ← sq, minorNorm, ← conjTranspose_submatrix, j.le_last.not_gt]; ring

/-- Let γ have level j, k = h_c⁻¹γh_c' ∈ K, and w = i(k)·i(k⁻¹)·`Filling.saturationIndex` k with i =
`Filling.xRowsIndex` j. Then w ≠ 0, and for each basis v of link γ some v·e satisfies
`Filling.HasIntegralLifts` with `Filling.linkDiscSq`(v,e)·w² ≤ (`Filling.minorNorm` j γ)². -/
lemma exists_lifts_linkDiscSq_le [StablyUnram E] [Fintype τ]
    {t} (hk : γ ∈ S.termsOver c t c') (hj : S.HasLevel j γ) {v :
  Matrix _ τ E} (hv : HasLeftInv v) (hL : colSpan v = link γ) : let k := S.termPosition c c' γ
  let w : ℝ := S.xRowsIndex j k * S.xRowsIndex j k⁻¹ * S.saturationIndex k
  ∃ e, HasIntegralLifts c γ (finAdeleMat v * e.1) ∧ S.linkDiscSq v e * w ^ 2 ≤ S.minorNorm j γ ^ 2 ∧
    w ≠ 0 := by
  intro k; obtain ⟨hD, D, _, l, _⟩ := hj.abs_norm_bordered_det, hj.minorNorm_pos.ne',
    isIntMatrix_framePair (termsOver.isIntMatrix_termPosition hk), id hv
  extract_lets r m f s p P M at hD
  obtain ⟨u, ⟨h₇, h₈⟩, h₉⟩ := by simpa [fromRows_ext_iff, -Matrix.mul_assoc] using
    (exists_mul_eq_of_col_mem_range (x := ((mᴴ * S.ratGram).fromRows (linkMatrix γ)).fromRows
    (sᴴ * S.ratGram)) (y := (fromRows 0 (fromCols 0 v)).fromRows (fromCols (diagonal 1) 0)) fun b ↦
    (mem_map.1 (hL.le ⟨_, congr($(v.mul_fromCols 0 1)ᵀ b)⟩)).elim fun t ⟨a, e⟩ ↦ by
    choose _ x _ o using exists_frameImage_eq_of_isNormalForm hj.1.inv (snoc ((fromRows 0
      (fromCols 1 0) · b) ∘ r.symm - t ∘ inl) 0); use t + frameImage 1 *ᵥ ite (j ≤ 𝔰.ϱ) x 0
    obtain ⟨⟩ := star_mul_last_eq_of_frameImage_eq o, frameImage_mulVec _ x ▸ o.symm
    rw [mulVecLin_apply, fromRows_mulVec, fromRows_mulVec, ← mulVecLin_apply,
      isotropicFramePair_mulVec_eq_zero_iff.2] <;> split
      <;> simp_all [s, r, frameImage_one_mulVec, funext_iff, -mulVec, mulVec.eq_1 (_ * _)]; omega)
  choose a e z hn using exists_isPrimitiveMatrix_mul_fromBlocks (S.classCoord c * finAdeleMat u)
    ⟨finAdeleMat ((sᴴ * S.ratGram).fromRows
    (l * linkMatrix γ)) * (classBasis c).1, by simp [classCoord, ← Matrix.map_mul, *]⟩
  use e, ⟨_, _, _, of _, h₇, (hn.1 · <| inr ·), by ext; simp [*]⟩
  obtain ⟨g : (S.latMiddle (𝔸f E)).splitGram.submatrix 𝔰.besselFrame id * isotropicFramePair k =
    fromCols 0 (xRows ((S.latMiddle _).frameGram ↑k⁻¹))ᴴ, q, o⟩ := by simp [↓frameGram_inv,
    frameGram, ← ext_iff], congr($(classCoord_gram c m u) * a.1.fromBlocks z 0 e.1),
    xRows_conjTranspose_mul_eq (n :=
    u.toCols₁) congr(toCols₁ $h₇) (by simpa using! congr(zFormPair (S.ratMiddle E) * toCols₁ $h₈))
  rw [Matrix.mul_assoc, h₇, classCoord_mul_isotropicFramePair] at q; let F :=
    (isotropicFramePair k).submatrix id f
  choose hs b using jacobi_perp_discriminant (F := F) (N :=
    finAdeleMat M) S.isUnimodular_latMiddle.splitGram (by tauto) hn (congr(submatrix $q f _).trans
    (by simp)) (by simp [← card_congr r, hL ▸ card_eq_finrank_colSpan hv, finrank_link]; lia)
    (S.classCoord c * finAdeleMat (s.fromCols p)) (principalIdele (.mk0 S.N (by simp))) (by
    unfold F; erw [← classCoord_mul_isotropicFramePair, ← mul_fromCols, ← fromCols_map,
      classCoord_gram c P P]; simp [M]) (by simp [*])
  let Q := (sᴴ * S.ratGram).fromRows (pᴴ * S.ratGram) * u
  rw [hD, gram_mul, genIndex_det_conj, (?_ : _ * _ = RingHom.mapMatrix _ (uᴴ * S.ratGram * u +
    (S.N⁻¹ : E) • Qᴴ * Q)), (?_ : _ + _ = fromBlocks ((S.N⁻¹ : E) • 1) 0 0 (vᴴ * S.linkMetric * v)),
    ← RingHom.map_det, genIndex_algebraMap] at b; simp [genIndex_natCast] at b
  simp [s, r, linkMatrix, ← ext_iff, -Subtype.forall] at h₈ h₉
  have I := submoduleIndex_colLattice_intVectors (M :=
    a) fun b d ↦ by simpa [classCoord_eq_fromBlocks, h₉] using hn.1 (inl b) (inl d)
  obtain ⟨d₁, h₄⟩ := @ne_zero_and_le_of_dvd (S.xRowsIndex j k) _ (mod_cast I ▸ (genIndex_pos
    a.det).ne') (submoduleIndex_dvd_of_le (mulVecBilin
    ℕ _ _ ∘ₗ mulVecBilin ℕ _ (-(finAdeleMat u).submatrix (inl ·.1) inl)) (colLattice_le (⟨_,
    fun _ ↦ by simpa [classCoord_eq_fromBlocks] using hn.1 (inl _) <| inl ·, rfl⟩)) (colLattice_le
    (r.surjective.forall.2 (Sum.rec (mem_sup_right <| col_mem_colLattice ·) fun b ↦ mem_sup_left ⟨_,
    single_mem_intVectors b, by simpa [k, r, *, funext_iff, frameGram_termPosition, ← r.sum_comp,
    add_eq_zero_iff_eq_neg'] using congr((finAdeleMat $o)ᵀ b)⟩)))),
    @ne_zero_and_le_of_dvd (S.xRowsIndex j k⁻¹ * S.saturationIndex k) (submoduleIndex
    (intVectors ..) (preimageLattice (Ô E) F)) (by simp [·, D] at b) (by
    grw [show xRowsIndex .. ∣ submoduleIndex (colLattice _ F) (colLattice _ (isotropicFramePair
      k)) from submoduleIndex_dvd_of_le (mulVecBilin ℕ _ _) (colLattice_le
      (congr($gᵀ _ ∈ colLattice ..).ge <| ·.rec (fun _ ↦
      zero_mem _) col_mem_colLattice)) (colLattice_le (mem_sup_left ⟨_, col_mem_colLattice <|
      inr ·, congr($gᵀ (inr _))⟩)), saturationIndex, AddSubgroup.relIndex_mul_relIndex]
    exacts [submoduleIndex_dvd_of_le _ (by tauto) fun x ⟨h, r, e⟩ ↦ mem_sup_left ((hs x (by
      simpa [← e] using congr($qᴴ *ᵥ r))).imp (by simp_all [preimageLattice])), colLattice_le
      (col_mem_colLattice <| f ·), le_inf (colLattice_le (by tauto)) LinearMap.map_le_range])
  use ?_, by simp_all
  grw [mul_assoc, linkDiscSq, d₁.2, ← Nat.cast_mul, h₄.2, I]
  exact (mul_left_cancel₀ (by simp) (.trans (by simp; field) b)).le
  simp_rw [linkMetric, Q, p,
    framePair_last_eq_zFormPair_mul]; generalize zFormPair (S.ratMiddle E) = L
  simp [*, fromBlocks_smul, ← ext_iff,
    ← by simpa [← two_smul E, *] using gram_linkMatrix_mul h₇ h₇ 2⁻¹ (-2⁻¹)]
  simp [Q, finAdeleMat_conjTranspose, map_splitGram_ratMiddle, ← classCoord_conj_splitGram c]

end

attribute [-simp] fromBlocks_map

variable {S : Filling E 𝔰} {c : S.Classes} {γ : S.G E} {m}

lemma HasIntegralLifts.exists_isIntMatrix c' : HasIntegralLifts c γ
  m → let k := S.termPosition c c' γ; let T := S.latMiddle (𝔸f E); ∃ n : Matrix 𝔰.BesselIndex
      τ _, IsIntMatrix (Ô E) n ∧ zFormPair T * linkMatrix k * n = finAdeleMat (zFormPair
      (S.ratMiddle E)) * m ∧ (isotropicFramePair k)ᴴ * T.splitGram * n = 0 ∧ ∀ p, m.toRows₁ =
      fromRows p 0 → n.toRows₂.toRows₁ = S.classCoordX₀ c * p | ⟨_, _, _, w, a, i, e⟩ => ⟨_, i, by
  simp_rw [← framePair_last_eq_zFormPair_mul, isotropicFramePair, ← classCoord_mul_framePair,
    ← Matrix.mul_assoc _ _ w]; erw [classCoord_gram, framePair_last_eq_zFormPair_mul,
    classCoord_gram, a]
  simp +contextual [← e, ← ext_iff, classCoord_eq_fromBlocks, linkMatrix, mul_apply]⟩

variable [StablyUnram E] [Fintype τ]

variable {c' : S.Classes} {γ : S.G E} {j : Fin (𝔰.ϱ + 1 + 1)} {s x} {m : Matrix _ τ _} (hs :
  S.Agrees s)
  (h : γ ∈ S.termsOver c s c') (hc : S.HasLevel j γ) (hq : S.FixesNormAtLeast s x) {γ' : S.G E}

/-- Let m, y be rational with columns orthogonal for `Filling.linkMetric`, and let the columns of
(m | y)f be lifts of γ,
f invertible adelic. Then for some adelic z and invertible a, v, the columns of ma and mz + yv are
lifts, and the squared discriminants multiply: linkDiscSq(m,a)·linkDiscSq(y,v) = linkDiscSq((m | y),
f). -/
lemma HasIntegralLifts.exists_orthogonal_split {s} {y : Matrix _ (Fin s) E} {f} (o :
  mᴴ * S.linkMetric * y = 0) : HasIntegralLifts c γ (finAdeleMat (fromCols
  m y) * f.1) → ∃ᵉ (a) (v) (z : Matrix τ _ (𝔸f E)), HasIntegralLifts c γ (finAdeleMat m * a.1) ∧
  HasIntegralLifts c γ (finAdeleMat m * z + finAdeleMat y * v.1) ∧ S.linkDiscSq m a * S.linkDiscSq y
  v = S.linkDiscSq (fromCols m y) f := fun ⟨_, _, t, u, p, q, k⟩ ↦ by
  choose a v z h using exists_isPrimitiveMatrix_mul_fromBlocks _ ⟨_, f.3⟩
  have T {ι} g : HasIntegralLifts (τ := ι) c γ _ := ⟨_, _, t, _, p, ((Matrix.mul_assoc _ u _ ▸ q.mul
    h.1) · <| g ·), congr(submatrix $(Matrix.mul_assoc ..) _ g).symm⟩
  simp [↓k] at T
  use a, v, z, T .inl, T .inr, (isPrimitiveMatrix_iff.1 h).elim fun V ⟨i,
    e⟩ ↦ by simp [linkDiscSq, o, field, by simpa [genIndex_det_eq_one _ _ i,
    IsAdelic.exists_topology] using congr(genIndex (f * $e).det)]

omit [StablyUnram E] in
/-- If γ has level j, its link contains a pair (a − z, yz) with a in X₀ and y in E such that
𝗀(γ) = D_j D̄_j(1 − yȳ), D_j the leading minor of Z(γ). -/
lemma HasLevel.exists_mem_link_termDisc_eq (h : S.HasLevel j γ) : ∃ a y,
  (a ⊕ᵥ -1 ⊕ᵥ (0 ⊕ᵥ y) : _ → E) ∈ link γ ∧ S.termDisc γ = leadingMinor
  (S.frameProducts γ) j * star (leadingMinor (S.frameProducts γ) j) * (1 - star (y ()) * y ()) := by
  refine .elim ?_ fun x (h : _ ∧ _) ↦ ⟨(frameImage γ *ᵥ x) ∘ 𝔰.indexX₀, _,
    mem_link.2 ⟨init x, by erw [← frameImage_one_mulVec, ← frameImage_mulVec]; use h.1⟩, h.2⟩
  cases j using lastCases
  choose y e _ using exists_mulVec_eq_single_det (S.frameProducts γ)
  cases norm_sq_middle_part_eq e rfl
  use (S.N / (S.frameProducts γ).det) • y, by simp_all [HasLevel, funext_iff, leadingMinor]; grind
  simp_all [HasLevel, frameDisc, leadingMinor, field]
  choose y x hx e using exists_frameImage_eq_of_isNormalForm h.1.inv (-1)
  use y; rw [frameImage_mulVec, star_mul_last_eq_of_frameImage_eq e, e, frameImage_mulVec]
  simpa [funext_iff, frameImage_one_mulVec, hx, is_le, ← not_le] using h.2.2

lemma one_le_xRowsIndex_and_saturationIndex (h : γ ∈ S.termsOver c s c') (hc : S.HasLevel j γ) : 1 ≤
  S.xRowsIndex j (S.termPosition c c' γ) ∧ 1 ≤ S.saturationIndex (S.termPosition c c' γ) ∧ 0 <
  S.classGauge j c c' γ := (exists_basis_matrix _).choose_spec.elim (exists_lifts_linkDiscSq_le h
  hc) |>.elim (by simp_all [classGauge, hc.minorNorm_pos, ← not_lt, zero_lt_iff])

include hs h hc hq

/-- Let γ have level j over (c, s, c'), s agreeing, `Filling.FixesNormAtLeast` s x;
y be r vectors of link γ
independent modulo X₀²; w satisfy `Filling.HasIntegralLifts` with w ≡ yv modulo X₀². Then r ≤ 1 +
(j−ϱ)₊ and (x'D)² ≤ `Filling.linkDiscSq`(y,v)·max(∏_v|𝗀(γ)|_v, N^fD)², D = `Filling.minorNorm` j γ;
x' = x if j > ϱ and the premise of hp (forcing r maximal) holds, else 1. -/
lemma minorNorm_sq_le_linkDiscSq_mul {r i w} (y : Matrix _ (Fin r) E) v (hp : i = 0 → finrank
  E ↥(link γ ⊓ (zFormPair (S.ratMiddle E)).mulVecLin.ker) + r = finrank E (link γ)) (hy : colSpan
  y ≤ link γ) (hi : HasLeftInv (zFormPair (S.ratMiddle E) * y)) (hl : HasIntegralLifts c γ w) (o :
  finAdeleMat (zFormPair (S.ratMiddle E)) * w = finAdeleMat (zFormPair (S.ratMiddle E) * y) * v.1) :
  r ≤ 1 + (j - 𝔰.ϱ) ∧ ite (𝔰.ϱ < j ∧ i = 0) x 1 ^ 2 * S.minorNorm j γ ^ 2 ≤
  S.linkDiscSq y v * (S.termDiscNorm γ ⊔ S.N ^ numInfPlaces E * S.minorNorm j γ) ^ 2 := by
  obtain ⟨⟨⟨_, K⟩, rfl, rfl⟩, ⟨n, I, e, q, -⟩, D, ⟨ρ, hρ⟩, C, ⟨a, u, f, l⟩, a', u', ⟨t⟩, -⟩ :=
    h, hl.exists_isIntMatrix c', hc.minorNorm_pos, not_forall.1 (minors_eq_zero_iff.1 ·
    (mulVec_injective_iff.1 hi.mulVec_injective)), hc.2,
    hc.exists_mem_link_termDisc_eq, hc.inv.exists_mem_link_termDisc_eq
  let ε := (of ((fun () ↦ a ⊕ᵥ -1 ⊕ᵥ (0 ⊕ᵥ u)) ⊕ᵥ fun () ↦ 0 ⊕ᵥ u' ⊕ᵥ (a' ⊕ᵥ -1)))ᵀ
  have ε₁ : colSpan ε ≤ link γ := by simpa [↓range_mulVecLin, span_insert, ε, f] using ⟨γ *ᵥ t, by
        simp_all [funext_iff, ↓SetLike.mem_coe]⟩
  have ε₂ {τ w} [Fintype τ] h := have := gram_linkForm_eq_zero_of_le_link (σ := τ) (u := w) ε₁ h
    show εᴴ * S.linkMetric * w = zFormPair (S.ratMiddle E) *
      w by simp [← ext_iff, ε, middleGram, linkMetric, mul_apply] at this ⊢; grind
  have k : zFormPair (S.ratMiddle E) * ε = (S.N : E) • fromBlocks 1 (-diagonal u)ᴴ
    (-diagonal u) 1 := by simpa [← ext_iff, ε, mul_apply, middleGram, add_neg_eq_zero, mul_comm,
    Unique.forall_iff] using congrFun₂ (gram_linkForm_eq_zero_of_le_link ε₁ ε₁) (.inl ()) (.inr ())
  have p : ρ.Injective := fun _ _ _ ↦ by_contra (hρ <| det_zero_of_row_eq · (by aesop))
  let g h := Equiv.ofBijective ρ (p.bijective_of_nat_card_le h)
  apply S.isUnimodular_latMiddle.splitGram.isIntMatrix.mul at I; simp_rw
    [← framePair_last_eq_zFormPair_mul, Matrix.mul_assoc, o, ← ε₂ hy] at e q
  have' L := liouville_gram linkMetric_posDef (ε.submatrix id ρ) y 1 v (ε₂ hy ▸ hρ) _ _
  erw [submatrix_mul_equiv (εᴴ * S.linkMetric) ε ρ (.refl _)] at L
  nth_grw 1 [linkDiscSq, termDiscNorm, L]
  obtain _ | _ | r := r; iterate 2 grw [← le_max_right]; swap
  grw [← S.N_prime.one_le]; simp
  cases h : ρ 0 <;> simp [*, abs_norm_eq_prod_norm_sq] <;> linear_combination
  erw [det_submatrix_equiv_self (g (by simp))] at *
  grw [← le_max_left]
  simpa [*, minorNorm, j.is_le.antisymm (C.2.2 fun _ ↦ by simp_all [← not_lt]),
    abs_norm_eq_prod_norm_sq, field, Finset.prod_pow, pow_mul] using card_le_of_injective ρ p
  positivity
  erw [conjTranspose_one, one_mul, ← congr(det (submatrix $e ρ id))]
  split; choose _ _ _ a b _ using exists_basis_extend_ker (by rw [k]; simp_all) ε₁
  use (le_genIndex_det_of_fixesNormAtLeast hs I rfl q
    (g (by simp_all [← b ▸ card_eq_finrank_colSpan a]; omega)) · hq)
  exact_mod_cast one_le_genIndex (IsIntMatrix.det_mem fun _ _ ↦
    (isIntMatrix_framePair K.isIntMatrix).isInt_conjTranspose.mul I _ _)

/-- Let γ have level j over an agreeing s with `Filling.FixesNormAtLeast` s x. Then link γ ∩ link γ'
has codimension i in link γ, |κ| ≤ dim T° + i + (j−ϱ)₊ (T° = `commonLink` γ γ'),
and a lifting complement (y,v) has
(`Filling.pairInvariant`·x')²·`Filling.linkDiscSq`(y,v) ≤ `Filling.classGauge`²; x' = x if j > ϱ, i
= 0, else 1. -/
lemma exists_link_split_le_classGauge γ' : (0 < S.latticeDisc c (commonLink γ γ') ∧ 1 ≤
  S.frameValueIndex c (S.termPosition c c' γ) 1 (commonLink γ γ')) ∧ ∃ᵉ (i) (ρ) (_ : Fintype ρ) (m :
  Matrix _ ρ E) (y : Matrix _ (Fin i) E) (v) (z : Matrix ρ _ (𝔸f E)), let L := link γ ⊓ link γ'; i =
    𝔰.k + 1 - finrank E L ∧ 𝔰.k ≤ finrank E (commonLink γ γ') + i + (j - 𝔰.ϱ) ∧ (i = 0 → L =
    link γ) ∧ colSpan m = L ∧ colSpan y ≤ link γ ∧ (∀ t, y *ᵥ t ∈ L → t = 0) ∧ colSpan (fromCols
  m y) = link γ ∧ HasIntegralLifts c γ (finAdeleMat m * z + finAdeleMat y * v.1) ∧ (S.pairInvariant
    c c' γ γ' * ite (𝔰.ϱ < j ∧ i = 0) x 1) ^ 2 * S.linkDiscSq y v ≤ S.classGauge j c c' γ ^ 2 := by
  choose m b e using
    exists_basis_matrix (link γ ⊓ link γ' ⊓ (zFormPair (S.ratMiddle E)).mulVecLin.ker)
  choose i hl using (le_inf_iff.1 e.le).imp inf_le_left.trans' mul_eq_zero_of_range_le_ker
  let p := m.toRows₁.toRows₁
  have hQ : mᴴ * S.linkMetric * m = pᴴ * p := have := gram_linkForm_eq_zero_of_le_link i i
    by simp_all [← ext_iff, linkMetric, mul_apply, p, middleGram, add_neg_eq_zero, ← two_mul]
  rw [pairInvariant, latticeDisc, frameValueIndex, one_smul,
    (by ext; simp [commonLink, ← e]; rfl : commonLink γ γ' = colSpan p)]
  choose r u _ i k l O o using
    exists_basis_extend_ker (det_gram_linkMetric_ne_zero b) (e ▸ inf_le_left)
  choose s y _ i' k' l' O' o' using
    exists_basis_extend_ker (det_gram_linkMetric_ne_zero i) (k ▸ inf_le_left)
  choose _ P q w using exists_lifts_linkDiscSq_le h hc i' k'
  choose _ v z P p₂ q₁ using P.exists_orthogonal_split O'
  choose a g _ p₃ p₄ q₂ using P.exists_orthogonal_split O
  obtain ⟨⟨_, hn, _, h₁, e'⟩, n, n₁, n₂, _⟩ := p₃.exists_isIntMatrix c', card_eq_finrank_colSpan
    (v := p) ⟨(pᴴ * p)⁻¹ * pᴴ, by simp [hQ ▸ det_gram_linkMetric_ne_zero b]⟩,
    k ▸ card_eq_finrank_colSpan i, k' ▸ card_eq_finrank_colSpan i', finrank_link γ
  specialize e' (finAdeleMat p * a.1) (by clear * - hl; simp_all [← ext_iff, mul_apply, p,
    middleGram])
  simp at n n₁ n₂
  have L (z : s = 0) := eq_of_le_of_finrank_eq inf_le_left (n₁ ▸ z ▸ n₂)
  have ⟨B, G⟩ := minorNorm_sq_le_linkDiscSq_mul hs h hc hq u g (L · ▸ n₁) (by order) (.of_ker_le_bot
    fun t _ ↦ o t (by simp_all [l _])) p₄ (by simp [← Matrix.mul_assoc, ← Matrix.map_mul, hl])
  refine (sublatticeDisc_mul_index_sq_le _ _ _ n le_rfl a (D :=
    S.linkDiscSq m a) (by simp [← genIndex_algebraMap, RingHom.map_det, linkDiscSq,
    hQ]) (by simp [linkDiscSq, hQ ▸ det_gram_linkMetric_ne_zero b, hQ, genIndex.apply_ne_zero_iff])
    (e' ▸ by tauto) fun j ↦ e' ▸ ⟨_, fun _ ↦ hn.neg _ j, congr($(xRows_conjTranspose_mul_eq h₁
    (by simp [*, ← Matrix.mul_assoc, ← Matrix.map_mul]))ᵀ j)⟩
    ).elim fun X Y ↦ ⟨Y, s, _, _, _, y, v, z, by omega, by omega, L, k, l', k ▸ o', k', p₂, ?_⟩
  unfold linkDiscSq at *; grw [← mul_le_mul_iff_left₀ (pow_pos hc.minorNorm_pos 2), mul_pow,
    mul_right_comm (_ ^ 2), mul_assoc, G, ← q, ← q₁, ← q₂, mul_pow, X,
    classGauge]; apply le_of_eq; clear * - w; grind-linarith

/-- For γ, γ' of level j over one agreeing s with `Filling.FixesNormAtLeast` s x, some i has
|κ| ≤ dim T° + i + (j−ϱ)₊ (T° = `commonLink` γ γ'), is 0
only for equal links, and P(γ,γ')P(γ',γ)x'² ≤ (2/g)^(2if)·G(γ)G(γ') (P = `Filling.pairInvariant`,
G = `Filling.classGauge` j c c'); x' = x if j > ϱ and i = 0, else 1. -/
lemma pairInvariant_mul_le (h' : γ' ∈ S.termsOver c s c') (hd : S.HasLevel j γ') : ∃ i, 𝔰.k ≤
  finrank E (commonLink γ γ') + i + (j - 𝔰.ϱ) ∧ (i = 0 → link γ = link γ') ∧
  S.pairInvariant c c' γ γ' * S.pairInvariant c c' γ' γ * (if 𝔰.ϱ < j ∧ i = 0 then x else 1) ^ 2 ≤
  (2 / S.g) ^ (2 * i * numInfPlaces E) * (S.classGauge j c c' γ * S.classGauge j c c' γ') := by
  obtain ⟨⟨-, _, _, _, _, y, v, z, rfl, r, _, e, e₆, -, e₇, ⟨_, _, _, w, a, i, k⟩, h₉⟩, -, _, _, _,
    _, y', v', _, rfl, -, _, _, y₂, h₇, -, ⟨_, _, _, u, b, l, k'⟩, h₉'⟩ :=
    exists_link_split_le_classGauge hs h hc hq γ',
    inf_comm (link γ) _ ▸ exists_link_split_le_classGauge hs h' hd hq γ
  exists _, r, by grind
  let Q := diagonal (S.linkForm.diag / S.linkMetric.diag)
  have L := by simpa [Matrix.mul_assoc _ _ Q, y'ᴴ.mul_assoc _ S.linkForm, (by
    simp [← ext_iff, Q, linkMetric, mul_apply, diagonal_apply, middleGram]; grind :
    S.linkMetric * Q = S.linkForm ∧ Qᴴ * S.linkForm = (2 : E) ^ 2 • S.linkMetric),
    ← Matrix.mul_assoc, abs_norm_eq_prod_norm_sq, map_ofNat, ← pow_mul, -Nat.cast_mul] using
    (liouville_gram S.linkMetric_posDef ((S.g⁻¹ : E) • y) (Q * y') v v' · zero_le_one <|
    one_le_genIndex <| IsIntMatrix.det_mem ·)
  apply le_of_sq_le_sq <;> simp_rw [linkDiscSq, classGauge, termDiscNorm, abs_norm_eq_prod_norm_sq,
    mul_pow] at *
  grw [← h₉, ← h₉', ← mul_one (_ ^ 2), L (mt exists_mulVec_eq_zero_iff.2 fun ⟨t, ht, h⟩ ↦ ht (h₇ t
    ⟨mem_link_iff_orthogonal.2 (by simp [← e₇, star_mulVec_dotProduct, ← Matrix.mul_assoc, h,
    gram_linkForm_eq_zero_of_le_link _ y₂, e]), y₂ ⟨t, rfl⟩⟩))
    (by simpa [gram_linkForm_eq_zero_of_le_link e₆, gram_linkForm_eq_zero_of_le_link (γ := γ'),
    ← finAdeleMat_conjTranspose, ← Matrix.map_mul, *, ← (finAdeleMat _).mul_assoc, -Nat.cast_mul]
    using (congr($kᴴ * finAdeleMat ((S.g⁻¹ : E) • S.linkForm) * $k').subst (by
    convert ((i.isInt_conjTranspose.mul S.isUnimodular_latMiddle.splitGram.isIntMatrix).mul
      ((S.principalLevel_eq_unitaryLevel.le (mul_inv_cancel s ▸ termsOver.mul h
      (.inv h'))).2.mul l)).neg
    simpa [Matrix.map_sub, Units.smul_def, smul_sub, coe_termPosition, classCoord, gIdele,
      finAdeleMat_conjTranspose, -map_mul, map_splitGram_ratMiddle, ← classCoord_conj_splitGram c,
      fromBlocks_smul] using congr(wᴴ * finAdeleMat ($(gram_linkMatrix_mul a b ..)) * u))))]
  ring_nf; rfl
  positivity
