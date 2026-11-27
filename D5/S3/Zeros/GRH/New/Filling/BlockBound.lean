/- GID: D5/S3/Zeros/GRH/New/Filling/BlockBound
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/Filling/BlockBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.Filling.BlockBound. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Filling/BlockBound.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.New.RealPlace.OpenCellBound
import D5.S3.Zeros.GRH.New.Filling.ThinClasses
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Incoherent and degenerate pairs are negligible (see New.Filling.CrudeEnergy).

This file: Sum of inverse discriminant powers over classes and subspaces.
Colouring count of kept near frames weighted by inverse index powers. Weighted count of near
congruent pairs of terms, summed over classes, is bounded. Block amplitude bounded by a sum of sizes
over kept near terms. -/
seal Finset.univ Finset.sum Finset.prod

open AddSubgroup Module DoubleCoset ENNReal Fintype MatMul Matrix MeasureTheory Submodule

namespace Filling

variable {E : Type} [Field E] [CMType E] {𝔰 : Shape} {S : Filling E 𝔰}

/-- Under `Filling.IsAdmissible`, the sum of d^(−(k+1)), d = `Filling.latticeDisc` c T, over all
classes c and all subspaces T of X₀ of codimension s is at most #{c}·N^(−kf)·τ^(s+1), where k = |κ|
and f counts infinite places, τ = `Filling.tailScale`. -/
lemma sum_latticeDisc_inv_le [StablyUnram E]
    [ok : S.IsAdmissible] s : ∑ c, ∑' T : {T : Submodule E _ // finrank E
  T + s = 𝔰.k}, ENNReal.ofReal (S.latticeDisc c T.1 ^ (𝔰.k + 1))⁻¹ ≤ .ofReal
  (card S.Classes / S.N ^ (𝔰.k * numInfPlaces E) * S.tailScale ^ (s + 1)) := S.of_size_bounds (by
  intros; rw [mul_comm_div]; set b : ℝ := _ / _
  set f := fun _ ↦ _; let A := Kf .. ⧸ (S.latStabilizer.comap S.inclHFin).subgroupOf _
  have := Subgroup.fintypeOfIndexNeZero (Nat.cast_pos.1 (ok.le_relIndex.trans_lt' (by bound))).ne'
  have hB u : ∑ φ : A, f ⟦u * φ.out⟧ ≤ .ofReal (Nat.card A * b)
  choose g hη k hk h using fun φ : A ↦ mk_out_eq_mul stdRatPoints S.columnLevel (u * φ.out)
  let y (φ : A) := φ.out * ⟨_, S.hasFiniteType_columnLevel.1 (hk φ)⟩
  have hy φ : ↑(y φ) = φ := .trans (QuotientGroup.mk_mul_of_mem _
    (S.principalLevel_eq_unitaryLevel.le (ok.1.le (hk φ))).1) φ.out_eq
  let r φ := replicateRow Unit ((y φ).1⁻¹.1.1 𝔰.k₀); rw [← Finset.univ.tsum_subtype']
  refine (ENNReal.tsum_mul_left.trans_le
    ((mul_le_mul_right (tsum_sublatticeDisc_inv_le u s) _).trans ?_)).trans'
    (.trans (ENNReal.tsum_le_tsum fun φ ↦ ?_) (ENNReal.tsum_comm.trans_le (ENNReal.tsum_le_tsum
    fun T ↦ if h : _ + s = _ then ENNReal.tsum_mul_right.trans_le (mul_left_mono
    (tsum_inv_index_pow_le_of_congr S.piBar_mem r (fun φ _ _ ↦ (y φ).2.isIntMatrix_inv _)
    (sublatticeBasis u.1.3 T).2.1 (equivOfCardEq (by simpa)) (K := .comap (.proj ()) (_ ∙ _))
    (fun | _, ⟨_, h, rfl⟩ => mem_span_singleton_iff_exists_mul.2 ⟨_, h (), rfl⟩) _ (fun
    _ _ ↦ dvd_rfl) (𝔰.k + 1) (by simp; lia) fun B _ a h H ↦ (tsum_eq_single ⟨a, h⟩ fun ⟨b, k⟩ ↦
    absurd (Subtype.mk_eq_mk.2 (hy b ▸ hy a ▸ QuotientGroup.eq.2 (S.inclHFin_mem_latStabilizer.2
    ⟨(_ * y a).2, fun _ ↦ (by simpa [← mul_apply, mulVec, dotProduct, r] using H _ k _ h ⟨_,
    (y a).2.isIntMatrix.isInt_transpose ·, rfl⟩)⟩)))).le)) else by simp [h])))
  · grw [show genIndex _ = _ by simpa [genIndex_natCast, genIndex_pos,
      le_of_lt] using congr(√(genIndex $S.piBar_mul_star)), mul_one, ← ofReal_mul (by bound),
      ← Subgroup.index_eq_card, ← Subgroup.relIndex, ← ok.le_relIndex]
    apply ofReal_le_ofReal (le_of_pow_le_pow_left₀ (NeZero.ne 1000) (by bound) _)
    simp [div_pow, pow_mul, field, pow_right_comm _ _ 1000]
    grw [N_le, S.size_le, pow_mul S.tailScale 4 250, tailScale_pow_four, ← Shape.k,
      ← Nat.add_sub_of_le S.ϱ_le_k]
    simp [← pow_mul, ← pow_add]; gcongr; lia
  cases' inv_mem (hη φ) with η hη; let P := η.1.toLin.toLinearEquiv
  refine .trans (ENNReal.tsum_le_tsum fun ⟨T, b⟩ ↦ ?_) (tsum_comp_le_tsum_of_injective
    ((map_injective_of_injective P.injective).comp Subtype.val_injective) _)
  erw [latticeDisc, sublatticeDisc]; obtain ⟨q, ⟨V, -⟩, x, a, -, hx, e⟩ := sublatticeBasis _ T
  by_cases d : genIndex (qᴴ * q).det = 0; simp [d]
  erw [classCoordX₀, h] at V; simp [e, ← hη, isIntMatrix_middleBaseChange_mul] at V
  obtain ⟨w, p, z⟩ := sublatticeDisc_mul_index_sq_le u.1.3 _ (r φ) (P.finrank_map_eq T).symm
    (fun | _, ⟨v, rfl⟩ => ⟨_, hx.le ⟨v, rfl⟩, mulVec_mulVec ..⟩) a (by simp [e, ← genIndex_det_conj,
    finAdeleMat_conjTranspose, by simpa using U.gram_invariant η x x])
    d (by simpa [y] using (y φ).2.isIntMatrix.mul V.1) (K := .comap (.proj ()) (_ ∙ _)) (by
    simpa [r, y, ← Matrix.mul_assoc] using! V.2)
  grw [← Real.le_sqrt_of_sq_le w]; simp [*, mul_pow, P.finrank_map_eq]
  lift f to S.Classes → NNReal using Quot.ind (div_mul_cancel · _ ▸
    sum_ne_top.1 ((hB _).trans_lt coe_lt_top).ne ⟦1⟧ (by simp)) with f
  let φ g := b - f (⟦g⟧)
  have e γ a k h g : φ _ = φ g := congr(b - f $((eq ..).2 ⟨γ, a, k, h, rfl⟩)).symm
  have r : S.columnLevel ≤ rightStab φ := by simpa [LE.le] using e 1
  simp (disch := finiteness) only [← ofNNReal_finsetSum, le_ofReal_iff_toReal_le, coe_toReal] at *
  simpa [↓classIntegral_eq_classSum r, classSum_eq_sum, φ, NeZero.pos,
    ← sum_congr _ f (congrArg f ·.out_eq)] using (classIntegral_sum (K :=
    S.columnLevel) Finset.univ (fun _ : A ↦ .id ℝ) _ (fun _ ↦ ⟨(by simpa using e · · 1),
    Subgroup.isOpen_mono r S.hasFiniteType_columnLevel.2⟩) (congrFun rfl) :).le.trans'
    (mul_nonneg (by simp) (finsum_nonneg (mul_nonneg (by simp) <| by simpa [φ] using hB ·.out))))

variable [S.IsAdmissible] {c} {γ : ↥(S.G E)} {j : Fin (𝔰.ϱ + 2)} {A : Set (S.Classes × S.G E)}

section

open Norms.L2Operator

attribute [-simp] MulMemClass.coe_mul Nat.cast_mul Prod.forall Subgroup.coe_mul sup_of_le_right

attribute [local simp ←] pow_add pow_mul pow_succ'

attribute [local simp] Finset.mul_sum IsIntMatrix Matrix.mul_apply splitGram funext_iff inclMatrix
  mul_assoc mul_pow sub_mul

/-- Shared vectors of a near γ of level j are short: for b ≥ j, D_j times the e_a-coordinate of
γf applied to column b of the inverse of `Filling.paddedLeading` j Z(γ) has absolute value below
q₀^((ϱ+1)⁴)/2 at every infinite place, q₀ = `Filling.levelPrime` 0. -/
lemma HasLevel.norm_shared_vector_lt (h : S.IsNear γ ∧ S.HasLevel j γ) {u b Y} (U :
  u ∈ besselU0) (hb : ↑j ≤ b.1) (H : paddedLeading j (S.frameProducts γ) = Y) v a : 2 * ‖Φ v
  ((frameImage (u * γ).1.1 *ᵥ Y.det • Y⁻¹ᵀ b) (.inl a))‖ < S.levelPrime 0 ^ 𝔰.n ^ 4 := by
  obtain ⟨⟨w, e⟩, t : 2 ≤ S.b, y, p, q⟩ :=
    H ▸ h.2.exists_shared_frame_vector hb, by grind [thousand_le_b], h.1
  have ⟨A, hu, r⟩ :=
    (mul_right_surjective (y v)⁻¹).exists.1 (exists_norm_le_of_besselSize_le (p v).2)
  let g {z} (_ : z ∈ S.boxedPoints) := of fun k c ↦ S.basisScale v (𝔰.besselFrame k) / S.basisScale
    v (𝔰.besselFrame c) * A.1.1 (𝔰.besselFrame k) ⬝ᵥ frameVector (z v) c
  let M := S.b ^ (5 * 𝔰.n ^ 2)
  have G z h k c : ‖@g z h k c‖ ≤ M := by
    simp [g, M, basisScale_besselFrame, field] at *
    grw [show ‖_ ⬝ᵥ _‖ ≤ _ from (PiLp.norm_apply_le ..).trans (A.1.1.l2_opNorm_mulVec _),
      r, (h v).1 c, boxSize, ← one_le_abs_kappa, abs_kappa_le]; simp
    gcongr <;> nlinarith [S.ϱ_le, 𝔰.ϱ.sub_le k]
  have k := by
    simpa [det_eq_one_of_unitriangular (Z :=
      g p) fun _ _ h ↦ congr(_ * $(frameMatrix_unitriangular hu _ _ h)).trans (by
      aesop)] using ((g p).fromBlocks (-g q) 0 (Y.map (Φ v))).det_updateCol_sum (.inl a.castSucc)
  have E k : ∑ c, Φ v (w c) * g p k c = ∑ c, Φ v (Y⁻¹ c b) * g q k c := by
    convert congr(S.basisScale v (𝔰.besselFrame k) * A.1 (𝔰.besselFrame k) ⬝ᵥ (y v)⁻¹ *ᵥ (Φ v ∘ $e /
      S.basisScale v)) <;> simp [g, entrywise, Finset.sum_div, Subgroup.coe_mul, frameVector,
      ite_div, apply_ite, -sum_sum_type, @Finset.sum_comm (Fin _)] <;> grind [basisScale_ne_zero]
  erw [mulVec_smul, map_mul, ← mulVec_mulVec, ← e, ← frameImage_mulVec, ← one_mul u,
    frameImage_mul_of_mem_besselU0 U, frameImage_one_mulVec,
    RingHom.map_det, mul_comm (det _), ← k (_ ∘ (w ⊕ᵥ Y⁻¹ᵀ b))]
  grw [← le_levelPrime, norm_det_le_norm_pow, l2_opNorm_le_of_apply (M := M) (by
    simp [updateCol_apply, E, by simpa [H] using congr(Φ v ∘ $(h.2.paddedLeading_mul_inv)ᵀ b)]
    simp [← H, paddedLeading]
    grind [norm_one, norm_zero, one_le_pow₀, one_le_b, IsNear.norm_frameProducts_le]), ← sq,
    card_sum, card_fin, Nat.cast_add, S.succ_le_b, ← two_mul, t, t]
  simp [M]
  gcongr <;> clear * - t <;> grind [S.ϱ_le]

/-- Under `Filling.IsAdmissible`, let A consist of pairs (c',γ) with `Filling.IsLabelledTerm` j c t,
and let T ⊂ X₀ have codimension ≤ s. If on A the index `Filling.frameValueIndex` (a = g, V = T) of k
= h_c⁻¹γh_c' divides n(k), then ∑_A n(k)^(−|κ|) ≤ b^(2000(ϱ+1)⁶(s+1)f). -/
lemma tsum_invPowWeight_le_of_codim_le [StablyUnram E]
    {t} s (h : A ⊆ {p | S.IsLabelledTerm j c t p}) T {n : _ → ℕ}
    (hQ : ∀ p ∈ A, S.frameValueIndex c (S.termElem c p) S.gIdele T ∣ n (S.termElem c p)) (hT : 𝔰.k ≤
  finrank E T + s) : ∑' p : A, S.invPowWeight c n p ≤
  .ofReal (S.b ^ (2000 * 𝔰.n ^ 6 * (s + 1) * numInfPlaces E)) := S.of_size_bounds fun _ _ _ o ↦ by
  cases' T.finrank_le.dest with l hl; simp at hl
  intros; have K {p} a := (@h p a).2.choose_spec.1
  grw [tsum_le_of_encard_range_le (R := (S.frameProducts ·.2 = S.frameProducts ·.2)) _
    (encard_integral_le Function.uncurry (by bound) (Set.forall_mem_range.2 fun p i ↦
    ⟨isIntegral_frameProducts (K p.2) .., ((h p.2).1.1.1.norm_frameProducts_le · ..)⟩)
    Function.uncurry_injective.injOn) (by tauto) fun A hA p₀ h₀ e ↦ ?_]; rotate_right
  obtain ⟨⟨⟨⟨N⟩, -, D⟩⟩, F⟩ := h (hA h₀), fun {p} a ↦ And.intro (h (hA a)) (e p a _ h₀)
  let O := (Ô E).comap (algebraMap E _)
  have : IsStarStable O := ⟨(by simpa [O] using star_mem_Ô ·)⟩
  let Y := paddedLeading j (S.frameProducts p₀.2)
  have iY :
    IsIntMatrix O Y := by simp [O, Y, paddedLeading, ite_mem, isIntegral_frameProducts (K (hA h₀))]
  let M := S.levelPrime 0 ^ 𝔰.n ^ 4
  have iy := nsmul_mem (iY.mul iY.isInt_conjTranspose).det_mem S.g
  have n0 : M • S.g • (Y * Yᴴ).det ≠ 0 := by simp [M, Y, D]
  let d := principalIdele n0.isUnit.unit
  have hd : ↑d ∈ Ô E := nsmul_mem iy M
  have nd : genIndex d.1 ≤ _ := (genIndex_algebraMap _).trans_le (by
    simp [M, Y, abs_norm_eq_prod_norm_sq, ← sq]; grw [g_le_b_pow, N.norm_map_leadingMinor_le,
      levelPrime_le])
  have := genIndex_pos d; simp [frameValueIndex, frameGram_termPosition, invPowWeight] at hQ ⊢
  grw [tsum_inv_index_pow_le_of_congr hd (fun p ↦ (frameMiddle (S.termElem c p).1.1)ᴴ)
    (fun p h _ _ ↦ (termsOver.isIntMatrix_termPosition (K (hA h))).isInt_conjTranspose
    _ _) ((isPrimitiveMatrix_iff.2 S.isUnimodular_latMiddle.2).mul_iff.2
    (sublatticeBasis (gram_classCoordX₀ c) T).2.1) (equivOfCardEq
    (by simp [← hl, add_assoc]; rfl)) (le_sup_of_le_right _) (n <| S.termElem c ·) (fun p h ↦ .trans
    (submoduleIndex_dvd_of_le .id le_sup_left (by simp)) ((F h).2 ▸ hQ p (hA h))) _ (by simp [← hl])
    fun B hB p₁ h₁ e ↦ (F (hB h₁)).elim fun G' f ↦ ?_, nd]
  rotate_left 2
  choose! u hu eu using fun p h ↦ (@F p (hB h)).elim fun a b ↦
    (a.1.2.exists_frameImage_toRows₂_eq_add (.refl _) (by simp) G'.1.2 (b ▸ f)
    (by simpa [b] using! e _ h₁ p h <| col_mem_colLattice ·)).elim fun l i ↦ show ∃ u ∈ S.classUnip₀
    c, ∀ i a, (u * p.2).1 (.inr i) (𝔰.besselFrame a) = p₁.2.1 (.inr i) (𝔰.besselFrame a) from
    (S.exists_mem_classUnip c id (-fromRows 0 ((l.fromRows 0).fromRows 0)) 0 (by simp) (by simp) (by
    simpa [classCoord_eq_fromBlocks] using i.1) (by simp) rfl).imp (by clear * - i; simp_all
    [middleGram, Fin.forall_fin_succ', Subgroup.coe_mul, ← ext_iff, frameGram])
  grw [tsum_le_of_colouring (fun p ↦ (frameImage (S.termPosition c p.1 (u p * p.2)).1.1).toRows₁)
    (submoduleIndex_smul_ne_zero hd) (fun _ a _ _ ↦ termsOver.isIntMatrix_termPosition
    (.mul (hu _ a).1.2 (K (hA (hB a)))) _ _) (fun _ ↦ 1) 1, submoduleIndex_smul_intVectors hd, nd]
  simp; norm_cast; simp [Set.encard_le_one_iff]
  intro C hC _ _ H' p q a b
  let ξ := (frameImage (u q * q.2) - frameImage (u p * p.2).1.1).toRows₁
  have ⟨X, x, iX⟩ : ∃ X, ξ = _ • X ∧ IsIntMatrix O X := ⟨_, (smul_inv_smul₀ n0 _).symm, (by
    simpa [ξ, O, d, frameImage_termPosition, classCoord_eq_fromBlocks, Units.smul_def,
      intVectors] using Set.mem_smul_set_iff_inv_smul_mem (a := d).1 <| H' _ b _ a ·)⟩
  grw [hC] at a b
  let P := xRows (S.frameProducts p₁.2)
  let α := (xRows Y.adjugateᵀ)ᵀ
  let T := X * α
  have s : Tᴴ * P = -(P * α)ᴴ * X := (smul_right_inj n0).1 (by
    simpa [x, T, mul_comm Y.det] using congr(αᴴ * $((by
    linear_combination (norm := (ext; simp [ξ, P, eu, a, b, frameGram, mul_sub]; ring))
      congr(submatrix $((u q * q.2).2.trans (u p * p.2).2.symm) 𝔰.besselFrame 𝔰.besselFrame) :
      ξᴴ * P = Pᴴ * -ξ))))
  have z i k (J : ↑j ≤ k.1) : (X * Y.adjugate) i k = 0 := (mul_eq_zero_iff_left (by simp [Y, D])).1
    (eq_zero_of_norm_Φ (algebraMap_mem_Ô.1 ((iX.mul iY.adjugate).smul iy i k)) fun v ↦ by
    have t p h := (F (hB h)).2 ▸ HasLevel.norm_shared_vector_lt ((F (hB h)).1.1.imp And.left id) (hu
      p h).2 J rfl v i
    have := congr(‖Φ v (($x * Y.adjugate) i k)‖).ge
    simp [ξ, Y, M, inv_def, entrywise, D, ← Finset.mul_sum] at *
    by_contra! h; grw [← h, norm_sub_le] at this
    linarith [t _ b, t _ a])
  let σ := (M : E) • (Yᴴ.det • T - Y.det • Tᴴ - (P * α)ᴴ * T)
  have k : S.g • (σ * P) =
    ξ := by cases ((lt_or_ge 𝔰.ϱ j).imp (by simpa [P, α, Y, ← ext_iff, paddedLeading,
    f, ·.trans'] using (congr(submatrix $Y.mul_adjugate Fin.castSucc Fin.castSucc))) fun J ↦
    Matrix.ext fun a b ↦ sum_of_injective _ Fin.castSuccEmb.2 _ _ (by simp +contextual [z, J.trans])
    fun c ↦ mul_eq_mul_left_iff.2 ((em' _).imp (by simp +contextual [Y, P, paddedLeading, f]) (z a
    _)) : P * α = Y.det • 1 ∨ T * P = X * Y.adjugate * Y) <;> simp [σ, adjugate_mul, *] <;> module
  have ⟨r, _, hr, τ, er⟩ := S.exists_mem_classUnip c id 0 _ (by simp) (by simp [σ, s]; module)
    (by simp) (show IsIntMatrix O σ by apply_rules (transparency := .reducible) [IsIntMatrix.smul,
    IsIntMatrix.sub, IsIntMatrix.mul, IsIntMatrix.isInt_conjTranspose, IsIntMatrix.det_mem] <;>
    simp [α, iY.adjugate _, O, P, isIntegral_frameProducts (K (hA h₀)), f]) rfl
  apply (F (hB a)).1.eq_of_frameImage_eq (mul_mem (hr (by simp)) (hu _ a)) (hu _ b) (F (hB b)).1
  simpa [↓frameImage_mul (s := r), ← ext_iff, er, eu, a, b, P, frameGram, ξ,
    eq_sub_iff_add_eq'] using k
  grw [one_le_two, add_le_mul le_rfl, o, o]
  simp (disch := bound); gcongr; simpa; grw [show l ≤ s by lia]; lia; bound
  rintro _ ⟨v, h, rfl⟩
  simpa [d, Y, preimageLattice, inv_def, smul_smul, D, mul_left_comm _⁻¹, -map_mul] using
    (iY.adjugate.isInt_conjTranspose.smul (nsmul_mem iY.det_mem M)).mulVec (M := finAdeleMat _) h

end

open Pointwise Set

omit [S.IsAdmissible] in
lemma submoduleIndex_gIdele_smul {n} {M N : Submodule (Ô E) (n → 𝔸f E)} (h : 1 ≤ submoduleIndex N M)
  (i : N ≤ M) : submoduleIndex (S.gIdele • M) M = submoduleIndex (S.gIdele • N) N :=
  Nat.eq_of_mul_eq_mul_right h (by erw [relIndex_mul_relIndex (hKL := i), mul_comm, submoduleIndex,
  ← relIndex_pointwise_smul S.gIdele, relIndex_mul_relIndex (hHK := smul_set_mono
  i)] <;> first | rfl | apply smul_le_self_of_tower (⟨_, S.gIdele_mem⟩ : Ô E))

variable [StablyUnram E] {S : Filling E 𝔰} [S.IsAdmissible] {T : Set ↥(S.G E)}

/-- Under the standing hypotheses, for each level j the pair weights `Filling.pairWeight`, summed
over all classes c, c' and all pairs p of terms, total at most 2τ², where τ = b^(kf/4). -/
lemma sum_pairWeight_le : ∑ c, ∑ c', ∑' (γ) (γ'), S.pairWeight j c c' γ γ' ≤
  .ofReal (2 * S.tailScale ^ 2) := by
  apply S.of_size_bounds; intros; apply ((tsum_fiberwise (fun (⟨i, t, c, T, q, p⟩ : Σ i t c, Σ (T :
    {T : Submodule E (𝔰.κ → E) // finrank E T + i = 𝔰.k}) (q : ofPred (S.IsLabelledTerm j c t)),
    {p | S.IsLabelledTerm j c t p ∧ S.CongruentTerms c p.1 q.1.2 p.2 ∧ commonLink q.1.2 p.2 = T}) ↦
    S.termWeight j i c q p T) fun ⟨_, _, c, _, q, p⟩ ↦ (c, p.1.1, q.1.2, p.1.2)).trans_le ?_).trans'
  · simp -iota [pairWeight]; gcongr; split_ifs with h; have ⟨h@⟨s, o, o'⟩, m, m'⟩ := h
    exact .trans (by rfl) (ENNReal.le_tsum ⟨⟨_, _, _, ⟨commonLink .., by simp [(finrank_le
      _).trans]⟩, ⟨(_, _), m, s, o, rfl⟩, (_, _), ⟨m', s, o', rfl⟩, h, rfl⟩, rfl⟩)
    simp
  simp [ENNReal.tsum_sigma', termWeight]
  grw [ENNReal.tsum_le_tsum (g := (.ofReal <| 2⁻¹ ^ · * S.tailScale ^ 2)) fun m ↦ ?_]
  simp [-inv_pow]
  grw [tsum_invPowWeight_le_of_codim_le (m + 𝔰.ϱ + 1) (by exact inf_le_left) ?T ?A ?C, ENNReal.tsum_mul_right.le,
    tsum_invPowWeight_le_of_codim_le m (by rfl) _ (by exact fun p h ↦ (relIndex_dvd_of_le_left _ inf_le_left).trans ((
                        relIndex_inf_mul_relIndex _ (toAddSubgroup _) _).symm.dvd.trans (mul_dvd_mul ((submoduleIndex_dvd_of_le
                        (K' := _ ⊓ _) .id le_rfl (by simp)).trans ((submoduleIndex_gIdele_smul (one_le_xRowsIndex_and_saturationIndex h.2.choose_spec.1 h.1.2).1
                        (colLattice_le (col_mem_colLattice ·.1))).dvd.trans (submoduleIndex_dvd_of_le _ (fun | _, ⟨v, h, rfl⟩ => ⟨_, ⟨_, h, rfl⟩,
                                                  by simp⟩) le_sup_left))) dvd_rfl))) (by exact a.2.ge)]
  case T T => exact T.1 ⊓ (frameMiddle a.1.2.1).toRows₁ᴴ.mulVecLin.ker
  case' C T => rw [← map_comap_subtype, ← LinearMap.ker_domRestrict]
  · set N := (mulVecLin _).domRestrict T.1
    obtain ⟨e : _ = _⟩ := T.2, N.finrank_range_add_finrank_ker, N.range.finrank_le
    simp_all [SubmoduleElem]; omega
  case' A c _ T => refine fun y ⟨_, ⟨s, ⟨k, rk, ek⟩, k', rk', ek'⟩, f⟩ ↦
    submoduleIndex_dvd_of_le (S.gIdele • ((frameImage (S.termElem c y).1.1)ᴴ *
    (S.latMiddle (𝔸f E)).splitGram).mulVecLin) (colLattice_le (Sum.rec (⟨_, col_mem_colLattice ·, by
    ext1; simp [frameGram, splitGram, mulVec_eq_sum, mul_apply, Units.smul_def]⟩) fun a ↦
    ⟨0, by simp, congrArg _ (funext fun i ↦ .trans (by cases i using Fin.lastCases <;> simp)
    (congrFun₂ (termElem ..).2 ..).symm)⟩)) (le_sup_of_le_left ?_)
  · set γ := a.1.2; set L := T.1 ⊓ _; obtain ⟨_, ⟨hb, -⟩, p, a, -, hp, rfl⟩ := sublatticeBasis _ L
    rintro _ ⟨r, hy, rfl⟩
    let P : Matrix 𝔰.BesselIndex .. := fromRows 0 ((p.fromRows 0).fromRows 0)
    have φ : (frameImage γ.1.1)ᴴ * S.ratGram * P = 0 := .trans (by simp [P, splitGram, entrywise,
      middleGram]) (mul_eq_zero_of_range_le_ker (hp.le.trans inf_le_right))
    obtain ⟨w, hw⟩ := exists_mul_eq_of_col_mem_range (x := isotropicFramePair y.2) (y :=
      y.2.1.1 * (γ⁻¹.1.1 * P) - P) fun i ↦ by
      obtain ⟨z, ⟨⟨h, h'⟩, hq⟩, e⟩ := f.ge (hp.le ⟨_, p.mulVec_single_one i⟩).1
      obtain ⟨w, a, e'⟩ := congr(($(U.form_mul_inv_eq _) *ᵥ _) ∘ 𝔰.besselFrame).trans congr($φᵀ i),
        mem_link.1 h'
      rw [← mulVec_mulVec] at w; set u := γ⁻¹.1.1 *ᵥ _
      simp [funext_iff, middleGram, splitGram, mulVec_eq_sum, Fin.forall_fin_succ'] at hq e w
      have l := (link γ).sub_mem ⟨_, isotropicFramePair_mulVec_eq_zero_iff.2 ⟨fun _ ↦ rfl, w.1⟩,
        rfl⟩ h
      have f := by simpa [funext_iff] using
        eq_zero_of_ratMiddle_form_eq_zero (u ∘ .inr ∘ .inl - z ∘ .inr) (by simp [*]) (by
        simpa [-Finset.sum_add_distrib, dot_mulVec_eq_sum_sum, u, P, *, ← neg_add,
          -neg_add_rev] using mem_link_iff_orthogonal.1 l _ l)
      use (y.2.1.1 *ᵥ (a ⊕ᵥ (z ∘ .inr ⊕ᵥ 0))) ∘ .inl ⊕ᵥ (u ∘ .inl - a); show _ = _ *ᵥ u - _
      simp [funext_iff, mulVec_eq_sum, sub_mul, P, w.1] at e' ⊢; grind-linarith only
    refine ⟨_, ⟨((S.principalLevel_eq_unitaryLevel.le ⟨k' * k⁻¹, by simp [*], rfl⟩).2.mul (N :=
      S.classCoord c * (finAdeleMat P * a.1)) (by simpa [IsIntMatrix, P,
      classCoord_eq_fromBlocks] using hb)).neg.mulVec hy, -(S.gIdele⁻¹ • finAdeleMat w * a.1) *ᵥ r,
      ?_⟩, ?_⟩ <;> simp [-sub_mulVec, ← smul_mulVec, -coe_units_inv] <;> congr
    simpa [↓← classCoord_mul_isotropicFramePair, ek, ek', coe_termPosition, Matrix.map_sub,
      classCoord, ← (classBasis _).1.mul_assoc, -coe_units_inv]
      using! congr(S.classCoord c * finAdeleMat ($hw) * a.1)
    simp [← ek', by simpa [↓← frameImage_mul] using congr($((U.gram_invariant (k' * k⁻¹).1
      (frameImage k) (S.classCoord c * finAdeleMat P)).trans (by erw [ek, frameImage_termPosition,
      classCoord_gram, φ])) * a.1)]
    simp [entrywise, P, classCoord_eq_fromBlocks, splitGram]
  conv_lhs => simp [ENat.card_eq_coe_natCard, ← Finset.sum_mul]
  grw [sum_latticeDisc_inv_le, ← ofReal_natCast]
  simp (disch := positivity) only [mul_pow, ← ofReal_mul, ofReal_le_ofReal_iff, inv_pow, field]
  rw [← pow_succ, sq S.tailScale, mul_pow]; nth_grw 3 [← pow_le_tailScale le_rfl]
  simp [← pow_mul, mul_assoc, ← pow_add]; gcongr; lia

attribute [local instance] IsFiniteMeasure.toSigmaFinite Side.cut

/-- For the cut Bessel functions and stable T with 𝗀 ≠ 0 on T, ‖A_T(c,s,c')‖ is at most the sum of
ν·`classSize` ⊤ (∏_v|𝗀(γ)|_v) over the near terms γ of T over (c,s,c') that are the chosen
representatives of 𝖴⁰_c(g)γ𝖴⁰_c'(g); ν = `Filling.unipCovolume`, 𝗀 = `Filling.termDisc`. -/
lemma enorm_amplitudeSum_le_classSize_top (hT : S.IsStable T) (h : ∀ γ ∈ T,
  S.termDisc γ ≠ 0) c s c' : ‖S.amplitudeSum T c s c'‖ₑ ≤ ∑' γ : ↥(T ∩ S.termsOver c s c'),
  ite (S.IsNearRep c c' γ) (.ofReal (S.unipCovolume * S.classSize ⊤ (S.termDiscNorm γ))) 0 := by
  choose ω _ ωs ωt ω1 ωS using Exists.intro _ (isBoxPartition_epsilon c')
  choose ρ R using (exists_maximalFor_of_wellFoundedGT _ (S.IsNearRep c c') <|
    @Quot.exists_rep _ (setoid (S.classUnip c) (S.classUnip₀ c')) ·)
  choose G F C using (hasSum_amplitudeSum_change_of_weight (σ := ·) hT c s c'
    (fun γ y ↦ ite (ρ ⟦γ⟧ = γ) 1 0 * ω ((S.ratToInf γ)⁻¹ * y)) fun γ o y ↦ by
    simp [mul_assoc, -ite_mul, ENNReal.tsum_comm]
    apply ωt; intro x
    let g := γ * x⁻¹
    choose u k v m e using (eq (a := g)).1 (R ⟦g⟧).1.symm
    refine ENNReal.tsum_prod ▸ .trans (tsum_congr fun (b, a) ↦ if_congr
      (((congrArg ρ ((eq (b := g)).2 ⟨_,
      one_mem _, _, b.2, by simp [g, mul_assoc]⟩)).trans e).congr_left.trans ⟨fun f ↦ ?_,
      by simp_all [g, mul_assoc]⟩) rfl rfl) (tsum_ite_eq ⟨⟨⟨v, m.1⟩, m⟩⁻¹, u, k⟩ 1)
    obtain ⟨⟨w, l⟩, ⟨⟩⟩ := mul_left_surjective ⟨u, k⟩ a
    have e' := by simpa [mul_assoc] using congr($f * b)
    cases eq_one_of_mem_besselU_of_fix (B := frameImage g.1.1 * (S.frameProducts g)⁻¹.submatrix id
      _) l.1 (by erw [← Matrix.mul_assoc, ← frameImage_mul, ← e', frameImage_mul_of_mem_besselU0
      (mul_mem m b.2).2]) (by simpa [frameGram, splitGram, entrywise] using congr($(mul_nonsing_inv
                                _ (hasLevel_last (h g (by
      simpa using! (hT 1 (by simp) _ x⁻¹.2.1 _).2 o.1))).2.1.isUnit).submatrix .castSucc .castSucc))
    clear * - e'; simp_all [g, Subtype.ext_iff, mul_eq_one_iff_eq_inv'])
  grw [← (G _).tsum_eq, enorm_tsum_le_tsum_enorm]; gcongr with γ
  split_ifs with e n <;> simp <;> try
    refine Not.imp_symm exists_ne_zero_of_integral_ne_zero fun ⟨a, z⟩ ↦ ?_
  obtain ⟨_, C, ⟨_, p, q⟩, N⟩ := S.unipCovolume_pos, C .full, n.1,
    n.1.le_classSize_and_cellMass_le (one_le_prod_norm_Φ (by
    apply_rules [IsIntegral.det, fun _ _ ↦ isIntegral_frameProducts γ.2.2 .., IsIntegral.pow,
      isIntegral_natCast, map_isIntegral_int, IsIntegral.mul, IsIntegral.sub]) (h _ γ.2.1))
  choose B l m τ hB _ H _ _ hl ht using fun v ↦
    (S.besselSys v).open_cell (by simp [gramDiscReal_realFrameGram_ratToInf, Finset.prod_pos,
    γ.2.1, *]) (p v).1 (q v).1 (le_self_pow₀ S.one_le_b nofun)
  choose x ht T using (exists_notMem_null_le_lintegral (Measurable.aemeasurable (by fun_prop))
    (Measure.ae_pi_le_pi (Filter.eventually_pi ht))).imp fun _ ↦ And.imp of_not_not
    (IsL2Contraction.pi (by fun_prop) (fun _ _ _ ↦ ContinuousOn.integrableOn_compact (hB _)
    (by fun_prop)) H (ω · |>.toReal) 1 (by fun_prop) (by simp [toReal_le_of_le_ofReal, *])).trans'
  have I σ := ((F σ γ).comp_mul_left (S.ratToInf γ * fun v ↦ τ v (x v))).restrict (s := univ.pi B)
  grw [← ENNReal.le_tsum γ, N.1, ← lintegral_mul_left_eq_self, ← enorm_toReal_smul_le,
    ← setLIntegral_le_lintegral, ← enorm_integral_le_lintegral_enorm] at C
  simp [e, smul_sub] at C I
  grw [← integral_mul_left_eq_self, ← setIntegral_eq_integral_of_forall_compl_eq_zero
    fun y ↦ Not.imp_symm fun z ↦ ?_, ← sub_eq_iff_comm.1 (integral_sub (I _) (I _)).symm,
    ← add_halves (S.unipCovolume * _), enorm_sub_le, C, ofReal_add, ENNReal.add_le_add_iff_right,
    ← ENNReal.pow_le_pow_left_iff two_ne_zero, ← ofReal_pow, ← N.2, ← hl,
    euclidean_enorm_sq_eq_sum, ← (Equiv.arrowProdEquivProdArrow ..).sum_comp]
  simp [↓eval_integral_piLp (I _).eval_piLp, volume_pi, Measure.restrict_pi_pi, besselKernel,
    besselFn, mul_assoc, ωS, ht _, ← ofReal_norm] at T ⊢
  grw [T, ofReal_toReal_le, ω1]; simp [Measure.pi_univ, ofReal_prod_of_nonneg]
  any_goals rw [classSize]; finiteness
  all_goals simp [toReal_eq_zero_iff] at z; let hy := inCut_of_besselKernel_ne_zero z.2
  exact fun v _ ↦
    (ht v).2 _ (by simpa [mul_assoc, frameBox, frameVector_mul, ht _] using ωs _ v z.1.1 (hy v).2)
    ((hy v).1.trans (pow_right_mono₀ S.one_le_b (by nlinarith [S.ϱ_le])))
  choose u H B using exists_classUnip_mul_mem_boxedPoints c (hy · |>.1)
  choose a A b B' o using mk_out_eq_mul (S.classUnip₀ c) _ (u * γ)
  exact n (e ▸ (R _).2 ((eq ..).2 ⟨_, mul_mem A.1 H, b, B', o.trans (by group)⟩).symm
    (fun h ↦ (n (e ▸ h)).elim) ⟨o ▸
    .mul_of_mem_besselU0 ⟨_, B, by simp [boxedPoints, *, -Pi.mul_apply]⟩ A.2 B'.2, by simp⟩)

/-- For the cut Bessel functions and stable T of level j, ‖A_T(c,s,c')‖ is at most the sum of
ν·`Filling.classSize` j (`Filling.classGauge`) over near terms of T over (c,s,c') that represent
their classes 𝖴⁰_c(g)γ𝖴⁰_c'(g), and is 0 unless s agrees. -/
lemma enorm_amplitudeSum_le_classSize (hT : S.IsStable T) {j} (h : ∀ γ ∈ T, S.HasLevel j γ) c s
  c' : ‖S.amplitudeSum T c s c'‖ₑ ≤ ∑' γ : {γ ∈ T ∩ S.termsOver c s c' | S.Agrees s ∧
  S.IsNearRep c c' γ}, .ofReal (S.unipCovolume * S.classSize j (S.classGauge j c c' γ)) := by
  by_cases! ¬S.Agrees s; simp [amplitudeSum_eq_zero_of_not_agrees, *]
  let K := {γ | S.N ^ numInfPlaces E * S.minorNorm j γ < S.termDiscNorm γ}
  have sK : S.IsStable (T \ K) := by simp_all [IsStable, K, minorNorm, termDiscNorm,
    frameDisc_frameGram_besselU_mul, leadingMinor_frameGram_besselU_mul]
  have ι k : S.xRowsIndex ⊤ k = 1 :=
    relIndex_eq_one.2 (colLattice_le (col_mem_colLattice <| Subtype.mk · (by simp)))
  have p γ : S.termDisc γ = 0 → γ ∉ K := by simp_all [K, termDiscNorm, minorNorm]; bound
  simp [amplitudeSum_split T K]
  grw [← tsum_extend_zero Subtype.val_injective, ← tsum_comp_le_tsum_of_injective
    Subtype.val_injective, Summable.tsum_union_disjoint, enorm_add_le, amplitudeSum,
    enorm_tsum_le_tsum_enorm, enorm_amplitude_le, enorm_amplitudeSum_le_classSize_top,
    tsum_setElem_eq_tsum_setElem_sdiff _ _ fun _ ↦ id, tsum_mono_subtype (t := ⋃ δ ∈ {δ ∈ T \
    K ∩ S.termsOver c s c' | S.IsNearRep c c' δ}, doubleCoset δ (S.classUnip₀ c) (S.classUnip₀ c')),
    tsum_biUnion_le_tsum]
  gcongr with x x <;> obtain ⟨γ, ⟨t, k⟩, w⟩ := x
  simp [*, t.1, tsum_amplitudeAbs_class_le k _ (not_lt.1 t.2), Function.extend_val_apply]
  cases show j = ⊤ by grind [HasLevel]
  split <;> simp [*, classGauge, k.out.le, Function.extend_val_apply]
  exact fun γ ⟨⟨t, w⟩, z⟩ ↦ (mk_out_eq_mul _ _ γ).elim fun u ⟨a, v, b, o⟩ ↦ mem_biUnion ⟨o ▸
    ⟨(sK u⁻¹ (inv_mem a.1.1) _ b.1.1 _).2 t, by simpa using termsOver.mul (.mul a.1.2 w) b.1.2⟩,
    o ▸ .mul_of_mem_besselU0 (((pow_ne_zero 2 z).pos.trans_le amplitudeAbs_sq_le).ne'.imp_symm
    (by simp +contextual [schurIntegral, schurWeight, boxCutoff, indicator, IsNear, -mul_ite])) a.2
    b.2, by simp⟩ ((mem_quotToDoubleCoset_iff ..).2 rfl)
  repeat first | grind | simp_all [IsStable]
