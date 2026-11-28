/- GID: D5/S3/Zeros/GRH/New/Seesaw/GoodDatumExists
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/Seesaw/GoodDatumExists
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.Seesaw.GoodDatumExists. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Seesaw/GoodDatumExists.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.New.Seesaw.AdmissibleEvaluation
import D5.S3.Zeros.GRH.New.Seesaw.PairTensorData
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Seesaw identity for a chain of theta lifts (see New.Seesaw.SeesawTheorem).

This file: Constant terms of the chain's finite data are admissible sums with controlled
denominators. An invariant admissible combination yields a good datum computing the definite
chain. -/
seal Finset.univ Finset.sum Finset.prod

open Finset Ideal Matrix Modulus Space TensorProduct TensorChain Weil

namespace Data

attribute [-simp] coe_algebraMap_Ô

attribute [local simp] lastPair middlePair entrywise inclMatrix

variable {P} (D : Data P) (ϑ : D.Twist)

lemma isAdmissibleEval_pairEvalY i (hi : i ≤ D.ϱ) :
  IsAdmissibleEval D.N D.piPlaces (algebraMap _ _ D.piGBar) (pairEvalY i) := by
  have L {k l} j (e : _ =
    j := by grind) := congr(Grading.SpansLattice _ _ _ (_ ^ $e)).mp (D.spansLattice_gradingY k l)
  let δ := star D.chosenIdele⁻¹.1 * D.chosenIdele
  unfold pairEvalY; split_ifs <;> (try lia) <;> apply isAdmissibleEval_finEval (1 ⊕ᵥ (1 ⊕ᵥ fun _ ↦
    ite (i < D.ϱ) 1 δ)) (L (D.ϱ - i).succ) δ (by simp +contextual [δ, chosenIdele, generator_spec,
    places, v_inv, not_isChosen_of_N_mem, ← v_chosenIdele, ← IsChosen.eq_1]) <;> (first
    | rintro s t e x c ⟨o, h, k, a, b⟩ _ rfl (j | j) | simp +contextual [D.isSplitLevel_piPlaces,
      selfOrConj, mem_Ô, piIdele_spec, mem_Ô.1 (generator_spec _).1, chosenIdele, ← v_chosenIdele,
      δ, ↓coe_divStar, ideleA, *, v_inv, division_def] <;> grind [Units.mul_inv, star_one,
      star_mul']) <;> subst_vars <;> [apply inv_xFin_mulVec_mem_of_spansLattice (L (D.ϱ -
    i).succ) (x ∘ .inl) a; apply inv_xFin_mulVec_mem_of_spansLattice (L (D.ϱ - i)) (x ∘ .inr)
    b; apply inv_xFin_mulVec_mem_of_spansLattice (L 1) (x ∘
    .inl) (add_mem a (mul_mem Weil.normNegOne.1.2 b)); revert j] <;> (try simp [univ_eq_empty, xFin,
    reindex_equiv (D.lastGrading D.m_eq_two_mul_varrho_add_two).indexEquiv,
    (D.m_eq_two_mul_varrho_add_two ▸ D.isStd_spaceY).point_eq_one]) <;> grind
    [star_normNegOne_mul_self, show D.piIdele⁻¹.1 = (_⁻¹ : D.E) by rfl]

/-- There is a constant C such that, for every tame ϑ (q = ∏_Q Nw) and y integral away from q,
⊗_{i≤ϱ} `Data.evaluatedDatum` ϑ y i is an admissible combination of the C·`Data.reducedVacuum` t, t
in `Data.admissibleTranslations` q, of denominator `Data.cutBound`^{2m} and, if Q = ∅, size 1. -/
lemma exists_isAdmissibleComb_reducedVacuum : ∃ C : ℂ, ∀ ϑ y,
  (∀ k, y k ∈ localLevel _ {w | ϑ.levelNorm ∉ w.1}) →
  IsAdmissibleComb (C • D.reducedVacuum ·) (admissibleTranslations ϑ.levelNorm) ϑ.levelNorm
  (D.cutBound ^ (2 * D.m)) (ϑ.Q = ∅) 1 (TensorChain.pure (evaluatedDatum ϑ y) _) := by
  choose! C hC using D.isAdmissibleEval_pairEvalY
  use (range D.ϱ.succ).prod ?Grading.c, fun ϑ y hy ↦ ?_; swap
  have a {k} : IsAdmissibleComb _ (translations _ ϑ.levelNorm (star (D.piGBar : 𝔸f D.E))).carrier
    ϑ.levelNorm _ (ϑ.Q = ∅) 1 (translatedUpsilon ϑ y k).1 :=
    .smul (.bind (.map (isAdmissibleComb_name (g := D.piGBar) (B := 1) _ _ (by
    erw [Nat.cast_prod, ← prod_coe_sort]
    exact mul_mem_mul (span_piGBar D ▸ by simp) (prod_mem_prod fun _ _ ↦ absNorm_mem _)) (by
    simp [ite_mem]) (by erw [Pi.single_comp_equiv (.curry ..)]; simp [apply_ite])
    (projOn_vacElem _)) _) 1 1 (fun x hx ↦ by
    erw [G.onHom_fin]; generalize e : Prod.snd _ = g
    have I : g ∈ localLevel _ {w | ↑ϑ.levelNorm ∉ w.1} := by simp_all [localLevel, ← e]
    exact isAdmissibleComb_weil_vacElem _ (mul_one _) (fun y hy ↦
      mulVec_eq_sum _ g.1.1 ▸ (weightedTranslations ..).sum_mem fun j _ i w h
      ↦ by erw [mul_left_comm, map_mul]; exact mul_le_one' ((I w h).isIntMatrix ..) (add_mem
      hx (fun j w _ ↦ mem_Ô.1 (mul_mem (star_mem_Ô (coe_mem_Ô _)) (hy j)) w) j w h))
      (fun _ _ hl ↦ by simp [← Complex.mul_conj', ← finMultiplier_inv,
      Parameters.norm_finMultiplier_eq_one, localLevel_le_integralAbove_of_coprime hl I]) (by
      simp +contextual [finMultiplier_eq_one_of_mem, mem_Kf_iff, I _, one_notMem])) (mul_one _).dvd)
    (fun l _ hl ↦ by simp [D.hasWeight_liftChar.hasWeight_rankTwist.norm_padic_det,
    localLevel_le_integralAbove_of_coprime hl (hy _)]) ?_
  refine .bind (.pure (D.cutBound ^ 4) 1 _ fun i hi ↦ (((a.map_bilinear arrowProduct.toLinearMap₁₂
    a).of_eq_isOfFinOrder_smul fun y hy ↦ ?_).map (D.pairEvalY i)).bind _ _ (hC i (by omega) _ _
    ϑ.7.coprime_mul_left) ?_) 1 1 (fun t h ↦ (congrArg _ (pure_smul _ _ _ fun i _ ↦ ?_)).mpr
    (.single t h)) (by rw [m_eq_two_mul_varrho_add_two]; ring_nf; rfl)
  exact ⟨_, invMonoidHom.isOfFinOrder (isOfFinOrder_ψf _).pow, fun r ↦
    r.1.elim (fun i ↦ -Weil.normNegOne.1.1 * star (y.1 (r.2, i))) (y.2 ⟨·, r.2⟩), Prod.rec (Sum.rec
    (fun i l ↦ star_star (_ : 𝔸f D.E) ▸ star_mem_weightedTranslations (neg_mem Weil.normNegOne.1.2)
    hy.1 id (l, i)) fun _ _ ↦ hy.2 _), by simp [eq_inv_smul_iff₀, ← arrowProduct_vacElem,
    finHeisOp_arrowProduct, mul_left_comm Weil.normNegOne.1.1, ← mul_assoc]; rfl⟩
  simp [↓absNorm_piGBar, ↓card_Ohat_quot_span D.piGBar_ne_zero, Nat.card_fun, ← pow_mul,
    ← pow_add, ↓card_X, n, m_eq_two_mul_varrho_add_two, Shape.MiddleIndex]
  gcongr; grw [Nat.le_of_lt_succ hi]; lia
  simp [pairTranslates, smul_smul, ← smul_tmul',
    (show translateDatum t · = _ from (heisFinPart ..).map_smul _ ⟨_, vacElem_mem_finitePart⟩)]
  congr! 1; rw [← div_mul_cancel₀ (C i)]; simp
  simp [D.hasWeight_liftChar.hasWeight_rankTwist.norm_map_eq_one, funext_iff]

lemma projOnFinPart_pairTranslates (ϑ : D.TameChar) {t} (ht : t ∈ D.admissibleTranslations
  ϑ.levelNorm) i : TensorProduct.map (projOnFinPart _ D.piPlaces) (projOnFinPart _ D.piPlaces)
  (D.pairTranslates (D.translateDatum t) i) = D.translateDatum t _ ⊗ₜ D.translateDatum t _ := by
  have {j y} : projOnFinPart _ D.piPlaces (heisFinPart _ y (D.translateDatum t j)) =
    boxIndicator .. • heisFinPart _ y _ := Subtype.ext (projOn_finHeisOp _
    (by exact D.projOn_translateDatum (D.mem_integralAfter ht fun w ↦ by grind
    [not_isChosen_of_N_mem, D.isSplitLevel_piPlaces.natCast_mem_iff, star_star,
    w.2.notMem_of_isCoprime_of_mem ϑ.7.coprime_mul_left.cast])) y)
  simp [pairTranslates, translateSum, *, ite_tmul]
  rw [Fintype.sum_eq_single 0 fun y hy ↦ ite_eq_right fun e ↦
    hy (funext fun i ↦ (D.isSplitLevel_piPlaces.reduction_eq_iff.2 (by
    cases i <;> simp_all [mem_integralBox, idem_mul_mem_Ô, or_imp])).symm.trans (map_zero _))]
  simp [← Pi.zero_def, residueOverN, heisFinPart, LinearMap.restrict_apply, finHeisOp,
    stdLattice.semichar]

/-- For t admissible for q, `Data.reducedVacuum` t is an admissible combination of pure tensors of
translated vacua (translations admissible for qN, denominator 1, under p size ≤ N^(f·n_m·(ϱ+1))). -/
lemma isAdmissibleComb_reducedVacuum {q p} ⦃t⦄ (ht : t ∈ D.admissibleTranslations q) :
  IsAdmissibleComb (fun x ↦ pure (fun _ ↦ D.translateDatum x _ ⊗ₜ D.translateDatum x _) _)
  (D.admissibleTranslations (q * D.N)) q (1 ^ D.ϱ.succ) p (|↑(D.N ^ (D.f * D.n D.m))| ^ D.ϱ.succ)
  (D.reducedVacuum t) := by
  apply IsAdmissibleComb.pure (α := (D.X ·.succ × _ → _)) (v := fun i x ↦
    heisFinPart _ x.1 _ ⊗ₜ heisFinPart _ x.2 _)
  simp_intro .. [pairTranslates, translateSum]
  refine .of_eq_isOfFinOrder_smul (congr(∑ _, $(one_smul ..)).subst (.of_sum (by simp) (by
    simp_intro .. [↓card_X, ← pow_mul, card_piPlaces]; gcongr; exacts [D.le_of_hasLogBound,
      D.n_mono (by grind)]))) fun y _ ↦ ⟨_, (isOfFinOrder_ψf _).mul (isOfFinOrder_ψf _), (_, _), ?_,
    .trans (by apply congrArg₂ <;> ext1 <;> apply finHeisOp_finHeisOp) (smul_tmul_smul ..)⟩
  constructor <;> intro i w <;> simp_intro e [w.2.mul_mem_iff_mem_or_mem,
    D.isSplitLevel_piPlaces.natCast_mem_iff] <;> simpa [e, apply_ite, ite_apply] using ht _ i w e.1

attribute [local simp] Finsupp.sum liftInPairs_pure

/-- For a twist ϑ, q = ∏_Q Nv, let w be an admissible combination of the `Data.reducedVacuum` t, t
in `Data.admissibleTranslations` q (denominator 1, size ≤ `Data.cutBound`^{3m} if Q = ∅), fixed by ∏
K_j with last component 1. Then for some good datum Ψ the chain of paired lifts with datum w equals
∑_t Ψ(t)·(chain with data `Data.translateDatum` t) on all smooth forms on X₀. -/
lemma exists_isGoodDatum_of_invariant {w} (hw :
  IsAdmissibleComb D.reducedVacuum (D.admissibleTranslations ϑ.levelNorm) ϑ.levelNorm 1 (ϑ.Q = ∅)
  (↑(D.cutBound ^ (2 * D.m)) * D.cutBound ^ (2 * D.ϱ + 2)) w) (hi : ∀ b : ∀ k, D.columnLevel k,
  b (2 * D.ϱ + 2) = 1 → TensorChain.map (twoKernelAction (D.liftKernel ϑ) (b ·)) _ w = w) : ∃ Ψ,
  IsGoodDatum ϑ Ψ ∧ ∀ φ, TensorChain.lift (TensorChain.liftInPairs (D.liftKernel ϑ · |>.lift)) φ _
  w = chainComb ϑ Ψ D.translateDatum _ φ := let T := TensorChain.lift (TensorChain.liftInPairs (M :=
    (TensorChain _ ·)) fun _ ↦ TensorProduct.mk ..) _ _
  hw.bind _ _ D.isAdmissibleComb_reducedVacuum
    (hB := by simpa using fun _ ↦ Real.le_exp_of_log_le D.le_of_hasLogBound).imp fun Ψ s ↦
  ⟨⟨s.1, @id (_ = 2 * (_ + 1)) D.m_eq_two_mul_varrho_add_two ▸ fun b h β ↦ by simpa [s,
    twoKernelAction, ← ((lift_pure ..).trans (liftInPairs_pure ..) : T _ = TensorChain.pure ..)]
    using (congr(β (T $(hi b (h _ .refl))))), fun φ ↦ by
  simpa [s] using! congrArg (TensorChain.lift (TensorChain.liftInPairs (D.liftKernel ϑ · |>.lift)) φ
    _) (hw.elim fun r e ↦ by simp +contextual [e, reducedVacuum, D.projOnFinPart_pairTranslates ϑ,
    e.1.1, ← pairTranslates.eq_1] : w = TensorChain.map (fun i ↦ translateSum .. ∘ₗ
    TensorProduct.map (projOnFinPart ..) (projOnFinPart ..)) _ w)⟩, by simp [s, chain]⟩
