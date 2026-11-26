/- GID: D5/S3/Zeros/GRH/New/Exchange/DeterminantVectors
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/Exchange/DeterminantVectors
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.Exchange.DeterminantVectors. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Exchange/DeterminantVectors.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.Weil.MixedModel.EquivariantCoefficients
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Exchange theorem for theta integrals of complementary rank (see
New.Exchange.ExchangeTheorem).

Part of: Schrödinger and mixed models of the Weil representation; action of parabolic subgroups
(known result; see Lib.Weil.MixedModel.ZeroTermLaw).

This file: Determinant vectors in Fock space are cone integrals of determinant vectors one floor
up. -/
seal Finset.univ Finset.sum Finset.prod

noncomputable section


attribute [-simp] principalMinor_of_forall principalMinor_of_forall_not
open Matrix MeasureTheory Complex WeilData Space Splitting MvPolynomial Finset Fintype MatMul
  Heisenberg IsVacuum MixedModel Prod
attribute [local simp] div_mul_eq_mul_div slice_vac sum_prod_type fst_sum realVec Splitting.frameAt
  realMatrix negCount zpow_add₀ mul_div mul_pow prod_ne_zero_iff div_pow pairSign
  mul_eq_one_iff_eq_inv integral_smul_const blockDiagonal div_eq_iff
variable {E} [Field E] [CMType E] [WeilData E] {n n' r r'} [Fintype n] [Fintype n'] [Fintype r]
  [Fintype r'] (s : n → ℤˣ) (t : r → ℤˣ) (k) (m : _ → ℕ) (c) (F : Matrix n r (𝔸 E))

/-- The square matrix ζF, where ζ is the real adelic matrix formed from the coordinates of u
that join lines of equal sign. -/
abbrev posCoordMatrix u :=
  atRealPlace (vecToMat (realVec (posProj (realSigns E (homSigns s t)) *ᵥ u)) * F)

/-- c times the Gaussian at u times the conjugate of ∏_w det₊(M_w)^{m_w}·det₋(M_w)^{m_w+2k},
where M = `posCoordMatrix` s t F u and det± are the principal minors on t = ±1. -/
def detVectorFn u := c * realVac u * star (∏ w, let M := posCoordMatrix s t F u w
             principalMinor M (t · = 1) ^ m w * principalMinor M (t · = -1) ^ (m w + 2 * k))

variable {s t k m} {s' t'} {W : Space E n s} {W' : Space E n' s'} {V : Space E r t}
  {V' : Space E r' t'} (A : W'.Splitting W Unit) (X :
  V'.Splitting V Unit) [IsBaseAdapted A] [IsBaseAdapted X] {D : W.Splitting W' r}

/-- Determinant vectors: v is rapid and equals the function `detVectorFn` s t k m c F for some
constant c and matrix F. -/
def detVectors k m :=
  {v : PairFock E s t | IsRapidDatum v ∧ ∃ c F, ∀ u, v u = detVectorFn s t k m c F u}

omit [WeilData E] in
lemma frameAt_real_unitary {t} (h :
  D.IsAdapted 1 t) w : let P := atRealPlace (D.frameAt 1 t) w; (Pᴴ * P = 1 ∧ P * Pᴴ = 1) ∧
    signMatrix s * P = P * fromBlocks (n := r ⊕ r) (fromBlocks 0 1 1 0) 0 0 (signMatrix s') := by
  intro P; have o := (mul_eq_one_comm_of_card_eq _ _ _ (by simp +arith [D.card_eq])).1 (h.1 w)
  erw [h.1, o, ← Matrix.one_mul (_ * P), ← o, P.mul_assoc, ← Pᴴ.mul_assoc, gram_map_real]
  simp [↓gram_frameAt, stdForm, signMatrix]

omit [Fintype n] in
lemma posProj_eq : posProj s =
  (2⁻¹ : ℂ) • (1 + signMatrix s) := by rw [signMatrix_eq_posProj_sub]; module

/-- In the mixed model of a splitting adapted at 1, for all a, u some U has positive part
Iu₊ − La − Ka and (slice a v)(u) = v(U) for every Fock vector v of a polynomial in the positive
coordinates. -/
lemma PositivePart.exists_slice_eq {t} (h : D.IsAdapted 1 t) a u : ∃ U,
  posProj (realSigns E s) *ᵥ U = h.mixedModel.L *ᵥ -a + h.mixedModel.I *ᵥ posProj
  (realSigns E s') *ᵥ u + h.mixedModel.K *ᵥ -a ∧ ∀ P, let v := polyVector _ (rename
    (@Subtype.val _ (realSigns E s · = 1)) P); h.mixedModel.slice a v u = v U := by
  let J a z b := h.mixedModel.L *ᵥ a + h.mixedModel.I *ᵥ z + h.mixedModel.K *ᵥ b
  have q a z b : posProj (realSigns E s) *ᵥ J a z b =
      J (midpoint ℂ a b) (posProj (realSigns E s') *ᵥ z) (midpoint ℂ a b) := by
    ext ⟨w, l⟩; have := congr(($((frameAt_real_unitary h w).2) *ᵥ
      (vecToMat a w ⊕ᵥ vecToMat b w ⊕ᵥ vecToMat z w)) l)
    simp [J, posProj_eq, midpoint_eq_smul_add, signMatrix, ↓mulVec_add, IsAdapted.mixedModel,
      mulVec, dotProduct, vecToMat] at *
    grind
  have n a u c z : star (J a u a) ⬝ᵥ J c z c = 2 * star a ⬝ᵥ c + star u ⬝ᵥ z := by rw [(?_ : J =
    fun a z b ↦ realMatrix (D.frameAt 1 t) *ᵥ fun (w, i) ↦ (vecToMat a w ⊕ᵥ vecToMat b w ⊕ᵥ vecToMat
    z w) i), star_mulVec_dotProduct, mulVec_mulVec, realMatrix_orthonormal _ h] <;> simp [entrywise,
    vecToMat, J, IsAdapted.mixedModel, funext_iff] <;> grind
  have ⟨_, _, _, e⟩ := h.mixedModel.exists_decomp
  have' he : _ ∘ Equiv.sumCompl (realSigns E s · = 1) = _ := Sum.comp_elim ..
  use J (-a) u (-a), by simp [q, J], fun P ↦ sub_eq_zero.1 (.trans
    (by simp [← polyVector_one, realBoxProd_polyVector]; rfl) congr($((hom_ext fun y ↦ ?_ :
    (modelEval u ∘L h.mixedModel.slice a - modelEval _) ∘L (realBoxProd he).flip vacVector = 0)) P))
  simp [realBoxProd, OrthogonalSum.tmul, Rep.left]; erw [(realCoordSum he).tmul_vacElem,
    (by ext; simp_all [realCoordSum, posProj] : (realCoordSum he).equiv (y, 0) = posProj (realSigns
    E s) *ᵥ (realCoordSum he).equiv (y, 0)), ← e ((realCoordSum _).equiv _), q, slice_realHeisOp]
  simp [*, realHeis.eq_1, realVac, ← exp_add, signMatrix_eq_posProj_sub, ↓signMatrix_one]; grind

/-- Let W′, V′ be W, V plus a hyperbolic plane, with adapted splittings, z ≥ 1 and rk W′ = 2k +
2·(negative signs of W′). Every determinant vector v (`detVectors` k m) is the cone
integral at z, with weights k + m, of a determinant vector v′. -/
lemma surjOn_cone_integral_detVectors β z (hz : 1 ≤ z) (hn : card n' = 2 * (k + negCount s')) :
  (detVectors k m).SurjOn
  (∫ p, coneIntegrand A X (k + m ·) β z · p ∂.prod .haar .haar) (detVectors k m) :=
  fun v ⟨_, c, F, e⟩ ↦ (tsum_lineTerm A X β).2.choose_spec.choose_spec.elim fun _ ⟨hy, l⟩ ↦ by
  let G := ((-(scaleIdele E).1.1⁻¹, 0) :
    𝔸 E) • (A.kAdelic * X.kAdelicᴴ + A.lAdelic * X.lAdelicᴴ) + A.iAdelic * F * X.iAdelicᴴ
  let d w σ := det (of fun l i : {i // t' i = σ} ↦ ∑ j, C (star ((scaleIdele E * G j l).1
    w)) * if h : _ = 1 then .X (⟨(w, i, j), h⟩ : {c // realSigns E (homSigns s' t') c = 1}) else 0)
  let R x : PairFock E s' t' :=
    polyVector _ (rename (↑) (C x * ∏ w, d w 1 ^ m w * d w (-1) ^ (m w + 2 * k)))
  have K x g (h : ∀ w, g w ∈ blockDiagAlg t') u :
      realPairWeil (card n' / 2 - (k + m ·) ·) 0 (1, g) (R x) u = detVectorFn s' t' k m x G u := by
    erw [realPairWeil_polyVector _ _ (by simp) h, IsVacuum.smul_apply, polyVector_apply,
      aeval_bind₁]
    set f := fun _ : _ × _ ↦ _
    simp [detVectorFn, pow_add, hn, zpow_sub₀, two_mul k, (by
      simpa [hn, two_mul, ← add_assoc] using negCount_neg_add s' :), fun w σ ↦ show
      eval f (rename (↑) (d w σ)) =
      principalMinor (posCoordMatrix s' t' G u w)ᴴ (t' · = σ) * principalMinor (g w) (t' · = σ) by
      rw [← principalMinor_mul (by clear * - h; grind [mem_blockDiagAlg])]
      simp [f, principalMinor, eval_rename, RingHom.map_det, d]; congr!; ext
      simp +contextual [posProj, mul_apply, vecToMat, toSquareBlockProp, apply_dite (eval _),
        sum_mul, holCoord_eq, @sum_comm n', mul_sum, ite_sum_zero, -sum_ite_irrel]
      clear * - h; grind [mem_blockDiagAlg]]; ring
  have H x := by simpa using K x 1
  have Φ q : ∃ φ : ℝ, ∀ d : ℝ, coneIntegrand A X (k + m ·) β z (R (d * c)) q = φ.exp • d • v := ?_
  choose φ Φ using Φ
  use R ((∫ q, (φ q).exp ∂.prod .haar .haar)⁻¹ * c),
    ⟨(weightedNorm_polyVector_ne_top · _), _, _, H _⟩
  by_cases v = 0 <;> simp [↓Φ, *, fun h ↦ (integral_exp_pos ((integrable_smul_const h).1 (funext
    (Φ · 1) ▸ (integrable_coneIntegrand _ _ _ _ hz (weightedNorm_polyVector_ne_top · _)).1))).ne']
  choose y a₁ a₃ using PositivePart.exists_slice_eq hy _
  use -∑ w, ‖q.2.1 w‖ ^ 2 + .log (ideleAbs (q.2.map (.inl ..)) ^ z *
    ∏ w, normSq (q.2.1 w) ^ (k + m w)); intro; ext u
  erw [Real.exp_add, Real.exp_log (by simp [Real.rpow_pos_of_pos, prod_pos]), coneIntegrand, ext
    (K _ _ (mem_maxCompactU.1 <| q.1.2.1 · ⟨⟩) · |>.trans (H ..).symm), lineTermReal,
    IsVacuum.smul_apply, a₃, H]
  have a w σ : principalMinor (posCoordMatrix s' t' G (y u) w) (t' · = σ) =
    q.2.1 w * principalMinor (posCoordMatrix s t F u w) (t · = σ) := ?_
  simp [*, ← (by simpa [star_dot_self_eq_sum] using a₃ u 1 :), ← Complex.coe_smul, detVectorFn,
    pow_add, ← conj_mul',
    normSq_eq_conj_mul_self, _root_.zpow_mul, prod_pow, pow_right_comm _ 2, prod_eq_zero_iff]; ring
  have := frameAt_real_unitary (by simp [IsAdapted, IsBaseAdapted.isOrthoIntegral] :
    X.IsAdapted 1 1) w; extract_lets P at this
  rw [(?_ : posCoordMatrix _ _ G _ w =
    P * (scalar (Unit ⊕ Unit) (q.2.1 w)).fromBlocks 0 0 (posCoordMatrix s t F u w) * Pᴴ)]
  fin_cases σ <;> simp [↓principalMinor_sign_eq_det, principalMinor_eq_det, ← posProj.eq_1,
    posProj_eq, mul_apply, sub_eq_add_neg, this, ← (signMatrix _).mul_assoc P, ← this.1.elim
    det_conj_of_mul_eq_one, ↓(det_classical _).symm.trans (det_fin_two _), ← fromBlocks_one',
    ← Pᴴ.mul_assoc P, fromBlocks_add, fromBlocks_neg, ← det_submatrix_equiv_self (.ofBijective
    ![.inl (), Sum.inr ()] (by open Calc in decide +kernel)), fromBlocks_smul] <;> ring_nf <;> simp
  rw [Splitting.frameAt, inv_one, _root_.G.mat_one, Matrix.one_mul, fromCols_ext_iff] at l
  simp_rw [posCoordMatrix, a₁, map_add, IsAdapted.mixedModel, realVec_realMatrix_mulVec, l.2,
    fromCols_inj l.1]
  cases β <;> simp [kronecker_mulVec_eq_matToVec, ← Pi.zero_def, ← matToVec_add, Function.comp_def,
    mk_zero_zero, G] <;> ext <;> simp [↓← (vecToMat _).mul_assoc, mul_apply, P,
    vecToMat, -Matrix.mul_assoc, field] <;> ring
