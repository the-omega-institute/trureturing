/- GID: D5/S3/Zeros/GRH/Lib/Weil/Lift/Edge
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/Weil/Lift/Edge
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.Weil.Lift.Edge. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/Weil/Lift/Edge.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.DiscreteSeries.Theta.JointHarmonicExists
import D5.S3.Zeros.GRH.Lib.DiscreteSeries.Theta.LocalThetaCorrespondence
import D5.S3.Zeros.GRH.Lib.Weil.DualPair.FourierCoefficient
import D5.S3.Zeros.GRH.Lib.Adelic.CuspForms.ReproducingKernel
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Known result: Joint harmonics and global theta lifts between discrete series types. Here the
parameter has large gaps, and the types are given by integrable projector kernels. The lift is shown
to carry forms fixed by one kernel to forms fixed by the other, in both directions, without Howe
duality. Source: J.-S. Li, Theta lifting for unitary representations with nonzero cohomology, Duke
Math. J. 61 (1990); Howe, JAMS 2 (1989); A. Ichino, arXiv 2002.09148, Lemma 7.8.

This file: Theta lifts with joint harmonic data carry discrete series forms to the corresponding
type. -/

noncomputable section


open NumberField MeasureTheory Matrix ComplexConjugate MvPolynomial Fintype Norms.L2Operator
  Classical Complex CompactlySupported Set Heisenberg.IsVacuum
variable {E n n' ι : Type} [Field E] [CMType E] [WeilData E]
  [Fintype n] [Fintype n'] [Fintype ι] {s : n → _} {t : n' → _} (γ γ' : InfinitePlace E → ℤ)
  (l : _ → n → ℤ) (l' : _ → n' → ℤ) {η : ι → _}
  (Ω : GInf E s × GInf E t → fockSpace (realSigns E η) →L[ℂ] fockSpace (realSigns E η))
  (e : GInf E s → ℂ) (e' : GInf E t → ℂ) (Φ : fockSpace (realSigns E η))

/-- e is a cusp kernel of order 0; ∫ ⟨Φ, Ω(x,1)Φ⟩ ē(x)/e(1) dx ≠ 0; for theta kernels over Ω,
lifts of forms of type e by Φ⊗f with a level have type e', and lifts by v⊗f, v polynomial,
are R(α_v) of them, α_v in C_c. -/
structure IsHalfEdge where
  isCuspKernel_source : IsCuspKernel 0 e
  inner_ne_zero : ∫ x, realInner Φ (Ω (x, 1) Φ) * (conj (e x) / e 1) ≠ 0
  lift_isForm_and_eq_realConv : ∀ v ∈ range (polyVector _), ∃ α : C_c(_, ℂ), ∀ {V : Space E ι η} {S
    T y f} (Θ : ThetaKernel _ S T), (∀ x y v f, Θ.ω ((x, 1), y, 1) (V.integrated v f) =
    V.integrated (Ω (x, y) v) f) → S.IsForm e y → let F := S.lift Θ (V.integrated Φ f) y; (∀ K :
      OpenSubgroup _, HasLevel F K → T.IsForm e' F) ∧ S.lift Θ (V.integrated v f) y = realConv α F

/-- Φ is a half edge for Ω with kernels e, e', and also for Ω with its two groups exchanged with
kernels conj(e'), conj(e). -/
structure IsEdge extends IsHalfEdge Ω e e' Φ where
  swapped : IsHalfEdge (Ω ·.swap) (star e') (star e) Φ

/-- The element −l if the Boolean d is true, and l otherwise. -/
abbrev negIf {α} [Neg α] d (l : α) := cond d (-l) l

/-- The parameters l (signs s) and l' (signs t) correspond: at each infinite place w, l'_w and
−l_w match for signs t, s and weights γ_w, −γ'_w (`IsMatch`). -/
def ParamsCorrespond s t := ∀ w, IsMatch (.std t s (γ w) (-γ' w)) (l' w) (-l w)

/-- The product over the infinite places w of chosen joint harmonic polynomials (`IsJointHarmonic`;
arbitrary where none exists) for signs t, s and parameters l'_w, −l_w, each in the variables of
w. -/
def jointHarmonic {E n n' : Type} [Field E] [NumberField E] [Fintype n] [Fintype n']
    (γ γ' : InfinitePlace E → ℤ) (l : _ → n → ℤ) (l' : _ → n' → ℤ) s t := ∏ w,
  (epsilon (IsJointHarmonic (.std t s (γ w) (-γ' w)) (l' w) (-l w))).rename (w, ·)

variable {γ γ' l l' Ω} {π π' Φ : _ → _} [Nonempty n] [Nonempty n']
attribute [local simp] realConv rep_apply_apply realPairWeil pairHomInf realWeil_piTensor mul_assoc
  ContinuousMultilinearMap.map_smul_univ

omit [WeilData E] in
lemma integral_piTensor_eq_integratedRep {A} (hu : ∀ w, IsUnitaryRep A (π w) realInner) (k : _ →
  _ → ℂ) (a : ∀ w, Continuous (k w)) (hk : ∀ w, Integrable fun g ↦ k w g * ‖g.1.1‖ ^ A) (v : _ →
  fockSpace η) {X} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X] (T : _ →L[ℂ] X) :
  let F (x : GInf E s) := T (piTensor fun w ↦ k w (x w) • π w (x w) (v w))
  Integrable F ∧ ∫ x, F x = T (piTensor fun w ↦
    integratedRep (π w) (k w) (v w)) := have := (hu · |>.1)
  (fun I ↦ ⟨T.integrable_comp I, T.integral_comp_comm I ▸ congrArg T (ext fun z ↦
    ((modelEval z).integral_comp_comm I).symm.trans (congr(∏ w, $(map_integratedRep (hu w) (hk w)
                  (modelEval _) _)) ▸ integral_fintype_prod_eq_prod _ :))⟩) (.mono' (.const_mul
                  (.fintype_prod fun w ↦ (integrable_smul_rep (hu w) (hk w) _).norm) _)
    (Continuous.aestronglyMeasurable (by fun_prop)) (.of_forall fun _ ↦ piTensor.le_opNorm _))

/-- Let n, n' ≥ 1, (π_w, π'_w) oscillator pairs, Φ_w joint harmonics of parameters l_w, l'_w,
and let Ω act on pure tensors through ⊗π_w and ⊗π'_w. Then the tensor product of the Fock
vectors of the Φ_w is a half edge e_{−l} → e_{l'}. -/
lemma isHalfEdge_of_oscillatorPair {T : _ → _} (hp : ∀ w, OscillatorPair (T w) (π w) (π' w))
    (hΦ : ∀ w, IsJointHarmonic (T w) (l w) (l' w) (Φ w)) (hΩ : ∀ v, (∀ x, Ω (x, 1) (piTensor v)
    = piTensor fun w ↦ π w (x w) (v w)) ∧ ∀ y, Ω (1, y) (piTensor v) = piTensor fun w ↦ π' w (y w)
  (v w)) : IsHalfEdge Ω (typeKernel (-l) s) (typeKernel l' t) (piTensor (polyVector η <| Φ ·)) := by
  have A := integral_piTensor_eq_integratedRep (hp · |>.unitary_rep) _ (by fun_prop)
    (hΦ · |>.hasLargeGap.integrable_norm_pow_smul_dsKernel)
  simp [← hΩ] at A
  choose α e using fun a w ↦ (hp w).exists_bump_integratedRep_eq (hΦ w) (monomial (.curry a w) 1)
  refine (fun h ↦ ⟨h, by simpa [h.apply_one_ne_zero, conj_dsKernel_neg (hΦ _).gap, ↓mul_div,
    mul_comm, integral_div] using (A _ (realInner _)).2.trans_ne (by simp [realInner_piTensor,
    Finset.prod_eq_zero_iff, ne_zero_of_re_pos
    ((hp _).re_inner_integratedRep_pos (hΦ _))]), fun _ ⟨P, o⟩ ↦ o ▸ ⟨∑ a ∈ P.support, P.coeff a •
    bumpProduct (α a), ?_⟩⟩) (isCuspKernel_typeKernel (l := -l) (hΦ · |>.hasLargeGap.neg))
  introv W hy
  obtain ⟨⟨L, hL⟩, ⟨_, _, hC⟩, B, ⟨⟩⟩ := Θ.exists_clm_lift (hy.mem_rapidFunctions h),
    Θ.exists_norm_theta_mul_le (hy.mem_rapidFunctions h), (hΦ · |>.swap.hasLargeGap le_rfl), hy.1
  have M v g : _ = S.lift Θ (V.integrated (piTensor v) f) y g := (hL (V.integrated _ f) g).trans (by
    erw [← (A v (_ ∘L V.integrated.flip f)).2, ← hy.3 h.1.2]
    simp [← W, ← hL, ↓Θ.lift_omega_left hy.1, Space.lift, ← integral_const_mul]
    rw [← integral_inv_eq_self, integral_integral_swap]
    simp [-integral_const_mul, typeKernel, ((hΦ _).hasLargeGap
      le_rfl).isIdempotentKernel_dsKernel.3, ← conj_dsKernel_neg (hΦ _).gap]; ac_rfl
    exact (((A v (V.integrated.flip f)).1.norm.comp_inv.const_mul _).comp_fst _).mono'
      (by fun_prop) (.of_forall fun ⟨x, a⟩ ↦ (hC _ (a * (x, 1)) g).trans' (by simp [← W])))
  have R {k} b (a := by fun_prop) g :=
    integral_piTensor_eq_integratedRep (hp · |>.column_rep.unitary_rep) k a b
    (fun w ↦ integratedRep (π w) (dsKernel (l w)) (Φ w)) (L g ∘L V.integrated.flip f)
  obtain ⟨R₀, Q⟩ := R (B · |>.integrable_norm_pow_smul_dsKernel), fun a ↦
    R (integrable_bump_inv_smul _ <| α a ·)
  simp [(hp _).integratedRep_fix (hΦ _) (B _).integrable_norm_pow_smul_dsKernel
    (B _).isIdempotentKernel_dsKernel.convolution_self, M, ← e, ← hΩ, ← W, ← hL, ← lift_mul_right,
    -Prod.forall] at R₀ Q
  use (funext (R₀ · |>.2) ▸ T.isForm_realConv (isCuspKernel_typeKernel B) ⟨.congr (by fun_prop)
    (one_mul · ▸ ((lift_mul_right Θ 1 _).trans (hL ..)).symm), Θ.fixesLeft_lift, ·, ·⟩ (R₀ · |>.1))
  ext; simp [bumpProduct, Finset.sum_mul, Q, integral_finsetSum, Integrable.const_mul]
  nth_rw 1 [P.as_sum]; simp [hL, piTensor_polyVector, monomial_eq, C_mul', prod_prod_type]

/-- In positive ranks, if each Φ_w is a joint harmonic (`IsJointHarmonic`) with parameters l'_w,
−l_w for `FockDualPair.std` t s γ_w (−γ'_w), the Fock vector of ∏_w Φ_w (separate variables per
place) is a `IsEdge` for `realPairWeil` γ γ' with kernels `typeKernel` of l, l'.

Known result: Joint harmonics and global theta lifts between discrete series types. -/
lemma isEdge_of_isJointHarmonic (hΦ : ∀ w, IsJointHarmonic (.std t s (γ w) (-γ' w)) (l' w) (-l w) (Φ
  w)) : IsEdge (realPairWeil γ γ') (typeKernel l s) (typeKernel l' t) ↑(∏ w, rename (w, ·) (Φ w)) :=
  piTensor_polyVector Φ ▸ ⟨neg_neg l ▸ isHalfEdge_of_oscillatorPair (fun _ ↦ .swap
  oscillatorPair_detTwist) (hΦ · |>.swap)
  (by simp), by simpa +unfoldPartialApp [typeKernel, ← conj_dsKernel_neg (hΦ _).gap',
  ← (conj_dsKernel_neg (hΦ _).gap), Pi.star_def] using
  isHalfEdge_of_oscillatorPair (fun x ↦ oscillatorPair_detTwist) hΦ (by simp)⟩

/-- Let n, n' ≥ 1. If l, l' correspond for the weights γ, γ' and signs s, t, the Fock vector of
the product `jointHarmonic` of joint harmonics is an edge e_l → e_{l'} for the real Weil
representation of weights γ, γ'. -/
lemma ParamsCorrespond.isEdge_jointHarmonic (h : ParamsCorrespond γ γ' l l' s t) :
  IsEdge (realPairWeil γ γ') (typeKernel l s) (typeKernel l' t) (jointHarmonic γ γ' l l' s t) :=
  isEdge_of_isJointHarmonic (epsilon_spec <| h · |>.exists_isJointHarmonic)
