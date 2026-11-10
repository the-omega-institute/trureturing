/- GID: D5/S3/HilbertOperators/UnitaryPowerDilation
   generality: G
   mirror-B: D5/B/S3/HilbertOperators/UnitaryPowerDilation
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Analysis.CStarAlgebra.Unitary.Span, mathlib/module/Mathlib.Analysis.InnerProductSpace.l2Space, mathlib/module/Mathlib.Analysis.InnerProductSpace.Adjoint]
   utility: none
   digest: Every contraction on an arbitrary complete complex Hilbert space has one unitary dilation simultaneously compressing all natural powers. -/

/-
Halmos.lean source section:
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa

Schaeffer.lean source section:
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa

Source: LeanPool/lean-pool at 89f2facbb6478492222a9b43047e9c837bc65be6,
LeanPool/OperatorTheory/Operator/Dilation/{Halmos,Schaeffer}.lean.
The full Apache licenses are docs/reports/brooks-suppliers/lean-pool-LICENSE.txt
and docs/reports/brooks-suppliers/daviskahan-LICENSE.txt. The complete Pool
NOTICE and NOTICE.extra.yml are retained as .txt under
 docs/reports/unitary-power-dilation-suppliers/.
Ancestor: savarin/lean-operator-theory at 6f90bb7e6b056b54f56005e0416d77d6d7c2a478.
Modification notice: combine the consumed Halmos and repeated-interaction
network proof in one native namespace, adapt imports and module visibility,
make support private, and omit the unused simple bilateral-shift branch and
unused definitional application helpers. Their source equalities are
retained inline in the consuming proofs. The mathematical endpoint and
substantive proof steps are preserved. Full source hashes and correspondence
are in Library/HilbertOperators/leanpool2026unitarypowerdilation.md.
Retire this transplant when this repository adopts a Mathlib pin providing an
equivalent arbitrary-complete-complex-Hilbert common-all-powers theorem;
replace it with direct reuse and remove support thereby made unnecessary.
-/

import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Algebra.Star.Unitary

namespace D5.S3.HilbertOperators.UnitaryPowerDilation

open ContinuousLinearMap
open scoped ENNReal InnerProductSpace

universe u
noncomputable section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

private noncomputable def halmosOffDiagonalLinear (T : E →L[ℂ] E) :
    WithLp 2 (E × E) →ₗ[ℂ] WithLp 2 (E × E) where
  toFun x := WithLp.toLp 2 (T x.snd, adjoint T x.fst)
  map_add' x y := by
    apply WithLp.ofLp_injective 2
    change (T (x.snd + y.snd), adjoint T (x.fst + y.fst)) =
      (T x.snd + T y.snd, adjoint T x.fst + adjoint T y.fst)
    exact Prod.ext (map_add T x.snd y.snd) (map_add (adjoint T) x.fst y.fst)
  map_smul' c x := by
    apply WithLp.ofLp_injective 2
    change (T (c • x.snd), adjoint T (c • x.fst)) =
      (c • T x.snd, c • adjoint T x.fst)
    exact Prod.ext (map_smul T c x.snd) (map_smul (adjoint T) c x.fst)

private theorem halmosOffDiagonalLinear_bound (T : E →L[ℂ] E)
    (x : WithLp 2 (E × E)) :
    ‖halmosOffDiagonalLinear T x‖ ≤ ‖T‖ * ‖x‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg T) (norm_nonneg x))).mp
  calc
    ‖halmosOffDiagonalLinear T x‖ ^ 2 = ‖T x.snd‖ ^ 2 + ‖adjoint T x.fst‖ ^ 2 := by
      rw [WithLp.prod_norm_sq_eq_of_L2]
      rfl
    _ ≤ (‖T‖ * ‖x.snd‖) ^ 2 + (‖T‖ * ‖x.fst‖) ^ 2 := by
      exact add_le_add
        (pow_le_pow_left₀ (norm_nonneg _) (T.le_opNorm x.snd) 2)
        (pow_le_pow_left₀ (norm_nonneg _) (by
          simpa only [LinearIsometryEquiv.norm_map] using (adjoint T).le_opNorm x.fst) 2)
    _ = ‖T‖ ^ 2 * (‖x.fst‖ ^ 2 + ‖x.snd‖ ^ 2) := by ring
    _ = ‖T‖ ^ 2 * ‖x‖ ^ 2 := by rw [WithLp.prod_norm_sq_eq_of_L2]
    _ = (‖T‖ * ‖x‖) ^ 2 := by ring

private noncomputable def halmosOffDiagonal (T : E →L[ℂ] E) :
    WithLp 2 (E × E) →L[ℂ] WithLp 2 (E × E) :=
  (halmosOffDiagonalLinear T).mkContinuous ‖T‖ (halmosOffDiagonalLinear_bound T)

@[simp]
private theorem halmosOffDiagonal_apply (T : E →L[ℂ] E)
    (x : WithLp 2 (E × E)) :
    halmosOffDiagonal T x = WithLp.toLp 2 (T x.snd, adjoint T x.fst) :=
  rfl

private theorem norm_halmosOffDiagonal_le (T : E →L[ℂ] E) :
    ‖halmosOffDiagonal T‖ ≤ ‖T‖ :=
  LinearMap.mkContinuous_norm_le _ (norm_nonneg T) (halmosOffDiagonalLinear_bound T)

private theorem isSelfAdjoint_halmosOffDiagonal (T : E →L[ℂ] E) :
    IsSelfAdjoint (halmosOffDiagonal T) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro x y
  change ⟪halmosOffDiagonal T x, y⟫_ℂ = ⟪x, halmosOffDiagonal T y⟫_ℂ
  rw [halmosOffDiagonal_apply, halmosOffDiagonal_apply]
  simp only [WithLp.prod_inner_apply]
  simp only [adjoint_inner_right, adjoint_inner_left, add_comm]
  rfl

private noncomputable def halmosGrading :
    WithLp 2 (E × E) →L[ℂ] WithLp 2 (E × E) :=
  (LinearIsometryEquiv.withLpProdCongr 2
    (LinearIsometryEquiv.refl ℂ E) (LinearIsometryEquiv.neg ℂ (E := E)) :
      WithLp 2 (E × E) →L[ℂ] WithLp 2 (E × E))

private theorem one_sub_halmosOffDiagonal_sq_commute_grading (T : E →L[ℂ] E) :
    Commute (1 - halmosOffDiagonal T ^ 2) (halmosGrading (E := E)) := by
  rw [Commute]
  apply ContinuousLinearMap.ext
  intro x
  simp only [mul_apply_eq_comp, pow_two, sub_apply, one_apply_eq_self,
    (show ∀ x : WithLp 2 (E × E),
      halmosGrading x = WithLp.toLp 2 (x.fst, -x.snd) from fun _ => rfl), halmosOffDiagonal_apply, WithLp.toLp_fst,
    WithLp.toLp_snd, map_neg]
  apply WithLp.ofLp_injective 2
  change (x.fst - T (adjoint T x.fst), -x.snd - -(adjoint T (T x.snd))) =
    (x.fst - T (adjoint T x.fst), -(x.snd - adjoint T (T x.snd)))
  apply Prod.ext
  · rfl
  · abel_nf

private theorem sqrt_one_sub_halmosOffDiagonal_sq_fst_zero (T : E →L[ℂ] E)
    (x : E) :
    ((CFC.sqrt (1 - halmosOffDiagonal T ^ 2) :
      WithLp 2 (E × E) →L[ℂ] WithLp 2 (E × E))
        (WithLp.toLp 2 (0, x))).fst = 0 := by
  have hcomm : Commute (CFC.sqrt (1 - halmosOffDiagonal T ^ 2))
      (halmosGrading (E := E)) := by
    simpa only [CFC.sqrt] using
      (one_sub_halmosOffDiagonal_sq_commute_grading T).cfcₙ_nnreal NNReal.sqrt
  have happ := congrArg
    (fun q : WithLp 2 (E × E) →L[ℂ] WithLp 2 (E × E) =>
      (q (WithLp.toLp 2 (0, x))).fst) hcomm.eq
  simp only [mul_apply_eq_comp, (show ∀ x : WithLp 2 (E × E),
      halmosGrading x = WithLp.toLp 2 (x.fst, -x.snd) from fun _ => rfl), WithLp.toLp_fst,
    WithLp.toLp_snd] at happ
  have hneg : WithLp.toLp 2 ((0 : E), -x) =
      -(WithLp.toLp 2 ((0 : E), x) : WithLp 2 (E × E)) := by
    rw [← WithLp.toLp_neg]
    congr 1
    apply Prod.ext
    · exact (neg_zero : -(0 : E) = 0).symm
    · rfl
  rw [hneg, map_neg, WithLp.neg_fst] at happ
  let v : E := ((CFC.sqrt (1 - halmosOffDiagonal T ^ 2) :
    WithLp 2 (E × E) →L[ℂ] WithLp 2 (E × E))
      (WithLp.toLp 2 (0, x))).fst
  change -v = v at happ
  have hvadd : v + v = 0 := by
    calc
      v + v = -v + v := by rw [happ]
      _ = 0 := neg_add_cancel v
  have htwo : (2 : ℂ) • v = 0 := by
    simpa only [two_smul] using hvadd
  exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)

private noncomputable def halmosFlip :
    WithLp 2 (E × E) →L[ℂ] WithLp 2 (E × E) :=
  LinearIsometryEquiv.withLpProdComm 2 ℂ E E

private theorem halmosFlip_mem_unitary :
    halmosFlip (E := E) ∈ unitary (WithLp 2 (E × E) →L[ℂ] WithLp 2 (E × E)) := by
  exact (Unitary.linearIsometryEquiv.symm
    (LinearIsometryEquiv.withLpProdComm 2 ℂ E E)).property

/-- Every contraction has a unitary extension on the Hilbert direct sum of two copies of its
space, whose compression to the first summand is the original operator. -/
private theorem exists_halmos_unitary_dilation (T : E →L[ℂ] E) (hT : ‖T‖ ≤ 1) :
    ∃ (U : WithLp 2 (E × E) →L[ℂ] WithLp 2 (E × E)),
    U ∈ unitary (WithLp 2 (E × E) →L[ℂ] WithLp 2 (E × E)) ∧
    ∀ x : E, (U (WithLp.toLp 2 (x, 0))).fst = T x := by
  let a := halmosOffDiagonal T
  let w := a + Complex.I • CFC.sqrt (1 - a ^ 2)
  let U := w * halmosFlip (E := E)
  have ha : IsSelfAdjoint a := isSelfAdjoint_halmosOffDiagonal T
  have haw : ‖a‖ ≤ 1 := (norm_halmosOffDiagonal_le T).trans hT
  have hw : w ∈ unitary (WithLp 2 (E × E) →L[ℂ] WithLp 2 (E × E)) :=
    ha.self_add_I_smul_cfcSqrt_sub_sq_mem_unitary a haw
  refine ⟨U, ?_, ?_⟩
  · exact (unitary _).mul_mem hw halmosFlip_mem_unitary
  · intro x
    simp only [U, w, a, mul_apply_eq_comp, (show ∀ x : WithLp 2 (E × E),
      halmosFlip x = WithLp.toLp 2 (x.snd, x.fst) from fun _ => rfl), WithLp.toLp_fst,
      WithLp.toLp_snd, add_apply, halmosOffDiagonal_apply, smul_apply,
      WithLp.add_fst, WithLp.smul_fst, map_zero]
    rw [sqrt_one_sub_halmosOffDiagonal_sq_fst_zero]
    simp only [add_zero, smul_zero]


/-- One site in the repeated-interaction model: a system and one environment copy. -/
private abbrev SchaefferNetworkFiber (E : Type u) := WithLp 2 (E × E)

/-- The bilateral Hilbert sum of system-environment sites. -/
private abbrev SchaefferNetworkSpace (E : Type u) [NormedAddCommGroup E] :=
  lp (fun _ : ℤ => SchaefferNetworkFiber E) 2

/-- Insert the system space into the system component of one network site. -/
private noncomputable def schaefferFiberEmbedding :
    E →L[ℂ] SchaefferNetworkFiber E :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ E E).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.inl ℂ E E)

/-- Embed the original space at the system component of site zero. -/
private noncomputable def schaefferNetworkEmbedding :
    E →L[ℂ] SchaefferNetworkSpace E :=
  (lp.singleContinuousLinearMap ℂ (fun _ : ℤ => SchaefferNetworkFiber E) 2 0).comp
    schaefferFiberEmbedding

omit [CompleteSpace E] in
/-- The network embedding preserves inner products. -/
private theorem inner_schaefferNetworkEmbedding (x y : E) :
    ⟪schaefferNetworkEmbedding x, schaefferNetworkEmbedding y⟫_ℂ = ⟪x, y⟫_ℂ := by
  simp only [(show ∀ x : E, schaefferNetworkEmbedding x =
      lp.single 2 (0 : ℤ) (WithLp.toLp 2 (x, 0)) from fun _ => rfl), lp.inner_single_left,
    lp.single_apply_self, WithLp.prod_inner_apply, inner_zero_right, add_zero]

/-- The adjoint of the network embedding extracts the system component at site zero. -/
private theorem adjoint_schaefferNetworkEmbedding_apply (f : SchaefferNetworkSpace E) :
    ContinuousLinearMap.adjoint
      (schaefferNetworkEmbedding : E →L[ℂ] SchaefferNetworkSpace E) f = (f 0).fst := by
  refine ext_inner_right ℂ fun x => ?_
  rw [ContinuousLinearMap.adjoint_inner_left]
  simp only [(show ∀ x : E, schaefferNetworkEmbedding x =
      lp.single 2 (0 : ℤ) (WithLp.toLp 2 (x, 0)) from fun _ => rfl), lp.inner_single_right,
    WithLp.prod_inner_apply, inner_zero_right, add_zero]
  rfl

private def lpPointwiseForward
    (W : SchaefferNetworkFiber E ≃ₗᵢ[ℂ] SchaefferNetworkFiber E)
    (f : SchaefferNetworkSpace E) : SchaefferNetworkSpace E :=
  ⟨fun i => W (f i), by
    change Memℓp (fun i : ℤ => W (f i)) 2
    rw [memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
    simpa only [W.norm_map] using
      (lp.memℓp f).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)⟩

omit [CompleteSpace E] in
private theorem norm_lpPointwiseForward
    (W : SchaefferNetworkFiber E ≃ₗᵢ[ℂ] SchaefferNetworkFiber E)
    (f : SchaefferNetworkSpace E) : ‖lpPointwiseForward W f‖ = ‖f‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [show ‖lpPointwiseForward W f‖ ^ 2 =
      ∑' i : ℤ, ‖lpPointwiseForward W f i‖ ^ (2 : ℕ) by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞))
        (by norm_num : 0 < (2 : ℝ≥0∞).toReal) (lpPointwiseForward W f)]
  rw [show ‖f‖ ^ 2 = ∑' i : ℤ, ‖f i‖ ^ (2 : ℕ) by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞))
        (by norm_num : 0 < (2 : ℝ≥0∞).toReal) f]
  simp only [(show ∀ (W : SchaefferNetworkFiber E ≃ₗᵢ[ℂ] SchaefferNetworkFiber E)
      (f : SchaefferNetworkSpace E) (i : ℤ),
      lpPointwiseForward W f i = W (f i) from fun _ _ _ => rfl), W.norm_map]

/-- Apply the same fiberwise unitary at every integer site. -/
private def lpPointwiseEquiv
    (W : SchaefferNetworkFiber E ≃ₗᵢ[ℂ] SchaefferNetworkFiber E) :
    SchaefferNetworkSpace E ≃ₗᵢ[ℂ] SchaefferNetworkSpace E where
  toFun := lpPointwiseForward W
  invFun := lpPointwiseForward W.symm
  left_inv f := by
    apply lp.ext
    funext i
    simp only [(show ∀ (W : SchaefferNetworkFiber E ≃ₗᵢ[ℂ] SchaefferNetworkFiber E)
      (f : SchaefferNetworkSpace E) (i : ℤ),
      lpPointwiseForward W f i = W (f i) from fun _ _ _ => rfl), W.symm_apply_apply]
  right_inv f := by
    apply lp.ext
    funext i
    simp only [(show ∀ (W : SchaefferNetworkFiber E ≃ₗᵢ[ℂ] SchaefferNetworkFiber E)
      (f : SchaefferNetworkSpace E) (i : ℤ),
      lpPointwiseForward W f i = W (f i) from fun _ _ _ => rfl), W.apply_symm_apply]
  map_add' _ _ := by
    apply lp.ext
    funext i
    simp only [(show ∀ (W : SchaefferNetworkFiber E ≃ₗᵢ[ℂ] SchaefferNetworkFiber E)
      (f : SchaefferNetworkSpace E) (i : ℤ),
      lpPointwiseForward W f i = W (f i) from fun _ _ _ => rfl), lp.coeFn_add, Pi.add_apply, map_add]
  map_smul' _ _ := by
    apply lp.ext
    funext i
    simp only [(show ∀ (W : SchaefferNetworkFiber E ≃ₗᵢ[ℂ] SchaefferNetworkFiber E)
      (f : SchaefferNetworkSpace E) (i : ℤ),
      lpPointwiseForward W f i = W (f i) from fun _ _ _ => rfl), lp.coeFn_smul, Pi.smul_apply, map_smul,
      RingHom.id_apply]
  norm_map' := norm_lpPointwiseForward W

/-- Lift a two-coordinate unitary to the pointwise unitary on the network space. -/
private def schaefferPointwiseUnitary
    (J : unitary (SchaefferNetworkFiber E →L[ℂ] SchaefferNetworkFiber E)) :
    unitary (SchaefferNetworkSpace E →L[ℂ] SchaefferNetworkSpace E) :=
  Unitary.linearIsometryEquiv.symm
    (lpPointwiseEquiv (Unitary.linearIsometryEquiv J))

omit [CompleteSpace E] in
omit [InnerProductSpace ℂ E] in
private theorem summable_network_fst_sq (f : SchaefferNetworkSpace E) :
    Summable fun i : ℤ => ‖(f i).fst‖ ^ (2 : ℕ) := by
  have hf : Summable fun i : ℤ => ‖f i‖ ^ (2 : ℕ) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      (lp.memℓp f).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
  refine hf.of_nonneg_of_le (fun _ => sq_nonneg _) (fun i => ?_)
  have h := WithLp.prod_norm_sq_eq_of_L2 (f i)
  nlinarith only [h, sq_nonneg ‖(f i).snd‖]

omit [CompleteSpace E] in
omit [InnerProductSpace ℂ E] in
private theorem summable_network_snd_sq (f : SchaefferNetworkSpace E) :
    Summable fun i : ℤ => ‖(f i).snd‖ ^ (2 : ℕ) := by
  have hf : Summable fun i : ℤ => ‖f i‖ ^ (2 : ℕ) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      (lp.memℓp f).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
  refine hf.of_nonneg_of_le (fun _ => sq_nonneg _) (fun i => ?_)
  have h := WithLp.prod_norm_sq_eq_of_L2 (f i)
  nlinarith only [h, sq_nonneg ‖(f i).fst‖]

private def schaefferIntShift : ℤ ≃ ℤ := Equiv.addRight (1 : ℤ)

private def schaefferRouteForward (f : SchaefferNetworkSpace E) :
    SchaefferNetworkSpace E :=
  ⟨fun i => WithLp.toLp 2 ((f i).fst, (f (schaefferIntShift.symm i)).snd), by
    change Memℓp
      (fun i : ℤ => WithLp.toLp 2
        ((f i).fst, (f (schaefferIntShift.symm i)).snd)) 2
    rw [memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
    have hs : Summable fun i : ℤ =>
        ‖(f (schaefferIntShift.symm i)).snd‖ ^ (2 : ℕ) :=
      schaefferIntShift.symm.summable_iff.mpr (summable_network_snd_sq f)
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two,
      WithLp.prod_norm_sq_eq_of_L2, WithLp.toLp_fst, WithLp.toLp_snd] using
      (summable_network_fst_sq f).add hs⟩

private def schaefferRouteBackward (f : SchaefferNetworkSpace E) :
    SchaefferNetworkSpace E :=
  ⟨fun i => WithLp.toLp 2 ((f i).fst, (f (schaefferIntShift i)).snd), by
    change Memℓp
      (fun i : ℤ => WithLp.toLp 2 ((f i).fst, (f (schaefferIntShift i)).snd)) 2
    rw [memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
    have hs : Summable fun i : ℤ => ‖(f (schaefferIntShift i)).snd‖ ^ (2 : ℕ) :=
      schaefferIntShift.summable_iff.mpr (summable_network_snd_sq f)
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two,
      WithLp.prod_norm_sq_eq_of_L2, WithLp.toLp_fst, WithLp.toLp_snd] using
      (summable_network_fst_sq f).add hs⟩

omit [CompleteSpace E] in
omit [InnerProductSpace ℂ E] in
private theorem norm_schaefferRouteForward (f : SchaefferNetworkSpace E) :
    ‖schaefferRouteForward f‖ = ‖f‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  have ha := summable_network_fst_sq f
  have hb := summable_network_snd_sq f
  have hbShift : Summable fun i : ℤ =>
      ‖(f (schaefferIntShift.symm i)).snd‖ ^ (2 : ℕ) :=
    schaefferIntShift.symm.summable_iff.mpr hb
  calc
    ‖schaefferRouteForward f‖ ^ 2 =
        ∑' i : ℤ, (‖(f i).fst‖ ^ (2 : ℕ) +
          ‖(f (schaefferIntShift.symm i)).snd‖ ^ (2 : ℕ)) := by
      rw [show ‖schaefferRouteForward f‖ ^ 2 =
          ∑' i : ℤ, ‖schaefferRouteForward f i‖ ^ (2 : ℕ) by
        simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
          lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞))
            (by norm_num : 0 < (2 : ℝ≥0∞).toReal) (schaefferRouteForward f)]
      simp only [(show ∀ (f : SchaefferNetworkSpace E) (i : ℤ), schaefferRouteForward f i =
      WithLp.toLp 2 ((f i).fst, (f (schaefferIntShift.symm i)).snd) from fun _ _ => rfl), WithLp.prod_norm_sq_eq_of_L2,
        WithLp.toLp_fst, WithLp.toLp_snd]
    _ = (∑' i : ℤ, ‖(f i).fst‖ ^ (2 : ℕ)) +
        ∑' i : ℤ, ‖(f (schaefferIntShift.symm i)).snd‖ ^ (2 : ℕ) :=
      ha.tsum_add hbShift
    _ = (∑' i : ℤ, ‖(f i).fst‖ ^ (2 : ℕ)) +
        ∑' i : ℤ, ‖(f i).snd‖ ^ (2 : ℕ) := by
      rw [schaefferIntShift.symm.tsum_eq
        (fun i : ℤ => ‖(f i).snd‖ ^ (2 : ℕ))]
    _ = ∑' i : ℤ, (‖(f i).fst‖ ^ (2 : ℕ) + ‖(f i).snd‖ ^ (2 : ℕ)) :=
      (ha.tsum_add hb).symm
    _ = ‖f‖ ^ 2 := by
      rw [show ‖f‖ ^ 2 = ∑' i : ℤ, ‖f i‖ ^ (2 : ℕ) by
        simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
          lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞))
            (by norm_num : 0 < (2 : ℝ≥0∞).toReal) f]
      simp only [WithLp.prod_norm_sq_eq_of_L2]

/-- Keep each system component fixed and shift each environment component one site right. -/
private def schaefferRouteEquiv :
    SchaefferNetworkSpace E ≃ₗᵢ[ℂ] SchaefferNetworkSpace E where
  toFun := schaefferRouteForward
  invFun := schaefferRouteBackward
  left_inv f := by
    apply lp.ext
    funext i
    apply WithLp.ofLp_injective
    simp only [(show ∀ (f : SchaefferNetworkSpace E) (i : ℤ), schaefferRouteBackward f i =
      WithLp.toLp 2 ((f i).fst, (f (schaefferIntShift i)).snd) from fun _ _ => rfl), (show ∀ (f : SchaefferNetworkSpace E) (i : ℤ), schaefferRouteForward f i =
      WithLp.toLp 2 ((f i).fst, (f (schaefferIntShift.symm i)).snd) from fun _ _ => rfl),
      WithLp.toLp_fst, WithLp.toLp_snd, WithLp.ofLp_toLp,
      schaefferIntShift.symm_apply_apply]
    exact Prod.eta _
  right_inv f := by
    apply lp.ext
    funext i
    apply WithLp.ofLp_injective
    simp only [(show ∀ (f : SchaefferNetworkSpace E) (i : ℤ), schaefferRouteBackward f i =
      WithLp.toLp 2 ((f i).fst, (f (schaefferIntShift i)).snd) from fun _ _ => rfl), (show ∀ (f : SchaefferNetworkSpace E) (i : ℤ), schaefferRouteForward f i =
      WithLp.toLp 2 ((f i).fst, (f (schaefferIntShift.symm i)).snd) from fun _ _ => rfl),
      WithLp.toLp_fst, WithLp.toLp_snd, WithLp.ofLp_toLp,
      schaefferIntShift.apply_symm_apply]
    exact Prod.eta _
  map_add' _ _ := by
    apply lp.ext
    funext i
    apply WithLp.ofLp_injective
    apply Prod.ext <;> rfl
  map_smul' _ _ := by
    apply lp.ext
    funext i
    apply WithLp.ofLp_injective
    apply Prod.ext <;> rfl
  norm_map' := norm_schaefferRouteForward

private def schaefferRouteUnitary :
    unitary (SchaefferNetworkSpace E →L[ℂ] SchaefferNetworkSpace E) :=
  Unitary.linearIsometryEquiv.symm schaefferRouteEquiv

/-- Apply the same Halmos interaction at every site, then move each environment output
one site to the right. -/
private def schaefferGlobalUnitary
    (J : unitary (SchaefferNetworkFiber E →L[ℂ] SchaefferNetworkFiber E)) :
    unitary (SchaefferNetworkSpace E →L[ℂ] SchaefferNetworkSpace E) :=
  schaefferRouteUnitary * schaefferPointwiseUnitary J

private noncomputable def schaefferGlobalOperator
    (J : unitary (SchaefferNetworkFiber E →L[ℂ] SchaefferNetworkFiber E)) :
    SchaefferNetworkSpace E →L[ℂ] SchaefferNetworkSpace E :=
  schaefferGlobalUnitary J

private theorem schaefferGlobalOperator_mem_unitary
    (J : unitary (SchaefferNetworkFiber E →L[ℂ] SchaefferNetworkFiber E)) :
    schaefferGlobalOperator J ∈
      unitary (SchaefferNetworkSpace E →L[ℂ] SchaefferNetworkSpace E) :=
  (schaefferGlobalUnitary J).property

@[simp]
private theorem schaefferGlobalOperator_apply
    (J : unitary (SchaefferNetworkFiber E →L[ℂ] SchaefferNetworkFiber E))
    (f : SchaefferNetworkSpace E) (i : ℤ) :
    schaefferGlobalOperator J f i = WithLp.toLp 2
      (((J : SchaefferNetworkFiber E →L[ℂ] SchaefferNetworkFiber E) (f i)).fst,
        ((J : SchaefferNetworkFiber E →L[ℂ] SchaefferNetworkFiber E)
          (f (schaefferIntShift.symm i))).snd) := by
  change schaefferRouteEquiv
    (lpPointwiseEquiv (Unitary.linearIsometryEquiv J) f) i = _
  rfl

private noncomputable def schaefferOrbit
    (J : unitary (SchaefferNetworkFiber E →L[ℂ] SchaefferNetworkFiber E))
    (n : ℕ) (x : E) : SchaefferNetworkSpace E :=
  (schaefferGlobalOperator J ^ n) (schaefferNetworkEmbedding x)

@[simp]
private theorem schaefferOrbit_succ_apply
    (J : unitary (SchaefferNetworkFiber E →L[ℂ] SchaefferNetworkFiber E))
    (n : ℕ) (x : E) (i : ℤ) :
    schaefferOrbit J (n + 1) x i = WithLp.toLp 2
      (((J : SchaefferNetworkFiber E →L[ℂ] SchaefferNetworkFiber E)
        (schaefferOrbit J n x i)).fst,
       ((J : SchaefferNetworkFiber E →L[ℂ] SchaefferNetworkFiber E)
        (schaefferOrbit J n x (schaefferIntShift.symm i))).snd) := by
  rw [schaefferOrbit, pow_succ']
  exact schaefferGlobalOperator_apply J _ i

private theorem schaeffer_power_state
    (T : E →L[ℂ] E)
    (J : unitary (SchaefferNetworkFiber E →L[ℂ] SchaefferNetworkFiber E))
    (hJ : ∀ z : E,
      ((J : SchaefferNetworkFiber E →L[ℂ] SchaefferNetworkFiber E)
        (WithLp.toLp 2 (z, 0))).fst = T z)
    (n : ℕ) (x : E) :
    (schaefferOrbit J n x 0).fst = (T ^ n) x ∧
    (schaefferOrbit J n x 0).snd = 0 ∧
    ∀ i : ℤ, i < 0 → schaefferOrbit J n x i = 0 := by
  induction n with
  | zero =>
      refine ⟨?_, ?_, ?_⟩
      · simp only [schaefferOrbit, pow_zero, one_apply_eq_self,
          (show ∀ x : E, schaefferNetworkEmbedding x =
      lp.single 2 (0 : ℤ) (WithLp.toLp 2 (x, 0)) from fun _ => rfl), lp.single_apply_self,
          WithLp.toLp_fst]
      · simp only [schaefferOrbit, pow_zero, one_apply_eq_self,
          (show ∀ x : E, schaefferNetworkEmbedding x =
      lp.single 2 (0 : ℤ) (WithLp.toLp 2 (x, 0)) from fun _ => rfl), lp.single_apply_self,
          WithLp.toLp_snd]
      intro i hi
      simp only [schaefferOrbit, pow_zero, one_apply_eq_self,
        (show ∀ x : E, schaefferNetworkEmbedding x =
      lp.single 2 (0 : ℤ) (WithLp.toLp 2 (x, 0)) from fun _ => rfl)]
      rw [lp.single_apply_ne]
      exact ne_of_lt hi
  | succ n ih =>
      rcases ih with ⟨ihfst, ihsnd, ihneg⟩
      have hzero : schaefferOrbit J n x 0 = WithLp.toLp 2 ((T ^ n) x, 0) := by
        apply WithLp.ofLp_injective
        exact Prod.ext ihfst ihsnd
      refine ⟨?_, ?_, ?_⟩
      · rw [schaefferOrbit_succ_apply, WithLp.toLp_fst, hzero, hJ,
          pow_succ', mul_apply_eq_comp]
      · rw [schaefferOrbit_succ_apply, WithLp.toLp_snd]
        have hm1 : schaefferIntShift.symm (0 : ℤ) = -1 := rfl
        rw [hm1, ihneg (-1) (by omega), map_zero]
        rfl
      · intro i hi
        rw [schaefferOrbit_succ_apply]
        have hprev : schaefferIntShift.symm i < 0 := by
          change i - 1 < 0
          omega
        rw [ihneg i hi, ihneg _ hprev, map_zero]
        rfl

/-- Every contraction has a unitary power dilation on a larger Hilbert space. -/
theorem exists_unitary_power_dilation (T : E →L[ℂ] E) (hT : ‖T‖ ≤ 1) :
    ∃ (H : Type u) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (_ : CompleteSpace H)
      (V : E →L[ℂ] H) (U : H →L[ℂ] H),
    (∀ x y : E, ⟪V x, V y⟫_ℂ = ⟪x, y⟫_ℂ) ∧
    U ∈ unitary (H →L[ℂ] H) ∧
    (∀ (n : ℕ) (x : E),
      ContinuousLinearMap.adjoint V ((U ^ n) (V x)) = (T ^ n) x) := by
  obtain ⟨J, hJunitary, hJcompression⟩ := exists_halmos_unitary_dilation T hT
  let JU : unitary (SchaefferNetworkFiber E →L[ℂ] SchaefferNetworkFiber E) :=
    ⟨J, hJunitary⟩
  have hJU : ∀ z : E,
      ((JU : SchaefferNetworkFiber E →L[ℂ] SchaefferNetworkFiber E)
        (WithLp.toLp 2 (z, 0))).fst = T z := hJcompression
  refine ⟨SchaefferNetworkSpace E, inferInstance, inferInstance, inferInstance,
    schaefferNetworkEmbedding, schaefferGlobalOperator JU, ?_, ?_, ?_⟩
  · exact inner_schaefferNetworkEmbedding
  · exact schaefferGlobalOperator_mem_unitary JU
  · intro n x
    rw [adjoint_schaefferNetworkEmbedding_apply]
    change (schaefferOrbit JU n x 0).fst = (T ^ n) x
    exact (schaeffer_power_state T JU hJU n x).1


end
end D5.S3.HilbertOperators.UnitaryPowerDilation
