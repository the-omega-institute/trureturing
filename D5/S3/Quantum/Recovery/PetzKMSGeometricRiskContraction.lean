import D5.S3.Quantum.Recovery.PetzCommutingInputUniformRecovery
import D5.S3.Quantum.Foundation.FiniteHermitianTraceDuality
import D5.S3.Quantum.Information.StrongSubadditivity.Physlib.ForMathlib.HermitianMat.Inner
import Mathlib.Analysis.InnerProductSpace.Positive

/-!
# KMS geometric-risk contraction for ordinary Petz recovery

The quarter-root sandwich intertwines the KMS map with a Gram operator.
Reversing the factors transfers its nonzero eigenvalues even on singular
references. Hermitian trace duality tests the resulting weighted residual.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator InnerProductSpace
open D5.S3.Quantum.Foundation.FiniteStateChannel (DensityState)
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf (MatrixMap)
open D5.S3.Quantum.Foundation.FiniteTraceDistance (traceNorm)
open D5.S3.Quantum.Foundation.FiniteHermitianTraceDuality (exists_hermitian_traceNorm_test)
open D5.S3.Quantum.Information.PartialTraceMutualInformation (density_posSemidef)
open D5.S3.Quantum.Divergence.SupportAwareRelativeEntropy (SupportContained)
open D5.S3.Quantum.Recovery.SpectralTransposeRecovery (spectralInverseSqrt spectralSupport)
open D5.S3.Quantum.Lieb.SupportPerspectiveTransport (spectral_sqrt_normalization)
open PetzPositiveTraceFidelity (traceDual_unital)
open PetzPositiveTracePostselection (ordinaryPetz)
open PetzPostselectionSpectralJensen (stateMatrix)
open PetzLikelihoodRectangularAmplitude (commutingResolution likelihoodOperator)
open QuadraticBayesRiskGeometricPetz (geometricRisk tracePair)

open private map_le from D5.S3.Quantum.Recovery.PetzPositiveTracePostselection
open private geometric_quadratic_le scoreSecondMoment from
  D5.S3.Quantum.Recovery.QuadraticBayesRiskGeometricPetz
open private commutingResolution_weighted_cfc sum_image_pieces image_scoreMoment from
  D5.S3.Quantum.Recovery.PetzCommutingInputUniformRecovery
open private likelihoodOperator_pos sqrt_eq_real_cfc from
  D5.S3.Quantum.Recovery.PetzLikelihoodRectangularAmplitude

namespace PetzKMSGeometricRiskContraction

variable {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

private def onHermitian (Φ : MatrixMap a b ℂ) (hΦ : Φ.IsPositive) :
    HermitianMat a ℂ →ₗ[ℝ] HermitianMat b ℂ where
  toFun X := ⟨Φ X.mat, hΦ.IsHermitianPreserving X.H⟩
  map_add' X Y := by
    apply Subtype.ext
    exact map_add Φ X.mat Y.mat
  map_smul' r X := by
    apply Subtype.ext
    exact LinearMap.map_smul_of_tower Φ r X.mat

omit [DecidableEq a] in
private theorem inner_sandwich (W : Matrix a a ℂ) (hW : W.IsHermitian)
    (X Y : HermitianMat a ℂ) :
    ⟪X, HermitianMat.conjLinear ℝ W Y⟫_ℝ =
      ⟪HermitianMat.conjLinear ℝ W X, Y⟫_ℝ := by
  simp only [HermitianMat.inner_eq_re_trace, HermitianMat.conjLinear_apply,
    HermitianMat.conj_apply_mat, hW.eq]
  congr 1
  rw [← Matrix.mul_assoc X.mat (W * Y.mat) W, Matrix.trace_mul_cycle]
  simp only [Matrix.mul_assoc]

omit [DecidableEq a] in
private theorem sandwich_comp (W : Matrix a a ℂ) (X : HermitianMat a ℂ) :
    HermitianMat.conjLinear ℝ W (HermitianMat.conjLinear ℝ W X) =
      HermitianMat.conjLinear ℝ (W * W) X := HermitianMat.conj_conj X W W

private theorem opNorm_apply_le_of_subunital (T : MatrixMap a a ℂ) (hT : T.IsPositive)
    (hOne : T 1 ≤ 1) (X : HermitianMat a ℂ) : ‖T X.mat‖ ≤ ‖X.mat‖ := by
  let r := ‖X.mat‖
  have hu : T (algebraMap ℝ (Matrix a a ℂ) r) ≤ algebraMap ℝ (Matrix a a ℂ) r := by
    rw [Algebra.algebraMap_eq_smul_one, LinearMap.map_smul_of_tower]
    exact smul_le_smul_of_nonneg_left hOne (norm_nonneg _)
  have hp := (map_le T hT (X.H.isSelfAdjoint.le_algebraMap_norm_self X.mat)).trans hu
  have hn := map_le T hT (X.H.isSelfAdjoint.neg_algebraMap_norm_le_self X.mat)
  rw [map_neg] at hn
  have hlow := (neg_le_neg hu).trans hn
  refine ((hT.IsHermitianPreserving X.H).isSelfAdjoint.norm_le_max_of_le_of_le hlow hp).trans ?_
  simp only [norm_neg, max_self, Algebra.algebraMap_eq_smul_one, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (show 0 ≤ r from norm_nonneg _)]
  have hproj : IsStarProjection (1 : Matrix a a ℂ) := by simp
  exact mul_le_of_le_one_right (norm_nonneg _) (hproj.norm_le)

-- For D A and A D, A transfers each nonzero eigenvalue to a Hermitian direction.
private theorem gram_residual_cauchySchwarz
    (D A : HermitianMat a ℂ →ₗ[ℝ] HermitianMat a ℂ)
    (hG : (D ∘ₗ A).IsPositive)
    (hT : ∀ X, ‖(A (D X)).mat‖ ≤ ‖X.mat‖) (X Y : HermitianMat a ℂ) :
    let S := (1 : Module.End ℝ (HermitianMat a ℂ)) - D ∘ₗ A
    0 ≤ ⟪Y, S Y⟫_ℝ ∧
      ⟪X, S Y⟫_ℝ ^ 2 ≤ ⟪X, S X⟫_ℝ * ⟪Y, S Y⟫_ℝ := by
  classical
  let ι := Fin (Module.finrank ℝ (HermitianMat a ℂ))
  let e : OrthonormalBasis ι ℝ (HermitianMat a ℂ) := hG.isSymmetric.eigenvectorBasis rfl
  let μ : ι → ℝ := hG.isSymmetric.eigenvalues rfl
  let S : Module.End ℝ (HermitianMat a ℂ) := 1 - D ∘ₗ A
  have hμ (i : ι) : μ i ≤ 1 := by
    by_contra! h
    have he : D (A (e i)) = μ i • e i := hG.isSymmetric.apply_eigenvectorBasis rfl i
    have hne : (A (e i)).mat ≠ 0 := by
      intro hz
      have hz' : A (e i) = 0 := Subtype.ext hz
      rw [hz', map_zero, eq_comm, smul_eq_zero] at he
      exact he.elim (ne_of_gt (zero_lt_one.trans h)) (e.orthonormal.ne_zero i)
    have he' : A (D (A (e i))) = μ i • A (e i) := by rw [he, map_smul]
    have hn := hT (A (e i))
    rw [he', HermitianMat.mat_smul, norm_smul, Real.norm_eq_abs,
      abs_of_pos (zero_lt_one.trans h)] at hn
    exact (not_le_of_gt h) (le_of_mul_le_mul_right (by simpa only [one_mul] using hn)
      (norm_pos_iff.mpr hne))
  let v (Z : HermitianMat a ℂ) (i : ι) := Real.sqrt (1 - μ i) * e.repr Z i
  have hcoord (U V : HermitianMat a ℂ) :
      (∑ i : ι, v U i * v V i) = ⟪U, S V⟫_ℝ := by
    rw [← e.sum_inner_mul_inner U (S V)]
    apply Finset.sum_congr rfl
    intro i _
    have hrepr : e.repr (S V) i = (1 - μ i) * e.repr V i := by
      change e.repr (V - (D ∘ₗ A) V) i = _
      rw [map_sub, PiLp.sub_apply]
      change e.repr V i - e.repr ((D ∘ₗ A) V) i = _
      have hcoordG : e.repr ((D ∘ₗ A) V) i = μ i * e.repr V i :=
        hG.isSymmetric.eigenvectorBasis_apply_self_apply rfl V i
      rw [hcoordG, sub_mul, one_mul]
    rw [real_inner_comm (e i) U, ← e.repr_apply_apply, ← e.repr_apply_apply, hrepr]
    dsimp only [v]
    rw [mul_mul_mul_comm, Real.mul_self_sqrt (sub_nonneg.mpr (hμ i))]
    ring
  change 0 ≤ ⟪Y, S Y⟫_ℝ ∧ ⟪X, S Y⟫_ℝ ^ 2 ≤ ⟪X, S X⟫_ℝ * ⟪Y, S Y⟫_ℝ
  rw [← hcoord X Y, ← hcoord X X, ← hcoord Y Y]
  exact ⟨Finset.sum_nonneg fun i _ => mul_self_nonneg _, by
    simpa only [pow_two] using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (v X) (v Y)⟩

set_option maxHeartbeats 800000 in
-- Elaborating the Hermitian restrictions and their ambient matrix identities uses extra heartbeats.
/-- The full trace norm of the ordinary Petz residual on a Hermitian score is
bounded by its KMS quadratic deficit. The score may be signed. -/
private theorem weighted_residual_bound (Φ : MatrixMap a b ℂ) (hΦ : Φ.IsPositive)
    (hTP : Φ.IsTracePreserving) (σ Y : Matrix a a ℂ)
    (hσ : σ.PosSemidef) (htr : σ.trace = 1) (hY : Y.IsHermitian) :
    let W := CFC.sqrt σ
    let H := spectralInverseSqrt (Φ σ)
    let p := Φ (W * Y * W)
    traceNorm (W * Y * W - ordinaryPetz Φ σ p) ^ 2 ≤
      tracePair Y (W * Y * W) - tracePair p (H * p * H) := by
  classical
  let W := CFC.sqrt σ
  let H := spectralInverseSqrt (Φ σ)
  let U := CFC.sqrt W
  let V := CFC.sqrt H
  have hW : W.PosSemidef := (CFC.sqrt_nonneg σ).posSemidef
  have hH : H.PosSemidef := by
    change (cfc (fun x : ℝ => (Real.sqrt x)⁻¹) (Φ σ)).PosSemidef
    apply Matrix.nonneg_iff_posSemidef.mp
    exact (cfc_nonneg_iff _ _ ((Φ σ).finite_real_spectrum.continuousOn _)
      (hΦ hσ).isHermitian).2 fun x _ => inv_nonneg.mpr (Real.sqrt_nonneg x)
  have hU : U.IsHermitian := (CFC.sqrt_nonneg W).posSemidef.isHermitian
  have hV : V.IsHermitian := (CFC.sqrt_nonneg H).posSemidef.isHermitian
  have hUU : U * U = W := CFC.sqrt_mul_sqrt_self _ hW.nonneg
  have hVV : V * V = H := CFC.sqrt_mul_sqrt_self _ hH.nonneg
  have hWW : W * W = σ := CFC.sqrt_mul_sqrt_self _ hσ.nonneg
  let D := HermitianMat.conjLinear ℝ U
  let E := HermitianMat.conjLinear ℝ V
  let F := onHermitian Φ hΦ
  let F' := onHermitian Φ.dual hΦ.dual
  let A := F' ∘ₗ E ∘ₗ E ∘ₗ F ∘ₗ D
  let B := E ∘ₗ F ∘ₗ D
  have hD (X : HermitianMat a ℂ) :
      (D (D X)).mat = W * X.mat * W := by
    change (HermitianMat.conjLinear ℝ U (HermitianMat.conjLinear ℝ U X)).mat = _
    rw [sandwich_comp, hUU]
    simp only [HermitianMat.conjLinear_apply,
      HermitianMat.conj_apply_mat, hW.isHermitian.eq]
  have hE (X : HermitianMat b ℂ) :
      (E (E X)).mat = H * X.mat * H := by
    change (HermitianMat.conjLinear ℝ V (HermitianMat.conjLinear ℝ V X)).mat = _
    rw [sandwich_comp, hVV]
    simp only [HermitianMat.conjLinear_apply,
      HermitianMat.conj_apply_mat, hH.isHermitian.eq]
  have hF (X : HermitianMat a ℂ) (Z : HermitianMat b ℂ) :
      ⟪X, F' Z⟫_ℝ = ⟪F X, Z⟫_ℝ :=
    congrArg Complex.re (MatrixMap.Dual.trace_eq Φ X.mat Z.mat).symm
  have hGram (X Z : HermitianMat a ℂ) :
      ⟪X, D (A Z)⟫_ℝ = ⟪B X, B Z⟫_ℝ := by
    change ⟪X, D (F' (E (E (F (D Z)))))⟫_ℝ = _
    rw [inner_sandwich U hU, hF, inner_sandwich V hV]
    rfl
  have hG : (D ∘ₗ A).IsPositive := by
    refine (LinearMap.isPositive_iff _).2 ⟨fun X Z => ?_, fun X => ?_⟩
    · change ⟪D (A X), Z⟫_ℝ = ⟪X, D (A Z)⟫_ℝ
      rw [real_inner_comm Z (D (A X)), hGram, hGram, real_inner_comm]
    · change 0 ≤ ⟪D (A X), X⟫_ℝ
      rw [real_inner_comm X (D (A X)), hGram]
      exact real_inner_self_nonneg
  let T : MatrixMap a a ℂ :=
    Φ.dual ∘ₗ LinearMap.mulLeftRight ℂ (H, H) ∘ₗ Φ ∘ₗ LinearMap.mulLeftRight ℂ (W, W)
  have hTapply (Z : Matrix a a ℂ) : T Z = Φ.dual (H * Φ (W * Z * W) * H) := by
    rfl
  have hTpos : T.IsPositive := by
    intro Z hZ
    rw [hTapply]
    have hmid : (W * Z * W).PosSemidef := by
      simpa only [hW.isHermitian.eq] using hZ.mul_mul_conjTranspose_same W
    exact hΦ.dual (by
      simpa only [hH.isHermitian.eq] using (hΦ hmid).mul_mul_conjTranspose_same H)
  have hTOne : T 1 ≤ 1 := by
    obtain ⟨_, _, hp, hpp, _, _, _, hnorm⟩ := spectral_sqrt_normalization (Φ σ) (hΦ hσ)
    have hproj : IsStarProjection (spectralSupport (Φ σ)) := ⟨hpp, hp⟩
    calc
      T 1 = Φ.dual (spectralSupport (Φ σ)) := by rw [hTapply, Matrix.mul_one, hWW, hnorm]
      _ ≤ Φ.dual 1 := map_le _ hΦ.dual (sub_nonneg.mp hproj.one_sub_nonneg)
      _ = 1 := traceDual_unital Φ hTP
  have hAD (X : HermitianMat a ℂ) : (A (D X)).mat = T X.mat := by
    rw [hTapply]
    change Φ.dual ((E (E (F (D (D X))))).mat) = _
    rw [hE]
    change Φ.dual (H * Φ (D (D X)).mat * H) = _
    rw [hD]
  let S : Module.End ℝ (HermitianMat a ℂ) := 1 - D ∘ₗ A
  let y : HermitianMat a ℂ := ⟨Y, hY⟩
  let residual := W * Y * W - ordinaryPetz Φ σ (Φ (W * Y * W))
  have hres : (D (S (D y))).mat = residual := by
    change (D (D y - D (A (D y)))).mat = _
    rw [map_sub, HermitianMat.mat_sub, hD, hD, hAD, hTapply]
    rfl
  obtain ⟨K, hK, hKnorm, htest⟩ :=
    exists_hermitian_traceNorm_test residual (hres ▸ (D (S (D y))).H)
  let k : HermitianMat a ℂ := ⟨K, hK⟩
  have hdiag (X : HermitianMat a ℂ) :
      ⟪D X, S (D X)⟫_ℝ =
        tracePair X.mat (W * X.mat * W) -
          tracePair (Φ (W * X.mat * W)) (H * Φ (W * X.mat * W) * H) := by
    change ⟪D X, D X - D (A (D X))⟫_ℝ = _
    rw [inner_sub_right, ← inner_sandwich U hU X (D X), hGram]
    have hin : ⟪X, D (D X)⟫_ℝ = tracePair X.mat (W * X.mat * W) := by
      rw [HermitianMat.inner_eq_re_trace, hD]
      rfl
    have hout : ⟪B (D X), B (D X)⟫_ℝ =
        tracePair (Φ (W * X.mat * W)) (H * Φ (W * X.mat * W) * H) := by
      change ⟪E (F (D (D X))), E (F (D (D X)))⟫_ℝ = _
      rw [← inner_sandwich V hV (F (D (D X))) (E (F (D (D X)))),
        HermitianMat.inner_eq_re_trace, hE]
      change tracePair (Φ (D (D X)).mat) (H * Φ (D (D X)).mat * H) = _
      rw [hD]
    exact congrArg₂ (· - ·) hin hout
  have htest' : ⟪D k, S (D y)⟫_ℝ = traceNorm residual := by
    rw [← inner_sandwich U hU k (S (D y)), HermitianMat.inner_eq_re_trace, hres]
    exact htest
  have hk2 : K * K ≤ 1 := by
    calc
      K * K = star K * K := by rw [Matrix.star_eq_conjTranspose, hK.eq]
      _ ≤ algebraMap ℝ (Matrix a a ℂ) (‖K‖ ^ 2) :=
        CStarAlgebra.star_mul_le_algebraMap_norm_sq K
      _ ≤ 1 := by
        rw [← map_one (algebraMap ℝ (Matrix a a ℂ))]
        exact (algebraMap_mono (α := ℝ) (β := Matrix a a ℂ))
          (by
            nlinarith only [hKnorm, norm_nonneg K,
              mul_nonneg (norm_nonneg K) (sub_nonneg.mpr hKnorm)])
  have hkWeighted : ⟪D k, S (D k)⟫_ℝ ≤ 1 := by
    have hnonneg := hG.inner_nonneg_right (D k)
    change 0 ≤ ⟪D k, D (A (D k))⟫_ℝ at hnonneg
    change ⟪D k, D k - D (A (D k))⟫_ℝ ≤ 1
    rw [inner_sub_right, ← inner_sandwich U hU k (D k)]
    have hgeom := geometric_quadratic_le σ K W hW.isHermitian.eq hWW hK
    have hmass := (Complex.nonneg_iff.mp
      (hσ.trace_mul_nonneg (Matrix.le_iff.mp hk2))).1
    simp only [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re, Matrix.mul_one,
      htr, Complex.one_re] at hmass
    change ⟪k, D (D k)⟫_ℝ - ⟪D k, D (A (D k))⟫_ℝ ≤ 1
    have hin : ⟪k, D (D k)⟫_ℝ = (K * (W * K * W)).trace.re := by
      rw [HermitianMat.inner_eq_re_trace, hD]
      rfl
    rw [hin]
    unfold tracePair at hgeom
    rw [Matrix.mul_assoc K W (K * W), ← Matrix.mul_assoc W K W] at hgeom
    linarith only [hnonneg, hgeom, hmass]
  obtain ⟨hy, hCS⟩ := gram_residual_cauchySchwarz D A hG
    (fun X => by rw [hAD]; exact opNorm_apply_le_of_subunital T hTpos hTOne X) (D k) (D y)
  change 0 ≤ ⟪D y, S (D y)⟫_ℝ at hy
  change ⟪D k, S (D y)⟫_ℝ ^ 2 ≤ ⟪D k, S (D k)⟫_ℝ * ⟪D y, S (D y)⟫_ℝ at hCS
  rw [htest'] at hCS
  have hbound := hCS.trans (mul_le_of_le_one_left hy hkWeighted)
  rw [hdiag] at hbound
  exact hbound

/-- For commuting supported density states, the squared full trace-norm
error of ordinary Petz recovery is bounded by the geometric risk of the
actual likelihood pieces after the positive trace-preserving map. -/
theorem traceNorm_sub_ordinaryPetz_sq_le_geometricRisk_of_commute
    (ρ σ : DensityState a) (hComm : Commute (stateMatrix ρ) (stateMatrix σ))
    (hSupp : SupportContained ρ σ) (Φ : MatrixMap a b ℂ)
    (hΦ : Φ.IsPositive) (hTP : Φ.IsTracePreserving) :
    let L := commutingResolution ρ σ hComm hSupp
    traceNorm (stateMatrix ρ - ordinaryPetz Φ (stateMatrix σ) (Φ (stateMatrix ρ))) ^ 2 ≤
      geometricRisk (fun j => Φ (L.piece j)) L.likelihood := by
  classical
  let L := commutingResolution ρ σ hComm hSupp
  let Q := stateMatrix σ
  let W := CFC.sqrt Q
  let Y := likelihoodOperator ρ σ
  let H := spectralInverseSqrt (Φ Q)
  have hY := (likelihoodOperator_pos ρ σ).isHermitian
  have hρ : W * Y * W = stateMatrix ρ := by
    have h := commutingResolution_weighted_cfc ρ σ hComm hSupp (fun x => x)
    change (∑ j, L.likelihood j • L.piece j) = W * cfc (fun x : ℝ => x) Y * W at h
    rw [L.sum_weighted, cfc_id' ℝ Y hY.isSelfAdjoint] at h
    exact h.symm
  have hQH : Commute Q (spectralInverseSqrt Q) :=
    ((Commute.refl Q).cfc_real (fun x : ℝ => (Real.sqrt x)⁻¹)).symm
  have hQY : Commute Q Y :=
    (hQH.mul_right hComm.symm).mul_right hQH
  have hWY : Commute W Y := by
    change Commute (CFC.sqrt Q) Y
    rw [sqrt_eq_real_cfc (density_posSemidef σ)]
    exact hQY.cfc_real _
  have hsecond :
      scoreSecondMoment (fun j => Φ (L.piece j)) L.likelihood =
        tracePair Y (W * Y * W) := by
    have h := commutingResolution_weighted_cfc ρ σ hComm hSupp (fun x => x ^ 2)
    change (∑ j, L.likelihood j ^ 2 • L.piece j) = W * cfc (· ^ 2 : ℝ → ℝ) Y * W at h
    rw [cfc_pow_id Y 2 hY.isSelfAdjoint, pow_two] at h
    calc
      _ = (∑ j, L.likelihood j ^ 2 • L.piece j).trace.re := by
        have hTrace (X : Matrix a a ℂ) : (Φ X).trace = X.trace := hTP X
        simp only [scoreSecondMoment, hTrace, Matrix.trace_sum, Matrix.trace_smul,
          Complex.re_sum, Complex.real_smul, Complex.re_ofReal_mul]
      _ = tracePair Y (W * Y * W) := by
        rw [h]
        unfold tracePair
        apply congrArg (fun X : Matrix a a ℂ => X.trace.re)
        calc
          W * (Y * Y) * W = (W * Y) * Y * W := by rw [Matrix.mul_assoc W Y Y]
          _ = (Y * W) * Y * W := congrArg (fun X => X * Y * W) hWY.eq
          _ = Y * (W * Y * W) := by simp only [Matrix.mul_assoc]
  have hbound := weighted_residual_bound Φ hΦ hTP Q Y (density_posSemidef σ) σ.2.2 hY
  change traceNorm (W * Y * W - ordinaryPetz Φ Q (Φ (W * Y * W))) ^ 2 ≤
    tracePair Y (W * Y * W) - tracePair (Φ (W * Y * W)) (H * Φ (W * Y * W) * H) at hbound
  rw [← hsecond, hρ] at hbound
  change _ ≤ geometricRisk (fun j => Φ (L.piece j)) L.likelihood
  unfold geometricRisk
  rw [sum_image_pieces L Φ, image_scoreMoment L Φ]
  exact hbound


open Filter MeasureTheory Set
open scoped Topology
open PetzActualLikelihoodEntropy (actualEntropyLoss actualEntropyLoss_dummy geometricRisk_dummy)
open PetzLikelihoodHessianIntegration (bkmDeficit)
open LikelihoodRationalTailSeparation (mixtureScore)
open QuadraticBayesRiskGeometricPetz (geometricRisk_eq_half_pairwise pgmEffects pgmEffects_isPOVM
  geometricRisk_le_bkm_deficit)

open private integral_hessian from D5.S3.Quantum.Recovery.PetzLikelihoodHessianIntegration
open private lossPath velocity hessian lossPath_one continuous_lossPath lossPath_zero velocity_zero
  lossPath_hasDerivAt velocity_hasDerivAt continuousOn_hessian hessian_eq_tilted_bkmDeficit
  dummyEnsemble dummyLikelihood dummyEnsemble_posSemidef dummyEnsemble_sum_posDef
  weight weight_pos from
  D5.S3.Quantum.Recovery.PetzActualLikelihoodEntropy
open private actualEntropyLoss_image from D5.S3.Quantum.Recovery.PetzCommutingInputUniformRecovery

private theorem weight_mono {x y t : ℝ} (ht : 0 ≤ t) (hxy : x ≤ y) :
    weight x t ≤ weight y t :=
  add_le_add_right (mul_le_mul_of_nonneg_left hxy ht) _

-- Evaluate the twice-integrated scalar comparison by its rational primitive.
private theorem weighted_hessian_endpoint (m M c : ℝ) (hM : 1 ≤ M)
    (δ v h : ℝ → ℝ) (hδ₁ : ContinuousAt δ 1) (hδ₀ : δ 0 = 0) (hv₀ : v 0 = 0)
    (hδ : ∀ t ∈ Ico (0 : ℝ) 1, HasDerivWithinAt δ (v t) (Ico 0 1) t)
    (hv : ∀ t ∈ Ico (0 : ℝ) 1, HasDerivWithinAt v (h t) (Ico 0 1) t)
    (hh : ∀ u ∈ Ico (0 : ℝ) 1, ContinuousOn h (Icc 0 u))
    (hLower : ∀ t ∈ Ico (0 : ℝ) 1, c * (weight m t / weight M t ^ 4) ≤ h t) :
    c * ((2 * M + m) / (6 * M ^ 2)) ≤ δ 1 := by
  let k := M - 1
  let b := 2 * M + m - 3
  let f (t : ℝ) := 1 + k * t
  let p (t : ℝ) := (1 / 2 : ℝ) * t ^ 2 + (b / 6) * t ^ 3
  let q (t : ℝ) := t + (b / 2) * t ^ 2 + (k * b / 6) * t ^ 3
  let d (t : ℝ) := c * (p t / f t ^ 2)
  let w (t : ℝ) := c * (q t / f t ^ 3)
  let g (t : ℝ) := c * (weight m t / weight M t ^ 4)
  have hf (t : ℝ) : f t = weight M t := by dsimp [f, k, weight]; ring
  have hne (t : ℝ) (ht : 0 ≤ t) : f t ≠ 0 :=
    (add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg (sub_nonneg.mpr hM) ht)).ne'
  have hdf (t : ℝ) : HasDerivAt f k t := by
    simpa only [mul_one, id_eq] using ((hasDerivAt_id t).const_mul k).const_add 1
  have hd₁ (t : ℝ) (ht : 0 ≤ t) : HasDerivAt d (w t) t := by
    have hp : HasDerivAt p (t + (b / 2) * t ^ 2) t := by
      have hp' : HasDerivAt p _ t :=
        (((hasDerivAt_id t).pow 2).const_mul (1 / 2 : ℝ)).add
          (((hasDerivAt_id t).pow 3).const_mul (b / 6))
      convert hp' using 1
      simp only [id_eq]
      norm_num
      <;> ring
    have hd : HasDerivAt d _ t :=
      (hp.div ((hdf t).pow 2) (pow_ne_zero _ (hne t ht))).const_mul c
    convert hd using 1
    change c * (q t / f t ^ 3) =
      c * (((t + b / 2 * t ^ 2) * f t ^ 2 - p t * ((2 : ℕ) * f t ^ (2 - 1 : ℕ) * k)) /
        (f t ^ 2) ^ 2)
    simp only [← mul_div_assoc]
    apply (div_eq_div_iff (pow_ne_zero 3 (hne t ht))
      (pow_ne_zero 2 (pow_ne_zero 2 (hne t ht)))).2
    dsimp only [q, p, f]
    norm_num
    <;> ring
  have hd₂ (t : ℝ) (ht : 0 ≤ t) : HasDerivAt w (g t) t := by
    have hq : HasDerivAt q (1 + b * t + (k * b / 2) * t ^ 2) t := by
      have hq' : HasDerivAt q _ t := ((hasDerivAt_id t).add
        (((hasDerivAt_id t).pow 2).const_mul (b / 2))).add
        (((hasDerivAt_id t).pow 3).const_mul (k * b / 6))
      convert hq' using 1
      simp only [id_eq]
      norm_num
      <;> ring
    have hd : HasDerivAt w _ t :=
      (hq.div ((hdf t).pow 3) (pow_ne_zero _ (hne t ht))).const_mul c
    convert hd using 1
    change c * (weight m t / weight M t ^ 4) =
      c * (((1 + b * t + k * b / 2 * t ^ 2) * f t ^ 3 -
        q t * ((3 : ℕ) * f t ^ (3 - 1 : ℕ) * k)) / (f t ^ 3) ^ 2)
    rw [← hf]
    simp only [← mul_div_assoc]
    apply (div_eq_div_iff (pow_ne_zero 4 (hne t ht))
      (pow_ne_zero 2 (pow_ne_zero 3 (hne t ht)))).2
    dsimp only [q, f, weight, b, k]
    norm_num
    <;> ring
  have hd0 : d 0 = 0 := by simp [d, p]
  have hw0 : w 0 = 0 := by simp [w, q]
  have hgc (u : ℝ) : ContinuousOn g (Icc 0 u) := by
    refine continuousOn_const.mul ((by unfold weight; fun_prop : ContinuousOn
      (weight m) (Icc 0 u)).div (by unfold weight; fun_prop) fun t ht => ?_)
    rw [← hf]
    exact pow_ne_zero _ (hne t ht.1)
  have hle (u : ℝ) (hu : u ∈ Ico (0 : ℝ) 1) : d u ≤ δ u := by
    rw [← integral_hessian d w g hu hd0 hw0
      (fun t ht => (hd₁ t ht.1).hasDerivWithinAt)
      (fun t ht => (hd₂ t ht.1).hasDerivWithinAt) (hgc u),
      ← integral_hessian δ v h hu hδ₀ hv₀ hδ hv (hh u hu)]
    have hLeft : ContinuousOn (fun t => (u - t) * g t) (Icc 0 u) :=
      (continuousOn_const.sub continuousOn_id).mul (hgc u)
    have hRight : ContinuousOn (fun t => (u - t) * h t) (Icc 0 u) :=
      (continuousOn_const.sub continuousOn_id).mul (hh u hu)
    rw [← uIcc_of_le hu.1] at hLeft hRight
    exact intervalIntegral.integral_mono_on hu.1 hLeft.intervalIntegrable hRight.intervalIntegrable
      fun t ht => mul_le_mul_of_nonneg_left (hLower t ⟨ht.1, ht.2.trans_lt hu.2⟩)
        (sub_nonneg.mpr ht.2)
  have hdcont : ContinuousAt d 1 := (hd₁ 1 zero_le_one).continuousAt
  have hfilter : (𝓝[Ico (0 : ℝ) 1] (1 : ℝ)).NeBot := right_nhdsWithin_Ico_neBot zero_lt_one
  have hs : ∀ᶠ u : ℝ in 𝓝[Ico (0 : ℝ) 1] (1 : ℝ), u ∈ Ico 0 1 := self_mem_nhdsWithin
  have hlim : d 1 ≤ δ 1 := le_of_tendsto_of_tendsto
    hdcont.continuousWithinAt hδ₁.continuousWithinAt (hs.mono hle)
  have hdend : d 1 = c * ((2 * M + m) / (6 * M ^ 2)) := by
    have hf1 : f 1 = M := by rw [hf]; simp [weight]
    dsimp only [d]
    rw [hf1]
    simp only [p, one_pow, mul_one, b]
    ring
  rwa [hdend] at hlim

section LikelihoodIntegral

variable {ι : Type*} [Fintype ι]

private theorem tilted_hessian_lower (A : ι → Matrix b b ℂ) (lam : ι → ℝ)
    (hA : ∀ i, (A i).PosSemidef) (hQ : (∑ i, A i).PosDef)
    (hlam : ∀ i, 0 ≤ lam i) {m M : ℝ} (hm : 0 ≤ m) (hM : 1 ≤ M)
    (hb : ∀ i, A i ≠ 0 → m ≤ lam i ∧ lam i ≤ M)
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) 1) :
    geometricRisk A lam * (weight m t / weight M t ^ 4) ≤ hessian A lam t := by
  classical
  let d (i : ι) := mixtureScore (lam i) t
  let C (i : ι) := weight (lam i) t • A i
  have hwt (i : ι) : 0 < weight (lam i) t := weight_pos (hlam i) ht
  have hmw : 0 < weight m t := weight_pos hm ht
  have hMw : 0 < weight M t := weight_pos (zero_le_one.trans hM) ht
  have hC (i : ι) : (C i).PosSemidef := (hA i).smul (hwt i).le
  have hCsum : (∑ i, C i).PosDef := by
    have hExtra : (∑ i, (t * lam i) • A i).PosSemidef :=
      Matrix.posSemidef_sum Finset.univ fun i _ => (hA i).smul (mul_nonneg ht.1 (hlam i))
    simpa only [C, weight, add_smul, Finset.sum_add_distrib, Finset.smul_sum] using
      (hQ.smul (sub_pos.mpr ht.2)).add_posSemidef hExtra
  have hdom (i : ι) : weight m t • A i ≤ C i := by
    by_cases hz : A i = 0
    · simp [C, hz]
    exact smul_le_smul_of_nonneg_right (weight_mono ht.1 (hb i hz).1) (hA i).nonneg
  have hdif (i j : ι) :
      d i - d j = (lam i - lam j) / (weight (lam i) t * weight (lam j) t) := by
    dsimp only [d, mixtureScore]
    change (lam i - 1) / weight (lam i) t - (lam j - 1) / weight (lam j) t = _
    field_simp [(hwt i).ne', (hwt j).ne']
    unfold weight
    ring
  obtain ⟨hPGM, _⟩ := pgmEffects_isPOVM A hA
  have hpairs (i j : ι) :
      (lam i - lam j) ^ 2 * tracePair (A i) (pgmEffects A (some j)) / weight M t ^ 4 ≤
        (d i - d j) ^ 2 * tracePair (A i) (pgmEffects A (some j)) := by
    by_cases hi : A i = 0
    · simp [hi, tracePair]
    by_cases hj : A j = 0
    · simp [hj, tracePair, pgmEffects]
    have hpair := (Complex.nonneg_iff.mp ((hA i).trace_mul_nonneg (hPGM (some j)))).1
    have hden : (weight (lam i) t * weight (lam j) t) ^ 2 ≤ weight M t ^ 4 := by
      rw [show (4 : ℕ) = 2 * 2 by decide, pow_mul]
      apply pow_le_pow_left₀ (mul_nonneg (hwt i).le (hwt j).le)
      rw [pow_two]
      exact mul_le_mul (weight_mono ht.1 (hb i hi).2) (weight_mono ht.1 (hb j hj).2)
        (hwt j).le hMw.le
    rw [hdif, div_pow, div_mul_eq_mul_div₀]
    exact div_le_div_of_nonneg_left (mul_nonneg (sq_nonneg _) hpair)
      (pow_pos (mul_pos (hwt i) (hwt j)) _) hden
  have hscore : geometricRisk A lam / weight M t ^ 4 ≤ geometricRisk A d := by
    rw [geometricRisk_eq_half_pairwise A lam hA, geometricRisk_eq_half_pairwise A d hA,
      mul_div_assoc]
    simp only [Finset.sum_div]
    exact mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hpairs i j) (by norm_num)
  rw [hessian_eq_tilted_bkmDeficit A lam hlam ht]
  change _ ≤ bkmDeficit C d
  calc
    _ = weight m t * (geometricRisk A lam / weight M t ^ 4) := by ring
    _ ≤ weight m t * geometricRisk A d := mul_le_mul_of_nonneg_left hscore hmw.le
    _ ≤ geometricRisk C d :=
      PetzGeometricRiskSuperadditivity.smul_geometricRisk_le A C d hA _ hmw.le hdom
    _ ≤ _ := geometricRisk_le_bkm_deficit C d hC hCsum

private theorem weighted_geometricRisk_le_actualEntropyLoss
    (A : ι → Matrix b b ℂ) (lam : ι → ℝ) (hA : ∀ i, (A i).PosSemidef)
    (hlam : ∀ i, 0 ≤ lam i) {m M : ℝ} (hm : 0 ≤ m) (hm1 : m ≤ 1) (hM : 1 ≤ M)
    (hb : ∀ i, A i ≠ 0 → m ≤ lam i ∧ lam i ≤ M) :
    geometricRisk A lam * ((2 * M + m) / (6 * M ^ 2)) ≤ actualEntropyLoss A lam := by
  have hFaithful (A : Option ι → Matrix b b ℂ) (lam : Option ι → ℝ)
      (hA : ∀ i, (A i).PosSemidef) (hQ : (∑ i, A i).PosDef)
      (hlam : ∀ i, 0 ≤ lam i) (hb : ∀ i, A i ≠ 0 → m ≤ lam i ∧ lam i ≤ M) :
      geometricRisk A lam * ((2 * M + m) / (6 * M ^ 2)) ≤ actualEntropyLoss A lam := by
    rw [← lossPath_one]
    exact weighted_hessian_endpoint m M (geometricRisk A lam) hM
      (lossPath A lam) (velocity A lam) (hessian A lam)
      (continuous_lossPath A lam hA).continuousAt (lossPath_zero A lam) (velocity_zero A lam)
      (fun _ ht => (lossPath_hasDerivAt A lam hA hQ hlam ht).hasDerivWithinAt)
      (fun _ ht => (velocity_hasDerivAt A lam hA hQ hlam ht).hasDerivWithinAt)
      (fun _ hu => continuousOn_hessian A lam hA hQ hlam hu)
      (fun _ ht => tilted_hessian_lower A lam hA hQ hlam hm hM hb ht)
  have hlam' (i : Option ι) : 0 ≤ dummyLikelihood lam i := by
    cases i with
    | none => exact zero_le_one
    | some i => exact hlam i
  have hb' (i : Option ι) (hi : dummyEnsemble A i ≠ 0) :
      m ≤ dummyLikelihood lam i ∧ dummyLikelihood lam i ≤ M := by
    cases i with
    | none => exact ⟨hm1, hM⟩
    | some i => exact hb i hi
  have h := hFaithful (dummyEnsemble A) (dummyLikelihood lam) (dummyEnsemble_posSemidef A hA)
    (dummyEnsemble_sum_posDef A hA) hlam' hb'
  rw [actualEntropyLoss_dummy A lam hA hlam] at h
  have hScores : dummyLikelihood lam = fun i => i.elim 1 lam := by
    funext i
    cases i <;> rfl
  rwa [hScores, geometricRisk_dummy A lam 1 hA] at h

end LikelihoodIntegral

open D5.S3.Quantum.Divergence.SupportAwareRelativeEntropy (finiteTraceLogRelativeEntropy)
open PetzPositiveTracePostselection (mapDensityState)

/-- The weighted likelihood integral bounds ordinary Petz recovery for
commuting states. The likelihood bounds apply to pieces of nonzero mass. -/
theorem traceNorm_sub_ordinaryPetz_sq_le_bounded_umegakiLoss_of_commute
    (ρ σ : DensityState a) (hComm : Commute (stateMatrix ρ) (stateMatrix σ))
    (hSupp : SupportContained ρ σ) (Φ : MatrixMap a b ℂ)
    (hΦ : Φ.IsPositive) (hTP : Φ.IsTracePreserving)
    (m M : ℝ) (hm : 0 ≤ m)
    (hb : let L := commutingResolution ρ σ hComm hSupp
      ∀ j, L.piece j ≠ 0 → m ≤ L.likelihood j ∧ L.likelihood j ≤ M) :
    traceNorm (stateMatrix ρ - ordinaryPetz Φ (stateMatrix σ) (Φ (stateMatrix ρ))) ^ 2 ≤
      (6 * M ^ 2 / (2 * M + m)) *
        (finiteTraceLogRelativeEntropy ρ σ -
          finiteTraceLogRelativeEntropy
            (mapDensityState Φ hΦ hTP ρ) (mapDensityState Φ hΦ hTP σ)) := by
  classical
  let L := commutingResolution ρ σ hComm hSupp
  let A j := Φ (L.piece j)
  let lam := L.likelihood
  have hA (j : _) : (A j).PosSemidef := hΦ (L.piece_pos j)
  have hb' (j : _) (hj : A j ≠ 0) : m ≤ lam j ∧ lam j ≤ M :=
    hb j (fun hz => hj (by
      change L.piece j = 0 at hz
      change Φ (L.piece j) = 0
      rw [hz, map_zero]))
  have hmass : ∑ j, (A j).trace.re = 1 := by
    rw [← Complex.re_sum, ← Matrix.trace_sum, show (∑ j, A j) = _ from sum_image_pieces L Φ]
    exact congrArg Complex.re ((hTP (stateMatrix σ)).trans σ.2.2)
  have hscore : ∑ j, (A j).trace.re * lam j = 1 := by
    rw [PetzActualLikelihoodEntropy.likelihoodMass_eq_trace,
      show QuadraticBayesRiskGeometricPetz.scoreMoment A lam = _ from image_scoreMoment L Φ]
    exact congrArg Complex.re ((hTP (stateMatrix ρ)).trans ρ.2.2)
  have hterm (j : _) :
      (A j).trace.re * m ≤ (A j).trace.re * lam j ∧
        (A j).trace.re * lam j ≤ (A j).trace.re * M := by
    by_cases hz : A j = 0
    · simp [hz]
    have hn := (Complex.nonneg_iff.mp (hA j).trace_nonneg).1
    exact ⟨mul_le_mul_of_nonneg_left (hb' j hz).1 hn, mul_le_mul_of_nonneg_left (hb' j hz).2 hn⟩
  have hm1 : (∑ j, (A j).trace.re * m) ≤ ∑ j, (A j).trace.re * lam j :=
    Finset.sum_le_sum (fun j _ => (hterm j).1)
  have hM : (∑ j, (A j).trace.re * lam j) ≤ ∑ j, (A j).trace.re * M :=
    Finset.sum_le_sum (fun j _ => (hterm j).2)
  rw [← Finset.sum_mul, hmass, one_mul, hscore] at hm1
  rw [← Finset.sum_mul, hmass, one_mul, hscore] at hM
  have hloss :=
    weighted_geometricRisk_le_actualEntropyLoss A lam hA L.likelihood_nonneg hm hm1 hM hb'
  have hloss' := (actualEntropyLoss_image ρ σ hComm hSupp Φ hΦ hTP)
  change actualEntropyLoss A lam = _ at hloss'
  rw [hloss'] at hloss
  have hden : 0 < 2 * M + m := by linarith
  have hnum : 0 < 6 * M ^ 2 := mul_pos (by norm_num) (sq_pos_of_pos (zero_lt_one.trans_le hM))
  refine (traceNorm_sub_ordinaryPetz_sq_le_geometricRisk_of_commute
    ρ σ hComm hSupp Φ hΦ hTP).trans ?_
  calc
    geometricRisk A lam = (6 * M ^ 2 / (2 * M + m)) *
        (geometricRisk A lam * ((2 * M + m) / (6 * M ^ 2))) := by
      field_simp [hden.ne', hnum.ne']
    _ ≤ _ := mul_le_mul_of_nonneg_left hloss (div_nonneg hnum.le hden.le)


end PetzKMSGeometricRiskContraction
