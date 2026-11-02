/- GID: D5/S3/Quantum/Foundation/ApproximateOrientedAnchorRepair
   generality: G
   mirror-B: D5/B/S3/Quantum/Foundation/ApproximateOrientedAnchorRepair
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Uniform Hilbert polar repair from finite oriented approximate comparisons. -/

module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
public import Mathlib.LinearAlgebra.Matrix.Gershgorin
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic

/-! Finite oriented comparisons and uniform repair on the original complete Hilbert output. -/

public section
noncomputable section
open scoped InnerProductSpace ComplexOrder BigOperators MatrixOrder Matrix.Norms.L2Operator Ring
open Complex ContinuousLinearMap

namespace D5.S3.Quantum.Foundation.ApproximateOrientedAnchorRepair

variable {H W : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [FiniteDimensional ℂ H] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  [FiniteDimensional ℂ W]

local instance : CompleteSpace H := FiniteDimensional.complete ℂ H
local instance : CompleteSpace W := FiniteDimensional.complete ℂ W

/-- The actual basis extension, without any orthogonality premise on its images. -/
def basisExtension {d : ℕ} (a : OrthonormalBasis (Fin d) ℂ H) (F : H → W) : H →L[ℂ] W :=
  (a.toBasis.constr ℂ (fun j => F (a j))).toContinuousLinearMap

def eta (d : ℕ) (δ : ℝ) : ℝ := Real.sqrt ((d : ℝ) / 2) * δ

def kappa (d : ℕ) (δ : ℝ) : ℝ := ((d : ℝ) - 1) / Real.sqrt 2 * δ

private lemma basisExtension_apply {d : ℕ} (a : OrthonormalBasis (Fin d) ℂ H)
    (F : H → W) (j : Fin d) : basisExtension a F (a j) = F (a j) := by
  simp [basisExtension]

private lemma comparison_re (x a : H) (y b : W)
    (hx : ‖x‖ = 1) (ha : ‖a‖ = 1) (hy : ‖y‖ = 1) (hb : ‖b‖ = 1)
    {δ : ℝ} (h : ‖y - b‖ ^ 2 ≤ ‖x - a‖ ^ 2 + δ) :
    (⟪a, x⟫_ℂ).re - δ / 2 ≤ (⟪b, y⟫_ℂ).re := by
  rw [norm_sub_sq (𝕜 := ℂ), norm_sub_sq (𝕜 := ℂ), hx, ha, hy, hb, inner_re_symm y b,
    inner_re_symm x a] at h
  change 1 ^ 2 - 2 * (⟪b, y⟫_ℂ).re + 1 ^ 2 ≤
    1 ^ 2 - 2 * (⟪a, x⟫_ℂ).re + 1 ^ 2 + δ at h
  linarith

private lemma four_anchor_coordinates {d : ℕ}
    (a : OrthonormalBasis (Fin d) ℂ H) (F : H → W) {δ : ℝ}
    (hN : ∀ x, ‖x‖ = 1 → ‖F x‖ = 1)
    (hphase : ∀ j (k : Fin 4), F ((I ^ (k : ℕ)) • a j) = (I ^ (k : ℕ)) • F (a j))
    (hcomp : ∀ x, ‖x‖ = 1 → ∀ j (k : Fin 4),
      ‖F x - F ((I ^ (k : ℕ)) • a j)‖ ^ 2 ≤
        ‖x - (I ^ (k : ℕ)) • a j‖ ^ 2 + δ)
    (x : H) (hx : ‖x‖ = 1) (j : Fin d) :
    |(⟪F (a j), F x⟫_ℂ - ⟪a j, x⟫_ℂ).re| ≤ δ / 2 ∧
    |(⟪F (a j), F x⟫_ℂ - ⟪a j, x⟫_ℂ).im| ≤ δ / 2 := by
  have hn := hN (a j) (a.norm_eq_one j)
  have h (k : Fin 4) := comparison_re x ((I ^ (k : ℕ)) • a j) (F x)
    ((I ^ (k : ℕ)) • F (a j)) hx
    (by simp [norm_smul, a.norm_eq_one]) (hN x hx)
    (by simp [norm_smul, hn]) (by simpa only [hphase] using hcomp x hx j k)
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  norm_num [inner_smul_left, I_sq, pow_succ, Complex.mul_re, Complex.mul_im,
    Complex.conj_ofReal, Complex.sub_re, Complex.sub_im] at h0 h1 h2 h3 ⊢
  constructor <;> rw [abs_le] <;> constructor <;> linarith

private lemma complex_norm_bound {z : ℂ} {δ : ℝ} (hδ : 0 ≤ δ)
    (hr : |z.re| ≤ δ / 2) (hi : |z.im| ≤ δ / 2) : ‖z‖ ≤ δ / Real.sqrt 2 := by
  have hr2 := sq_le_sq' (abs_le.mp hr).1 (abs_le.mp hr).2
  have hi2 := sq_le_sq' (abs_le.mp hi).1 (abs_le.mp hi).2
  have hs : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hpos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  apply (sq_le_sq₀ (norm_nonneg _) (div_nonneg hδ hpos.le)).mp
  have hn : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [Complex.norm_def, Real.sq_sqrt (Complex.normSq_nonneg z)]
    simp only [Complex.normSq_apply, pow_two]
  rw [hn, div_pow, hs]
  nlinarith

private lemma coordinate_error {d : ℕ}
    (a : OrthonormalBasis (Fin d) ℂ H) (F : H → W) {δ : ℝ} (hδ : 0 ≤ δ)
    (hN : ∀ x, ‖x‖ = 1 → ‖F x‖ = 1)
    (hphase : ∀ j (k : Fin 4), F ((I ^ (k : ℕ)) • a j) = (I ^ (k : ℕ)) • F (a j))
    (hcomp : ∀ x, ‖x‖ = 1 → ∀ j (k : Fin 4),
      ‖F x - F ((I ^ (k : ℕ)) • a j)‖ ^ 2 ≤
        ‖x - (I ^ (k : ℕ)) • a j‖ ^ 2 + δ)
    (x : H) (hx : ‖x‖ = 1) :
    ‖(basisExtension a F).adjoint (F x) - x‖ ≤ eta d δ := by
  have he (j : Fin d) :
      ⟪a j, (basisExtension a F).adjoint (F x) - x⟫_ℂ =
        ⟪F (a j), F x⟫_ℂ - ⟪a j, x⟫_ℂ := by
    rw [inner_sub_right, adjoint_inner_right, basisExtension_apply]
  have hp (j : Fin d) : ‖⟪a j, (basisExtension a F).adjoint (F x) - x⟫_ℂ‖ ^ 2 ≤ δ ^ 2 / 2 := by
    rw [he]
    have hc := four_anchor_coordinates a F hN hphase hcomp x hx j
    have hr := sq_le_sq' (abs_le.mp hc.1).1 (abs_le.mp hc.1).2
    have hi := sq_le_sq' (abs_le.mp hc.2).1 (abs_le.mp hc.2).2
    rw [Complex.norm_def, Real.sq_sqrt (Complex.normSq_nonneg _)]
    simp only [Complex.normSq_apply]
    nlinarith
  unfold eta
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) hδ)).mp
  rw [← a.sum_sq_norm_inner_right, mul_pow,
    Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (d : ℝ) / 2)]
  calc
    _ ≤ ∑ _j : Fin d, δ ^ 2 / 2 := Finset.sum_le_sum (fun j _ => hp j)
    _ = _ := by simp; ring

private def operatorMatrix {d : ℕ} (a : OrthonormalBasis (Fin d) ℂ H) :
    (H →L[ℂ] H) ≃⋆ₐ[ℂ] Matrix (Fin d) (Fin d) ℂ :=
  (show (H →ₗ[ℂ] H) ≃⋆ₐ[ℂ] (H →L[ℂ] H) from
    { LinearMap.toContinuousLinearMap with
      map_mul' := fun _ _ => rfl
      map_star' := LinearMap.adjoint_toContinuousLinearMap }).symm.trans
        (LinearMap.toMatrixOrthonormal a)

private lemma operatorMatrix_apply {d : ℕ} (a : OrthonormalBasis (Fin d) ℂ H)
    (T : H →L[ℂ] H) (i j : Fin d) : operatorMatrix a T i j = ⟪a i, T (a j)⟫_ℂ :=
  LinearMap.toMatrixOrthonormal_apply_apply a T.toLinearMap i j

private lemma gram_spectrum {d : ℕ} (hd : 1 ≤ d)
    (a : OrthonormalBasis (Fin d) ℂ H) (F : H → W) {δ : ℝ} (hδ : 0 ≤ δ)
    (hN : ∀ x, ‖x‖ = 1 → ‖F x‖ = 1)
    (hcoord : ∀ x, ‖x‖ = 1 → ∀ j,
      |(⟪F (a j), F x⟫_ℂ - ⟪a j, x⟫_ℂ).re| ≤ δ / 2 ∧
      |(⟪F (a j), F x⟫_ℂ - ⟪a j, x⟫_ℂ).im| ≤ δ / 2)
    (t : ℝ) (ht : t ∈ spectrum ℝ ((basisExtension a F).adjoint.comp (basisExtension a F))) :
    |t - 1| ≤ kappa d δ := by
  classical
  let B := basisExtension a F
  let G := B.adjoint.comp B
  let M := operatorMatrix a G
  have hm (i j : Fin d) : M i j = ⟪F (a i), F (a j)⟫_ℂ := by
    change operatorMatrix a G i j = _
    rw [operatorMatrix_apply]
    change ⟪a i, B.adjoint (B (a j))⟫_ℂ = _
    rw [adjoint_inner_right]
    simp only [B, basisExtension_apply]
  have hdiag (j : Fin d) : M j j = 1 := by
    rw [hm, inner_self_eq_norm_sq_to_K, hN _ (a.norm_eq_one j)]
    norm_num
  have hoff (i j : Fin d) (hij : i ≠ j) : ‖M i j‖ ≤ δ / Real.sqrt 2 := by
    have hc := hcoord (a j) (a.norm_eq_one j) i
    have hz : ⟪a i, a j⟫_ℂ = 0 := a.orthonormal.inner_eq_zero hij
    rw [hz, sub_zero] at hc
    rw [hm]
    exact complex_norm_bound hδ hc.1 hc.2
  have htC : (t : ℂ) ∈ spectrum ℂ G := (spectrum.algebraMap_mem_iff ℂ).mpr ht
  have htM : (t : ℂ) ∈ spectrum ℂ M := by
    rw [show M = operatorMatrix a G from rfl, AlgEquiv.spectrum_eq]
    exact htC
  have hev : Module.End.HasEigenvalue (Matrix.toLin' M) (t : ℂ) := by
    apply Module.End.HasEigenvalue.of_mem_spectrum
    rwa [Matrix.spectrum_toLin']
  obtain ⟨i, hi⟩ := eigenvalue_mem_ball hev
  have hball : |t - 1| ≤ ∑ j ∈ Finset.univ.erase i, ‖M i j‖ := by
    simpa only [dist_eq_norm, hdiag, ← Complex.ofReal_one, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs] using
      (Metric.mem_closedBall.mp hi)
  refine hball.trans ?_
  calc
    _ ≤ ∑ _j ∈ Finset.univ.erase i, δ / Real.sqrt 2 :=
      Finset.sum_le_sum fun j hj => hoff i j (Finset.ne_of_mem_erase hj).symm
    _ = kappa d δ := by
      have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
      simp only [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i),
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [Nat.cast_sub hd]
      unfold kappa
      ring

private lemma scalar_root_bound {κ t : ℝ} (hκ : 0 ≤ κ) (hκ1 : κ < 1)
    (ht : |t - 1| ≤ κ) : |Real.sqrt t - 1| ≤ 1 - Real.sqrt (1 - κ) := by
  have hlo : 0 ≤ 1 - κ := by linarith
  have hslo := Real.sqrt_nonneg (1 - κ)
  have hsone : Real.sqrt (1 - κ) ≤ 1 := Real.sqrt_le_one.mpr (by linarith)
  have hs2 := Real.sq_sqrt hlo
  have ht0 : 0 ≤ t := by have := (abs_le.mp ht).1; linarith
  have htl : Real.sqrt (1 - κ) ≤ Real.sqrt t :=
    Real.sqrt_le_sqrt (by have := (abs_le.mp ht).1; linarith)
  have hs := Real.sqrt_one_add_le (x := -κ) (by linarith : -1 ≤ -κ)
  have hhalf : Real.sqrt (1 - κ) ≤ 1 - κ / 2 := by
    rw [show 1 + -κ = 1 - κ by ring] at hs
    linarith
  have htu : Real.sqrt t ≤ 2 - Real.sqrt (1 - κ) := by
    apply (Real.sqrt_le_iff).mpr
    refine ⟨by linarith, ?_⟩
    have := (abs_le.mp ht).2
    nlinarith
  rw [abs_le]
  constructor <;> linarith

/-- Finite four-direction comparisons repair the actual nonlinear map, uniformly on the unit
sphere, by the polar isometry into the same complete output. -/
theorem finite_oriented_anchor_polar_repair {d : ℕ} (hd : 1 ≤ d)
    (a : OrthonormalBasis (Fin d) ℂ H) (F : H → W) (δ : ℝ) (hδ : 0 ≤ δ)
    (hN : ∀ x, ‖x‖ = 1 → ‖F x‖ = 1)
    (hphase : ∀ j (k : Fin 4), F ((I ^ (k : ℕ)) • a j) = (I ^ (k : ℕ)) • F (a j))
    (hcomp : ∀ x, ‖x‖ = 1 → ∀ j (k : Fin 4),
      ‖F x - F ((I ^ (k : ℕ)) • a j)‖ ^ 2 ≤
        ‖x - (I ^ (k : ℕ)) • a j‖ ^ 2 + δ)
    (hsmall : kappa d δ < 1) :
    let B := basisExtension a F
    let G := B.adjoint.comp B
    IsStrictlyPositive G ∧
      ∃ U : H →ₗᵢ[ℂ] W,
        U.toContinuousLinearMap = B.comp (CFC.sqrt G)⁻¹ʳ ∧
        ‖G - 1‖ ≤ kappa d δ ∧
        ‖B - U.toContinuousLinearMap‖ ≤ 1 - Real.sqrt (1 - kappa d δ) ∧
        ∀ x, ‖x‖ = 1 →
          ‖F x - U x‖ ≤ min 2
            (Real.sqrt (kappa d δ + 2 * eta d δ) + 1 - Real.sqrt (1 - kappa d δ)) := by
  classical
  let B := basisExtension a F
  let G := B.adjoint.comp B
  have hG0 : 0 ≤ G :=
    ContinuousLinearMap.nonneg_iff_isPositive.mpr (isPositive_adjoint_comp_self B)
  have hGs : IsSelfAdjoint G := hG0.isSelfAdjoint
  have hk0 : 0 ≤ kappa d δ := by
    unfold kappa
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    positivity
  have he0 : 0 ≤ eta d δ := mul_nonneg (Real.sqrt_nonneg _) hδ
  have hspec : ∀ t ∈ spectrum ℝ G, |t - 1| ≤ kappa d δ :=
    gram_spectrum hd a F hδ hN (fun x hx j =>
      four_anchor_coordinates a F hN hphase hcomp x hx j)
  have hpos : IsStrictlyPositive G := by
    apply (StarOrderedRing.isStrictlyPositive_iff_spectrum_pos (R := ℝ) G hGs).mpr
    intro t ht
    have := (abs_le.mp (hspec t ht)).1
    linarith
  have hGram : ‖G - 1‖ ≤ kappa d δ := by
    have heq : cfc (fun t : ℝ => t - 1) G = G - 1 := by
      rw [cfc_sub (fun t : ℝ => t) (fun _ : ℝ => 1) G (by fun_prop) (by fun_prop),
        cfc_id' ℝ G hGs, cfc_const_one ℝ G hGs]
    rw [← heq]
    exact norm_cfc_le hk0 (fun t ht => by simpa [Real.norm_eq_abs] using hspec t ht)
  have hradius : 0 ≤ 1 - Real.sqrt (1 - kappa d δ) := by
    have hs : Real.sqrt (1 - kappa d δ) ≤ 1 :=
      Real.sqrt_le_one.mpr (by linarith)
    linarith
  have hroot : ‖CFC.sqrt G - 1‖ ≤ 1 - Real.sqrt (1 - kappa d δ) := by
    have heq : cfc (fun t : ℝ => Real.sqrt t - 1) G = CFC.sqrt G - 1 := by
      rw [cfc_sub Real.sqrt (fun _ : ℝ => 1) G (by fun_prop) (by fun_prop),
        cfc_const_one ℝ G hGs, CFC.sqrt_eq_real_sqrt G hG0,
        cfcₙ_eq_cfc (f := Real.sqrt)]
    rw [← heq]
    exact norm_cfc_le hradius (fun t ht => by
      simpa [Real.norm_eq_abs] using scalar_root_bound hk0 hsmall (hspec t ht))
  let R := CFC.sqrt G
  let Q := R⁻¹ʳ
  have hR : IsUnit R := (CFC.isUnit_sqrt_iff G hG0).mpr hpos.isUnit
  have hRQ : R * Q = 1 := Ring.mul_inverse_cancel R hR
  have hQR : Q * R = 1 := Ring.inverse_mul_cancel R hR
  have hQ : Q.adjoint = Q := (CFC.sqrt_nonneg G).isSelfAdjoint.ringInverse.star_eq
  let U₀ := B.comp Q
  have hU : U₀.adjoint.comp U₀ = 1 := by
    have heq : U₀.adjoint.comp U₀ = Q * (G * Q) := by
      ext x
      simp only [U₀, G, adjoint_comp, comp_apply, hQ]
      rfl
    rw [heq, ← CFC.sqrt_mul_sqrt_self G hG0]
    change Q * (R * R * Q) = 1
    calc
      _ = (Q * R) * (R * Q) := by noncomm_ring
      _ = 1 := by rw [hQR, hRQ, one_mul]
  let U : H →ₗᵢ[ℂ] W :=
    { U₀.toLinearMap with norm_map' := U₀.norm_map_iff_adjoint_comp_self.mpr hU }
  have hUR : U₀.comp R = B := by
    ext x
    change B (Q (R x)) = B x
    have he := congrArg (fun T : H →L[ℂ] H => T x) hQR
    change Q (R x) = x at he
    exact congrArg B he
  have hUnorm : ‖U₀‖ ≤ 1 := by
    apply U₀.opNorm_le_bound zero_le_one
    intro x
    change ‖U₀ x‖ ≤ 1 * ‖x‖
    rw [one_mul]
    exact (U₀.norm_map_iff_adjoint_comp_self.mpr hU x).le
  have hBU : ‖B - U₀‖ ≤ 1 - Real.sqrt (1 - kappa d δ) := by
    have heq : B - U₀ = U₀.comp (R - 1) := by
      rw [ContinuousLinearMap.comp_sub, hUR]
      rfl
    rw [heq]
    exact (U₀.opNorm_comp_le (R - 1)).trans
      ((mul_le_mul_of_nonneg_right hUnorm (norm_nonneg _)).trans (by simpa [R] using hroot))
  refine ⟨hpos, U, rfl, hGram, hBU, ?_⟩
  intro x hx
  have hζ : ‖B.adjoint (F x) - x‖ ≤ eta d δ :=
    coordinate_error a F hδ hN hphase hcomp x hx
  have hquad : (⟪x, (G - 1) x⟫_ℂ).re ≤ kappa d δ := by
    calc
      _ ≤ ‖⟪x, (G - 1) x⟫_ℂ‖ := Complex.re_le_norm _
      _ ≤ ‖x‖ * ‖(G - 1) x‖ := norm_inner_le_norm _ _
      _ ≤ kappa d δ := by
        rw [hx, one_mul]
        exact ((G - 1).le_opNorm x).trans (by simpa [hx] using hGram)
  have herr : -(⟪x, B.adjoint (F x) - x⟫_ℂ).re ≤ eta d δ := by
    calc
      _ ≤ |(⟪x, B.adjoint (F x) - x⟫_ℂ).re| := neg_le_abs _
      _ ≤ ‖⟪x, B.adjoint (F x) - x⟫_ℂ‖ := Complex.abs_re_le_norm _
      _ ≤ ‖x‖ * ‖B.adjoint (F x) - x‖ := norm_inner_le_norm _ _
      _ ≤ eta d δ := by simpa only [hx, one_mul] using hζ
  have hid : ‖F x - B x‖ ^ 2 =
      (⟪x, (G - 1) x⟫_ℂ).re - 2 * (⟪x, B.adjoint (F x) - x⟫_ℂ).re := by
    have hnB := B.apply_norm_sq_eq_inner_adjoint_right x
    change ‖B x‖ ^ 2 = (⟪x, G x⟫_ℂ).re at hnB
    rw [norm_sub_sq (𝕜 := ℂ), hN x hx, inner_re_symm (F x) (B x),
      ← adjoint_inner_right B x (F x)]
    change 1 ^ 2 - 2 * (⟪x, B.adjoint (F x)⟫_ℂ).re + ‖B x‖ ^ 2 = _
    have hxx : ⟪x, x⟫_ℂ = 1 := by
      rw [inner_self_eq_norm_sq_to_K, hx]
      norm_num
    have hone : (1 : H →L[ℂ] H) x = x := rfl
    simp only [ContinuousLinearMap.sub_apply, hone,
      inner_sub_right, Complex.sub_re, hxx, Complex.one_re]
    linarith

  have hFB : ‖F x - B x‖ ≤ Real.sqrt (kappa d δ + 2 * eta d δ) := by
    apply (Real.le_sqrt (norm_nonneg _) (by positivity)).mpr
    rw [hid]
    linarith
  apply le_min
  · calc
      ‖F x - U x‖ ≤ ‖F x‖ + ‖U x‖ := norm_sub_le _ _
      _ = 2 := by rw [hN x hx, U.norm_map, hx]; norm_num
  · calc
      ‖F x - U x‖ ≤ ‖F x - B x‖ + ‖B x - U x‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ Real.sqrt (kappa d δ + 2 * eta d δ) +
          (1 - Real.sqrt (1 - kappa d δ)) := by
        apply add_le_add hFB
        exact ((B - U₀).le_opNorm x).trans (by simpa [hx] using hBU)
      _ = _ := by ring

#print axioms finite_oriented_anchor_polar_repair

end D5.S3.Quantum.Foundation.ApproximateOrientedAnchorRepair
