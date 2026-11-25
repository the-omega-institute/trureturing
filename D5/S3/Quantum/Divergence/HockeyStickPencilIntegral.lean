/- GID: D5/S3/Quantum/Divergence/HockeyStickPencilIntegral
   generality: G
   mirror-B: D5/B/S3/Quantum/Divergence/HockeyStickPencilIntegral
   mirror-E: none(waiver:finite-matrix-proof)
   anchors: []
   utility: none
   digest: An exact weighted integral of the negative inertia of a shifted Hermitian pencil. -/

import D5.S3.Quantum.Matrix.LinGProperty.ArithmeticBound
import D5.S3.SpectralTopology.HermitianEigenvaluePerturbation
import D5.S3.Weil.Pick.DiagonalSignNegativeIndex
import D5.S3.Weil.ZetaLinear.FullRankInertiaPullback
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

/-!
# Weighted negative inertia of a Hermitian pencil

For a fixed shift with positive definite endpoints, a congruence reduces negative
inertia to scalar affine sign tests. The actual integrals of these tests are evaluated
on the two real tails. This is the fixed-shift step for Frenkel's relative entropy
formula (Lemmas 4–5 and Theorem 6, arXiv:2208.12194).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Filter Matrix MeasureTheory RHLinalg Set Unitary
open scoped BigOperators ComplexOrder ENNReal MatrixOrder Matrix.Norms.L2Operator Topology

namespace D5.S3.Quantum.Divergence.HockeyStickPencilIntegral

/-- Weight of the affine-pencil integral. Real division gives zero at both poles. -/
def pencilWeight (t : ℝ) : ℝ := 1 / (|t| * (t - 1) ^ 2)

private def spectralSummand (z : ℝ) : ℝ :=
  Real.log (1 + z) - z / (1 + z)

-- One primitive serves both tails, with b = -1 after reflection of the left tail.
private theorem tail_integral {a b : ℝ} (ha : 0 < a) (hab : b < a) (hb : b ^ 2 = 1) :
    IntegrableOn (fun x => 1 / (x * (x - b) ^ 2)) (Ioi a) ∧
      (∫ x in Ioi a, 1 / (x * (x - b) ^ 2)) = spectralSummand (-b / a) := by
  let F (x : ℝ) := Real.log x - Real.log (x - b) - b / (x - b)
  have hderiv (x : ℝ) (hx : x ∈ Ici a) :
      HasDerivAt F (1 / (x * (x - b) ^ 2)) x := by
    have hx0 : 0 < x := ha.trans_le hx
    have hxb : 0 < x - b := sub_pos.mpr (hab.trans_le hx)
    have hsub : HasDerivAt (fun y : ℝ => y - b) 1 x := (hasDerivAt_id x).sub_const b
    have h := ((Real.hasDerivAt_log hx0.ne').sub (hsub.log hxb.ne')).sub
      ((hasDerivAt_const x b).div hsub hxb.ne')
    convert h using 1
    field_simp [hx0.ne', hxb.ne']
    nlinarith only [hb]
  have hpos (x : ℝ) (hx : x ∈ Ioi a) : 0 ≤ 1 / (x * (x - b) ^ 2) :=
    div_nonneg zero_le_one (mul_nonneg (ha.trans hx).le (sq_nonneg _))
  have hinv : Tendsto (fun x : ℝ => b / (x - b)) atTop (𝓝 0) := by
    have hsub : Tendsto (fun x : ℝ => x - b) atTop atTop := by
      simpa only [sub_eq_add_neg, id_eq] using
        tendsto_atTop_add_const_right atTop (-b) tendsto_id
    simpa only [div_eq_mul_inv, mul_zero, Function.comp_def] using
      tendsto_const_nhds.mul (tendsto_inv_atTop_zero.comp hsub)
  have hlog : Tendsto (fun x : ℝ => Real.log (1 + b / (x - b))) atTop (𝓝 0) := by
    have hone : Tendsto (fun x : ℝ => 1 + b / (x - b)) atTop (𝓝 (1 : ℝ)) := by
      simpa only [add_zero] using (tendsto_const_nhds (x := (1 : ℝ))).add hinv
    have h := (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hone
    simpa only [Real.log_one, Function.comp_def] using h
  have hlim : Tendsto F atTop (𝓝 0) := by
    have h := hlog.sub hinv
    rw [sub_zero] at h
    refine h.congr' (eventually_atTop.mpr ⟨a, fun x hx => ?_⟩)
    have hx0 : x ≠ 0 := (ha.trans_le hx).ne'
    have hxb : x - b ≠ 0 := (sub_pos.mpr (hab.trans_le hx)).ne'
    have heq : 1 + b / (x - b) = x / (x - b) := by
      field_simp
      ring
    rw [heq, Real.log_div hx0 hxb]
  refine ⟨integrableOn_Ioi_deriv_of_nonneg' hderiv hpos hlim, ?_⟩
  rw [integral_Ioi_of_hasDerivAt_of_nonneg' hderiv hpos hlim, zero_sub]
  have ha0 := ha.ne'
  have hab0 := (sub_pos.mpr hab).ne'
  have heq : 1 + -b / a = (a - b) / a := by
    field_simp
    ring
  have hquot : (-b / a) / ((a - b) / a) = -(b / (a - b)) := by field_simp
  rw [spectralSummand, heq, Real.log_div hab0 ha0, hquot]
  dsimp [F]
  ring

private theorem scalar_cutoff_integral (z : ℝ) (hz : -1 < z) :
    IntegrableOn pencilWeight {t | 1 + t * z < 0} ∧
      (∫ t in {t | 1 + t * z < 0}, pencilWeight t) = spectralSummand z := by
  rcases lt_trichotomy z 0 with hn | rfl | hp
  · let a := -1 / z
    have ha : 1 < a := (lt_div_iff_of_neg hn).mpr (by linarith)
    have ha0 : 0 < a := zero_lt_one.trans ha
    have hset : {t : ℝ | 1 + t * z < 0} = Ioi a := by
      ext t
      change 1 + t * z < 0 ↔ a < t
      rw [div_lt_iff_of_neg hn]
      constructor <;> intro h <;> linarith
    have hab : -1 / a = z := by
      dsimp [a]
      field_simp
    have hweight : EqOn pencilWeight (fun x => 1 / (x * (x - 1) ^ 2)) (Ioi a) :=
      fun x hx => by simp [pencilWeight, abs_of_pos (ha0.trans hx)]
    obtain ⟨hi, he⟩ := tail_integral ha0 ha (by norm_num)
    rw [hab] at he
    refine ⟨?_, ?_⟩
    · rw [hset]
      exact hi.congr_fun (fun x hx => (hweight hx).symm) measurableSet_Ioi
    · rw [hset, setIntegral_congr_fun measurableSet_Ioi hweight, he]
  · norm_num [spectralSummand]
  · let a := 1 / z
    have ha : 0 < a := div_pos one_pos hp
    have hab : (-1 : ℝ) < a := (neg_lt_zero.mpr one_pos).trans ha
    have hset : {t : ℝ | 1 + t * z < 0} = Iio (-a) := by
      ext t
      change 1 + t * z < 0 ↔ t < -(1 / z)
      rw [← neg_div, lt_div_iff₀ hp]
      constructor <;> intro h <;> linarith
    let f (x : ℝ) := 1 / (x * (x - (-1)) ^ 2)
    have hweight : EqOn pencilWeight (fun x => f (-x)) (Iio (-a)) := by
      intro x hx
      have hx0 : x < 0 := hx.trans (neg_lt_zero.mpr ha)
      simp only [pencilWeight, abs_of_neg hx0, f]
      rw [show (-x - (-1 : ℝ)) ^ 2 = (x - 1) ^ 2 by ring]
    obtain ⟨hi, he⟩ := tail_integral ha hab (by norm_num)
    have harg : -(-1 : ℝ) / a = z := by
      dsimp [a]
      field_simp
    rw [harg] at he
    rw [hset]
    constructor
    · have hpre : (fun x : ℝ => -x) ⁻¹' Ioi a = Iio (-a) := by
        ext x
        simp
      have H := ((Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
        (Homeomorph.neg ℝ).measurableEmbedding).mpr hi
      rw [hpre] at H
      exact H.congr_fun (fun x hx => (hweight hx).symm) measurableSet_Iio
    · rw [setIntegral_congr_fun measurableSet_Iio hweight, ← integral_Iic_eq_integral_Iio,
        integral_comp_neg_Iic, neg_neg, he]

open D5.S3.Weil.Pick.DiagonalSignNegativeIndex

variable {n : Type*} [Fintype n] [DecidableEq n]

private theorem negIndex_congr {X Y : Matrix n n ℂ} (hX : X.IsHermitian)
    (hY : Y.IsHermitian) (h : X = Y) : negIndex hX = negIndex hY := by
  subst Y
  rfl

/-- For positive definite shifted endpoints, the weighted negative inertia of the
actual shifted pencil is integrable. Its integral counts each normalized eigenvalue
with the contribution `log (1 + λ) - λ / (1 + λ)`. -/
theorem integral_weighted_negIndex_shifted_pencil
    {A B : Matrix n n ℂ}
    {r : ℝ} (hX : (A + r • (1 : Matrix n n ℂ)).PosDef)
    (hY : (B + r • (1 : Matrix n n ℂ)).PosDef) :
    let hA : A.IsHermitian := by
      simpa only [add_sub_cancel_right] using
        hX.isHermitian.sub (isHermitian_one.smul (IsSelfAdjoint.all r))
    let hB : B.IsHermitian := by
      simpa only [add_sub_cancel_right] using
        hY.isHermitian.sub (isHermitian_one.smul (IsSelfAdjoint.all r))
    let R := (CFC.sqrt (A + r • (1 : Matrix n n ℂ)))⁻¹
    let hK := isHermitian_conjTranspose_mul_mul R (hB.sub hA)
    let hP (t : ℝ) := (hA.add ((hB.sub hA).smul (IsSelfAdjoint.all t))).add
      (isHermitian_one.smul (IsSelfAdjoint.all r))
    Integrable (fun t => pencilWeight t * (negIndex (hP t) : ℝ)) ∧
      (∫ t, pencilWeight t * (negIndex (hP t) : ℝ)) =
        ∑ i, (Real.log (1 + hK.eigenvalues i) -
          hK.eigenvalues i / (1 + hK.eigenvalues i)) := by
  classical
  dsimp only
  let hA : A.IsHermitian := by
    simpa only [add_sub_cancel_right] using
      hX.isHermitian.sub (isHermitian_one.smul (IsSelfAdjoint.all r))
  let hB : B.IsHermitian := by
    simpa only [add_sub_cancel_right] using
      hY.isHermitian.sub (isHermitian_one.smul (IsSelfAdjoint.all r))
  let X := A + r • (1 : Matrix n n ℂ)
  let Y := B + r • (1 : Matrix n n ℂ)
  let D := B - A
  let S := CFC.sqrt X
  let R := S⁻¹
  let K := Rᴴ * D * R
  let hK : K.IsHermitian := isHermitian_conjTranspose_mul_mul R (hB.sub hA)
  let hP (t : ℝ) := (hA.add ((hB.sub hA).smul (IsSelfAdjoint.all t))).add
    (isHermitian_one.smul (IsSelfAdjoint.all r))
  let Q (t : ℝ) := 1 + t • K
  let hQ (t : ℝ) : (Q t).IsHermitian :=
    isHermitian_one.add (hK.smul (IsSelfAdjoint.all t))
  let U : Matrix n n ℂ := hK.eigenvectorUnitary
  let d (t : ℝ) (i : n) := 1 + t * hK.eigenvalues i
  change Integrable (fun t => pencilWeight t * (negIndex (hP t) : ℝ)) ∧
    (∫ t, pencilWeight t * (negIndex (hP t) : ℝ)) =
      ∑ i, spectralSummand (hK.eigenvalues i)
  have hS : IsUnit S := (CFC.isUnit_sqrt_iff_isStrictlyPositive).mpr hX.isStrictlyPositive
  have hSdet := (Matrix.isUnit_iff_isUnit_det S).mp hS
  have hRS : R * S = 1 := Matrix.nonsing_inv_mul S hSdet
  have hSR : S * R = 1 := Matrix.mul_nonsing_inv S hSdet
  have hR : IsUnit R := Matrix.isUnit_nonsing_inv_iff.mpr hS
  have hRh : Rᴴ = R := ((CFC.sqrt_nonneg X).posSemidef.isHermitian.inv).eq
  have hSS : S * S = X := by
    simpa only [pow_two] using CFC.sq_sqrt X hX.posSemidef.nonneg
  have hRXR : Rᴴ * X * R = 1 := by
    rw [hRh, ← hSS, ← mul_assoc, hRS, one_mul, hSR]
  have hpull (t : ℝ) : Rᴴ * (A + t • D + r • (1 : Matrix n n ℂ)) * R = Q t := by
    calc
      _ = Rᴴ * (X + t • D) * R := by
        rw [show A + t • D + r • (1 : Matrix n n ℂ) = X + t • D from
          add_right_comm A (t • D) (r • 1)]
      _ = 1 + t • K := by rw [mul_add, add_mul, Matrix.mul_smul, Matrix.smul_mul, hRXR]
  have hU : U * Uᴴ = 1 := (Matrix.mem_unitaryGroup_iff.mp hK.eigenvectorUnitary.prop)
  have hU' : Uᴴ * U = 1 := (Matrix.mem_unitaryGroup_iff'.mp hK.eigenvectorUnitary.prop)
  have hdiag (t : ℝ) : Uᴴ * Q t * U = realDiagonal (d t) := by
    have hspec : K = U * realDiagonal hK.eigenvalues * Uᴴ := by
      calc
        K = conjStarAlgAut ℂ _ hK.eigenvectorUnitary
            (diagonal (RCLike.ofReal ∘ hK.eigenvalues)) := hK.spectral_theorem
        _ = _ := by rw [conjStarAlgAut_apply, star_eq_conjTranspose]; rfl
    have hD : Uᴴ * K * U = realDiagonal hK.eigenvalues := by
      calc
        _ = (Uᴴ * U) * realDiagonal hK.eigenvalues * (Uᴴ * U) := by
          conv_lhs => rw [hspec]
          noncomm_ring
        _ = _ := by rw [hU', one_mul, mul_one]
    rw [show Q t = 1 + t • K from rfl, mul_add, add_mul, mul_one, hU',
      Matrix.mul_smul, Matrix.smul_mul, hD]
    ext i j
    by_cases hij : i = j
    · subst j
      simp [realDiagonal, d, Complex.real_smul]
    · simp [realDiagonal, d, hij]
  have hQ1 : (Q 1).PosDef := by
    rw [← hpull, one_smul]
    have hYeq : A + D + r • (1 : Matrix n n ℂ) = Y := by
      dsimp [D, Y]
      abel
    rw [hYeq]
    exact hY.conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit hR)
  have hUD : (realDiagonal (d 1)).PosDef := by
    rw [← hdiag]
    have hUnitU : IsUnit U := isUnit_iff_exists_inv.mpr ⟨Uᴴ, hU⟩
    exact hQ1.conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit hUnitU)
  have hlower (i : n) : -1 < hK.eigenvalues i := by
    have hpos := (Matrix.posDef_diagonal_iff.mp hUD) i
    change (0 : ℂ) < ((1 + (1 : ℝ) * hK.eigenvalues i : ℝ) : ℂ) at hpos
    rw [← Complex.ofReal_zero, Complex.real_lt_real, one_mul] at hpos
    linarith
  have hcount (t : ℝ) : negIndex (hP t) = negativeWeightCount (d t) := by
    have hfirst := negIndex_conj_eq_of_rightInverse (hP t) R S hRS
    have hsecond := negIndex_conj_eq_of_rightInverse (hQ t) U Uᴴ hU
    calc
      _ = negIndex (isHermitian_conjTranspose_mul_mul R (hP t)) := hfirst.symm
      _ = negIndex (hQ t) := negIndex_congr _ _ (hpull t)
      _ = negIndex (isHermitian_conjTranspose_mul_mul U (hQ t)) := hsecond.symm
      _ = negIndex (real_diagonal_isHermitian (d t)) := negIndex_congr _ _ (hdiag t)
      _ = _ := real_diagonal_negIndex_eq_negative_count _
  let cutoff (i : n) : Set ℝ := {t | 1 + t * hK.eigenvalues i < 0}
  have hmeas (i : n) : MeasurableSet (cutoff i) :=
    measurableSet_lt (by fun_prop) measurable_const
  have hcut (i : n) := scalar_cutoff_integral (hK.eigenvalues i) (hlower i)
  have hi (i : n) : Integrable ((cutoff i).indicator pencilWeight) :=
    (integrable_indicator_iff (hmeas i)).mpr (hcut i).1
  have heq : (fun t => pencilWeight t * (negIndex (hP t) : ℝ)) =
      fun t => ∑ i, (cutoff i).indicator pencilWeight t := by
    funext t
    simp only [hcount, negativeWeightCount, Finset.card_eq_sum_ones, Nat.cast_sum,
      Finset.mul_sum, Finset.sum_filter]
    exact Finset.sum_congr rfl fun i _ => by simp [cutoff, d, Set.indicator_apply]
  rw [heq]
  refine ⟨integrable_finsetSum _ (fun i _ => hi i), ?_⟩
  rw [integral_finsetSum _ (fun i _ => hi i)]
  exact Finset.sum_congr rfl fun i _ => by
    rw [integral_indicator (hmeas i)]
    exact (hcut i).2

#print axioms integral_weighted_negIndex_shifted_pencil

open D5.S3.Quantum.Matrix D5.S3.SpectralTopology

private theorem eigenvalue_continuous_of_continuous {α : Type*} [TopologicalSpace α]
    {M : α → Matrix n n ℂ} (hM : ∀ x, (M x).IsHermitian)
    (hcont : Continuous M) (i : n) :
    Continuous (fun x => (hM x).eigenvalues i) := by
  let T := Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)
  have hT : Continuous T :=
    (T.toAlgEquiv.toLinearEquiv.toLinearMap.restrictScalars ℝ).continuous_of_finiteDimensional
  rw [continuous_iff_continuousAt]
  intro a
  apply tendsto_iff_dist_tendsto_zero.mpr
  have hbound (b : α) : dist ((hM b).eigenvalues i) ((hM a).eigenvalues i) ≤
      ‖T (M b - M a)‖ := by
    rw [Real.dist_eq]
    apply HermitianEigenvaluePerturbation.abs_eigenvalue_sub_eigenvalue_le
      (Matrix.isSymmetric_toEuclideanLin_iff.mpr (hM b))
      (Matrix.isSymmetric_toEuclideanLin_iff.mpr (hM a)) finrank_euclideanSpace
    intro v
    change ‖(Matrix.toEuclideanLin (M b) - Matrix.toEuclideanLin (M a)) v‖ ≤ _
    rw [← map_sub, ← Matrix.coe_toEuclideanCLM_eq_toEuclideanLin]
    exact (T (M b - M a)).le_opNorm v
  have hlim : Tendsto (fun b => ‖T (M b - M a)‖) (𝓝 a) (𝓝 0) := by
    have hc : Continuous (fun b => ‖T (M b - M a)‖) :=
      (hT.comp (hcont.sub continuous_const)).norm
    simpa only [sub_self, map_zero, norm_zero] using hc.tendsto a
  exact squeeze_zero (fun _ => dist_nonneg) hbound hlim

private theorem shifted_eigenvalue {M : Matrix n n ℂ} (hM : M.IsHermitian) (r : ℝ)
    (i : n) :
    (hM.add (isHermitian_one.smul (IsSelfAdjoint.all r))).eigenvalues i =
      hM.eigenvalues i + r := by
  let h := hM.add (isHermitian_one.smul (IsSelfAdjoint.all r))
  have he : M + r • (1 : Matrix n n ℂ) = M + (r : ℂ) • (1 : Matrix n n ℂ) := by
    ext i j
    simp [Complex.real_smul]
  let hC := he ▸ h
  have heig := LinGProperty.eigenvalues_zero_add_scalar_finite M hM r hC
    ((eigEquiv (n := n)).symm i)
  have hsame := (Matrix.IsHermitian.eigenvalues_eq_eigenvalues_iff h hC).mpr
    (congrArg Matrix.charpoly he)
  exact (congrFun hsame i).trans heig

private theorem spectral_layer_cake {M : Matrix n n ℂ} (hM : M.IsHermitian) :
    (∫⁻ r in Ioi (0 : ℝ),
      (negIndex (hM.add (isHermitian_one.smul (IsSelfAdjoint.all r))) : ℝ≥0∞)) =
        ENNReal.ofReal (rtrace (hermNegPart hM)) := by
  classical
  let : MeasurableSpace n := ⊤
  let : MeasurableSingletonClass n := ⟨fun _ => trivial⟩
  let f (i : n) := (hM.eigenvalues i)⁻
  have hmeas : Measurable f := measurable_from_top
  have hc := lintegral_eq_lintegral_meas_lt Measure.count
    (.of_forall fun _ => negPart_nonneg _) hmeas.aemeasurable
  simp only [lintegral_count, tsum_fintype] at hc
  rw [rtrace_hermNegPart, ENNReal.ofReal_sum_of_nonneg (fun i _ => negPart_nonneg (hM.eigenvalues i))]
  change _ = ∑ i, ENNReal.ofReal (f i)
  rw [hc]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  have hr0 : 0 < r := hr
  let hShift := hM.add (isHermitian_one.smul (IsSelfAdjoint.all r))
  change (negIndex hShift : ℝ≥0∞) = Measure.count {i | r < f i}
  have he (i : n) : hShift.eigenvalues i = hM.eigenvalues i + r := shifted_eigenvalue hM r i
  have hset : {i | r < f i} = (Finset.univ.filter (fun i => hShift.eigenvalues i < 0) : Set n) := by
    ext i
    simp only [Set.mem_ofPred_eq, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ,
      true_and, he i]
    change r < max (-hM.eigenvalues i) 0 ↔ hM.eigenvalues i + r < 0
    simp only [lt_max_iff, not_lt.mpr hr0.le, or_false]
    constructor <;> intro h <;> linarith
  rw [hset, Measure.count_apply_finset]
  rfl

/-- Tonelli's theorem assembles the fixed-shift formula into the affine-pencil
negative-part integral for positive semidefinite endpoints. The integral over the
positive shifts is expressed as a nonnegative Lebesgue integral. -/
theorem lintegral_weighted_negPart_pencil
    {A B : Matrix n n ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    let hM (t : ℝ) := hA.isHermitian.add
      ((hB.isHermitian.sub hA.isHermitian).smul (IsSelfAdjoint.all t))
    (∫⁻ t, ENNReal.ofReal (pencilWeight t * rtrace (hermNegPart (hM t)))) =
      ∫⁻ r in Ioi (0 : ℝ),
        let R := (CFC.sqrt (A + r • (1 : Matrix n n ℂ)))⁻¹
        let hK := isHermitian_conjTranspose_mul_mul R (hB.isHermitian.sub hA.isHermitian)
        ENNReal.ofReal (∑ i, (Real.log (1 + hK.eigenvalues i) -
          hK.eigenvalues i / (1 + hK.eigenvalues i))) := by
  classical
  let hM (t : ℝ) := hA.isHermitian.add
    ((hB.isHermitian.sub hA.isHermitian).smul (IsSelfAdjoint.all t))
  let hP (t r : ℝ) := (hM t).add (isHermitian_one.smul (IsSelfAdjoint.all r))
  let weight (t : ℝ) := ENNReal.ofReal (pencilWeight t)
  let f (t r : ℝ) := (negIndex (hP t r) : ℝ≥0∞)
  have hw (t : ℝ) : 0 ≤ pencilWeight t :=
    div_nonneg zero_le_one (mul_nonneg (abs_nonneg _) (sq_nonneg _))
  have hwm : Measurable weight := by unfold weight pencilWeight; fun_prop
  have hfm : Measurable (Function.uncurry f) := by
    have he (i : n) : Continuous (fun t => (hM t).eigenvalues i) :=
      eigenvalue_continuous_of_continuous hM (by fun_prop) i
    have hset (i : n) : MeasurableSet {p : ℝ × ℝ | (hM p.1).eigenvalues i + p.2 < 0} :=
      measurableSet_lt ((he i).measurable.comp measurable_fst |>.add measurable_snd)
        measurable_const
    have hfun : Function.uncurry f = fun p => ∑ i,
        Set.indicator {p : ℝ × ℝ | (hM p.1).eigenvalues i + p.2 < 0}
          (fun _ => (1 : ℝ≥0∞)) p := by
      funext p
      change (negIndex (hP p.1 p.2) : ℝ≥0∞) = _
      have hshift (i : n) : (hP p.1 p.2).eigenvalues i = (hM p.1).eigenvalues i + p.2 :=
        shifted_eigenvalue (hM p.1) p.2 i
      simp only [negIndex, hshift, Finset.card_eq_sum_ones, Nat.cast_sum,
        Finset.sum_filter, Set.indicator_apply, Set.mem_ofPred_eq]
      exact Finset.sum_congr rfl fun i _ => by split <;> simp_all
    rw [hfun]
    exact Finset.measurable_sum _ fun i _ => measurable_const.indicator (hset i)
  change (∫⁻ t, ENNReal.ofReal (pencilWeight t * rtrace (hermNegPart (hM t)))) = _
  calc
    _ = ∫⁻ t, ∫⁻ r in Ioi (0 : ℝ), weight t * f t r := by
      apply lintegral_congr
      intro t
      rw [ENNReal.ofReal_mul (hw t), ← spectral_layer_cake (hM t)]
      exact (lintegral_const_mul _ (hfm.comp (measurable_const.prodMk measurable_id))).symm
    _ = ∫⁻ r in Ioi (0 : ℝ), ∫⁻ t, weight t * f t r := by
      exact lintegral_lintegral_swap ((hwm.comp measurable_fst).mul hfm).aemeasurable
    _ = _ := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      have hr0 : 0 < r := hr
      have hx : (A + r • (1 : Matrix n n ℂ)).PosDef :=
        Matrix.PosDef.posSemidef_add hA (Matrix.PosDef.one.smul hr0)
      have hy : (B + r • (1 : Matrix n n ℂ)).PosDef :=
        Matrix.PosDef.posSemidef_add hB (Matrix.PosDef.one.smul hr0)
      obtain ⟨hi, he⟩ :=
        integral_weighted_negIndex_shifted_pencil hx hy
      calc
        _ = ∫⁻ t, ENNReal.ofReal (pencilWeight t * (negIndex (hP t r) : ℝ)) := by
          apply lintegral_congr
          intro t
          rw [ENNReal.ofReal_mul (hw t), ENNReal.ofReal_natCast]
        _ = ENNReal.ofReal (∫ t, pencilWeight t * (negIndex (hP t r) : ℝ)) :=
          (ofReal_integral_eq_lintegral_ofReal hi
            (.of_forall fun t => mul_nonneg (hw t) (Nat.cast_nonneg _))).symm
        _ = _ := congrArg ENNReal.ofReal he

#print axioms lintegral_weighted_negPart_pencil

end D5.S3.Quantum.Divergence.HockeyStickPencilIntegral
