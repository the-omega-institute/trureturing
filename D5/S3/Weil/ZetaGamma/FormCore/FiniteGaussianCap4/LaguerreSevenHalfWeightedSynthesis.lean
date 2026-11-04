/- GID: D5/S3/Weil/ZetaGamma/FormCore/FiniteGaussianCap4/LaguerreSevenHalfWeightedSynthesis
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:analytic-synthesis)
   anchors: []
   utility: none
   digest: Physical graph and absolute Mellin synthesis from weighted Laguerre coefficients. -/
import D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.LaguerreSevenHalfFourthGraph
import D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.LaguerreSevenHalfMellinAbsoluteBound
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.PSeries
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.LinearAlgebra.Finsupp.LSum

/-! The source polynomials, normalization and orthogonality are the actual
definitions in LaguerreSevenHalfPolynomial/Jacobi. The complete upstream
Apache-2.0 notice is retained in LaguerreSevenHalfPolynomial. This module
constructs a map into its actual physical image; no completeness of the
Laguerre family, closedness of that image or original-domain surjectivity is
assumed. All new estimates are analytic, not finite numerical certificates. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Polynomial
open scoped BigOperators Topology ENNReal

namespace FiniteGaussianCap4.LaguerreSevenHalf.WeightedSynthesis

abbrev Coeff := lp (fun _ : ℕ => ℝ) 2

def coefficientWeight (k : ℕ) : ℝ := ((k : ℝ) + 1) ^ 2

def finiteCoefficients (v : ℕ →₀ ℝ) (k : ℕ) : ℝ := v k / coefficientWeight k

def finitePolynomial (v : ℕ →₀ ℝ) : ℝ[X] :=
  ∑ k ∈ v.support, C (finiteCoefficients v k) * psiPolynomial (2 * k)

def finiteFeature (v : ℕ →₀ ℝ) (x : ℝ) : ℝ :=
  physicalPolynomial (finitePolynomial v) x

theorem finiteFeature_eq (v : ℕ →₀ ℝ) (x : ℝ) :
    finiteFeature v x = ∑ k ∈ v.support, finiteCoefficients v k * centralPsi x (2 * k) := by
  simp only [finiteFeature, finitePolynomial, physicalPolynomial, eval_finsetSum,
    eval_mul, eval_C, Finset.mul_sum, psiPolynomial, centralPsi, phi]
  apply Finset.sum_congr rfl
  intro k hk
  ring

private theorem finiteFeature_continuous (v : ℕ →₀ ℝ) : Continuous (finiteFeature v) := by
  unfold finiteFeature physicalPolynomial
  fun_prop

private theorem finiteFeature_base_integrable (v : ℕ →₀ ℝ) :
    IntegrableOn (fun x : ℝ => x ^ (7 / 2 : ℝ) * finiteFeature v x ^ 2) (Ioi 0) := by
  simpa only [finiteFeature, pow_two, mul_assoc] using
    integrable_physical_product (finitePolynomial v) (finitePolynomial v)

private theorem finiteFeature_base_integral (v : ℕ →₀ ℝ) :
    (∫ x in Ioi (0 : ℝ), x ^ (7 / 2 : ℝ) * finiteFeature v x ^ 2) =
      ∑ k ∈ v.support, finiteCoefficients v k ^ 2 := by
  rw [show (fun x : ℝ => x ^ (7 / 2 : ℝ) * finiteFeature v x ^ 2) =
    (fun x => x ^ (7 / 2 : ℝ) * physicalPolynomial (finitePolynomial v) x *
      physicalPolynomial (finitePolynomial v) x) by funext x; simp only [finiteFeature]; ring,
    integral_physical_product, finitePolynomial, polynomialPair_sum_left]
  apply Finset.sum_congr rfl
  intro k hk
  rw [polynomialPair_C_left, polynomialPair_comm, polynomialPair_sum_left]
  simp only [polynomialPair_C_left, polynomialPair_psi]
  have hinj (j : ℕ) : (2 * j = 2 * k) ↔ j = k := by omega
  simp_rw [hinj]
  simp [Finset.sum_ite_eq', hk, pow_two]

private theorem finiteFeature_range (v : ℕ →₀ ℝ) :
    ∃ N : ℕ, (∀ x : ℝ, finiteFeature v x =
      ∑ k ∈ Finset.range N, finiteCoefficients v k * centralPsi x (2 * k)) ∧
      (∑ k ∈ Finset.range N,
        ((k : ℝ) + 1) ^ 4 * finiteCoefficients v k ^ 2) =
        ∑ k ∈ v.support, v k ^ 2 := by
  let N := v.support.sup id + 1
  have hsub : v.support ⊆ Finset.range N := by
    intro k hk
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup (f := id) hk))
  have hz (k : ℕ) (hk : k ∉ v.support) : finiteCoefficients v k = 0 := by
    have hv : v k = 0 := by simpa only [Finsupp.mem_support_iff, not_not] using hk
    simp [finiteCoefficients, hv]
  refine ⟨N, ?_, ?_⟩
  · intro x
    rw [finiteFeature_eq]
    exact Finset.sum_subset hsub (fun k hk hkn => by rw [hz k hkn, zero_mul])
  · rw [← Finset.sum_subset hsub (fun k hk hkn => by rw [hz k hkn]; ring)]
    apply Finset.sum_congr rfl
    intro k hk
    dsimp [finiteCoefficients, coefficientWeight]
    field_simp [ne_of_gt (show 0 < (k : ℝ) + 1 by positivity)]
    <;> ring

private theorem finiteFeature_fourth (v : ℕ →₀ ℝ) :
    IntegrableOn (fun x : ℝ => x ^ (15 / 2 : ℝ) * finiteFeature v x ^ 2) (Ioi 0) ∧
      (∫ x in Ioi (0 : ℝ), x ^ (15 / 2 : ℝ) * finiteFeature v x ^ 2) ≤
        (648 : ℝ) ^ 2 * ∑ k ∈ v.support, v k ^ 2 := by
  obtain ⟨N, hreal, hnorm⟩ := finiteFeature_range v
  simpa only [hreal, hnorm] using finite_even_physical_x2_graph_bound (finiteCoefficients v) N

private theorem finiteFeature_mellin_integrable (v : ℕ →₀ ℝ) :
    IntegrableOn (fun x : ℝ => x ^ (5 / 4 : ℝ) * finiteFeature v x) (Ioi 0) := by
  have h := integrable_finsetSum v.support (fun k _ =>
    (integrable_centralPsi (2 * k)).const_mul (finiteCoefficients v k))
  apply h.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  rw [finiteFeature_eq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  ring

private def reciprocalShift : Coeff :=
  ⟨fun k => 1 / ((k : ℝ) + 1), by
    apply memℓp_gen
    have h := (summable_nat_add_iff 1).mpr
      ((Real.summable_one_div_nat_pow (p := 2)).mpr (by decide))
    simp only [Nat.cast_add, Nat.cast_one] at h
    convert h using 1
    funext k
    simp only [ENNReal.toReal_ofNat, Real.rpow_two, norm_div, norm_one,
      Real.norm_of_nonneg (by positivity : 0 ≤ (k : ℝ) + 1), div_pow, one_pow]⟩

def includeFinite : (ℕ →₀ ℝ) →ₗ[ℝ] Coeff :=
  Finsupp.lsum ℝ (fun k => lp.lsingle (𝕜 := ℝ) (E := fun _ : ℕ => ℝ) 2 k)

private theorem includeFinite_apply (v : ℕ →₀ ℝ) (k : ℕ) : includeFinite v k = v k := by
  simp only [includeFinite, Finsupp.lsum_apply, Finsupp.sum, lp.coeFn_sum,
    Finset.sum_apply, lp.coeFn_single]
  simp [Finset.sum_pi_single, Finsupp.mem_support_iff, eq_comm]

private theorem includeFinite_norm_sq (v : ℕ →₀ ℝ) :
    ‖includeFinite v‖ ^ 2 = ∑ k ∈ v.support, v k ^ 2 := by
  change ‖∑ k ∈ v.support, lp.single 2 k (v k)‖ ^ 2 = _
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs] using
    lp.norm_sum_single (p := (2 : ℝ≥0∞)) (by norm_num) v v.support

private theorem includeFinite_dense : DenseRange includeFinite := by
  intro w
  apply isClosed_closure.mem_of_tendsto (lp.hasSum_single ENNReal.ofNat_ne_top w)
  apply Filter.Eventually.of_forall
  intro s
  apply subset_closure
  refine ⟨∑ k ∈ s, Finsupp.single k (w k), ?_⟩
  simp [includeFinite, map_sum, Finsupp.lsum_single]

private theorem finiteFeature_mellin_bound (v : ℕ →₀ ℝ) :
    (∫ x in Ioi (0 : ℝ), x ^ (5 / 4 : ℝ) * |finiteFeature v x|) ≤
      20 * ‖reciprocalShift‖ * ‖includeFinite v‖ := by
  have hnorm (k : ℕ) :
      |finiteCoefficients v k| * (10 * ((2 * k : ℕ) + 1 : ℝ)) ≤
        20 * (‖includeFinite v k‖ * ‖reciprocalShift k‖) := by
    rw [includeFinite_apply]
    dsimp [finiteCoefficients, coefficientWeight, reciprocalShift]
    rw [abs_div, abs_of_pos (sq_pos_of_pos (show 0 < (k : ℝ) + 1 by positivity))]
    simp only [Real.norm_eq_abs, abs_one, abs_div,
      abs_of_pos (show 0 < (k : ℝ) + 1 by positivity), Nat.cast_add, Nat.cast_mul,
      Nat.cast_one, Nat.cast_ofNat]
    calc
      _ ≤ |v k| / ((k : ℝ) + 1) ^ 2 * (20 * ((k : ℝ) + 1)) := by
        apply mul_le_mul_of_nonneg_left (by linarith)
        exact div_nonneg (abs_nonneg _) (sq_nonneg _)
      _ = _ := by
        field_simp [ne_of_gt (show 0 < (k : ℝ) + 1 by positivity)]
        <;> ring
  have hsum := lp.tsum_mul_le_mul_norm (p := (2 : ℝ≥0∞)) (q := (2 : ℝ≥0∞))
    (by norm_num; exact Real.HolderConjugate.two_two) (includeFinite v) reciprocalShift
  have hleft : IntegrableOn (fun x : ℝ => x ^ (5 / 4 : ℝ) * |finiteFeature v x|)
      (Ioi 0) := by
    apply (finiteFeature_mellin_integrable v).norm.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg hx.le _)]
  calc
    _ ≤ ∫ x in Ioi (0 : ℝ), ∑ k ∈ v.support,
        |finiteCoefficients v k| * (x ^ (5 / 4 : ℝ) * |centralPsi x (2 * k)|) := by
      apply integral_mono_ae hleft
        (integrable_finsetSum v.support (fun k _ =>
          (centralPsi_integrable_absolute_mellin (2 * k)).const_mul _))
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
        rw [finiteFeature_eq]
        calc
          _ ≤ x ^ (5 / 4 : ℝ) * ∑ k ∈ v.support,
              |finiteCoefficients v k * centralPsi x (2 * k)| :=
            mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (Real.rpow_nonneg hx.le _)
          _ = _ := by simp only [Finset.mul_sum, abs_mul]; congr 1; ext k; ring
    _ = ∑ k ∈ v.support, |finiteCoefficients v k| *
        (∫ x in Ioi (0 : ℝ), x ^ (5 / 4 : ℝ) * |centralPsi x (2 * k)|) := by
      rw [integral_finsetSum _ (fun k _ =>
        (centralPsi_integrable_absolute_mellin (2 * k)).const_mul _)]
      simp only [integral_const_mul]
    _ ≤ ∑ k ∈ v.support, 20 * (‖includeFinite v k‖ * ‖reciprocalShift k‖) := by
      apply Finset.sum_le_sum
      intro k hk
      exact (mul_le_mul_of_nonneg_left (centralPsi_absolute_mellin_le (2 * k))
        (abs_nonneg _)).trans (hnorm k)
    _ ≤ 20 * (‖includeFinite v‖ * ‖reciprocalShift‖) := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left
        ((hsum.1.sum_le_tsum v.support
          (fun _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))).trans hsum.2) (by norm_num)
    _ = _ := by ring

/-- The actual physical graph measure, with both base and fourth graph weights. -/
def graphMeasure : Measure ℝ :=
  (volume.restrict (Ioi 0)).withDensity
    (fun x => ENNReal.ofReal (x ^ (7 / 2 : ℝ) + x ^ (15 / 2 : ℝ)))

/-- The actual absolute central Mellin measure. -/
def mellinMeasure : Measure ℝ :=
  (volume.restrict (Ioi 0)).withDensity (fun x => ENNReal.ofReal (x ^ (5 / 4 : ℝ)))

abbrev PhysicalSpace := Lp ℝ 2 graphMeasure × Lp ℝ 1 mellinMeasure

private theorem graphDensity_measurable :
    Measurable (fun x : ℝ => ENNReal.ofReal (x ^ (7 / 2 : ℝ) + x ^ (15 / 2 : ℝ))) := by
  fun_prop

private theorem mellinDensity_measurable :
    Measurable (fun x : ℝ => ENNReal.ofReal (x ^ (5 / 4 : ℝ))) := by
  fun_prop

theorem finiteFeature_graph_memLp (v : ℕ →₀ ℝ) :
    MemLp (finiteFeature v) 2 graphMeasure := by
  rw [memLp_two_iff_integrable_sq (finiteFeature_continuous v).aestronglyMeasurable]
  apply (integrable_withDensity_iff_integrable_smul' graphDensity_measurable
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))).mpr
  apply ((finiteFeature_base_integrable v).add (finiteFeature_fourth v).1).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  rw [ENNReal.toReal_ofReal (add_nonneg (Real.rpow_nonneg hx.le _)
    (Real.rpow_nonneg hx.le _)), smul_eq_mul]
  simp only [Pi.add_apply]
  ring

theorem finiteFeature_mellin_memLp (v : ℕ →₀ ℝ) :
    MemLp (finiteFeature v) 1 mellinMeasure := by
  rw [memLp_one_iff_integrable]
  apply (integrable_withDensity_iff_integrable_smul' mellinDensity_measurable
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))).mpr
  apply (finiteFeature_mellin_integrable v).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  rw [ENNReal.toReal_ofReal (Real.rpow_nonneg hx.le _), smul_eq_mul]

private def featureLinear : (ℕ →₀ ℝ) →ₗ[ℝ] (ℝ → ℝ) :=
  Finsupp.lsum ℝ (fun k => LinearMap.toSpanSingleton ℝ (ℝ → ℝ)
    (fun x => centralPsi x (2 * k) / coefficientWeight k))

private theorem featureLinear_eq (v : ℕ →₀ ℝ) (x : ℝ) :
    featureLinear v x = finiteFeature v x := by
  rw [finiteFeature_eq]
  simp only [featureLinear, Finsupp.lsum_apply, Finsupp.sum,
    LinearMap.toSpanSingleton_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro k hk
  dsimp [finiteCoefficients]
  ring

private def featureToLpLinear (μ : Measure ℝ) (p : ℝ≥0∞)
    (h : ∀ v, MemLp (finiteFeature v) p μ) : (ℕ →₀ ℝ) →ₗ[ℝ] Lp ℝ p μ where
  toFun v := (h v).toLp (finiteFeature v)
  map_add' v w := by
    apply Lp.ext
    filter_upwards [(h (v + w)).coeFn_toLp, (h v).coeFn_toLp, (h w).coeFn_toLp,
      Lp.coeFn_add ((h v).toLp _) ((h w).toLp _)] with x hsum hv hw hadd
    rw [hsum, hadd, Pi.add_apply, hv, hw]
    simp only [← featureLinear_eq, map_add, Pi.add_apply]
  map_smul' c v := by
    apply Lp.ext
    filter_upwards [(h (c • v)).coeFn_toLp, (h v).coeFn_toLp,
      Lp.coeFn_smul c ((h v).toLp _)] with x hcv hv hsmul
    change _ = (c • (h v).toLp (finiteFeature v)) x
    rw [hcv, hsmul, Pi.smul_apply, hv]
    simp only [← featureLinear_eq, map_smul, Pi.smul_apply, RingHom.id_apply]

/-- The finite physical synthesis uses the same representative in both actual measures. -/
def finiteSynthesis : (ℕ →₀ ℝ) →ₗ[ℝ] PhysicalSpace :=
  (featureToLpLinear graphMeasure 2 finiteFeature_graph_memLp).prod
    (featureToLpLinear mellinMeasure 1 finiteFeature_mellin_memLp)

private theorem finiteSynthesis_graph_norm_sq (v : ℕ →₀ ℝ) :
    ‖(finiteSynthesis v).1‖ ^ 2 =
      (∫ x in Ioi (0 : ℝ), x ^ (7 / 2 : ℝ) * finiteFeature v x ^ 2) +
      (∫ x in Ioi (0 : ℝ), x ^ (15 / 2 : ℝ) * finiteFeature v x ^ 2) := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [RCLike.inner_apply, conj_trivial]
  rw [integral_congr_ae (show (fun x => (finiteSynthesis v).1 x *
      (finiteSynthesis v).1 x) =ᵐ[graphMeasure] (fun x => finiteFeature v x ^ 2) by
    filter_upwards [(finiteFeature_graph_memLp v).coeFn_toLp] with x hx
    change (finiteSynthesis v).1 x = finiteFeature v x at hx
    rw [hx, pow_two])]
  rw [graphMeasure, integral_withDensity_eq_integral_toReal_smul graphDensity_measurable
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  rw [← integral_add (finiteFeature_base_integrable v) (finiteFeature_fourth v).1]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  rw [ENNReal.toReal_ofReal (add_nonneg (Real.rpow_nonneg hx.le _)
    (Real.rpow_nonneg hx.le _)), smul_eq_mul]
  ring

private theorem finiteSynthesis_graph_bound (v : ℕ →₀ ℝ) :
    ‖(finiteSynthesis v).1‖ ≤ 649 * ‖includeFinite v‖ := by
  have hbase : (∫ x in Ioi (0 : ℝ), x ^ (7 / 2 : ℝ) * finiteFeature v x ^ 2) ≤
      ‖includeFinite v‖ ^ 2 := by
    rw [finiteFeature_base_integral, includeFinite_norm_sq]
    apply Finset.sum_le_sum
    intro k hk
    dsimp [finiteCoefficients, coefficientWeight]
    rw [div_pow]
    apply div_le_self (sq_nonneg _)
    have h : (1 : ℝ) ≤ (k : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) k]
    exact one_le_pow₀ (one_le_pow₀ h)
  have hfourth := (finiteFeature_fourth v).2
  rw [← includeFinite_norm_sq] at hfourth
  have hgraph := finiteSynthesis_graph_norm_sq v
  nlinarith [norm_nonneg (finiteSynthesis v).1, norm_nonneg (includeFinite v),
    sq_nonneg ‖includeFinite v‖]

private theorem finiteSynthesis_mellin_norm (v : ℕ →₀ ℝ) :
    ‖(finiteSynthesis v).2‖ =
      ∫ x in Ioi (0 : ℝ), x ^ (5 / 4 : ℝ) * |finiteFeature v x| := by
  rw [L1.norm_eq_integral_norm]
  rw [integral_congr_ae (show (fun x => ‖(finiteSynthesis v).2 x‖) =ᵐ[mellinMeasure]
      (fun x => |finiteFeature v x|) by
    filter_upwards [(finiteFeature_mellin_memLp v).coeFn_toLp] with x hx
    change (finiteSynthesis v).2 x = finiteFeature v x at hx
    rw [hx, Real.norm_eq_abs])]
  rw [mellinMeasure, integral_withDensity_eq_integral_toReal_smul mellinDensity_measurable
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  rw [ENNReal.toReal_ofReal (Real.rpow_nonneg hx.le _), smul_eq_mul]

def synthesisBound : ℝ := max 649 (20 * ‖reciprocalShift‖)

private theorem finiteSynthesis_bound (v : ℕ →₀ ℝ) :
    ‖finiteSynthesis v‖ ≤ synthesisBound * ‖includeFinite v‖ := by
  rw [Prod.norm_def, max_le_iff]
  constructor
  · exact (finiteSynthesis_graph_bound v).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  · rw [finiteSynthesis_mellin_norm]
    exact (finiteFeature_mellin_bound v).trans_eq (by ring) |>.trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))

/-- Continuous synthesis into the actual physical graph and absolute Mellin spaces. -/
def synthesis : Coeff →L[ℝ] PhysicalSpace := finiteSynthesis.extendOfNorm includeFinite

/-- The extension agrees with each actual finite Laguerre polynomial in both spaces. -/
theorem synthesis_finite (v : ℕ →₀ ℝ) :
    synthesis (includeFinite v) = finiteSynthesis v :=
  LinearMap.extendOfNorm_eq includeFinite_dense ⟨synthesisBound, finiteSynthesis_bound⟩ v

/-- Uniform simultaneous graph and Mellin control for all square-summable weighted coefficients. -/
theorem synthesis_norm_le (w : Coeff) : ‖synthesis w‖ ≤ synthesisBound * ‖w‖ :=
  LinearMap.norm_extendOfNorm_apply_le includeFinite_dense _ finiteSynthesis_bound w

/-- Every coefficient vector is synthesized by its actual finite single-mode sums. -/
theorem synthesis_hasSum (w : Coeff) :
    HasSum (fun k => finiteSynthesis (Finsupp.single k (w k))) (synthesis w) := by
  have hsingle (k : ℕ) : includeFinite (Finsupp.single k (w k)) = lp.single 2 k (w k) := by
    ext j
    rw [includeFinite_apply]
    simp [Finsupp.single_apply, lp.single_apply, Pi.single, Function.update, eq_comm]
  have h := synthesis.hasSum (lp.hasSum_single ENNReal.ofNat_ne_top w)
  simpa only [← hsingle, synthesis_finite] using h

end FiniteGaussianCap4.LaguerreSevenHalf.WeightedSynthesis
