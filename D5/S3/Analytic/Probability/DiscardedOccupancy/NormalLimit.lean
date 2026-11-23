/- GID: D5/S3/Analytic/Probability/DiscardedOccupancy/NormalLimit
   generality: G
   mirror-B: D5/B/S3/Analytic/Probability/DiscardedOccupancy/NormalLimit
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The number of ordinary bins hit converges to a Gaussian after standardization by the row moments. -/

import D5.S3.Analytic.Probability.DiscardedOccupancy.Characteristic

section

open scoped BigOperators Topology ENNReal
open Finset Filter MeasureTheory ProbabilityTheory

namespace DiscardedOccupancy

noncomputable section

theorem weight_bounds {n : ℕ} (hn : 0 < n) {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1)
    (m j : ℕ) : 0 ≤ weight n p m j ∧ weight n p m j ≤ 1 := by
  have ha := a_bounds hn hp hp'
  exact ⟨pow_nonneg ha.1 _, pow_le_one₀ ha.1 ha.2⟩

theorem weight_succ (n : ℕ) (p : ℝ) {m j : ℕ} (hj : j < m) :
    weight n p m j = a n p * weight n p m (j + 1) := by
  have h : m - j = m - (j + 1) + 1 := by omega
  rw [weight, weight, h, pow_succ, mul_comm]

def gaussianProduct (n : ℕ) (p : ℝ) (m : ℕ) (τ : ℝ) (j : ℕ) : ℂ :=
  ∏ i ∈ range j, gaussianFactor (weight n p m (i+1) * τ) (predictableVariance n p i)

def stepBound (n : ℕ) (p τ : ℝ) : ℝ :=
  (Real.exp 1 + 1) * |τ|^3 + (τ^2 / 2) * fluctuationBound n p

theorem telescoping_comparison {n : ℕ} (hn : 0 < n) {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1)
    {m : ℕ} (hm : m ≤ n) {τ : ℝ} (hτ : |τ| ≤ 1) {j : ℕ} (hj : j ≤ m) :
    ‖rowPhase n p j (weight n p m j * τ) - gaussianProduct n p m τ j‖ ≤
      (j : ℝ) * stepBound n p τ := by
  induction j with
  | zero => simp [rowPhase_zero, gaussianProduct]
  | succ j ih =>
    let w := weight n p m (j + 1)
    let s := w * τ
    let g := gaussianFactor s (predictableVariance n p j)
    let f₀ := rowPhase n p j (weight n p m j * τ)
    let f₁ := rowPhase n p (j + 1) s
    let G := gaussianProduct n p m τ j
    have hw := weight_bounds hn hp hp' m (j + 1)
    have hs : |s| ≤ |τ| := by
      rw [show s = w * τ by rfl, abs_mul, abs_of_nonneg hw.1]
      exact mul_le_of_le_one_left (abs_nonneg _) hw.2
    have hs2 : s^2 ≤ τ^2 := by
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hs 2
    have hs3 := pow_le_pow_left₀ (abs_nonneg _) hs 3
    have hstep := conditional_comparison hn hp hp' (show j ≤ n by omega) (hs.trans hτ)
    have hscale : a n p * s = weight n p m j * τ := by
      rw [weight_succ n p (show j < m by omega), ← mul_assoc]
    rw [hscale] at hstep
    have hstep' : ‖f₁ - f₀ * g‖ ≤ stepBound n p τ := by
      refine hstep.trans ?_
      unfold stepBound
      have hf : 0 ≤ fluctuationBound n p := by unfold fluctuationBound; positivity
      gcongr
    have hprod : ‖f₀ - G‖ ≤ (j : ℝ) * stepBound n p τ := ih (by omega)
    have hmean := mean_bounds hn hp hp' j
    have hg : ‖g‖ ≤ 1 := norm_gaussianFactor_le s (v_bounds hp hp' hmean.1 hmean.2).1
    rw [gaussianProduct, Finset.prod_range_succ]
    change ‖f₁ - G * g‖ ≤ ((j + 1 : ℕ) : ℝ) * stepBound n p τ
    calc
      _ ≤ ‖f₁ - f₀ * g‖ + ‖f₀ * g - G * g‖ := by
        simpa only [dist_eq_norm] using dist_triangle f₁ (f₀ * g) (G * g)
      _ = ‖f₁ - f₀ * g‖ + ‖f₀ - G‖ * ‖g‖ := by rw [← sub_mul, norm_mul]
      _ ≤ stepBound n p τ + (j : ℝ) * stepBound n p τ :=
        add_le_add hstep' ((mul_le_of_le_one_right (norm_nonneg _) hg).trans hprod)
      _ = _ := by push_cast; ring

theorem terminal_comparison {n : ℕ} (hn : 0 < n) {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1)
    {m : ℕ} (hm : m ≤ n) {τ : ℝ} (hτ : |τ| ≤ 1) :
    ‖rowPhase n p m τ - gaussianProduct n p m τ m‖ ≤ (m : ℝ) * stepBound n p τ := by
  simpa [weight] using telescoping_comparison hn hp hp' hm hτ (le_refl m)

def deterministicVariance (n : ℕ) (p : ℝ) (m : ℕ) : ℝ :=
  ∑ j ∈ range m, (weight n p m (j+1))^2 * predictableVariance n p j

theorem gaussianProduct_eq_exp (n : ℕ) (p : ℝ) (m : ℕ) (τ : ℝ) :
    gaussianProduct n p m τ m =
      (↑(Real.exp (-(τ^2 / 2) * deterministicVariance n p m)) : ℂ) := by
  rw [gaussianProduct, deterministicVariance, Finset.mul_sum, Real.exp_sum]
  rw [Complex.ofReal_prod]
  apply Finset.prod_congr rfl
  intro j _
  unfold gaussianFactor
  congr 2
  ring

theorem deterministic_variance_error {n : ℕ} (hn : 0 < n) {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1)
    {m : ℕ} (hm : m ≤ n) :
    |deterministicVariance n p m - variance n p m| ≤ (m : ℝ) * fluctuationBound n p := by
  rw [deterministicVariance, weighted_variance hn, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ j ∈ range m,
        |(weight n p m (j+1))^2 * predictableVariance n p j -
          (a n p ^ (m - (j + 1)))^2 * expect n p j (fun x => v n p x)| := by
      simpa only [Real.norm_eq_abs] using (norm_sum_le (range m) (fun j =>
        (weight n p m (j+1))^2 * predictableVariance n p j -
          (a n p ^ (m - (j + 1)))^2 * expect n p j (fun x => v n p x)))
    _ ≤ ∑ _j ∈ range m, fluctuationBound n p := by
      apply Finset.sum_le_sum
      intro j hj
      let w := weight n p m (j + 1)
      let u := predictableVariance n p j
      change |w^2 * u - w^2 * expect n p j (fun x => v n p x)| ≤ _
      rw [← mul_sub, abs_mul, abs_of_nonneg (sq_nonneg w), abs_sub_comm,
        ← expect_const hn p j u, ← expect_sub]
      have he : |expect n p j (fun x => v n p x - u)| ≤ fluctuationBound n p :=
        (by simpa only [Real.norm_eq_abs] using norm_expect_le hp hp' (fun x => v n p x - u) :
          |expect n p j (fun x => v n p x - u)| ≤ expect n p j (fun x => |v n p x - u|)).trans
          (variance_fluctuation hn hp hp' ((mem_range.mp hj).le.trans hm))
      have hw := weight_bounds hn hp hp' m (j+1)
      exact (mul_le_of_le_one_left (abs_nonneg _) (pow_le_one₀ hw.1 hw.2)).trans he
    _ = _ := by simp [nsmul_eq_mul]

def linearCoefficient (p : ℝ) : ℝ := p * (1 - p)^3 / 6

theorem linearCoefficient_pos {p : ℝ} (hp : 0 < p) (hp' : p < 1) :
    0 < linearCoefficient p := by
  unfold linearCoefficient
  positivity

theorem linear_variance {n : ℕ} (hn : 2 ≤ n) {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) :
    linearCoefficient p * n ≤ variance n p (n - 1) := by
  have h : n ≤ 3 * (n / 2) := by omega
  have hr : (n : ℝ) ≤ 3 * ((n / 2 : ℕ) : ℝ) := by exact_mod_cast h
  have hc : 0 ≤ linearCoefficient p := by unfold linearCoefficient; positivity
  calc
    _ ≤ linearCoefficient p * (3 * ((n / 2 : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_left hr hc
    _ = (n / 2 : ℕ) * (p * (1 - p)^3 / 2) := by unfold linearCoefficient; ring
    _ ≤ _ := variance_lower (by omega) hp hp'

theorem variance_pos {n : ℕ} (hn : 2 ≤ n) {p : ℝ} (hp : 0 < p) (hp' : p < 1) :
    0 < variance n p (n - 1) := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  exact (mul_pos (linearCoefficient_pos hp hp') hn').trans_le (linear_variance hn hp.le hp'.le)

private theorem tendsto_succ_cast : Tendsto (fun N : ℕ => (N.succ : ℝ)) atTop atTop := by
  refine tendsto_atTop_mono (fun N => ?_) tendsto_natCast_atTop_atTop
  exact_mod_cast Nat.le_succ N

theorem variance_tendsto_atTop {p : ℝ} (hp : 0 < p) (hp' : p < 1) :
    Tendsto (fun N : ℕ => variance N.succ p N) atTop atTop := by
  refine tendsto_atTop_mono' atTop ?_
    (tendsto_succ_cast.const_mul_atTop (linearCoefficient_pos hp hp'))
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
  exact linear_variance (show 2 ≤ N.succ by omega) hp.le hp'.le

theorem fluctuation_tendsto (p : ℝ) :
    Tendsto (fun N : ℕ => fluctuationBound N.succ p) atTop (𝓝 0) := by
  have ht := ((Real.tendsto_sqrt_atTop.comp tendsto_succ_cast).inv_tendsto_atTop).const_mul p
  rw [mul_zero] at ht
  apply ht.congr
  intro N
  have hn : (0 : ℝ) < N.succ := by exact_mod_cast Nat.succ_pos N
  have hs := Real.sqrt_pos.2 hn
  dsimp [fluctuationBound, Function.comp_def]
  field_simp
  rw [Real.sq_sqrt hn.le]

private theorem div_variance_bound {n : ℕ} (hn : 2 ≤ n) {p : ℝ} (hp : 0 < p) (hp' : p < 1) :
    (n : ℝ) / variance n p (n - 1) ≤ 1 / linearCoefficient p := by
  apply (div_le_div_iff₀ (variance_pos hn hp hp') (linearCoefficient_pos hp hp')).2
  simpa [mul_comm] using linear_variance hn hp.le hp'.le

theorem standardized_predictor_tendsto {p : ℝ} (hp : 0 < p) (hp' : p < 1) :
    Tendsto (fun N : ℕ => deterministicVariance N.succ p N / variance N.succ p N)
      atTop (𝓝 1) := by
  apply tendsto_iff_norm_sub_tendsto_zero.2
  have hF : Tendsto (fun N : ℕ => (1 / linearCoefficient p) * fluctuationBound N.succ p)
      atTop (𝓝 0) := by
    simpa only [mul_zero] using (fluctuation_tendsto p).const_mul (1 / linearCoefficient p)
  refine squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) ?_ hF
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
    have hn : 2 ≤ N.succ := by omega
    let V := variance N.succ p N
    let P := deterministicVariance N.succ p N
    let F := fluctuationBound N.succ p
    change ‖P / V - 1‖ ≤ (1 / linearCoefficient p) * F
    have hV : 0 < V := variance_pos hn hp hp'
    have hF : 0 ≤ F := by dsimp [F, fluctuationBound]; positivity
    have hN' : (N : ℝ) ≤ N.succ := by exact_mod_cast Nat.le_succ N
    have he : P / V - 1 = (P - V) / V := by field_simp
    rw [he, Real.norm_eq_abs, abs_div, abs_of_pos hV]
    calc
      _ ≤ ((N : ℝ) * F) / V :=
        div_le_div_of_nonneg_right
          (deterministic_variance_error (Nat.succ_pos N) hp.le hp'.le (Nat.le_succ N)) hV.le
      _ ≤ ((N.succ : ℝ) * F) / V :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hN' hF) hV.le
      _ = ((N.succ : ℝ) / V) * F := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (div_variance_bound hn hp hp') hF

theorem gaussianProduct_tendsto {p : ℝ} (hp : 0 < p) (hp' : p < 1) (t : ℝ) :
    Tendsto (fun N : ℕ => gaussianProduct N.succ p N (t / Real.sqrt (variance N.succ p N)) N)
      atTop (𝓝 (↑(Real.exp (-(t^2/2))) : ℂ)) := by
  have hratio := (standardized_predictor_tendsto hp hp').const_mul (-(t^2/2))
  rw [mul_one] at hratio
  have h := ((Real.continuous_exp.tendsto _).comp hratio).ofReal
  apply h.congr
  intro N
  let V := variance N.succ p N
  let P := deterministicVariance N.succ p N
  have he : -(t^2/2) * (P / V) = -((t / Real.sqrt V)^2 / 2) * P := by
    rw [div_pow, Real.sq_sqrt (variance_nonneg (Nat.succ_pos N) hp.le hp'.le N)]
    ring
  rw [gaussianProduct_eq_exp]
  exact congrArg (fun x : ℝ => (Real.exp x : ℂ)) he

theorem phase_product_difference_tendsto {p : ℝ} (hp : 0 < p) (hp' : p < 1) (t : ℝ) :
    Tendsto (fun N : ℕ =>
      ‖rowPhase N.succ p N (t / Real.sqrt (variance N.succ p N)) -
        gaussianProduct N.succ p N (t / Real.sqrt (variance N.succ p N)) N‖)
      atTop (𝓝 0) := by
  let σ := fun N : ℕ => Real.sqrt (variance N.succ p N)
  let C := 1 / linearCoefficient p
  let R := fun N : ℕ => (Real.exp 1 + 1) * |t|^3 * (σ N)⁻¹ +
    (t^2 / 2) * fluctuationBound N.succ p
  have hσ : Tendsto σ atTop atTop := Real.tendsto_sqrt_atTop.comp (variance_tendsto_atTop hp hp')
  have hR : Tendsto R atTop (𝓝 0) := by
    simpa only [R, Pi.inv_apply, mul_zero, add_zero] using
      (hσ.inv_tendsto_atTop.const_mul ((Real.exp 1 + 1) * |t|^3)).add
        ((fluctuation_tendsto p).const_mul (t^2 / 2))
  have hCR : Tendsto (fun N => C * R N) atTop (𝓝 0) := by
    simpa only [mul_zero] using hR.const_mul C
  refine squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) ?_ hCR
  filter_upwards [eventually_ge_atTop (1 : ℕ), hσ.eventually_ge_atTop (max 1 |t|)]
    with N hN hσN
  have hn : 2 ≤ N.succ := by omega
  have hσpos : 0 < σ N := lt_of_lt_of_le zero_lt_one ((le_max_left _ _).trans hσN)
  let s := t / σ N
  have hs : |s| ≤ 1 := by
    rw [show s = t / σ N by rfl, abs_div, abs_of_pos hσpos]
    exact (div_le_one hσpos).2 ((le_max_right _ _).trans hσN)
  have hV : (σ N)^2 = variance N.succ p N :=
    Real.sq_sqrt (variance_nonneg (Nat.succ_pos N) hp.le hp'.le N)
  have hE : 0 ≤ stepBound N.succ p s := by dsimp [stepBound, fluctuationBound]; positivity
  have hRN : 0 ≤ R N := by dsimp [R, fluctuationBound]; positivity
  have hN' : (N : ℝ) ≤ N.succ := by exact_mod_cast Nat.le_succ N
  calc
    _ ≤ (N : ℝ) * stepBound N.succ p s :=
      terminal_comparison (Nat.succ_pos N) hp.le hp'.le (Nat.le_succ N) hs
    _ ≤ (N.succ : ℝ) * stepBound N.succ p s := mul_le_mul_of_nonneg_right hN' hE
    _ = ((N.succ : ℝ) / (σ N)^2) * R N := by
      dsimp only [stepBound, R, s]
      rw [abs_div, abs_of_pos hσpos]
      field_simp
    _ ≤ C * R N := by
      rw [hV]
      exact mul_le_mul_of_nonneg_right (div_variance_bound hn hp hp') hRN

theorem native_row_charFun_tendsto {p : ℝ} (hp : 0 < p) (hp' : p < 1) (t : ℝ) :
    Tendsto (fun N : ℕ =>
      charFun (standardizedLaw (Nat.succ_pos N) hp.le hp'.le N).toMeasure t)
      atTop (𝓝 (↑(Real.exp (-(t^2/2))) : ℂ)) := by
  let f := fun N : ℕ => rowPhase N.succ p N (t / Real.sqrt (variance N.succ p N))
  let g := fun N : ℕ => gaussianProduct N.succ p N (t / Real.sqrt (variance N.succ p N)) N
  have hdiff : Tendsto (fun N => f N - g N) atTop (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.2 (by simpa only [sub_zero] using
      (phase_product_difference_tendsto hp hp' t))
  have h := hdiff.add (gaussianProduct_tendsto hp hp' t)
  rw [zero_add] at h
  apply h.congr
  intro N
  rw [charFun_standardizedLaw]
  change f N - g N + g N = _
  rw [sub_add_cancel]
  unfold f rowPhase standardized
  congr 1
  funext x
  congr 1
  ring

def standardGaussian : ProbabilityMeasure ℝ := ⟨gaussianReal 0 1, inferInstance⟩

theorem native_row_normal_limit {p : ℝ} (hp : 0 < p) (hp' : p < 1) :
    Tendsto (fun N : ℕ => standardizedLaw (Nat.succ_pos N) hp.le hp'.le N)
      atTop (𝓝 standardGaussian) := by
  refine ProbabilityMeasure.tendsto_iff_tendsto_charFun.2 (fun t => ?_)
  have h : charFun standardGaussian.toMeasure t = (↑(Real.exp (-(t^2/2))) : ℂ) := by
    unfold standardGaussian
    change charFun (gaussianReal 0 1) t = _
    rw [charFun_gaussianReal, Complex.ofReal_exp]
    congr 1
    push_cast
    simp
  rw [h]
  exact native_row_charFun_tendsto hp hp' t

/-- Row index `N` represents `N + 1` ordinary bins and `N` independent throws. -/
theorem occupancy_normal_limit (k : ℕ) (hk : 2 ≤ k) :
    Tendsto (rowLaw k hk) atTop (𝓝 standardGaussian) :=
  native_row_normal_limit (palette_bounds hk).1 (palette_bounds hk).2

end
end DiscardedOccupancy

end

section

open scoped BigOperators Topology ENNReal ProbabilityTheory
open Filter Finset MeasureTheory ProbabilityTheory

namespace DiscardedOccupancy

noncomputable section

/-- A bin is counted exactly when a coordinate of the word chose that bin. -/
def literalCount (n m : ℕ) (ω : Fin m → Option (Fin n)) : ℝ :=
  ((univ.filter fun i : Fin n => ∃ t : Fin m, ω t = some i).card : ℝ)

theorem literalCount_eq_count (n m : ℕ) (ω : Fin m → Option (Fin n)) :
    literalCount n m ω = count n m ω := by
  have h : (univ.filter fun i : Fin n => ∃ t : Fin m, ω t = some i) = occupied n m ω := by
    ext i
    simp [mem_occupied_iff]
  simp [literalCount, count, h]

def literalMeasure {n : ℕ} (hn : 0 < n) {k : ℕ} (hk : 2 ≤ k) (m : ℕ) :
    Measure (Fin m → Option (Fin n)) :=
  Measure.pi fun _ : Fin m => (throwPMF hn (palette_bounds hk).1.le (palette_bounds hk).2.le).toMeasure

instance {n : ℕ} (hn : 0 < n) {k : ℕ} (hk : 2 ≤ k) (m : ℕ) :
    IsProbabilityMeasure (literalMeasure hn hk m) := by
  unfold literalMeasure
  infer_instance

theorem literal_independent_throw_law {n : ℕ} (hn : 0 < n) {k : ℕ} (hk : 2 ≤ k) (m : ℕ) :
    iIndepFun (fun t (ω : Fin m → Option (Fin n)) => ω t) (literalMeasure hn hk m) ∧
    (∀ t : Fin m,
      ((literalMeasure hn hk m).map (fun ω => ω t)) {none} =
        ENNReal.ofReal (1 - 1 / (k : ℝ))) ∧
    (∀ (t : Fin m) (i : Fin n),
      ((literalMeasure hn hk m).map (fun ω => ω t)) {some i} =
        ENNReal.ofReal (1 / ((k : ℝ) * n))) := by
  have hp := palette_bounds hk
  have he : literalMeasure hn hk m = (wordPMF hn hp.1.le hp.2.le m).toMeasure :=
    (wordMeasure_eq_pi hn hp.1.le hp.2.le m).symm
  rw [he]
  refine ⟨independent_throws hn hp.1.le hp.2.le m, ?_, ?_⟩
  · intro t
    rw [throw_marginal hn hp.1.le hp.2.le t]
    exact (palette_throw_mass hn hk).1
  · intro t i
    rw [throw_marginal hn hp.1.le hp.2.le t]
    exact (palette_throw_mass hn hk).2 i

theorem literal_moments {n : ℕ} (hn : 0 < n) {k : ℕ} (hk : 2 ≤ k) (m : ℕ) :
    (∫ ω, literalCount n m ω ∂literalMeasure hn hk m) = mean n (paletteP k) m ∧
    Var[literalCount n m; literalMeasure hn hk m] = variance n (paletteP k) m := by
  have hp := palette_bounds hk
  have he : literalMeasure hn hk m = (wordPMF hn hp.1.le hp.2.le m).toMeasure :=
    (wordMeasure_eq_pi hn hp.1.le hp.2.le m).symm
  rw [he]
  have hc : literalCount n m = fun ω => (count n m ω : ℝ) := funext (literalCount_eq_count n m)
  rw [hc]
  exact ⟨integral_count hn hp.1.le hp.2.le m, variance_count hn hp.1.le hp.2.le m⟩

/-- Standardization uses the integral and variance under the product measure of the row. -/
def literalStandardized {n : ℕ} (hn : 0 < n) {k : ℕ} (hk : 2 ≤ k) (m : ℕ)
    (ω : Fin m → Option (Fin n)) : ℝ :=
  (literalCount n m ω - ∫ y, literalCount n m y ∂literalMeasure hn hk m) /
    Real.sqrt (Var[literalCount n m; literalMeasure hn hk m])

def literalLaw (k : ℕ) (hk : 2 ≤ k) (N : ℕ) : ProbabilityMeasure ℝ :=
  ⟨(literalMeasure (Nat.succ_pos N) hk N).map (literalStandardized (Nat.succ_pos N) hk N),
    (Measure.isProbabilityMeasure_map_iff (measurable_of_countable _).aemeasurable).2
      inferInstance⟩

theorem literalLaw_eq_rowLaw (k : ℕ) (hk : 2 ≤ k) (N : ℕ) :
    literalLaw k hk N = rowLaw k hk N := by
  have hn := Nat.succ_pos N
  have hp := palette_bounds hk
  have hm := literal_moments hn hk N
  have he : literalMeasure hn hk N = (wordPMF hn hp.1.le hp.2.le N).toMeasure :=
    (wordMeasure_eq_pi hn hp.1.le hp.2.le N).symm
  apply Subtype.ext
  change (literalMeasure hn hk N).map (literalStandardized hn hk N) =
    (wordPMF hn hp.1.le hp.2.le N).toMeasure.map
      (fun ω => standardized (N + 1) (paletteP k) N (count (N + 1) N ω))
  have hfun : literalStandardized hn hk N =
      fun ω => standardized (N + 1) (paletteP k) N (count (N + 1) N ω) := by
    funext ω
    rw [literalStandardized, standardized, hm.1, hm.2, literalCount_eq_count]
  rw [hfun, he]

/-- The standardized number of hit bins in the `N + 1`-bin, `N`-throw row
converges weakly to the standard normal. -/
theorem exact_occupancy_normal_limit (k : ℕ) (hk : 2 ≤ k) :
    Tendsto (literalLaw k hk) atTop (𝓝 (⟨gaussianReal 0 1, inferInstance⟩ : ProbabilityMeasure ℝ)) := by
  exact (occupancy_normal_limit k hk).congr (fun N => (literalLaw_eq_rowLaw k hk N).symm)

theorem literal_variance_positive {n : ℕ} (hn : 2 ≤ n) {k : ℕ} (hk : 2 ≤ k) :
    0 < Var[literalCount n (n-1); literalMeasure (show 0 < n by omega) hk (n-1)] := by
  rw [(literal_moments (show 0 < n by omega) hk (n-1)).2]
  exact variance_pos hn (palette_bounds hk).1 (palette_bounds hk).2

theorem literal_variance_eventually_positive (k : ℕ) (hk : 2 ≤ k) :
    ∀ᶠ N : ℕ in atTop,
      0 < Var[literalCount (N+1) N; literalMeasure (Nat.succ_pos N) hk N] := by
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
  exact literal_variance_positive (show 2 ≤ N+1 by omega) hk

theorem literal_linear_variance {n : ℕ} (hn : 2 ≤ n) {k : ℕ} (hk : 2 ≤ k) :
    linearCoefficient (paletteP k) * n ≤
      Var[literalCount n (n-1); literalMeasure (show 0 < n by omega) hk (n-1)] := by
  rw [(literal_moments (show 0 < n by omega) hk (n-1)).2]
  exact linear_variance hn (palette_bounds hk).1.le (palette_bounds hk).2.le

end
end DiscardedOccupancy

end
