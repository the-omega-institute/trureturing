/- GID: D5/S3/Entropy/DoubleSidedBottleneckMoments
   generality: G
   mirror-B: D5/B/S3/Entropy/DoubleSidedBottleneckMoments
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Uniform entropy deficits control all posterior moment products. -/

/-
admission_basis: escape-witness
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/30706
The source entropy is the frozen binaryEntropyBits expression; no entropy alias is added.
Direct frozen dependencies: declaration identities at base fcd028003080ee51fe117e1277b6f3768c12b47a.
F1: D5/S3/Quantum/Information/QubitEntropyContraction.logRatio; statement_id=sha256:bb9ddc35fc615b4ef0c2ef184ee0b38420a2fea66b80854ce40df89141cdfd1e
F2: D5/S3/Quantum/Information/QubitEntropyContraction.radialEntropy; statement_id=sha256:7a1844d69160c7cdadf8d7d90c10352564fffc2c16ba40e815a355ebc8bc8ebd
F3: D5/S3/Quantum/Information/QubitEntropyContraction.radial_concave; statement_id=sha256:8026c9153902c93bfa1487395d7f93f3268e56ab78a89faa6aa82ebcb253cff0
F4: D5/S3/Quantum/Information/QubitEntropyContraction.radial_deriv; statement_id=sha256:e8867f89ff5d6dbfe903566df6ee22ac61ad20b965100eb78500fcd8a1d28307
F5: D5/S3/Quantum/Information/QubitEntropyContraction.radial_deriv2; statement_id=sha256:0d6c93f85b7e4c54a6cc869eee6cc53e301d2b85b55ae58405f8953d16d69a2a
Declarations (frozen inputs above are followed through same-delivery helpers):
Curvature.phi: proof_shape: bind-only; escape_witness: none; dependencies: none; consumers: Curvature.entropy_strong_convex,Curvature.phi_convex,Curvature.phi_hasDerivAt,Curvature.phi_strictMono,Curvature.phi_tangent_bound,D5.S3.Entropy.DoubleSidedBottleneckBSC.Boundary.phi_psi,D5.S3.Entropy.DoubleSidedBottleneckBSC.Boundary.scalar_mgl,D5.S3.Entropy.DoubleSidedBottleneckBSC.bias_zero_of_rate_nonpos,D5.S3.Entropy.DoubleSidedBottleneckBSC.full_budget_upper,D5.S3.Entropy.DoubleSidedBottleneckBSC.interior_bscOptimal,D5.S3.Entropy.DoubleSidedBottleneckBSC.objective_noiseless_formula,D5.S3.Entropy.DoubleSidedBottleneckBSC.phi_bias,D5.S3.Entropy.DoubleSidedBottleneckBSC.phi_crossover,D5.S3.Entropy.DoubleSidedBottleneckBSC.phi_f,D5.S3.Entropy.DoubleSidedBottleneckBSC.rate_phi,entropy_moment_deficits,entropy_product_moment_deficits,posterior_local_optimality
Curvature.entropy_strong_convex: proof_shape: bind-only; escape_witness: none; dependencies: F1,F2,F4,F5; consumers: entropy_moment_deficits
Curvature.phi_convex: proof_shape: bind-only; escape_witness: none; dependencies: F3; consumers: Curvature.phi_tangent_bound,D5.S3.Entropy.DoubleSidedBottleneckBSC.bias_zero_of_rate_nonpos,entropy_moment_deficits
Curvature.phi_strictMono: proof_shape: bind-only; escape_witness: none; dependencies: none; consumers: D5.S3.Entropy.DoubleSidedBottleneckBSC.bias_zero_of_rate_nonpos,entropy_moment_deficits
Curvature.slope: proof_shape: bind-only; escape_witness: none; dependencies: F1; consumers: Curvature.phi_hasDerivAt,Curvature.phi_tangent_bound,Curvature.slope_nonneg,D5.S3.Entropy.DoubleSidedBottleneckBSC.interior_bscOptimal,entropy_moment_deficits,entropy_product_moment_deficits,posterior_local_optimality
Curvature.phi_hasDerivAt: proof_shape: bind-only; escape_witness: none; dependencies: F2,F1,F4; consumers: Curvature.phi_tangent_bound
Curvature.slope_nonneg: proof_shape: bind-only; escape_witness: none; dependencies: F1; consumers: D5.S3.Entropy.DoubleSidedBottleneckBSC.interior_bscOptimal,entropy_product_moment_deficits,posterior_local_optimality
Curvature.phi_tangent_bound: proof_shape: bind-only; escape_witness: none; dependencies: F2,F1,F4,F3; consumers: entropy_moment_deficits
Moments.power_taylor_bound: proof_shape: content; escape_witness: Moments.power_taylor_bound; dependencies: none; consumers: Moments.even_moment_deficit
Moments.avg_add: proof_shape: bind-only; escape_witness: none; dependencies: none; consumers: Moments.even_moment_deficit,Moments.variance_identity
Moments.avg_sub: proof_shape: bind-only; escape_witness: none; dependencies: none; consumers: D5.S3.Entropy.DoubleSidedBottleneckBSC.Boundary.scalar_mgl,Moments.even_moment_deficit,Moments.odd_moment_sq_deficit,Moments.variance_identity
Moments.avg_mul: proof_shape: bind-only; escape_witness: none; dependencies: none; consumers: Moments.even_moment_deficit,Moments.odd_moment_sq_deficit,Moments.variance_identity
Moments.avg_const: proof_shape: bind-only; escape_witness: none; dependencies: none; consumers: D5.S3.Entropy.DoubleSidedBottleneckBSC.Boundary.scalar_mgl,Moments.even_moment_deficit,Moments.variance_identity
Moments.variance_identity: proof_shape: bind-only; escape_witness: none; dependencies: none; consumers: Moments.strong_jensen_deficit
Moments.strong_jensen_deficit: proof_shape: bind-only; escape_witness: none; dependencies: none; consumers: entropy_moment_deficits
Moments.even_moment_deficit: proof_shape: content; escape_witness: Moments.power_taylor_bound; dependencies: none; consumers: entropy_moment_deficits
Moments.power_lipschitz: proof_shape: bind-only; escape_witness: none; dependencies: none; consumers: Moments.odd_moment_sq_deficit
Moments.weighted_cauchy: proof_shape: bind-only; escape_witness: none; dependencies: none; consumers: Moments.odd_moment_sq_deficit
Moments.odd_moment_sq_deficit: proof_shape: bind-only; escape_witness: none; dependencies: none; consumers: entropy_moment_deficits
Series.coeffTerm: proof_shape: bind-only; escape_witness: none; dependencies: none; consumers: Series.coefficient_comparison,Series.hasSum_f,Series.product_hasSum,posterior_local_optimality
Series.hasSum_f: proof_shape: bind-only; escape_witness: none; dependencies: none; consumers: Series.product_hasSum
ProductBounds.even_product_deficit: proof_shape: bind-only; escape_witness: none; dependencies: none; consumers: entropy_product_moment_deficits
ProductBounds.odd_product_deficit: proof_shape: bind-only; escape_witness: none; dependencies: none; consumers: entropy_product_moment_deficits
ProductBounds.leading_deficit: proof_shape: bind-only; escape_witness: none; dependencies: none; consumers: posterior_local_optimality
ProductBounds.threshold_tail_nonpos: proof_shape: bind-only; escape_witness: none; dependencies: none; consumers: posterior_local_optimality
entropy_moment_deficits: proof_shape: content; escape_witness: Moments.power_taylor_bound; dependencies: F2,F1,F4,F3,F5; consumers: entropy_product_moment_deficits,posterior_local_optimality
power_avg_bounds: proof_shape: bind-only; escape_witness: none; dependencies: none; consumers: entropy_product_moment_deficits
entropy_product_moment_deficits: proof_shape: content; escape_witness: Moments.power_taylor_bound; dependencies: F1,F2,F4,F3,F5; consumers: posterior_local_optimality
Series.product_hasSum: proof_shape: bind-only; escape_witness: none; dependencies: none; consumers: posterior_local_optimality
Series.half: proof_shape: bind-only; escape_witness: none; dependencies: none; consumers: D5.S3.Entropy.DoubleSidedBottleneckBSC.interior_bscOptimal,D5.S3.Entropy.DoubleSidedBottleneckBSC.objective_bsc_productValue,Series.coefficient_comparison,Series.symmetric_even,Series.symmetric_odd,posterior_local_optimality
Series.signed: proof_shape: bind-only; escape_witness: none; dependencies: none; consumers: D5.S3.Entropy.DoubleSidedBottleneckBSC.interior_bscOptimal,D5.S3.Entropy.DoubleSidedBottleneckBSC.objective_bsc_productValue,Series.coefficient_comparison,Series.symmetric_even,Series.symmetric_odd,posterior_local_optimality
Series.symmetric_even: proof_shape: bind-only; escape_witness: none; dependencies: none; consumers: Series.coefficient_comparison,posterior_local_optimality
Series.symmetric_odd: proof_shape: bind-only; escape_witness: none; dependencies: none; consumers: Series.coefficient_comparison,posterior_local_optimality
Series.coefficient_comparison: proof_shape: bind-only; escape_witness: none; dependencies: none; consumers: posterior_local_optimality
Series.geometric_difference_bound: proof_shape: bind-only; escape_witness: none; dependencies: none; consumers: posterior_local_optimality
productValue: proof_shape: bind-only; escape_witness: none; dependencies: none; consumers: D5.S3.Entropy.DoubleSidedBottleneckBSC.interior_bscOptimal,D5.S3.Entropy.DoubleSidedBottleneckBSC.objective_bsc_productValue,D5.S3.Entropy.DoubleSidedBottleneckBSC.objective_noiseless_formula,D5.S3.Entropy.DoubleSidedBottleneckBSC.objective_productValue,posterior_local_optimality
posterior_local_optimality: proof_shape: content; escape_witness: Moments.power_taylor_bound; dependencies: F1,F2,F4,F3,F5; consumers: D5.S3.Entropy.DoubleSidedBottleneckBSC.interior_bscOptimal
Definitions specify objects, not proof claims; their bind-only label claims no new theorem.
The non-binding estimate is the induction invariant Moments.power_taylor_bound.
-/

import D5.S3.Quantum.Information.QubitEntropyContraction


open Set
namespace D5.S3.Entropy.DoubleSidedBottleneckMoments.Curvature

noncomputable def phi (x : ℝ) : ℝ := Real.log 2 - Real.binEntropy ((1 + Real.sqrt x) / 2)

private theorem entropy_strong_convex :
    ConvexOn ℝ (Icc (0 : ℝ) 1) (fun x => phi x - x ^ 2 / 12) := by
  let d1 : ℝ → ℝ := fun u => D5.S3.Quantum.Information.QubitEntropyContraction.logRatio (Real.sqrt u) / (4 * Real.sqrt u) - u / 6
  let d2 : ℝ → ℝ := fun u =>
    (2 * Real.sqrt u / (1 - u) - D5.S3.Quantum.Information.QubitEntropyContraction.logRatio (Real.sqrt u)) / (8 * Real.sqrt u ^ 3) - 1 / 6
  have hd1 (u : ℝ) (hu : u ∈ Ioo (0 : ℝ) 1) :
      HasDerivAt (fun x => phi x - x ^ 2 / 12) (d1 u) u := by
    have h := ((hasDerivAt_const u (Real.log 2)).sub (D5.S3.Quantum.Information.QubitEntropyContraction.radial_deriv hu)).sub
      ((hasDerivAt_pow 2 u).div_const 12)
    convert h using 1
    · rfl
    · dsimp [d1]; ring
  have hd2 (u : ℝ) (hu : u ∈ Ioo (0 : ℝ) 1) : HasDerivAt d1 (d2 u) u := by
    have h := (D5.S3.Quantum.Information.QubitEntropyContraction.radial_deriv2 hu).neg.sub ((hasDerivAt_id u).div_const 6)
    convert h using 1
    · funext x
      dsimp [d1]
      ring
    · dsimp [d2]
      ring
  apply convexOn_of_hasDerivWithinAt2_nonneg (f' := d1) (f'' := d2) (convex_Icc 0 1)
    ((continuous_const.sub (Real.binEntropy_continuous.comp (by fun_prop))).sub
      ((continuous_id.pow 2).div_const 12)).continuousOn
    (fun u hu => (hd1 u (by simpa using hu)).hasDerivWithinAt)
    (fun u hu => (hd2 u (by simpa using hu)).hasDerivWithinAt)
  intro u hu
  have hu' : u ∈ Ioo (0 : ℝ) 1 := by simpa using hu
  have hs : 0 < Real.sqrt u := Real.sqrt_pos.mpr hu'.1
  have hs1 : Real.sqrt u < 1 := (Real.sqrt_lt' (by norm_num)).mpr (by nlinarith [hu'.2])
  have hsq := Real.sq_sqrt hu'.1.le
  have hlog := Real.log_div_le_sum_range_add hs.le hs1 2
  norm_num [Finset.sum_range_succ] at hlog
  rw [Real.log_div (by positivity : 1 + Real.sqrt u ≠ 0)
    (by linarith : 1 - Real.sqrt u ≠ 0)] at hlog
  have hlog' : D5.S3.Quantum.Information.QubitEntropyContraction.logRatio (Real.sqrt u) ≤
      2 * Real.sqrt u / (1 - u) - 4 / 3 * Real.sqrt u ^ 3 := by
    change Real.log (1 + Real.sqrt u) - Real.log (1 - Real.sqrt u) ≤ _
    have hden : 0 < 1 - u := by linarith [hu'.2]
    rw [hsq] at hlog
    have hmul := (le_div_iff₀ hden).mp
      (show (Real.log (1 + Real.sqrt u) - Real.log (1 - Real.sqrt u)) / 2 -
          Real.sqrt u - Real.sqrt u ^ 3 / 3 ≤ Real.sqrt u ^ 5 / (1 - u) by linarith [hlog])
    apply (le_sub_iff_add_le).mpr
    apply (le_div_iff₀ hden).mpr
    have h3 : Real.sqrt u * u = Real.sqrt u ^ 3 := by nlinarith [hsq]
    have h5 : Real.sqrt u ^ 3 * u = Real.sqrt u ^ 5 := by
      calc
        _ = Real.sqrt u ^ 3 * Real.sqrt u ^ 2 := by rw [hsq]
        _ = _ := by ring
    nlinarith [h3, h5]
  dsimp [d2]
  apply sub_nonneg.mpr
  apply (le_div_iff₀ (by positivity : 0 < 8 * Real.sqrt u ^ 3)).mpr
  linarith

end D5.S3.Entropy.DoubleSidedBottleneckMoments.Curvature

namespace D5.S3.Entropy.DoubleSidedBottleneckMoments.Curvature

theorem phi_convex : ConvexOn ℝ (Icc (0 : ℝ) 1) phi := by
  exact (convexOn_const (Real.log 2) (convex_Icc 0 1)).sub D5.S3.Quantum.Information.QubitEntropyContraction.radial_concave

theorem phi_strictMono : StrictMonoOn phi (Icc (0 : ℝ) 1) := by
  have harg {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
      (1 + Real.sqrt x) / 2 ∈ Icc (2⁻¹ : ℝ) 1 := by
    have h0 := Real.sqrt_nonneg x
    have h1 : Real.sqrt x ≤ 1 := by simpa using Real.sqrt_le_sqrt hx.2
    constructor <;> linarith
  intro x hx y hy hxy
  have hroot : Real.sqrt x < Real.sqrt y := Real.sqrt_lt_sqrt hx.1 hxy
  have h := Real.binEntropy_strictAntiOn (harg hx) (harg hy) (by linarith)
  exact sub_lt_sub_left h (Real.log 2)

noncomputable def slope (m : ℝ) : ℝ := D5.S3.Quantum.Information.QubitEntropyContraction.logRatio (Real.sqrt m) / (4 * Real.sqrt m)

private theorem phi_hasDerivAt {m : ℝ} (hm : m ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt phi (slope m) m := by
  convert (hasDerivAt_const m (Real.log 2)).sub (D5.S3.Quantum.Information.QubitEntropyContraction.radial_deriv hm) using 1
  · rfl
  · dsimp [slope]; ring

theorem slope_nonneg {m : ℝ} (hm : m ∈ Ioo (0 : ℝ) 1) : 0 ≤ slope m := by
  have hs : Real.sqrt m < 1 := (Real.sqrt_lt' (by norm_num)).mpr (by nlinarith [hm.2])
  have hl : Real.log (1 - Real.sqrt m) ≤ Real.log (1 + Real.sqrt m) :=
    Real.log_le_log (by linarith) (by linarith [Real.sqrt_nonneg m])
  exact div_nonneg (sub_nonneg.mpr hl) (by positivity)

private theorem phi_tangent_bound {m v : ℝ} (hm : m ∈ Ioo (0 : ℝ) 1)
    (hv : v ∈ Icc (0 : ℝ) 1) (hvm : v ≤ m) :
    phi m - phi v ≤ slope m * (m - v) := by
  rcases hvm.eq_or_lt with heq | hlt
  · simp [heq]
  · have h := phi_convex.slope_le_of_hasDerivAt hv ⟨hm.1.le, hm.2.le⟩ hlt
      (phi_hasDerivAt hm)
    rw [slope_def_field] at h
    exact (div_le_iff₀ (sub_pos.mpr hlt)).mp h

end D5.S3.Entropy.DoubleSidedBottleneckMoments.Curvature

set_option autoImplicit false

open scoped BigOperators
open Finset
namespace D5.S3.Entropy.DoubleSidedBottleneckMoments.Moments


private theorem power_taylor_bound (k : ℕ) {x v : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) (hv : v ∈ Set.Icc (0 : ℝ) 1) :
    x ^ (k + 1) ≤ v ^ (k + 1) + (k + 1 : ℝ) * v ^ k * (x - v) +
      (k : ℝ) * (k + 1) / 2 * (x - v) ^ 2 := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hp : v ^ k ≤ 1 := pow_le_one₀ hv.1 hv.2
    have h₁ := mul_le_mul_of_nonneg_left ih hx.1
    have h₂ : x * ((k : ℝ) * (k + 1) / 2 * (x - v) ^ 2) ≤
        (k : ℝ) * (k + 1) / 2 * (x - v) ^ 2 :=
      mul_le_of_le_one_left (by positivity) hx.2
    have h₃ := mul_le_mul_of_nonneg_right hp
      (show 0 ≤ ((k : ℝ) + 1) * (x - v) ^ 2 by positivity)
    simp only [Nat.cast_add, Nat.cast_one, pow_succ] at *
    nlinarith

private theorem avg_add {A : Type*} [Fintype A] (p f g : A → ℝ) :
    dotProduct p (fun i => f i + g i) = dotProduct p f + dotProduct p g := by
  exact dotProduct_add p f g

theorem avg_sub {A : Type*} [Fintype A] (p f g : A → ℝ) :
    dotProduct p (fun i => f i - g i) = dotProduct p f - dotProduct p g := by
  exact dotProduct_sub p f g

private theorem avg_mul {A : Type*} [Fintype A] (p f : A → ℝ) (c : ℝ) :
    dotProduct p (fun i => c * f i) = c * dotProduct p f := by
  exact dotProduct_smul c p f

theorem avg_const {A : Type*} [Fintype A] (p : A → ℝ) (c : ℝ)
    (hp : ∑ i, p i = 1) : dotProduct p (fun _ => c) = c := by
  unfold dotProduct
  rw [← Finset.sum_mul, hp, one_mul]

private theorem variance_identity {A : Type*} [Fintype A] (p x : A → ℝ)
    (hp : ∑ i, p i = 1) :
    dotProduct p (fun i => (x i - dotProduct p x) ^ 2) = dotProduct p (fun i => x i ^ 2) - (dotProduct p x) ^ 2 := by
  have he : (fun i => (x i - dotProduct p x) ^ 2) =
      (fun i => x i ^ 2 - (2 * dotProduct p x) * x i + dotProduct p x ^ 2) := by funext i; ring
  rw [he, avg_add, avg_sub, avg_mul, avg_const p _ hp]
  ring

private theorem strong_jensen_deficit {A : Type*} [Fintype A]
    (p x : A → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1)
    (hx : ∀ i, x i ∈ Set.Icc (0 : ℝ) 1)
    (φ : ℝ → ℝ) (hφ : ConvexOn ℝ (Set.Icc 0 1) (fun t => φ t - t ^ 2 / 12))
    (m M : ℝ) (hbudget : dotProduct p (fun i => φ (x i)) ≤ φ m)
    (htangent : φ m - φ (dotProduct p x) ≤ M * (m - dotProduct p x)) :
    dotProduct p (fun i => (x i - dotProduct p x) ^ 2) ≤ 12 * M * (m - dotProduct p x) := by
  have hj := hφ.map_sum_le (t := Finset.univ) (w := p) (p := x)
    (fun i _ => hp0 i) hp1 (fun i _ => hx i)
  simp only [smul_eq_mul] at hj
  have heq : (∑ i, p i * (φ (x i) - x i ^ 2 / 12)) =
      dotProduct p (fun i => φ (x i)) - dotProduct p (fun i => x i ^ 2) / 12 := by
    simp only [dotProduct, mul_sub, sum_sub_distrib, mul_div_assoc, sum_div]
  change φ (dotProduct p x) - dotProduct p x ^ 2 / 12 ≤ _ at hj
  rw [heq] at hj
  rw [variance_identity p x hp1]
  linarith

private theorem even_moment_deficit {A : Type*} [Fintype A]
    (p x : A → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1)
    (hx : ∀ i, x i ∈ Set.Icc (0 : ℝ) 1)
    (m M : ℝ) (hv : dotProduct p x ∈ Set.Icc (0 : ℝ) 1) (hvm : dotProduct p x ≤ m)
    (hvariance : dotProduct p (fun i => (x i - dotProduct p x) ^ 2) ≤ 12 * M * (m - dotProduct p x))
    (k : ℕ) :
    dotProduct p (fun i => x i ^ (k + 1)) ≤ m ^ (k + 1) +
      6 * k * (k + 1 : ℝ) * M * (m - dotProduct p x) := by
  have hm : 0 ≤ m := hv.1.trans hvm
  have ht := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    mul_le_mul_of_nonneg_left (power_taylor_bound k (hx i) hv) (hp0 i))
  have hc : dotProduct p (fun i => x i - dotProduct p x) = 0 := by
    rw [avg_sub, avg_const p _ hp1]; ring
  have he : (∑ i, p i * (dotProduct p x ^ (k + 1) + (k + 1 : ℝ) * dotProduct p x ^ k *
      (x i - dotProduct p x) + (k : ℝ) * (k + 1) / 2 * (x i - dotProduct p x) ^ 2)) =
      dotProduct p x ^ (k + 1) +
        (k : ℝ) * (k + 1) / 2 * dotProduct p (fun i => (x i - dotProduct p x) ^ 2) := by
    change dotProduct p (fun i => _ + _ + _) = _
    rw [avg_add, avg_add, avg_const p _ hp1, avg_mul, avg_mul, hc]
    ring
  change dotProduct p (fun i => x i ^ (k + 1)) ≤ _ at ht
  rw [he] at ht
  have hp := pow_le_pow_left₀ hv.1 hvm (k + 1)
  have hvar := mul_le_mul_of_nonneg_left hvariance
    (show 0 ≤ (k : ℝ) * (k + 1) / 2 by positivity)
  nlinarith

private theorem power_lipschitz (k : ℕ) {x v : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) (hv : v ∈ Set.Icc (0 : ℝ) 1) :
    |x ^ k - v ^ k| ≤ k * |x - v| := by
  have hmax : max |x| |v| ≤ 1 := by
    rw [abs_of_nonneg hx.1, abs_of_nonneg hv.1]
    exact max_le hx.2 hv.2
  have hp : max |x| |v| ^ (k - 1) ≤ 1 :=
    pow_le_one₀ (le_max_of_le_left (abs_nonneg x)) hmax
  calc
    _ ≤ |x - v| * k * max |x| |v| ^ (k - 1) := abs_pow_sub_pow_le x v k
    _ ≤ |x - v| * k * 1 := mul_le_mul_of_nonneg_left hp (by positivity)
    _ = _ := by ring

private theorem weighted_cauchy {A : Type*} [Fintype A]
    (p s t : A → ℝ) (hp : ∀ i, 0 ≤ p i) :
    (dotProduct p (fun i => s i * t i)) ^ 2 ≤
      dotProduct p (fun i => s i ^ 2) * dotProduct p (fun i => t i ^ 2) := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (fun i _ => mul_nonneg (hp i) (sq_nonneg (s i)))
    (fun i _ => mul_nonneg (hp i) (sq_nonneg (t i)))
  intro i _
  exact le_of_eq (by ring)

private theorem odd_moment_sq_deficit {A : Type*} [Fintype A]
    (p s : A → ℝ) (hp0 : ∀ i, 0 ≤ p i)
    (hs : ∀ i, |s i| ≤ 1) (hcenter : dotProduct p s = 0)
    (m M : ℝ) (hv : dotProduct p (fun i => s i ^ 2) ∈ Set.Icc (0 : ℝ) 1)
    (hvm : dotProduct p (fun i => s i ^ 2) ≤ m)
    (hvariance : dotProduct p (fun i => (s i ^ 2 - dotProduct p (fun j => s j ^ 2)) ^ 2) ≤
      12 * M * (m - dotProduct p (fun i => s i ^ 2))) (k : ℕ) :
    (dotProduct p (fun i => s i ^ (2 * k + 1))) ^ 2 ≤
      12 * m * k ^ 2 * M * (m - dotProduct p (fun i => s i ^ 2)) := by
  let v := dotProduct p (fun i => s i ^ 2)
  have hx (i : A) : s i ^ 2 ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨sq_nonneg _, by nlinarith [abs_le.mp (hs i)]⟩
  have hcentered : dotProduct p (fun i => s i * ((s i ^ 2) ^ k - v ^ k)) =
      dotProduct p (fun i => s i ^ (2 * k + 1)) := by
    have hf : (fun i => s i * ((s i ^ 2) ^ k - v ^ k)) =
        (fun i => s i ^ (2 * k + 1) - v ^ k * s i) := by
      funext i
      rw [pow_add, pow_one, pow_mul]
      ring
    rw [hf, avg_sub, avg_mul, hcenter, mul_zero, sub_zero]
  have hcs := weighted_cauchy p s (fun i => (s i ^ 2) ^ k - v ^ k) hp0
  rw [hcentered] at hcs
  have hpoint (i : A) : ((s i ^ 2) ^ k - v ^ k) ^ 2 ≤
      (k : ℝ) ^ 2 * (s i ^ 2 - v) ^ 2 := by
    have h := power_lipschitz k (hx i) hv
    have h' := mul_self_le_mul_self (abs_nonneg ((s i ^ 2) ^ k - v ^ k)) h
    simpa only [sq_abs, ← sq, mul_pow] using h'
  have hbound : dotProduct p (fun i => ((s i ^ 2) ^ k - v ^ k) ^ 2) ≤
      (k : ℝ) ^ 2 * dotProduct p (fun i => (s i ^ 2 - v) ^ 2) := by
    rw [← avg_mul]
    exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hpoint i) (hp0 i))
  have hvar := mul_le_mul_of_nonneg_left hvariance (show 0 ≤ (k : ℝ) ^ 2 by positivity)
  have hV : 0 ≤ dotProduct p (fun i => (s i ^ 2 - v) ^ 2) :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (hp0 i) (sq_nonneg _))
  have hvv : 0 ≤ v := hv.1
  have hstep := mul_le_mul_of_nonneg_left hbound hvv
  have hstep2 := mul_le_mul_of_nonneg_right hvm (mul_nonneg (sq_nonneg (k : ℝ)) hV)
  have hm : 0 ≤ m := hv.1.trans hvm
  have hstep3 := mul_le_mul_of_nonneg_left hvar hm
  change dotProduct p (fun i => s i ^ (2 * k + 1)) ^ 2 ≤ v * _ at hcs
  nlinarith

end D5.S3.Entropy.DoubleSidedBottleneckMoments.Moments

namespace D5.S3.Entropy.DoubleSidedBottleneckMoments.Series
open Finset
open scoped BigOperators

private noncomputable def coeffTerm (z : ℝ) (k : ℕ) : ℝ :=
  (-z) ^ (k + 2) / (((k : ℝ) + 1) * ((k : ℝ) + 2))

private theorem hasSum_f {z : ℝ} (hz : |z| < 1) :
    HasSum (coeffTerm z) ((1 + z) * Real.log (1 + z) - z) := by
  have hl := Real.hasSum_pow_div_log_of_abs_lt_one (x := -z) (by simpa using hz)
  have ht : HasSum (fun k : ℕ => (-z) ^ ((k + 1) + 1) / ((k + 1 : ℕ) + 1 : ℝ))
      (-Real.log (1 + z) + z) := by
    have h := (hasSum_nat_add_iff' (f := fun k : ℕ => (-z) ^ (k + 1) / (k + 1 : ℝ)) 1).mpr hl
    simpa using h
  have hh := (hl.mul_left (-z)).sub ht
  convert hh using 1
  · funext k
    dsimp [coeffTerm]
    push_cast
    have hk1 : (k : ℝ) + 1 ≠ 0 := by exact Nat.cast_add_one_ne_zero k
    have hk2 : (k : ℝ) + 2 ≠ 0 := by positivity
    field_simp [hk1, hk2]
    simp only [pow_succ]
    ring
  · simp only [sub_neg_eq_add] at *
    ring

end D5.S3.Entropy.DoubleSidedBottleneckMoments.Series

namespace D5.S3.Entropy.DoubleSidedBottleneckMoments.ProductBounds

private theorem even_product_deficit {a b m n C D E : ℝ} (k : ℕ)
    (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (hm : m ∈ Set.Icc (0 : ℝ) 1)
    (hn : n ∈ Set.Icc (0 : ℝ) 1) (hC : 0 ≤ C) (hD : 0 ≤ D) (hE : 0 ≤ E)
    (ha : a ≤ m) (hb : b ≤ n)
    (ha' : a ≤ m ^ (k + 1) + C * D)
    (hb' : b ≤ n ^ (k + 1) + C * E) :
    a * b - m ^ (k + 1) * n ^ (k + 1) ≤ C * (n * D + m * E) := by
  have hm' : m ^ (k + 1) ≤ m := (by
    rw [pow_succ]
    exact mul_le_of_le_one_left hm.1 (pow_le_one₀ hm.1 hm.2))
  have h₁ := mul_le_mul_of_nonneg_right ha' hb0
  have h₂ := mul_le_mul_of_nonneg_left hb' (pow_nonneg hm.1 (k + 1))
  have h₃ := mul_le_mul_of_nonneg_right hb (mul_nonneg hC hD)
  have h₄ := mul_le_mul_of_nonneg_right hm' (mul_nonneg hC hE)
  nlinarith

private theorem odd_product_deficit {a b m n C D E : ℝ}
    (hm : 0 ≤ m) (hn : 0 ≤ n) (hC : 0 ≤ C) (hD : 0 ≤ D) (hE : 0 ≤ E)
    (ha : a ^ 2 ≤ 2 * m * C * D) (hb : b ^ 2 ≤ 2 * n * C * E) :
    |a * b| ≤ C * (n * D + m * E) := by
  have hprod := mul_le_mul ha hb (sq_nonneg b) (by positivity : 0 ≤ 2 * m * C * D)
  have hgap : 0 ≤ C ^ 2 * (n * D - m * E) ^ 2 := mul_nonneg (sq_nonneg C) (sq_nonneg _)
  have hbound : 0 ≤ C * (n * D + m * E) := by positivity
  have hab : 0 ≤ |a * b| := abs_nonneg _
  have habsq : |a * b| ^ 2 = a ^ 2 * b ^ 2 := by rw [sq_abs, mul_pow]
  nlinarith

private theorem leading_deficit {m n D E : ℝ} (hm : 0 ≤ m) (hn : 0 ≤ n)
    (hD : D ∈ Set.Icc (0 : ℝ) m) (hE : E ∈ Set.Icc (0 : ℝ) n) :
    ((m - D) * (n - E) - m * n) / 2 ≤ -(n * D + m * E) / 4 := by
  have h₁ := mul_le_mul_of_nonneg_left hD.2 hE.1
  have h₂ := mul_le_mul_of_nonneg_left hE.2 hD.1
  nlinarith

private theorem threshold_tail_nonpos {M δ : ℝ} (hM : 0 ≤ M) (hδ : 0 ≤ δ)
    (hδ1 : δ < 1) (hsmall : δ ≤ 1 / (1 + 6 * M)) :
    -(1 : ℝ) / 4 + 3 * M * δ / (2 * (1 - δ)) ≤ 0 := by
  have hd : 0 < 1 + 6 * M := by positivity
  have h' := (le_div_iff₀ hd).mp hsmall
  have hden : 0 < 2 * (1 - δ) := by positivity
  have hh : 3 * M * δ / (2 * (1 - δ)) ≤ 1 / 4 := by
    apply (div_le_iff₀ hden).mpr
    nlinarith
  linarith

end D5.S3.Entropy.DoubleSidedBottleneckMoments.ProductBounds
namespace D5.S3.Entropy.DoubleSidedBottleneckMoments
open Moments Curvature
open scoped BigOperators

private theorem entropy_moment_deficits {A : Type*} [Fintype A]
    (p s : A → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1)
    (hs : ∀ i, |s i| ≤ 1) (hcenter : dotProduct p s = 0)
    (m : ℝ) (hm : m ∈ Set.Ioo (0 : ℝ) 1)
    (hbudget : dotProduct p (fun i => phi (s i ^ 2)) ≤ phi m) :
    dotProduct p (fun i => s i ^ 2) ∈ Set.Icc (0 : ℝ) m ∧
    dotProduct p (fun i => (s i ^ 2 - dotProduct p (fun j => s j ^ 2)) ^ 2) ≤
      12 * Curvature.slope m * (m - dotProduct p (fun i => s i ^ 2)) ∧
    ∀ k : ℕ,
      dotProduct p (fun i => s i ^ (2 * (k + 1))) ≤ m ^ (k + 1) +
        6 * k * (k + 1 : ℝ) * Curvature.slope m * (m - dotProduct p (fun i => s i ^ 2)) ∧
      (dotProduct p (fun i => s i ^ (2 * k + 1))) ^ 2 ≤
        12 * m * k ^ 2 * Curvature.slope m * (m - dotProduct p (fun i => s i ^ 2)) := by
  have hx (i : A) : s i ^ 2 ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨sq_nonneg _, by nlinarith [abs_le.mp (hs i)]⟩
  have hv : dotProduct p (fun i => s i ^ 2) ∈ Set.Icc (0 : ℝ) 1 := by
    simpa only [dotProduct, smul_eq_mul] using (convex_Icc (0 : ℝ) 1).sum_mem
      (t := Finset.univ) (w := p) (z := fun i => s i ^ 2)
      (fun i _ => hp0 i) hp1 (fun i _ => hx i)
  have hj := phi_convex.map_sum_le (t := Finset.univ) (w := p)
    (p := fun i => s i ^ 2) (fun i _ => hp0 i) hp1 (fun i _ => hx i)
  simp only [smul_eq_mul] at hj
  change phi (dotProduct p (fun i => s i ^ 2)) ≤ dotProduct p (fun i => phi (s i ^ 2)) at hj
  have hvm : dotProduct p (fun i => s i ^ 2) ≤ m :=
    (phi_strictMono.le_iff_le hv ⟨hm.1.le, hm.2.le⟩).mp (hj.trans hbudget)
  have hvar := strong_jensen_deficit p (fun i => s i ^ 2) hp0 hp1 hx phi
    entropy_strong_convex m (Curvature.slope m) hbudget (phi_tangent_bound hm hv hvm)
  refine ⟨⟨hv.1, hvm⟩, hvar, ?_⟩
  intro k
  constructor
  · simpa only [← pow_mul] using
      even_moment_deficit p (fun i => s i ^ 2) hp0 hp1 hx m (Curvature.slope m) hv hvm hvar k
  · exact odd_moment_sq_deficit p s hp0 hs hcenter m (Curvature.slope m) hv hvm hvar k

private theorem power_avg_bounds {C : Type*} [Fintype C] (w x : C → ℝ) (hw : ∀ i, 0 ≤ w i)
      (hx : ∀ i, |x i| ≤ 1) (k : ℕ) :
      0 ≤ dotProduct w (fun i => x i ^ (2 * (k + 1))) ∧
      dotProduct w (fun i => x i ^ (2 * (k + 1))) ≤ dotProduct w (fun i => x i ^ 2) := by
    have hx2 (i : C) : x i ^ 2 ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨sq_nonneg _, by nlinarith [abs_le.mp (hx i)]⟩
    constructor
    · exact Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) (Even.pow_nonneg ⟨k+1, by omega⟩ _))
    · apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_left _ (hw i)
      change x i ^ (2 * (k + 1)) ≤ x i ^ 2
      rw [pow_mul, pow_succ]
      exact mul_le_of_le_one_left (hx2 i).1 (pow_le_one₀ (hx2 i).1 (hx2 i).2)

private theorem entropy_product_moment_deficits {A B : Type*} [Fintype A] [Fintype B]
    (p s : A → ℝ) (q t : B → ℝ)
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1)
    (hq0 : ∀ j, 0 ≤ q j) (hq1 : ∑ j, q j = 1)
    (hs : ∀ i, |s i| ≤ 1) (ht : ∀ j, |t j| ≤ 1)
    (hsc : dotProduct p s = 0) (htc : dotProduct q t = 0)
    (m n : ℝ) (hm : m ∈ Set.Ioo (0 : ℝ) 1) (hn : n ∈ Set.Ioo (0 : ℝ) 1)
    (hmb : dotProduct p (fun i => phi (s i ^ 2)) ≤ phi m)
    (hnb : dotProduct q (fun j => phi (t j ^ 2)) ≤ phi n) :
    let M := max (Curvature.slope m) (Curvature.slope n)
    let D := m - dotProduct p (fun i => s i ^ 2)
    let E := n - dotProduct q (fun j => t j ^ 2)
    ∀ k : ℕ,
      dotProduct p (fun i => s i ^ (2 * (k + 1))) * dotProduct q (fun j => t j ^ (2 * (k + 1))) -
          m ^ (k + 1) * n ^ (k + 1) ≤ 6 * k * (k + 1 : ℝ) * M * (n * D + m * E) ∧
      |dotProduct p (fun i => s i ^ (2 * k + 1)) * dotProduct q (fun j => t j ^ (2 * k + 1))| ≤
        6 * k ^ 2 * M * (n * D + m * E) := by
  dsimp only
  let M := max (Curvature.slope m) (Curvature.slope n)
  let D := m - dotProduct p (fun i => s i ^ 2)
  let E := n - dotProduct q (fun j => t j ^ 2)
  have hsdef := entropy_moment_deficits p s hp0 hp1 hs hsc m hm hmb
  have htdef := entropy_moment_deficits q t hq0 hq1 ht htc n hn hnb
  have hm0 : 0 ≤ m := hm.1.le
  have hn0 : 0 ≤ n := hn.1.le
  have hD : 0 ≤ D := sub_nonneg.mpr hsdef.1.2
  have hE : 0 ≤ E := sub_nonneg.mpr htdef.1.2
  have hM : 0 ≤ M := (slope_nonneg hm).trans (le_max_left _ _)
  intro k
  have hms := le_max_left (Curvature.slope m) (Curvature.slope n)
  have hns := le_max_right (Curvature.slope m) (Curvature.slope n)
  have hme : dotProduct p (fun i => s i ^ (2 * (k + 1))) ≤ m ^ (k + 1) +
      6 * k * (k + 1 : ℝ) * M * D := by
    have hu := mul_le_mul_of_nonneg_left hms
      (show 0 ≤ 6 * (k : ℝ) * (k + 1) * D by positivity)
    have hh := (hsdef.2.2 k).1
    dsimp [D, M] at *
    nlinarith
  have hne : dotProduct q (fun j => t j ^ (2 * (k + 1))) ≤ n ^ (k + 1) +
      6 * k * (k + 1 : ℝ) * M * E := by
    have hu := mul_le_mul_of_nonneg_left hns
      (show 0 ≤ 6 * (k : ℝ) * (k + 1) * E by positivity)
    have hh := (htdef.2.2 k).1
    dsimp [E, M] at *
    nlinarith
  have hmo := (hsdef.2.2 k).2
  have hno := (htdef.2.2 k).2
  constructor
  · change _ ≤ (6 * k * (k + 1 : ℝ) * M) * (n * D + m * E)
    apply ProductBounds.even_product_deficit (C := 6 * k * (k + 1 : ℝ) * M) k
      (power_avg_bounds p s hp0 hs k).1 (power_avg_bounds q t hq0 ht k).1
      ⟨hm.1.le, hm.2.le⟩ ⟨hn.1.le, hn.2.le⟩ (by positivity) hD hE
      ((power_avg_bounds p s hp0 hs k).2.trans hsdef.1.2)
      ((power_avg_bounds q t hq0 ht k).2.trans htdef.1.2)
    · convert hme using 1 <;> dsimp [D, M] <;> ring
    · convert hne using 1 <;> dsimp [E, M] <;> ring
  · change _ ≤ (6 * (k : ℝ) ^ 2 * M) * (n * D + m * E)
    apply ProductBounds.odd_product_deficit (C := 6 * (k : ℝ) ^ 2 * M) hm.1.le hn.1.le (by positivity) hD hE
    · have hu := mul_le_mul_of_nonneg_left hms
        (show 0 ≤ 12 * m * (k : ℝ) ^ 2 * D by positivity)
      nlinarith [hmo]
    · have hu := mul_le_mul_of_nonneg_left hns
        (show 0 ≤ 12 * n * (k : ℝ) ^ 2 * E by positivity)
      nlinarith [hno]

end D5.S3.Entropy.DoubleSidedBottleneckMoments
namespace D5.S3.Entropy.DoubleSidedBottleneckMoments.Series
open Moments
open scoped BigOperators

private theorem product_hasSum {A B : Type*} [Fintype A] [Fintype B]
    (p s : A → ℝ) (q t : B → ℝ) {δ : ℝ} (hδ : |δ| < 1)
    (hs : ∀ i, |s i| ≤ 1) (ht : ∀ j, |t j| ≤ 1) :
    HasSum (fun k : ℕ => coeffTerm δ k *
      dotProduct p (fun i => s i ^ (k + 2)) * dotProduct q (fun j => t j ^ (k + 2)))
      ((∑ i, ∑ j, p i * q j * (-Real.negMulLog (1 + δ * s i * t j))) - δ * dotProduct p s * dotProduct q t) := by
  have hz (i : A) (j : B) : |δ * s i * t j| < 1 := by
    have hst : |s i| * |t j| ≤ 1 := mul_le_one₀ (hs i) (abs_nonneg _) (ht j)
    rw [abs_mul, abs_mul]
    calc
      _ = |δ| * (|s i| * |t j|) := by ring
      _ ≤ |δ| * 1 := mul_le_mul_of_nonneg_left hst (abs_nonneg δ)
      _ < 1 := by simpa using hδ
  have hh := hasSum_sum (s := Finset.univ) (fun i _ =>
    hasSum_sum (s := Finset.univ) (fun j _ =>
      (hasSum_f (hz i j)).mul_left (p i * q j)))
  convert hh using 1
  · funext k
    dsimp only [dotProduct, coeffTerm]
    rw [mul_assoc, Finset.sum_mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [show -(δ * s i * t j) = (-δ) * s i * t j by ring, mul_pow, mul_pow]
    ring
  · simp only [Real.negMulLog, neg_mul, neg_neg] at *
    simp_rw [mul_sub, Finset.sum_sub_distrib]
    congr 1
    dsimp [dotProduct]
    rw [mul_assoc, Finset.sum_mul_sum]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring

noncomputable def half : Bool → ℝ := fun _ => 1 / 2
noncomputable def signed (a : ℝ) : Bool → ℝ := fun i => if i then a else -a

private theorem symmetric_even (a : ℝ) (k : ℕ) :
    dotProduct half (fun i => signed a i ^ (2 * (k + 1))) = (a ^ 2) ^ (k + 1) := by
  simp [dotProduct, half, signed, pow_mul]

private theorem symmetric_odd (a : ℝ) (k : ℕ) :
    dotProduct half (fun i => signed a i ^ (2 * k + 1)) = 0 := by
  simp [dotProduct, half, signed, pow_add, pow_mul]

end D5.S3.Entropy.DoubleSidedBottleneckMoments.Series

namespace D5.S3.Entropy.DoubleSidedBottleneckMoments.Series
open Moments
open scoped BigOperators

private theorem coefficient_comparison (X Y : ℕ → ℝ) (a b M W δ : ℝ)
    (hM : 0 ≤ M) (hW : 0 ≤ W) (hδ : 0 ≤ δ)
    (heven : ∀ k : ℕ, X (2 * (k + 1)) * Y (2 * (k + 1)) -
      (a ^ 2) ^ (k + 1) * (b ^ 2) ^ (k + 1) ≤ 6 * k * (k + 1 : ℝ) * M * W)
    (hodd : ∀ k : ℕ, |X (2 * k + 1) * Y (2 * k + 1)| ≤ 6 * k ^ 2 * M * W)
    (k : ℕ) :
    coeffTerm δ (k + 1) *
      (X (k + 3) * Y (k + 3) -
        dotProduct half (fun i => signed a i ^ (k + 3)) * dotProduct half (fun j => signed b j ^ (k + 3))) ≤
      (3 / 2 : ℝ) * M * W * δ ^ (k + 3) := by
  have hden : 0 < ((k : ℝ) + 2) * ((k : ℝ) + 3) := by positivity
  have hmw : 0 ≤ M * W := mul_nonneg hM hW
  rcases Nat.even_or_odd (k + 3) with he | ho
  · obtain ⟨r, hr⟩ := he
    have hr0 : r ≠ 0 := by omega
    obtain ⟨u, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hr0
    have hku : k + 3 = 2 * (u + 1) := by omega
    have hkr : (k : ℝ) + 3 = 2 * (u + 1 : ℝ) := by exact_mod_cast hku
    have hmom := heven u
    have hnorm : X (k + 3) * Y (k + 3) -
        dotProduct half (fun i => signed a i ^ (k + 3)) * dotProduct half (fun j => signed b j ^ (k + 3)) ≤
        6 * u * (u + 1 : ℝ) * M * W := by
      simpa only [hku, symmetric_even] using hmom
    have hc : (X (k + 3) * Y (k + 3) -
        dotProduct half (fun i => signed a i ^ (k + 3)) * dotProduct half (fun j => signed b j ^ (k + 3))) /
        (((k : ℝ) + 2) * ((k : ℝ) + 3)) ≤ (3 / 2 : ℝ) * M * W := by
      apply (div_le_iff₀ hden).mpr
      have hpoly : 6 * (u : ℝ) * (u + 1) ≤
          (3 / 2 : ℝ) * (((k : ℝ) + 2) * ((k : ℝ) + 3)) := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_right hpoly hmw]
    have hneg : (-δ) ^ (k + 3) = δ ^ (k + 3) := by
      rw [hku, pow_mul, neg_sq, ← pow_mul]
    dsimp [coeffTerm]
    push_cast
    rw [show k + 1 + 2 = k + 3 by omega, hneg]
    convert mul_le_mul_of_nonneg_right hc (pow_nonneg hδ (k + 3)) using 1 <;> ring
  · obtain ⟨u, hu⟩ := ho
    have hku : k + 3 = 2 * u + 1 := by omega
    have hkr : (k : ℝ) + 3 = 2 * (u : ℝ) + 1 := by exact_mod_cast hku
    have hmom := hodd u
    have hnorm : -(X (k + 3) * Y (k + 3)) ≤ 6 * u ^ 2 * M * W := by
      rw [hku]
      exact (neg_le_abs _).trans hmom
    have hc : -(X (k + 3) * Y (k + 3)) /
        (((k : ℝ) + 2) * ((k : ℝ) + 3)) ≤ (3 / 2 : ℝ) * M * W := by
      apply (div_le_iff₀ hden).mpr
      have hpoly : 6 * (u : ℝ) ^ 2 ≤
          (3 / 2 : ℝ) * (((k : ℝ) + 2) * ((k : ℝ) + 3)) := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_right hpoly hmw]
    have hneg : (-δ) ^ (k + 3) = -(δ ^ (k + 3)) := by
      rw [hku, pow_add, pow_one, pow_mul, neg_sq, ← pow_mul]
      ring
    have hzeroa : dotProduct half (fun i => signed a i ^ (k + 3)) = 0 := by
      rw [hku, symmetric_odd]
    dsimp [coeffTerm]
    push_cast
    rw [show k + 1 + 2 = k + 3 by omega, hneg, hzeroa]
    convert mul_le_mul_of_nonneg_right hc (pow_nonneg hδ (k + 3)) using 1 <;> ring

private theorem geometric_difference_bound (c : ℕ → ℝ) (z M W δ : ℝ)
    (hc : HasSum c z) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hlead : c 0 ≤ -W * δ ^ 2 / 4)
    (htail : ∀ k : ℕ, c (k + 1) ≤ (3 / 2 : ℝ) * M * W * δ ^ (k + 3)) :
    z ≤ W * δ ^ 2 * (-(1 : ℝ) / 4 + 3 * M * δ / (2 * (1 - δ))) := by
  have htailSum := (hasSum_nat_add_iff' (f := c) 1).mpr hc
  simp only [Finset.sum_range_one] at htailSum
  have hgeom := (hasSum_geometric_of_lt_one hδ0 hδ1).mul_left
    ((3 / 2 : ℝ) * M * W * δ ^ 3)
  have hle : z - c 0 ≤ (3 / 2 : ℝ) * M * W * δ ^ 3 * (1 - δ)⁻¹ := by
    apply hasSum_le _ htailSum hgeom
    intro k
    convert htail k using 1 <;> rw [pow_add] <;> ring
  have hden : 1 - δ ≠ 0 := ne_of_gt (sub_pos.mpr hδ1)
  have heq : W * δ ^ 2 * (-(1 : ℝ) / 4 + 3 * M * δ / (2 * (1 - δ))) =
      -W * δ ^ 2 / 4 + (3 / 2 : ℝ) * M * W * δ ^ 3 * (1 - δ)⁻¹ := by
    field_simp [hden]
    <;> ring
  rw [heq]
  linarith

end D5.S3.Entropy.DoubleSidedBottleneckMoments.Series

namespace D5.S3.Entropy.DoubleSidedBottleneckMoments
open Moments Curvature Series
open scoped BigOperators

noncomputable def productValue {A B : Type*} [Fintype A] [Fintype B]
    (δ : ℝ) (p s : A → ℝ) (q t : B → ℝ) : ℝ :=
  ∑ i, ∑ j, p i * q j * (-Real.negMulLog (1 + δ * s i * t j))

theorem posterior_local_optimality {A B : Type*} [Fintype A] [Fintype B]
    (p s : A → ℝ) (q t : B → ℝ)
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1)
    (hq0 : ∀ j, 0 ≤ q j) (hq1 : ∑ j, q j = 1)
    (hs : ∀ i, |s i| ≤ 1) (ht : ∀ j, |t j| ≤ 1)
    (hsc : dotProduct p s = 0) (htc : dotProduct q t = 0)
    (a b : ℝ) (ha : a ^ 2 ∈ Set.Ioo (0 : ℝ) 1) (hb : b ^ 2 ∈ Set.Ioo (0 : ℝ) 1)
    (hmb : dotProduct p (fun i => phi (s i ^ 2)) ≤ phi (a ^ 2))
    (hnb : dotProduct q (fun j => phi (t j ^ 2)) ≤ phi (b ^ 2))
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hsmall : δ ≤ 1 / (1 + 6 * max (Curvature.slope (a ^ 2)) (Curvature.slope (b ^ 2)))) :
    productValue δ p s q t ≤ productValue δ half (signed a) half (signed b) := by
  let M := max (Curvature.slope (a ^ 2)) (Curvature.slope (b ^ 2))
  let D := a ^ 2 - dotProduct p (fun i => s i ^ 2)
  let E := b ^ 2 - dotProduct q (fun j => t j ^ 2)
  let W := b ^ 2 * D + a ^ 2 * E
  let X : ℕ → ℝ := fun k => dotProduct p (fun i => s i ^ k)
  let Y : ℕ → ℝ := fun k => dotProduct q (fun j => t j ^ k)
  let c : ℕ → ℝ := fun k => coeffTerm δ k *
    (X (k + 2) * Y (k + 2) -
      dotProduct half (fun i => signed a i ^ (k + 2)) * dotProduct half (fun j => signed b j ^ (k + 2)))
  have hsp := entropy_moment_deficits p s hp0 hp1 hs hsc (a ^ 2) ha hmb
  have htp := entropy_moment_deficits q t hq0 hq1 ht htc (b ^ 2) hb hnb
  have hD : D ∈ Set.Icc (0 : ℝ) (a ^ 2) :=
    ⟨sub_nonneg.mpr hsp.1.2, by dsimp [D]; linarith [hsp.1.1]⟩
  have hE : E ∈ Set.Icc (0 : ℝ) (b ^ 2) :=
    ⟨sub_nonneg.mpr htp.1.2, by dsimp [E]; linarith [htp.1.1]⟩
  have hM : 0 ≤ M := (slope_nonneg ha).trans (le_max_left _ _)
  have hW : 0 ≤ W := add_nonneg (mul_nonneg (sq_nonneg b) hD.1)
    (mul_nonneg (sq_nonneg a) hE.1)
  have hsa (i : Bool) : |signed a i| ≤ 1 := by
    have hh : |a| ≤ 1 := (sq_le_one_iff_abs_le_one a).mp ha.2.le
    cases i <;> simpa [signed] using hh
  have hsb (i : Bool) : |signed b i| ≤ 1 := by
    have hh : |b| ≤ 1 := (sq_le_one_iff_abs_le_one b).mp hb.2.le
    cases i <;> simpa [signed] using hh
  have hca : dotProduct half (signed a) = 0 := by simpa using symmetric_odd a 0
  have hcb : dotProduct half (signed b) = 0 := by simpa using symmetric_odd b 0
  have hδ : |δ| < 1 := by rwa [abs_of_nonneg hδ0]
  have hseries : HasSum c
      (productValue δ p s q t - productValue δ half (signed a) half (signed b)) := by
    have hh := (product_hasSum p s q t hδ hs ht).sub
      (product_hasSum half (signed a) half (signed b) hδ hsa hsb)
    simp only [hsc, htc, hca, hcb, mul_zero, sub_zero] at hh
    convert hh using 1
    · funext k
      dsimp [c, X, Y]
      ring
    · rfl
  have hlead : c 0 ≤ -W * δ ^ 2 / 4 := by
    have hh := mul_le_mul_of_nonneg_right
      (ProductBounds.leading_deficit (sq_nonneg a) (sq_nonneg b) hD hE) (sq_nonneg δ)
    have ha2 : dotProduct half (fun i => signed a i ^ 2) = a ^ 2 := by
      simpa using symmetric_even a 0
    have hb2 : dotProduct half (fun i => signed b i ^ 2) = b ^ 2 := by
      simpa using symmetric_even b 0
    convert hh using 1 <;> dsimp [c, X, Y, D, E, W, coeffTerm] <;>
      norm_num [ha2, hb2] <;> ring
  have hmoment := entropy_product_moment_deficits p s q t hp0 hp1 hq0 hq1 hs ht hsc htc
    (a ^ 2) (b ^ 2) ha hb hmb hnb
  have htail (k : ℕ) : c (k + 1) ≤ (3 / 2 : ℝ) * M * W * δ ^ (k + 3) := by
    have hh := coefficient_comparison X Y a b M W δ hM hW hδ0
      (fun k => (hmoment k).1) (fun k => (hmoment k).2) k
    simpa only [c, Nat.add_assoc] using hh
  have hh := geometric_difference_bound c
    (productValue δ p s q t - productValue δ half (signed a) half (signed b)) M W δ
    hseries hδ0 hδ1 hlead htail
  have hbnd := ProductBounds.threshold_tail_nonpos hM hδ0 hδ1 hsmall
  have hnonpos := mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hW (sq_nonneg δ)) hbnd
  linarith

end D5.S3.Entropy.DoubleSidedBottleneckMoments
