/- GID: D5/S3/Observer/Linear/DerivativeLayerExactPivot
   generality: G
   mirror-B: D5/B/S3/Observer/Linear/DerivativeLayerExactPivot
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [lake/module/D5.S3.Analytic.PolynomialL2Derivative]
   utility: none
   digest: Attain the exact Schur pivot for factorially normalized derivative layers. -/

import D5.S3.Analytic.PolynomialL2Derivative
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
# Exact unit-interval pivot for real derivative layers

The kernel filtration and orthogonal layers are the `N` and `E` in
`D5.S3.Observer.Linear.DerivativeLayerNativeGramian`. The factorially
normalized layer map gives the coefficient of the corresponding monomial
in its limiting observation. We use linear maps on the layer subtypes so
the minimization can take an independent state in each earlier layer.
The output can be any real inner product space.
-/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Observer.Linear.DerivativeLayerExactPivot

open MeasureTheory
open scoped Interval Polynomial InnerProductSpace ComplexConjugate
open D5.S3.Analytic

section Filtration

variable {V W : Type*}
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable [AddCommGroup W] [Module ℝ W]

/-- Vanishing of the first `k` output derivatives. -/
def derivativeKernel (B : V →ₗ[ℝ] V) (C : V →ₗ[ℝ] W) (k : ℕ) : Submodule ℝ V :=
  ⨅ j : Fin k, LinearMap.ker (C.comp (B ^ (j : ℕ)))

/-- The new observable directions at order `k`. -/
def derivativeLayer (B : V →ₗ[ℝ] V) (C : V →ₗ[ℝ] W) (k : ℕ) : Submodule ℝ V :=
  derivativeKernel B C k ⊓ (derivativeKernel B C (k + 1))ᗮ

/-- The coefficient of `s ^ k` on the order-`k` layer. -/
def derivativeLayerOutput (B : V →ₗ[ℝ] V) (C : V →ₗ[ℝ] W) (k : ℕ) :
    derivativeLayer B C k →ₗ[ℝ] W :=
  (k.factorial : ℝ)⁻¹ • (C.comp (B ^ k)).domRestrict (derivativeLayer B C k)

private theorem mem_derivativeKernel (B : V →ₗ[ℝ] V) (C : V →ₗ[ℝ] W)
    (k : ℕ) (x : V) :
    x ∈ derivativeKernel B C k ↔ ∀ j : ℕ, j < k → C ((B ^ j) x) = 0 := by
  unfold derivativeKernel
  constructor
  · intro hx j hj
    have hz := ((Submodule.mem_iInf _).mp hx) (⟨j, hj⟩ : Fin k)
    simpa only [LinearMap.mem_ker, LinearMap.comp_apply] using hz
  · intro hx
    apply (Submodule.mem_iInf _).mpr
    intro j
    exact LinearMap.mem_ker.mpr (hx j j.isLt)

/-- Advancing the state by `B` consumes one vanishing derivative. -/
private theorem apply_mem_derivativeKernel (B : V →ₗ[ℝ] V) (C : V →ₗ[ℝ] W)
    {k : ℕ} {x : V} (hx : x ∈ derivativeKernel B C (k + 1)) :
    B x ∈ derivativeKernel B C k := by
  apply (mem_derivativeKernel B C k (B x)).mpr
  intro j hj
  have hz := (mem_derivativeKernel B C (k + 1) x).mp hx (j + 1)
    (Nat.succ_lt_succ hj)
  simpa only [pow_succ, Module.End.mul_apply] using hz

/-- The next kernel contributes zero to the order-`k` derivative. Hence
restricting to the orthogonal layer and dividing by `k!` preserve the range. -/
private theorem derivativeLayerOutput_range [FiniteDimensional ℝ V]
    (B : V →ₗ[ℝ] V) (C : V →ₗ[ℝ] W) (k : ℕ) :
    LinearMap.range (derivativeLayerOutput B C k) =
      (derivativeKernel B C k).map (C.comp (B ^ k)) := by
  have hfactor : (k.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  rw [derivativeLayerOutput, LinearMap.range_smul _ _ (inv_ne_zero hfactor),
    LinearMap.range_domRestrict]
  apply le_antisymm
  · intro y hy
    obtain ⟨x, hx, hxy⟩ := Submodule.mem_map.mp hy
    change x ∈ derivativeKernel B C k ⊓ (derivativeKernel B C (k + 1))ᗮ at hx
    exact Submodule.mem_map.mpr ⟨x, (Submodule.mem_inf.mp hx).1, hxy⟩
  · intro y hy
    obtain ⟨x, hx, hxy⟩ := Submodule.mem_map.mp hy
    have hnest : derivativeKernel B C (k + 1) ≤ derivativeKernel B C k := by
      intro z hz
      exact (mem_derivativeKernel B C k z).mpr fun j hj =>
        (mem_derivativeKernel B C (k + 1) z).mp hz j (hj.trans (Nat.lt_succ_self k))
    let : CompleteSpace (derivativeKernel B C (k + 1)) :=
      FiniteDimensional.complete ℝ _
    have hsplit :
        derivativeKernel B C (k + 1) ⊔ derivativeLayer B C k =
          derivativeKernel B C k := by
      simpa only [derivativeLayer, inf_comm] using
        (Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection hnest)
    have hx' : x ∈ derivativeKernel B C (k + 1) ⊔ derivativeLayer B C k := by
      rw [hsplit]
      exact hx
    obtain ⟨x₀, hx₀, x₁, hx₁, hsum⟩ := Submodule.mem_sup.mp hx'
    have hzero : C ((B ^ k) x₀) = 0 :=
      (mem_derivativeKernel B C (k + 1) x₀).mp hx₀ k (Nat.lt_succ_self k)
    refine Submodule.mem_map.mpr ⟨x₁, hx₁, ?_⟩
    calc
      (C.comp (B ^ k)) x₁ = (C.comp (B ^ k)) (x₀ + x₁) := by
        simp only [map_add, LinearMap.comp_apply, hzero, zero_add]
      _ = y := by rw [hsum, hxy]

/-- Every later derivative-layer range lies in each earlier one. -/
private theorem derivativeLayerOutput_range_antitone [FiniteDimensional ℝ V]
    (B : V →ₗ[ℝ] V) (C : V →ₗ[ℝ] W) :
    Antitone (fun k => LinearMap.range (derivativeLayerOutput B C k)) := by
  apply antitone_nat_of_succ_le
  intro k y hy
  rw [derivativeLayerOutput_range B C (k + 1)] at hy
  rw [derivativeLayerOutput_range B C k]
  obtain ⟨x, hx, hxy⟩ := Submodule.mem_map.mp hy
  refine Submodule.mem_map.mpr ⟨B x, apply_mem_derivativeKernel B C hx, ?_⟩
  simpa only [LinearMap.comp_apply, pow_succ, Module.End.mul_apply] using hxy

end Filtration

section ShiftedLegendre

private def legendreR (k : ℕ) : ℝ[X] :=
  (Polynomial.shiftedLegendre k).map (Int.castRingHom ℝ)

private def legendreLead (k : ℕ) : ℝ :=
  (-1 : ℝ) ^ k * ((2 * k).choose k : ℝ)

/-- The shifted Legendre polynomial divided by its signed leading coefficient. -/
def monicShiftedLegendre (k : ℕ) : ℝ[X] :=
  Polynomial.C ((legendreLead k)⁻¹) * legendreR k

/-- The squared unit-interval norm of the monic shifted Legendre polynomial. -/
def schurFactor (k : ℕ) : ℝ :=
  1 / ((2 * (k : ℝ) + 1) * ((2 * k).choose k : ℝ) ^ 2)

private theorem legendreLead_ne_zero (k : ℕ) : legendreLead k ≠ 0 := by
  have hchoose : 0 < (2 * k).choose k := Nat.choose_pos (by omega)
  have hcast : 0 < ((2 * k).choose k : ℝ) := by exact_mod_cast hchoose
  exact mul_ne_zero (pow_ne_zero _ (by norm_num)) hcast.ne'

private theorem legendreLead_sq (k : ℕ) :
    legendreLead k ^ 2 = ((2 * k).choose k : ℝ) ^ 2 := by
  have hsign : ((-1 : ℝ) ^ k) ^ 2 = 1 := by
    rw [pow_two, ← mul_pow]
    norm_num
  rw [legendreLead, mul_pow, hsign, one_mul]

private theorem legendreR_map (k : ℕ) :
    (legendreR k).map Complex.ofRealHom = PolynomialL2Derivative.legendreC k := by
  have hcast : Complex.ofRealHom.comp (Int.castRingHom ℝ) = Int.castRingHom ℂ := by
    ext n
    simp
  rw [legendreR, Polynomial.map_map, hcast, PolynomialL2Derivative.legendreC]

private theorem coeff_legendreC_top (k : ℕ) :
    (PolynomialL2Derivative.legendreC k).coeff k = (legendreLead k : ℂ) := by
  simp [PolynomialL2Derivative.coeff_legendreC, legendreLead, two_mul]

private theorem legendreR_natDegree_le (k : ℕ) : (legendreR k).natDegree ≤ k := by
  calc
    (legendreR k).natDegree ≤ (Polynomial.shiftedLegendre k).natDegree :=
      Polynomial.natDegree_map_le
    _ = k := Polynomial.natDegree_shiftedLegendre k

private theorem monicShiftedLegendre_natDegree_le (k : ℕ) :
    (monicShiftedLegendre k).natDegree ≤ k :=
  (Polynomial.natDegree_C_mul_le _ _).trans (legendreR_natDegree_le k)

private theorem monicShiftedLegendre_coeff_self (k : ℕ) :
    (monicShiftedLegendre k).coeff k = 1 := by
  have h := congrArg (fun p : ℂ[X] => p.coeff k) (legendreR_map k)
  have htop : (legendreR k).coeff k = legendreLead k := by
    apply Complex.ofReal_injective
    simpa only [Polynomial.coeff_map, Complex.ofRealHom_eq_coe, coeff_legendreC_top] using h
  rw [monicShiftedLegendre, Polynomial.coeff_C_mul, htop,
    inv_mul_cancel₀ (legendreLead_ne_zero k)]

/-- Normalize the existing Rodrigues top moment by the signed leading coefficient. -/
private theorem moment_legendreC_of_natDegree_le (k : ℕ) (q : ℂ[X])
    (hq : q.natDegree ≤ k) :
    PolynomialL2Derivative.moment (PolynomialL2Derivative.legendreC k) q =
      (q.coeff k / (legendreLead k : ℂ)) / (2 * (k : ℂ) + 1) := by
  have hchoose : ((2 * k).choose k : ℂ) * (k.factorial : ℂ) * (k.factorial : ℂ) =
      ((2 * k).factorial : ℂ) := by
    rw [two_mul]
    exact_mod_cast Nat.add_choose_mul_factorial_mul_factorial k k
  have hfactorial : ((2 * k + 1).factorial : ℂ) =
      (2 * (k : ℂ) + 1) * ((2 * k).choose k : ℂ) *
        ((k.factorial : ℂ) * (k.factorial : ℂ)) := by
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, ← hchoose]
    simp only [Nat.cast_mul, Nat.cast_ofNat, mul_assoc]
  have hfac : (k.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  have hbeta : (k.factorial : ℂ) * (k.factorial : ℂ) / ((2 * k + 1).factorial : ℂ) =
      1 / ((2 * (k : ℂ) + 1) * ((2 * k).choose k : ℂ)) := by
    rw [hfactorial]
    simpa only [one_mul] using mul_div_mul_right (1 : ℂ) _ (mul_ne_zero hfac hfac)
  rw [PolynomialL2Derivative.moment_legendreC_top k q hq, PolynomialL2Derivative.integral_rod,
    hbeta]
  simp [legendreLead, div_eq_mul_inv, mul_inv_rev, ← inv_pow, mul_assoc, mul_left_comm, mul_comm]

private theorem integral_legendreR_mul (k : ℕ) (q : ℝ[X]) (hq : q.natDegree ≤ k) :
    (∫ s : ℝ in 0..1, (legendreR k).eval s * q.eval s) =
      q.coeff k / legendreLead k / (2 * (k : ℝ) + 1) := by
  have htransport :
      ((∫ s : ℝ in 0..1, (legendreR k).eval s * q.eval s : ℝ) : ℂ) =
        PolynomialL2Derivative.moment (PolynomialL2Derivative.legendreC k)
          (q.map Complex.ofRealHom) := by
    rw [← intervalIntegral.integral_ofReal, PolynomialL2Derivative.moment,
      ← legendreR_map]
    apply intervalIntegral.integral_congr
    intro s _
    have hleft := Polynomial.eval_map_apply (p := legendreR k) Complex.ofRealHom s
    have hright := Polynomial.eval_map_apply (p := q) Complex.ofRealHom s
    simp only [Complex.ofRealHom_eq_coe] at hleft hright
    simp only [Complex.ofReal_mul, hleft, hright]
  have hdegree : (q.map Complex.ofRealHom).natDegree ≤ k :=
    Polynomial.natDegree_map_le.trans hq
  apply Complex.ofReal_injective
  rw [htransport, moment_legendreC_of_natDegree_le k _ hdegree]
  simp only [Polynomial.coeff_map, Complex.ofRealHom_eq_coe, Complex.ofReal_div,
    Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_natCast,
    Complex.ofReal_one]

/-- The monic residual pairs with a degree-at-most-`k` polynomial through
its coefficient of degree `k` alone. -/
private theorem integral_monicShiftedLegendre_mul (k : ℕ) (q : ℝ[X]) (hq : q.natDegree ≤ k) :
    (∫ s : ℝ in 0..1, (monicShiftedLegendre k).eval s * q.eval s) =
      schurFactor k * q.coeff k := by
  calc
    _ = (legendreLead k)⁻¹ * (∫ s : ℝ in 0..1, (legendreR k).eval s * q.eval s) := by
      simp only [monicShiftedLegendre, Polynomial.eval_mul, Polynomial.eval_C,
        mul_assoc, intervalIntegral.integral_const_mul]
    _ = q.coeff k / ((2 * (k : ℝ) + 1) * legendreLead k ^ 2) := by
      rw [integral_legendreR_mul k q hq]
      have hweight : (2 * (k : ℝ) + 1) ≠ 0 := by positivity
      field_simp [legendreLead_ne_zero k, hweight]
    _ = schurFactor k * q.coeff k := by
      rw [legendreLead_sq, schurFactor]
      ring

private theorem integral_monicShiftedLegendre_mul_pow (k i : ℕ) (hi : i < k) :
    (∫ s : ℝ in 0..1, (monicShiftedLegendre k).eval s * s ^ i) = 0 := by
  have h := integral_monicShiftedLegendre_mul k (Polynomial.X ^ i)
    ((Polynomial.natDegree_X_pow_le i).trans hi.le)
  rw [Polynomial.coeff_X_pow, ite_eq_right hi.ne.symm, mul_zero] at h
  simpa only [Polynomial.eval_pow, Polynomial.eval_X] using h

private theorem integral_monicShiftedLegendre_sq (k : ℕ) :
    (∫ s : ℝ in 0..1, ((monicShiftedLegendre k).eval s) ^ 2) = schurFactor k := by
  simpa only [pow_two, monicShiftedLegendre_coeff_self, mul_one] using
    integral_monicShiftedLegendre_mul k (monicShiftedLegendre k)
      (monicShiftedLegendre_natDegree_le k)

private theorem monicShiftedLegendre_eval (k : ℕ) (s : ℝ) :
    (monicShiftedLegendre k).eval s =
      s ^ k + ∑ i : Fin k, s ^ (i : ℕ) * (monicShiftedLegendre k).coeff (i : ℕ) := by
  have h := Polynomial.eval_eq_sum_range' (n := k + 1)
    (Nat.lt_succ_of_le (monicShiftedLegendre_natDegree_le k)) s
  rw [Finset.sum_range_succ, monicShiftedLegendre_coeff_self, one_mul] at h
  calc
    _ = (∑ i ∈ Finset.range k, (monicShiftedLegendre k).coeff i * s ^ i) + s ^ k := h
    _ = _ := by
      rw [Fin.sum_univ_eq_sum_range (fun i => s ^ i * (monicShiftedLegendre k).coeff i)]
      simp only [mul_comm, add_comm]

end ShiftedLegendre

section Minimum

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]

/-- Evaluate a vector polynomial with coefficients indexed by the degrees below `k`. -/
def lowerProfile (k : ℕ) (a : Fin k → W) (s : ℝ) : W :=
  ∑ i : Fin k, s ^ (i : ℕ) • a i

private theorem continuous_lowerProfile (k : ℕ) (a : Fin k → W) :
    Continuous (lowerProfile k a) :=
  continuous_finsetSum _ fun i _ => (continuous_id.pow (i : ℕ)).smul continuous_const

private theorem integral_inner_monic_lower (k : ℕ) (v : W) (a : Fin k → W) :
    (∫ s : ℝ in 0..1, ⟪(monicShiftedLegendre k).eval s • v, lowerProfile k a s⟫_ℝ) = 0 := by
  calc
    _ = ∫ s : ℝ in 0..1,
        ∑ i : Fin k, ((monicShiftedLegendre k).eval s * s ^ (i : ℕ)) * ⟪v, a i⟫_ℝ := by
      apply intervalIntegral.integral_congr
      intro s _
      simp only [lowerProfile, inner_sum, real_inner_smul_left, real_inner_smul_right,
        mul_assoc, mul_left_comm]
    _ = ∑ i : Fin k,
        ∫ s : ℝ in 0..1, ((monicShiftedLegendre k).eval s * s ^ (i : ℕ)) * ⟪v, a i⟫_ℝ :=
      intervalIntegral.integral_finsetSum fun i _ =>
        (((monicShiftedLegendre k).continuous.mul (continuous_id.pow (i : ℕ))).mul
          continuous_const).intervalIntegrable 0 1
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      rw [intervalIntegral.integral_mul_const,
        integral_monicShiftedLegendre_mul_pow k (i : ℕ) i.isLt, zero_mul]

private theorem integral_monicProfile_norm_sq (k : ℕ) (v : W) :
    (∫ s : ℝ in 0..1, ‖(monicShiftedLegendre k).eval s • v‖ ^ 2) =
      schurFactor k * ‖v‖ ^ 2 := by
  calc
    _ = ∫ s : ℝ in 0..1, ((monicShiftedLegendre k).eval s) ^ 2 * ‖v‖ ^ 2 := by
      apply intervalIntegral.integral_congr
      intro s _
      change ‖(monicShiftedLegendre k).eval s • v‖ ^ 2 =
        ((monicShiftedLegendre k).eval s) ^ 2 * ‖v‖ ^ 2
      rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    _ = _ := by
      rw [intervalIntegral.integral_mul_const, integral_monicShiftedLegendre_sq]

/-- The minimum squared distance to the earlier vector observation layers.
For each earlier degree, only membership of the leading vector in the
corresponding output range is required. -/
theorem filtered_polynomial_pivot_isLeast
    {X : ℕ → Type*} [∀ i, AddCommGroup (X i)] [∀ i, Module ℝ (X i)]
    (D : ∀ i, X i →ₗ[ℝ] W) (k : ℕ) (v : W)
    (hv : ∀ i : ℕ, i < k → v ∈ LinearMap.range (D i)) :
    IsLeast
      (Set.range (fun a : ∀ i : Fin k, X (i : ℕ) =>
        ∫ s : ℝ in 0..1, ‖s ^ k • v - lowerProfile k (fun i => D (i : ℕ) (a i)) s‖ ^ 2))
      (schurFactor k * ‖v‖ ^ 2) := by
  classical
  let cost (a : ∀ i : Fin k, X (i : ℕ)) : ℝ :=
    ∫ s : ℝ in 0..1, ‖s ^ k • v - lowerProfile k (fun i => D (i : ℕ) (a i)) s‖ ^ 2
  change IsLeast (Set.range cost) _
  let residual (s : ℝ) : W := (monicShiftedLegendre k).eval s • v
  let discrepancy (a : ∀ i : Fin k, X (i : ℕ)) : Fin k → W :=
    fun i => (monicShiftedLegendre k).coeff (i : ℕ) • v + D (i : ℕ) (a i)
  have hsplit (a : ∀ i : Fin k, X (i : ℕ)) (s : ℝ) :
      s ^ k • v - lowerProfile k (fun i => D (i : ℕ) (a i)) s =
        residual s - lowerProfile k (discrepancy a) s := by
    simp only [residual, monicShiftedLegendre_eval, discrepancy, lowerProfile, add_smul,
      Finset.sum_smul, smul_add, Finset.sum_add_distrib, smul_smul]
    abel
  have hres : Continuous residual :=
    (monicShiftedLegendre k).continuous.smul continuous_const
  have henergy (a : ∀ i : Fin k, X (i : ℕ)) :
      cost a = schurFactor k * ‖v‖ ^ 2 +
        ∫ s : ℝ in 0..1, ‖lowerProfile k (discrepancy a) s‖ ^ 2 := by
    let g := lowerProfile k (discrepancy a)
    have hg : Continuous g := continuous_lowerProfile k (discrepancy a)
    have hres_sq : Continuous (fun s : ℝ => ‖residual s‖ ^ 2) := hres.norm.pow 2
    have hg_sq : Continuous (fun s : ℝ => ‖g s‖ ^ 2) := hg.norm.pow 2
    have hcross : Continuous (fun s : ℝ => 2 * ⟪residual s, g s⟫_ℝ) :=
      continuous_const.mul (Continuous.inner (𝕜 := ℝ) hres hg)
    have horth : (∫ s : ℝ in 0..1, ⟪residual s, g s⟫_ℝ) = 0 :=
      integral_inner_monic_lower k v (discrepancy a)
    have hcross_zero : (∫ s : ℝ in 0..1, 2 * ⟪residual s, g s⟫_ℝ) = 0 := by
      rw [intervalIntegral.integral_const_mul, horth, mul_zero]
    have hres_energy : (∫ s : ℝ in 0..1, ‖residual s‖ ^ 2) = schurFactor k * ‖v‖ ^ 2 :=
      integral_monicProfile_norm_sq k v
    change cost a = schurFactor k * ‖v‖ ^ 2 + ∫ s : ℝ in 0..1, ‖g s‖ ^ 2
    calc
      cost a = ∫ s : ℝ in 0..1,
          (‖residual s‖ ^ 2 - 2 * ⟪residual s, g s⟫_ℝ) + ‖g s‖ ^ 2 := by
        apply intervalIntegral.integral_congr
        intro s _
        exact (congrArg (fun z : W => ‖z‖ ^ 2) (hsplit a s)).trans (norm_sub_sq_real _ _)
      _ = _ := by
        have hdiff : IntervalIntegrable (fun s : ℝ =>
            ‖residual s‖ ^ 2 - 2 * ⟪residual s, g s⟫_ℝ) volume 0 1 :=
          (hres_sq.sub hcross).intervalIntegrable 0 1
        rw [intervalIntegral.integral_add hdiff (hg_sq.intervalIntegrable 0 1),
          intervalIntegral.integral_sub (hres_sq.intervalIntegrable 0 1)
            (hcross.intervalIntegrable 0 1),
          hres_energy, hcross_zero, sub_zero]
  constructor
  · have hlift (i : Fin k) :
        ∃ x : X (i : ℕ), D (i : ℕ) x = -((monicShiftedLegendre k).coeff (i : ℕ) • v) := by
      exact LinearMap.mem_range.mp
        ((LinearMap.range (D (i : ℕ))).neg_mem
          ((LinearMap.range (D (i : ℕ))).smul_mem _ (hv (i : ℕ) i.isLt)))
    choose a ha using hlift
    refine ⟨a, ?_⟩
    rw [henergy a]
    simp only [lowerProfile, discrepancy, ha, add_neg_cancel, smul_zero, Finset.sum_const_zero,
      norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), intervalIntegral.integral_zero, add_zero]
  · rintro _ ⟨a, rfl⟩
    rw [henergy a]
    exact le_add_of_nonneg_right
      (intervalIntegral.integral_nonneg_of_forall (by norm_num : (0 : ℝ) ≤ 1)
        (fun s => sq_nonneg ‖lowerProfile k (discrepancy a) s‖))

/-- The exact variational Schur coefficient on a state of the actual
derivative layer. The same statement includes empty and repeated ranges. -/
theorem derivative_layer_pivot_isLeast
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (B : V →ₗ[ℝ] V) (C : V →ₗ[ℝ] W) (k : ℕ) (x : derivativeLayer B C k) :
    IsLeast
      (Set.range (fun a : ∀ i : Fin k, derivativeLayer B C (i : ℕ) =>
        ∫ s : ℝ in 0..1, ‖s ^ k • derivativeLayerOutput B C k x -
          lowerProfile k (fun i => derivativeLayerOutput B C (i : ℕ) (a i)) s‖ ^ 2))
      (schurFactor k * ‖derivativeLayerOutput B C k x‖ ^ 2) :=
  filtered_polynomial_pivot_isLeast (derivativeLayerOutput B C) k
    (derivativeLayerOutput B C k x) fun _ hi =>
      derivativeLayerOutput_range_antitone B C hi.le
        (LinearMap.mem_range_self (derivativeLayerOutput B C k) x)

end Minimum

end D5.S3.Observer.Linear.DerivativeLayerExactPivot
