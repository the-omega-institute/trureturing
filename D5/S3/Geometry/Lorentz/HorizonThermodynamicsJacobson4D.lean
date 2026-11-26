/- GID: D5/S3/Geometry/Lorentz/HorizonThermodynamicsJacobson4D
   generality: G
   mirror-B: D5/B/S3/Geometry/Lorentz/HorizonThermodynamicsJacobson4D
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Null-cone closure, flat-chart Bianchi recovery, sharp optical focusing, and stationary quantum focusing in four dimensions. -/

import OmegaBuild.Commands
import D5.S3.Geometry.Lorentz.WeylNullScreen
import D5.S3.Quantum.Dynamics.EntropyProductionCoherenceDeletionIdentity
import D5.S3.Quantum.Divergence.SpectralCeilingRelativeEntropy
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Tactic.LinearCombination

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Geometry.Lorentz.HorizonThermodynamicsJacobson4D

open Matrix Set Filter
open scoped Topology Matrix

abbrev Chart := Fin 4 → ℝ
abbrev Tensor := Matrix (Fin 4) (Fin 4) ℝ

/-- The Minkowski metric with the time coordinate first and timelike sign negative. -/
def eta (K : Type*) [Ring K] : Matrix (Fin 4) (Fin 4) K :=
  diagonal ![-1, 1, 1, 1]

/-- The trace with one index raised by the Minkowski metric. -/
def minkowskiTrace (R : Tensor) : ℝ := ∑ a, eta ℝ a a * R a a

/-- Flat-chart contracted derivative in the second tensor index. -/
def divergence (R : Chart → Tensor) (x : Chart) (b : Fin 4) : ℝ :=
  ∑ a, eta ℝ a a * fderiv ℝ (fun y => R y a b) x (Pi.single a 1)

private theorem eta_diag_sq (a : Fin 4) : eta ℝ a a ^ 2 = 1 := by
  fin_cases a <;> norm_num [eta]

private theorem eta_square_value {K : Type*} [CommRing K] (k : Fin 4 → K) :
    (∑ a, eta K a a * k a * k a) = WeylNullScreen.minkowski k k := by
  simp [eta, WeylNullScreen.minkowski, Fin.sum_univ_succ, add_assoc]

/-- Nine explicit null directions suffice to recover the metric multiple over any
characteristic-zero field. The three spatial pairs use the integer triple 3, 4, 5. -/
theorem symmetric_null_vanishing_iff_smul_eta {K : Type*} [Field K] [CharZero K]
    (S : Matrix (Fin 4) (Fin 4) K) (hs : Sᵀ = S) :
    (∀ k : Fin 4 → K, (∑ a, eta K a a * k a * k a) = 0 →
      (∑ a, ∑ b, k a * S a b * k b) = 0) ↔ ∃ c : K, S = c • eta K := by
  have symm (a b : Fin 4) : S b a = S a b := congrFun (congrFun hs a) b
  constructor
  · intro h
    have probe (k : Fin 4 → K) (hk : WeylNullScreen.minkowski k k = 0) :
        (∑ a, ∑ b, k a * S a b * k b) = 0 :=
      h k ((eta_square_value k).trans hk)
    have p01 := probe ![1, 1, 0, 0] (by norm_num [WeylNullScreen.minkowski])
    have m01 := probe ![1, -1, 0, 0] (by norm_num [WeylNullScreen.minkowski])
    have p02 := probe ![1, 0, 1, 0] (by norm_num [WeylNullScreen.minkowski])
    have m02 := probe ![1, 0, -1, 0] (by norm_num [WeylNullScreen.minkowski])
    have p03 := probe ![1, 0, 0, 1] (by norm_num [WeylNullScreen.minkowski])
    have m03 := probe ![1, 0, 0, -1] (by norm_num [WeylNullScreen.minkowski])
    norm_num [Fin.sum_univ_succ, symm 0 1, symm 0 2, symm 0 3] at p01 m01 p02 m02 p03 m03
    have four_ne : (4 : K) ≠ 0 := by norm_num
    have off01 : S 0 1 = 0 :=
      (mul_eq_zero.mp (show (4 : K) * S 0 1 = 0 by linear_combination p01 - m01)).resolve_left four_ne
    have off02 : S 0 2 = 0 :=
      (mul_eq_zero.mp (show (4 : K) * S 0 2 = 0 by linear_combination p02 - m02)).resolve_left four_ne
    have off03 : S 0 3 = 0 :=
      (mul_eq_zero.mp (show (4 : K) * S 0 3 = 0 by linear_combination p03 - m03)).resolve_left four_ne
    have diag1 : S 1 1 = -S 0 0 := by linear_combination p01 - 2 * off01
    have diag2 : S 2 2 = -S 0 0 := by linear_combination p02 - 2 * off02
    have diag3 : S 3 3 = -S 0 0 := by linear_combination p03 - 2 * off03
    have p12 := probe ![5, 3, 4, 0] (by norm_num [WeylNullScreen.minkowski])
    have p13 := probe ![5, 3, 0, 4] (by norm_num [WeylNullScreen.minkowski])
    have p23 := probe ![5, 0, 3, 4] (by norm_num [WeylNullScreen.minkowski])
    norm_num [Fin.sum_univ_succ, symm 0 1, symm 0 2, symm 0 3, symm 1 2, symm 1 3,
      symm 2 3, off01, off02, off03, diag1, diag2, diag3] at p12 p13 p23
    have coefficient_ne : (24 : K) ≠ 0 := by norm_num
    have off12 : S 1 2 = 0 :=
      (mul_eq_zero.mp (show (24 : K) * S 1 2 = 0 by linear_combination p12)).resolve_left coefficient_ne
    have off13 : S 1 3 = 0 :=
      (mul_eq_zero.mp (show (24 : K) * S 1 3 = 0 by linear_combination p13)).resolve_left coefficient_ne
    have off23 : S 2 3 = 0 :=
      (mul_eq_zero.mp (show (24 : K) * S 2 3 = 0 by linear_combination p23)).resolve_left coefficient_ne
    refine ⟨-S 0 0, Matrix.ext fun a b => ?_⟩
    fin_cases a <;> fin_cases b <;>
      norm_num [eta, Matrix.smul_apply, smul_eq_mul, diagonal_apply, diag1, diag2, diag3,
        symm 0 1, symm 0 2, symm 0 3, symm 1 2, symm 1 3, symm 2 3,
        off01, off02, off03, off12, off13, off23]
  · rintro ⟨c, rfl⟩ k hk
    simp only [Matrix.smul_apply, smul_eq_mul]
    calc
      _ = ∑ a, c * (∑ b, k a * (eta K a b * k b)) := by
        apply Finset.sum_congr rfl
        intro a _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro b _
        ring
      _ = c * (∑ a, eta K a a * k a * k a) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a _
        rw [← Finset.mul_sum]
        change c * (k a * ((eta K) *ᵥ k) a) = _
        simp only [eta, mulVec_diagonal, diagonal_apply_eq]
        ring
      _ = 0 := by rw [hk, mul_zero]

private theorem null_pairing (k : Chart) :
    k ⬝ᵥ (eta ℝ *ᵥ k) = WeylNullScreen.minkowski k k := by
  rw [← eta_square_value]
  unfold dotProduct
  simp_rw [eta, mulVec_diagonal, diagonal_apply_eq]
  apply Finset.sum_congr rfl
  intro a _
  ring

private theorem null_residual (S : Tensor) (hs : Sᵀ = S)
    (hnull : ∀ k : Chart, WeylNullScreen.minkowski k k = 0 → k ⬝ᵥ (S *ᵥ k) = 0) :
    S = (-S 0 0) • eta ℝ := by
  obtain ⟨c, hc⟩ := (symmetric_null_vanishing_iff_smul_eta S hs).mp (fun k hk => by
    have h := hnull k ((eta_square_value k).symm.trans hk)
    simpa only [dotProduct, mulVec, Finset.mul_sum, mul_assoc] using h)
  have h00 := congrFun (congrFun hc (0 : Fin 4)) (0 : Fin 4)
  have hf : -S 0 0 = c := by
    simp [eta, Matrix.smul_apply, smul_eq_mul] at h00
    rw [h00, neg_neg]
  rw [hf, hc]

private theorem trace_differentiable {R : Chart → Tensor} {x : Chart}
    (hR : ∀ a b, DifferentiableAt ℝ (fun y => R y a b) x) :
    DifferentiableAt ℝ (fun y => minkowskiTrace (R y)) x := by
  exact DifferentiableAt.fun_sum fun a _ => (hR a a).const_mul _

/-- The contracted divergence of a scalar metric multiple is its derivative
in the corresponding coordinate direction. -/
private theorem divergence_smul_eta {f : Chart → ℝ} {x : Chart}
    (hf : DifferentiableAt ℝ f x) (b : Fin 4) :
    divergence (fun y => f y • eta ℝ) x b = fderiv ℝ f x (Pi.single b 1) := by
  unfold divergence
  rw [Finset.sum_eq_single b]
  · simp only [Matrix.smul_apply, smul_eq_mul, fderiv_mul_const hf,
      _root_.smul_apply, smul_eq_mul]
    calc
      _ = eta ℝ b b ^ 2 * fderiv ℝ f x (Pi.single b 1) := by ring
      _ = _ := by rw [eta_diag_sq, one_mul]
  · intro a _ hab
    have hz : eta ℝ a b = 0 := diagonal_apply_ne _ hab
    simp [Matrix.smul_apply, hz]
  · simp

/-- The null relation determines the metric multiple pointwise. Contracted
Bianchi and conservation make its trace-corrected scalar constant on the domain. -/
theorem jacobson_bianchi_einstein_equation
    (U : Set Chart) (hU : IsOpen U) (hconn : IsPreconnected U)
    (R T : Chart → Tensor) (κ : ℝ)
    (hR : ∀ x ∈ U, ∀ a b, DifferentiableAt ℝ (fun y => R y a b) x)
    (hT : ∀ x ∈ U, ∀ a b, DifferentiableAt ℝ (fun y => T y a b) x)
    (hsR : ∀ x ∈ U, (R x)ᵀ = R x) (hsT : ∀ x ∈ U, (T x)ᵀ = T x)
    (hnull : ∀ x ∈ U, ∀ k : Chart, WeylNullScreen.minkowski k k = 0 →
      k ⬝ᵥ ((R x - κ • T x) *ᵥ k) = 0)
    (hBianchi : ∀ x ∈ U, ∀ b,
      divergence (fun y => R y - (minkowskiTrace (R y) / 2) • eta ℝ) x b = 0)
    (hConservation : ∀ x ∈ U, ∀ b, divergence T x b = 0) :
    let φ : Chart → ℝ := fun x => (R x - κ • T x) 0 0
    (∀ x ∈ U, HasFDerivAt (fun y => φ y + minkowskiTrace (R y) / 2) (0 : Chart →L[ℝ] ℝ) x) ∧
      ∃ Λ : ℝ, ∀ x ∈ U, R x - (minkowskiTrace (R x) / 2) • eta ℝ + Λ • eta ℝ = κ • T x := by
  let φ : Chart → ℝ := fun x => (R x - κ • T x) 0 0
  have residual (x : Chart) (hx : x ∈ U) : R x - κ • T x = (-φ x) • eta ℝ := by
    apply null_residual
    · rw [transpose_sub, transpose_smul, hsR x hx, hsT x hx]
    · exact hnull x hx
  let g : Chart → ℝ := fun x => -φ x - minkowskiTrace (R x) / 2
  have hg (x : Chart) (hx : x ∈ U) : DifferentiableAt ℝ g x := by
    have htrace := trace_differentiable (R := R) (x := x) (hR x hx)
    have hhalf : DifferentiableAt ℝ (fun y : Chart => minkowskiTrace (R y) / 2) x := by
      simpa only [div_eq_mul_inv] using htrace.mul_const ((2 : ℝ)⁻¹)
    exact (((hR x hx 0 0).sub ((hT x hx 0 0).const_mul κ)).neg).sub hhalf
  have split (x : Chart) (hx : x ∈ U) :
      R x - (minkowskiTrace (R x) / 2) • eta ℝ = κ • T x + g x • eta ℝ := by
    calc
      _ = κ • T x + ((R x - κ • T x) - (minkowskiTrace (R x) / 2) • eta ℝ) := by abel
      _ = _ := by rw [residual x hx, show g x = -φ x - minkowskiTrace (R x) / 2 by rfl, sub_smul]
  have zeroDerivative (x : Chart) (hx : x ∈ U) : HasFDerivAt g (0 : Chart →L[ℝ] ℝ) x := by
    have hcoord (b : Fin 4) : fderiv ℝ g x (Pi.single b 1) = 0 := by
      have hSum : divergence (fun y => κ • T y + g y • eta ℝ) x b =
          κ * divergence T x b + divergence (fun y => g y • eta ℝ) x b := by
        unfold divergence
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro a _
        have hT' := (hT x hx a b).hasFDerivAt.const_mul κ
        have hg' := (hg x hx).hasFDerivAt.mul_const (eta ℝ a b)
        have hpair := (hT'.add hg').fderiv
        change fderiv ℝ (fun y => κ * T y a b + g y * eta ℝ a b) x = _ at hpair
        simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
        rw [hpair, fderiv_mul_const (hg x hx)]
        simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
        ring
      have hEq : divergence (fun y => R y - (minkowskiTrace (R y) / 2) • eta ℝ) x b =
          divergence (fun y => κ • T y + g y • eta ℝ) x b := by
        unfold divergence
        apply Finset.sum_congr rfl
        intro a _
        have hNear : ∀ᶠ y in 𝓝 x, y ∈ U := hU.mem_nhds hx
        have hEntry : (fun y => (R y - (minkowskiTrace (R y) / 2) • eta ℝ) a b)
            =ᶠ[𝓝 x] (fun y => (κ • T y + g y • eta ℝ) a b) := by
          filter_upwards [hNear] with y hy
          exact congrFun (congrFun (split y hy) a) b
        rw [hEntry.fderiv_eq]
      rw [hSum, hConservation x hx b, mul_zero, zero_add, divergence_smul_eta (hg x hx)] at hEq
      exact hEq.symm.trans (hBianchi x hx b)
    have hzero : fderiv ℝ g x = 0 := by
      ext v
      rw [← Finset.univ_sum_single v, map_sum]
      have hsingle (b : Fin 4) : Pi.single b (v b) = v b • (Pi.single b 1 : Chart) := by
        ext a
        by_cases h : a = b <;> simp [h]
      simp_rw [hsingle, map_smul, hcoord, smul_zero, Finset.sum_const_zero,
        _root_.zero_apply]
    simpa only [hzero] using (hg x hx).hasFDerivAt
  obtain ⟨c, hc⟩ := hU.exists_is_const_of_fderiv_eq_zero hconn
    (fun x hx => (zeroDerivative x hx).differentiableAt.differentiableWithinAt)
    (fun x hx => (zeroDerivative x hx).fderiv)
  refine ⟨?_, -c, fun x hx => ?_⟩
  · intro x hx
    convert (zeroDerivative x hx).neg using 1
    · funext y
      change φ y + minkowskiTrace (R y) / 2 = -(-φ y - minkowskiTrace (R y) / 2)
      ring
    · simp
  · rw [split x hx, hc x hx, neg_smul]
    abel

/-- Constant vacuum Ricci fields realize arbitrary and distinct cosmological constants. -/
theorem cosmological_constant_indeterminacy_counterexample
    (κ Λ₁ Λ₂ : ℝ) (hne : Λ₁ ≠ Λ₂) :
    let R : ℝ → Chart → Tensor := fun Λ _ => Λ • eta ℝ
    let T : Chart → Tensor := fun _ => 0
    (∀ Λ x k, WeylNullScreen.minkowski k k = 0 → k ⬝ᵥ ((R Λ x - κ • T x) *ᵥ k) = 0) ∧
    (∀ Λ x b, divergence (fun y => R Λ y - (minkowskiTrace (R Λ y) / 2) • eta ℝ) x b = 0) ∧
    (∀ x b, divergence T x b = 0) ∧
    (∀ Λ x, R Λ x - (minkowskiTrace (R Λ x) / 2) • eta ℝ + Λ • eta ℝ = 0) ∧
    R Λ₁ ≠ R Λ₂ := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro Λ x k hk
    rw [smul_zero, sub_zero, Matrix.smul_mulVec, dotProduct_smul, null_pairing, hk, smul_zero]
  · intro Λ x b
    simp [divergence]
  · intro x b
    simp [divergence]
  · intro Λ x
    have htrace : minkowskiTrace (Λ • eta ℝ) = 4 * Λ := by
      simp only [minkowskiTrace, Matrix.smul_apply, smul_eq_mul,
        show ∀ a : Fin 4, eta ℝ a a * (Λ * eta ℝ a a) = Λ by
          intro a
          linear_combination Λ * eta_diag_sq a]
      simp
    rw [htrace, show 4 * Λ / 2 = Λ + Λ by ring, add_smul]
    abel
  · intro h
    have h00 := congrFun (congrFun (congrFun h (0 : Chart)) (0 : Fin 4)) (0 : Fin 4)
    exact hne (by simpa [eta, Matrix.smul_apply, smul_eq_mul] using h00)

/-- The null Ricci and shear terms each reinforce focusing. Nonzero shear gives
strict focusing beyond the expansion term, including at vanishing Ricci flux. -/
theorem raychaudhuri_monotonic_focusing
    (θ : ℝ → ℝ) (σ : ℝ → ℂ) (Φ : ℝ → ℝ) (t : ℝ)
    (hθ : HasDerivAt θ (-(θ t)^2 / 2 - ‖σ t‖^2 - Φ t) t)
    (hNEC : 0 ≤ Φ t) :
    deriv θ t ≤ -(θ t)^2 / 2 ∧ -(θ t)^2 / 2 ≤ 0 ∧
      (σ t ≠ 0 → deriv θ t < -(θ t)^2 / 2) := by
  rw [hθ.deriv]
  have hshear := sq_nonneg ‖σ t‖
  refine ⟨by linarith, by nlinarith, fun hσ => ?_⟩
  have hpositive : 0 < ‖σ t‖^2 := pow_pos (norm_pos_iff.mpr hσ) _
  linarith

/-- Reciprocal comparison gives the sharp upper endpoint for every closed interval
of a finite, initially converging solution to the focusing inequality. -/
theorem hawking_penrose_caustic_bound
    (θ : ℝ → ℝ) (L : ℝ) (hL : 0 ≤ L) (hinit : θ 0 < 0)
    (hcont : ContinuousOn θ (Icc 0 L)) (hdiff : DifferentiableOn ℝ θ (Ioo 0 L))
    (hfocus : ∀ t ∈ Ioo 0 L, deriv θ t ≤ -(θ t)^2 / 2) :
    (∀ t ∈ Icc 0 L, θ t < 0 ∧ t / 2 ≤ 1 / θ t - 1 / θ 0 ∧
      θ t ≤ θ 0 / (1 + (θ 0 / 2) * t)) ∧ L < -2 / θ 0 := by
  have hanti : AntitoneOn θ (Icc 0 L) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 L) hcont
    · simpa only [interior_Icc] using hdiff
    · intro t ht
      rw [interior_Icc] at ht
      have := hfocus t ht
      nlinarith [sq_nonneg (θ t)]
  have hzero : (0 : ℝ) ∈ Icc 0 L := ⟨le_rfl, hL⟩
  have hneg (t : ℝ) (ht : t ∈ Icc 0 L) : θ t < 0 :=
    (hanti hzero ht ht.1).trans_lt hinit
  let f : ℝ → ℝ := fun t => (θ t)⁻¹ - t / 2
  have hfcont : ContinuousOn f (Icc 0 L) :=
    (hcont.inv₀ fun t ht => (hneg t ht).ne).sub (continuous_id.div_const 2).continuousOn
  have hfd (t : ℝ) (ht : t ∈ Ioo 0 L) :
      HasDerivAt f (-(deriv θ t) / (θ t)^2 - 1 / 2) t := by
    have hd := ((hdiff t ht).differentiableAt (isOpen_Ioo.mem_nhds ht)).hasDerivAt
    exact (hd.inv (hneg t (Ioo_subset_Icc_self ht)).ne).sub ((hasDerivAt_id t).div_const 2)
  have hfmono : MonotoneOn f (Icc 0 L) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 L) hfcont
    · rw [interior_Icc]
      exact fun t ht => (hfd t ht).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hfd t ht).deriv, sub_nonneg, le_div_iff₀ (sq_pos_of_ne_zero
        (hneg t (Ioo_subset_Icc_self ht)).ne)]
      linarith [hfocus t ht]
  have hrecip (t : ℝ) (ht : t ∈ Icc 0 L) : t / 2 ≤ 1 / θ t - 1 / θ 0 := by
    have h := hfmono hzero ht ht.1
    dsimp [f] at h
    simpa only [one_div] using (show t / 2 ≤ (θ t)⁻¹ - (θ 0)⁻¹ by linarith)
  have hbound : L < -2 / θ 0 := by
    have h := hrecip L ⟨hL, le_rfl⟩
    have hnegative := one_div_neg.mpr (hneg L ⟨hL, le_rfl⟩)
    rw [show -2 / θ 0 = -2 * (1 / θ 0) by ring]
    linarith
  refine ⟨fun t ht => ⟨hneg t ht, hrecip t ht, ?_⟩, hbound⟩
  have hdenom : 0 < 1 + (θ 0 / 2) * t := by
    have htop := ht.2.trans_lt hbound
    have hm := (lt_div_iff_of_neg hinit).mp htop
    nlinarith
  rw [le_div_iff₀ hdenom]
  have htneg := hneg t ht
  have hleft := (div_le_iff_of_neg hinit).mp (show 1 / θ 0 ≤ 1 / θ t - t / 2 by
    linarith [hrecip t ht])
  have hright := mul_le_mul_of_nonpos_right hleft htneg.le
  have hcancel : (1 / θ t) * θ t = 1 := by field_simp [htneg.ne]
  nlinarith

/-- The exact negative solution saturates reciprocal comparison at all times
before its pole. Its pole agrees with the ceiling computed from the initial value. -/
theorem hawking_penrose_caustic_sharpness (T : ℝ) (hT : 0 < T) :
    let θ : ℝ → ℝ := fun t => -2 / (T - t)
    θ 0 < 0 ∧ T = -2 / θ 0 ∧
      ∀ t < T, HasDerivAt θ (-(θ t)^2 / 2) t ∧
        1 / θ t - 1 / θ 0 = t / 2 := by
  dsimp only
  have hAtZero : T - 0 = T := sub_zero T
  rw [hAtZero]
  refine ⟨div_neg_of_neg_of_pos (by norm_num) hT, ?_, fun t ht => ?_⟩
  · field_simp
  · have hne : T - t ≠ 0 := (sub_pos.mpr ht).ne'
    have hd := ((hasDerivAt_const t T).sub (hasDerivAt_id t)).inv hne
    refine ⟨?_, by field_simp; ring⟩
    convert hd.const_mul (-2 : ℝ) using 1
    · funext x
      simp [div_eq_mul_inv, Pi.inv_apply, Pi.sub_apply]
    · simp only [Pi.sub_apply, id_eq]
      field_simp
      ring

/-- On an open stationary interval, Raychaudhuri first removes Ricci flux
and shear. The Sachs equation then removes the Weyl component driving that shear. -/
theorem stationary_horizon_shear_weyl_rigidity
    (a b : ℝ) (θ Φ : ℝ → ℝ) (σ Ψ : ℝ → ℂ)
    (hθ : ∀ t ∈ Ioo a b, HasDerivAt θ (-(θ t)^2 / 2 - ‖σ t‖^2 - Φ t) t)
    (hσ : ∀ t ∈ Ioo a b, HasDerivAt σ (-(θ t : ℂ) * σ t - Ψ t) t)
    (hNEC : ∀ t ∈ Ioo a b, 0 ≤ Φ t)
    (hstationary : ∀ t ∈ Ioo a b, θ t = 0) :
    ∀ t ∈ Ioo a b, Φ t = 0 ∧ σ t = 0 ∧ Ψ t = 0 := by
  have stationary (t : ℝ) (ht : t ∈ Ioo a b) : Φ t = 0 ∧ σ t = 0 := by
    have hNear : θ =ᶠ[𝓝 t] (fun _ => 0) := by
      filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
      exact hstationary s hs
    have hzero := (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq hNear
    have hshear : σ t = 0 := by
      by_contra hne
      have hstrict := (raychaudhuri_monotonic_focusing θ σ Φ t (hθ t ht) (hNEC t ht)).2.2 hne
      simpa [hzero.deriv, hstationary t ht] using hstrict
    have hEq := (hθ t ht).unique hzero
    exact ⟨by simpa [hstationary t ht, hshear] using hEq, hshear⟩
  intro t ht
  have hNear : σ =ᶠ[𝓝 t] (fun _ => 0) := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
    exact (stationary s hs).2
  have hEq := (hσ t ht).unique ((hasDerivAt_const t (0 : ℂ)).congr_of_eventuallyEq hNear)
  exact ⟨(stationary t ht).1, (stationary t ht).2, by simpa [hstationary t ht] using hEq⟩

/-- At zero expansion and shear, the area law and Raychaudhuri give the exact
second generalized-entropy variation and its affine-generator energy threshold. -/
theorem qfc_iff_qnec_at_stationary_horizon
    (G t₀ : ℝ) (hG : 0 < G) (A θ Φ S S' : ℝ → ℝ) (σ : ℝ → ℂ) (S'' : ℝ)
    (hA : 0 < A t₀)
    (hArea : ∀ᶠ t in 𝓝 t₀, HasDerivAt A (θ t * A t) t)
    (hEntropy : ∀ᶠ t in 𝓝 t₀, HasDerivAt S (S' t) t)
    (hEntropy' : HasDerivAt S' S'' t₀)
    (hRay : HasDerivAt θ (-(θ t₀)^2 / 2 - ‖σ t₀‖^2 - Φ t₀) t₀)
    (hθ : θ t₀ = 0) (hσ : σ t₀ = 0) :
    let Sgen : ℝ → ℝ := fun t => A t / (4 * G) + S t
    let Sgen' : ℝ → ℝ := fun t => (θ t * A t) / (4 * G) + S' t
    (∀ᶠ t in 𝓝 t₀, HasDerivAt Sgen (Sgen' t) t) ∧
    HasDerivAt Sgen' (-(A t₀ / (4 * G)) * Φ t₀ + S'') t₀ ∧
    ((-(A t₀ / (4 * G)) * Φ t₀ + S'') ≤ 0 ↔ (4 * G / A t₀) * S'' ≤ Φ t₀) ∧
    (∀ Tkk, Φ t₀ = 8 * Real.pi * G * Tkk →
      ((-(A t₀ / (4 * G)) * Φ t₀ + S'') ≤ 0 ↔
        S'' / (2 * Real.pi * A t₀) ≤ Tkk)) := by
  dsimp only
  have hG' : 0 < 4 * G := by positivity
  have hThreshold : (-(A t₀ / (4 * G)) * Φ t₀ + S'') ≤ 0 ↔ (4 * G / A t₀) * S'' ≤ Φ t₀ := by
    rw [show (4 * G / A t₀) * S'' = (4 * G * S'') / A t₀ by ring, div_le_iff₀ hA]
    have hRewrite : (A t₀ / (4 * G)) * Φ t₀ = (Φ t₀ * A t₀) / (4 * G) := by ring
    rw [neg_mul, hRewrite, neg_add_eq_sub, sub_nonpos, le_div_iff₀ hG']
    simp [mul_comm]
  refine ⟨?_, ?_, hThreshold, ?_⟩
  · filter_upwards [hArea, hEntropy] with t hAt hSt
    exact (hAt.div_const (4 * G)).add hSt
  · have hDer := (((hRay.mul hArea.self_of_nhds).div_const (4 * G))).add hEntropy'
    convert hDer using 1
    simp [hθ, hσ]
    ring
  · intro Tkk hT
    have hnorm : 0 < 2 * Real.pi * A t₀ := by positivity [Real.pi_pos]
    rw [hThreshold, hT, show (4 * G / A t₀) * S'' = (4 * G * S'') / A t₀ by ring,
      div_le_iff₀ hA, div_le_iff₀ hnorm]
    constructor <;> intro h
    · have hh : (4 * G) * S'' ≤ (4 * G) * (Tkk * (2 * Real.pi * A t₀)) := by
        convert h using 1
        ring
      exact (mul_le_mul_iff_right₀ hG').mp hh
    · convert mul_le_mul_of_nonneg_left h hG'.le using 1
      ring

section Pinching

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open D5.S3.Quantum.Decoherence.ProjectedUnistochasticDynamics
open D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition
open D5.S3.Quantum.Divergence.SpectralCeilingRelativeEntropy
open D5.S3.Quantum.Divergence.VonNeumannEntropyPinching
open D5.S3.Quantum.Dynamics.EntropyProductionCoherenceDeletionIdentity
open D5.S3.Quantum.Dynamics.ProjectionProbabilityFlow

variable {n : Type*} [Fintype n] [DecidableEq n]

private theorem pinching_support (A : Matrix n n ℂ) (hA : A.PosSemidef)
    (v : n → ℂ) (hv : projectiveReadout A *ᵥ v = 0) : A *ᵥ v = 0 := by
  have hv' (j : n) : A j j * v j = 0 := by
    simpa [projectiveReadout, mulVec_diagonal] using congrFun hv j
  ext i
  unfold mulVec dotProduct
  apply Finset.sum_eq_zero
  intro j _
  rcases mul_eq_zero.mp (hv' j) with hdiag | hzero
  · have hstar : star (Pi.single j 1 : n → ℂ) = Pi.single j 1 := by
      ext k
      by_cases h : k = j <;> simp [Pi.star_apply, h]
    have hcol : A *ᵥ (Pi.single j 1 : n → ℂ) = 0 :=
      hA.dotProduct_mulVec_zero_iff.mp (by
        rw [hstar, single_one_dotProduct, mulVec_single_one]
        exact hdiag)
    have hEntry : A i j = 0 := by simpa [mulVec_single_one] using congrFun hcol i
    simp [hEntry]
  · simp [hzero]

/-- The Clausius area assignment for a record pinching is nonnegative
and is strictly positive exactly when the pinching changes the state. -/
theorem clausius_area_monotonicity_from_record_pinching (G : ℝ) (hG : 0 < G)
    (rho : DensityState n) :
    let P := basisPinchingState rho
    let A := densityMatrix rho
    let B := densityMatrix P
    let ΔA := 4 * G * (vonNeumannEntropy P - vonNeumannEntropy rho)
    ΔA = 4 * G * quantumRelativeEntropy rho P ∧ 0 ≤ ΔA ∧
      (∀ i j, i ≠ j → A i j ≠ 0 → 0 < ΔA) ∧
      (ΔA = 0 ↔ B = A) := by
  dsimp only
  let P := basisPinchingState rho
  let A := densityMatrix rho
  let B := densityMatrix P
  have hBform : B = projectiveReadout A := rfl
  have hU : (1 : Matrix n n ℂ) ∈ unitaryGroup n ℂ := one_mem _
  have hid (r : DensityState n) : unitaryConjugateState 1 hU r = r := by
    apply Subtype.ext
    change CStarMatrix.ofMatrix (unitaryEvolution 1 (densityMatrix r)) = r.1
    simp [unitaryEvolution, densityMatrix]
  let r : ℕ → DensityState n :=
    Nat.rec rho (fun _ s => basisPinchingState (unitaryConjugateState 1 hU s))
  have hStep (k : ℕ) : r (k + 1) = basisPinchingState (unitaryConjugateState 1 hU (r k)) := rfl
  have hEntropy := (entropy_production_coherence_deletion_identity 1 hU r hStep).1 0
  change vonNeumannEntropy (basisPinchingState (unitaryConjugateState 1 hU rho)) -
      vonNeumannEntropy rho = quantumRelativeEntropy (unitaryConjugateState 1 hU rho)
        (basisPinchingState (unitaryConjugateState 1 hU rho)) ∧
      0 ≤ quantumRelativeEntropy (unitaryConjugateState 1 hU rho)
        (basisPinchingState (unitaryConjugateState 1 hU rho)) at hEntropy
  rw [hid] at hEntropy
  have hp (s : DensityState n) : (densityMatrix s).PosSemidef := by
    rw [← Matrix.nonneg_iff_posSemidef]
    exact map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm s.2.1
  let M := ‖A‖ + ‖B‖ + 1
  have hM : 0 < M := by dsimp [M]; positivity
  have ceiling (X : Matrix n n ℂ) (hX : X.PosSemidef) (hx : ‖X‖ ≤ M) :
      X ≤ (M : ℂ) • 1 := by
    have he : algebraMap ℝ (Matrix n n ℂ) M = (M : ℂ) • 1 := by
      simp [Algebra.algebraMap_eq_smul_one]
    rw [← he]
    exact (CStarAlgebra.norm_le_iff_le_algebraMap X hM.le hX.nonneg).mp hx
  have hsupport (v : n → ℂ) (hv : B *ᵥ v = 0) : A *ᵥ v = 0 :=
    pinching_support A (hp rho) v (hBform ▸ hv)
  have hKlein := actual_matrix_spectral_ceiling_strong_klein A B (hp rho) (hp P) M hM
    (ceiling A (hp rho) (by dsimp [M]; linarith [norm_nonneg B]))
    (ceiling B (hp P) (by dsimp [M]; linarith [norm_nonneg A]))
    hsupport
  have htrA : A.trace = 1 := rho.2.2
  have htrB : B.trace = 1 := P.2.2
  have hquant : ((A - B)ᴴ * (A - B)).trace.re / (2 * M) ≤ quantumRelativeEntropy rho P := by
    rw [htrA, htrB, sub_add_cancel] at hKlein
    change _ ≤ (A * (cfc Real.log A - cfc Real.log B)).trace.re
    exact hKlein
  have hstrict (hne : B ≠ A) : 0 < quantumRelativeEntropy rho P := by
    have hn := (Complex.nonneg_iff.mp
      (Matrix.posSemidef_conjTranspose_mul_self (A - B)).trace_nonneg)
    have hz : ((A - B)ᴴ * (A - B)).trace.re ≠ 0 := by
      intro h
      have htrace : ((A - B)ᴴ * (A - B)).trace = 0 := Complex.ext h hn.2.symm
      exact hne (sub_eq_zero.mp (Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp htrace)).symm
    exact (div_pos (lt_of_le_of_ne hn.1 hz.symm) (by positivity)).trans_le hquant
  have h' : 0 < 4 * G := by positivity
  change 4 * G * (vonNeumannEntropy P - vonNeumannEntropy rho) = _ ∧ _ ∧ _ ∧ _
  rw [hEntropy.1]
  refine ⟨rfl, mul_nonneg h'.le hEntropy.2, ?_, ?_⟩
  · intro i j hij hne
    apply mul_pos h' (hstrict ?_)
    intro he
    have hij' := congrFun (congrFun he i) j
    exact hne (by simpa [hBform, projectiveReadout, diagonal_apply_ne _ hij] using hij'.symm)
  · constructor
    · intro hz
      by_contra hn
      exact (mul_pos h' (hstrict hn)).ne' hz
    · intro he
      have hr : P = rho := Subtype.ext (CStarMatrix.ofMatrix.symm.injective he)
      change basisPinchingState rho = rho at hr
      change 4 * G * quantumRelativeEntropy rho P = 0
      rw [← hEntropy.1, hr, sub_self, mul_zero]

end Pinching

#print axioms symmetric_null_vanishing_iff_smul_eta
#print axioms jacobson_bianchi_einstein_equation
#print axioms cosmological_constant_indeterminacy_counterexample
#print axioms raychaudhuri_monotonic_focusing
#print axioms hawking_penrose_caustic_bound
#print axioms hawking_penrose_caustic_sharpness
#print axioms stationary_horizon_shear_weyl_rigidity
#print axioms qfc_iff_qnec_at_stationary_horizon
#print axioms clausius_area_monotonicity_from_record_pinching

end D5.S3.Geometry.Lorentz.HorizonThermodynamicsJacobson4D
