import OmegaBuild.Commands
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-! Omega original.

Coordinate derivatives and conformal covariance of a half-space power kernel
for a diagonal quadratic form with one variable sign. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter Set
open scoped Topology

namespace OmegaMath.ConformalHalfSpaceKernel

def denominator (σ z t x y : ℝ) : ℝ :=
  z ^ 2 + σ * t ^ 2 + x ^ 2 + y ^ 2

def kernel (σ Δ z t x y : ℝ) : ℝ :=
  (z / denominator σ z t x y) ^ Δ

def metric (σ L z dz dt dx dy : ℝ) : ℝ :=
  (L ^ 2 / z ^ 2) * denominator σ dz dt dx dy

def radialSlope (Δ z s : ℝ) : ℝ :=
  Δ * (1 / z - 2 * z / s)

def radialCurvature (Δ z s : ℝ) : ℝ :=
  (radialSlope Δ z s) ^ 2 + Δ * (-(1 / z ^ 2) - 2 / s + 4 * z ^ 2 / s ^ 2)

def transverseSlope (Δ w q s : ℝ) : ℝ :=
  -2 * Δ * w * q / s

def transverseCurvature (Δ w q s : ℝ) : ℝ :=
  (transverseSlope Δ w q s) ^ 2 - 2 * Δ * w / s + 4 * Δ * w ^ 2 * q ^ 2 / s ^ 2

private theorem hasDerivAt_powerRatio {a b : ℝ → ℝ} {a' b' u Δ : ℝ}
    (ha : HasDerivAt a a' u) (hb : HasDerivAt b b' u) (ha0 : 0 < a u) (hb0 : 0 < b u) :
    HasDerivAt (fun v => (a v / b v) ^ Δ)
      (Δ * (a' / a u - b' / b u) * (a u / b u) ^ Δ) u := by
  have hq := (div_pos ha0 hb0).ne'
  convert (ha.div hb hb0.ne').rpow_const (p := Δ) (Or.inl hq) using 1
  simp only [Pi.div_apply]
  rw [Real.rpow_sub_one hq]
  field_simp

private theorem hasDerivAt_quadratic (w q c : ℝ) :
    HasDerivAt (fun v : ℝ => c + w * v ^ 2) (2 * w * q) q := by
  have h : HasDerivAt (fun v : ℝ => v) 1 q := hasDerivAt_id q
  convert ((h.pow 2).const_mul w).const_add c using 1
  norm_num
  ring

private theorem radial_first (Δ c z : ℝ) (hz : 0 < z) (hs : 0 < c + z ^ 2) :
    HasDerivAt (fun v => (v / (c + v ^ 2)) ^ Δ)
      (radialSlope Δ z (c + z ^ 2) * (z / (c + z ^ 2)) ^ Δ) z := by
  simpa only [radialSlope, one_mul, mul_one, id_eq] using
    hasDerivAt_powerRatio (Δ := Δ) (hasDerivAt_id z) (hasDerivAt_quadratic 1 z c)
      hz (show 0 < c + 1 * z ^ 2 by simpa using hs)

private theorem radial_slope_deriv (Δ c z : ℝ) (hz : 0 < z) (hs : 0 < c + z ^ 2) :
    HasDerivAt (fun v => radialSlope Δ v (c + v ^ 2))
      (Δ * (-(1 / z ^ 2) - 2 / (c + z ^ 2) + 4 * z ^ 2 / (c + z ^ 2) ^ 2)) z := by
  have hs' : HasDerivAt (fun v : ℝ => c + v ^ 2) (2 * z) z := by
    simpa using hasDerivAt_quadratic 1 z c
  have h₁ := (hasDerivAt_const z (1 : ℝ)).div (hasDerivAt_id z) hz.ne'
  have h₂ := ((hasDerivAt_id z).const_mul (2 : ℝ)).div hs' hs.ne'
  convert (h₁.sub h₂).const_mul Δ using 1
  · rfl
  · simp only [id_eq, zero_mul, one_mul, zero_sub]
    field_simp
    ring

private theorem radial_power_jet (Δ c z : ℝ) (hz : 0 < z) (hs : 0 < c + z ^ 2) :
    let f := fun v : ℝ => (v / (c + v ^ 2)) ^ Δ
    HasDerivAt f (radialSlope Δ z (c + z ^ 2) * f z) z ∧
      HasDerivAt (deriv f) (radialCurvature Δ z (c + z ^ 2) * f z) z := by
  dsimp
  have hp := radial_first Δ c z hz hs
  refine ⟨hp, ?_⟩
  have hevent : ∀ᶠ v : ℝ in 𝓝 z, 0 < v ∧ 0 < c + v ^ 2 := by
    have hz' : ∀ᶠ v : ℝ in 𝓝 z, 0 < v := isOpen_Ioi.mem_nhds hz
    have hs' : ∀ᶠ v : ℝ in 𝓝 z, 0 < c + v ^ 2 :=
      (continuous_const.add (continuous_id.pow 2)).continuousAt.eventually
        (isOpen_Ioi.mem_nhds hs)
    exact hz'.and hs'
  have heq : deriv (fun v : ℝ => (v / (c + v ^ 2)) ^ Δ) =ᶠ[𝓝 z]
      (fun v => radialSlope Δ v (c + v ^ 2) * (v / (c + v ^ 2)) ^ Δ) := by
    filter_upwards [hevent] with v hv
    exact (radial_first Δ c v hv.1 hv.2).deriv
  apply HasDerivAt.congr_of_eventuallyEq _ heq
  convert (radial_slope_deriv Δ c z hz hs).mul hp using 1
  unfold radialCurvature
  ring

private theorem transverse_first (Δ z c w q : ℝ) (hz : 0 < z) (hs : 0 < c + w * q ^ 2) :
    HasDerivAt (fun v => (z / (c + w * v ^ 2)) ^ Δ)
      (transverseSlope Δ w q (c + w * q ^ 2) * (z / (c + w * q ^ 2)) ^ Δ) q := by
  convert hasDerivAt_powerRatio (Δ := Δ) (hasDerivAt_const q z)
    (hasDerivAt_quadratic w q c) hz hs using 1
  unfold transverseSlope
  ring

private theorem transverse_slope_deriv (Δ c w q : ℝ) (hs : 0 < c + w * q ^ 2) :
    HasDerivAt (fun v => transverseSlope Δ w v (c + w * v ^ 2))
      (-2 * Δ * w / (c + w * q ^ 2) + 4 * Δ * w ^ 2 * q ^ 2 / (c + w * q ^ 2) ^ 2) q := by
  convert (((hasDerivAt_id q).const_mul (-2 * Δ * w)).div
    (hasDerivAt_quadratic w q c) hs.ne') using 1
  · rfl
  · simp only [id_eq, mul_one]
    field_simp
    ring

theorem transverseJet (Δ z c w q : ℝ) (hz : 0 < z) (hs : 0 < c + w * q ^ 2) :
    let f := fun v : ℝ => (z / (c + w * v ^ 2)) ^ Δ
    HasDerivAt f (transverseSlope Δ w q (c + w * q ^ 2) * f q) q ∧
      HasDerivAt (deriv f) (transverseCurvature Δ w q (c + w * q ^ 2) * f q) q := by
  dsimp
  have hp := transverse_first Δ z c w q hz hs
  refine ⟨hp, ?_⟩
  have hevent : ∀ᶠ v : ℝ in 𝓝 q, 0 < c + w * v ^ 2 :=
    (continuous_const.add (continuous_const.mul (continuous_id.pow 2))).continuousAt.eventually
      (isOpen_Ioi.mem_nhds hs)
  have heq : deriv (fun v : ℝ => (z / (c + w * v ^ 2)) ^ Δ) =ᶠ[𝓝 q]
      (fun v => transverseSlope Δ w v (c + w * v ^ 2) * (z / (c + w * v ^ 2)) ^ Δ) := by
    filter_upwards [hevent] with v hv
    exact (transverse_first Δ z c w v hz hv).deriv
  apply HasDerivAt.congr_of_eventuallyEq _ heq
  convert (transverse_slope_deriv Δ c w q hs).mul hp using 1
  unfold transverseCurvature
  ring

theorem radialJet {σ Δ z t x y : ℝ} (hz : 0 < z) (hs : 0 < denominator σ z t x y) :
    let f := fun v : ℝ => kernel σ Δ v t x y
    HasDerivAt f (radialSlope Δ z (denominator σ z t x y) * f z) z ∧
      HasDerivAt (deriv f) (radialCurvature Δ z (denominator σ z t x y) * f z) z := by
  let c := σ * t ^ 2 + x ^ 2 + y ^ 2
  have heq (v : ℝ) : denominator σ v t x y = c + v ^ 2 := by
    dsimp [denominator, c]
    ring
  simp only [kernel, heq] at hs ⊢
  exact radial_power_jet Δ c z hz hs

theorem coordinateJets {σ Δ z t x y : ℝ} (hz : 0 < z) (hs : 0 < denominator σ z t x y) :
    let s := denominator σ z t x y
    let k := kernel σ Δ z t x y
    let ft := fun v : ℝ => kernel σ Δ z v x y
    let fx := fun v : ℝ => kernel σ Δ z t v y
    let fy := fun v : ℝ => kernel σ Δ z t x v
    (HasDerivAt ft (transverseSlope Δ σ t s * k) t ∧
      HasDerivAt (deriv ft) (transverseCurvature Δ σ t s * k) t) ∧
    (HasDerivAt fx (transverseSlope Δ 1 x s * k) x ∧
      HasDerivAt (deriv fx) (transverseCurvature Δ 1 x s * k) x) ∧
    (HasDerivAt fy (transverseSlope Δ 1 y s * k) y ∧
      HasDerivAt (deriv fy) (transverseCurvature Δ 1 y s * k) y) := by
  dsimp only
  have ht (v : ℝ) : denominator σ z v x y = (z ^ 2 + x ^ 2 + y ^ 2) + σ * v ^ 2 := by
    unfold denominator
    ring
  have hx (v : ℝ) : denominator σ z t v y = (z ^ 2 + σ * t ^ 2 + y ^ 2) + 1 * v ^ 2 := by
    unfold denominator
    ring
  have hy (v : ℝ) : denominator σ z t x v = (z ^ 2 + σ * t ^ 2 + x ^ 2) + 1 * v ^ 2 := by
    unfold denominator
    ring
  exact ⟨by simpa only [kernel, ht] using transverseJet Δ z _ σ t hz (ht t ▸ hs),
    by simpa only [kernel, hx] using transverseJet Δ z _ 1 x hz (hx x ▸ hs),
    by simpa only [kernel, hy] using transverseJet Δ z _ 1 y hz (hy y ▸ hs)⟩

private theorem kernel_coefficients {σ Δ z t x y s : ℝ}
    (hσ : σ ^ 2 = 1) (hz : z ≠ 0) (hs : s ≠ 0) (h : s = denominator σ z t x y) :
    z ^ 2 * (radialCurvature Δ z s + σ * transverseCurvature Δ σ t s +
      transverseCurvature Δ 1 x s + transverseCurvature Δ 1 y s) -
      2 * z * radialSlope Δ z s = Δ * (Δ - 3) := by
  have hσ₃ : σ ^ 3 = σ := by
    rw [show σ ^ 3 = σ ^ 2 * σ by ring, hσ, one_mul]
  unfold radialCurvature radialSlope transverseCurvature transverseSlope
  have hrad :
      (Δ * (1 / z - 2 * z / s)) ^ 2 + Δ * (-(1 / z ^ 2) - 2 / s + 4 * z ^ 2 / s ^ 2) =
        Δ * (Δ - 1) / z ^ 2 - 2 * Δ * (2 * Δ + 1) / s +
          4 * Δ * (Δ + 1) * z ^ 2 / s ^ 2 := by
    field_simp
    ring
  have htr (w q : ℝ) :
      (-2 * Δ * w * q / s) ^ 2 - 2 * Δ * w / s + 4 * Δ * w ^ 2 * q ^ 2 / s ^ 2 =
        -2 * Δ * w / s + 4 * Δ * (Δ + 1) * w ^ 2 * q ^ 2 / s ^ 2 := by ring
  rw [hrad, htr, htr, htr]
  have hsum :
      σ * (-2 * Δ * σ / s + 4 * Δ * (Δ + 1) * σ ^ 2 * t ^ 2 / s ^ 2) =
        -2 * Δ / s + 4 * Δ * (Δ + 1) * σ * t ^ 2 / s ^ 2 := by
    calc
      _ = -2 * Δ * σ ^ 2 / s + 4 * Δ * (Δ + 1) * σ ^ 3 * t ^ 2 / s ^ 2 := by ring
      _ = _ := by rw [hσ, hσ₃]; ring
  rw [hsum]
  unfold denominator at h
  field_simp
  linear_combination -4 * Δ * (Δ + 1) * z ^ 2 * h

theorem kernel_equation {σ Δ z t x y : ℝ} (hσ : σ ^ 2 = 1)
    (hz : 0 < z) (hs : 0 < denominator σ z t x y) :
    z ^ 2 * (deriv (deriv (fun v => kernel σ Δ v t x y)) z +
      σ * deriv (deriv (fun v => kernel σ Δ z v x y)) t +
      deriv (deriv (fun v => kernel σ Δ z t v y)) x +
      deriv (deriv (fun v => kernel σ Δ z t x v)) y) -
      2 * z * deriv (fun v => kernel σ Δ v t x y) z = Δ * (Δ - 3) * kernel σ Δ z t x y := by
  obtain ⟨hr, hrr⟩ := radialJet (Δ := Δ) hz hs
  obtain ⟨⟨_, htt⟩, ⟨_, hxx⟩, ⟨_, hyy⟩⟩ := coordinateJets (Δ := Δ) hz hs
  rw [hr.deriv, hrr.deriv, htt.deriv, hxx.deriv, hyy.deriv]
  let s := denominator σ z t x y
  calc
    _ = (z ^ 2 * (radialCurvature Δ z s + σ * transverseCurvature Δ σ t s +
        transverseCurvature Δ 1 x s + transverseCurvature Δ 1 y s) -
        2 * z * radialSlope Δ z s) * kernel σ Δ z t x y := by dsimp [s]; ring
    _ = _ := by rw [kernel_coefficients hσ hz.ne' hs.ne' rfl]

theorem kernel_scaling {σ Δ a z t x y : ℝ}
    (ha : 0 < a) (hz : 0 < z) (hs : 0 < denominator σ z t x y) :
    kernel σ Δ (a * z) (a * t) (a * x) (a * y) =
      a ^ (-Δ) * kernel σ Δ z t x y := by
  have hd : denominator σ (a * z) (a * t) (a * x) (a * y) =
      a ^ 2 * denominator σ z t x y := by
    unfold denominator
    ring
  have hratio : a * z / (a ^ 2 * denominator σ z t x y) =
      a⁻¹ * (z / denominator σ z t x y) := by
    field_simp [ha.ne', hs.ne']
  unfold kernel
  rw [hd, hratio, Real.mul_rpow (inv_nonneg.mpr ha.le) (div_nonneg hz.le hs.le),
    Real.rpow_neg_eq_inv_rpow]

theorem kernel_boundary (Δ t x y : ℝ) (hr : 0 < t ^ 2 + x ^ 2 + y ^ 2) :
    Tendsto (fun z : ℝ => z ^ (-Δ) * kernel 1 Δ z t x y) (𝓝[>] 0)
      (𝓝 (Real.sqrt (t ^ 2 + x ^ 2 + y ^ 2) ^ (-2 * Δ))) := by
  let d := fun z : ℝ => denominator 1 z t x y
  have d0 : d 0 = t ^ 2 + x ^ 2 + y ^ 2 := by simp [d, denominator]
  have hd : Continuous d := by unfold d denominator; fun_prop
  have hcont : ContinuousAt (fun z => d z ^ (-Δ)) 0 :=
    (Real.continuousAt_rpow_const (d 0) (-Δ) (Or.inl (d0 ▸ hr.ne'))).comp hd.continuousAt
  have heq : (fun z => d z ^ (-Δ)) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun z => z ^ (-Δ) * kernel 1 Δ z t x y) := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    change 0 < z at hz
    have hs : 0 < d z := by
      dsimp [d, denominator]
      nlinarith [sq_nonneg z]
    change d z ^ (-Δ) = z ^ (-Δ) * (z / d z) ^ Δ
    rw [Real.div_rpow hz.le hs.le, ← mul_div_assoc, ← Real.rpow_add hz,
      neg_add_cancel, Real.rpow_zero, one_div, Real.rpow_neg hs.le]
  have hpow : d 0 ^ (-Δ) = Real.sqrt (t ^ 2 + x ^ 2 + y ^ 2) ^ (-2 * Δ) := by
    rw [d0, Real.sqrt_eq_rpow, ← Real.rpow_mul hr.le]
    congr 1
    ring
  rw [← hpow]
  exact (hcont.tendsto.mono_left nhdsWithin_le_nhds).congr' heq

def inverseCoordinate (s q : ℝ) : ℝ := q / s

def denominatorVelocity (σ z t x y dz dt dx dy : ℝ) : ℝ :=
  2 * (z * dz + σ * t * dt + x * dx + y * dy)

def inverseVelocity (s ds q dq : ℝ) : ℝ :=
  (dq * s - q * ds) / s ^ 2

theorem denominator_hasDerivAt {σ u dz dt dx dy : ℝ} {z t x y : ℝ → ℝ}
    (hz : HasDerivAt z dz u) (ht : HasDerivAt t dt u) (hx : HasDerivAt x dx u)
    (hy : HasDerivAt y dy u) :
    HasDerivAt (fun v => denominator σ (z v) (t v) (x v) (y v))
      (denominatorVelocity σ (z u) (t u) (x u) (y u) dz dt dx dy) u := by
  convert (((hz.pow 2).add ((ht.pow 2).const_mul σ)).add (hx.pow 2)).add (hy.pow 2) using 1
  · rfl
  · simp [denominatorVelocity]
    ring

theorem inverseCoordinate_hasDerivAt {u dq ds : ℝ} {q s : ℝ → ℝ}
    (hq : HasDerivAt q dq u) (hs : HasDerivAt s ds u) (hs₀ : s u ≠ 0) :
    HasDerivAt (fun v => inverseCoordinate (s v) (q v)) (inverseVelocity (s u) ds (q u) dq) u :=
  hq.div hs hs₀

theorem inversion_preserves_patch {σ z t x y : ℝ}
    (hz : 0 < z) (hs : 0 < denominator σ z t x y) :
    let s := denominator σ z t x y
    0 < inverseCoordinate s z ∧
      denominator σ (inverseCoordinate s z) (inverseCoordinate s t)
        (inverseCoordinate s x) (inverseCoordinate s y) = 1 / s := by
  dsimp [inverseCoordinate]
  refine ⟨div_pos hz hs, ?_⟩
  let s := denominator σ z t x y
  change denominator σ (z / s) (t / s) (x / s) (y / s) = 1 / s
  have h : s = z ^ 2 + σ * t ^ 2 + x ^ 2 + y ^ 2 := rfl
  have hs₀ : s ≠ 0 := hs.ne'
  unfold denominator
  field_simp [hs₀]
  linear_combination -h

theorem inversion_involutive {σ z t x y : ℝ}
    (hz : 0 < z) (hs : 0 < denominator σ z t x y) :
    let s := denominator σ z t x y
    let s' := denominator σ (inverseCoordinate s z) (inverseCoordinate s t)
      (inverseCoordinate s x) (inverseCoordinate s y)
    inverseCoordinate s' (inverseCoordinate s z) = z ∧
      inverseCoordinate s' (inverseCoordinate s t) = t ∧
      inverseCoordinate s' (inverseCoordinate s x) = x ∧
      inverseCoordinate s' (inverseCoordinate s y) = y := by
  dsimp only
  rw [(inversion_preserves_patch hz hs).2]
  have recover (q : ℝ) : inverseCoordinate (1 / denominator σ z t x y)
      (inverseCoordinate (denominator σ z t x y) q) = q := by
    unfold inverseCoordinate
    field_simp [hs.ne']
  exact ⟨recover z, recover t, recover x, recover y⟩

private theorem inversion_denominator {σ z t x y dz dt dx dy s : ℝ} (hs : s ≠ 0)
    (h : s = denominator σ z t x y) :
    let ds := denominatorVelocity σ z t x y dz dt dx dy
    denominator σ (inverseVelocity s ds z dz) (inverseVelocity s ds t dt)
      (inverseVelocity s ds x dx) (inverseVelocity s ds y dy) =
      denominator σ dz dt dx dy / s ^ 2 := by
  dsimp [denominator, denominatorVelocity, inverseVelocity] at *
  field_simp
  linear_combination -4 * (z * dz + σ * t * dt + x * dx + y * dy) ^ 2 * h

theorem inversion_metric_pullback {σ L z t x y : ℝ} (dz dt dx dy : ℝ)
    (hz : 0 < z) (hs : 0 < denominator σ z t x y) :
    let s := denominator σ z t x y
    let ds := denominatorVelocity σ z t x y dz dt dx dy
    metric σ L (inverseCoordinate s z) (inverseVelocity s ds z dz)
      (inverseVelocity s ds t dt) (inverseVelocity s ds x dx) (inverseVelocity s ds y dy) =
      metric σ L z dz dt dx dy := by
  dsimp only
  unfold metric
  rw [inversion_denominator hs.ne' rfl]
  let s := denominator σ z t x y
  change L ^ 2 / (z / s) ^ 2 * (denominator σ dz dt dx dy / s ^ 2) = _
  have hs₀ : s ≠ 0 := hs.ne'
  field_simp [hz.ne', hs₀]

theorem kernel_inverted_height (σ Δ z t x y : ℝ) :
    kernel σ Δ z t x y = inverseCoordinate (denominator σ z t x y) z ^ Δ := rfl

end OmegaMath.ConformalHalfSpaceKernel
