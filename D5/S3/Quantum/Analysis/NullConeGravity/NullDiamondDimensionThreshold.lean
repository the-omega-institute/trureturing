/- GID: D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondDimensionThreshold
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/NullConeGravity/NullDiamondDimensionThreshold
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact harmonic multiplicities, angular summability thresholds and the de Sitter conformal locus. -/

import OmegaBuild.Commands
import D5.S3.Geometry.Lorentz.DimensionSelection4D
import D5.S3.Quantum.Analysis.NullConeGravity.NullDiamondSphere4D
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.NumberTheory.Harmonic.Bounds

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-! Multiplicities and dimension thresholds for the leading null-diamond angular model. -/

noncomputable section

namespace NullConeGravity

open MeasureTheory Set Filter
open scoped BigOperators

/-- The difference of homogeneous polynomial dimensions in degree ℓ and degree ℓ minus two. -/
def harmonicMult (D ℓ : ℕ) : ℕ :=
  Nat.choose (ℓ + D - 2) (D - 2) -
    (if 2 ≤ ℓ then Nat.choose (ℓ + D - 4) (D - 2) else 0)

private theorem harmonicMult_pascal (k ℓ : ℕ) (hℓ : 1 ≤ ℓ) :
    harmonicMult (k + 3) ℓ = (ℓ + k).choose k + (ℓ + k - 1).choose k := by
  let n := ℓ + k - 1
  have hn : n + 1 = ℓ + k := by dsimp [n]; omega
  have htop : ℓ + (k + 3) - 2 = n + 1 + 1 := by omega
  have hbottom : ℓ + (k + 3) - 4 = n := by dsimp [n]; omega
  have hk : k + 3 - 2 = k + 1 := by omega
  have hsub : (if 2 ≤ ℓ then n.choose (k + 1) else 0) = n.choose (k + 1) := by
    split_ifs with h
    · rfl
    · rw [Nat.choose_eq_zero_of_lt]
      dsimp [n]
      omega
  rw [harmonicMult, htop, hk, hbottom, hsub, Nat.choose_succ_succ' (n + 1) k,
    Nat.choose_succ_succ' n k, hn]
  change _ = (ℓ + k).choose k + n.choose k
  omega

theorem harmonicMult_four (ℓ : ℕ) : harmonicMult 4 ℓ = 2 * ℓ + 1 := by
  cases ℓ with
  | zero => decide
  | succ n =>
    rw [show 4 = 1 + 3 by decide, harmonicMult_pascal 1 (n + 1) (by omega)]
    simp only [Nat.choose_one_right]
    omega

private theorem choose_two_scaled (n : ℕ) :
    2 * (n + 2).choose 2 = (n + 1) * (n + 2) := by
  change (Nat.factorial 2) * (n + 2).choose 2 = _
  rw [← Nat.descFactorial_eq_factorial_mul_choose]
  simp [Nat.descFactorial_succ, show n + 2 - 1 = n + 1 by omega, mul_comm]

private theorem choose_three_scaled (n : ℕ) :
    6 * (n + 3).choose 3 = (n + 1) * (n + 2) * (n + 3) := by
  change (Nat.factorial 3) * (n + 3).choose 3 = _
  rw [← Nat.descFactorial_eq_factorial_mul_choose]
  simp [Nat.descFactorial_succ, show n + 3 - 1 = n + 2 by omega,
    show n + 3 - 2 = n + 1 by omega, mul_comm, mul_assoc]

theorem harmonicMult_five (ℓ : ℕ) : harmonicMult 5 ℓ = (ℓ + 1)^2 := by
  cases ℓ with
  | zero => decide
  | succ n =>
    rw [show 5 = 2 + 3 by decide, harmonicMult_pascal 2 (n + 1) (by omega)]
    have h₁ := choose_two_scaled (n + 1)
    have h₂ := choose_two_scaled n
    rw [show n + 1 + 2 - 1 = n + 2 by omega]
    zify at h₁ h₂ ⊢
    nlinarith only [h₁, h₂]

theorem harmonicMult_six (ℓ : ℕ) :
    harmonicMult 6 ℓ = (ℓ + 1) * (ℓ + 2) * (2 * ℓ + 3) / 6 := by
  cases ℓ with
  | zero => decide
  | succ n =>
    rw [show 6 = 3 + 3 by decide, harmonicMult_pascal 3 (n + 1) (by omega)]
    rw [show n + 1 + 3 - 1 = n + 3 by omega]
    have h₁ := choose_three_scaled (n + 1)
    have h₂ := choose_three_scaled n
    have h : 6 * ((n + 1 + 3).choose 3 + (n + 3).choose 3) =
        (n + 1 + 1) * (n + 1 + 2) * (2 * (n + 1) + 3) := by
      zify at h₁ h₂ ⊢
      nlinarith only [h₁, h₂]
    rw [← h, Nat.mul_comm 6, Nat.mul_div_cancel _ (by decide : 0 < 6)]

/-- Uniform lower and upper bounds in degree, with dimension-dependent constants. -/
theorem harmonicMult_bounds (D : ℕ) (hD : 4 ≤ D) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ ∀ ℓ : ℕ, 1 ≤ ℓ →
      a * (ℓ : ℝ) ^ (D - 3) ≤ (harmonicMult D ℓ : ℝ) ∧
      (harmonicMult D ℓ : ℝ) ≤ b * (ℓ : ℝ) ^ (D - 3) := by
  let k := D - 3
  have hD' : D = k + 3 := by dsimp [k]; omega
  refine ⟨(k.factorial : ℝ)⁻¹, 2 * (2 : ℝ)^k, ?_, by positivity, ?_⟩
  · exact inv_pos.mpr (by exact_mod_cast k.factorial_pos)
  intro ℓ hℓ
  rw [hD', harmonicMult_pascal k ℓ hℓ, Nat.cast_add,
    show k + 3 - 3 = k by omega]
  have hlower : (ℓ : ℝ)^k / (k.factorial : ℝ) ≤ ((ℓ + k).choose k : ℝ) := by
    have h := Nat.pow_le_choose (α := ℝ) k (ℓ + k)
    rw [show ℓ + k + 1 - k = ℓ + 1 by omega] at h
    refine le_trans ?_ h
    gcongr
    omega
  have hfirst : ((ℓ + k).choose k : ℝ) ≤ ((ℓ : ℝ) + 1)^k := by
    exact_mod_cast Nat.choose_add_le_add_one_pow ℓ k
  have hsecond : ((ℓ + k - 1).choose k : ℝ) ≤ ((ℓ + k).choose k : ℝ) := by
    exact_mod_cast Nat.choose_le_choose k (Nat.sub_le _ _)
  have hℓ' : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hupper : ((ℓ : ℝ) + 1)^k ≤ (2 : ℝ)^k * (ℓ : ℝ)^k := by
    rw [← mul_pow]
    gcongr
    linarith
  constructor
  · rw [mul_comm, ← div_eq_mul_inv]
    exact hlower.trans (le_add_of_nonneg_right (by positivity))
  · calc
      _ ≤ 2 * (((ℓ : ℝ) + 1)^k) := by linarith
      _ ≤ _ := by rw [mul_assoc]; gcongr

/-- Squared leading angular eigenvalue with its degree multiplicity and without the overall amplitude. -/
def leadingModeWeight (D ℓ : ℕ) : ℝ :=
  (harmonicMult D ℓ : ℝ) /
    ((((ℓ : ℝ) + ((D : ℝ) - 2)/2 - 1) * ((ℓ : ℝ) + ((D : ℝ) - 2)/2)) ^ 2)

private theorem leadingModeWeight_bounds (D : ℕ) (hD : 4 ≤ D) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ ∀ ℓ : ℕ, 1 ≤ ℓ →
      a * (ℓ : ℝ) ^ ((D : ℤ) - 7) ≤ leadingModeWeight D ℓ ∧
      leadingModeWeight D ℓ ≤ b * (ℓ : ℝ) ^ ((D : ℤ) - 7) := by
  obtain ⟨a, b, ha, hb, hbounds⟩ := harmonicMult_bounds D hD
  let c : ℝ := (D : ℝ) + 1
  have hD' : (4 : ℝ) ≤ D := by exact_mod_cast hD
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨a / c^4, b, by positivity, hb, ?_⟩
  intro ℓ hℓ
  let x : ℝ := ℓ
  let κ : ℝ := ((D : ℝ) - 2) / 2
  have hx : 1 ≤ x := by
    change 1 ≤ (ℓ : ℝ)
    exact_mod_cast hℓ
  have hxpos : 0 < x := by linarith
  have hκ : 1 ≤ κ := by dsimp [κ]; linarith
  have hκc : κ ≤ c - 1 := by dsimp [c, κ]; linarith
  have hcx : x + κ ≤ c * x := by
    nlinarith [mul_nonneg (show 0 ≤ c - 1 by dsimp [c]; linarith)
      (show 0 ≤ x - 1 by linarith)]
  have hlower : x^4 ≤ ((x + κ - 1) * (x + κ))^2 := by
    rw [show x^4 = (x*x)^2 by ring]
    gcongr <;> linarith
  have hupper : ((x + κ - 1) * (x + κ))^2 ≤ c^4 * x^4 := by
    rw [show c^4 * x^4 = ((c*x)*(c*x))^2 by ring]
    apply pow_le_pow_left₀ (mul_nonneg (by linarith) (by linarith))
    exact mul_le_mul (by linarith) hcx (by linarith) (by positivity)
  have hpos : 0 < ((x + κ - 1) * (x + κ))^2 := by
    exact (pow_pos hxpos 4).trans_le hlower
  have hpow : x ^ ((D : ℤ) - 7) * x^4 = x ^ (D - 3) := by
    rw [← zpow_natCast x 4, ← zpow_add₀ hxpos.ne',
      show (D : ℤ) - 7 + (4 : ℕ) = ((D - 3 : ℕ) : ℤ) by omega, zpow_natCast]
  obtain ⟨h₁, h₂⟩ := hbounds ℓ hℓ
  change a / c^4 * x ^ ((D : ℤ) - 7) ≤ _ ∧ _ ≤ b * x ^ ((D : ℤ) - 7)
  unfold leadingModeWeight
  change _ ≤ (harmonicMult D ℓ : ℝ) / ((x + κ - 1) * (x + κ))^2 ∧
    (harmonicMult D ℓ : ℝ) / ((x + κ - 1) * (x + κ))^2 ≤ _
  constructor
  · apply (le_div_iff₀ hpos).mpr
    calc
      _ ≤ (a / c^4 * x ^ ((D : ℤ) - 7)) * (c^4 * x^4) := by gcongr
      _ = a * (x ^ ((D : ℤ) - 7) * x^4) := by field_simp
      _ ≤ _ := by rw [hpow]; exact h₁
  · apply (div_le_iff₀ hpos).mpr
    calc
      _ ≤ b * x ^ (D - 3) := h₂
      _ = (b * x ^ ((D : ℤ) - 7)) * x^4 := by rw [mul_assoc, hpow]
      _ ≤ _ := by gcongr

/-- The leading angular mode sum converges exactly in dimensions four and five. -/
theorem leadingModeWeight_summable_iff (D : ℕ) (hD : 4 ≤ D) :
    Summable (fun ℓ : ℕ => if ℓ = 0 then 0 else leadingModeWeight D ℓ) ↔ D = 4 ∨ D = 5 := by
  obtain ⟨a, b, ha, _hb, hab⟩ := leadingModeWeight_bounds D hD
  rw [← summable_nat_add_iff 1]
  simp only [Nat.add_one_ne_zero, ite_false]
  open D5.S3.Geometry.Lorentz.DimensionSelection4D in
  have h := angular_trace_summable_iff_of_eventually_comparable D
      (fun ℓ => leadingModeWeight D (ℓ + 1)) (fun _ => by unfold leadingModeWeight; positivity)
      ha (Filter.Eventually.of_forall fun ℓ => by
        simpa [angularMode] using (hab (ℓ + 1) (by omega)))
  exact h.trans (by omega)

private theorem harmonic_sum (L : ℕ) :
    (∑ n ∈ Finset.range L, ((n + 1 : ℕ) : ℝ)⁻¹) = (harmonic L : ℝ) := by
  simp [harmonic]

/-- The cutoff through degree L has logarithmic growth in dimension six. -/
theorem leadingModeWeight_sum_six_bounds :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ ∀ L : ℕ, 2 ≤ L →
      a * Real.log L ≤ ∑ n ∈ Finset.range L, leadingModeWeight 6 (n + 1) ∧
      (∑ n ∈ Finset.range L, leadingModeWeight 6 (n + 1)) ≤ b * Real.log L := by
  obtain ⟨a, b, ha, hb, hab⟩ := leadingModeWeight_bounds 6 (by decide)
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨a, b * (1 + (Real.log 2)⁻¹), ha, by positivity, ?_⟩
  intro L hL
  have hL' : (2 : ℝ) ≤ L := by exact_mod_cast hL
  have hLL : 0 < (L : ℝ) := by linarith
  have hlo : Real.log (L : ℝ) ≤ (harmonic L : ℝ) := by
    refine le_trans (Real.log_le_log hLL ?_) (log_add_one_le_harmonic L)
    norm_cast
    omega
  have hup : (harmonic L : ℝ) ≤ (1 + (Real.log 2)⁻¹) * Real.log L := by
    have h₁ : 1 ≤ (Real.log 2)⁻¹ * Real.log L := by
      rw [← div_eq_inv_mul, le_div_iff₀ hlog, one_mul]
      exact Real.log_le_log (by norm_num) hL'
    have h₂ := harmonic_le_one_add_log L
    linarith
  constructor
  · calc
      _ ≤ a * (harmonic L : ℝ) := by gcongr
      _ = ∑ n ∈ Finset.range L, a * ((n + 1 : ℕ) : ℝ)⁻¹ := by
        rw [← Finset.mul_sum, harmonic_sum]
      _ ≤ _ := Finset.sum_le_sum fun n _ => by
        simpa using (hab (n + 1) (by omega)).1
  · calc
      _ ≤ ∑ n ∈ Finset.range L, b * ((n + 1 : ℕ) : ℝ)⁻¹ :=
        Finset.sum_le_sum fun n _ => by simpa using (hab (n + 1) (by omega)).2
      _ = b * (harmonic L : ℝ) := by rw [← Finset.mul_sum, harmonic_sum]
      _ ≤ _ := by rw [mul_assoc]; gcongr

private theorem power_sum_bounds (k L : ℕ) :
    (L : ℝ)^(k+1) / (k+1 : ℝ) ≤ ∑ n ∈ Finset.range L, ((n + 1 : ℕ) : ℝ)^k ∧
    (∑ n ∈ Finset.range L, ((n + 1 : ℕ) : ℝ)^k) ≤ (L : ℝ)^(k+1) := by
  have hmono : MonotoneOn (fun x : ℝ => x^k) (Icc 0 (0 + (L : ℝ))) := by
    intro x hx y _ hxy
    exact pow_le_pow_left₀ hx.1 hxy _
  have h := hmono.integral_le_sum
  simp only [zero_add] at h
  rw [integral_pow] at h
  refine ⟨by simpa using h, ?_⟩
  calc
    _ ≤ ∑ _n ∈ Finset.range L, (L : ℝ)^k := Finset.sum_le_sum fun n hn =>
      pow_le_pow_left₀ (by positivity) (by exact_mod_cast Finset.mem_range.mp hn) _
    _ = _ := by simp [pow_succ, mul_comm]

/-- The cutoff through degree L grows as L raised to D minus six in all higher dimensions. -/
theorem leadingModeWeight_sum_ge_seven_bounds (D : ℕ) (hD : 7 ≤ D) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ ∀ L : ℕ, 1 ≤ L →
      a * (L : ℝ) ^ (D - 6) ≤ ∑ n ∈ Finset.range L, leadingModeWeight D (n + 1) ∧
      (∑ n ∈ Finset.range L, leadingModeWeight D (n + 1)) ≤ b * (L : ℝ) ^ (D - 6) := by
  obtain ⟨a, b, ha, hb, hab⟩ := leadingModeWeight_bounds D (by omega)
  let k := D - 7
  refine ⟨a / ((k : ℝ)+1), b, by positivity, hb, ?_⟩
  intro L _hL
  rw [show D - 6 = k + 1 by dsimp [k]; omega]
  have hcast : (D : ℤ) - 7 = (k : ℤ) := by dsimp [k]; omega
  have hmode (n : ℕ) := hab (n + 1) (by omega)
  simp only [hcast, zpow_natCast] at hmode
  obtain ⟨hlo, hup⟩ := power_sum_bounds k L
  constructor
  · calc
      _ = a * ((L : ℝ)^(k+1) / (k+1 : ℝ)) := by ring
      _ ≤ a * (∑ n ∈ Finset.range L, ((n + 1 : ℕ) : ℝ)^k) := by gcongr
      _ ≤ _ := by rw [Finset.mul_sum]; exact Finset.sum_le_sum fun n _ => (hmode n).1
  · calc
      _ ≤ b * (∑ n ∈ Finset.range L, ((n + 1 : ℕ) : ℝ)^k) := by
        rw [Finset.mul_sum]; exact Finset.sum_le_sum fun n _ => (hmode n).2
      _ ≤ _ := by gcongr

/-- Integrability of the squared leading power against the local spherical weight. -/
theorem angular_power_sq_integrable_iff (D : ℕ) (hD : 5 ≤ D) :
    IntegrableOn (fun t : ℝ => t ^ (((D : ℝ) - 4) / 2) *
      (t ^ (-(((D : ℝ) - 4) / 2))) ^ 2) (Set.Ioc 0 2) volume ↔ D = 5 := by
  let β : ℝ := ((D : ℝ) - 4) / 2
  change IntegrableOn (fun t : ℝ => t^β * (t^(-β))^2) (Ioc 0 2) volume ↔ _
  rw [integrableOn_Ioc_iff_integrableOn_Ioo]
  have heq : Set.EqOn (fun t : ℝ => t^β * (t^(-β))^2) (fun t => t^(-β)) (Ioo 0 2) := by
    intro t ht
    change t^β * (t^(-β))^2 = t^(-β)
    rw [pow_two, ← mul_assoc, ← Real.rpow_add ht.1, add_neg_cancel,
      Real.rpow_zero, one_mul]
  rw [integrableOn_congr_fun heq measurableSet_Ioo,
    intervalIntegral.integrableOn_Ioo_rpow_iff (by norm_num)]
  have hD' : (5 : ℝ) ≤ D := by exact_mod_cast hD
  constructor
  · intro h
    have hlt : (D : ℝ) < 6 := by dsimp [β] at h; linarith
    have : D < 6 := by exact_mod_cast hlt
    omega
  · rintro rfl
    norm_num [β]

/-- Leading squared angular density in the coordinate measured from coincidence. -/
def angularSquaredDensity (D : ℕ) (t : ℝ) : ℝ :=
  if D = 4 then (Real.log t)^2 else
    t ^ (((D : ℝ) - 4) / 2) * (t ^ (-(((D : ℝ) - 4) / 2))) ^ 2

theorem angularSquaredDensity_integrable_iff (D : ℕ) (hD : 4 ≤ D) :
    IntegrableOn (angularSquaredDensity D) (Ioc 0 2) volume ↔ D = 4 ∨ D = 5 := by
  by_cases h : D = 4
  · subst D
    simp only [true_or, iff_true]
    change IntegrableOn (fun t : ℝ => (Real.log t)^2) (Ioc 0 2) volume
    exact
      (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 2)).mp
        intervalIntegrable_log_sq
  · simp only [h, false_or]
    have hdensity : angularSquaredDensity D = fun t : ℝ =>
        t ^ (((D : ℝ) - 4) / 2) * (t ^ (-(((D : ℝ) - 4) / 2))) ^ 2 := by
      funext t
      simp [angularSquaredDensity, h]
    rw [hdensity]
    exact angular_power_sq_integrable_iff D (by omega)

/-- Conformal curvature coupling in spacetime dimension D. -/
def deSitterConformalCoupling (D : ℕ) : ℝ := ((D : ℝ) - 2) / (4 * ((D : ℝ) - 1))

/-- Scalar curvature in the de Sitter normalization with Hubble parameter H. -/
def deSitterRicciScalar (D : ℕ) (H : ℝ) : ℝ := (D : ℝ) * ((D : ℝ) - 1) * H^2

/-- Effective squared mass relative to the conformal reference. -/
def deSitterConformalMassSq (D : ℕ) (m ξ H : ℝ) : ℝ :=
  m^2 + (ξ - deSitterConformalCoupling D) * deSitterRicciScalar D H

theorem deSitterConformalMassSq_eq_sub (D : ℕ) (hD : 4 ≤ D) (m ξ H : ℝ) :
    m^2 + ξ * deSitterRicciScalar D H -
      (((D : ℝ) - 2)/2) * ((((D : ℝ) - 2)/2) + 1) * H^2 =
    deSitterConformalMassSq D m ξ H := by
  have hD' : (4 : ℝ) ≤ D := by exact_mod_cast hD
  unfold deSitterConformalMassSq deSitterConformalCoupling deSitterRicciScalar
  field_simp [show (D : ℝ) - 1 ≠ 0 by linarith]
  ring

theorem deSitterConformalMassSq_conformal (D : ℕ) (H : ℝ) :
    deSitterConformalMassSq D 0 (deSitterConformalCoupling D) H = 0 := by
  simp [deSitterConformalMassSq]

theorem deSitterConformalMassSq_minimal_neg (D : ℕ) (hD : 4 ≤ D) (H : ℝ) (hH : 0 < H) :
    deSitterConformalMassSq D 0 0 H < 0 := by
  rw [← deSitterConformalMassSq_eq_sub D hD]
  simp only [zero_pow (by decide : 2 ≠ 0), zero_mul, add_zero, zero_sub, neg_lt_zero]
  have hD' : (4 : ℝ) ≤ D := by exact_mod_cast hD
  exact mul_pos (mul_pos (by linarith) (by linarith)) (pow_pos hH _)

/-- A nonzero conformal mass coefficient leaves the leading dimension threshold intact. -/
theorem deSitter_leadingModeWeight_summable_iff (D : ℕ) (hD : 4 ≤ D) (m ξ H : ℝ) :
    Summable (fun ℓ : ℕ => if ℓ = 0 then 0 else
      deSitterConformalMassSq D m ξ H ^ 2 * leadingModeWeight D ℓ) ↔
      deSitterConformalMassSq D m ξ H = 0 ∨ D = 4 ∨ D = 5 := by
  let δ := deSitterConformalMassSq D m ξ H
  change Summable (fun ℓ : ℕ => if ℓ = 0 then 0 else δ^2 * leadingModeWeight D ℓ) ↔
    δ = 0 ∨ D = 4 ∨ D = 5
  by_cases hδ : δ = 0
  · simp [hδ]
  · have h (ℓ : ℕ) : (if ℓ = 0 then 0 else δ^2 * leadingModeWeight D ℓ) =
        δ^2 * (if ℓ = 0 then 0 else leadingModeWeight D ℓ) := by
      split_ifs <;> simp
    simp only [h, hδ, false_or]
    rw [summable_mul_left_iff (pow_ne_zero _ hδ), leadingModeWeight_summable_iff D hD]

end NullConeGravity
