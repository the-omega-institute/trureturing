/- GID: D5/S3/Quantum/Gauge/GaugeUnificationRG4D
   generality: G
   mirror-B: D5/B/S3/Quantum/Gauge/GaugeUnificationRG4D
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: One-loop gauge running, Weyl multiplet traces, and the three-coupling unification condition. -/

import OmegaBuild.Commands
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! One-loop inverse-coupling flow and the traces of a single all-left-handed Weyl
generation. The beta convention gives a positive coefficient for asymptotic freedom.
The abelian inverse coupling uses the normalization α₁ = (5/3) αY. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter
open scoped BigOperators Topology

namespace D5.S3.Quantum.Gauge.GaugeUnificationRG4D

/-- One-loop coefficient for fundamental Dirac fermions and complex scalar multiplets. -/
def betaOneLoop (N nf ns : ℕ) : ℝ :=
  (11 / 3 : ℝ) * N - (2 / 3 : ℝ) * nf - (1 / 6 : ℝ) * ns

theorem asymptotic_freedom_iff (N nf ns : ℕ) :
    0 < betaOneLoop N nf ns ↔ 4 * nf + ns < 22 * N := by
  have h : ((4 * nf + ns : ℕ) : ℝ) < ((22 * N : ℕ) : ℝ) ↔
      4 * nf + ns < 22 * N := Nat.cast_lt
  rw [← h]
  push_cast
  unfold betaOneLoop
  constructor <;> intro h' <;> linarith

theorem qcd_asymptotic_freedom_iff (nf : ℕ) :
    0 < betaOneLoop 3 nf 0 ↔ nf ≤ 16 := by
  rw [asymptotic_freedom_iff]
  omega

theorem qcd_six_flavors_beta : betaOneLoop 3 6 0 = 7 := by
  norm_num [betaOneLoop]

/-- Inverse coupling with initial value `a₀` at the reference scale `μ₀`. -/
def rgInvCoupling (b₀ a₀ μ₀ μ : ℝ) : ℝ :=
  a₀ + (b₀ / (2 * Real.pi)) * Real.log (μ / μ₀)

theorem rgInvCoupling_hasDerivAt (b₀ a₀ : ℝ) {μ₀ μ : ℝ} (hμ₀ : 0 < μ₀)
    (hμ : 0 < μ) :
    HasDerivAt (rgInvCoupling b₀ a₀ μ₀) (b₀ / (2 * Real.pi * μ)) μ := by
  have hlog := (Real.hasDerivAt_log (div_ne_zero hμ.ne' hμ₀.ne')).comp μ
    ((hasDerivAt_id μ).div_const μ₀)
  have h : HasDerivAt (rgInvCoupling b₀ a₀ μ₀)
      ((b₀ / (2 * Real.pi)) * ((μ / μ₀)⁻¹ * (1 / μ₀))) μ :=
    (hlog.const_mul (b₀ / (2 * Real.pi))).const_add a₀
  convert h using 1
  field_simp [Real.pi_ne_zero, hμ.ne', hμ₀.ne']

theorem rg_asymptotic_freedom_limit {b₀ : ℝ} (a₀ : ℝ) {μ₀ : ℝ}
    (hb₀ : 0 < b₀) (hμ₀ : 0 < μ₀) :
    Tendsto (fun μ => (rgInvCoupling b₀ a₀ μ₀ μ)⁻¹) atTop (𝓝 0) := by
  have hlog : Tendsto (fun μ : ℝ => Real.log (μ / μ₀)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_id.atTop_div_const hμ₀)
  have hslope := hlog.const_mul_atTop (div_pos hb₀ (by positivity : 0 < 2 * Real.pi))
  have hflow : Tendsto (rgInvCoupling b₀ a₀ μ₀) atTop atTop :=
    tendsto_const_nhds.add_atTop hslope
  exact hflow.inv_tendsto_atTop

theorem rg_zero_scale_iff (a₀ : ℝ) {b₀ μ₀ μ : ℝ} (hb₀ : b₀ ≠ 0) (hμ₀ : 0 < μ₀)
    (hμ : 0 < μ) :
    rgInvCoupling b₀ a₀ μ₀ μ = 0 ↔ μ = μ₀ * Real.exp (-(2 * Real.pi * a₀ / b₀)) := by
  unfold rgInvCoupling
  constructor
  · intro hz
    have hlog : Real.log (μ / μ₀) = -(2 * Real.pi * a₀ / b₀) := by
      rw [← neg_div]
      apply (eq_div_iff hb₀).2
      field_simp [Real.pi_ne_zero] at hz
      linarith
    have hexp := congrArg Real.exp hlog
    rw [Real.exp_log (div_pos hμ hμ₀)] at hexp
    exact ((div_eq_iff hμ₀.ne').mp hexp).trans (mul_comm _ _)
  · intro h
    rw [h, mul_div_cancel_left₀ _ hμ₀.ne', Real.log_exp]
    field_simp [hb₀, Real.pi_ne_zero]
    ring

theorem rg_zero_scale_unique (a₀ : ℝ) {b₀ μ₀ : ℝ} (hb₀ : b₀ ≠ 0) (hμ₀ : 0 < μ₀) :
    ∃! μ : ℝ, 0 < μ ∧ rgInvCoupling b₀ a₀ μ₀ μ = 0 := by
  have hs : 0 < μ₀ * Real.exp (-(2 * Real.pi * a₀ / b₀)) :=
    mul_pos hμ₀ (Real.exp_pos _)
  refine ⟨_, ⟨hs, (rg_zero_scale_iff a₀ hb₀ hμ₀ hs).2 rfl⟩, ?_⟩
  intro μ hμ
  exact (rg_zero_scale_iff a₀ hb₀ hμ₀ hμ.1).1 hμ.2

theorem rg_confinement_scale_lt {b₀ a₀ μ₀ : ℝ} (hb₀ : 0 < b₀) (ha₀ : 0 < a₀)
    (hμ₀ : 0 < μ₀) :
    μ₀ * Real.exp (-(2 * Real.pi * a₀ / b₀)) < μ₀ := by
  calc
    μ₀ * Real.exp (-(2 * Real.pi * a₀ / b₀)) < μ₀ * Real.exp 0 :=
      mul_lt_mul_of_pos_left
        (Real.exp_lt_exp.mpr (neg_lt_zero.mpr (div_pos (by positivity) hb₀))) hμ₀
    _ = μ₀ := by simp

theorem rg_landau_pole_gt {b₀ a₀ μ₀ : ℝ} (hb₀ : b₀ < 0) (ha₀ : 0 < a₀)
    (hμ₀ : 0 < μ₀) :
    μ₀ < μ₀ * Real.exp (-(2 * Real.pi * a₀ / b₀)) := by
  calc
    μ₀ = μ₀ * Real.exp 0 := by simp
    _ < μ₀ * Real.exp (-(2 * Real.pi * a₀ / b₀)) :=
      mul_lt_mul_of_pos_left
        (Real.exp_lt_exp.mpr (neg_pos.mpr (div_neg_of_pos_of_neg (by positivity) hb₀))) hμ₀

/-- The quark doublet, conjugate up and down singlets, lepton doublet, and
conjugate charged lepton. -/
inductive SMFermion where
  | QL | uRc | dRc | LL | eRc
  deriving DecidableEq

instance : Fintype SMFermion where
  elems := {.QL, .uRc, .dRc, .LL, .eRc}
  complete f := by cases f <;> simp

/-- Number of weak components in the multiplet. -/
def weakMultiplicity : SMFermion → ℕ
  | .QL | .LL => 2
  | .uRc | .dRc | .eRc => 1

/-- Number of color components in the multiplet. -/
def colorMultiplicity (Nc : ℕ) : SMFermion → ℕ
  | .QL | .uRc | .dRc => Nc
  | .LL | .eRc => 1

/-- Eigenvalue of the third weak generator on the specified weak component. -/
def weylT3 : (f : SMFermion) → Fin (weakMultiplicity f) → ℝ
  | .QL, i | .LL, i => if i.val = 0 then 1 / 2 else -1 / 2
  | .uRc, _ | .dRc, _ | .eRc, _ => 0

/-- Hypercharge on the anomaly-free curve with the charged lepton normalized to one. -/
def weylY (Nc : ℕ) : SMFermion → ℝ
  | .QL => 1 / (2 * (Nc : ℝ))
  | .uRc => -((Nc : ℝ) + 1) / (2 * Nc)
  | .dRc => ((Nc : ℝ) - 1) / (2 * Nc)
  | .LL => -1 / 2
  | .eRc => 1

/-- Sum over weak components, weighted by color multiplicity. -/
def weylTrace (Nc : ℕ) (weight : ℝ → ℝ → ℝ) : ℝ :=
  ∑ f : SMFermion, (colorMultiplicity Nc f : ℝ) *
    ∑ i : Fin (weakMultiplicity f), weight (weylT3 f i) (weylY Nc f)

/-- Color trace per weak component, with the fundamental and its conjugate
both having Dynkin index one half. -/
def colorIndex : SMFermion → ℝ
  | .QL | .uRc | .dRc => 1 / 2
  | .LL | .eRc => 0

def weylT3SqTrace (Nc : ℕ) : ℝ :=
  weylTrace Nc fun t _ => t ^ 2

def weylColorSqTrace : ℝ :=
  ∑ f : SMFermion, (weakMultiplicity f : ℝ) * colorIndex f

def weylT3YTrace (Nc : ℕ) : ℝ :=
  weylTrace Nc fun t y => t * y

def weylYSqTraceAnom (Nc : ℕ) : ℝ :=
  weylTrace Nc fun _ y => y ^ 2

def weylQSqTraceAnom (Nc : ℕ) : ℝ :=
  weylTrace Nc fun t y => (t + y) ^ 2

private theorem sum_smFermion (weight : SMFermion → ℝ) :
    (∑ f : SMFermion, weight f) =
      weight .QL + (weight .uRc + (weight .dRc + (weight .LL + weight .eRc))) := by
  change (∑ f ∈ ({.QL, .uRc, .dRc, .LL, .eRc} : Finset SMFermion), weight f) = _
  simp [Finset.sum_insert]

theorem weylT3SqTrace_eq (Nc : ℕ) : weylT3SqTrace Nc = ((Nc : ℝ) + 1) / 2 := by
  norm_num [weylT3SqTrace, weylTrace, sum_smFermion, colorMultiplicity,
    weakMultiplicity, weylT3, Fin.sum_univ_succ]
  ring

theorem weylColorSqTrace_eq : weylColorSqTrace = 2 := by
  norm_num [weylColorSqTrace, sum_smFermion, weakMultiplicity, colorIndex]

theorem color_weak_unification_iff_three (Nc : ℕ) :
    weylT3SqTrace Nc = weylColorSqTrace ↔ Nc = 3 := by
  rw [weylT3SqTrace_eq, weylColorSqTrace_eq]
  constructor
  · intro h
    exact_mod_cast (show (Nc : ℝ) = 3 by linarith)
  · rintro rfl
    norm_num

theorem weylT3YTrace_eq_zero (Nc : ℕ) : weylT3YTrace Nc = 0 := by
  have hdoublet (y : ℝ) :
      (∑ i : Fin 2, (if i.val = 0 then (1 / 2 : ℝ) else -1 / 2) * y) = 0 := by
    norm_num [Fin.sum_univ_two]
  have hq : (∑ i : Fin (weakMultiplicity .QL), weylT3 .QL i * weylY Nc .QL) = 0 :=
    hdoublet _
  have hl : (∑ i : Fin (weakMultiplicity .LL), weylT3 .LL i * weylY Nc .LL) = 0 :=
    hdoublet _
  rw [weylT3YTrace, weylTrace, sum_smFermion, hq, hl]
  simp [weylT3]

theorem weylYSqTraceAnom_eq {Nc : ℕ} (hNc : Nc ≠ 0) :
    weylYSqTraceAnom Nc = ((Nc : ℝ) + 1) * (Nc + 2) / (2 * Nc) := by
  have hn : (Nc : ℝ) ≠ 0 := by exact_mod_cast hNc
  norm_num [weylYSqTraceAnom, weylTrace, sum_smFermion, colorMultiplicity,
    weakMultiplicity, weylY, Fin.sum_univ_succ]
  field_simp [hn]
  ring

theorem weyl_pythagoras (Nc : ℕ) :
    weylQSqTraceAnom Nc = weylT3SqTrace Nc + weylYSqTraceAnom Nc := by
  have hsplit : weylQSqTraceAnom Nc =
      weylT3SqTrace Nc + 2 * weylT3YTrace Nc + weylYSqTraceAnom Nc := by
    unfold weylQSqTraceAnom weylT3SqTrace weylT3YTrace weylYSqTraceAnom weylTrace
    have hmixed :
        (∑ f : SMFermion, (colorMultiplicity Nc f : ℝ) *
          ∑ i : Fin (weakMultiplicity f), 2 * weylT3 f i * weylY Nc f) =
        2 * ∑ f : SMFermion, (colorMultiplicity Nc f : ℝ) *
          ∑ i : Fin (weakMultiplicity f), weylT3 f i * weylY Nc f := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro f _
      apply Finset.sum_congr rfl
      intro i _
      ring
    simp only [add_sq, Finset.sum_add_distrib, mul_add, hmixed]
  rw [hsplit, weylT3YTrace_eq_zero, mul_zero, add_zero]

theorem weylQSqTraceAnom_eq {Nc : ℕ} (hNc : Nc ≠ 0) :
    weylQSqTraceAnom Nc = ((Nc : ℝ) + 1) ^ 2 / Nc := by
  have hn : (Nc : ℝ) ≠ 0 := by exact_mod_cast hNc
  rw [weyl_pythagoras, weylT3SqTrace_eq, weylYSqTraceAnom_eq hNc]
  field_simp [hn]
  ring

theorem gut_hypercharge_norm_anom {Nc : ℕ} (hNc : Nc ≠ 0) :
    weylYSqTraceAnom Nc / weylT3SqTrace Nc = ((Nc : ℝ) + 2) / Nc := by
  have hn : (Nc : ℝ) ≠ 0 := by exact_mod_cast hNc
  have hp : (Nc : ℝ) + 1 ≠ 0 := by positivity
  rw [weylYSqTraceAnom_eq hNc, weylT3SqTrace_eq]
  field_simp [hn, hp]

theorem gut_hypercharge_norm_three : weylYSqTraceAnom 3 / weylT3SqTrace 3 = 5 / 3 := by
  norm_num [gut_hypercharge_norm_anom (by decide : (3 : ℕ) ≠ 0)]

theorem gut_weinberg_anom {Nc : ℕ} (hNc : Nc ≠ 0) :
    weylT3SqTrace Nc / weylQSqTraceAnom Nc = (Nc : ℝ) / (2 * (Nc + 1)) := by
  have hn : (Nc : ℝ) ≠ 0 := by exact_mod_cast hNc
  have hp : (Nc : ℝ) + 1 ≠ 0 := by positivity
  rw [weylT3SqTrace_eq, weylQSqTraceAnom_eq hNc]
  field_simp [hn, hp]

theorem gut_weinberg_three_eighths : weylT3SqTrace 3 / weylQSqTraceAnom 3 = 3 / 8 := by
  norm_num [gut_weinberg_anom (by decide : (3 : ℕ) ≠ 0)]

theorem weinberg_anom_sub_fixed (Nc : ℕ) :
    (Nc : ℝ) / (2 * (Nc + 1)) - 9 * (Nc + 1) / (4 * (9 + 5 * Nc)) =
      ((Nc : ℝ) ^ 2 - 9) / (4 * (Nc + 1) * (9 + 5 * Nc)) := by
  have hp : (Nc : ℝ) + 1 ≠ 0 := by positivity
  have hq : 9 + 5 * (Nc : ℝ) ≠ 0 := by positivity
  field_simp [hp, hq]
  ring

theorem weinberg_curves_cross_iff_three (Nc : ℕ) :
    (Nc : ℝ) / (2 * (Nc + 1)) = 9 * (Nc + 1) / (4 * (9 + 5 * Nc)) ↔ Nc = 3 := by
  rw [← sub_eq_zero, weinberg_anom_sub_fixed]
  have hden : (4 * ((Nc : ℝ) + 1) * (9 + 5 * Nc)) ≠ 0 := by positivity
  rw [div_eq_zero_iff, or_iff_left hden]
  constructor
  · intro h
    have hfactor : ((Nc : ℝ) - 3) * ((Nc : ℝ) + 3) = 0 := by linear_combination h
    have hp : (Nc : ℝ) + 3 ≠ 0 := by positivity
    exact_mod_cast (sub_eq_zero.mp ((mul_eq_zero.mp hfactor).resolve_right hp) :
      (Nc : ℝ) = 3)
  · rintro rfl
    norm_num

/-- Weak components for the three colored copies of each quark multiplet and
the single lepton multiplets. The quark doublets are listed by color. -/
def sm15State : Fin 15 → (f : SMFermion) × Fin (weakMultiplicity f) :=
  ![⟨.QL, (0 : Fin 2)⟩, ⟨.QL, (1 : Fin 2)⟩,
    ⟨.QL, (0 : Fin 2)⟩, ⟨.QL, (1 : Fin 2)⟩,
    ⟨.QL, (0 : Fin 2)⟩, ⟨.QL, (1 : Fin 2)⟩,
    ⟨.uRc, (0 : Fin 1)⟩, ⟨.uRc, (0 : Fin 1)⟩, ⟨.uRc, (0 : Fin 1)⟩,
    ⟨.dRc, (0 : Fin 1)⟩, ⟨.dRc, (0 : Fin 1)⟩, ⟨.dRc, (0 : Fin 1)⟩,
    ⟨.LL, (0 : Fin 2)⟩, ⟨.LL, (1 : Fin 2)⟩, ⟨.eRc, (0 : Fin 1)⟩]

def sm15T3 (i : Fin 15) : ℝ :=
  match sm15State i with
  | ⟨f, j⟩ => weylT3 f j

private theorem sm15T3_apply (i : Fin 15) :
    sm15T3 i = (![1 / 2, -1 / 2, 1 / 2, -1 / 2, 1 / 2, -1 / 2,
      0, 0, 0, 0, 0, 0, 1 / 2, -1 / 2, 0] : Fin 15 → ℝ) i := by
  fin_cases i <;> rfl

def sm15Y (i : Fin 15) : ℝ := weylY 3 (sm15State i).1

def sm15Q (i : Fin 15) : ℝ := sm15T3 i + sm15Y i

theorem sm15_trace_T3_sq : ∑ i : Fin 15, (sm15T3 i) ^ 2 = 2 := by
  norm_num [sm15T3_apply, Fin.sum_univ_succ]

theorem sm15_trace_Y_sq : ∑ i : Fin 15, (sm15Y i) ^ 2 = 10 / 3 := by
  norm_num [sm15Y, sm15State, weylY, Fin.sum_univ_succ]

theorem sm15_trace_Q_sq : ∑ i : Fin 15, (sm15Q i) ^ 2 = 16 / 3 := by
  norm_num [sm15Q, sm15T3_apply, sm15Y, sm15State, Fin.sum_univ_succ, weylY]

theorem sm15_trace_T3_Y : ∑ i : Fin 15, sm15T3 i * sm15Y i = 0 := by
  norm_num [sm15T3_apply, sm15Y, sm15State, Fin.sum_univ_succ, weylY]

theorem sm15_trace_Y : ∑ i : Fin 15, sm15Y i = 0 := by
  norm_num [sm15Y, sm15State, weylY, Fin.sum_univ_succ]

theorem sm15_trace_Y_cube : ∑ i : Fin 15, (sm15Y i) ^ 3 = 0 := by
  norm_num [sm15Y, sm15State, weylY, Fin.sum_univ_succ]

def smBeta1 (ng nH : ℕ) : ℝ := -(4 / 3 : ℝ) * ng - (1 / 10 : ℝ) * nH

def smBeta2 (ng nH : ℕ) : ℝ := (22 / 3 : ℝ) - (4 / 3 : ℝ) * ng - (1 / 6 : ℝ) * nH

def smBeta3 (ng : ℕ) : ℝ := 11 - (4 / 3 : ℝ) * ng

theorem sm_beta_standard_values :
    smBeta1 3 1 = -41 / 10 ∧ smBeta2 3 1 = 19 / 6 ∧ smBeta3 3 = 7 := by
  norm_num [smBeta1, smBeta2, smBeta3]

theorem sm_beta_diff_independent_of_ng (ng nH : ℕ) :
    smBeta2 ng nH - smBeta1 ng nH = 22 / 3 - (nH : ℝ) / 15 ∧
    smBeta3 ng - smBeta2 ng nH = 11 / 3 + (nH : ℝ) / 6 ∧
    smBeta3 ng - smBeta1 ng nH = 11 + (nH : ℝ) / 10 := by
  unfold smBeta1 smBeta2 smBeta3
  exact ⟨by ring, by ring, by ring⟩

theorem three_coupling_unification_iff {a₁ a₂ a₃ b₁ b₂ b₃ : ℝ}
    (ha12 : a₁ ≠ a₂) (h12 : b₁ < b₂) (h23 : b₂ < b₃) :
    (∃ t aGUT, a₁ + b₁ * t = aGUT ∧ a₂ + b₂ * t = aGUT ∧ a₃ + b₃ * t = aGUT) ↔
      (a₂ - a₃) / (a₁ - a₂) = (b₂ - b₃) / (b₁ - b₂) := by
  have ha := sub_ne_zero.mpr ha12
  have hb := sub_ne_zero.mpr h12.ne
  rw [div_eq_div_iff ha hb]
  constructor
  · rintro ⟨t, aGUT, h₁, h₂, h₃⟩
    linear_combination (b₁ - b₂) * (h₂ - h₃) - (b₂ - b₃) * (h₁ - h₂)
  · intro h
    let t := (a₂ - a₃) / (b₃ - b₂)
    have ht₂₃ : (b₃ - b₂) * t = a₂ - a₃ := by
      dsimp [t]
      field_simp [sub_ne_zero.mpr h23.ne']
    have ht₁₂ : (b₂ - b₁) * t = a₁ - a₂ := by
      apply (mul_left_cancel₀ (sub_ne_zero.mpr h23.ne'))
      linear_combination (b₂ - b₁) * ht₂₃ - h
    exact ⟨t, a₁ + b₁ * t, rfl, by linear_combination ht₁₂,
      by linear_combination ht₁₂ + ht₂₃⟩

def mssmBeta1 : ℝ := -33 / 5

def mssmBeta2 : ℝ := -1

def mssmBeta3 : ℝ := 3

theorem sm_B_ratio_eq :
    (smBeta3 3 - smBeta2 3 1) / (smBeta2 3 1 - smBeta1 3 1) = 115 / 218 := by
  obtain ⟨h₁, h₂, h₃⟩ := sm_beta_standard_values
  rw [h₁, h₂, h₃]
  norm_num

theorem mssm_B_ratio_eq : (mssmBeta3 - mssmBeta2) / (mssmBeta2 - mssmBeta1) = 5 / 7 := by
  norm_num [mssmBeta1, mssmBeta2, mssmBeta3]

theorem sm_B_ratio_lt_mssm : (115 / 218 : ℝ) < 5 / 7 := by
  norm_num

/-- Square of the weak mixing sine, computed from the hypercharge and weak couplings. -/
def weakMixingAngleSq (a₁inv a₂inv : ℝ) : ℝ :=
  ((3 / 5 : ℝ) * a₁inv⁻¹) / ((3 / 5 : ℝ) * a₁inv⁻¹ + a₂inv⁻¹)

theorem gut_weinberg_running_formula {a₁inv a₂inv : ℝ}
    (h₁ : a₁inv ≠ 0) (h₂ : a₂inv ≠ 0) :
    weakMixingAngleSq a₁inv a₂inv = 3 * a₂inv / (5 * a₁inv + 3 * a₂inv) := by
  have hscale : (5 * a₁inv * a₂inv) ≠ 0 := by positivity
  unfold weakMixingAngleSq
  rw [← mul_div_mul_left _ _ hscale]
  have hnum : 5 * a₁inv * a₂inv * (3 / 5 * a₁inv⁻¹) = 3 * a₂inv := by
    field_simp [h₁]
  have hden : 5 * a₁inv * a₂inv * (3 / 5 * a₁inv⁻¹ + a₂inv⁻¹) =
      5 * a₁inv + 3 * a₂inv := by
    field_simp [h₁, h₂]
    ring
  rw [hnum, hden]

theorem gut_weinberg_at_unification {aGUT : ℝ} (ha : aGUT ≠ 0) :
    weakMixingAngleSq aGUT aGUT = 3 / 8 := by
  rw [gut_weinberg_running_formula ha ha]
  have hden : 5 * aGUT + 3 * aGUT ≠ 0 := by
    intro hz
    exact ha (by linarith)
  apply (div_eq_iff hden).2
  ring

/-- The electromagnetic coupling is the reciprocal of the sum of the two inverse
couplings expressed in electroweak normalization. -/
def electromagneticCoupling (a₁inv a₂inv : ℝ) : ℝ :=
  ((5 / 3 : ℝ) * a₁inv + a₂inv)⁻¹

/-- Georgi–Quinn–Weinberg offset from common inverse coupling at the unification scale. -/
theorem gut_weinberg_running_offset (b₁ b₂ aGUT μGUT μ : ℝ)
    (h₁ : rgInvCoupling b₁ aGUT μGUT μ ≠ 0) (h₂ : rgInvCoupling b₂ aGUT μGUT μ ≠ 0)
    (hEM : (5 / 3 : ℝ) * rgInvCoupling b₁ aGUT μGUT μ +
      rgInvCoupling b₂ aGUT μGUT μ ≠ 0) :
    weakMixingAngleSq (rgInvCoupling b₁ aGUT μGUT μ) (rgInvCoupling b₂ aGUT μGUT μ) -
        3 / 8 =
      (5 / (16 * Real.pi)) *
        electromagneticCoupling (rgInvCoupling b₁ aGUT μGUT μ)
          (rgInvCoupling b₂ aGUT μGUT μ) * (b₂ - b₁) * Real.log (μ / μGUT) := by
  let a₁ := rgInvCoupling b₁ aGUT μGUT μ
  let a₂ := rgInvCoupling b₂ aGUT μGUT μ
  change weakMixingAngleSq a₁ a₂ - 3 / 8 =
    (5 / (16 * Real.pi)) * electromagneticCoupling a₁ a₂ * (b₂ - b₁) *
      Real.log (μ / μGUT)
  have hden : 5 * a₁ + 3 * a₂ ≠ 0 := by
    intro hz
    apply hEM
    change (5 / 3 : ℝ) * a₁ + a₂ = 0
    linear_combination hz / 3
  have hd : a₂ - a₁ = ((b₂ - b₁) / (2 * Real.pi)) * Real.log (μ / μGUT) := by
    dsimp [a₁, a₂, rgInvCoupling]
    ring
  rw [gut_weinberg_running_formula (show a₁ ≠ 0 from h₁) (show a₂ ≠ 0 from h₂)]
  change (5 / 3 : ℝ) * a₁ + a₂ ≠ 0 at hEM
  calc
    3 * a₂ / (5 * a₁ + 3 * a₂) - 3 / 8 =
        (5 / 8 : ℝ) * (a₂ - a₁) * electromagneticCoupling a₁ a₂ := by
      unfold electromagneticCoupling
      field_simp [hEM, hden]
      ring
    _ = _ := by
      rw [hd]
      field_simp [Real.pi_ne_zero]
      ring

end D5.S3.Quantum.Gauge.GaugeUnificationRG4D
