/- GID: D5/S3/Quantum/Gauge/ElectroweakHiggsMechanism4D
   generality: G
   mirror-B: D5/B/S3/Quantum/Gauge/ElectroweakHiggsMechanism4D
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact electroweak vacuum stabilizer, gauge mass rotation, custodial rho, and Higgs fluctuation spectrum. -/

import OmegaBuild.Commands
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Quantum.Gauge.ElectroweakHiggsMechanism4D

def higgsPotential (lam v : ℝ) (Φ : Fin 2 → ℂ) : ℝ :=
  lam * ((‖Φ 0‖ ^ 2 + ‖Φ 1‖ ^ 2) - v ^ 2 / 2) ^ 2

def higgsVac (v : ℝ) : Fin 2 → ℂ := ![0, (v / Real.sqrt 2 : ℂ)]

theorem higgsPotential_nonneg {lam v : ℝ} {Φ : Fin 2 → ℂ} (hlam : 0 < lam) :
    0 ≤ higgsPotential lam v Φ := by
  unfold higgsPotential
  positivity

theorem higgsPotential_eq_zero_iff {lam v : ℝ} {Φ : Fin 2 → ℂ} (hlam : 0 < lam) :
    higgsPotential lam v Φ = 0 ↔ ‖Φ 0‖ ^ 2 + ‖Φ 1‖ ^ 2 = v ^ 2 / 2 := by
  unfold higgsPotential
  rw [mul_eq_zero]
  constructor
  · intro h
    rcases h with h | h
    · exact False.elim ((ne_of_gt hlam) h)
    · exact sub_eq_zero.mp (sq_eq_zero_iff.mp h)
  · intro h
    right
    exact sq_eq_zero_iff.mpr (sub_eq_zero.mpr h)

theorem higgsPotential_vacuum_zero {lam v : ℝ} (hlam : 0 < lam) :
    higgsPotential lam v (higgsVac v) = 0 := by
  apply (higgsPotential_eq_zero_iff hlam).2
  have hnorm : ‖(v / Real.sqrt 2 : ℂ)‖ ^ 2 = v ^ 2 / 2 := by
    rw [Complex.sq_norm]
    simp [Complex.normSq]
    have hs : (Real.sqrt 2) ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
    have hs0 : Real.sqrt 2 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
    field_simp [hs0]
  change ‖(0 : ℂ)‖ ^ 2 + ‖(v / Real.sqrt 2 : ℂ)‖ ^ 2 = v ^ 2 / 2
  rw [hnorm]
  simp

def ewGeneratorAction (a₁ a₂ a₃ b : ℝ) (Φ : Fin 2 → ℂ) : Fin 2 → ℂ :=
  ![((a₁ - Complex.I * a₂) / 2 : ℂ) * Φ 1 + ((a₃ + b) / 2 : ℂ) * Φ 0,
    ((a₁ + Complex.I * a₂) / 2 : ℂ) * Φ 0 + ((-a₃ + b) / 2 : ℂ) * Φ 1]

theorem higgs_vacuum_stabilizer_iff {v a₁ a₂ a₃ b : ℝ} (hv : 0 < v) :
    ewGeneratorAction a₁ a₂ a₃ b (higgsVac v) = 0 ↔
      a₁ = 0 ∧ a₂ = 0 ∧ b = a₃ := by
  have hs : Real.sqrt 2 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
  constructor
  · intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp [ewGeneratorAction, higgsVac, hs] at h0 h1
    rcases h0 with h0 | h0
    · rcases h1 with h1 | h1
      · have hre : a₁ = 0 := by
          have := congrArg Complex.re h0
          norm_num at this
          nlinarith
        have him : a₂ = 0 := by
          have := congrArg Complex.im h0
          norm_num at this
          nlinarith
        have hb : b = a₃ := by
          have := congrArg Complex.re h1
          norm_num at this
          nlinarith
        exact ⟨hre, him, hb⟩
      · linarith
    · linarith
  · rintro ⟨rfl, rfl, rfl⟩
    funext i
    fin_cases i <;> simp [ewGeneratorAction, higgsVac]

/-- The doublet action in the standard two-complex-coordinate parametrization of
SU(2). The hypercharge circle coordinate is the phase acting on the doublet. -/
def ewGroupAction (α β ζ : ℂ) (Φ : Fin 2 → ℂ) : Fin 2 → ℂ :=
  ![ζ * (α * Φ 0 + β * Φ 1), ζ * (-star β * Φ 0 + star α * Φ 1)]

theorem higgs_group_stabilizer_iff {v : ℝ} {α β ζ : ℂ} (hv : 0 < v)
    (hunit : Complex.normSq α + Complex.normSq β = 1)
    (hphase : Complex.normSq ζ = 1) :
    ewGroupAction α β ζ (higgsVac v) = higgsVac v ↔ β = 0 ∧ ζ = α := by
  have hζ : ζ ≠ 0 := by
    intro h
    simp [h] at hphase
  have hn : (v / Real.sqrt 2 : ℂ) ≠ 0 := by
    apply div_ne_zero
    · exact_mod_cast hv.ne'
    · exact_mod_cast (show Real.sqrt 2 ≠ 0 by positivity)
  constructor
  · intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    change ζ * (α * 0 + β * (v / Real.sqrt 2 : ℂ)) = 0 at h0
    change ζ * (-star β * 0 + star α * (v / Real.sqrt 2 : ℂ)) =
      (v / Real.sqrt 2 : ℂ) at h1
    have hβ : β = 0 := by simpa [hζ, hn] using h0
    have hα : α * (starRingEnd ℂ) α = 1 := by
      rw [Complex.mul_conj]
      simpa [hβ] using congrArg Complex.ofReal hunit
    have hζα : ζ * star α = 1 := by
      apply mul_right_cancel₀ hn
      simpa [mul_assoc] using h1
    have hstar : (starRingEnd ℂ) α ≠ 0 := by
      intro hz
      rw [hz, mul_zero] at hα
      exact zero_ne_one hα
    exact ⟨hβ, mul_right_cancel₀ hstar (hζα.trans hα.symm)⟩
  · rintro ⟨rfl, rfl⟩
    have hα : ζ * (starRingEnd ℂ) ζ = 1 := by
      rw [Complex.mul_conj]
      exact_mod_cast hphase
    funext i
    fin_cases i <;> simp [ewGroupAction, higgsVac, ← mul_assoc, hα]

def gaugeDerivative (g gp v W₁ W₂ W₃ B : ℝ) : Fin 2 → ℂ :=
  ![(-Complex.I / 2) * (g * (W₁ - Complex.I * W₂)) * (v / Real.sqrt 2 : ℂ),
    (-Complex.I / 2) * (-g * W₃ + gp * B) * (v / Real.sqrt 2 : ℂ)]

theorem gaugeDerivative_eq_generator_action (g gp v W₁ W₂ W₃ B : ℝ) :
    gaugeDerivative g gp v W₁ W₂ W₃ B =
      (-Complex.I) • ewGeneratorAction (g * W₁) (g * W₂) (g * W₃) (gp * B) (higgsVac v) := by
  funext i
  fin_cases i <;> simp [gaugeDerivative, ewGeneratorAction, higgsVac] <;> ring

def ewMassQuadratic (g gp v W₁ W₂ W₃ B : ℝ) : ℝ :=
  2 * (‖gaugeDerivative g gp v W₁ W₂ W₃ B 0‖ ^ 2 +
    ‖gaugeDerivative g gp v W₁ W₂ W₃ B 1‖ ^ 2)

theorem ew_mass_quadratic_form (g gp v W₁ W₂ W₃ B : ℝ) :
    ewMassQuadratic g gp v W₁ W₂ W₃ B =
      g ^ 2 * v ^ 2 / 4 * (W₁ ^ 2 + W₂ ^ 2) + v ^ 2 / 4 * (g * W₃ - gp * B) ^ 2 := by
  unfold ewMassQuadratic gaugeDerivative
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [Complex.sq_norm, Complex.sq_norm]
  simp [Complex.normSq]
  have hs : (Real.sqrt 2) ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  have hs0 : Real.sqrt 2 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
  field_simp [hs0]
  rw [hs]
  ring

def cosW (g gp : ℝ) : ℝ := g / Real.sqrt (g ^ 2 + gp ^ 2)
def sinW (g gp : ℝ) : ℝ := gp / Real.sqrt (g ^ 2 + gp ^ 2)
def mWSq (g v : ℝ) : ℝ := g ^ 2 * v ^ 2 / 4
def mZSq (g gp v : ℝ) : ℝ := (g ^ 2 + gp ^ 2) * v ^ 2 / 4
def photonMode (g gp W₃ B : ℝ) : ℝ := sinW g gp * W₃ + cosW g gp * B
def zMode (g gp W₃ B : ℝ) : ℝ := cosW g gp * W₃ - sinW g gp * B

theorem ew_neutral_rotation_orthogonal {g gp W₃ B : ℝ}
    (h : 0 < g ^ 2 + gp ^ 2) :
    zMode g gp W₃ B ^ 2 + photonMode g gp W₃ B ^ 2 = W₃ ^ 2 + B ^ 2 := by
  unfold zMode photonMode cosW sinW
  have hs : 0 < Real.sqrt (g ^ 2 + gp ^ 2) := Real.sqrt_pos.2 h
  have hs2 : (Real.sqrt (g ^ 2 + gp ^ 2)) ^ 2 = g ^ 2 + gp ^ 2 :=
    Real.sq_sqrt h.le
  field_simp [hs.ne']
  nlinarith

theorem ew_mass_diagonalized {g gp v W₁ W₂ W₃ B : ℝ}
    (hsum : 0 < g ^ 2 + gp ^ 2) :
    ewMassQuadratic g gp v W₁ W₂ W₃ B =
      mWSq g v * (W₁ ^ 2 + W₂ ^ 2) + mZSq g gp v * zMode g gp W₃ B ^ 2 := by
  rw [ew_mass_quadratic_form]
  unfold mWSq mZSq zMode cosW sinW
  have hs : (Real.sqrt (g ^ 2 + gp ^ 2)) ^ 2 = g ^ 2 + gp ^ 2 :=
    Real.sq_sqrt hsum.le
  have hs0 : Real.sqrt (g ^ 2 + gp ^ 2) ≠ 0 := (Real.sqrt_pos.2 hsum).ne'
  field_simp [hs0]
  rw [hs]
  ring

/-- Mass matrix in the ordered real coordinates W₁, W₂, W₃, B. -/
def ewMassMatrix (g gp v : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![mWSq g v, 0, 0, 0;
     0, mWSq g v, 0, 0;
     0, 0, mWSq g v, -(g * gp * v ^ 2 / 4);
     0, 0, -(g * gp * v ^ 2 / 4), mWSq gp v]

theorem ew_gauge_mass_matrix (g gp v W₁ W₂ W₃ B : ℝ) :
    ewMassQuadratic g gp v W₁ W₂ W₃ B =
      dotProduct ![W₁, W₂, W₃, B] ((ewMassMatrix g gp v).mulVec ![W₁, W₂, W₃, B]) := by
  rw [ew_mass_quadratic_form]
  simp [ewMassMatrix, mWSq, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  ring

theorem ew_W_mass_sq (g gp v : ℝ) :
    (ewMassMatrix g gp v).mulVec ![1, 0, 0, 0] = mWSq g v • ![1, 0, 0, 0] ∧
    (ewMassMatrix g gp v).mulVec ![0, 1, 0, 0] = mWSq g v • ![0, 1, 0, 0] := by
  constructor <;> funext i <;> fin_cases i <;>
    simp [ewMassMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

theorem ew_photon_massless (g gp v : ℝ) :
    (ewMassMatrix g gp v).mulVec ![0, 0, sinW g gp, cosW g gp] = 0 := by
  funext i
  fin_cases i <;>
    simp [ewMassMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mWSq, sinW, cosW] <;> ring

theorem ew_Z_mass_sq (g gp v : ℝ) :
    (ewMassMatrix g gp v).mulVec ![0, 0, cosW g gp, -sinW g gp] =
      mZSq g gp v • ![0, 0, cosW g gp, -sinW g gp] := by
  funext i
  fin_cases i <;>
    simp [ewMassMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      mWSq, mZSq, sinW, cosW] <;> ring

theorem ew_mass_order {g gp v : ℝ} (hg : 0 < g) (hgp : 0 < gp) (hv : 0 < v) :
    0 < mWSq g v ∧ mWSq g v < mZSq g gp v := by
  refine ⟨by unfold mWSq; positivity, ?_⟩
  have hgap : 0 < gp ^ 2 * v ^ 2 / 4 := by positivity
  unfold mWSq mZSq
  nlinarith

theorem ew_custodial_rho_eq_one {g gp v : ℝ} (hg : 0 < g) (hv : 0 < v) :
    mWSq g v / (mZSq g gp v * cosW g gp ^ 2) = 1 := by
  unfold mWSq mZSq cosW
  have hsum : 0 < g ^ 2 + gp ^ 2 := by positivity
  have hs : (Real.sqrt (g ^ 2 + gp ^ 2)) ^ 2 = g ^ 2 + gp ^ 2 :=
    Real.sq_sqrt hsum.le
  have hs0 : Real.sqrt (g ^ 2 + gp ^ 2) ≠ 0 := (Real.sqrt_pos.2 hsum).ne'
  field_simp [hs0, hg.ne', hv.ne']
  rw [hs]

theorem ew_electric_charge_relations {g gp : ℝ} (hg : 0 < g) (hgp : 0 < gp) :
    g * sinW g gp = gp * cosW g gp ∧
      g * sinW g gp = g * gp / Real.sqrt (g ^ 2 + gp ^ 2) ∧
      (g * sinW g gp) ^ 2 = g ^ 2 * gp ^ 2 / (g ^ 2 + gp ^ 2) ∧
      (g * sinW g gp)⁻¹ ^ 2 = g⁻¹ ^ 2 + gp⁻¹ ^ 2 := by
  unfold sinW cosW
  have hsum : 0 < g ^ 2 + gp ^ 2 := by positivity
  have hs0 : Real.sqrt (g ^ 2 + gp ^ 2) ≠ 0 := (Real.sqrt_pos.2 hsum).ne'
  have hs2 : (Real.sqrt (g ^ 2 + gp ^ 2)) ^ 2 = g ^ 2 + gp ^ 2 :=
    Real.sq_sqrt hsum.le
  refine ⟨?_, ?_, ?_, ?_⟩
  · field_simp
  · field_simp
  · field_simp [hs0]
    rw [hs2]
  · field_simp [hg.ne', hgp.ne', hs0]
    rw [hs2]
    ring

def higgsFluctuation (v g₁ g₂ h g₃ : ℝ) : Fin 2 → ℂ :=
  ![((g₁ + Complex.I * g₂) / Real.sqrt 2 : ℂ),
    ((v + h + Complex.I * g₃) / Real.sqrt 2 : ℂ)]

theorem higgs_fluctuation_expansion (lam v g₁ g₂ h g₃ : ℝ) :
    higgsPotential lam v (higgsFluctuation v g₁ g₂ h g₃) =
      lam / 4 * (2 * v * h + h ^ 2 + g₁ ^ 2 + g₂ ^ 2 + g₃ ^ 2) ^ 2 := by
  unfold higgsPotential higgsFluctuation
  have hs : (Real.sqrt 2) ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  have hs0 : Real.sqrt 2 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
  rw [Complex.sq_norm, Complex.sq_norm]
  simp [Complex.normSq]
  field_simp [hs0]
  ring

theorem higgs_fluctuation_homogeneous_terms (lam v g₁ g₂ h g₃ : ℝ) :
    let q := h ^ 2 + g₁ ^ 2 + g₂ ^ 2 + g₃ ^ 2
    higgsPotential lam v (higgsFluctuation v g₁ g₂ h g₃) =
      lam * v ^ 2 * h ^ 2 + lam * v * h * q + lam / 4 * q ^ 2 := by
  dsimp
  rw [higgs_fluctuation_expansion]
  ring

private theorem second_deriv_square_quadratic (c a b : ℝ) :
    deriv (deriv (fun t : ℝ => c * (a * t + b * t ^ 2) ^ 2)) 0 = 2 * c * a ^ 2 := by
  have hq (x : ℝ) : HasDerivAt (fun t : ℝ => a * t + b * t ^ 2) (a + b * (2 * x)) x := by
    have hid : HasDerivAt (fun t : ℝ => t) 1 x := hasDerivAt_id x
    have h := HasDerivAt.add (hid.const_mul a) ((hid.fun_pow 2).const_mul b)
    change HasDerivAt ((fun t : ℝ => a * t) + (fun t : ℝ => b * t ^ 2)) _ x
    simpa using h
  have hfirst : deriv (fun t : ℝ => c * (a * t + b * t ^ 2) ^ 2) =
      fun t => c * (2 * (a * t + b * t ^ 2) * (a + b * (2 * t))) := by
    funext x
    simpa using (((hq x).fun_pow 2).const_mul c).deriv
  rw [hfirst]
  have hid : HasDerivAt (fun t : ℝ => t) 1 0 := hasDerivAt_id 0
  have hlin : HasDerivAt (fun t : ℝ => a + b * (2 * t)) (b * 2) 0 := by
    simpa using ((hid.const_mul 2).const_mul b).const_add a
  have h := (HasDerivAt.mul ((hq 0).const_mul 2) hlin).const_mul c
  have hd := h.deriv
  convert hd using 1
  norm_num
  ring

/-- Second directional derivative along any real fluctuation of the doublet. -/
theorem higgs_hessian_diagonal (lam v g₁ g₂ h g₃ : ℝ) :
    deriv (deriv (fun t => higgsPotential lam v
      (higgsFluctuation v (t * g₁) (t * g₂) (t * h) (t * g₃)))) 0 =
      (2 * lam * v ^ 2) * h ^ 2 := by
  have heq : (fun t : ℝ => higgsPotential lam v
      (higgsFluctuation v (t * g₁) (t * g₂) (t * h) (t * g₃))) =
      (fun t => lam / 4 * ((2 * v * h) * t + (h ^ 2 + g₁ ^ 2 + g₂ ^ 2 + g₃ ^ 2) * t ^ 2) ^ 2) := by
    funext t
    rw [higgs_fluctuation_expansion]
    ring
  rw [heq, second_deriv_square_quadratic]
  ring

theorem higgs_hessian_spectrum {lam v : ℝ} (hlam : 0 < lam) (hv : 0 < v) :
    deriv (deriv (fun h => higgsPotential lam v (higgsFluctuation v 0 0 h 0))) 0 =
      2 * lam * v ^ 2 ∧
    deriv (deriv (fun x => higgsPotential lam v (higgsFluctuation v x 0 0 0))) 0 = 0 ∧
    deriv (deriv (fun x => higgsPotential lam v (higgsFluctuation v 0 x 0 0))) 0 = 0 ∧
    deriv (deriv (fun x => higgsPotential lam v (higgsFluctuation v 0 0 0 x))) 0 = 0 ∧
    0 < 2 * lam * v ^ 2 := by
  refine ⟨?_, ?_, ?_, ?_, by positivity⟩
  · simpa using higgs_hessian_diagonal lam v 0 0 1 0
  · simpa using higgs_hessian_diagonal lam v 1 0 0 0
  · simpa using higgs_hessian_diagonal lam v 0 1 0 0
  · simpa using higgs_hessian_diagonal lam v 0 0 0 1

end D5.S3.Quantum.Gauge.ElectroweakHiggsMechanism4D
