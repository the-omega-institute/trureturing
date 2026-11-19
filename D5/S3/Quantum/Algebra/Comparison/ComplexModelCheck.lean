import D5.S3.Quantum.Algebra.Comparison.RoundTripComparison
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Complex.Basic

open Filter Asymptotics
open scoped Topology
open D5.S3.Quantum.Algebra.Comparison.RoundTripComparison

noncomputable section
attribute [local instance 100] LieRing.ofAssociativeRing
set_option backward.isDefEq.respectTransparency false

namespace ComplexComparisonCheck

def imaginary : LieSubalgebra ℝ ℂ :=
  { Complex.reLm.ker with
    lie_mem' := by
      intro x y hx hy
      change (x * y - y * x).re = 0
      simp [mul_comm] }

def circle : Subgroup ℂˣ where
  carrier := {u | ‖(u : ℂ)‖ = 1}
  one_mem' := by simp
  mul_mem' := by
    intro u v hu hv
    change ‖((u : ℂ) * (v : ℂ))‖ = 1
    rw [norm_mul, hu, hv, one_mul]
  inv_mem' := by
    intro u hu
    change ‖((u⁻¹ : ℂˣ) : ℂ)‖ = 1
    rw [Units.val_inv_eq_inv_val, norm_inv, hu, inv_one]

def halfImag : LinearMap.BilinForm ℝ imaginary where
  toFun X :=
    { toFun := fun Y => (X : ℂ).im * (Y : ℂ).im / 2
      map_add' := by intros; simp; ring
      map_smul' := by intros; simp; ring }
  map_add' := by intros; ext; simp; ring
  map_smul' := by intros; ext; simp; ring

def phi (g : circle) : ℝ := (1 + (((g : ℂˣ) : ℂ)).re) / 2

private theorem imaginary_re (X : imaginary) : (X : ℂ).re = 0 := X.property

private theorem imaginary_norm (X : imaginary) : (X : ℂ).im ^ 2 = ‖X‖ ^ 2 := by
  have hh := Complex.sq_norm_sub_sq_re (X : ℂ)
  simpa [imaginary_re] using hh.symm

private theorem circle_norm (g : circle) :
    (((g : ℂˣ) : ℂ)).re ^ 2 + (((g : ℂˣ) : ℂ)).im ^ 2 = 1 := by
  have hh := Complex.sq_norm (((g : ℂˣ) : ℂ))
  rw [g.property, one_pow] at hh
  simpa only [Complex.normSq_apply, pow_two] using hh.symm

private theorem exp_mem (X : imaginary) : expUnit (X : ℂ) ∈ circle := by
  change ‖NormedSpace.exp (X : ℂ)‖ = 1
  rw [← Complex.exp_eq_exp_ℂ, Complex.norm_exp, imaginary_re, Real.exp_zero]

def model : Data imaginary circle where
  exp_mem := exp_mem
  conj_mem := by
    intro g X
    have he : (g : ℂˣ) * (X : ℂ) * ↑((g : ℂˣ)⁻¹) = (X : ℂ) := by
      calc
        _ = ((g : ℂˣ) * ↑((g : ℂˣ)⁻¹) : ℂ) * (X : ℂ) := by ring
        _ = (X : ℂ) := by rw [Units.mul_inv, one_mul]
    rw [he]
    exact X.property
  phi := phi
  h := halfImag
  symmetric := by
    constructor
    intro X Y
    change (X : ℂ).im * (Y : ℂ).im / 2 = (Y : ℂ).im * (X : ℂ).im / 2
    ring
  bounded := by
    intro g
    have hb := Complex.abs_re_le_norm (((g : ℂˣ) : ℂ))
    rw [g.property] at hb
    obtain ⟨hl, hu⟩ := abs_le.mp hb
    change 0 ≤ (1 + (((g : ℂˣ) : ℂ)).re) / 2 ∧
      (1 + (((g : ℂˣ) : ℂ)).re) / 2 ≤ 1
    constructor <;> linarith
  faithful := by
    intro g
    constructor
    · intro hg
      change (1 + (((g : ℂˣ) : ℂ)).re) / 2 = 1 at hg
      have hre : (((g : ℂˣ) : ℂ)).re = 1 := by linarith
      have him : (((g : ℂˣ) : ℂ)).im = 0 := by
        have hs : (((g : ℂˣ) : ℂ)).im ^ 2 = 0 := by nlinarith [circle_norm g]
        exact sq_eq_zero_iff.mp hs
      apply Subtype.ext
      apply Units.ext
      apply Complex.ext
      · simpa using hre
      · simpa using him
    · rintro rfl
      norm_num [phi]
  duplication := by
    intro g
    change (1 + ((((g : ℂˣ) : ℂ)) * (((g : ℂˣ) : ℂ))).re) / 2 =
      (2 * ((1 + (((g : ℂˣ) : ℂ)).re) / 2) - 1) ^ 2
    rw [Complex.mul_re]
    nlinarith [circle_norm g]
  conjugation := by
    intro g k
    have hk : k * g * k⁻¹ = g := by simp [mul_comm, mul_left_comm, mul_assoc]
    rw [hk]
  expansion := by
    have ht : Tendsto (fun X : imaginary => (X : ℂ).im) (𝓝 0) (𝓝 0) := by
      simpa using! (Complex.continuous_im.comp continuous_subtype_val).tendsto
        (0 : imaginary)
    have hr :=
      (D5.S3.Analytic.Dilation.DuplicationQuadraticGerm.cosine_quadratic_germ 1).comp_tendsto ht
    have hh := hr.const_mul_left (1 / 2 : ℝ)
    refine hh.congr (fun X => ?_) (fun X => ?_)
    · change (1 / 2 : ℝ) * (Real.cos (1 * (X : ℂ).im) -
          (1 - (1 ^ 2 / 2) * (X : ℂ).im ^ 2)) =
        (1 + (NormedSpace.exp (X : ℂ)).re) / 2 -
          (1 - ((X : ℂ).im * (X : ℂ).im / 2) / 2)
      rw [← Complex.exp_eq_exp_ℂ, Complex.exp_re, imaginary_re, Real.exp_zero]
      ring
    · exact imaginary_norm X

example : ∃ (D : Data imaginary circle) (X : imaginary), X ≠ 0 := by
  refine ⟨model, ⟨Complex.I, by change Complex.I.re = 0; simp⟩, ?_⟩
  intro h
  have hh := congrArg (fun X : imaginary => (X : ℂ)) h
  exact Complex.I_ne_zero hh

#print axioms ComplexComparisonCheck.model

end ComplexComparisonCheck
