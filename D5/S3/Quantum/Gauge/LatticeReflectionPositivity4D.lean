/- GID: D5/S3/Quantum/Gauge/LatticeReflectionPositivity4D
   generality: G
   mirror-B: D5/B/S3/Quantum/Gauge/LatticeReflectionPositivity4D
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Reflection positivity of finite Wilson lattice gauge theory and planar Wilson-loop bounds. -/

import OmegaBuild.Commands
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
open scoped BigOperators ComplexConjugate
noncomputable section

namespace D5.S3.Quantum.Gauge.LatticeReflectionPositivity4D

section Abstract

variable {X ι : Type*} [Fintype X] [Fintype ι]

/-- The pairing for reflection exchanging two copies of the half configuration space. -/
def reflectionPairing (K : X → X → ℝ) (f g : X → ℂ) : ℂ :=
  ∑ x, ∑ y, (K x y : ℂ) * (star (f y) * g x)

/-- The unperturbed pairing is a single squared norm. -/
theorem product_reflection_positivity (w : X → ℝ) (f : X → ℂ) :
    reflectionPairing (fun x y => w x * w y) f f =
      (↑(‖∑ x, (w x : ℂ) * f x‖ ^ 2) : ℂ) := by
  rw [Complex.sq_norm, ← Complex.mul_conj]
  simp only [map_sum, map_mul, Complex.conj_ofReal, reflectionPairing, Complex.ofReal_mul,
    Finset.sum_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  rw [Complex.star_def]
  ring

/-- The real part of a Hermitian finite feature kernel. -/
def interaction (A : ι → X → ℂ) (c : ι → ℝ) (x y : X) : ℝ :=
  ∑ i, c i * (A i x * star (A i y)).re

private def realFeature (A : ι → X → ℂ) (c : ι → ℝ) (i : ι × Bool) (x : X) : ℝ :=
  Real.sqrt (c i.1) * if i.2 then (A i.1 x).re else (A i.1 x).im

omit [Fintype X] in
private theorem interaction_gram (A : ι → X → ℂ) (c : ι → ℝ) (hc : ∀ i, 0 ≤ c i) (x y : X) :
    interaction A c x y = ∑ i : ι × Bool, realFeature A c i x * realFeature A c i y := by
  rw [interaction, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Fintype.sum_bool, realFeature, Bool.false_eq_true, ite_false, ite_true,
    Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  calc
    _ = c i * ((A i x).im * (A i y).im + (A i x).re * (A i y).re) := by ring
    _ = _ := by
      conv_lhs => rw [← Real.sq_sqrt (hc i)]
      ring

private theorem pairing_gram {J : Type*} [Fintype J] (B : J → X → ℝ)
    (w : X → ℝ) (f : X → ℂ) :
    reflectionPairing (fun x y => w x * w y * ∑ j, B j x * B j y) f f =
      ∑ j, (↑(‖∑ x, ((w x * B j x : ℝ) : ℂ) * f x‖ ^ 2) : ℂ) := by
  let term (x y : X) (j : J) :=
    (((w x * B j x) * (w y * B j y) : ℝ) : ℂ) * (star (f y) * f x)
  calc
    _ = ∑ x, ∑ y, ∑ j, term x y j := by
      unfold reflectionPairing
      refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
      simp only [term, Complex.ofReal_mul, Complex.ofReal_sum, Finset.mul_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl fun _ _ => by ring
    _ = ∑ j, ∑ x, ∑ y, term x y j := by
      have h (x : X) : (∑ y, ∑ j, term x y j) = ∑ j, ∑ y, term x y j := Finset.sum_comm
      simp_rw [h]
      exact Finset.sum_comm
    _ = _ := by simp_rw [← product_reflection_positivity, reflectionPairing, term]

/-- Every nonnegative integer power of the interaction preserves reflection positivity. -/
theorem factorized_interaction_pow_rp (w : X → ℝ) (A : ι → X → ℂ) (c : ι → ℝ)
    (hc : ∀ i, 0 ≤ c i) (n : ℕ) (f : X → ℂ) :
    0 ≤ (reflectionPairing (fun x y => w x * w y * interaction A c x y ^ n) f f).re ∧
      (reflectionPairing (fun x y => w x * w y * interaction A c x y ^ n) f f).im = 0 := by
  have h x y : interaction A c x y ^ n =
      ∑ p : Fin n → ι × Bool, (∏ i, realFeature A c (p i) x) * (∏ i, realFeature A c (p i) y) := by
    rw [interaction_gram A c hc, Fintype.sum_pow]
    simp_rw [Finset.prod_mul_distrib]
  simp_rw [h, pairing_gram, Complex.re_sum, Complex.im_sum, Complex.ofReal_re, Complex.ofReal_im]
  exact ⟨Finset.sum_nonneg fun _ _ => sq_nonneg _, by simp⟩

/-- The Wilson-type Boltzmann factor built from two copies of the half action. -/
def boltzmann (S : X → ℝ) (A : ι → X → ℂ) (c : ι → ℝ) (β : ℝ) (x y : X) : ℝ :=
  Real.exp (β * (S x + S y + interaction A c x y))

/-- The exponential of a nonnegatively coupled real feature interaction is reflection positive. -/
theorem exponential_boltzmann_reflection_positivity
    (w : X → ℝ) (S : X → ℝ) (A : ι → X → ℂ) (c : ι → ℝ) (β : ℝ)
    (hc : ∀ i, 0 ≤ c i) (hβ : 0 ≤ β) (f : X → ℂ) :
    0 ≤ (reflectionPairing (fun x y => w x * w y * boltzmann S A c β x y) f f).re ∧
      (reflectionPairing (fun x y => w x * w y * boltzmann S A c β x y) f f).im = 0 := by
  let u x := w x * Real.exp (β * S x)
  have hw x y : w x * w y * boltzmann S A c β x y =
      u x * u y * Real.exp (β * interaction A c x y) := by
    simp only [boltzmann, mul_add, Real.exp_add, u]
    ring
  simp_rw [hw]
  let K (n : ℕ) x y := u x * u y * interaction A c x y ^ n
  let a (n : ℕ) := β ^ n / (n.factorial : ℝ)
  have h x y : HasSum (fun n => a n * K n x y)
      (u x * u y * Real.exp (β * interaction A c x y)) := by
    rw [Real.exp_eq_exp_ℝ]
    convert (NormedSpace.expSeries_div_hasSum_exp (β * interaction A c x y)).mul_left (u x * u y) using 1
    ext n
    dsimp [a, K]
    rw [mul_pow]
    ring
  have hs (part : ℂ → ℝ) (hp : ∀ r : ℝ, ∀ z : ℂ, part ((r : ℂ) * z) = r * part z) :
      HasSum (fun n => ∑ x, ∑ y, a n * part ((K n x y : ℂ) * (star (f y) * f x)))
        (∑ x, ∑ y, u x * u y * Real.exp (β * interaction A c x y) * part (star (f y) * f x)) := by
    simp_rw [hp, ← mul_assoc]
    exact hasSum_sum fun x _ => hasSum_sum fun y _ => (h x y).mul_right _
  have hre : ∀ (r : ℝ) (z : ℂ), ((r : ℂ) * z).re = r * z.re := by
    simp [Complex.mul_re]
  have him : ∀ (r : ℝ) (z : ℂ), ((r : ℂ) * z).im = r * z.im := by
    simp [Complex.mul_im]
  have hr := hs Complex.re hre
  have hi := hs Complex.im him
  simp_rw [← Finset.mul_sum] at hr hi
  simp only [reflectionPairing, Complex.re_sum, Complex.im_sum, hre, him]
  constructor
  · rw [← hr.tsum_eq]
    exact tsum_nonneg fun n => mul_nonneg (div_nonneg (pow_nonneg hβ _) (by positivity))
      (by simpa only [reflectionPairing, Complex.re_sum] using
        (factorized_interaction_pow_rp u A c hc n f).1)
  · rw [← hi.tsum_eq]
    have hn n : (∑ x, ∑ y, ((K n x y : ℂ) * (star (f y) * f x)).im) = 0 := by
      simpa only [reflectionPairing, Complex.im_sum] using
        (factorized_interaction_pow_rp u A c hc n f).2
    simp only [hn, mul_zero, tsum_zero]

/-- On two configurations the sign observable has exactly the indicated negative pairing. -/
theorem negative_coupling_rp_counterexample (β : ℝ) (hβ : β < 0) :
    let f : Bool → ℂ := fun x => if x then 1 else -1
    let z := reflectionPairing (boltzmann (fun _ => 0) (fun _ : Unit => f) (fun _ => 1) β) f f
    z = (↑(4 * Real.sinh β) : ℂ) ∧ (4 * Real.sinh β : ℝ) < 0 := by
  dsimp
  constructor
  · simp [reflectionPairing, boltzmann, interaction, Real.sinh_eq]
    ring
  · rw [Real.sinh_eq]
    have h := Real.exp_lt_exp.mpr (show β < -β by linarith)
    linarith

private theorem reflectionPairing_cauchy_schwarz (K : X → X → ℝ)
    (hs : ∀ x y, K x y = K y x) (hp : ∀ f, 0 ≤ (reflectionPairing K f f).re)
    (f g : X → ℂ) :
    ‖reflectionPairing K f g‖ ^ 2 ≤ (reflectionPairing K f f).re * (reflectionPairing K g g).re := by
  let core : PreInnerProductSpace.Core ℂ (X → ℂ) :=
    { inner := reflectionPairing K
      conj_inner_symm := fun u v => by
        simp only [reflectionPairing, map_sum, map_mul, Complex.conj_ofReal,
          Complex.star_def, Complex.conj_conj]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
        rw [hs y x, mul_comm (v x)]
      re_inner_nonneg := hp
      add_left := fun u v z => by
        simp only [reflectionPairing, Pi.add_apply, star_add, add_mul, mul_add, Finset.sum_add_distrib]
      smul_left := fun u v r => by
        simp only [reflectionPairing, Pi.smul_apply, smul_eq_mul, star_mul', Complex.star_def,
          Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
        ring }
  let _ : PreInnerProductSpace.Core ℂ (X → ℂ) := core
  have h := InnerProductSpace.Core.inner_mul_inner_self_le (𝕜 := ℂ) f g
  rw [InnerProductSpace.Core.norm_inner_symm (𝕜 := ℂ) g f] at h
  rw [pow_two]
  exact h

end Abstract

end D5.S3.Quantum.Gauge.LatticeReflectionPositivity4D
