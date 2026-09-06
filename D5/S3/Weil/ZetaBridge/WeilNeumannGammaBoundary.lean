/- GID: D5/S3/Weil/ZetaBridge/WeilNeumannGammaBoundary
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaBridge/WeilNeumannGammaBoundary
   mirror-E: none(waiver:resolvent-kernel-and-canonical-Gamma-mixture)
   anchors: []
   digest: The actual Neumann-minus-free Laplace resolvent kernel has a positive rank-two boundary completion, including every finite canonical Gamma mixture. -/

import D5.S3.Weil.ZetaBridge.WeilArithmeticCouplingJet
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Neumann completion of the canonical Gamma resolvent

For `a > 0`, `b > 0` and `x,y` in `[-a,a]`, `neumannLaplaceKernel`
is `2*b` times the Green kernel of the Neumann realization of
`-d^2/dx^2 + b^2`. `freeLaplaceKernel` is `2*b` times the compressed
whole-line resolvent kernel. Their formulas are specified independently.

The positive rank-two factorization is proved below, rather than used as
the definition of the Neumann kernel. The last theorem specializes the
rates to `2*r + 1/2`, which are precisely the rates in the repository's
actual arithmetic Gamma boundary series.

The Green-operator interpretation, integration against L2 functions,
passage through the infinite positive Gamma mixture, and the resulting
energy-weighted arithmetic Schur inequality are paper steps. They are not
claimed to be formalized by this file. Lean elaboration has not been run.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.Weil.ZetaBridge.WeilNeumannGammaBoundary

open scoped BigOperators

/-- Twice the rate times the compressed whole-line resolvent kernel. -/
def freeLaplaceKernel (b x y : ℝ) : ℝ :=
  Real.exp (-b * |x - y|)

/-- Twice the rate times the Neumann Green kernel, in exponential coordinates.
On the interval it equals
`2*cosh(b*(min x y+a))*cosh(b*(a-max x y))/sinh(2*b*a)`. -/
def neumannLaplaceKernel (a b x y : ℝ) : ℝ :=
  let E := Real.exp (b * a)
  let u := Real.exp (b * min x y)
  let v := Real.exp (b * max x y)
  ((E * u + E⁻¹ * u⁻¹) * (E * v⁻¹ + E⁻¹ * v)) /
    (E ^ 2 - (E⁻¹) ^ 2)

/-- Twice the even hyperbolic boundary response. -/
def evenBoundaryResponse (b x : ℝ) : ℝ :=
  Real.exp (b * x) + (Real.exp (b * x))⁻¹

/-- Twice the odd hyperbolic boundary response. -/
def oddBoundaryResponse (b x : ℝ) : ℝ :=
  Real.exp (b * x) - (Real.exp (b * x))⁻¹

private theorem scalar_green_completion
    {E u v : ℝ} (hE : 1 < E) (hu : u ≠ 0) (hv : v ≠ 0) :
    ((E * u + E⁻¹ * u⁻¹) * (E * v⁻¹ + E⁻¹ * v)) /
        (E ^ 2 - (E⁻¹) ^ 2) - u / v =
      ((u + u⁻¹) * (v + v⁻¹)) / (2 * (E ^ 2 - 1)) +
      ((u - u⁻¹) * (v - v⁻¹)) / (2 * (E ^ 2 + 1)) := by
  have hEp : 0 < E := by linarith
  have hE0 : E ≠ 0 := ne_of_gt hEp
  have hs : 0 < E ^ 2 - 1 := by nlinarith
  have hp : 0 < E ^ 2 + 1 := by positivity
  have hdid : E ^ 2 - (E⁻¹) ^ 2 =
      ((E ^ 2 - 1) * (E ^ 2 + 1)) / E ^ 2 := by
    field_simp [hE0]
    <;> ring
  have hd : E ^ 2 - (E⁻¹) ^ 2 ≠ 0 := by
    rw [hdid]
    exact ne_of_gt (div_pos (mul_pos hs hp) (pow_pos hEp 2))
  field_simp [hE0, hu, hv, hd, ne_of_gt hs, ne_of_gt hp]
  <;> ring

/-- The independently specified two Green kernels differ by an explicit
positive rank-two completion. This algebraic identity holds for all x,y;
the Green-operator interpretation uses x,y in the original interval. -/
theorem neumann_laplace_boundary_completion
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (x y : ℝ) :
    neumannLaplaceKernel a b x y - freeLaplaceKernel b x y =
      evenBoundaryResponse b x * evenBoundaryResponse b y /
        (2 * ((Real.exp (b * a)) ^ 2 - 1)) +
      oddBoundaryResponse b x * oddBoundaryResponse b y /
        (2 * ((Real.exp (b * a)) ^ 2 + 1)) := by
  have hE : 1 < Real.exp (b * a) :=
    Real.one_lt_exp_iff.mpr (mul_pos hb ha)
  rcases le_total x y with hxy | hyx
  · have hf : freeLaplaceKernel b x y =
        Real.exp (b * x) / Real.exp (b * y) := by
      unfold freeLaplaceKernel
      rw [abs_of_nonpos (sub_nonpos.mpr hxy)]
      have he : -b * -(x - y) = b * x - b * y := by ring
      rw [he, Real.exp_sub]
    rw [hf]
    simpa only [neumannLaplaceKernel, min_eq_left hxy, max_eq_right hxy,
      evenBoundaryResponse, oddBoundaryResponse] using
      scalar_green_completion hE (Real.exp_ne_zero (b * x))
        (Real.exp_ne_zero (b * y))
  · have hf : freeLaplaceKernel b x y =
        Real.exp (b * y) / Real.exp (b * x) := by
      unfold freeLaplaceKernel
      rw [abs_of_nonneg (sub_nonneg.mpr hyx)]
      have he : -b * (x - y) = b * y - b * x := by ring
      rw [he, Real.exp_sub]
    rw [hf]
    simpa only [neumannLaplaceKernel, min_eq_right hyx, max_eq_left hyx,
      evenBoundaryResponse, oddBoundaryResponse, mul_comm] using
      scalar_green_completion hE (Real.exp_ne_zero (b * y))
        (Real.exp_ne_zero (b * x))

private theorem finite_rank_one_energy
    {ι : Type*} (S : Finset ι) (v h : ι → ℝ) (D : ℝ) :
    (∑ i ∈ S, ∑ j ∈ S, v i * (h i * h j / D) * v j) =
      (∑ i ∈ S, v i * h i) ^ 2 / D := by
  calc
    _ = ∑ i ∈ S, ∑ j ∈ S,
        (v i * h i) * (v j * h j) * D⁻¹ := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = (∑ i ∈ S, (v i * h i) * (∑ j ∈ S, v j * h j)) * D⁻¹ := by
      simp only [Finset.sum_mul, Finset.mul_sum]
    _ = ((∑ i ∈ S, v i * h i) * (∑ j ∈ S, v j * h j)) * D⁻¹ := by
      rw [Finset.sum_mul]
    _ = _ := by ring

/-- Full finite quadratic identity. Both boundary directions remain present;
there is no parity condition or vanishing-boundary assumption on the data. -/
theorem neumann_laplace_boundary_energy
    {ι : Type*} (S : Finset ι) (x v : ι → ℝ)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (∑ i ∈ S, ∑ j ∈ S,
      v i * (neumannLaplaceKernel a b (x i) (x j) -
        freeLaplaceKernel b (x i) (x j)) * v j) =
      (∑ i ∈ S, v i * evenBoundaryResponse b (x i)) ^ 2 /
        (2 * ((Real.exp (b * a)) ^ 2 - 1)) +
      (∑ i ∈ S, v i * oddBoundaryResponse b (x i)) ^ 2 /
        (2 * ((Real.exp (b * a)) ^ 2 + 1)) := by
  simp_rw [neumann_laplace_boundary_completion ha hb,
    mul_add, add_mul, Finset.sum_add_distrib]
  rw [finite_rank_one_energy, finite_rank_one_energy]

/-- Positivity of the actual Neumann-minus-free resolvent kernel. -/
theorem neumann_laplace_boundary_energy_nonneg
    {ι : Type*} (S : Finset ι) (x v : ι → ℝ)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    0 ≤ ∑ i ∈ S, ∑ j ∈ S,
      v i * (neumannLaplaceKernel a b (x i) (x j) -
        freeLaplaceKernel b (x i) (x j)) * v j := by
  rw [neumann_laplace_boundary_energy S x v ha hb]
  have hE : 1 < Real.exp (b * a) :=
    Real.one_lt_exp_iff.mpr (mul_pos hb ha)
  have hs : 0 < (Real.exp (b * a)) ^ 2 - 1 := by nlinarith
  exact add_nonneg (div_nonneg (sq_nonneg _) (by positivity))
    (div_nonneg (sq_nonneg _) (by positivity))

/-- Every finite mixture at the canonical Gamma rates has a positive boundary
correction. Infinite-mixture convergence and L2 integration are separate
analytic bridges, not hidden assumptions of this finite theorem. -/
theorem canonical_gamma_resolvent_boundary_nonneg
    {ι : Type*} (S : Finset ι) (x v : ι → ℝ)
    {a : ℝ} (ha : 0 < a) (R : ℕ) :
    0 ≤ ∑ r ∈ Finset.range R, ∑ i ∈ S, ∑ j ∈ S,
      v i * (neumannLaplaceKernel a (2 * (r : ℝ) + 1 / 2) (x i) (x j) -
        freeLaplaceKernel (2 * (r : ℝ) + 1 / 2) (x i) (x j)) * v j := by
  apply Finset.sum_nonneg
  intro r hr
  exact neumann_laplace_boundary_energy_nonneg S x v ha (by positivity)

#print axioms neumann_laplace_boundary_completion
#print axioms neumann_laplace_boundary_energy
#print axioms canonical_gamma_resolvent_boundary_nonneg

end D5.S3.Weil.ZetaBridge.WeilNeumannGammaBoundary
