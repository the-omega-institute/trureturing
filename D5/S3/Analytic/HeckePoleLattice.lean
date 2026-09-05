/- GID: D5/S3/Analytic/HeckePoleLattice
   generality: G
   mirror-B: D5/B/S3/Analytic/HeckePoleLattice
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A Hecke factor has exactly the regulator-spaced simple-pole lattice. -/

import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Tactic

namespace D5.S3.Analytic.HeckePoleLattice

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Set

noncomputable section

/-- The `n`-th point on the `k`-th regulator-spaced vertical line. Allowing
`n : Int` includes both signs in the source's `plus-or-minus` notation. -/
def heckePole (eta : Real) (k : Nat) (n : Int) : Complex :=
  -(2 * (k : Complex)) +
    (n : Complex) * (2 * (Real.pi : Complex) * Complex.I) /
      (Real.log eta : Complex)

/-- The entire denominator whose reciprocal is the Hecke-type meromorphic
factor on the `k`-th line. -/
def heckeDenominator (eta : Real) (k : Nat) (s : Complex) : Complex :=
  1 - Complex.exp ((s + 2 * (k : Complex)) * (Real.log eta : Complex))

/-- A model Hecke factor with its logarithmically periodic pole line exposed. -/
def heckeFactor (eta : Real) (k : Nat) (s : Complex) : Complex :=
  (heckeDenominator eta k s)⁻¹

private theorem denominator_analytic (eta : Real) (k : Nat) (s : Complex) :
    AnalyticAt Complex (heckeDenominator eta k) s := by
  unfold heckeDenominator
  exact analyticAt_const.sub
    ((by fun_prop : AnalyticAt Complex
      (fun z : Complex =>
        (z + 2 * (k : Complex)) * (Real.log eta : Complex)) s).cexp')

private theorem denominator_zero_iff (eta : Real) (heta : 1 < eta)
    (k : Nat) (s : Complex) :
    heckeDenominator eta k s = 0 ↔ exists n : Int, s = heckePole eta k n := by
  have hlog : Real.log eta ≠ 0 := (Real.log_pos heta).ne'
  have hlogC : (Real.log eta : Complex) ≠ 0 := by exact_mod_cast hlog
  rw [heckeDenominator, sub_eq_zero]
  constructor
  · intro hone
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp hone.symm
    refine ⟨n, ?_⟩
    have hsadd :
        s + 2 * (k : Complex) =
          (n : Complex) * (2 * (Real.pi : Complex) * Complex.I) /
            (Real.log eta : Complex) :=
      (eq_div_iff hlogC).2 hn
    unfold heckePole
    linear_combination hsadd
  · rintro ⟨n, rfl⟩
    apply Eq.symm
    rw [Complex.exp_eq_one_iff]
    refine ⟨n, ?_⟩
    unfold heckePole
    field_simp [hlogC]
    ring

private theorem factor_order_eq_neg_one_iff (eta : Real) (heta : 1 < eta)
    (k : Nat) (s : Complex) :
    meromorphicOrderAt (heckeFactor eta k) s = (-1 : Int) ↔
      heckeDenominator eta k s = 0 := by
  have hlog : Real.log eta ≠ 0 := (Real.log_pos heta).ne'
  have hlogC : (Real.log eta : Complex) ≠ 0 := by exact_mod_cast hlog
  have hanalytic := denominator_analytic eta k s
  unfold heckeFactor
  change meromorphicOrderAt ((heckeDenominator eta k)⁻¹) s = (-1 : Int) ↔
    heckeDenominator eta k s = 0
  rw [meromorphicOrderAt_inv, hanalytic.meromorphicOrderAt_eq]
  by_cases hzero : heckeDenominator eta k s = 0
  · have hinnerDifferentiable : DifferentiableAt Complex
        (fun z : Complex =>
          (z + 2 * (k : Complex)) * (Real.log eta : Complex))
        s := by
      fun_prop
    have hinnerDeriv :
        deriv (fun z : Complex =>
          (z + 2 * (k : Complex)) * (Real.log eta : Complex)) s =
            (Real.log eta : Complex) := by
      simp [deriv_mul_const_field, deriv_add_const, deriv_id'']
    have hconstantDifferentiable : DifferentiableAt Complex
        (fun _ : Complex => (1 : Complex)) s :=
      differentiableAt_const (c := (1 : Complex))
    have hdenominatorDeriv : deriv (heckeDenominator eta k) s =
        -(Complex.exp
            ((s + 2 * (k : Complex)) * (Real.log eta : Complex)) *
              (Real.log eta : Complex)) := by
      unfold heckeDenominator
      rw [deriv_fun_sub hconstantDifferentiable hinnerDifferentiable.cexp,
        deriv_const, deriv_cexp hinnerDifferentiable, hinnerDeriv, zero_sub]
    have hexp :
        Complex.exp
          ((s + 2 * (k : Complex)) * (Real.log eta : Complex)) = 1 := by
      have hzero' := hzero
      unfold heckeDenominator at hzero'
      exact (sub_eq_zero.mp hzero').symm
    have hderiv : deriv (heckeDenominator eta k) s ≠ 0 := by
      rw [hdenominatorDeriv, hexp]
      simp [hlogC]
    rw [hanalytic.analyticOrderAt_eq_one_of_zero_deriv_ne_zero hzero hderiv]
    simp [hzero]
  · rw [hanalytic.analyticOrderAt_eq_zero.mpr hzero]
    simp [hzero]

/-- **Hecke pole lattice.** For every `eta > 1`, all factors
`P_k(s) = (1 - exp ((s + 2k) log eta))⁻¹` are meromorphic on the whole
complex plane. Their poles are all simple, and their exact locations are
`-2k + 2 pi i n / log eta` for integers `n`; thus the imaginary spacing is
set by the logarithmic regulator. -/
theorem hecke_pole_lattice (eta : Real) (heta : 1 < eta) :
    (forall k : Nat, MeromorphicOn (heckeFactor eta k) univ) ∧
      forall (k : Nat) (s : Complex),
        meromorphicOrderAt (heckeFactor eta k) s = (-1 : Int) ↔
          exists n : Int, s = heckePole eta k n := by
  constructor
  · intro k s _
    exact (denominator_analytic eta k s).meromorphicAt.inv
  · intro k s
    rw [factor_order_eq_neg_one_iff eta heta k s,
      denominator_zero_iff eta heta k s]

#print axioms hecke_pole_lattice

end

end D5.S3.Analytic.HeckePoleLattice
