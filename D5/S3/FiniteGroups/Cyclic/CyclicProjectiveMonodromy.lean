/- GID: D5/S3/FiniteGroups/Cyclic/CyclicProjectiveMonodromy
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/Cyclic/CyclicProjectiveMonodromy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.RingTheory.RootsOfUnity.Complex]
   utility: none
   digest: Projective powers detect the ambient cyclic associator product. -/

import D5.S3.FiniteGroups.Cyclic.CyclicAssociatorObstruction
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Tactic.Ring
import OmegaBuild.Commands

/-!
For `x, y` in the centralizer of `g`, use the slant multiplier
`α g x y * α x y g / α x g y` in the law `T x * T y = c_g(x, y) • T (x * y)`,
with the unit scalar coerced to `ℂ`. At `y = g` the last two factors cancel,
so for `x = g ^ i` the multiplier is `α g (g ^ i) g`. Only these products
and `T 1 = 1` enter the power comparison.

In the order-three application, a nonzero vector with conformal monodromy
`exp (2πiρ)` at `ρ = 16/9 + n/3` determines the cyclic product of this same
`α` as the primitive third root `exp (2πi/3)`. Application to the VOA still
requires identifying `T` on the actual degree-`g` twisted module, proving its
slant law for the ambient associator, and matching `T g` on the nonzero
conformal eigenvector with the stated phase normalization.
-/

compile_only_with_mathlib

set_option autoImplicit false

open scoped BigOperators

namespace D5.S3.FiniteGroups.Cyclic.CyclicProjectiveMonodromy

open CyclicAssociatorObstruction (cyclicProduct cyclicProduct_eq_one_of_mem twoCoboundary)

variable {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]

/-- Iterating the normalized slant law makes the order power a scalar endomorphism. -/
theorem pow_orderOf_eq_cyclicProduct_smul
    (α : G → G → G → ℂˣ) (g : G) (T : G → Module.End ℂ V)
    (hOne : T 1 = 1)
    (hMul : ∀ i : ℕ, T (g ^ i) * T g = (α g (g ^ i) g : ℂ) • T (g ^ i * g)) :
    T g ^ orderOf g = ((cyclicProduct α g : ℂˣ) : ℂ) • (1 : Module.End ℂ V) := by
  have hpow (k : ℕ) : T g ^ k =
      (((∏ i ∈ Finset.range k, α g (g ^ i) g) : ℂˣ) : ℂ) • T (g ^ k) := by
    induction k with
    | zero =>
        simp only [pow_zero, Finset.range_zero, Finset.prod_empty, Units.val_one, one_smul, hOne]
    | succ k ih =>
        rw [pow_succ (T g) k, ih, smul_mul_assoc, hMul k, smul_smul,
          Finset.prod_range_succ, Units.val_mul, pow_succ g k]
  simpa only [pow_orderOf_eq_one, hOne, cyclicProduct] using hpow (orderOf g)

/-- A nonzero eigenvector determines the cyclic product from its eigenvalue. -/
theorem cyclicProduct_coe_eq_eigenvalue_pow
    (α : G → G → G → ℂˣ) (g : G) (T : G → Module.End ℂ V)
    (hOne : T 1 = 1)
    (hMul : ∀ i : ℕ, T (g ^ i) * T g = (α g (g ^ i) g : ℂ) • T (g ^ i * g))
    {v : V} {z : ℂ} (hv : v ≠ 0) (heig : T g v = z • v) :
    ((cyclicProduct α g : ℂˣ) : ℂ) = z ^ orderOf g := by
  have happly (k : ℕ) : (T g ^ k) v = z ^ k • v := by
    induction k with
    | zero => simp only [pow_zero, Module.End.one_apply, one_smul]
    | succ k ih =>
        rw [pow_succ' (T g) k, Module.End.mul_apply, ih, (T g).map_smul, heig,
          smul_smul, pow_succ z k]
  apply smul_left_injective ℂ hv
  calc
    ((cyclicProduct α g : ℂˣ) : ℂ) • v = (T g ^ orderOf g) v := by
      rw [pow_orderOf_eq_cyclicProduct_smul α g T hOne hMul,
        LinearMap.smul_apply, Module.End.one_apply]
    _ = z ^ orderOf g • v := happly (orderOf g)

private theorem order_three_monodromy_phase_cube (n : ℕ) :
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (16 / 9 + (n : ℂ) / 3)) ^ (3 : ℕ) =
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I / 3) := by
  have hexponent :
      (3 : ℂ) * (2 * (Real.pi : ℂ) * Complex.I * (16 / 9 + (n : ℂ) / 3)) =
        2 * (Real.pi : ℂ) * Complex.I / 3 +
          ((n + 5 : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    simp only [Nat.cast_add, Nat.cast_ofNat]
    ring
  rw [← Complex.exp_nat_mul]
  simp only [Nat.cast_ofNat, hexponent, Complex.exp_add,
    Complex.exp_nat_mul_two_pi_mul_I, mul_one]

/-- The order-three conformal monodromy at weight `16/9 + n/3` has nontrivial cyclic product. -/
theorem cyclicProduct_ne_one_of_order_three_monodromy
    (α : G → G → G → ℂˣ) (g : G) (T : G → Module.End ℂ V)
    (hOne : T 1 = 1)
    (hMul : ∀ i : ℕ, T (g ^ i) * T g = (α g (g ^ i) g : ℂ) • T (g ^ i * g))
    (hg : orderOf g = 3) (n : ℕ) {v : V} (hv : v ≠ 0)
    (heig : T g v = Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
      (16 / 9 + (n : ℂ) / 3)) • v) : cyclicProduct α g ≠ 1 := by
  have hphase := cyclicProduct_coe_eq_eigenvalue_pow α g T hOne hMul hv heig
  rw [hg, order_three_monodromy_phase_cube n] at hphase
  have hprimitive : IsPrimitiveRoot (Complex.exp (2 * (Real.pi : ℂ) * Complex.I / 3)) 3 := by
    simpa only [Nat.cast_ofNat] using Complex.isPrimitiveRoot_exp 3 (by decide)
  intro htriv
  rw [htriv, Units.val_one] at hphase
  exact hprimitive.ne_one (by decide) hphase.symm

/-- Order-three conformal monodromy excludes membership in any subgroup trivializing `α`. -/
theorem not_mem_of_order_three_monodromy
    (α : G → G → G → ℂˣ) (g : G) (T : G → Module.End ℂ V)
    (hOne : T 1 = 1)
    (hMul : ∀ i : ℕ, T (g ^ i) * T g = (α g (g ^ i) g : ℂ) • T (g ^ i * g))
    (hg : orderOf g = 3) (n : ℕ) {v : V} (hv : v ≠ 0)
    (heig : T g v = Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
      (16 / 9 + (n : ℂ) / 3)) • v)
    (H : Subgroup G) (β : H → H → ℂˣ)
    (hβ : ∀ a b c : H, α a.val b.val c.val = twoCoboundary β a b c) : g ∉ H := by
  intro hmem
  exact cyclicProduct_ne_one_of_order_three_monodromy α g T hOne hMul hg n hv heig
    (cyclicProduct_eq_one_of_mem α H β hβ hmem)

#print axioms pow_orderOf_eq_cyclicProduct_smul
#print axioms cyclicProduct_coe_eq_eigenvalue_pow
#print axioms order_three_monodromy_phase_cube
#print axioms cyclicProduct_ne_one_of_order_three_monodromy
#print axioms not_mem_of_order_three_monodromy

end D5.S3.FiniteGroups.Cyclic.CyclicProjectiveMonodromy
