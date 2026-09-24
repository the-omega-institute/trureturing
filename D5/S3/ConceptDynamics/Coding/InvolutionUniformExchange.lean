/- GID: D5/S3/ConceptDynamics/Coding/InvolutionUniformExchange
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/InvolutionUniformExchange
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: An involution constructs genuine nonnegative group-ring exchange factors. -/

import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Abel

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange

noncomputable section

universe u
variable {H : Type u} [Group H] [Fintype H]

abbrev ZAlg (H : Type u) [Group H] := MonoidAlgebra ℤ H
abbrev NAlg (H : Type u) [Group H] := MonoidAlgebra ℕ H

def basis (g : H) : ZAlg H := MonoidAlgebra.single g 1

def uniform (H : Type u) [Group H] [Fintype H] : ZAlg H := ∑ g : H, basis g

/-- These factors use every group element with coefficient one before one subtraction. -/
def leftFactor (s t : H) : ZAlg H := uniform H + (1 - basis s) * basis t

def rightFactor (s : H) : ZAlg H := 1 + basis s

def source (s t : H) : ZAlg H :=
  uniform H + uniform H + (1 - basis s) * basis t * (1 + basis s)

def target (H : Type u) [Group H] [Fintype H] : ZAlg H := uniform H + uniform H

/-- The original nonuniform matrix is exactly the forward product. -/
theorem factors_forward (s t : H) : leftFactor s t * rightFactor s = source s t := by
  classical
  have uniform_mul_basis : uniform H * basis s = uniform H := by
    calc
      uniform H * basis s = ∑ h : H, basis (h * s) := by
        simp [uniform, basis, Finset.sum_mul]
      _ = uniform H := by
        simpa [uniform, Function.comp_def] using
          (Finset.sum_comp_equiv (s := (Finset.univ : Finset H))
            (f := basis) (Equiv.mulRight s))
  unfold leftFactor rightFactor source
  rw [add_mul, mul_add, mul_one, uniform_mul_basis]

/-- Reversing the factors kills the nonuniform term through the involution identity. -/
theorem factors_reverse (s t : H) (hs : s * s = 1) :
    rightFactor s * leftFactor s t = target H := by
  classical
  have hss : basis s * basis s = 1 := by
    simp [basis, hs]
  have basis_mul_uniform : basis s * uniform H = uniform H := by
    calc
      basis s * uniform H = ∑ h : H, basis (s * h) := by
        simp [uniform, basis, Finset.mul_sum]
      _ = uniform H := by
        simpa [uniform, Function.comp_def] using
          (Finset.sum_comp_equiv (s := (Finset.univ : Finset H))
            (f := basis) (Equiv.mulLeft s))
  have hcancel : (1 + basis s) * (1 - basis s) = (0 : ZAlg H) := by
    rw [add_mul, one_mul, mul_sub, mul_one, hss]
    simp [sub_eq_add_neg, add_assoc]
  unfold rightFactor leftFactor target
  rw [mul_add, add_mul, one_mul, basis_mul_uniform, ← mul_assoc, hcancel,
    zero_mul, add_zero]

/-- Coefficientwise conversion supplies actual natural-number group-ring factors. -/
def toNat (p : ZAlg H) : NAlg H :=
  MonoidAlgebra.ofCoeff (p.coeff.mapRange Int.toNat (by decide))

def liftNat (H : Type u) [Group H] : NAlg H →+* ZAlg H :=
  MonoidAlgebra.mapRingHom H (Nat.castRingHom ℤ)

/-- Noncommuting choices give distinct endpoints, ruling out a zero-step exchange. -/
theorem source_ne_target (s t : H) (hs : s * s = 1) (hst : s * t ≠ t * s) :
    source s t ≠ target H := by
  classical
  have hs1 : s ≠ 1 := by
    intro h
    apply hst
    simp [h]
  have hts : t * s ≠ t := by
    intro h
    apply hs1
    exact mul_left_cancel (h.trans (mul_one t).symm)
  have hst' : s * t ≠ t := by
    intro h
    apply hs1
    exact mul_right_cancel (h.trans (one_mul t).symm)
  have hsts : (s * t) * s ≠ t := by
    intro h
    apply hst
    calc
      s * t = ((s * t) * s) * s := by rw [mul_assoc, hs, mul_one]
      _ = t * s := congrArg (fun x : H => x * s) h
  have hexpand : source s t = target H + basis t + basis (t * s) -
      basis (s * t) - basis ((s * t) * s) := by
    unfold source target
    simp only [mul_add, add_mul, sub_mul, mul_sub, one_mul, mul_one]
    simp only [basis, MonoidAlgebra.single_mul_single, one_mul]
    abel
  intro h
  have heq := congrArg (fun p : ZAlg H => p.coeff t) h
  simp [hexpand, target, basis, Finsupp.single_apply, hts, hst', hsts] at heq

#print axioms factors_forward
#print axioms factors_reverse
#print axioms source_ne_target

end

end D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange
