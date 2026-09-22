/- GID: D5/S3/ConceptDynamics/Coding/InvolutionUniformExchange
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/InvolutionUniformExchange
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
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

@[simp] theorem basis_mul (g h : H) : basis g * basis h = basis (g * h) := by
  simp [basis]

@[simp] theorem basis_one : basis (1 : H) = 1 := rfl

@[simp] theorem uniform_coeff (g : H) : (uniform H).coeff g = 1 := by
  classical
  simp [uniform, basis, Finsupp.single_apply]

@[simp] theorem uniform_mul_basis (g : H) : uniform H * basis g = uniform H := by
  classical
  calc
    uniform H * basis g = ∑ h : H, basis (h * g) := by
      simp [uniform, Finset.sum_mul]
    _ = uniform H := by
      simpa [uniform, Function.comp_def] using
        (Finset.sum_comp_equiv (s := (Finset.univ : Finset H))
          (f := basis) (Equiv.mulRight g))

@[simp] theorem basis_mul_uniform (g : H) : basis g * uniform H = uniform H := by
  classical
  calc
    basis g * uniform H = ∑ h : H, basis (g * h) := by
      simp [uniform, Finset.mul_sum]
    _ = uniform H := by
      simpa [uniform, Function.comp_def] using
        (Finset.sum_comp_equiv (s := (Finset.univ : Finset H))
          (f := basis) (Equiv.mulLeft g))

/-- These factors use every group element with coefficient one before one subtraction. -/
def leftFactor (s t : H) : ZAlg H := uniform H + (1 - basis s) * basis t

def rightFactor (s : H) : ZAlg H := 1 + basis s

def source (s t : H) : ZAlg H :=
  uniform H + uniform H + (1 - basis s) * basis t * (1 + basis s)

def target (H : Type u) [Group H] [Fintype H] : ZAlg H := uniform H + uniform H

theorem leftFactor_coeff [DecidableEq H] (s t g : H) :
    (leftFactor s t).coeff g =
      1 + (if t = g then 1 else 0) - (if s * t = g then 1 else 0) := by
  classical
  unfold leftFactor
  rw [sub_mul, one_mul, basis_mul]
  simp [basis, Finsupp.single_apply, add_sub_assoc]

theorem leftFactor_nonnegative (s t g : H) : 0 ≤ (leftFactor s t).coeff g := by
  classical
  rw [leftFactor_coeff]
  by_cases ht : t = g
  · rw [if_pos ht]
    by_cases hst : s * t = g
    · rw [if_pos hst]
      decide
    · rw [if_neg hst]
      decide
  · rw [if_neg ht]
    by_cases hst : s * t = g
    · rw [if_pos hst]
      decide
    · rw [if_neg hst]
      decide

theorem rightFactor_nonnegative (s g : H) : 0 ≤ (rightFactor s).coeff g := by
  classical
  by_cases h1 : (1 : H) = g <;> by_cases hs : s = g <;>
    simp [rightFactor, basis, MonoidAlgebra.one_def, Finsupp.single_apply, h1, hs]

/-- The original nonuniform matrix is exactly the forward product. -/
theorem factors_forward (s t : H) : leftFactor s t * rightFactor s = source s t := by
  unfold leftFactor rightFactor source
  rw [add_mul, mul_add, mul_one, uniform_mul_basis]

/-- Reversing the factors kills the nonuniform term through the involution identity. -/
theorem factors_reverse (s t : H) (hs : s * s = 1) :
    rightFactor s * leftFactor s t = target H := by
  have hss : basis s * basis s = 1 := by rw [basis_mul, hs, basis_one]
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

theorem lift_toNat (p : ZAlg H) (hp : ∀ g : H, 0 ≤ p.coeff g) :
    liftNat H (toNat p) = p := by
  ext g
  simp [liftNat, toNat, Int.toNat_of_nonneg (hp g)]

/-- Every coefficient is constructed; nonnegativity is proved rather than assumed. -/
theorem nonnegative_involution_certificate (s t : H) (hs : s * s = 1) :
    ∃ U V : NAlg H,
      liftNat H (U * V) = source s t ∧ liftNat H (V * U) = target H := by
  refine ⟨toNat (leftFactor s t), toNat (rightFactor s), ?_, ?_⟩
  · rw [map_mul, lift_toNat _ (leftFactor_nonnegative s t),
      lift_toNat _ (rightFactor_nonnegative s)]
    exact factors_forward s t
  · rw [map_mul, lift_toNat _ (rightFactor_nonnegative s),
      lift_toNat _ (leftFactor_nonnegative s t)]
    exact factors_reverse s t hs

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
    simp only [mul_add, add_mul, sub_mul, mul_sub, one_mul, mul_one, basis_mul]
    abel
  intro h
  have heq := congrArg (fun p : ZAlg H => p.coeff t) h
  simp [hexpand, target, basis, Finsupp.single_apply, hts, hst', hsts] at heq

#print axioms factors_forward
#print axioms factors_reverse
#print axioms nonnegative_involution_certificate
#print axioms source_ne_target

end

end D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange
