/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/P48qNativeRestrictedDualField
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/Orbifold/P48qNativeRestrictedDualField
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: BPZ coefficients and a lower-truncated cubic-cover field on the actual restricted dual. -/

import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeDualCoefficients
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Algebra.Module.Submodule.Equiv
import Mathlib.Algebra.Vertex.VertexOperator
import OmegaBuild.Commands

/-! The BPZ pullbacks act on finite sums of functionals on actual twisted
energy eigenspaces. The minimum twisted weight bounds the pole order on each
restricted-dual input and gives a Laurent field in the cubic cover variable. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeRestrictedDualField

open scoped BigOperators Classical DirectSum
open HalfFockSpectralFiberSource (actualInverse)
open LatticeSugawaraCurrents (sugawaraMode)
open P48qAllJetWickField (NativeStates)
open P48qNativeDualCoefficients (bpzDualCoeff bpzDualCoeff_apply bpzTermOnEigenspaces)
open P48qTwistedChargeAction (lattice)
open P48qTwistedStateEnergy (totalLZero totalLZero_minimum)

noncomputable section

local notation "L₀" => sugawaraMode lattice (actualInverse lattice) 0
local notation "E" => totalLZero.eigenspace

abbrev ActualGrade (w : ℝ) := ↥(E (w : ℂ))

abbrev GradeDual (w : ℝ) := Module.Dual ℂ (ActualGrade w)

/-- The algebraic direct sum of the full duals of actual twisted eigenspaces. -/
abbrev RestrictedDual := ⨁ w : ℝ, GradeDual w

def shiftedWeight (w : ℝ) (d : ℕ) (k : ℤ) : ℝ := w + (d : ℝ) + (k : ℝ) / 3

private theorem shiftedWeight_ofReal (w : ℝ) (d : ℕ) (k : ℤ) :
    (shiftedWeight w d k : ℂ) = (w : ℂ) + (d : ℂ) + (k : ℂ) / 3 := by
  simp only [shiftedWeight, Complex.ofReal_add, Complex.ofReal_natCast,
    Complex.ofReal_div, Complex.ofReal_intCast, Complex.ofReal_ofNat]

/-- Align the real shifted grade with the complex index of the BPZ pullback. -/
def shiftedGradeEquiv (w : ℝ) (d : ℕ) (k : ℤ) :
    ActualGrade (shiftedWeight w d k) ≃ₗ[ℂ] E ((w : ℂ) + (d : ℂ) + (k : ℂ) / 3) :=
  LinearEquiv.ofEq _ _ (congrArg (fun z : ℂ => E z) (shiftedWeight_ofReal w d k))

/-- The coefficient on one input grade, with its output indexed over `ℝ`. -/
def gradeCoeff (a : NativeStates) (d : ℕ) (ha : L₀ a = (d : ℂ) • a) (w : ℝ) (k : ℤ) :
    GradeDual w →ₗ[ℂ] GradeDual (shiftedWeight w d k) :=
  (shiftedGradeEquiv w d k).toLinearMap.dualMap.comp (bpzDualCoeff a d ha (w : ℂ) k)

theorem gradeCoeff_apply (a : NativeStates) (d : ℕ) (ha : L₀ a = (d : ℂ) • a)
    (w : ℝ) (k : ℤ) (f : GradeDual w) (v : ActualGrade (shiftedWeight w d k)) :
    gradeCoeff a d ha w k f v = (-1 : ℂ) ^ d * ∑ j ∈ Finset.range (d + 1),
      (j.factorial : ℂ)⁻¹ * f (bpzTermOnEigenspaces a d ha (w : ℂ) k j
        (shiftedGradeEquiv w d k v)) := by
  rw [gradeCoeff, LinearMap.comp_apply, LinearMap.dualMap_apply]
  exact bpzDualCoeff_apply a d ha (w : ℂ) k f (shiftedGradeEquiv w d k v)

private theorem actualGrade_eq_zero_of_lt {w : ℝ} (hw : w < 16 / 9) (v : ActualGrade w) :
    v = 0 := by
  apply Subtype.ext
  change v.val = 0
  by_contra hv
  exact (not_le_of_gt hw) (totalLZero_minimum.2
    ⟨v.val, hv, Module.End.mem_eigenspace_iff.mp v.property⟩)

/-- Coefficients mapping to an energy below the actual minimum vanish. -/
theorem gradeCoeff_eq_zero_of_lt (a : NativeStates) (d : ℕ) (ha : L₀ a = (d : ℂ) • a)
    (w : ℝ) (k : ℤ) (h : shiftedWeight w d k < 16 / 9) : gradeCoeff a d ha w k = 0 := by
  apply LinearMap.ext
  intro f
  apply LinearMap.ext
  intro v
  simp only [actualGrade_eq_zero_of_lt h v, LinearMap.zero_apply, map_zero]

/-- The coefficient of `x^k` on the actual restricted dual, where `x^3 = z`. -/
def coeff (a : NativeStates) (d : ℕ) (ha : L₀ a = (d : ℂ) • a) (k : ℤ) :
    Module.End ℂ RestrictedDual :=
  DFinsupp.lsum ℂ (fun w =>
    (DirectSum.lof ℂ ℝ GradeDual (shiftedWeight w d k)).comp (gradeCoeff a d ha w k))

theorem coeff_lof (a : NativeStates) (d : ℕ) (ha : L₀ a = (d : ℂ) • a) (k : ℤ)
    (w : ℝ) (f : GradeDual w) :
    coeff a d ha k (DirectSum.lof ℂ ℝ GradeDual w f) =
      DirectSum.lof ℂ ℝ GradeDual (shiftedWeight w d k) (gradeCoeff a d ha w k f) := by
  unfold coeff
  exact DFinsupp.lsum_single ℂ _ w f

theorem coeff_apply_eq_sum (a : NativeStates) (d : ℕ) (ha : L₀ a = (d : ℂ) • a) (k : ℤ)
    (f : RestrictedDual) :
    coeff a d ha k f = ∑ w ∈ f.support,
      DirectSum.lof ℂ ℝ GradeDual (shiftedWeight w d k) (gradeCoeff a d ha w k (f w)) := by
  calc
    coeff a d ha k f =
        coeff a d ha k (∑ w ∈ f.support, DirectSum.lof ℂ ℝ GradeDual w (f w)) := by
      simpa only [DirectSum.lof_eq_of] using
        congrArg (fun v : RestrictedDual => coeff a d ha k v) (DirectSum.sum_support_of f).symm
    _ = _ := by simp only [map_sum, coeff_lof]

/-- The largest input weight in the support, with `0` included for the empty support. -/
def supportUpperWeight (f : RestrictedDual) : ℝ :=
  (insert 0 f.support).max' (Finset.insert_nonempty _ _)

/-- A single real cutoff controls every summand of a restricted-dual input. -/
theorem coeff_eq_zero_of_lt (a : NativeStates) (d : ℕ) (ha : L₀ a = (d : ℂ) • a)
    (k : ℤ) (f : RestrictedDual)
    (hk : (k : ℝ) < 3 * (16 / 9 - supportUpperWeight f - (d : ℝ))) :
    coeff a d ha k f = 0 := by
  rw [coeff_apply_eq_sum]
  apply Finset.sum_eq_zero
  intro w hw
  have hUpper : w ≤ supportUpperWeight f := by
    unfold supportUpperWeight
    exact Finset.le_max' _ _ (Finset.mem_insert_of_mem hw)
  have hshift : shiftedWeight w d k < 16 / 9 := by
    unfold shiftedWeight
    linarith only [hUpper, hk]
  rw [gradeCoeff_eq_zero_of_lt a d ha w k hshift, LinearMap.zero_apply, map_zero]

theorem coeff_support_bddBelow (a : NativeStates) (d : ℕ) (ha : L₀ a = (d : ℂ) • a)
    (f : RestrictedDual) : BddBelow (Function.support (fun k => coeff a d ha k f)) := by
  obtain ⟨b, hb⟩ := exists_int_le (3 * (16 / 9 - supportUpperWeight f - (d : ℝ)))
  refine ⟨b, ?_⟩
  intro k hk
  apply le_of_not_gt
  intro hkb
  have hcast : (k : ℝ) < (b : ℝ) := by exact_mod_cast hkb
  exact hk (coeff_eq_zero_of_lt a d ha k f (hcast.trans_le hb))

/-- The opposite Laurent field of a homogeneous source on the cubic cover. -/
def oppositeField (a : NativeStates) (d : ℕ) (ha : L₀ a = (d : ℂ) • a) :
    VertexOperator ℂ RestrictedDual :=
  VertexOperator.of_coeff (coeff a d ha) (coeff_support_bddBelow a d ha)

theorem oppositeField_coeff (a : NativeStates) (d : ℕ) (ha : L₀ a = (d : ℂ) • a) (k : ℤ) :
    HVertexOperator.coeff (oppositeField a d ha) k = coeff a d ha k := rfl

end
end D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeRestrictedDualField
