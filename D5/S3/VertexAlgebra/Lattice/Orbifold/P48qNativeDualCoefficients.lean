/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/P48qNativeDualCoefficients
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/Orbifold/P48qNativeDualCoefficients
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Coordinate-inverted native cubic coefficients and their eigenspace dual pullbacks. -/

import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeFieldGrading
import D5.S3.VertexAlgebra.LatticeSugawaraVirasoro
import Mathlib.LinearAlgebra.Dual.Defs
import Batteries.Tactic.OpenPrivate
import OmegaBuild.Commands

/-! On the cover `x^3 = z`, the `j`th term in coordinate inversion takes
the native field of `L(1)^j a` at `x⁻¹` and multiplies by `x^(3j - 6d)`.
Thus native exponent `m` contributes to exponent `3j - 6d - m`.
The energy law restricts each resulting coefficient to actual twisted
eigenspaces, where precomposition defines its action on the duals. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeDualCoefficients

open scoped BigOperators
open HalfFockSpectralFiberSource (actualInverse actualInverse_left actualInverse_right)
open LatticePositiveEnergy (actualL0_eigen_iff_grade carrierCoeffEquiv chargeEnergy_nonneg
  energy mem_grade_iff)
open LatticeSugawaraCurrents (sugawaraMode)
open LatticeSugawaraVirasoro (sugawaraMode_virasoro)
open P48qAllJetWickField (NativeStates nativeField)
open P48qNativeFieldGrading (nativeField_coeff_weight)
open P48qThirdTwistedField (State)
open P48qTwistedChargeAction (lattice)
open P48qTwistedStateEnergy (totalLZero)
open private gram_det_unit from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qConformalVectorDecomposition

noncomputable section

local notation "L₀" => sugawaraMode lattice (actualInverse lattice) 0
local notation "L₁" => sugawaraMode lattice (actualInverse lattice) 1
local notation "E" => totalLZero.eigenspace

private theorem sourceLZero_sourceLOne_commutator : L₀ * L₁ - L₁ * L₀ = (-1 : ℂ) • L₁ := by
  have h := sugawaraMode_virasoro lattice (actualInverse lattice)
    (actualInverse_left lattice gram_det_unit) (actualInverse_right lattice gram_det_unit) 0 1
  simpa only [zero_add, zero_sub, Int.cast_neg, Int.cast_one, one_ne_zero, if_false,
    zero_smul, add_zero] using h

private theorem sourceLOne_pow_weight (a : NativeStates) (d : ℂ) (ha : L₀ a = d • a) (j : ℕ) :
    L₀ ((L₁ ^ j) a) = (d - (j : ℂ)) • (L₁ ^ j) a := by
  induction j with
  | zero => simpa only [pow_zero, Module.End.one_apply, Nat.cast_zero, sub_zero] using ha
  | succ j ih =>
      rw [pow_succ', Module.End.mul_apply]
      have h := LinearMap.congr_fun sourceLZero_sourceLOne_commutator ((L₁ ^ j) a)
      simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply,
        ih, map_smul] at h
      have hScalar : (-1 : ℂ) + (d - (j : ℂ)) = d - ((j + 1 : ℕ) : ℂ) := by
        push_cast <;> ring
      rw [eq_add_of_sub_eq h, ← add_smul, hScalar]

/-- The actual nonnegative lattice spectrum kills every source power above its weight. -/
theorem sourceLOne_pow_eq_zero_of_lt (a : NativeStates) (d : ℕ) (ha : L₀ a = (d : ℂ) • a)
    (j : ℕ) (hj : d < j) : (L₁ ^ j) a = 0 := by
  let v : NativeStates := (L₁ ^ j) a
  have he : L₀ v = (((d : ℤ) - (j : ℤ) : ℤ) : ℂ) • v := by
    simpa only [v, Int.cast_sub, Int.cast_natCast] using sourceLOne_pow_weight a (d : ℂ) ha j
  have hv := (actualL0_eigen_iff_grade lattice (actualInverse lattice)
    (actualInverse_left lattice gram_det_unit) (actualInverse_right lattice gram_det_unit)
    ((d : ℤ) - (j : ℤ)) v).mp he
  change v = 0
  apply (carrierCoeffEquiv lattice).injective
  apply Finsupp.ext
  intro b
  change (v b.1).coeff b.2 = 0
  apply (mem_grade_iff lattice _ v).mp hv b
  have hb := chargeEnergy_nonneg lattice P48qGramPositivity.nebeGram_posDef b.1
  dsimp only [energy]
  omega

/-- The native coefficient in the `j`th BPZ summand, before scalar weighting. -/
def bpzTerm (a : NativeStates) (d : ℕ) (k : ℤ) (j : ℕ) : Module.End ℂ State :=
  HVertexOperator.coeff (nativeField ((L₁ ^ j) a)) (-k - 6 * (d : ℤ) + 3 * (j : ℤ))

/-- Each summand takes input weight `w + d + k/3` to output weight `w`. -/
theorem bpzTerm_weight (a : NativeStates) (d : ℕ) (ha : L₀ a = (d : ℂ) • a)
    (w : ℂ) (k : ℤ) (j : ℕ) (v : State) (hv : v ∈ E (w + (d : ℂ) + (k : ℂ) / 3)) :
    bpzTerm a d k j v ∈ E w := by
  apply Module.End.mem_eigenspace_iff.mpr
  have h := nativeField_coeff_weight ((L₁ ^ j) a) v (-k - 6 * (d : ℤ) + 3 * (j : ℤ))
    ((d : ℂ) - (j : ℂ)) (w + (d : ℂ) + (k : ℂ) / 3) (sourceLOne_pow_weight a (d : ℂ) ha j)
    (Module.End.mem_eigenspace_iff.mp hv)
  have hWeight : (w + (d : ℂ) + (k : ℂ) / 3) + ((d : ℂ) - (j : ℂ)) +
      ((-k - 6 * (d : ℤ) + 3 * (j : ℤ) : ℤ) : ℂ) / 3 = w := by
    push_cast <;> ring
  simpa only [bpzTerm, hWeight] using h

/-- The native term restricted by its energy law. -/
def bpzTermOnEigenspaces (a : NativeStates) (d : ℕ) (ha : L₀ a = (d : ℂ) • a)
    (w : ℂ) (k : ℤ) (j : ℕ) : E (w + (d : ℂ) + (k : ℂ) / 3) →ₗ[ℂ] E w :=
  (bpzTerm a d k j).restrict (bpzTerm_weight a d ha w k j)

/-- The coordinate-inverted BPZ coefficient of `x^k` on the given input eigenspace. -/
def bpzCoeff (a : NativeStates) (d : ℕ) (ha : L₀ a = (d : ℂ) • a)
    (w : ℂ) (k : ℤ) : E (w + (d : ℂ) + (k : ℂ) / 3) →ₗ[ℂ] E w :=
  (-1 : ℂ) ^ d • ∑ j ∈ Finset.range (d + 1),
    (j.factorial : ℂ)⁻¹ • bpzTermOnEigenspaces a d ha w k j

/-- The restriction has the ordinary BPZ coefficient as its underlying state. -/
theorem bpzCoeff_apply_val (a : NativeStates) (d : ℕ) (ha : L₀ a = (d : ℂ) • a)
    (w : ℂ) (k : ℤ) (v : E (w + (d : ℂ) + (k : ℂ) / 3)) :
    (bpzCoeff a d ha w k v).val = (-1 : ℂ) ^ d • ∑ j ∈ Finset.range (d + 1),
      (j.factorial : ℂ)⁻¹ • HVertexOperator.coeff (nativeField ((L₁ ^ j) a))
        (-k - 6 * (d : ℤ) + 3 * (j : ℤ)) v.val := by
  simp only [bpzCoeff, LinearMap.smul_apply, LinearMap.sum_apply, Submodule.coe_smul,
    Submodule.coe_sum, bpzTermOnEigenspaces, LinearMap.coe_restrict_apply, bpzTerm]

/-- The cutoff at `d` includes every potentially nonzero divided-power term. -/
theorem bpzCoeff_eq_finsum (a : NativeStates) (d : ℕ) (ha : L₀ a = (d : ℂ) • a)
    (w : ℂ) (k : ℤ) :
    bpzCoeff a d ha w k = (-1 : ℂ) ^ d • ∑ᶠ j : ℕ,
      (j.factorial : ℂ)⁻¹ • bpzTermOnEigenspaces a d ha w k j := by
  unfold bpzCoeff
  congr 1
  symm
  apply finsum_eq_sum_of_support_subset
  intro j hj
  by_contra hOutside
  change ¬ j ∈ Finset.range (d + 1) at hOutside
  rw [Finset.mem_range] at hOutside
  have hz := sourceLOne_pow_eq_zero_of_lt a d ha j (by omega)
  have hTerm : bpzTermOnEigenspaces a d ha w k j = 0 := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    change bpzTerm a d k j v.val = 0
    simp only [bpzTerm, hz, map_zero, Pi.zero_apply, LinearMap.zero_apply]
  apply hj
  change (j.factorial : ℂ)⁻¹ • bpzTermOnEigenspaces a d ha w k j = 0
  rw [hTerm, smul_zero]

/-- Pull back a functional on twisted weight `w` to weight `w + d + k/3`. -/
def bpzDualCoeff (a : NativeStates) (d : ℕ) (ha : L₀ a = (d : ℂ) • a)
    (w : ℂ) (k : ℤ) :
    Module.Dual ℂ (E w) →ₗ[ℂ] Module.Dual ℂ (E (w + (d : ℂ) + (k : ℂ) / 3)) :=
  (bpzCoeff a d ha w k).dualMap

/-- Evaluation of the dual coefficient is the signed sum of the restricted native readouts. -/
theorem bpzDualCoeff_apply (a : NativeStates) (d : ℕ) (ha : L₀ a = (d : ℂ) • a)
    (w : ℂ) (k : ℤ) (f : Module.Dual ℂ (E w)) (v : E (w + (d : ℂ) + (k : ℂ) / 3)) :
    bpzDualCoeff a d ha w k f v = (-1 : ℂ) ^ d * ∑ j ∈ Finset.range (d + 1),
      (j.factorial : ℂ)⁻¹ * f (bpzTermOnEigenspaces a d ha w k j v) := by
  rw [bpzDualCoeff, LinearMap.dualMap_apply]
  simp only [bpzCoeff, LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum, smul_eq_mul]

end
end D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeDualCoefficients
