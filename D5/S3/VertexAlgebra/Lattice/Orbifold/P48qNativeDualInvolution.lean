/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/P48qNativeDualInvolution
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/Orbifold/P48qNativeDualInvolution
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Double inverse-coordinate BPZ on the actual native cubic coefficients. -/

import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeDualCoefficients
import Batteries.Tactic.OpenPrivate
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Choose.Sum
import OmegaBuild.Commands

/-! Applying inverse-coordinate BPZ twice on the cover `x^3 = z` gives a
finite sum of actual native coefficients. The two source powers compose,
and the alternating divided-power sum at each positive total degree is zero. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeDualInvolution

open scoped BigOperators
open HalfFockSpectralFiberSource (actualInverse)
open LatticeSugawaraCurrents (sugawaraMode)
open P48qAllJetWickField (NativeStates nativeField)
open P48qNativeDualCoefficients (bpzCoeff bpzCoeff_apply_val bpzTerm)
open P48qThirdTwistedField (State)
open P48qTwistedChargeAction (lattice)
open P48qTwistedStateEnergy (totalLZero)
open private sourceLOne_pow_weight from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeDualCoefficients

noncomputable section

local notation "C" => HVertexOperator.coeff
local notation "L₀" => sugawaraMode lattice (actualInverse lattice) 0
local notation "L₁" => sugawaraMode lattice (actualInverse lattice) 1
local notation "E" => totalLZero.eigenspace

/-- The double BPZ coefficient of `x^k` for a source of weight `d`.
The `j`th term samples the first inversion at exponent `-k - 6*d + 3*j`
with source `L(1)^j a` of weight `d-j`. -/
def doubleBPZCoeff (a : NativeStates) (d : ℕ) (k : ℤ) : Module.End ℂ State :=
  (-1 : ℂ) ^ d • ∑ j ∈ Finset.range (d + 1),
    (j.factorial : ℂ)⁻¹ • ((-1 : ℂ) ^ (d - j) • ∑ i ∈ Finset.range (d - j + 1),
      (i.factorial : ℂ)⁻¹ • bpzTerm ((L₁ ^ j) a) (d - j) (-k - 6 * (d : ℤ) + 3 * (j : ℤ)) i)

private theorem bpz_sign (d j : ℕ) (hj : j ≤ d) :
    (-1 : ℂ) ^ d * (-1 : ℂ) ^ (d - j) = (-1 : ℂ) ^ j := by
  calc
    _ = (-1 : ℂ) ^ ((d - j) + j) * (-1 : ℂ) ^ (d - j) :=
      congrArg (fun n : ℕ => (-1 : ℂ) ^ n * (-1 : ℂ) ^ (d - j)) (by omega)
    _ = (-1 : ℂ) ^ j * ((-1 : ℂ) * (-1)) ^ (d - j) := by
      rw [pow_add, mul_pow]
      ring
    _ = _ := by rw [show (-1 : ℂ) * (-1) = 1 by norm_num, one_pow, mul_one]

private theorem sum_divided_power_scalars (n : ℕ) :
    (∑ j ∈ Finset.range (n + 1),
      (-1 : ℂ) ^ j * (j.factorial : ℂ)⁻¹ * ((n - j).factorial : ℂ)⁻¹) =
      (n.factorial : ℂ)⁻¹ * (0 : ℂ) ^ n := by
  have hFactorial : (n.factorial : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_pos n).ne'
  have hBinomial : (∑ j ∈ Finset.range (n + 1), (-1 : ℂ) ^ j * (n.choose j : ℂ)) =
      (0 : ℂ) ^ n := by
    simpa only [one_pow, mul_one, show (-1 : ℂ) + 1 = 0 by norm_num] using
      (add_pow (-1 : ℂ) 1 n).symm
  calc
    _ = ∑ j ∈ Finset.range (n + 1),
        (n.factorial : ℂ)⁻¹ * ((-1 : ℂ) ^ j * (n.choose j : ℂ)) := by
      apply Finset.sum_congr rfl
      intro j hj
      have hj' : j ≤ n := by
        have := Finset.mem_range.mp hj
        omega
      rw [Nat.cast_choose ℂ hj', div_eq_mul_inv, mul_inv_rev]
      symm
      calc
        _ = ((n.factorial : ℂ)⁻¹ * (n.factorial : ℂ)) *
            ((-1 : ℂ) ^ j * (j.factorial : ℂ)⁻¹ * ((n - j).factorial : ℂ)⁻¹) := by ring
        _ = _ := by rw [inv_mul_cancel₀ hFactorial, one_mul]
    _ = _ := by rw [← Finset.mul_sum, hBinomial]

/-- The two finite inversions recover the native coefficient as an endomorphism
of the actual twisted state space. The identity of sums holds for any cutoff
`d` and in particular for the homogeneous weight used in BPZ. -/
theorem doubleBPZCoeff_eq_native (a : NativeStates) (d : ℕ) (k : ℤ) :
    doubleBPZCoeff a d k = C (nativeField a) k := by
  let mode (n : ℕ) : Module.End ℂ State := C (nativeField ((L₁ ^ n) a)) (k + 3 * (n : ℤ))
  let summand (j i : ℕ) : Module.End ℂ State :=
    ((-1 : ℂ) ^ j * (j.factorial : ℂ)⁻¹ * (i.factorial : ℂ)⁻¹) • mode (i + j)
  have hIndex (j i : ℕ) (hj : j ≤ d) :
      -(-k - 6 * (d : ℤ) + 3 * (j : ℤ)) - 6 * ((d - j : ℕ) : ℤ) + 3 * (i : ℤ) =
        k + 3 * ((i + j : ℕ) : ℤ) := by
    rw [Nat.cast_sub hj, Nat.cast_add]
    ring
  have hPower (j i : ℕ) : (L₁ ^ i) ((L₁ ^ j) a) = (L₁ ^ (i + j)) a := by
    rw [pow_add, Module.End.mul_apply]
  calc
    doubleBPZCoeff a d k =
        ∑ j ∈ Finset.range (d + 1), ∑ i ∈ Finset.range (d - j + 1), summand j i := by
      unfold doubleBPZCoeff
      simp only [Finset.smul_sum, smul_smul, mul_assoc]
      apply Finset.sum_congr rfl
      intro j hj
      have hj' : j ≤ d := by
        have := Finset.mem_range.mp hj
        omega
      apply Finset.sum_congr rfl
      intro i _
      have hScalar :
          (-1 : ℂ) ^ d * ((j.factorial : ℂ)⁻¹ * ((-1 : ℂ) ^ (d - j) * (i.factorial : ℂ)⁻¹)) =
            (-1 : ℂ) ^ j * (j.factorial : ℂ)⁻¹ * (i.factorial : ℂ)⁻¹ := by
        calc
          _ = ((-1 : ℂ) ^ d * (-1 : ℂ) ^ (d - j)) *
              (j.factorial : ℂ)⁻¹ * (i.factorial : ℂ)⁻¹ := by ring
          _ = _ := by rw [bpz_sign d j hj']
      simp only [summand, mode, bpzTerm, hIndex j i hj', hPower j i, hScalar, mul_assoc]
    _ = ∑ j ∈ Finset.range (d + 1), ∑ i ∈ Finset.range (d + 1 - j), summand j i := by
      apply Finset.sum_congr rfl
      intro j hj
      have := Finset.mem_range.mp hj
      rw [show d - j + 1 = d + 1 - j by omega]
    _ = ∑ n ∈ Finset.range (d + 1), ∑ j ∈ Finset.range (n + 1),
        ((-1 : ℂ) ^ j * (j.factorial : ℂ)⁻¹ * ((n - j).factorial : ℂ)⁻¹) • mode n := by
      rw [← Finset.sum_range_diag_flip (d + 1) summand]
      apply Finset.sum_congr rfl
      intro n _
      apply Finset.sum_congr rfl
      intro j hj
      have hj' : j ≤ n := by
        have := Finset.mem_range.mp hj
        omega
      simp only [summand, Nat.sub_add_cancel hj']
    _ = ∑ n ∈ Finset.range (d + 1), ((n.factorial : ℂ)⁻¹ * (0 : ℂ) ^ n) • mode n := by
      apply Finset.sum_congr rfl
      intro n _
      rw [← Finset.sum_smul, sum_divided_power_scalars]
    _ = C (nativeField a) k := by
      rw [Finset.sum_range_succ']
      simp only [pow_succ (0 : ℂ), mul_zero, zero_smul, Finset.sum_const_zero,
        Nat.factorial_zero, Nat.cast_one, inv_one, pow_zero, one_mul, one_smul, add_zero, zero_add,
        mode, Module.End.one_apply, Nat.cast_zero]

private theorem sourceLOne_pow_nat_weight (a : NativeStates) (d j : ℕ)
    (ha : L₀ a = (d : ℂ) • a) (hj : j ≤ d) :
    L₀ ((L₁ ^ j) a) = ((d - j : ℕ) : ℂ) • (L₁ ^ j) a := by
  rw [Nat.cast_sub hj]
  exact sourceLOne_pow_weight a (d : ℂ) ha j

private theorem firstBPZInput_mem (w : ℂ) (d : ℕ) (k : ℤ)
    (j : ℕ) (hj : j ≤ d) (v : E (w - (d : ℂ) - (k : ℂ) / 3)) :
    v.val ∈ E (w + ((d - j : ℕ) : ℂ) + ((-k - 6 * (d : ℤ) + 3 * (j : ℤ) : ℤ) : ℂ) / 3) := by
  have hWeight : w + ((d - j : ℕ) : ℂ) + ((-k - 6 * (d : ℤ) + 3 * (j : ℤ) : ℤ) : ℂ) / 3 =
      w - (d : ℂ) - (k : ℂ) / 3 := by
    rw [Nat.cast_sub hj]
    push_cast <;> ring
  rw [hWeight]
  exact v.property

/-- On an actual twisted eigenspace, the second inversion of the existing
`bpzCoeff` recovers the native coefficient on the underlying state. -/
theorem doubleBPZCoeff_eq_native_on_eigenspace (a : NativeStates) (d : ℕ)
    (ha : L₀ a = (d : ℂ) • a) (w : ℂ) (k : ℤ) (v : E (w - (d : ℂ) - (k : ℂ) / 3)) :
    (-1 : ℂ) ^ d • (∑ j ∈ (Finset.range (d + 1)).attach,
      have hj : j.val ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp j.property)
      (j.val.factorial : ℂ)⁻¹ •
        (bpzCoeff ((L₁ ^ j.val) a) (d - j.val) (sourceLOne_pow_nat_weight a d j.val ha hj) w
          (-k - 6 * (d : ℤ) + 3 * (j.val : ℤ))
          ⟨v.val, firstBPZInput_mem w d k j.val hj v⟩).val) = C (nativeField a) k v.val := by
  calc
    _ = doubleBPZCoeff a d k v.val := by
      simp only [doubleBPZCoeff, LinearMap.smul_apply, LinearMap.sum_apply]
      apply congrArg (fun s : State => (-1 : ℂ) ^ d • s)
      rw [← Finset.sum_attach (Finset.range (d + 1))]
      apply Finset.sum_congr rfl
      intro j _
      simp only [bpzCoeff_apply_val, bpzTerm]
    _ = _ := LinearMap.congr_fun (doubleBPZCoeff_eq_native a d k) v.val

end
end D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeDualInvolution
