/- GID: D5/S3/VertexAlgebra/HalfFock/ActualMobiusAllOrder
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/HalfFock/ActualMobiusAllOrder
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Original corrected-field formal Mobius coefficients at every order. -/

import D5.S3.VertexAlgebra.HalfFock.ActualMobiusCovariance
import D5.S3.VertexAlgebra.LatticeActualLZeroGrading
import D5.S3.VertexAlgebra.SourceMobius.OriginalCarrier
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.Data.Nat.Choose.Sum

/-! Formal-u covariance on the original algebraic carriers. Multiplication of
endomorphisms acts right to left. No numeric target exponential is asserted.
The binomial-series implementation is due to Scott Carnahan (Apache 2.0);
the original lattice and current attributions remain with their suppliers. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.HalfFock.ActualMobiusAllOrder
open LatticeGeneratingFieldLocality LatticeHalfFock LatticeSugawaraCurrents
open LatticeHalfFockChargedTensorCoefficients LatticePositiveEnergy
open scoped BigOperators
noncomputable section

private abbrev A (D : LatticeData) (hu : IsUnit D.G.det) (e : ℤ) :
    Carrier D →ₗ[ℂ] Module.End ℂ (ActualTensor D hu) :=
  (LinearMap.proj e).comp
    (HVertexOperator.coeff.comp (LatticeHalfFockCorrectedField.correctedField D hu))

private abbrev T (D : LatticeData) (hu : IsUnit D.G.det) :=
  tensorL D (ActualGround D hu) (HalfFockSpectralFiberSource.actualInverse D) 1

private abbrev S (D : LatticeData) (j : ℤ) := sugawaraMode D (gramComplex D)⁻¹ j

private def ad (D : LatticeData) (hu : IsUnit D.G.det) :
    Module.End ℂ (Module.End ℂ (ActualTensor D hu)) :=
  LinearMap.mulLeft ℂ (T D hu) - LinearMap.mulRight ℂ (T D hu)

private def dividedAd (D : LatticeData) (hu : IsUnit D.G.det) (n : ℕ) (e : ℤ) :
    Carrier D →ₗ[ℂ] Module.End ℂ (ActualTensor D hu) :=
  (n.factorial : ℂ)⁻¹ • ((ad D hu ^ n).comp (A D hu e))

private theorem inverse_eq (D : LatticeData) (hu : IsUnit D.G.det) :
    (gramComplex D)⁻¹ = HalfFockSpectralFiberSource.actualInverse D :=
  Matrix.inv_eq_left_inv (HalfFockSpectralFiberSource.actualInverse_left D hu)

private theorem source_weight_lowering (D : LatticeData) (hu : IsUnit D.G.det)
    (h : ℤ) (a : Carrier D) (ha : S D 0 a = (h : ℂ) • a) (k : ℕ) :
    S D 0 ((S D 1 ^ k) a) = ((h : ℂ) - (k : ℂ)) • (S D 1 ^ k) a := by
  have hv := LatticeSugawaraVirasoro.sugawaraMode_virasoro D
    (HalfFockSpectralFiberSource.actualInverse D)
    (HalfFockSpectralFiberSource.actualInverse_left D hu)
    (HalfFockSpectralFiberSource.actualInverse_right D hu) 0 1
  rw [← inverse_eq D hu] at hv
  have comm : S D 0 * S D 1 - S D 1 * S D 0 = -(S D 1) := by
    simpa [S] using hv
  induction k with
  | zero => simpa using ha
  | succ k ih =>
    have hc := LinearMap.congr_fun comm ((S D 1 ^ k) a)
    simp only [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.neg_apply] at hc
    rw [ih, map_smul] at hc
    rw [pow_succ', Module.End.mul_apply]
    push_cast
    linear_combination (norm := module) hc

private theorem dividedAd_step (D : LatticeData) (hu : IsUnit D.G.det)
    (n : ℕ) (e : ℤ) (a : Carrier D) :
    (n + 1 : ℂ) • dividedAd D hu (n+1) e a = ad D hu (dividedAd D hu n e a) := by
  have hn : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hs : (n+1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  simp only [dividedAd, LinearMap.smul_apply, LinearMap.comp_apply, map_smul,
    Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, smul_smul,
    pow_succ', Module.End.mul_apply]
  congr 1
  field_simp

private def c (α : ℂ) (n k : ℕ) : ℂ :=
  if k ≤ n then Ring.choose (α - (k : ℂ)) (n-k) / (k.factorial : ℂ) else 0

private theorem choose_step (r : ℂ) (q : ℕ) :
    (q+1 : ℂ) * Ring.choose r (q+1) = (r-(q:ℂ)) * Ring.choose r q := by
  have h := Ring.choose_smul_choose r (by omega : q ≤ q+1)
  simpa [Nat.choose_succ_self_right, nsmul_eq_mul, mul_comm] using h

private theorem c_step_zero (α : ℂ) (n : ℕ) :
    (n+1 : ℂ) * c α (n+1) 0 = (α-(n:ℂ)) * c α n 0 := by
  simpa [c] using choose_step α n

private theorem c_step_succ (α : ℂ) (n k : ℕ) (hk : k ≤ n) :
    (n+1 : ℂ) * c α (n+1) (k+1) =
      c α n k + (α-(n:ℂ)-(k+1:ℂ)) * c α n (k+1) := by
  by_cases top : k=n
  · subst k
    have hn : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
    have hs : (n+1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    simp [c, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  · have hkn : k+1 ≤ n := by omega
    let m := n-(k+1)
    have split : n-k = m+1 := by omega
    have count : (n:ℂ) = (m:ℂ)+(k:ℂ)+1 := by exact_mod_cast (by omega : n=m+k+1)
    have hp := Ring.choose_succ_succ (α-(k+1:ℂ)) m
    have hs := choose_step (α-(k+1:ℂ)) m
    have ht : α-(k+1:ℂ)+1 = α-(k:ℂ) := by ring
    rw [ht] at hp
    have hf : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
    have hkp : (k+1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
    simp only [c, if_pos hk, if_pos hkn, if_pos (show k+1 ≤ n+1 by omega),
      show n+1-(k+1)=m+1 by omega, show n-(k+1)=m by rfl, split,
      Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    rw [hp, count]
    field_simp
    linear_combination (k+1:ℂ) * hs

end
end D5.S3.VertexAlgebra.HalfFock.ActualMobiusAllOrder
