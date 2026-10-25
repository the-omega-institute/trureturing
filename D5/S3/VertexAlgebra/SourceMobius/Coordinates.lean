/- GID: D5/S3/VertexAlgebra/SourceMobius/Coordinates
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/SourceMobius/Coordinates
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Binomial coordinate formula for the actual finite source flow. -/
import D5.S3.VertexAlgebra.SourceMobius.FlowLaws
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Choose.Basic
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace D5.S3.VertexAlgebra.SourceMobius
open LatticeGeneratingFieldLocality LatticeSugawaraCurrents MvPolynomial
open LatticeHalfFockFiniteCorrection (sourceWeight)
open scoped BigOperators

theorem variable_power (D : LatticeData) (a : Charge D) (i : Fin D.rank)
    (r n : ℕ) (h : n ≤ r) :
    ((sectorL1 D a).toLinearMap ^ n) (X (i,r)) =
      ((r+1).descFactorial n : ℂ) • X (i,r-n) := by
  induction n generalizing r with
  | zero => simp
  | succ n ih =>
    cases r with
    | zero => omega
    | succ r =>
      rw [pow_succ, Module.End.mul_apply]
      change ((sectorL1 D a).toLinearMap ^ n) (sectorL1 D a (X (i,r+1))) = _
      rw [show sectorL1 D a (X (i,r+1)) = (r+2 : ℂ) • X (i,r) by
        simp [sectorL1, loweringVariable], map_smul, ih r (by omega)]
      simp only [Nat.succ_descFactorial_succ, Nat.cast_mul, smul_smul, Nat.add_sub_add_right]
      congr 1
      push_cast
      ring

theorem variable_power_charge (D : LatticeData) (a : Charge D)
    (i : Fin D.rank) (r : ℕ) :
    ((sectorL1 D a).toLinearMap ^ (r+1)) (X (i,r)) =
      ((r+1).factorial : ℂ) • C (bilinear D (unitCharge D i) a : ℂ) := by
  rw [pow_succ', Module.End.mul_apply, variable_power D a i r r le_rfl,
    map_smul, Nat.sub_self]
  have hf : (r+1).descFactorial r = (r+1).factorial := by
    simpa using Nat.factorial_mul_descFactorial (show r ≤ r+1 by omega)
  simp [sectorL1, loweringVariable, hf]

/-- The actual finite algebra flow has the required binomial variable formula. -/
theorem sectorFlow_X (D : LatticeData) (a : Charge D) (u : ℂ)
    (i : Fin D.rank) (r : ℕ) :
    sectorFlow D a u (X (i,r)) =
      (∑ s ∈ Finset.range (r+1),
        (((r+1).choose (s+1) : ℂ) * u ^ (r-s)) • X (i,s)) +
        (u ^ (r+1)) • C (bilinear D (unitCharge D i) a : ℂ) := by
  classical
  have hd : weightedTotalDegree (sourceWeight D) (X (i,r) : Oscillator D) = r+1 := by
    rw [weightedTotalDegree, MvPolynomial.support_X]
    simp [sourceWeight, Finsupp.weight_single]
  rw [sectorFlow_eq_sum, hd, Finset.sum_range_succ, variable_power_charge]
  have hf : ((r+1).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (r+1)
  rw [smul_smul, div_mul_cancel₀ _ hf]
  congr 1
  calc
    _ = ∑ n ∈ Finset.range (r+1),
        (((r+1).choose n : ℂ) * u ^ n) • X (i,r-n) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [variable_power D a i r n (by simpa using Finset.mem_range.mp hn),
        smul_smul, Nat.descFactorial_eq_factorial_mul_choose]
      push_cast
      congr 1
      have hn' : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
      field_simp
    _ = _ := by
      rw [← Finset.sum_range_reflect (fun n =>
        (((r+1).choose n : ℂ) * u ^ n) • (X (i,r-n) : Oscillator D)) (r+1)]
      apply Finset.sum_congr rfl
      intro s hs
      have hs' : s ≤ r := by simpa using Finset.mem_range.mp hs
      have reflected : r - (r-s) = s := by omega
      have chosen : (r+1).choose (r-s) = (r+1).choose (s+1) := by
        apply Nat.choose_symm_of_eq_add
        omega
      simp only [Nat.add_sub_cancel, reflected, chosen]

/-- The closed coordinate formula determines the same algebra operation on
all finite oscillator polynomials, and hence all original charge sectors. -/
theorem sectorFlow_eq_aeval (D : LatticeData) (a : Charge D) (u : ℂ) :
    sectorFlow D a u = aeval (fun x : Index D =>
      (∑ s ∈ Finset.range (x.2+1),
        (((x.2+1).choose (s+1) : ℂ) * u ^ (x.2-s)) • X (x.1,s)) +
        (u ^ (x.2+1)) • C (bilinear D (unitCharge D x.1) a : ℂ)) := by
  apply MvPolynomial.algHom_ext
  intro x
  simpa using sectorFlow_X D a u x.1 x.2

end D5.S3.VertexAlgebra.SourceMobius
