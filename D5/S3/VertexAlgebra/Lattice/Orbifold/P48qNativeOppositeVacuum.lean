/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/P48qNativeOppositeVacuum
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/Orbifold/P48qNativeOppositeVacuum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Coordinate inversion and the nonzero ground vacuum coefficient of the cubic insertion. -/

import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeFixedRightJacobi
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qFiniteEnergyEigenspaces
import Batteries.Tactic.OpenPrivate
import OmegaBuild.Commands

/-! Coordinate inversion of the P48q right insertion paired with a functional on an
actual energy eigenspace. The physical exponents are indexed by a shifted copy of ℤ. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeOppositeVacuum

open scoped BigOperators
open HalfFockSpectralFiberSource (actualInverse)
open LatticeActualConformalState (omega)
open P48qAllJetWickField (nativeField)
open P48qFiniteEnergyEigenspaces (totalLZeroEigenspaceCoeffEquiv)
open P48qNativeConformalSector
  (fixedStates sector fixedField fixedField_coeff_val fixedOmega fixedVacuum vacuum_mem_sector_zero)
open P48qNativeConformalZero (native_conformal_coeff_neg_six_eq_totalLZero)
open P48qNativeFixedRightInsertion (rightInsertion rightInsertion_vacuum_coeff sectorTranslation)
open P48qNativeVirasoro (native_conformal_virasoro)
open P48qThirdTwistedField (State)
open P48qTwistedChargeAction (Momentum lattice)
open P48qTwistedStateEnergy (Occupation totalLZero totalLZero_coeff totalWeight totalLZero_minimum
  vacuum totalLZero_vacuum)
open StateField.BorcherdsPermutations (dividedTranslation)
open private stateCoeffEquiv stateCoeffEquiv_apply from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qFiniteEnergyEigenspaces
open private rightMode from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeFixedRightJacobi

noncomputable section

local notation "C" => HVertexOperator.coeff
local notation:max "L[" s "," n "]" => C (fixedField s fixedOmega) (-(n : ℤ) - 2)

/-- Retain the momentum and occupation coefficients on the specified energy fiber. -/
def gradeProjection (w : ℂ) : State →ₗ[ℂ] totalLZero.eigenspace w :=
  (totalLZeroEigenspaceCoeffEquiv w).symm.toLinearMap.comp
    ((Finsupp.lsubtypeDomain {x : Momentum × Occupation | (totalWeight x.1 x.2 : ℂ) = w}).comp
      stateCoeffEquiv.toLinearMap)

private theorem gradeProjection_coeff (w : ℂ) (v : State)
    (x : {x : Momentum × Occupation // (totalWeight x.1 x.2 : ℂ) = w}) :
    totalLZeroEigenspaceCoeffEquiv w (gradeProjection w v) x = (v x.val.1).coeff x.val.2 := by
  simp only [gradeProjection, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply]
  exact stateCoeffEquiv_apply v x.val

private theorem gradeProjection_self (w : ℂ) (v : totalLZero.eigenspace w) :
    gradeProjection w v.val = v := by
  apply (totalLZeroEigenspaceCoeffEquiv w).injective
  ext x
  rw [gradeProjection_coeff]
  rfl

private theorem gradeProjection_eq_zero {v : State} {w w' : ℂ}
    (hv : totalLZero v = w' • v) (hne : w ≠ w') : gradeProjection w v = 0 := by
  apply (totalLZeroEigenspaceCoeffEquiv w).injective
  ext x
  rw [gradeProjection_coeff, map_zero, Finsupp.zero_apply]
  have h := congrArg (fun u : State => (u x.val.1).coeff x.val.2) hv
  change (totalLZero v x.val.1).coeff x.val.2 =
    ((w' • v) x.val.1).coeff x.val.2 at h
  rw [totalLZero_coeff, x.property, Finsupp.smul_apply, MvPolynomial.coeff_smul, smul_eq_mul] at h
  by_contra hz
  exact hne (mul_right_cancel₀ hz h)

private theorem conformalMode_weight (s : Fin 3) (n : ℤ) (u : sector s) (w : ℂ)
    (hu : totalLZero u.val = w • u.val) :
    totalLZero (L[s, n] u).val = (w - (n : ℂ)) • (L[s, n] u).val := by
  let A : ℤ → Module.End ℂ State :=
    fun i => C (nativeField (omega lattice (actualInverse lattice))) (-3 * (i + 2))
  have hA (i : ℤ) : (L[s, i] u).val = A i u.val := by
    rw [fixedField_coeff_val]
    have hi : 3 * (-i - 2) = -3 * (i + 2) := by ring
    exact congrArg (fun k => C (nativeField fixedOmega.val) k u.val) hi
  have hA0 : A 0 = totalLZero := native_conformal_coeff_neg_six_eq_totalLZero
  have hvir : A 0 * A n - A n * A 0 = (-(n : ℂ)) • A n := by
    have h := native_conformal_virasoro 0 n
    dsimp only at h
    simpa only [A, zero_sub, zero_add, Int.cast_neg, Int.cast_zero,
      zero_pow (by decide : (3 : ℕ) ≠ 0), sub_zero, mul_zero, ite_self, zero_smul, add_zero]
      using h
  have hv := LinearMap.congr_fun hvir u.val
  simp only [hA0, LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply, hu,
    map_smul] at hv
  rw [hA]
  calc
    _ = (-(n : ℂ)) • A n u.val + w • A n u.val := eq_add_of_sub_eq hv
    _ = _ := by rw [← add_smul]; congr 1; ring

private theorem conformalPower_weight (s : Fin 3) (n : ℤ) (u : sector s) (w : ℂ)
    (hu : totalLZero u.val = w • u.val) (j : ℕ) :
    totalLZero ((L[s, n] ^ j) u).val =
      (w - (j : ℂ) * (n : ℂ)) • ((L[s, n] ^ j) u).val := by
  induction j with
  | zero => simpa only [pow_zero, Module.End.one_apply, Nat.cast_zero, zero_mul, sub_zero] using hu
  | succ j ih =>
    rw [pow_succ', Module.End.mul_apply]
    rw [conformalMode_weight s n _ _ ih]
    congr 1
    push_cast
    ring

private theorem dividedConformal_weight (s : Fin 3) (n : ℤ) (u : sector s) (w : ℂ)
    (hu : totalLZero u.val = w • u.val) (j : ℕ) :
    totalLZero (dividedTranslation L[s, n] j u).val =
      (w - (j : ℂ) * (n : ℂ)) • (dividedTranslation L[s, n] j u).val := by
  simp only [dividedTranslation, LinearMap.smul_apply, Submodule.coe_smul, map_smul,
    conformalPower_weight s n u w hu, smul_smul]
  rw [mul_comm]

/-- Physical exponent at integral index `k` for input weight `h / 9`. -/
def exponent (h k : ℤ) : ℚ := (k : ℚ) - 2 * (h : ℚ) / 9

private def inversionTerm (s : Fin 3) (w : ℂ) (u : sector s)
    (f : Module.Dual ℂ (totalLZero.eigenspace w)) (a : fixedStates) (k : ℤ) (j : ℕ) : ℂ :=
  f (gradeProjection w
    ((rightInsertion s (dividedTranslation L[s, 1] j u) a).coeff ((j : ℤ) - k)).val)

/-- Coordinate inversion with the positive branch of `(-z⁻²)^L(0)`.
The exponent `j - m - 2h/9` combines divided power `j` of the actual `L(1)`
with integral coefficient `m` of the actual right insertion at the inverse coordinate. -/
def invertedCoeff (s : Fin 3) (h : ℤ) (w : ℂ) (u : sector s)
    (f : Module.Dual ℂ (totalLZero.eigenspace w)) (a : fixedStates) (k : ℤ) : ℂ :=
  Complex.exp ((Real.pi : ℂ) * Complex.I * ((h : ℂ) / 9)) *
    ∑ j ∈ Finset.range (((h - 16) / 9).toNat + 1), inversionTerm s w u f a k j

/-- For a homogeneous input the displayed finite sum contains every
possibly nonzero term of the coordinate-inverted coefficient. -/
theorem invertedCoeff_eq_finsum (s : Fin 3) (h : ℤ) (w : ℂ) (u : sector s)
    (hu : totalLZero u.val = ((h : ℂ) / 9) • u.val)
    (f : Module.Dual ℂ (totalLZero.eigenspace w)) (a : fixedStates) (k : ℤ) :
    invertedCoeff s h w u f a k =
      Complex.exp ((Real.pi : ℂ) * Complex.I * ((h : ℂ) / 9)) *
        ∑ᶠ j : ℕ, inversionTerm s w u f a k j := by
  unfold invertedCoeff
  congr 1
  symm
  apply finsum_eq_sum_of_support_subset
  intro j hj
  by_contra hj'
  have hjlt : h - 16 < 9 * (j : ℤ) := by
    change ¬ j ∈ Finset.range (((h - 16) / 9).toNat + 1) at hj'
    rw [Finset.mem_range] at hj'
    omega
  have hjReal : (h : ℝ) - 16 < 9 * (j : ℝ) := by exact_mod_cast hjlt
  have hbelow : (h : ℝ) / 9 - (j : ℝ) < 16 / 9 := by linarith
  let v := dividedTranslation L[s, 1] j u
  have hw := dividedConformal_weight s 1 u ((h : ℂ) / 9) hu j
  have he : totalLZero v.val = (((h : ℝ) / 9 - (j : ℝ) : ℝ) : ℂ) • v.val := by
    simpa only [v, Int.cast_one, mul_one, Complex.ofReal_sub, Complex.ofReal_div,
      Complex.ofReal_intCast, Complex.ofReal_natCast, Complex.ofReal_ofNat] using hw
  have hz : v = 0 := by
    by_contra hv
    have hv' : v.val ≠ 0 := fun hz => hv (Subtype.ext hz)
    exact (not_le_of_gt hbelow) (totalLZero_minimum.2 ⟨v.val, hv', he⟩)
  apply hj
  change f (gradeProjection w ((rightInsertion s v a).coeff ((j : ℤ) - k)).val) = 0
  rw [hz]
  have hr : (rightInsertion s 0 a).coeff ((j : ℤ) - k) = 0 := by
    let n : ℤ := -((j : ℤ) - k) - 1
    rw [show (j : ℤ) - k = -n - 1 by dsimp [n]; omega]
    change rightMode s n 0 a = 0
    rw [map_zero, LinearMap.zero_apply]
  rw [hr, Submodule.coe_zero, map_zero, map_zero]

/-- The native twisted ground vector in rotation sector zero. -/
def ground : sector 0 := ⟨vacuum, vacuum_mem_sector_zero⟩

/-- The ground dual functional given by the zero-momentum constant coefficient. -/
def groundFunctional : Module.Dual ℂ (totalLZero.eigenspace (16 / 9 : ℂ)) :=
  ((MvPolynomial.lcoeff ℂ 0).comp (Finsupp.lapply 0)).comp
    (totalLZero.eigenspace (16 / 9 : ℂ)).subtype

private theorem groundFunctional_ground :
    groundFunctional (gradeProjection (16 / 9 : ℂ) ground.val) = 1 := by
  let v : totalLZero.eigenspace (16 / 9 : ℂ) :=
    ⟨vacuum, Module.End.mem_eigenspace_iff.mpr totalLZero_vacuum⟩
  change groundFunctional (gradeProjection (16 / 9 : ℂ) v.val) = 1
  rw [gradeProjection_self]
  change ((vacuum : State) 0).coeff 0 = 1
  simp [vacuum]

/-- Against the fixed vacuum, the paired ground insertion is a single nonzero
monomial of physical exponent `-32/9` and coefficient `exp(16πi/9)`. -/
theorem invertedCoeff_ground_vacuum :
    (∀ k : ℤ, invertedCoeff 0 16 (16 / 9) ground groundFunctional fixedVacuum k =
      if k = 0 then Complex.exp (16 * (Real.pi : ℂ) * Complex.I / 9) else 0) ∧
    exponent 16 0 = -32 / 9 ∧
    invertedCoeff 0 16 (16 / 9) ground groundFunctional fixedVacuum 0 ≠ 0 := by
  have hphase : (Real.pi : ℂ) * Complex.I * (((16 : ℤ) : ℂ) / 9) =
      16 * (Real.pi : ℂ) * Complex.I / 9 := by push_cast; ring
  have hcoeff (k : ℤ) : invertedCoeff 0 16 (16 / 9) ground groundFunctional fixedVacuum k =
      if k = 0 then Complex.exp (16 * (Real.pi : ℂ) * Complex.I / 9) else 0 := by
    unfold invertedCoeff
    rw [show (((16 : ℤ) - 16) / 9).toNat + 1 = 1 by decide,
      Finset.sum_range_one, hphase]
    simp only [inversionTerm, dividedTranslation, Nat.factorial_zero, Nat.cast_one, inv_one,
      pow_zero, one_smul, Module.End.one_apply, Nat.cast_zero, zero_sub]
    rw [rightInsertion_vacuum_coeff]
    by_cases hk : k = 0
    · subst k
      simp only [neg_zero, lt_irrefl, ite_false, Int.toNat_zero, dividedTranslation,
        Nat.factorial_zero, Nat.cast_one, inv_one, pow_zero, one_smul, Module.End.one_apply,
        ite_true, groundFunctional_ground, mul_one]
    · rw [ite_eq_right hk]
      by_cases hneg : -k < 0
      · simp only [ite_eq_left hneg, Submodule.coe_zero, map_zero, mul_zero]
      · rw [ite_eq_right hneg]
        let j := (-k).toNat
        have ht : sectorTranslation 0 = L[0, -1] := rfl
        have hw := dividedConformal_weight 0 (-1) ground (16 / 9) totalLZero_vacuum j
        have hne : (16 / 9 : ℂ) ≠ (16 / 9 : ℂ) - (j : ℂ) * ((-1 : ℤ) : ℂ) := by
          have hj : j ≠ 0 := by dsimp [j]; omega
          intro he
          have hzero : (j : ℂ) = 0 := by
            norm_num only [Int.cast_neg, Int.cast_one, mul_neg_one, sub_neg_eq_add] at he
            exact add_left_cancel (he.symm.trans (add_zero _).symm)
          exact hj (Nat.cast_eq_zero.mp hzero)
        rw [ht, gradeProjection_eq_zero hw hne, map_zero, mul_zero]
  refine ⟨hcoeff, by norm_num [exponent], ?_⟩
  rw [hcoeff, ite_eq_left rfl]
  exact Complex.exp_ne_zero _

#print axioms invertedCoeff_eq_finsum
#print axioms invertedCoeff_ground_vacuum

end
end D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeOppositeVacuum
