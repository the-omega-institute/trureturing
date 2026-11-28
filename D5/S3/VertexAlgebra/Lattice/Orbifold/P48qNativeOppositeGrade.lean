/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/P48qNativeOppositeGrade
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/Orbifold/P48qNativeOppositeGrade
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Conformal grade selection for the native opposite coefficients. -/

import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeOppositeVacuum

/-! The mixed Borcherds identity with the actual conformal state gives the grade
of a right insertion coefficient and hence the support after coordinate inversion. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeOppositeGrade

open scoped BigOperators VertexOperator
open HalfFockSpectralFiberSource (actualInverse)
open LatticeActualConformalState (omega)
open LatticeActualConformalWard (omega_product)
open LatticeAllStateReconstruction (mu)
open LatticeSugawaraCurrents (sugawaraMode)
open P48qNativeConformalSector
  (fixedStates sector fixedField fixedField_borcherds fixedField_conformal_zero
    fixedOmega fixedProduct)
open P48qNativeFixedRightInsertion (rightInsertion rightInsertion_translation sectorTranslation)
open P48qNativeFixedRightJacobi (rightInsertion_borcherds)
open P48qNativeOppositeVacuum (exponent gradeProjection invertedCoeff)
open P48qTwistedChargeAction (lattice)
open P48qTwistedStateEnergy (totalLZero totalLZero_minimum)
open StateField.BorcherdsPermutations (dividedTranslation)
open StateFieldResidueReconstruction (epsilon integerBinomial)
open private rightMode sectorMode from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeFixedRightJacobi
open private fixedField_translate_coeff signedBinomial_zero_sum from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeFixedRightInsertion
open private dividedConformal_weight gradeProjection_eq_zero inversionTerm from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeOppositeVacuum
open private finsum_range from D5.S3.VertexAlgebra.StateField.BorcherdsPermutations

noncomputable section

local notation "R" => rightMode
local notation "sourceLZero" => sugawaraMode lattice (actualInverse lattice) 0
local notation:max "L[" s "," n "]" =>
  HVertexOperator.coeff (fixedField s fixedOmega) (-(n : ℤ) - 2)

/-- The normalized fixed mode sends the actual weight `h / 9` to
`(h + 9 * (e - m - 1)) / 9`. -/
theorem fixedMode_weight (s : Fin 3) (a : fixedStates) (u : sector s)
    (e h : ℤ) (ha : sourceLZero a.val = (e : ℂ) • a.val)
    (hu : totalLZero u.val = ((h : ℂ) / 9) • u.val) (m : ℤ) :
    totalLZero (((fixedField s a)[[m]]) u).val =
      (((h + 9 * (e - m - 1) : ℤ) : ℂ) / 9) • (((fixedField s a)[[m]]) u).val := by
  have hSector (v : sector s) :
      (((fixedField s fixedOmega)[[1]]) v).val = totalLZero v.val := by
    rw [VertexOperator.ncoeff_apply, show -(1 : ℤ) - 1 = -2 by decide]
    exact fixedField_conformal_zero s v
  have hInput : ((fixedField s fixedOmega)[[1]]) u = ((h : ℂ) / 9) • u := by
    apply Subtype.ext
    rw [hSector, Submodule.coe_smul, hu]
  obtain ⟨N, hcut, hB⟩ := fixedField_borcherds s fixedOmega a
  let term (j : ℕ) : sector s :=
    Ring.choose (1 : ℂ) j • ((fixedField s (fixedProduct fixedOmega a j))[[1 + m - j]]) u
  have hJacobi := hB 1 m 0 u
  simp only [signedBinomial_zero_sum, epsilon, zpow_zero, one_smul, Nat.cast_zero,
    Int.toNat_natCast, Int.cast_one, add_zero, zero_add, sub_zero] at hJacobi
  change ((fixedField s fixedOmega)[[1]]) (((fixedField s a)[[m]]) u) -
    ((fixedField s a)[[m]]) (((fixedField s fixedOmega)[[1]]) u) =
      ∑ j ∈ Finset.range N, term j at hJacobi
  have support (n : ℕ) (hz : ∀ j ≥ n, term j = 0) :
      Function.support term ⊆ ↑(Finset.range n) := by
    intro j hj
    exact Finset.mem_range.mpr (lt_of_not_ge (fun hnj => hj (hz j hnj)))
  have hN := support N (by
    intro j hj
    simp only [term, hcut j (by exact_mod_cast hj), map_zero, VertexOperator.ncoeff_apply,
      Pi.zero_apply, LinearMap.zero_apply, smul_zero])
  have hTwo := support 2 (by
    intro j hj
    have hChoose : Ring.choose (1 : ℂ) j = 0 := by
      rw [← (Nat.cast_one : ((1 : ℕ) : ℂ) = 1), Ring.choose_natCast,
        Nat.choose_eq_zero_of_lt (show 1 < j by omega), Nat.cast_zero]
    simp only [term, hChoose, zero_smul])
  rw [← finsum_eq_sum_of_support_subset term hN,
    finsum_eq_sum_of_support_subset term hTwo] at hJacobi
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at hJacobi
  have h0 : term 0 = -((m + 1 : ℤ) : ℂ) • ((fixedField s a)[[m]]) u := by
    have hDerivative := fixedField_translate_coeff s a u (-(m + 1) - 1)
    have hIndex : -(m + 1) - 1 + 1 = -m - 1 := by omega
    have hScalar : ((-(m + 1) - 1 + 1 : ℤ) : ℂ) = -((m + 1 : ℤ) : ℂ) := by
      push_cast
      ring
    rw [hScalar, hIndex] at hDerivative
    simpa only [term, Ring.choose_zero_right, Nat.cast_zero, sub_zero, one_smul,
      show (1 : ℤ) + m = m + 1 by omega, VertexOperator.ncoeff_apply] using hDerivative
  have hSource : fixedProduct fixedOmega a 1 = (e : ℂ) • a := by
    apply Subtype.ext
    exact (omega_product lattice (actualInverse lattice) a.val 1).trans ha
  have h1 : term 1 = (e : ℂ) • ((fixedField s a)[[m]]) u := by
    change Ring.choose (1 : ℂ) 1 • sectorMode s (1 + m - 1) (fixedProduct fixedOmega a 1) u = _
    rw [show (1 : ℤ) + m - 1 = m by omega, hSource, map_smul, LinearMap.smul_apply,
      Ring.choose_one_right, one_smul] <;> rfl
  rw [h0, h1, hInput, map_smul] at hJacobi
  have hValue := congrArg (fun v : sector s => v.val) hJacobi
  simp only [Submodule.coe_sub, Submodule.coe_add, Submodule.coe_smul, hSector] at hValue
  let v := (((fixedField s a)[[m]]) u).val
  change totalLZero v - ((h : ℂ) / 9) • v =
    (-((m + 1 : ℤ) : ℂ)) • v + (e : ℂ) • v at hValue
  calc
    totalLZero v = ((-((m + 1 : ℤ) : ℂ)) • v + (e : ℂ) • v) + ((h : ℂ) / 9) • v :=
      eq_add_of_sub_eq hValue
    _ = _ := by
      rw [← add_smul, ← add_smul]
      congr 1
      push_cast
      ring

/-- Actual fixed-mode truncation at the lower endpoint of the twisted
spectrum. The bound is independent of the evaluation grade and test state. -/
theorem fixedMode_eq_zero_of_below_minimum (s : Fin 3) (a : fixedStates) (u : sector s)
    (e h : ℤ) (ha : sourceLZero a.val = (e : ℂ) • a.val)
    (hu : totalLZero u.val = ((h : ℂ) / 9) • u.val) (m : ℤ)
    (hm : h + 9 * (e - m - 1) < 16) :
    ((fixedField s a)[[m]]) u = 0 := by
  let H : ℤ := h + 9 * (e - m - 1)
  let v := ((fixedField s a)[[m]]) u
  have hWeight : totalLZero v.val = (((H : ℝ) / 9 : ℝ) : ℂ) • v.val := by
    simpa only [v, H, Complex.ofReal_div, Complex.ofReal_intCast, Complex.ofReal_ofNat] using
      fixedMode_weight s a u e h ha hu m
  by_contra hv
  have hMin := totalLZero_minimum.2 ⟨v.val, fun hz => hv (Subtype.ext hz), hWeight⟩
  have hH : H < 16 := hm
  have hBelow : (H : ℝ) < 16 := by exact_mod_cast hH
  linarith

private theorem rightMode_weight (s : Fin 3) (n : ℤ) (u : sector s) (b : fixedStates)
    (vWeight d : ℂ) (hu : totalLZero u.val = vWeight • u.val)
    (hb : sourceLZero b.val = d • b.val) :
    totalLZero (R s n u b).val = (vWeight + d - ((n + 1 : ℤ) : ℂ)) • (R s n u b).val := by
  have hSector (v : sector s) :
      (((fixedField s fixedOmega)[[1]]) v).val = totalLZero v.val := by
    rw [VertexOperator.ncoeff_apply, show -(1 : ℤ) - 1 = -2 by decide]
    exact fixedField_conformal_zero s v
  have hInput : ((fixedField s fixedOmega)[[1]]) u = vWeight • u := by
    apply Subtype.ext
    rw [hSector, Submodule.coe_smul, hu]
  have hSource : fixedProduct fixedOmega b 1 = d • b := by
    apply Subtype.ext
    change mu lattice (omega lattice (actualInverse lattice)) 1 b.val = d • b.val
    rw [omega_product, show (1 : ℤ) - 1 = 0 by decide]
    exact hb
  have hTranslation :
      R s (1 + n) (((fixedField s fixedOmega)[[0]]) u) b =
        (-((n + 1 : ℤ) : ℂ)) • R s n u b := by
    change (rightInsertion s (sectorTranslation s u) b).coeff (-(1 + n) - 1) =
      (-((n + 1 : ℤ) : ℂ)) • (rightInsertion s u b).coeff (-n - 1)
    rw [rightInsertion_translation, show -(1 + n) - 1 + 1 = -n - 1 by omega,
      show ((-n - 1 : ℤ) : ℂ) = -((n + 1 : ℤ) : ℂ) by push_cast <;> ring]
  let left (i : ℕ) : sector s :=
    integerBinomial 1 i • R s (1 + n - (i : ℤ)) (((fixedField s fixedOmega)[[0 + (i : ℤ)]]) u) b
  let right (i : ℕ) : sector s :=
    ((-1 : ℂ) ^ i * integerBinomial 0 i) •
      (((fixedField s fixedOmega)[[1 + 0 - (i : ℤ)]]) (R s (n + (i : ℤ)) u b) -
        epsilon 0 • R s (n + 0 - (i : ℤ)) u (fixedProduct fixedOmega b (1 + (i : ℤ))))
  obtain ⟨_, _, _, hJacobi⟩ := rightInsertion_borcherds s fixedOmega b u 1 n 0
  change (∑ᶠ i : ℕ, left i) = ∑ᶠ i : ℕ, right i at hJacobi
  have hLeft : (∑ᶠ i : ℕ, left i) = left 0 + left 1 := by
    rw [finsum_range (N := 2)]
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    · intro i hi
      have hChoose : integerBinomial 1 i = 0 := by
        rw [integerBinomial, show (1 : ℤ) = ((1 : ℕ) : ℤ) by rfl, Ring.choose_natCast,
          Nat.choose_eq_zero_of_lt (show 1 < i by omega), Nat.cast_zero, Int.cast_zero]
      simp only [left, hChoose, zero_smul]
  have hRight : (∑ᶠ i : ℕ, right i) = right 0 := by
    apply finsum_eq_single
    intro i hi
    simp only [right, integerBinomial, Ring.choose_zero_pos ℤ (Nat.pos_of_ne_zero hi),
      Int.cast_zero, mul_zero, zero_smul]
  have hLeftZero : left 0 = (-((n + 1 : ℤ) : ℂ)) • R s n u b := by
    simp only [left, integerBinomial, Ring.choose_zero_right, Int.cast_one, one_smul,
      Nat.cast_zero, sub_zero, add_zero, hTranslation]
  have hLeftOne : left 1 = vWeight • R s n u b := by
    simp only [left, integerBinomial, Ring.choose_one_right, Int.cast_one, one_smul,
      Nat.cast_one, zero_add, show 1 + n - 1 = n by omega, hInput, LinearMap.map_smul₂]
  have hRightZero :
      right 0 = ((fixedField s fixedOmega)[[1]]) (R s n u b) - d • R s n u b := by
    simp only [right, pow_zero, integerBinomial, Ring.choose_zero_right, Int.cast_one,
      mul_one, one_smul, Nat.cast_zero, add_zero, sub_zero, epsilon, zpow_zero, hSource,
      map_smul]
  rw [hLeft, hRight, hLeftZero, hLeftOne, hRightZero] at hJacobi
  have hValue := congrArg (fun v : sector s => v.val) hJacobi.symm
  simp only [Submodule.coe_add, Submodule.coe_sub, Submodule.coe_smul, hSector] at hValue
  let v := (R s n u b).val
  change totalLZero v - d • v = (-((n + 1 : ℤ) : ℂ)) • v + vWeight • v at hValue
  change totalLZero v = (vWeight + d - ((n + 1 : ℤ) : ℂ)) • v
  calc
    totalLZero v = ((-((n + 1 : ℤ) : ℂ)) • v + vWeight • v) + d • v :=
      eq_add_of_sub_eq hValue
    _ = _ := by
      rw [← add_smul, ← add_smul]
      congr 1
      ring

/-- A nonzero opposite coefficient selects a single evaluation grade, equivalently
a single physical exponent. The exponent is cast from `ℚ` into the scalar field. -/
theorem invertedCoeff_grade_of_ne_zero (s : Fin 3) (h : ℤ) (w d : ℂ) (u : sector s)
    (hu : totalLZero u.val = ((h : ℂ) / 9) • u.val)
    (f : Module.Dual ℂ (totalLZero.eigenspace w)) (a : fixedStates)
    (ha : sourceLZero a.val = d • a.val) (k : ℤ)
    (hnonzero : invertedCoeff s h w u f a k ≠ 0) :
    w = (h : ℂ) / 9 + d - (k : ℂ) ∧
      (exponent h k : ℂ) = d - (h : ℂ) / 9 - w := by
  have hgrade : w = (h : ℂ) / 9 + d - (k : ℂ) := by
    by_contra hne
    apply hnonzero
    unfold invertedCoeff
    refine mul_eq_zero.mpr (Or.inr ?_)
    apply Finset.sum_eq_zero
    intro j _
    unfold inversionTerm
    let v := dividedTranslation L[s, 1] j u
    have hv : totalLZero v.val = ((h : ℂ) / 9 - (j : ℂ)) • v.val := by
      simpa only [v, Int.cast_one, mul_one] using
        dividedConformal_weight s 1 u ((h : ℂ) / 9) hu j
    let n : ℤ := k - (j : ℤ) - 1
    have hn : -n - 1 = (j : ℤ) - k := by dsimp [n]; omega
    have hshift : (h : ℂ) / 9 - (j : ℂ) + d - ((n + 1 : ℤ) : ℂ) =
        (h : ℂ) / 9 + d - (k : ℂ) := by
      rw [show n + 1 = k - (j : ℤ) by dsimp [n]; omega]
      push_cast
      ring
    have hMode := rightMode_weight s n v a _ d hv ha
    rw [hshift] at hMode
    change f (gradeProjection w ((rightInsertion s v a).coeff ((j : ℤ) - k)).val) = 0
    rw [← hn]
    change f (gradeProjection w (R s n v a).val) = 0
    rw [gradeProjection_eq_zero hMode hne, map_zero]
  refine ⟨hgrade, ?_⟩
  rw [hgrade, exponent]
  simp only [Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_intCast, Rat.cast_ofNat]
  ring

end
end D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeOppositeGrade
