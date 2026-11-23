/- GID: D5/S3/VertexAlgebra/Lattice/ActualZhuRankOneOdd
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/ActualZhuRankOneOdd
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Abe's first odd Zhu product and the level-three relation on the native carrier. -/

import D5.S3.VertexAlgebra.Lattice.ActualZhuCurrentRelations
import D5.S3.VertexAlgebra.Sectors.LatticeDualCosetModule
import D5.S3.VertexAlgebra.LatticeInvolution
import Mathlib.Analysis.Real.Sqrt

/-!
T. Abe, *Fusion rules for the free bosonic orbifold vertex operator algebra*,
https://arxiv.org/abs/math/9907120v1, equation (4.2) and the singular vector
in Step 2 of the proof of Theorem 4.5. The coefficient of `L(-4)` in (4.2)
is `-1/2`. The calculations use the charge-zero summand of the existing
Gram-[2] lattice and its actual state-field map.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.Lattice.ActualZhuRankOneOdd

open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration
open LatticeAllStateField LatticeAllStateReconstruction LatticePositiveEnergy
open LatticeActualConformalState LatticeSugawaraCurrents LatticeInvolution
open FieldNormalProduct MvPolynomial
open scoped BigOperators VertexOperator

open private fractionalLattice multiplication_recursion
  from D5.S3.VertexAlgebra.Sectors.LatticeDualCosetModule
open private derivative_modes from D5.S3.VertexAlgebra.LatticeAllStateField

noncomputable section

/-- The native even rank-one lattice of Gram matrix [2]. -/
abbrev datum : LatticeData := fractionalLattice

local instance : NeZero datum.rank := ⟨by decide⟩

local instance : Subsingleton (Fin datum.rank) := by
  change Subsingleton (Fin 1)
  infer_instance

private theorem sum_rank_one {M : Type*} [AddCommMonoid M] (f : Fin datum.rank → M) :
    ∑ i, f i = f 0 := by
  classical
  exact Finset.sum_eq_single 0
    (fun i _ hi => (hi (Subsingleton.elim i 0)).elim)
    (fun hn => (hn (Finset.mem_univ 0)).elim)

private def lift : Oscillator datum →ₗ[ℂ] Carrier datum := Finsupp.lsingle 0
private def x (r : ℕ) : Oscillator datum := X (0, r)

local notation "J" => (neutralMode datum 0)
local notation "A" => (neutralField datum 0)

private theorem current_neg (n : ℤ) (p : Oscillator datum) (hn : n < 0) :
    J n (lift p) = lift (x (-n - 1).toNat * p) := by
  simp [lift, x, neutralPolynomialMode, hn]

private theorem current_one (n : ℤ) :
    J n (lift 1) = if n < 0 then lift (x (-n - 1).toNat) else 0 := by
  classical
  by_cases hn : n < 0
  · rw [ite_eq_left hn, current_neg _ _ hn, mul_one]
  · by_cases hz : n = 0
    · subst n
      simp [lift, neutralPolynomialMode, bilinear]
    · simp [lift, neutralPolynomialMode, hn, hz, Derivation.coeFn_coe]

private theorem current_x (n : ℤ) (r : ℕ) :
    J n (lift (x r)) =
      if n < 0 then lift (x (-n - 1).toNat * x r)
      else if n = (r : ℤ) + 1 then ((n : ℂ) * 2) • lift 1 else 0 := by
  classical
  by_cases hn : n < 0
  · rw [ite_eq_left hn, current_neg _ _ hn]
  rw [ite_eq_right hn]
  by_cases hz : n = 0
  · subst n
    simp [lift, neutralPolynomialMode, bilinear, show (0 : ℤ) ≠ (r : ℤ) + 1 by omega]
  have hindex : (n - 1).toNat = r ↔ n = (r : ℤ) + 1 := by omega
  by_cases hr : n = (r : ℤ) + 1
  · rw [ite_eq_left hr]
    have hd : (n - 1).toNat = r := hindex.mpr hr
    simp [lift, x, neutralPolynomialMode, hn, hz, sum_rank_one, hd,
      Derivation.coeFn_coe, show datum.G 0 0 = 2 by rfl, smul_smul]
  · rw [ite_eq_right hr]
    have hd : n.toNat - 1 ≠ r := by omega
    simp [lift, x, neutralPolynomialMode, hn, hz, sum_rank_one, Derivation.coeFn_coe, hd]

private theorem derivative_two (n : ℤ) :
    ((dividedDerivative 2 A)[[n]]) =
      ((n : ℂ) * ((n : ℂ) - 1) / 2) • J (n - 2) := by
  rw [show ((dividedDerivative 2 A)[[n]]) =
      ((Ring.choose (-n - 1 + 2 : ℤ) 2 : ℤ) : ℂ) • J (n - 2) from
    derivative_modes datum (0, 2) n]
  congr 1
  have h : 2 * Ring.choose (-n - 1 + 2 : ℤ) 2 =
      (-n - 1 + 2) * (-n - 1 + 2 - 1) := by
    simpa only [show Nat.choose 2 1 = 2 by decide, nsmul_eq_mul,
      Nat.cast_ofNat, Ring.choose_one_right, Nat.cast_one,
      show (2 : ℕ) - 1 = 1 by decide] using
      (Ring.choose_smul_choose (-n - 1 + 2 : ℤ) (n := 2) (k := 1) (by decide))
  have hc : (2 : ℂ) * ((Ring.choose (-n - 1 + 2 : ℤ) 2 : ℤ) : ℂ) =
      (((-n - 1 + 2 : ℤ)) : ℂ) * (((-n - 1 + 2 - 1 : ℤ)) : ℂ) := by
    exact_mod_cast h
  push_cast at hc
  apply (eq_div_iff (by norm_num : (2 : ℂ) ≠ 0)).mpr
  linear_combination hc

/-- Both normal-order halves are finite on the one-current input. -/
private theorem normal_row (left : VertexOperator ℂ (Carrier datum)) (q : ℤ) (r : ℕ)
    (hq : (r : ℤ) + 1 < q + 8)
    (hleft : ∀ j : ℕ, 8 ≤ j → (left[[(j : ℤ)]]) (lift (x r)) = 0) :
    (((normalMinusOne left A).1)[[q]]) (lift (x r)) =
      (∑ j ∈ Finset.range 8, (left[[-(j : ℤ) - 1]]) (J (q + j) (lift (x r)))) +
      (∑ j ∈ Finset.range 8, J (q - j - 1) ((left[[(j : ℤ)]]) (lift (x r)))) := by
  rw [(normalMinusOne left A).2]
  simp only [neutralField_ncoeff]
  congr 1
  · apply finsum_eq_sum_of_support_subset
    intro j hj
    rw [Finset.mem_coe, Finset.mem_range]
    by_contra! hj'
    have hz : J (q + j) (lift (x r)) = 0 := by
      rw [current_x, ite_eq_right (by omega), ite_eq_right (by omega)]
    exact hj (by simp [hz])
  · apply finsum_eq_sum_of_support_subset
    intro j hj
    rw [Finset.mem_coe, Finset.mem_range]
    by_contra! hj'
    exact hj (by simp [hleft j hj'])

private def normalization : ℂ := (↑(Real.sqrt 2) : ℂ)⁻¹

private theorem normalization_mul : normalization * normalization = (1 / 2 : ℂ) := by
  have hs : (↑(Real.sqrt 2) : ℂ) ^ 2 = 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  rw [← pow_two, normalization, inv_pow, hs, one_div]

/-- Modes of the unit-length current in Abe's conventions. -/
def h (n : ℤ) : Module.End ℂ (Carrier datum) := normalization • J n

/-- The lowest odd one-current vector. -/
def oddCurrent : Carrier datum := normalization • currentState datum 0

private theorem oddCurrent_eq : oddCurrent = normalization • lift (x 0) := rfl

/-- The native lattice involution acts on the normalized current by minus one. -/
theorem oddCurrent_parity : theta datum oddCurrent = -oddCurrent := by
  change thetaLinear datum (normalization • currentState datum 0) =
    -(normalization • currentState datum 0)
  simp only [currentState, map_smul, theta_single, neg_zero, sigma_X,
    Finsupp.single_neg, smul_neg]

/-- Abe's even weight-four vector `h(-3) h(-1) 1`. -/
def abeState : Carrier datum := h (-3) (h (-1) (vacuum datum))

private def inverseGram : Matrix (Fin datum.rank) (Fin datum.rank) ℂ := fun _ _ => 1 / 2

/-- The actual Sugawara modes for the inverse of [2]. -/
def L (m : ℤ) : Module.End ℂ (Carrier datum) := sugawaraMode datum inverseGram m

private theorem abeState_eq :
    abeState = (1 / 2 : ℂ) • lift (x 2 * x 0) := by
  change (normalization • J (-3)) ((normalization • J (-1)) (lift 1)) = _
  have h₁ : J (-1) (lift 1) = lift (x 0) := by norm_num [current_one]
  have h₃ : J (-3) (lift (x 0)) = lift (x 2 * x 0) := by norm_num [current_x]
  simp only [LinearMap.smul_apply, h₁, map_smul, h₃, smul_smul, normalization_mul]

private theorem abeState_grade : abeState ∈ grade datum 4 := by
  rw [abeState_eq]
  apply Submodule.smul_mem
  have hp : IsWeightedHomogeneous (oscillatorWeight datum) (x 2 * x 0) 4 :=
    (isWeightedHomogeneous_X ℂ (oscillatorWeight datum) (0, 2)).mul
      (isWeightedHomogeneous_X ℂ (oscillatorWeight datum) (0, 0))
  simpa [chargeEnergy_zero, lift] using
    ActualZhuCurrentRelations.single_weighted_grade datum 0 (x 2 * x 0) 4 hp

private theorem abeState_raw_field :
    Y datum (lift (x 2 * x 0)) = (normalMinusOne (dividedDerivative 2 A) A).1 := by
  change Y datum (Finsupp.single 0 (X ((0 : Fin datum.rank), 2) * x 0)) = _
  calc
    _ = (normalMinusOne (dividedDerivative 2 A) (Y datum (currentState datum 0))).1 :=
      multiplication_recursion datum (0, 2) 0 (x 0)
    _ = _ := by rw [current_state_field]

private theorem abe_mode_row (q : ℤ) (hq : (1 : ℤ) < q + 8) :
    mu datum abeState q oddCurrent =
      normalization • ((1 / 2 : ℂ) •
        ((∑ j ∈ Finset.range 8,
          ((dividedDerivative 2 A)[[-(j : ℤ) - 1]]) (J (q + j) (lift (x 0)))) +
        (∑ j ∈ Finset.range 8,
          J (q - j - 1) (((dividedDerivative 2 A)[[(j : ℤ)]]) (lift (x 0)))))) := by
  have hv : mu datum abeState q oddCurrent =
      normalization • mu datum abeState q (lift (x 0)) := by
    simp only [mu, oddCurrent_eq, map_smul]
  rw [hv]
  simp only [mu, abeState_eq, map_smul, Pi.smul_apply, LinearMap.smul_apply, abeState_raw_field]
  rw [normal_row (dividedDerivative 2 A) q 0 (by simpa using hq)]
  intro j hj
  rw [derivative_two, LinearMap.smul_apply, current_x, ite_eq_right (by omega),
    ite_eq_right (by omega), smul_zero]

set_option maxHeartbeats 1000000 in
-- Evaluating both finite normal-order sums at the five indices uses extra heartbeats.
/-- The five modes in the weight-four Zhu row, with the unit-normalized input
and pair. The variables in these coordinates are the native Gram-[2] variables. -/
theorem abe_modes_on_odd :
    mu datum abeState (-1) oddCurrent =
      normalization • lift ((9 : ℂ) • x 4 + (1 / 2 : ℂ) • (x 2 * x 0 ^ 2)) ∧
    mu datum abeState 0 oddCurrent = normalization • lift ((6 : ℂ) • x 3) ∧
    mu datum abeState 1 oddCurrent = normalization • lift ((4 : ℂ) • x 2) ∧
    mu datum abeState 2 oddCurrent = normalization • lift ((3 : ℂ) • x 1) ∧
    mu datum abeState 3 oddCurrent = normalization • lift ((3 : ℂ) • x 0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  all_goals
    rw [abe_mode_row _ (by norm_num)]
    apply congrArg (fun v : Carrier datum => normalization • v)
    norm_num [Finset.sum_range_succ, derivative_two, LinearMap.smul_apply,
      current_x, current_one, current_neg, map_smul, smul_smul] <;>
      simp only [← lift.map_add, ← lift.map_smul] <;>
      apply congrArg lift <;>
      (try simp only [pow_two, mul_comm, mul_assoc]) <;> module

private theorem sugawara_row (m : ℤ) (r : ℕ)
    (hm : (r : ℤ) + 1 < (m + 1) + 8) (hr : r + 1 < 8) :
    L m (lift (x r)) =
      (1 / 4 : ℂ) • ((∑ j ∈ Finset.range 8, J (-(j : ℤ) - 1) (J (m + 1 + j) (lift (x r)))) +
        (∑ j ∈ Finset.range 8, J (m + 1 - j - 1) (J j (lift (x r))))) := by
  have hn : (((normalMinusOne A A).1)[[m + 1]]) (lift (x r)) =
      (∑ j ∈ Finset.range 8, (A[[-(j : ℤ) - 1]]) (J (m + 1 + j) (lift (x r)))) +
      (∑ j ∈ Finset.range 8, J (m + 1 - j - 1) ((A[[(j : ℤ)]]) (lift (x r)))) := by
    apply normal_row A (m + 1) r hm
    intro j hj
    rw [neutralField_ncoeff, current_x, ite_eq_right (by omega), ite_eq_right (by omega)]
  simp only [neutralField_ncoeff] at hn
  norm_num [L, sugawaraMode, sugawaraField, sum_rank_one, inverseGram,
    quadraticSummand, map_smul, LinearMap.smul_apply, smul_smul, hn]

set_option maxHeartbeats 1000000 in
-- Evaluating the finite normal-order sums for all eight mode entries uses extra heartbeats.
private theorem sugawara_table :
    L (-1) (lift (x 0)) = lift (x 1) ∧
    L (-1) (lift (x 1)) = lift ((2 : ℂ) • x 2) ∧
    L (-1) (lift (x 2)) = lift ((3 : ℂ) • x 3) ∧
    L (-2) (lift (x 1)) = lift ((2 : ℂ) • x 3 + (1 / 4 : ℂ) • (x 0 ^ 2 * x 1)) ∧
    L (-2) (lift (x 2)) = lift ((3 : ℂ) • x 4 + (1 / 4 : ℂ) • (x 0 ^ 2 * x 2)) ∧
    L (-3) (lift (x 0)) = lift (x 3 + (1 / 2 : ℂ) • (x 0 ^ 2 * x 1)) ∧
    L (-3) (lift (x 1)) = lift ((2 : ℂ) • x 4 + (1 / 2 : ℂ) • (x 0 * x 1 ^ 2)) ∧
    L (-4) (lift (x 0)) =
      lift (x 4 + (1 / 2 : ℂ) • (x 0 ^ 2 * x 2) + (1 / 4 : ℂ) • (x 0 * x 1 ^ 2)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    rw [sugawara_row _ _ (by norm_num) (by norm_num)]
    norm_num [Finset.sum_range_succ, current_x, current_one, current_neg, map_smul, smul_smul] <;>
      simp only [← lift.map_add, ← lift.map_smul] <;>
      apply congrArg lift <;>
      (try simp only [pow_two, mul_comm, mul_left_comm, mul_assoc]) <;> module

/-- Abe (4.2) on the charge-zero one-current vector of the original carrier. -/
theorem abe_zhu_identity :
    ActualZhuProduct.star datum abeState oddCurrent =
      (3 : ℂ) • oddCurrent + (12 : ℂ) • L (-1) oddCurrent +
      (12 : ℂ) • L (-1) (L (-1) oddCurrent) - (8 : ℂ) • L (-3) oddCurrent +
      (16 : ℂ) • L (-2) (L (-1) oddCurrent) - (1 / 2 : ℂ) • L (-4) oddCurrent +
      (1 / 4 : ℂ) • L (-3) (L (-1) oddCurrent) +
      (3 / 2 : ℂ) • L (-2) (L (-1) (L (-1) oddCurrent)) := by
  obtain ⟨hm, h₀, h₁, h₂, h₃⟩ := abe_modes_on_odd
  obtain ⟨h10, h11, _, h21, h22, h30, h31, h40⟩ := sugawara_table
  have h11' : L (-1) (lift (x 1)) = (2 : ℂ) • lift (x 2) := by rw [h11, map_smul]
  rw [ActualZhuProduct.star_homogeneous datum 4 _ _ abeState_grade]
  norm_num [Finset.sum_range_succ, Nat.choose, hm, h₀, h₁, h₂, h₃]
  simp only [oddCurrent_eq, map_smul, h10, h11', h21, h22, h30, h31, h40]
  simp only [← lift.map_smul, ← lift.map_add, ← lift.map_sub]
  apply congrArg lift
  rw [mul_comm (x 2) (x 0 ^ 2)]
  module

/-- The image of Abe's level-three singular vector on the actual odd current. -/
theorem odd_level_three_null :
    (2 : ℂ) • L (-3) oddCurrent - (4 : ℂ) • L (-2) (L (-1) oddCurrent) +
      L (-1) (L (-1) (L (-1) oddCurrent)) = 0 := by
  obtain ⟨h10, h11, h12, h21, _, h30, _, _⟩ := sugawara_table
  -- Expose the scalar from L(-1)² before evaluating the last L(-1).
  have h11' : L (-1) (lift (x 1)) = (2 : ℂ) • lift (x 2) := by rw [h11, map_smul]
  simp only [oddCurrent_eq, map_smul, h10, h11', h12, h21, h30]
  rw [← lift.map_zero]
  simp only [← lift.map_smul, ← lift.map_add, ← lift.map_sub]
  apply congrArg lift
  module

end
end D5.S3.VertexAlgebra.Lattice.ActualZhuRankOneOdd
