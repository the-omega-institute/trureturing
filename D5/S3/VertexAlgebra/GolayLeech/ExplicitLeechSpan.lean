/- GID: D5/S3/VertexAlgebra/GolayLeech/ExplicitLeechSpan
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/GolayLeech/ExplicitLeechSpan
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The explicit basis spans exactly all integral Golay-congruence vectors. -/
import D5.S3.VertexAlgebra.GolayLeech.ExplicitLeechBasis

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0

namespace D5.S3.VertexAlgebra.GolayLeech.ExplicitLeechSpan

open scoped BigOperators Matrix
open ExplicitGolayCode ExplicitLeechCongruence ExplicitLeechBasis

def basisRange : Submodule ℤ Coordinates := LinearMap.range basisMatrix.mulVecLin

theorem range_le_lattice : basisRange ≤ lattice := by
  rintro vector ⟨coordinates, rfl⟩
  have members : ∀ column, coordinates column • (fun axis => basisMatrix axis column) ∈ lattice := by
    intro column
    exact lattice.smul_mem (coordinates column) (basis_column_member column)
  have sum_member : (∑ column : Fin 24,
      coordinates column • (fun axis => basisMatrix axis column)) ∈ lattice :=
    lattice.sum_mem (fun column _ => members column)
  convert sum_member using 1
  ext axis
  simp [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]

theorem generator_mem_range (index : Fin 60) : generatorVector index ∈ basisRange := by
  exact ⟨fun column => generatorCoordinates column index, finite_generator_coordinates index⟩

def liftedCode (message : Message) : Coordinates :=
  fun axis => ∑ position, (message position).val * (generator axis position).val

theorem liftedCode_reduction (message : Message) : reduction (liftedCode message) = encode message := by
  ext axis
  simp [reduction, liftedCode, encode, Matrix.mulVec, dotProduct, ZMod.natCast_val,
    mul_comm]

theorem finite_generator_weight :
    ∀ position : Fin 12, (∑ axis, (generator axis position).val) = 8 := by
  decide

theorem liftedCode_sum (message : Message) :
    (∑ axis, liftedCode message axis) = 8 * ∑ position, ((message position).val : ℤ) := by
  simp only [liftedCode, Nat.cast_sum, Nat.cast_mul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, ← Nat.cast_sum, finite_generator_weight]
  simp only [Nat.cast_ofNat, Nat.cast_sum]
  rw [← Finset.sum_mul, mul_comm]

theorem twice_liftedCode_mem_range (message : Message) : (2 : ℤ) • liftedCode message ∈ basisRange := by
  have summands : ∀ position : Fin 12,
      ((message position).val : ℤ) • generatorVector ⟨position.val + 47, by omega⟩ ∈ basisRange := by
    intro position
    exact basisRange.smul_mem _ (generator_mem_range _)
  convert basisRange.sum_mem (fun position _ => summands position) using 1
  ext axis
  simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply, liftedCode, Nat.cast_sum, Nat.cast_mul]
  have values : ∀ position : Fin 12,
      generatorVector ⟨position.val + 47, by omega⟩ axis =
        2 * ((generator axis position).val : ℤ) := by
    intro position
    simp [generatorVector, show ¬ position.val + 47 < 24 by omega,
      show ¬ position.val + 47 < 47 by omega, show position.val + 47 < 59 by omega]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro position _
  rw [values position]
  ring

theorem difference_mem_range (axis : Fin 24) :
    (4 : ℤ) • (unitVector axis - unitVector 0) ∈ basisRange := by
  by_cases zero : axis = 0
  · simp [zero]
  · have positive : 0 < axis.val := by
      have : axis.val ≠ 0 := by simpa using zero
      omega
    convert generator_mem_range ⟨axis.val + 23, by omega⟩ using 1
    simp [generatorVector, show ¬ axis.val + 23 < 24 by omega,
      show axis.val + 23 < 47 by omega]

theorem four_even_sum_mem_range (vector : Coordinates)
    (even_sum : ∃ quotient : ℤ, ∑ axis, vector axis = 2 * quotient) :
    (4 : ℤ) • vector ∈ basisRange := by
  obtain ⟨quotient, total⟩ := even_sum
  have base : (8 : ℤ) • unitVector 0 ∈ basisRange := by
    simpa [generatorVector] using generator_mem_range 0
  have rest : (∑ axis, vector axis • ((4 : ℤ) • (unitVector axis - unitVector 0))) ∈ basisRange := by
    exact basisRange.sum_mem (fun axis _ => basisRange.smul_mem _ (difference_mem_range axis))
  convert basisRange.add_mem (basisRange.smul_mem quotient base) rest using 1
  ext axis
  change 4 * vector axis = quotient * (8 * unitVector 0 axis) +
    ∑ other, vector other * (4 * (unitVector other axis - unitVector 0 axis))
  have expanded : ∀ other : Fin 24,
      vector other * (4 * (unitVector other axis - unitVector 0 axis)) =
        4 * (vector other * unitVector other axis) -
        4 * (vector other * unitVector 0 axis) := by
    intro other
    ring
  simp_rw [expanded]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    ← Finset.sum_mul, total]
  have diagonal : (∑ other, vector other * unitVector other axis) = vector axis := by
    simp [unitVector]
  rw [diagonal]
  ring

theorem even_member_mem_range (vector half : Coordinates) (quotient : ℤ)
    (coordinates : ∀ axis, vector axis = 2 * half axis)
    (codeword : reduction half ∈ code) (total : ∑ axis, half axis = 4 * quotient) :
    vector ∈ basisRange := by
  obtain ⟨message, encoded⟩ := codeword
  let quarter : Coordinates := fun axis => (half axis - liftedCode message axis) / 2
  have residual_even : ∀ axis, half axis = liftedCode message axis + 2 * quarter axis := by
    intro axis
    have reduced : ((half axis - liftedCode message axis : ℤ) : Binary) = 0 := by
      have equality := congrFun ((liftedCode_reduction message).trans encoded) axis
      simp only [reduction] at equality
      push_cast
      rw [← equality]
      ring
    have residue : (half axis - liftedCode message axis) % 2 = 0 := by
      have value := congrArg (fun scalar : Binary => (scalar.val : ℤ)) reduced
      simpa only [ZMod.val_intCast, ZMod.val_zero, Nat.cast_zero, Nat.cast_ofNat] using value
    dsimp [quarter]
    omega
  have quarter_sum : ∑ axis, quarter axis =
      2 * (quotient - 2 * ∑ position, ((message position).val : ℤ)) := by
    have recovered_total : (∑ axis, half axis) = (∑ axis, liftedCode message axis) +
        2 * ∑ axis, quarter axis := by
      simp_rw [residual_even]
      simp [Finset.sum_add_distrib, Finset.mul_sum]
    rw [total, liftedCode_sum] at recovered_total
    omega
  have remainder_member : (4 : ℤ) • quarter ∈ basisRange :=
    four_even_sum_mem_range quarter ⟨_, quarter_sum⟩
  convert basisRange.add_mem (twice_liftedCode_mem_range message) remainder_member using 1
  ext axis
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [coordinates, residual_even]
  ring

theorem lattice_le_range : lattice ≤ basisRange := by
  intro vector is_member
  obtain ⟨parity, half, quotient, allowed, coordinates, codeword, total⟩ := is_member
  rcases allowed with rfl | rfl
  · apply even_member_mem_range vector half quotient
    · intro axis; simpa using coordinates axis
    · exact codeword
    · simpa using total
  · let shifted : Coordinates := vector - generatorVector 59
    have twist_member : member (generatorVector 59) := range_le_lattice (generator_mem_range 59)
    have shifted_member : member shifted := member_add vector (-generatorVector 59)
      ⟨1, half, quotient, Or.inr rfl, coordinates, codeword, total⟩
      (member_neg _ twist_member)
    obtain ⟨shifted_parity, shifted_half, shifted_quotient, shifted_allowed,
      shifted_coordinates, shifted_codeword, shifted_total⟩ := shifted_member
    have shifted_zero : shifted_parity = 0 := by
      have original_coordinate := coordinates (23 : Fin 24)
      have shifted_coordinate := shifted_coordinates (23 : Fin 24)
      have twist_coordinate : generatorVector 59 (23 : Fin 24) = 1 := by decide
      dsimp [shifted] at shifted_coordinate
      rw [twist_coordinate] at shifted_coordinate
      rcases shifted_allowed with zero | one
      · exact zero
      · omega
    subst shifted_parity
    have shifted_in_range : shifted ∈ basisRange :=
      even_member_mem_range shifted shifted_half shifted_quotient
        (by intro axis; simpa using shifted_coordinates axis) shifted_codeword
        (by simpa using shifted_total)
    have := basisRange.add_mem shifted_in_range (generator_mem_range 59)
    simpa [shifted] using this

theorem basis_span_identity : basisRange = lattice :=
  le_antisymm range_le_lattice lattice_le_range

theorem basis_congruence_identity (vector : Coordinates) :
    (∃ charge : Coordinates, basisMatrix *ᵥ charge = vector) ↔ congruences vector := by
  change vector ∈ basisRange ↔ congruences vector
  rw [basis_span_identity]
  exact member_iff_congruences vector

end D5.S3.VertexAlgebra.GolayLeech.ExplicitLeechSpan
