/- GID: D5/S3/VertexAlgebra/GolayLeech/ExplicitLeechCongruence
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/GolayLeech/ExplicitLeechCongruence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The actual Golay congruences define an even rootless integer lattice. -/
import D5.S3.VertexAlgebra.GolayLeech.ExplicitGolayWeights
import Mathlib.Algebra.Module.Submodule.Lattice

set_option autoImplicit false
set_option maxHeartbeats 0

namespace D5.S3.VertexAlgebra.GolayLeech.ExplicitLeechCongruence

open scoped BigOperators
open ExplicitGolayCode ExplicitGolayWeights

abbrev Coordinates := Fin 24 → ℤ

def reduction (vector : Coordinates) : Word := fun axis => (vector axis : Binary)

def member (vector : Coordinates) : Prop :=
  ∃ (parity : ℤ) (half : Coordinates) (quotient : ℤ),
    (parity = 0 ∨ parity = 1) ∧
    (∀ axis, vector axis = parity + 2 * half axis) ∧
    reduction half ∈ code ∧ ∑ axis, half axis = 2 * parity + 4 * quotient

def congruences (vector : Coordinates) : Prop :=
  ∃ parity : ℤ, (parity = 0 ∨ parity = 1) ∧
    (∀ axis, vector axis % 2 = parity) ∧
    reduction (fun axis => (vector axis - parity) / 2) ∈ code ∧
    (∑ axis, vector axis) % 8 = 4 * parity

theorem member_iff_congruences (vector : Coordinates) :
    member vector ↔ congruences vector := by
  constructor
  · rintro ⟨parity, half, quotient, allowed, coordinates, codeword, total⟩
    refine ⟨parity, allowed, ?_, ?_, ?_⟩
    · intro axis
      rcases allowed with rfl | rfl <;> rw [coordinates axis] <;> omega
    · have recovered : (fun axis => (vector axis - parity) / 2) = half := by
        funext axis
        rw [coordinates axis]
        omega
      rwa [recovered]
    · have sum_coordinates : (∑ axis, vector axis) = 24 * parity + 2 * ∑ axis, half axis := by
        simp_rw [coordinates]
        simp [Finset.sum_add_distrib, Finset.mul_sum]
      rcases allowed with rfl | rfl <;> rw [sum_coordinates, total] <;> omega
  · rintro ⟨parity, allowed, coordinates, codeword, total⟩
    let half : Coordinates := fun axis => (vector axis - parity) / 2
    have recovery : ∀ axis, vector axis = parity + 2 * half axis := by
      intro axis
      have := coordinates axis
      dsimp [half]
      rcases allowed with rfl | rfl <;> omega
    have sum_coordinates : (∑ axis, vector axis) = 24 * parity + 2 * ∑ axis, half axis := by
      simp_rw [recovery]
      simp [Finset.sum_add_distrib, Finset.mul_sum]
    refine ⟨parity, half, (∑ axis, half axis - 2 * parity) / 4, allowed, recovery,
      codeword, ?_⟩
    rcases allowed with rfl | rfl <;> rw [sum_coordinates] at total <;> omega

theorem member_zero : member 0 := by
  refine ⟨0, 0, 0, Or.inl rfl, ?_, ?_, ?_⟩
  · intro axis; rfl
  · exact code.zero_mem
  · simp

theorem member_add (left right : Coordinates) (left_member : member left)
    (right_member : member right) : member (left + right) := by
  obtain ⟨parity, half, quotient, allowed, coordinates, codeword, total⟩ := left_member
  obtain ⟨other, other_half, other_quotient, other_allowed, other_coordinates,
    other_codeword, other_total⟩ := right_member
  have reduced_add : reduction (half + other_half) = reduction half + reduction other_half := by
    ext axis
    simp [reduction]
  have sum_add : (∑ axis, (half + other_half) axis) =
      (∑ axis, half axis) + ∑ axis, other_half axis := by
    simp [Finset.sum_add_distrib]
  rcases allowed with rfl | rfl <;> rcases other_allowed with rfl | rfl
  · refine ⟨0, half + other_half, quotient + other_quotient, Or.inl rfl, ?_, ?_, ?_⟩
    · intro axis; simp only [Pi.add_apply, coordinates, other_coordinates]; ring
    · rw [reduced_add]; exact code.add_mem codeword other_codeword
    · rw [sum_add, total, other_total]; ring
  · refine ⟨1, half + other_half, quotient + other_quotient, Or.inr rfl, ?_, ?_, ?_⟩
    · intro axis; simp only [Pi.add_apply, coordinates, other_coordinates]; ring
    · rw [reduced_add]; exact code.add_mem codeword other_codeword
    · rw [sum_add, total, other_total]; ring
  · refine ⟨1, half + other_half, quotient + other_quotient, Or.inr rfl, ?_, ?_, ?_⟩
    · intro axis; simp only [Pi.add_apply, coordinates, other_coordinates]; ring
    · rw [reduced_add]; exact code.add_mem codeword other_codeword
    · rw [sum_add, total, other_total]; ring
  · refine ⟨0, fun axis => half axis + other_half axis + 1,
      quotient + other_quotient + 7, Or.inl rfl, ?_, ?_, ?_⟩
    · intro axis; simp only [Pi.add_apply, coordinates, other_coordinates]; ring
    · have reduced : reduction (fun axis => half axis + other_half axis + 1) =
          reduction half + reduction other_half + (fun _ => 1) := by
        ext axis; simp [reduction]
      rw [reduced]
      exact code.add_mem (code.add_mem codeword other_codeword) code_contains_all_ones
    · simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, total, other_total]
      ring

theorem member_neg (vector : Coordinates) (is_member : member vector) : member (-vector) := by
  obtain ⟨parity, half, quotient, allowed, coordinates, codeword, total⟩ := is_member
  rcases allowed with rfl | rfl
  · refine ⟨0, -half, -quotient, Or.inl rfl, ?_, ?_, ?_⟩
    · intro axis; simp only [Pi.neg_apply, coordinates]; ring
    · have reduced : reduction (-half) = -reduction half := by
        ext axis; simp [reduction]
      rw [reduced]; exact code.neg_mem codeword
    · simp [Finset.sum_neg_distrib, total]
  · refine ⟨1, fun axis => -half axis - 1, -quotient - 7, Or.inr rfl, ?_, ?_, ?_⟩
    · intro axis; simp only [Pi.neg_apply, coordinates]; ring
    · have reduced : reduction (fun axis => -half axis - 1) =
          -reduction half - (fun _ => 1) := by
        ext axis; simp [reduction]
      rw [reduced]; exact code.sub_mem (code.neg_mem codeword) code_contains_all_ones
    · simp [Finset.sum_sub_distrib, Finset.sum_neg_distrib, total]
      ring

def additiveLattice : AddSubgroup Coordinates where
  carrier := {vector | member vector}
  zero_mem' := member_zero
  add_mem' := member_add _ _
  neg_mem' := member_neg _

def lattice : Submodule ℤ Coordinates := additiveLattice.toIntSubmodule

def squareSum (vector : Coordinates) : ℤ := ∑ axis, vector axis ^ 2

theorem integer_square_mod_four (value : ℤ) : value ^ 2 % 4 = value % 2 := by
  have remainder_nonnegative := Int.emod_nonneg value (by norm_num : (4 : ℤ) ≠ 0)
  have remainder_lt := Int.emod_lt_of_pos value (by norm_num : (0 : ℤ) < 4)
  have mod_two : value % 2 = value % 4 % 2 := by omega
  have mod_square : value ^ 2 % 4 = (value % 4) ^ 2 % 4 := by
    simp [pow_two, Int.mul_emod]
  rw [mod_square, mod_two]
  interval_cases remainder : value % 4 <;> norm_num

theorem squareSum_mod_four (vector : Coordinates) :
    squareSum vector % 4 = (weight (reduction vector) : ℤ) % 4 := by
  have residues : ∀ axis, vector axis ^ 2 % 4 = ((reduction vector axis).val : ℤ) % 4 := by
    intro axis
    rw [integer_square_mod_four, reduction, ZMod.val_intCast]
    omega
  simp only [squareSum, weight, Nat.cast_sum]
  calc
    (∑ axis, vector axis ^ 2) % 4 = (∑ axis, vector axis ^ 2 % 4) % 4 :=
      Finset.sum_int_mod _ _ _
    _ = (∑ axis, ((reduction vector axis).val : ℤ) % 4) % 4 := by simp_rw [residues]
    _ = (∑ axis, ((reduction vector axis).val : ℤ)) % 4 :=
      (Finset.sum_int_mod _ _ _).symm

theorem member_even_squareSum (vector : Coordinates) (is_member : member vector) :
    16 ∣ squareSum vector := by
  obtain ⟨parity, half, quotient, allowed, coordinates, codeword, total⟩ := is_member
  have weight_divisible : (weight (reduction half) : ℤ) % 4 = 0 := by
    exact_mod_cast code_doubly_even _ codeword
  have square_divisible : squareSum half % 4 = 0 := by
    rw [squareSum_mod_four, weight_divisible]
  have half_total : squareSum half = 4 * (squareSum half / 4) := by omega
  have expansion : squareSum vector = 24 * parity ^ 2 +
      4 * parity * (∑ axis, half axis) + 4 * squareSum half := by
    simp only [squareSum]
    simp_rw [coordinates, show ∀ axis, (parity + 2 * half axis) ^ 2 =
      parity ^ 2 + 4 * parity * half axis + 4 * half axis ^ 2 by intro axis; ring]
    simp [Finset.sum_add_distrib, Finset.mul_sum]
  rcases allowed with rfl | rfl
  · refine ⟨squareSum half / 4, ?_⟩
    nlinarith [expansion, half_total]
  · refine ⟨2 + quotient + squareSum half / 4, ?_⟩
    nlinarith [expansion, half_total, total]

theorem member_integral_pairing (left right : Coordinates)
    (left_member : member left) (right_member : member right) :
    8 ∣ ∑ axis, left axis * right axis := by
  obtain ⟨left_quotient, left_norm⟩ := member_even_squareSum left left_member
  obtain ⟨right_quotient, right_norm⟩ := member_even_squareSum right right_member
  obtain ⟨sum_quotient, sum_norm⟩ := member_even_squareSum (left + right)
    (member_add left right left_member right_member)
  have expansion : squareSum (left + right) = squareSum left + squareSum right +
      2 * ∑ axis, left axis * right axis := by
    simp only [squareSum, Pi.add_apply]
    simp_rw [show ∀ axis, (left axis + right axis) ^ 2 =
      left axis ^ 2 + right axis ^ 2 + 2 * (left axis * right axis) by intro axis; ring]
    simp [Finset.sum_add_distrib, Finset.mul_sum]
  refine ⟨sum_quotient - left_quotient - right_quotient, ?_⟩
  omega

theorem squareSum_positive (vector : Coordinates) (nonzero : vector ≠ 0) :
    0 < squareSum vector := by
  have exists_axis : ∃ axis, vector axis ≠ 0 := by
    by_contra failure
    apply nonzero
    ext axis
    simpa using not_exists.mp failure axis
  obtain ⟨axis, coordinate_nonzero⟩ := exists_axis
  exact Finset.sum_pos' (fun _ _ => sq_nonneg _) ⟨axis, Finset.mem_univ _,
    sq_pos_of_ne_zero coordinate_nonzero⟩

theorem integer_square_mod_two (value : ℤ) : value ^ 2 % 2 = value % 2 := by
  have := integer_square_mod_four value
  have two_mod : value ^ 2 % 2 = value ^ 2 % 4 % 2 := by omega
  rw [two_mod, this]
  omega

theorem squareSum_mod_two (vector : Coordinates) :
    squareSum vector % 2 = (∑ axis, vector axis) % 2 := by
  simp only [squareSum]
  calc
    (∑ axis, vector axis ^ 2) % 2 = (∑ axis, vector axis ^ 2 % 2) % 2 :=
      Finset.sum_int_mod _ _ _
    _ = (∑ axis, vector axis % 2) % 2 := by simp_rw [integer_square_mod_two]
    _ = (∑ axis, vector axis) % 2 := (Finset.sum_int_mod _ _ _).symm

theorem residue_le_square (value : ℤ) : ((value : Binary).val : ℤ) ≤ value ^ 2 := by
  rw [ZMod.val_intCast]
  norm_num only [Nat.cast_ofNat]
  have lower := Int.emod_nonneg value (by norm_num : (2 : ℤ) ≠ 0)
  have upper := Int.emod_lt_of_pos value (by norm_num : (0 : ℤ) < 2)
  rcases (show value = 0 ∨ value ≤ -1 ∨ 1 ≤ value by omega) with rfl | negative | positive
  · norm_num
  · nlinarith [sq_nonneg (value + 1)]
  · nlinarith [sq_nonneg (value - 1)]

theorem member_minimum_squareSum (vector : Coordinates) (is_member : member vector)
    (nonzero : vector ≠ 0) : 32 ≤ squareSum vector := by
  have divisible := member_even_squareSum vector is_member
  obtain ⟨parity, half, quotient, allowed, coordinates, codeword, total⟩ := is_member
  rcases allowed with rfl | rfl
  · by_cases code_nonzero : reduction half ≠ 0
    · have lower_weight := code_minimum_weight (reduction half) codeword code_nonzero
      have lower_half : (weight (reduction half) : ℤ) ≤ squareSum half := by
        simp only [weight, squareSum, Nat.cast_sum]
        exact Finset.sum_le_sum (fun axis _ => residue_le_square (half axis))
      have scaled : squareSum vector = 4 * squareSum half := by
        simp only [squareSum]
        simp_rw [coordinates]
        simp [mul_pow, Finset.mul_sum]
      rw [scaled]
      have : (8 : ℤ) ≤ (weight (reduction half) : ℤ) := by exact_mod_cast lower_weight
      omega
    · have reduced_zero : reduction half = 0 := not_ne_iff.mp code_nonzero
      let quarter : Coordinates := fun axis => half axis / 2
      have half_even : ∀ axis, half axis = 2 * quarter axis := by
        intro axis
        have reduced_axis := congrFun reduced_zero axis
        have reduced_value := congrArg ZMod.val reduced_axis
        have residue : half axis % 2 = 0 := by
          simpa only [reduction, ZMod.val_intCast, Pi.zero_apply, ZMod.val_zero,
            Nat.cast_zero, Nat.cast_ofNat] using
            congrArg (fun value : ℕ => (value : ℤ)) reduced_value
        dsimp [quarter]
        omega
      have quarter_nonzero : quarter ≠ 0 := by
        intro zero
        apply nonzero
        ext axis
        rw [coordinates, half_even]
        simp [zero]
      have quarter_total : (∑ axis, quarter axis) = 2 * quotient := by
        have : (∑ axis, half axis) = 2 * ∑ axis, quarter axis := by
          simp_rw [half_even]
          rw [Finset.mul_sum]
        omega
      have even_norm : squareSum quarter % 2 = 0 := by
        rw [squareSum_mod_two, quarter_total]
        omega
      have positive_norm := squareSum_positive quarter quarter_nonzero
      have scaled : squareSum vector = 16 * squareSum quarter := by
        simp only [squareSum]
        simp_rw [coordinates, half_even]
        simp [mul_pow, Finset.mul_sum, ← mul_assoc]
      rw [scaled]
      omega
  · have odd_coordinate_square : ∀ axis, 1 ≤ vector axis ^ 2 := by
      intro axis
      have := coordinates axis
      rcases (show vector axis ≤ -1 ∨ 1 ≤ vector axis by omega) with negative | positive
      · nlinarith
      · nlinarith
    have lower : 24 ≤ squareSum vector := by
      calc
        24 = ∑ _axis : Fin 24, (1 : ℤ) := by simp
        _ ≤ squareSum vector := Finset.sum_le_sum (fun axis _ => odd_coordinate_square axis)
    obtain ⟨quotient_norm, equation⟩ := divisible
    omega

end D5.S3.VertexAlgebra.GolayLeech.ExplicitLeechCongruence
