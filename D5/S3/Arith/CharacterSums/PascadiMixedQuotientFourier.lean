/- GID: D5/S3/Arith/CharacterSums/PascadiMixedQuotientFourier
   generality: G
   mirror-B: D5/B/S3/Arith/CharacterSums/PascadiMixedQuotientFourier
   mirror-E: none(waiver:open-original-total-count)
   anchors: []
   utility: none
   digest: The mixed-quotient inverse graph has a sparse stationary Fourier sum. -/

module

public import Mathlib.Analysis.Fourier.ZMod
public import Mathlib.Data.ZMod.Units
public import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Logic.Equiv.Fin.Basic

/-! Complete Fourier coefficients of the mixed-quotient inverse graph. -/

@[expose] public section

open scoped BigOperators

namespace D5.S3.Arith.CharacterSums.MixedQuotient

noncomputable section

variable {p : ℕ}

/-- Reduction from the first coordinate of the mixed quotient to the residue field. -/
def reduce : ZMod (p ^ 2) →+* ZMod p :=
  ZMod.castHom (dvd_pow_self p (by decide : 2 ≠ 0)) (ZMod p)

/-- The representative in the square modulus obtained from the least nonnegative digit. -/
def canonicalLift (a : ZMod p) : ZMod (p ^ 2) := a.val

variable [Fact p.Prime]

private instance squareNeZero : NeZero (p ^ 2) :=
  ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩

/-- The complete coefficient on the graph of
`(x,s) ↦ (C*x⁻¹, s*reduce(C*x⁻²))` in the mixed quotient. -/
def coefficient (C : (ZMod (p ^ 2))ˣ) (A B : ZMod (p ^ 2)) (D E : ZMod p) : ℂ :=
  ∑ x : (ZMod (p ^ 2))ˣ, ∑ s : ZMod p,
    ZMod.stdAddChar (A * (x : ZMod (p ^ 2)) +
      B * (C : ZMod (p ^ 2)) * (x⁻¹ : (ZMod (p ^ 2))ˣ).val) *
      ZMod.stdAddChar (s * (D + E * reduce ((C : ZMod (p ^ 2)) *
        ((x⁻¹ : (ZMod (p ^ 2))ˣ) : ZMod (p ^ 2)) ^ 2)))

/-- The two residue equations selected by orthogonality in the slope and lift digits. -/
def stationaryResidues (C : (ZMod (p ^ 2))ˣ) (A B : ZMod (p ^ 2)) (D E : ZMod p) :
    Finset ((ZMod p)ˣ) :=
  Finset.univ.filter fun a =>
    reduce A * (a : ZMod p) ^ 2 = reduce (C : ZMod (p ^ 2)) * reduce B ∧
      D * (a : ZMod p) ^ 2 = -reduce (C : ZMod (p ^ 2)) * E

private theorem isUnit_iff_reduce_ne_zero (x : ZMod (p ^ 2)) :
    IsUnit x ↔ reduce x ≠ 0 := by
  obtain ⟨n, rfl⟩ := ZMod.natCast_zmod_surjective x
  rw [map_natCast, ZMod.isUnit_natCast_iff_not_dvd_pow Fact.out (by decide : 0 < 2),
    ne_eq, ZMod.natCast_eq_zero_iff]

private def digitValue (a : (ZMod p)ˣ) (j : ZMod p) : ZMod (p ^ 2) :=
  canonicalLift (a : ZMod p) + (p : ZMod (p ^ 2)) * canonicalLift j

private theorem reduce_digitValue (a : (ZMod p)ˣ) (j : ZMod p) :
    reduce (digitValue a j) = (a : ZMod p) := by
  simp [digitValue, canonicalLift]

private def digitUnit (a : (ZMod p)ˣ) (j : ZMod p) : (ZMod (p ^ 2))ˣ :=
  ((isUnit_iff_reduce_ne_zero _).2 ((reduce_digitValue a j).trans_ne a.ne_zero)).unit

private theorem coe_digitUnit (a : (ZMod p)ˣ) (j : ZMod p) :
    (digitUnit a j : ZMod (p ^ 2)) = digitValue a j :=
  IsUnit.unit_spec _

private theorem reduce_digitUnit (a : (ZMod p)ˣ) (j : ZMod p) :
    reduce (digitUnit a j : ZMod (p ^ 2)) = (a : ZMod p) := by
  rw [coe_digitUnit, reduce_digitValue]

private theorem val_digitUnit (a : (ZMod p)ˣ) (j : ZMod p) :
    (digitUnit a j : ZMod (p ^ 2)).val = (a : ZMod p).val + p * j.val := by
  rw [coe_digitUnit, digitValue, canonicalLift, canonicalLift, ← Nat.cast_mul, ← Nat.cast_add]
  apply ZMod.val_natCast_of_lt
  let hi : Fin p := ⟨j.val, j.val_lt⟩
  let lo : Fin p := ⟨(a : ZMod p).val, ZMod.val_lt _⟩
  have hb := (finProdFinEquiv (hi, lo)).isLt
  change (a : ZMod p).val + p * j.val < p * p at hb
  simpa only [pow_two] using hb

private theorem digitUnit_bijective :
    Function.Bijective (fun aj : (ZMod p)ˣ × ZMod p => digitUnit aj.1 aj.2) := by
  refine ⟨?_, ?_⟩
  · rintro ⟨a, i⟩ ⟨b, j⟩ h
    have hval := congrArg (fun x : (ZMod (p ^ 2))ˣ => (x : ZMod (p ^ 2)).val) h
    simp only [val_digitUnit] at hval
    have hd : ((a : ZMod p), i.val) = ((b : ZMod p), j.val) :=
      (Nat.residueClassesEquiv p).symm.injective hval
    exact Prod.ext (Units.ext (congrArg Prod.fst hd))
      (ZMod.val_injective p (congrArg Prod.snd hd))
  · intro x
    let a := ZMod.unitsMap (dvd_pow_self p (by decide : 2 ≠ 0)) x
    let j : ZMod p := (((x : ZMod (p ^ 2)).val / p : ℕ) : ZMod p)
    have ha : (a : ZMod p).val = (x : ZMod (p ^ 2)).val % p := by
      change (reduce (x : ZMod (p ^ 2))).val = _
      conv_lhs => rw [← ZMod.natCast_zmod_val (x : ZMod (p ^ 2)),
        map_natCast, ZMod.val_natCast]
    have hj : (x : ZMod (p ^ 2)).val / p < p :=
      (Nat.div_lt_iff_lt_mul (Fact.out : p.Prime).pos).2
        (by simpa only [pow_two] using ZMod.val_lt (x : ZMod (p ^ 2)))
    refine ⟨(a, j), Units.ext (ZMod.val_injective _ ?_)⟩
    change (digitUnit a j : ZMod (p ^ 2)).val = (x : ZMod (p ^ 2)).val
    rw [val_digitUnit, ha, ZMod.val_natCast_of_lt hj, Nat.mod_add_div]

private theorem reduce_inv (x : (ZMod (p ^ 2))ˣ) :
    reduce ((x⁻¹ : (ZMod (p ^ 2))ˣ) : ZMod (p ^ 2)) =
      (reduce (x : ZMod (p ^ 2)))⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← map_mul, Units.inv_mul, map_one]

private theorem inverse_add_digit (a : (ZMod p)ˣ) (j : ZMod p) :
    ((digitUnit a j)⁻¹ : (ZMod (p ^ 2))ˣ).val =
      (canonicalLift (a : ZMod p))⁻¹ -
        ((p : ZMod (p ^ 2)) * canonicalLift j) * (canonicalLift (a : ZMod p))⁻¹ ^ 2 := by
  rw [← ZMod.inv_coe_unit]
  let u := canonicalLift (a : ZMod p)
  let t := (p : ZMod (p ^ 2)) * canonicalLift j
  have hunit : IsUnit u := (isUnit_iff_reduce_ne_zero _).2 (by
    simp [u, canonicalLift])
  have hu : u * u⁻¹ = 1 := ZMod.mul_inv_of_unit _ hunit
  have ht : t ^ 2 = 0 := by
    rw [mul_pow]
    norm_cast
    simp
  rw [coe_digitUnit]
  change (u + t)⁻¹ = _
  apply ZMod.inv_eq_of_mul_eq_one
  calc
    (u + t) * (u⁻¹ - t * u⁻¹ ^ 2) =
        u * u⁻¹ + t * u⁻¹ * (1 - u * u⁻¹) - t ^ 2 * u⁻¹ ^ 2 := by ring
    _ = 1 := by rw [hu, ht]; simp

private theorem stdAddChar_on_digit (z : ZMod (p ^ 2)) :
    ZMod.stdAddChar ((p : ZMod (p ^ 2)) * z) = ZMod.stdAddChar (reduce z) := by
  obtain ⟨n, rfl⟩ := ZMod.natCast_zmod_surjective z
  rw [map_natCast, ← Nat.cast_mul, ZMod.stdAddChar_apply, ZMod.stdAddChar_apply,
    ZMod.toCircle_natCast, ZMod.toCircle_natCast]
  have hp : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  congr 1
  push_cast
  field_simp

private theorem sum_stdAddChar_mul (b : ZMod p) :
    ∑ j : ZMod p, ZMod.stdAddChar (j * b) = if b = 0 then (p : ℂ) else 0 := by
  split_ifs with h
  · simp [h, ZMod.card]
  · simpa only [AddChar.mulShift_apply, mul_comm b] using
      (AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar p h))

private theorem phase_add_digit (C : (ZMod (p ^ 2))ˣ) (A B : ZMod (p ^ 2))
    (a : (ZMod p)ˣ) (j : ZMod p) :
    ZMod.stdAddChar (A * (digitUnit a j : ZMod (p ^ 2)) +
      B * (C : ZMod (p ^ 2)) * ((digitUnit a j)⁻¹ : (ZMod (p ^ 2))ˣ).val) =
    ZMod.stdAddChar (A * canonicalLift (a : ZMod p) +
      B * (C : ZMod (p ^ 2)) * (canonicalLift (a : ZMod p))⁻¹) *
    ZMod.stdAddChar (j * (reduce A - reduce B * reduce (C : ZMod (p ^ 2)) *
      ((a : ZMod p)⁻¹) ^ 2)) := by
  let u := canonicalLift (a : ZMod p)
  have hu : reduce u = (a : ZMod p) := by simp [u, canonicalLift]
  have huinv : reduce u⁻¹ = (a : ZMod p)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [← hu, ← map_mul, ZMod.inv_mul_of_unit _ ((isUnit_iff_reduce_ne_zero _).2
      (hu.trans_ne a.ne_zero)), map_one]
  rw [inverse_add_digit, coe_digitUnit]
  calc
    _ = ZMod.stdAddChar ((A * u + B * (C : ZMod (p ^ 2)) * u⁻¹) + (p : ZMod (p ^ 2)) *
          (canonicalLift j * (A - B * (C : ZMod (p ^ 2)) * u⁻¹ ^ 2))) := by
      congr 1
      simp only [digitValue, u]
      ring
    _ = _ := by
      have hd : reduce (canonicalLift j * (A - B * (C : ZMod (p ^ 2)) * u⁻¹ ^ 2)) =
          j * (reduce A - reduce B * reduce (C : ZMod (p ^ 2)) * ((a : ZMod p)⁻¹) ^ 2) := by
        simp only [map_mul, map_sub, map_pow, huinv, canonicalLift, map_natCast,
          ZMod.natCast_zmod_val]
      rw [ZMod.stdAddChar.map_add_eq_mul, stdAddChar_on_digit, hd]

private theorem phase_conditions (C : (ZMod (p ^ 2))ˣ) (A B : ZMod (p ^ 2))
    (D E : ZMod p) (a : (ZMod p)ˣ) :
    ((reduce A - reduce B * reduce (C : ZMod (p ^ 2)) * ((a : ZMod p)⁻¹) ^ 2 = 0) ∧
      D + E * (reduce (C : ZMod (p ^ 2)) * ((a : ZMod p)⁻¹) ^ 2) = 0) ↔
    a ∈ stationaryResidues C A B D E := by
  have ha : (a : ZMod p) ^ 2 ≠ 0 := pow_ne_zero _ a.ne_zero
  have cancel (u v : ZMod p) :
      u - v * ((a : ZMod p)⁻¹) ^ 2 = 0 ↔ u * (a : ZMod p) ^ 2 = v := by
    rw [sub_eq_zero, inv_pow, ← div_eq_mul_inv, eq_div_iff ha]
  simp only [stationaryResidues, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [cancel, mul_comm (reduce B)]
  have h :
      D + E * (reduce (C : ZMod (p ^ 2)) * ((a : ZMod p)⁻¹) ^ 2) =
        D - (-reduce (C : ZMod (p ^ 2)) * E) * ((a : ZMod p)⁻¹) ^ 2 := by ring
  rw [h, cancel]

/-- Both digit completions leave a factor of `p` and impose the two residue equations.
The remaining phase is evaluated at the canonical representative modulo `p²`. -/
theorem coefficient_eq_stationary_sum
    (C : (ZMod (p ^ 2))ˣ) (A B : ZMod (p ^ 2)) (D E : ZMod p) :
    (coefficient C A B D E = (p : ℂ) ^ 2 *
      ∑ a ∈ stationaryResidues C A B D E,
        ZMod.stdAddChar (A * canonicalLift (a : ZMod p) +
          B * (C : ZMod (p ^ 2)) * (canonicalLift (a : ZMod p))⁻¹)) ∧
    (stationaryResidues C A B D E).card ≤ p - 1 := by
  refine ⟨?_, (Finset.card_le_univ _).trans_eq (ZMod.card_units p)⟩
  unfold coefficient
  rw [← (Equiv.ofBijective _ digitUnit_bijective).sum_comp, Fintype.sum_prod_type]
  rw [Finset.mul_sum]
  conv_rhs =>
    unfold stationaryResidues
    rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a _
  have hmem : a ∈ stationaryResidues C A B D E ↔
      reduce A * (a : ZMod p) ^ 2 = reduce (C : ZMod (p ^ 2)) * reduce B ∧
      D * (a : ZMod p) ^ 2 = -reduce (C : ZMod (p ^ 2)) * E := by
    simp only [stationaryResidues, Finset.mem_filter, Finset.mem_univ, true_and]
  simp only [← hmem]
  simp only [Equiv.ofBijective_apply, ← Finset.mul_sum, sum_stdAddChar_mul, map_mul, map_pow,
    reduce_inv, reduce_digitUnit, phase_add_digit]
  rw [← Finset.sum_mul, ← Finset.mul_sum, sum_stdAddChar_mul]
  by_cases h₁ : reduce A - reduce B * reduce (C : ZMod (p ^ 2)) * ((a : ZMod p)⁻¹) ^ 2 = 0
  · by_cases h₂ : D + E * (reduce (C : ZMod (p ^ 2)) * ((a : ZMod p)⁻¹) ^ 2) = 0
    · rw [ite_eq_left ((phase_conditions C A B D E a).1 ⟨h₁, h₂⟩)]
      simp only [ite_eq_left h₁, ite_eq_left h₂]
      ring
    · simp only [ite_eq_right (fun ha => h₂ ((phase_conditions C A B D E a).2 ha).2),
        ite_eq_right h₂, mul_zero]
  · simp only [ite_eq_right (fun ha => h₁ ((phase_conditions C A B D E a).2 ha).1),
      ite_eq_right h₁, mul_zero, zero_mul]

/-- The coefficient vanishes when exactly one first-coordinate frequency is a unit. -/
theorem coefficient_eq_zero_of_mixed
    (C : (ZMod (p ^ 2))ˣ) (A B : ZMod (p ^ 2)) (D E : ZMod p)
    (hmixed : ¬ (IsUnit A ↔ IsUnit B)) :
    coefficient C A B D E = 0 := by
  have hC : reduce (C : ZMod (p ^ 2)) ≠ 0 :=
    (isUnit_iff_reduce_ne_zero _).1 C.isUnit
  have hempty : stationaryResidues C A B D E = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro a ha
    have heq := (Finset.mem_filter.mp ha).2.1
    have hz : reduce A = 0 ↔ reduce B = 0 := by
      simpa [mul_eq_zero, pow_ne_zero 2 a.ne_zero, hC] using
        congrArg (fun t : ZMod p => t = 0) heq
    apply hmixed
    simp only [isUnit_iff_reduce_ne_zero, ne_eq, hz]
  simp [(coefficient_eq_stationary_sum C A B D E).1, hempty]

/-- In the unit sector there are at most two phases, and any nonzero coefficient
lies on the support relation between the two frequency slopes. -/
theorem coefficient_unit_sector
    (C : (ZMod (p ^ 2))ˣ) (A B : ZMod (p ^ 2)) (D E : ZMod p)
    (hA : reduce A ≠ 0) (hB : reduce B ≠ 0) :
    ‖coefficient C A B D E‖ ≤ 2 * (p : ℝ) ^ 2 ∧
      (coefficient C A B D E ≠ 0 → D / reduce A = -E / reduce B) := by
  classical
  have hsum := (coefficient_eq_stationary_sum C A B D E).1
  by_cases h : (stationaryResidues C A B D E).Nonempty
  · obtain ⟨a, ha⟩ := h
    have haEq := (Finset.mem_filter.mp ha).2
    have hcard : (stationaryResidues C A B D E).card ≤ 2 := by
      refine (Finset.card_le_card (t := {a, -a}) ?_).trans Finset.card_le_two
      intro b hb
      have hbEq := (Finset.mem_filter.mp hb).2.1
      have hsquare : (b : ZMod p) ^ 2 = (a : ZMod p) ^ 2 :=
        mul_left_cancel₀ hA (hbEq.trans haEq.1.symm)
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsquare with heq | heq
      · have he : b = a := Units.ext heq
        simp [he]
      · have he : b = -a := Units.ext (by simpa using heq)
        simp [he]
    constructor
    · rw [hsum, norm_mul, norm_pow, Complex.norm_natCast]
      calc
        _ ≤ (p : ℝ) ^ 2 *
            ∑ b ∈ stationaryResidues C A B D E,
              ‖ZMod.stdAddChar (A * canonicalLift (b : ZMod p) +
                B * (C : ZMod (p ^ 2)) * (canonicalLift (b : ZMod p))⁻¹)‖ :=
          mul_le_mul_of_nonneg_left (norm_sum_le _ _) (sq_nonneg _)
        _ ≤ 2 * (p : ℝ) ^ 2 := by
          rw [mul_comm (2 : ℝ)]
          simp only [ZMod.stdAddChar_apply, Circle.norm_coe, Finset.sum_const, nsmul_eq_mul,
            mul_one]
          exact mul_le_mul_of_nonneg_left (by exact_mod_cast hcard) (sq_nonneg _)
    · intro _
      apply (div_eq_div_iff hA hB).2
      apply mul_right_cancel₀ (pow_ne_zero 2 a.ne_zero)
      calc
        (D * reduce B) * (a : ZMod p) ^ 2 =
            (D * (a : ZMod p) ^ 2) * reduce B := by ring
        _ = (-E) * (reduce (C : ZMod (p ^ 2)) * reduce B) := by rw [haEq.2]; ring
        _ = ((-E) * reduce A) * (a : ZMod p) ^ 2 := by rw [← haEq.1]; ring
  · have hempty := Finset.not_nonempty_iff_eq_empty.mp h
    simp [hsum, hempty, mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (sq_nonneg (p : ℝ))]

#print axioms coefficient_eq_stationary_sum
#print axioms coefficient_eq_zero_of_mixed
#print axioms coefficient_unit_sector

end

end D5.S3.Arith.CharacterSums.MixedQuotient
