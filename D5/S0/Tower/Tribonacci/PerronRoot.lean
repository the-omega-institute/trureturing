/- GID: D5/S0/Tower/Tribonacci/PerronRoot
   generality: I
   mirror-B: D5/B/S0/Tower/Tribonacci/PerronRoot
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Tribonacci name-count ratios converge to the unique real Perron root. -/

import D5.S0.Tower.Tribonacci.Values

namespace D5.S0.Tower.Tribonacci.PerronRoot

open D5.S0.Tower.Tribonacci.Names
open D5.S0.Tower.Tribonacci.Values
open Filter

local notation "t" => tribonacciConstant

/-- Any real Tribonacci root above one is the chosen Tribonacci constant. -/
theorem eq_tribonacciConstant_of_one_lt {x : Real} (hx : 1 < x)
    (hx_cubic : x ^ 3 = x ^ 2 + x + 1) : x = t := by
  have hfactor :
      (x - t) * (x ^ 2 + x * t + t ^ 2 - x - t - 1) = 0 := by
    calc
      (x - t) * (x ^ 2 + x * t + t ^ 2 - x - t - 1) =
          (x ^ 3 - x ^ 2 - x - 1) - (t ^ 3 - t ^ 2 - t - 1) := by ring
      _ = 0 := by rw [hx_cubic, tribonacciConstant_cubic]; ring
  have hx_pos : 0 < x := lt_trans (by norm_num) hx
  have hxx : 0 < x * (x - 1) := mul_pos hx_pos (sub_pos.mpr hx)
  have htt : 0 < t * (t - 1) :=
    mul_pos tribonacciConstant_pos (sub_pos.mpr one_lt_tribonacciConstant)
  have hxt : 0 < x * t - 1 := by
    nlinarith [mul_pos (sub_pos.mpr hx)
      (sub_pos.mpr one_lt_tribonacciConstant)]
  have hpositive : 0 < x ^ 2 + x * t + t ^ 2 - x - t - 1 := by
    nlinarith [hxx, htt, hxt]
  exact sub_eq_zero.mp ((mul_eq_zero.mp hfactor).resolve_right hpositive.ne')

/-- Exact characterization of the chosen root by its interval and cubic equation. -/
theorem eq_tribonacciConstant_iff {x : Real} :
    x = t ↔ 1 < x ∧ x < 2 ∧ x ^ 3 = x ^ 2 + x + 1 := by
  constructor
  · rintro rfl
    exact ⟨one_lt_tribonacciConstant, tribonacciConstant_lt_two,
      tribonacciConstant_cubic⟩
  · rintro ⟨hx, _, hx_cubic⟩
    exact eq_tribonacciConstant_of_one_lt hx hx_cubic

/-- The discrepancy between one Tribonacci step and multiplication by the Perron root. -/
noncomputable def tribonacciError (n : Nat) : Real :=
  (tribonacci (n + 1) : Real) - t * tribonacci n

/-- After removing the Perron factor, the error obeys the residual quadratic recurrence. -/
theorem tribonacci_error_add_two (n : Nat) :
    tribonacciError (n + 2) =
      -(t - 1) * tribonacciError (n + 1) - t⁻¹ * tribonacciError n := by
  have hrec : (tribonacci (n + 3) : Real) =
      tribonacci (n + 2) + tribonacci (n + 1) + tribonacci n := by
    exact_mod_cast tribonacci_add_three n
  simp only [tribonacciError, Nat.add_assoc, Nat.reduceAdd]
  rw [hrec]
  field_simp [tribonacciConstant_ne_zero]
  nlinarith [tribonacciConstant_cubic]

/-- A positive quadratic energy for the residual two-step recurrence. -/
noncomputable def tribonacciErrorEnergy (n : Nat) : Real :=
  tribonacciError (n + 1) ^ 2 +
    (t - 1) * tribonacciError (n + 1) * tribonacciError n +
      t⁻¹ * tribonacciError n ^ 2

/-- The residual energy contracts exactly by `t⁻¹` at every step. -/
theorem tribonacci_errorEnergy_succ (n : Nat) :
    tribonacciErrorEnergy (n + 1) = t⁻¹ * tribonacciErrorEnergy n := by
  rw [tribonacciErrorEnergy, tribonacciErrorEnergy, tribonacci_error_add_two]
  ring

theorem tribonacci_errorEnergy_discriminant_pos :
    0 < 4 * t⁻¹ - (t - 1) ^ 2 := by
  have hidentity :
      t * (4 * t⁻¹ - (t - 1) ^ 2) = (t - 1) ^ 2 + 2 := by
    field_simp [tribonacciConstant_ne_zero]
    nlinarith [tribonacciConstant_cubic]
  have hproduct : 0 < t * (4 * t⁻¹ - (t - 1) ^ 2) := by
    rw [hidentity]
    positivity
  rcases (mul_pos_iff.mp hproduct) with hpositive | hnegative
  · exact hpositive.2
  · exact False.elim (not_lt_of_ge tribonacciConstant_pos.le hnegative.1)

theorem tribonacci_errorEnergy_nonneg (n : Nat) :
    0 ≤ tribonacciErrorEnergy n := by
  have hidentity :
      4 * tribonacciErrorEnergy n =
        (2 * tribonacciError (n + 1) + (t - 1) * tribonacciError n) ^ 2 +
          (4 * t⁻¹ - (t - 1) ^ 2) * tribonacciError n ^ 2 := by
    rw [tribonacciErrorEnergy]
    ring
  have hright : 0 ≤
      (2 * tribonacciError (n + 1) + (t - 1) * tribonacciError n) ^ 2 +
        (4 * t⁻¹ - (t - 1) ^ 2) * tribonacciError n ^ 2 := by
    exact add_nonneg (sq_nonneg _)
      (mul_nonneg tribonacci_errorEnergy_discriminant_pos.le (sq_nonneg _))
  nlinarith

theorem tribonacci_error_sq_le_energy (n : Nat) :
    tribonacciError n ^ 2 ≤
      (4 / (4 * t⁻¹ - (t - 1) ^ 2)) * tribonacciErrorEnergy n := by
  let d : Real := 4 * t⁻¹ - (t - 1) ^ 2
  have hd : 0 < d := tribonacci_errorEnergy_discriminant_pos
  have hidentity :
      4 * tribonacciErrorEnergy n =
        (2 * tribonacciError (n + 1) + (t - 1) * tribonacciError n) ^ 2 +
          d * tribonacciError n ^ 2 := by
    dsimp [d]
    rw [tribonacciErrorEnergy]
    ring
  have hle : d * tribonacciError n ^ 2 ≤ 4 * tribonacciErrorEnergy n := by
    rw [hidentity]
    nlinarith [sq_nonneg
      (2 * tribonacciError (n + 1) + (t - 1) * tribonacciError n)]
  calc
    tribonacciError n ^ 2 = (d * tribonacciError n ^ 2) / d := by
      field_simp [hd.ne']
    _ ≤ (4 * tribonacciErrorEnergy n) / d :=
      (div_le_div_iff_of_pos_right hd).2 hle
    _ = (4 / (4 * t⁻¹ - (t - 1) ^ 2)) * tribonacciErrorEnergy n := by
      dsimp [d]
      ring

theorem tribonacci_errorEnergy_eq (n : Nat) :
    tribonacciErrorEnergy n = tribonacciErrorEnergy 0 * (t⁻¹) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [tribonacci_errorEnergy_succ, ih, pow_succ]
      ring

/-- The non-Perron component of the Tribonacci recurrence decays to zero. -/
theorem tribonacci_error_tendsto_zero :
    Tendsto tribonacciError atTop (nhds 0) := by
  let d : Real := 4 * t⁻¹ - (t - 1) ^ 2
  let C : Real := (4 / d) * tribonacciErrorEnergy 0
  have hd : 0 < d := tribonacci_errorEnergy_discriminant_pos
  have hbase_pos : 0 < t⁻¹ := inv_pos.mpr tribonacciConstant_pos
  have hbase_lt : t⁻¹ < 1 := inv_lt_one_of_one_lt₀ one_lt_tribonacciConstant
  have hbound (n : Nat) : tribonacciError n ^ 2 ≤ C * (t⁻¹) ^ n := by
    calc
      tribonacciError n ^ 2 ≤
          (4 / (4 * t⁻¹ - (t - 1) ^ 2)) * tribonacciErrorEnergy n :=
        tribonacci_error_sq_le_energy n
      _ = C * (t⁻¹) ^ n := by
        rw [tribonacci_errorEnergy_eq]
        dsimp [C, d]
        ring
  have hpow : Tendsto (fun n : Nat => (t⁻¹) ^ n) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hbase_pos.le hbase_lt
  have hupper : Tendsto (fun n : Nat => C * (t⁻¹) ^ n) atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul hpow
  have hsq : Tendsto (fun n : Nat => tribonacciError n ^ 2) atTop (nhds 0) :=
    squeeze_zero (fun n => sq_nonneg (tribonacciError n)) hbound hupper
  have habs : Tendsto (fun n : Nat => |tribonacciError n|) atTop (nhds 0) := by
    have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
    simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, Real.sqrt_zero] using hsqrt
  exact (tendsto_zero_iff_abs_tendsto_zero tribonacciError).2 habs

/-- Consecutive Tribonacci-number ratios converge to the Tribonacci Perron root. -/
theorem tribonacci_ratio_tendsto :
    Tendsto (fun n : Nat => (tribonacci (n + 1) : Real) / tribonacci n)
      atTop (nhds t) := by
  have hquotient : Tendsto
      (fun n : Nat => tribonacciError n / (tribonacci n : Real))
      atTop (nhds 0) := by
    apply (tendsto_zero_iff_abs_tendsto_zero
      (fun n : Nat => tribonacciError n / (tribonacci n : Real))).2
    change Tendsto
      (fun n : Nat => |tribonacciError n / (tribonacci n : Real)|)
      atTop (nhds 0)
    apply squeeze_zero' (g := fun n : Nat => |tribonacciError n|)
    · exact Eventually.of_forall fun n => abs_nonneg _
    · filter_upwards [eventually_ge_atTop 2] with n hn
      have hpos_nat : 0 < tribonacci n := by
        have hlevel := tribonacci_level_pos (n - 2)
        have hn_index : n - 2 + 2 = n := Nat.sub_add_cancel hn
        simpa only [hn_index] using hlevel
      have hpos_real : (0 : Real) < tribonacci n := by exact_mod_cast hpos_nat
      have hone : (1 : Real) ≤ tribonacci n := by
        exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hpos_nat.ne')
      rw [abs_div, abs_of_pos hpos_real]
      exact div_le_self (abs_nonneg _) hone
    · exact (tendsto_zero_iff_abs_tendsto_zero tribonacciError).1
        tribonacci_error_tendsto_zero
  have heventual :
      (fun n : Nat => (tribonacci (n + 1) : Real) / tribonacci n) =ᶠ[atTop]
        (fun n : Nat => tribonacciError n / tribonacci n + t) := by
    filter_upwards [eventually_ge_atTop 2] with n hn
    have hpos_nat : 0 < tribonacci n := by
      have hlevel := tribonacci_level_pos (n - 2)
      have hn_index : n - 2 + 2 = n := Nat.sub_add_cancel hn
      simpa only [hn_index] using hlevel
    dsimp [tribonacciError]
    field_simp [Nat.cast_ne_zero.mpr hpos_nat.ne']
    ring
  have hadd : Tendsto
      (fun n : Nat => tribonacciError n / tribonacci n + t)
      atTop (nhds t) := by
    simpa using hquotient.add_const t
  exact hadd.congr' heventual.symm

/-- Consecutive Tribonacci-name cardinality ratios have the same Perron limit. -/
theorem tribonacci_name_card_ratio_tendsto :
    Tendsto
      (fun Q : Nat =>
        (Fintype.card (TribonacciName (Q + 1)) : Real) /
          Fintype.card (TribonacciName Q))
      atTop (nhds t) := by
  have hrewrite :
      (fun Q : Nat =>
        (Fintype.card (TribonacciName (Q + 1)) : Real) /
          Fintype.card (TribonacciName Q)) =
        fun Q : Nat => (tribonacci (Q + 3) : Real) / tribonacci (Q + 2) := by
    funext Q
    rw [tribonacci_name_card, tribonacci_name_card]
  rw [hrewrite]
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    (tendsto_add_atTop_iff_nat
      (f := fun n : Nat => (tribonacci (n + 1) : Real) / tribonacci n)
      (l := nhds t) 2).2 tribonacci_ratio_tendsto

example {x : Real} :
    x = t ↔ 1 < x ∧ x < 2 ∧ x ^ 3 = x ^ 2 + x + 1 :=
  eq_tribonacciConstant_iff

example :
    Tendsto (fun n : Nat => (tribonacci (n + 1) : Real) / tribonacci n)
      atTop (nhds t) :=
  tribonacci_ratio_tendsto

example :
    Tendsto
      (fun Q : Nat =>
        (Fintype.card (TribonacciName (Q + 1)) : Real) /
          Fintype.card (TribonacciName Q))
      atTop (nhds t) :=
  tribonacci_name_card_ratio_tendsto

example : (tribonacci 6 : Real) / tribonacci 5 = 13 / 7 := by
  norm_num [tribonacci]

example : (tribonacci 7 : Real) / tribonacci 6 = 24 / 13 := by
  norm_num [tribonacci]

example : (tribonacci 8 : Real) / tribonacci 7 = 11 / 6 := by
  norm_num [tribonacci]

example : (tribonacci 9 : Real) / tribonacci 8 = 81 / 44 := by
  norm_num [tribonacci]

example : (tribonacci 10 : Real) / tribonacci 9 = 149 / 81 := by
  norm_num [tribonacci]

example : (tribonacci 11 : Real) / tribonacci 10 = 274 / 149 := by
  norm_num [tribonacci]

end D5.S0.Tower.Tribonacci.PerronRoot
