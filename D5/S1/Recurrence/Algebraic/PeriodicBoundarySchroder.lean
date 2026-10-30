/- GID: D5/S1/Recurrence/Algebraic/PeriodicBoundarySchroder
   generality: I
   mirror-B: D5/B/S1/Recurrence/Algebraic/PeriodicBoundarySchroder
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Kurkov's two periodic boundary recurrences have the large Schroder diagonal. -/

module

public import D5.S1.Recurrence.Algebraic.SchroderIntegralEGF
public import Mathlib.Tactic

/-! The two periodic source shifts are identified through a rational formal-series
model and induction first on coefficient degree, then on the unbounded column. -/

@[expose] public section

set_option autoImplicit false

open PowerSeries

namespace D5.S1.Recurrence.Algebraic.PeriodicBoundarySchroder

/-- The original natural array; the zeroth-row clause has priority for every column.
The recurrence is due to Mikhail Kurkov, OEIS A376317 (CC-BY-SA-4.0). -/
def P (f : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 1
  | n + 1, m => if m ≤ n + 1 then P f n m
      else P f (n + 1) (m - 1) + P f n (m + f (m - (n + 1)))
termination_by n m => (n, m)
decreasing_by all_goals simp_wf; omega

/-- The period-two shift in the source conjecture. -/
def f2 (d : ℕ) : ℕ := d % 2

/-- The period-three shift in the source conjecture. -/
def f3 (d : ℕ) : ℕ := if d % 3 = 0 then 0 else 1

private def C (f : ℕ → ℕ) (n d : ℕ) : ℕ := P f n (n + d)

private theorem C_zero (f : ℕ → ℕ) (d : ℕ) : C f 0 d = 1 := by
  simp [C, P]

private theorem C_boundary (f : ℕ → ℕ) (n : ℕ) : C f (n + 1) 0 = C f n 1 := by
  simp [C, P]

private theorem C_step (f : ℕ → ℕ) (n d : ℕ) :
    C f (n + 1) (d + 1) = C f (n + 1) d + C f n (d + 2 + f (d + 1)) := by
  have hm : ¬ n + 1 + (d + 1) ≤ n + 1 := by omega
  unfold C
  rw [P, ite_eq_right hm]
  rw [show n + 1 + (d + 1) - (n + 1) = d + 1 by omega]
  congr 2 <;> omega

/-- Coefficient degree is the outer induction; its hypothesis covers every column. -/
private theorem coefficient_identification (f : ℕ → ℕ) (H : ℕ → PowerSeries ℚ)
    (h0 : ∀ d, constantCoeff (H d) = 1)
    (hb : H 0 = 1 + X * H 1)
    (hs : ∀ d, H (d + 1) = H d + X * H (d + 2 + f (d + 1))) :
    ∀ n d, (C f n d : ℚ) = coeff n (H d) := by
  intro n
  induction n with
  | zero => intro d; simp [C_zero, coeff_zero_eq_constantCoeff, h0]
  | succ n ih =>
    intro d
    induction d with
    | zero =>
      rw [C_boundary, hb]
      simpa using ih 1
    | succ d hd =>
      rw [C_step, Nat.cast_add, hs d, map_add, coeff_succ_X_mul, ← hd, ← ih]

local notation "S" => D5.S1.Recurrence.Algebraic.SchroderIntegralEGF.R

private noncomputable def H2 (d : ℕ) : PowerSeries ℚ :=
  if d % 2 = 0 then (1 + X * S) * S ^ (d / 2) else S ^ (d / 2 + 1)

private theorem H2_even (j : ℕ) : H2 (2 * j) = (1 + X * S) * S ^ j := by
  simp [H2]

private theorem H2_odd (j : ℕ) : H2 (2 * j + 1) = S ^ (j + 1) := by
  have hd : (2 * j + 1) / 2 = j := by omega
  simp [H2, hd]

private theorem H2_system :
    (∀ d, constantCoeff (H2 d) = 1) ∧
    H2 0 = 1 + X * H2 1 ∧
    ∀ d, H2 (d + 1) = H2 d + X * H2 (d + 2 + f2 (d + 1)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro d
    unfold H2
    split_ifs <;> simp [D5.S1.Recurrence.Algebraic.SchroderIntegralEGF.R_zero]
  · simp [H2]
  · intro d
    have hr := Nat.mod_lt d (by decide : 0 < 2)
    have he := Nat.mod_add_div d 2
    rcases (show d % 2 = 0 ∨ d % 2 = 1 by omega) with h | h
    · obtain ⟨j, rfl⟩ : ∃ j, d = 2 * j := ⟨d / 2, by omega⟩
      have hf : f2 (2 * j + 1) = 1 := by simp [f2]
      rw [hf, H2_odd, H2_even]
      rw [show 2 * j + 2 + 1 = 2 * (j + 1) + 1 by omega, H2_odd]
      rw [pow_succ, pow_succ]
      linear_combination S ^ j * D5.S1.Recurrence.Algebraic.SchroderIntegralEGF.R_eq
    · obtain ⟨j, rfl⟩ : ∃ j, d = 2 * j + 1 := ⟨d / 2, by omega⟩
      have hf : f2 (2 * j + 1 + 1) = 0 := by simp [f2, Nat.add_mod]
      rw [hf, show 2 * j + 1 + 1 = 2 * (j + 1) by omega, H2_even, H2_odd]
      rw [show 2 * j + 1 + 2 + 0 = 2 * (j + 1) + 1 by omega, H2_odd]
      rw [pow_succ]
      ring

private noncomputable def R : PowerSeries ℚ :=
  (PowerSeries.C (1 / 2 : ℚ)) * (S ^ 2 + S)

private theorem R_equations : R - S = X * S * R ∧ S ^ 2 - R = X * S * R := by
  have hc : (2 : PowerSeries ℚ) * PowerSeries.C (1 / 2 : ℚ) = 1 := by
    change PowerSeries.C (2 : ℚ) * PowerSeries.C (1 / 2 : ℚ) = 1
    rw [← map_mul]
    norm_num
  constructor <;> dsimp [R]
  · linear_combination (PowerSeries.C (1 / 2 : ℚ)) * S * D5.S1.Recurrence.Algebraic.SchroderIntegralEGF.R_eq +
      S * hc
  · linear_combination (PowerSeries.C (1 / 2 : ℚ)) * S * D5.S1.Recurrence.Algebraic.SchroderIntegralEGF.R_eq -
      S ^ 2 * hc

private theorem R_constant : constantCoeff R = 1 := by
  norm_num [R, D5.S1.Recurrence.Algebraic.SchroderIntegralEGF.R_zero]

private noncomputable def H3 (d : ℕ) : PowerSeries ℚ :=
  if d = 0 then 1 + X * S else
    if (d - 1) % 3 = 0 then S * R ^ ((d - 1) / 3) else
    if (d - 1) % 3 = 1 then R ^ ((d - 1) / 3 + 1) else S ^ 2 * R ^ ((d - 1) / 3)

private theorem H3_one (j : ℕ) : H3 (3 * j + 1) = S * R ^ j := by
  simp [H3]
private theorem H3_two (j : ℕ) : H3 (3 * j + 2) = R ^ (j + 1) := by
  have hd : (3 * j + 1) / 3 = j := by omega
  simp [H3, show 3 * j + 2 - 1 = 3 * j + 1 by omega, hd]
private theorem H3_three (j : ℕ) : H3 (3 * j + 3) = S ^ 2 * R ^ j := by
  have hd : (3 * j + 2) / 3 = j := by omega
  simp [H3, show 3 * j + 3 - 1 = 3 * j + 2 by omega, hd]

private theorem H3_system :
    (∀ d, constantCoeff (H3 d) = 1) ∧
    H3 0 = 1 + X * H3 1 ∧
    ∀ d, H3 (d + 1) = H3 d + X * H3 (d + 2 + f3 (d + 1)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro d
    unfold H3
    split_ifs <;> simp [D5.S1.Recurrence.Algebraic.SchroderIntegralEGF.R_zero, R_constant]
  · simp [H3]
  · intro d
    cases d with
    | zero => simpa [H3, f3] using D5.S1.Recurrence.Algebraic.SchroderIntegralEGF.R_eq
    | succ d =>
      have hr := Nat.mod_lt d (by decide : 0 < 3)
      have he := Nat.mod_add_div d 3
      rcases (show d % 3 = 0 ∨ d % 3 = 1 ∨ d % 3 = 2 by omega) with h | h | h
      · obtain ⟨j, rfl⟩ : ∃ j, d = 3 * j := ⟨d / 3, by omega⟩
        have hf : f3 (3 * j + 1 + 1) = 1 := by simp [f3, Nat.add_mod]
        change H3 (3 * j + 1 + 1) = H3 (3 * j + 1) + X * H3 (3 * j + 1 + 2 + f3 (3 * j + 1 + 1))
        rw [hf, show 3 * j + 1 + 1 = 3 * j + 2 by omega, H3_two, H3_one]
        rw [show 3 * j + 1 + 2 + 1 = 3 * (j + 1) + 1 by omega, H3_one, pow_succ]
        linear_combination R ^ j * R_equations.1
      · obtain ⟨j, rfl⟩ : ∃ j, d = 3 * j + 1 := ⟨d / 3, by omega⟩
        have hf : f3 (3 * j + 2 + 1) = 0 := by simp [f3, Nat.add_mod]
        change H3 (3 * j + 2 + 1) = H3 (3 * j + 2) + X * H3 (3 * j + 2 + 2 + f3 (3 * j + 2 + 1))
        rw [hf, show 3 * j + 2 + 1 = 3 * j + 3 by omega, H3_three, H3_two]
        rw [show 3 * j + 2 + 2 + 0 = 3 * (j + 1) + 1 by omega, H3_one, pow_succ]
        linear_combination R ^ j * R_equations.2
      · obtain ⟨j, rfl⟩ : ∃ j, d = 3 * j + 2 := ⟨d / 3, by omega⟩
        have hf : f3 (3 * j + 3 + 1) = 1 := by simp [f3, Nat.add_mod]
        change H3 (3 * j + 3 + 1) = H3 (3 * j + 3) + X * H3 (3 * j + 3 + 2 + f3 (3 * j + 3 + 1))
        rw [hf, show 3 * j + 3 + 1 = 3 * (j + 1) + 1 by omega, H3_one, H3_three]
        rw [show 3 * j + 3 + 2 + 1 = 3 * (j + 1) + 3 by omega, H3_three, pow_succ]
        linear_combination S * R ^ j * R_equations.1

/-- Both periodic shifts in Kurkov's conjecture give A006318, without an index shift. -/
theorem result (n : ℕ) :
    P f2 (n + 1) (n + 1) = Nat.largeSchroder n ∧
    P f3 (n + 1) (n + 1) = Nat.largeSchroder n := by
  have diagonal (f : ℕ → ℕ) (H : ℕ → PowerSeries ℚ)
      (h0 : ∀ d, constantCoeff (H d) = 1)
      (hb : H 0 = 1 + X * H 1)
      (hs : ∀ d, H (d + 1) = H d + X * H (d + 2 + f (d + 1)))
      (h1 : H 1 = S) : P f (n + 1) (n + 1) = Nat.largeSchroder n := by
    have h := coefficient_identification f H h0 hb hs n 1
    rw [h1] at h
    have hp : P f (n + 1) (n + 1) = C f n 1 := by simp [P, C]
    rw [hp]
    exact_mod_cast (show (C f n 1 : ℚ) = (Nat.largeSchroder n : ℚ) by simpa [S] using h)
  exact ⟨diagonal f2 H2 H2_system.1 H2_system.2.1 H2_system.2.2 (by simp [H2]),
    diagonal f3 H3 H3_system.1 H3_system.2.1 H3_system.2.2 (by simp [H3])⟩

end D5.S1.Recurrence.Algebraic.PeriodicBoundarySchroder
