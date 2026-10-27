/- GID: D5/S1/Recurrence/Residue/HannaA232686Congruences
   generality: I
   mirror-B: D5/B/S1/Recurrence/Residue/HannaA232686Congruences
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S1/Recurrence/Residue/HannaA232686Congruences.result; premises=D5/S1/Recurrence/Residue/HannaA232686Congruences.numerator2,D5/S1/Recurrence/Residue/HannaA232686Congruences.multiple2,D5/S1/Recurrence/Residue/HannaA232686Congruences.numerator4,D5/S1/Recurrence/Residue/HannaA232686Congruences.multiple4
   digest: Hanna 232686 factorial coefficients satisfy both nominated congruences. -/

/-
admission_basis: open-problem-resolution (#21488; Proved)
escape_witness: none
Direct frozen dependencies: generated per declaration in the Stage A envelope.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/21758.
The rational series equation is stated as printed; coefficient congruences concern n! times coeff n A.
The convolution and power constructions are reused from ExponentialImplicitParityPeriodThree.
-/

import D5.S1.Recurrence.Residue.HannaEGFMachinery

set_option maxHeartbeats 4000000

open PowerSeries
open D5.S1.Recurrence.Residue.IntegralEGFComposition

namespace D5.S1.Recurrence.Residue.HannaA232686Congruences

/-- The source equation over rational formal series; the source data fix A(0)=1. -/
def IsSolution (A : PowerSeries ℚ) : Prop :=
  constantCoeff A = 1 ∧
    PowerSeries.derivative (R := ℚ) A = (A.subst (X * PowerSeries.derivative (R := ℚ) A)) ^ 2

/-- The two nominated OEIS conjectures, on factorial-normalized integer coefficients. -/
def claim : Prop :=
  ∀ A : PowerSeries ℚ, IsSolution A →
    ∃ a : ℕ → ℤ,
      (∀ n : ℕ, eCoeff A n = (a n : ℚ)) ∧
        (∀ n : ℕ, 2 ≤ n → (2 : ℤ) ∣ a n) ∧
        (∀ n : ℕ, 4 ≤ n → (4 : ℤ) ∣ a n)


end D5.S1.Recurrence.Residue.HannaA232686Congruences

open D5.S1.Recurrence.Residue.HannaEGFMachinery
namespace D5.S1.Recurrence.Residue.HannaA232686Congruences

private noncomputable def F2 : PowerSeries ℚ := C (1 : ℚ) * X^0 + C (1 : ℚ) * X^1
private noncomputable def B2 : PowerSeries ℚ := C (1 : ℚ) * X^0
private noncomputable def N2 : PowerSeries ℚ := finiteSeries [0,
  -2,
  -1]
private theorem numerator2 : B2 - (F2.subst (X * B2^1))^2 = N2 := by
  have hs : HasSubst (X * B2^1) := PowerSeries.HasSubst.X'.mul_left
  simp only [F2, subst_add (R := ℚ) hs, subst_mul (R := ℚ) hs,
    subst_pow (R := ℚ) hs, subst_X (R := ℚ) hs, subst_C, ← PowerSeries.C_apply]
  simp only [B2, N2, finiteSeries, List.foldr_cons, List.foldr_nil]
  <;> (simp only [PowerSeries.C_eq_algebraMap]; algebra with ℚ)
private theorem multiple2 : Multiple 2 N2 := by
  apply finite_multiple _ [0, -1, -1] 2
  intro n
  fin_cases n <;> norm_num [List.getElem!_eq_getElem?_getD, Nat.factorial]

private noncomputable def F4 : PowerSeries ℚ := C (1 : ℚ) * X^0 + C (1 : ℚ) * X^1 + C (1 : ℚ) * X^2 + C ((7 / 3) : ℚ) * X^3
private noncomputable def B4 : PowerSeries ℚ := C (1 : ℚ) * X^0 + C (2 : ℚ) * X^1 + C (7 : ℚ) * X^2
private noncomputable def N4 : PowerSeries ℚ := finiteSeries [0,
  0,
  0,
  (-98 / 3),
  (-299 / 3),
  -354,
  (-9964 / 9),
  (-9266 / 3),
  -7856,
  (-179620 / 9),
  (-143969 / 3),
  (-338884 / 3),
  (-743869 / 3),
  -479514,
  (-2461025 / 3),
  (-10453954 / 9),
  (-4000066 / 3),
  (-3294172 / 3),
  (-5764801 / 9)]
private theorem numerator4 : B4 - (F4.subst (X * B4^1))^2 = N4 := by
  have hs : HasSubst (X * B4^1) := PowerSeries.HasSubst.X'.mul_left
  simp only [F4, subst_add (R := ℚ) hs, subst_mul (R := ℚ) hs,
    subst_pow (R := ℚ) hs, subst_X (R := ℚ) hs, subst_C, ← PowerSeries.C_apply]
  simp only [B4, N4, finiteSeries, List.foldr_cons, List.foldr_nil]
  <;> (simp only [PowerSeries.C_eq_algebraMap]; algebra with ℚ)
private theorem multiple4 : Multiple 4 N4 := by
  apply finite_multiple _ [0, 0, 0, -49, -598, -10620, -199280, -3891720, -79188480, -1810569600, -43536225600, -1127263737600, -29692870099200, -746485912972800, -17878996175040000, -379732435834752000, -6974378371344384000, -97641297198821376000, -1025233620587624448000] 4
  intro n
  fin_cases n <;> norm_num [List.getElem!_eq_getElem?_getD, Nat.factorial]


private def f2 (n : ℕ) : ℤ := if n < 2 then (([1, 1] : List ℤ)[n]?).getD 0 else 0
private theorem coeff_F2 (n : ℕ) : eCoeff F2 n = (f2 n : ℚ) := by
  by_cases hn : n < 2
  · interval_cases n <;> norm_num [coeff_X, F2, f2, eCoeff]
  · have hne0 : n ≠ 0 := by omega
    have hne1 : n ≠ 1 := by omega
    simp [F2, f2, eCoeff, coeff_X, hn, hne0, hne1]
private theorem F2_derivative : PowerSeries.derivative (R := ℚ) F2 = B2 := by
  simp [F2, B2]
  <;> (simp only [PowerSeries.C_eq_algebraMap]; algebra with ℚ)
private theorem residual2 : Multiple 2 (PowerSeries.derivative (R := ℚ) F2 - sourceRhs F2 1 2 false) := by
  rw [sourceRhs, F2_derivative]
  simp only [Bool.false_eq_true, if_false]
  rw [numerator2]
  exact multiple2

private def f4 (n : ℕ) : ℤ := if n < 4 then (([1, 1, 2, 14] : List ℤ)[n]?).getD 0 else 0
private theorem coeff_F4 (n : ℕ) : eCoeff F4 n = (f4 n : ℚ) := by
  by_cases hn : n < 4
  · interval_cases n <;> norm_num [coeff_X, F4, f4, eCoeff]
  · have hne0 : n ≠ 0 := by omega
    have hne1 : n ≠ 1 := by omega
    have hne2 : n ≠ 2 := by omega
    have hne3 : n ≠ 3 := by omega
    simp [F4, f4, eCoeff, coeff_X, hn, hne0, hne1, hne2, hne3]
private theorem F4_derivative : PowerSeries.derivative (R := ℚ) F4 = B4 := by
  simp [F4, B4, Derivation.leibniz, smul_eq_mul]
  <;> (simp only [PowerSeries.C_eq_algebraMap]; algebra with ℚ)
private theorem residual4 : Multiple 4 (PowerSeries.derivative (R := ℚ) F4 - sourceRhs F4 1 2 false) := by
  rw [sourceRhs, F4_derivative]
  simp only [Bool.false_eq_true, if_false]
  rw [numerator4]
  exact multiple4

theorem result : claim := by
  intro A hA
  have he : PowerSeries.derivative (R := ℚ) A = sourceRhs A 1 2 false := by simpa [sourceRhs] using hA.2
  obtain ⟨a2,ha2,hm2⟩ := residual_transfer A F2 1 2 2 false hA.1 he f2 (coeff_F2) (by norm_num [f2]) (by intro h; rw [F2_derivative]; norm_num [B2]) residual2
  obtain ⟨a4,ha4,hm4⟩ := residual_transfer A F4 1 2 4 false hA.1 he f4 (coeff_F4) (by norm_num [f4]) (by intro h; rw [F4_derivative]; norm_num [B4]) residual4
  have hab : a2 = a4 := by
    funext n
    have hh := (ha2 n).symm.trans (ha4 n)
    exact_mod_cast hh
  refine ⟨a2,ha2,?_,?_⟩
  · intro n hn
    simpa [f2, Nat.not_lt.mpr hn] using hm2 n
  · intro n hn
    rw [hab]
    simpa [f4, Nat.not_lt.mpr hn] using hm4 n


end D5.S1.Recurrence.Residue.HannaA232686Congruences
