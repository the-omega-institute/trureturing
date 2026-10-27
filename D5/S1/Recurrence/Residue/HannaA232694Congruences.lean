/- GID: D5/S1/Recurrence/Residue/HannaA232694Congruences
   generality: I
   mirror-B: D5/B/S1/Recurrence/Residue/HannaA232694Congruences
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S1/Recurrence/Residue/HannaA232694Congruences.result; premises=D5/S1/Recurrence/Residue/HannaA232694Congruences.numerator3,D5/S1/Recurrence/Residue/HannaA232694Congruences.multiple3
   digest: Hanna 232694 factorial coefficients satisfy both nominated congruences. -/

/-
admission_basis: open-problem-resolution (#21485; Proved)
proof_shape: content
escape_witness: D5.S1.Recurrence.Residue.HannaEGFMachinery.residual_transfer
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/21758.
The rational series equation is stated as printed; coefficient congruences concern n! times coeff n A.
The convolution and power constructions are reused from ExponentialImplicitParityPeriodThree.
-/

import D5.S1.Recurrence.Residue.HannaEGFMachinery

set_option maxHeartbeats 4000000

open PowerSeries
open D5.S1.Recurrence.Residue.IntegralEGFComposition

namespace D5.S1.Recurrence.Residue.HannaA232694Congruences

/-- The source equation over rational formal series; the source data fix A(0)=1. -/
def IsSolution (A : PowerSeries ℚ) : Prop :=
  constantCoeff A = 1 ∧
    PowerSeries.derivative (R := ℚ) A = A.subst (X * (PowerSeries.derivative (R := ℚ) A) ^ 4)

/-- The two nominated OEIS conjectures, on factorial-normalized integer coefficients. -/
def claim : Prop :=
  ∀ A : PowerSeries ℚ, IsSolution A →
    ∃ a : ℕ → ℤ,
      (∀ n : ℕ, eCoeff A n = (a n : ℚ)) ∧
        (∀ n : ℕ, 3 ≤ n → (3 : ℤ) ∣ a n) ∧
        (∀ n : ℕ, (8 : ℤ) ∣ a n - 1)


end D5.S1.Recurrence.Residue.HannaA232694Congruences

open D5.S1.Recurrence.Residue.HannaEGFMachinery
namespace D5.S1.Recurrence.Residue.HannaA232694Congruences

private noncomputable def F3 : PowerSeries ℚ := C (1 : ℚ) * X^0 + C (1 : ℚ) * X^1 + C ((1 / 2) : ℚ) * X^2
private noncomputable def B3 : PowerSeries ℚ := C (1 : ℚ) * X^0 + C (1 : ℚ) * X^1
private noncomputable def N3 : PowerSeries ℚ := (Polynomial.ofCoeffList (R := ℚ) [0,
  0,
  (-9 / 2),
  -10,
  -18,
  -29,
  -35,
  -28,
  -14,
  -4,
  (-1 / 2)] : PowerSeries ℚ)
private theorem numerator3 : B3 - (F3.subst (X * B3^4))^1 = N3 := by
  have hs : HasSubst (X * B3^4) := PowerSeries.HasSubst.X'.mul_left
  simp only [F3, subst_add (R := ℚ) hs, subst_mul (R := ℚ) hs,
    subst_pow (R := ℚ) hs, subst_X (R := ℚ) hs, subst_C, ← PowerSeries.C_apply]
  simp only [B3, N3, Polynomial.ofCoeffList_cons, Polynomial.ofCoeffList_nil, Polynomial.coe_add, Polynomial.coe_mul, Polynomial.coe_C, Polynomial.coe_X, Polynomial.coe_zero]
  <;> (simp only [PowerSeries.C_eq_algebraMap]; algebra with ℚ)
private theorem multiple3 : Multiple 3 N3 := by
  apply finite_multiple _ [0, 0, -3, -20, -144, -1160, -8400, -47040, -188160, -483840, -604800] 3
  intro n
  fin_cases n <;> norm_num [List.getElem!_eq_getElem?_getD, Nat.factorial]


private def f3 (n : ℕ) : ℤ := if n < 3 then (([1, 1, 1] : List ℤ)[n]?).getD 0 else 0
private theorem coeff_F3 (n : ℕ) : eCoeff F3 n = (f3 n : ℚ) := by
  by_cases hn : n < 3
  · interval_cases n <;> norm_num [coeff_X, F3, f3, eCoeff]
  · have hne0 : n ≠ 0 := by omega
    have hne1 : n ≠ 1 := by omega
    have hne2 : n ≠ 2 := by omega
    simp [F3, f3, eCoeff, coeff_X, hn, hne0, hne1, hne2]
private theorem F3_derivative : PowerSeries.derivative (R := ℚ) F3 = B3 := by
  simp [F3, B3, Derivation.leibniz, smul_eq_mul]
  <;> (simp only [PowerSeries.C_eq_algebraMap]; algebra with ℚ)
private theorem residual3 : Multiple 3 (PowerSeries.derivative (R := ℚ) F3 - sourceRhs F3 4 1 false) := by
  rw [sourceRhs, F3_derivative]
  simp only [Bool.false_eq_true, if_false]
  rw [numerator3]
  exact multiple3

theorem result : claim := by
  intro A hA
  have he : PowerSeries.derivative (R := ℚ) A = sourceRhs A 4 1 false := by simpa [sourceRhs] using hA.2
  obtain ⟨a,ha,hm⟩ := residual_transfer A F3 4 1 3 false hA.1 he f3 (coeff_F3) (by norm_num [f3]) (by simp) residual3
  obtain ⟨b,hb,hbmod⟩ := residual_transfer A (exp ℚ) 4 1 8 false hA.1 he (fun _ => 1) (by simp) rfl (by simp)
    (by simpa [sourceRhs] using D5.S1.Recurrence.Residue.HannaEGFMachinery.exp_residual 4 8 D5.S1.Recurrence.Residue.HannaEGFMachinery.expSum_four_mod_eight)
  have hab : a = b := by
    funext n
    have hh := (ha n).symm.trans (hb n)
    exact_mod_cast hh
  refine ⟨a,ha,?_,?_⟩
  · intro n hn
    simpa [f3, Nat.not_lt.mpr hn] using hm n
  · intro n
    rw [hab]
    exact hbmod n


end D5.S1.Recurrence.Residue.HannaA232694Congruences
