import OmegaBuild.Commands
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Pi
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! Omega original.

The five occupation coordinates of the half-spin weight system for the
compact ten-dimensional orthogonal Lie algebra. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OmegaMath.SpinorWeights5

abbrev Weight := Fin 5 → Bool

def occupied (w : Weight) : Finset (Fin 5) := Finset.univ.filter fun i => w i = true

def count (w : Weight) : ℕ := (occupied w).card

abbrev EvenWeight := {w : Weight // Even (count w)}
abbrev OddWeight := {w : Weight // Odd (count w)}

private def listedWeight : Fin 16 → Weight :=
  ![![false, false, false, false, false],
    ![true, false, false, true, false], ![true, false, false, false, true],
    ![false, true, false, true, false], ![false, true, false, false, true],
    ![false, false, true, true, false], ![false, false, true, false, true],
    ![true, true, false, false, false], ![true, false, true, false, false],
    ![false, true, true, false, false],
    ![false, true, true, true, true], ![true, false, true, true, true],
    ![true, true, false, true, true], ![true, true, true, true, false],
    ![true, true, true, false, true], ![false, false, false, true, true]]

private theorem listedWeight_even : ∀ i, Even (count (listedWeight i)) := by decide

/-- Enumerate the even weights with the empty occupation first. -/
noncomputable def evenWeight : Fin 16 ≃ EvenWeight :=
  Equiv.ofBijective (fun i => ⟨listedWeight i, listedWeight_even i⟩) (by
    constructor
    · intro i j hij
      have h : ∀ i j, listedWeight i = listedWeight j → i = j := by decide
      exact h i j (congrArg Subtype.val hij)
    · have h : ∀ w : Weight, Even (count w) → ∃ i, listedWeight i = w := by decide
      intro w
      obtain ⟨i, hi⟩ := h w.1 w.2
      exact ⟨i, Subtype.ext hi⟩)

theorem so10_spinor16_card :
    Fintype.card Weight = 32 ∧ Fintype.card EvenWeight = 16 ∧
    Fintype.card OddWeight = 16 ∧
    Fintype.card {w : Weight // count w = 0} = 1 ∧
    Fintype.card {w : Weight // count w = 2} = 10 ∧
    Fintype.card {w : Weight // count w = 4} = 5 ∧
    Fintype.card EvenWeight = 1 + 10 + 5 := by
  decide

noncomputable section

/-- Occupied coordinates have Cartan weight one half. -/
def H (w : Weight) (i : Fin 5) : ℝ := if w i then 1 / 2 else -1 / 2

def cartan (h : Fin 5 → ℝ) (w : Weight) : ℝ := ∑ i, h i * H w i

def occupationAction (h : Fin 5 → ℝ) (w : Weight) : ℝ := ∑ i ∈ occupied w, h i

theorem cartan_eq_occupation_shift (h : Fin 5 → ℝ) (w : Weight) :
    cartan h w = occupationAction h w - (∑ i, h i) / 2 := by
  rw [cartan, occupationAction, occupied, Finset.sum_filter, div_eq_mul_inv, Finset.sum_mul,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  cases hwi : w i <;> simp [H, hwi] <;> ring

/-- The traceless Cartan action on the vacuum, the pairs and the missing indices. -/
theorem so10_su5_cartan_restriction (h : Fin 5 → ℝ) (hh : ∑ i, h i = 0) :
    (fun i => cartan h (evenWeight i).1) =
      ![0, h 0 + h 3, h 0 + h 4, h 1 + h 3, h 1 + h 4, h 2 + h 3, h 2 + h 4,
        h 0 + h 1, h 0 + h 2, h 1 + h 2,
        -h 0, -h 1, -h 2, -h 4, -h 3, h 3 + h 4] := by
  funext i
  rw [cartan_eq_occupation_shift, hh, zero_div, sub_zero]
  change occupationAction h (listedWeight i) = _
  rw [occupationAction, occupied, Finset.sum_filter]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero] at hh ⊢
  change h 0 + (h 1 + (h 2 + (h 3 + (h 4 + 0)))) = 0 at hh
  fin_cases i <;> simp [listedWeight] <;> linear_combination hh

def hyperchargeCoefficients : Fin 5 → ℝ := ![-1 / 3, -1 / 3, -1 / 3, 1 / 2, 1 / 2]

def weakCoefficients : Fin 5 → ℝ := ![0, 0, 0, 1 / 2, -1 / 2]

def hypercharge (w : Weight) : ℝ := occupationAction hyperchargeCoefficients w

def t3L (w : Weight) : ℝ := (H w 3 - H w 4) / 2

def t3R (w : Weight) : ℝ := (H w 3 + H w 4) / 2

def electricCharge (w : Weight) : ℝ :=
  occupationAction (hyperchargeCoefficients + weakCoefficients) w

def xCharge (w : Weight) : ℝ := 5 - 2 * (count w : ℝ)

def bMinusL (w : Weight) : ℝ := (xCharge w + 4 * hypercharge w) / 5

theorem so10_hypercharge_formula (w : Weight) :
    hypercharge w = -(1 / 3) * (H w 0 + H w 1 + H w 2) +
      (1 / 2) * (H w 3 + H w 4) := by
  have hh : ∑ i, hyperchargeCoefficients i = 0 := by
    norm_num [hyperchargeCoefficients, Fin.sum_univ_succ]
  rw [hypercharge, ← sub_zero (occupationAction _ w), ← zero_div 2, ← hh,
    ← cartan_eq_occupation_shift]
  simp [cartan, hyperchargeCoefficients, Fin.sum_univ_succ]
  ring

theorem so10_b_minus_l_is_cartan (w : Weight) :
    bMinusL w = -(2 / 3) * (H w 0 + H w 1 + H w 2) := by
  have hc : (count w : ℝ) = occupationAction (fun _ => 1) w := by
    simp [count, occupationAction]
  have hx : xCharge w = -2 * cartan (fun _ => 1) w := by
    rw [xCharge, hc, cartan_eq_occupation_shift]
    norm_num
    ring
  rw [bMinusL, hx, so10_hypercharge_formula]
  simp [cartan, Fin.sum_univ_succ]
  ring

theorem so10_electric_charge_gell_mann_nishijima (w : Weight) :
    electricCharge w = t3L w + t3R w + bMinusL w / 2 := by
  have hh : ∑ i, (hyperchargeCoefficients + weakCoefficients) i = 0 := by
    norm_num [hyperchargeCoefficients, weakCoefficients, Fin.sum_univ_succ]
  rw [electricCharge, ← sub_zero (occupationAction _ w), ← zero_div 2, ← hh,
    ← cartan_eq_occupation_shift, so10_b_minus_l_is_cartan]
  simp [cartan, hyperchargeCoefficients, weakCoefficients, t3L, t3R, Fin.sum_univ_succ]
  ring

/-- The cubic trace vanishes on every real Cartan element. -/
theorem so10_spinor16_anomaly_free (h : Fin 5 → ℝ) :
    ∑ w : EvenWeight, (cartan h w.1) ^ 3 = 0 := by
  rw [← evenWeight.sum_comp (fun w => (cartan h w.1) ^ 3)]
  change (∑ i, (cartan h (listedWeight i)) ^ 3) = 0
  simp [cartan, H, listedWeight, Fin.sum_univ_succ]
  ring

/-- The entries of each row give B minus L, left and right weak weights,
hypercharge and electric charge. -/
theorem so10_all_16_fermion_quantum_numbers :
    (fun i =>
      let w := (evenWeight i).1
      (bMinusL w, t3L w, t3R w, hypercharge w, electricCharge w)) =
    (![ (1, 0, -1 / 2, 0, 0),
        (1 / 3, 1 / 2, 0, 1 / 6, 2 / 3), (1 / 3, -1 / 2, 0, 1 / 6, -1 / 3),
        (1 / 3, 1 / 2, 0, 1 / 6, 2 / 3), (1 / 3, -1 / 2, 0, 1 / 6, -1 / 3),
        (1 / 3, 1 / 2, 0, 1 / 6, 2 / 3), (1 / 3, -1 / 2, 0, 1 / 6, -1 / 3),
        (-1 / 3, 0, -1 / 2, -2 / 3, -2 / 3),
        (-1 / 3, 0, -1 / 2, -2 / 3, -2 / 3),
        (-1 / 3, 0, -1 / 2, -2 / 3, -2 / 3),
        (-1 / 3, 0, 1 / 2, 1 / 3, 1 / 3), (-1 / 3, 0, 1 / 2, 1 / 3, 1 / 3),
        (-1 / 3, 0, 1 / 2, 1 / 3, 1 / 3),
        (-1, 1 / 2, 0, -1 / 2, 0), (-1, -1 / 2, 0, -1 / 2, -1),
        (1, 0, 1 / 2, 1, 1)] : Fin 16 → ℝ × ℝ × ℝ × ℝ × ℝ) := by
  funext i
  dsimp only
  rw [so10_electric_charge_gell_mann_nishijima, so10_b_minus_l_is_cartan,
    so10_hypercharge_formula]
  fin_cases i <;> norm_num [evenWeight, H, listedWeight, t3L, t3R,
    so10_b_minus_l_is_cartan]

end

end OmegaMath.SpinorWeights5
