/- GID: D5/S3/Weil/ZetaBridge/WeilArithmeticCouplingParityGram
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaBridge/WeilArithmeticCouplingParityGram
   mirror-E: none(waiver:separate-interval-and-form-domain-bridges)
   anchors: []
   digest: The actual odd arithmetic symbol splits the paired second-jet energy into two moment Gram blocks. -/

import D5.S3.Weil.ZetaBridge.WeilArithmeticCouplingSecondJet
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.LinearCombination

/-!
# Reflection-paired arithmetic coupling

The symbol and jet are the existing pole-Gamma-prime objects. No new Weil
form, abstract odd-symbol premise, spectral gap, or zero data is introduced.
The exact paired identity retains four moments. The infinite summation and
its numerical application are proved separately in the existing theory volume.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Weil.ZetaBridge.WeilArithmeticCouplingParityGram

open scoped BigOperators
open D5.S3.Weil.ZetaBridge.WeilArithmeticCouplingJet
open D5.S3.Weil.ZetaBridge.WeilArithmeticCouplingSecondJet

/-- Reflection oddness follows from the actual pole, Gamma and finite prime
terms. On the arithmetic range c>=2, absolute convergence is already proved
by `arithmetic_boundary_symbol_bound`. -/
theorem arithmetic_boundary_symbol_neg (c : ℕ) (n : ℤ) :
    arithmeticBoundarySymbol c (-n) = -arithmeticBoundarySymbol c n := by
  let L : ℝ := Real.log (c : ℝ)
  let w : ℝ := 2 * Real.pi * (n : ℝ) / L
  let wm : ℝ := 2 * Real.pi * ((-n : ℤ) : ℝ) / L
  let b : ℕ → ℝ := fun j => 2 * (j : ℝ) + 1 / 2
  let P : ℝ → ℝ := fun t =>
    2 * t * (Real.cosh (L / 2) - 1) / (t ^ 2 + 1 / 4)
  let G : ℝ → ℝ := fun t =>
    ∑' j : ℕ, t * (1 - Real.exp (-b j * L)) / (b j ^ 2 + t ^ 2)
  let V : ℝ → ℝ := fun t =>
    ∑ j ∈ Finset.range c,
      (ArithmeticFunction.vonMangoldt j / Real.sqrt j) * Real.sin (t * Real.log j)
  change -P wm - G wm - V wm = -(-P w - G w - V w)
  have hw : wm = -w := by
    dsimp [wm, w]
    push_cast
    ring
  have hP : P (-w) = -P w := by
    dsimp [P]
    rw [neg_sq]
    ring
  have hG : G (-w) = -G w := by
    dsimp [G]
    rw [← tsum_neg]
    apply tsum_congr
    intro j
    rw [neg_sq]
    ring
  have hV : V (-w) = -V w := by
    dsimp [V]
    simp only [neg_mul, Real.sin_neg, mul_neg, Finset.sum_neg_distrib]
  rw [hw, hP, hG, hV]
  ring

private theorem collect_jet (S : Finset ℤ) (s v : ℤ → ℂ) (t p q : ℂ) :
    (∑ n ∈ S, ((s n - t) / p + (s n - t) * (n : ℂ) / q) * v n) =
      ((∑ n ∈ S, s n * v n) - t * ∑ n ∈ S, v n) / p +
      ((∑ n ∈ S, s n * ((n : ℂ) * v n)) -
        t * ∑ n ∈ S, (n : ℂ) * v n) / q := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert n S hn ih =>
      simp only [Finset.sum_insert hn]
      simp only [div_eq_mul_inv] at ih ⊢
      linear_combination ih

private theorem jet_collection (c : ℕ) (S : Finset ℤ) (v : ℤ → ℂ) (m : ℤ) :
    couplingSecondJet c S v m =
      ((∑ n ∈ S, (arithmeticBoundarySymbol c n : ℂ) * v n) -
        (arithmeticBoundarySymbol c m : ℂ) * ∑ n ∈ S, v n) /
          ((Real.pi : ℂ) * (m : ℂ)) +
      ((∑ n ∈ S, (arithmeticBoundarySymbol c n : ℂ) * ((n : ℂ) * v n)) -
        (arithmeticBoundarySymbol c m : ℂ) * ∑ n ∈ S, (n : ℂ) * v n) /
          ((Real.pi : ℂ) * (m : ℂ) ^ 2) := by
  unfold couplingSecondJet
  push_cast
  exact collect_jet S (fun n => (arithmeticBoundarySymbol c n : ℂ)) v
    (arithmeticBoundarySymbol c m : ℂ)
    ((Real.pi : ℂ) * (m : ℂ)) ((Real.pi : ℂ) * (m : ℂ) ^ 2)

/-- Exact paired energy of the actual second jet. No parity or reality is
required of the coefficients, and none of the four boundary moments vanishes
by assumption. The two squared terms give two positive 2-by-2 moment Gram
blocks on summation over positive exterior modes. -/
theorem arithmetic_second_jet_pair_energy
    (c : ℕ) (S : Finset ℤ) (v : ℤ → ℂ) (m : ℤ) (hm : m ≠ 0) :
    let A0 : ℂ := ∑ n ∈ S, v n
    let B0 : ℂ := ∑ n ∈ S, (arithmeticBoundarySymbol c n : ℂ) * v n
    let A1 : ℂ := ∑ n ∈ S, (n : ℂ) * v n
    let B1 : ℂ := ∑ n ∈ S, (arithmeticBoundarySymbol c n : ℂ) * ((n : ℂ) * v n)
    ‖couplingSecondJet c S v m‖ ^ 2 + ‖couplingSecondJet c S v (-m)‖ ^ 2 =
      (2 / (Real.pi ^ 2 * (m : ℝ) ^ 2)) *
        (‖-(arithmeticBoundarySymbol c m : ℂ) * A0 + B1 / (m : ℂ)‖ ^ 2 +
          ‖B0 - (arithmeticBoundarySymbol c m : ℂ) * A1 / (m : ℂ)‖ ^ 2) := by
  dsimp only
  let A0 : ℂ := ∑ n ∈ S, v n
  let B0 : ℂ := ∑ n ∈ S, (arithmeticBoundarySymbol c n : ℂ) * v n
  let A1 : ℂ := ∑ n ∈ S, (n : ℂ) * v n
  let B1 : ℂ := ∑ n ∈ S, (arithmeticBoundarySymbol c n : ℂ) * ((n : ℂ) * v n)
  let U : ℂ := -(arithmeticBoundarySymbol c m : ℂ) * A0 + B1 / (m : ℂ)
  let V : ℂ := B0 - (arithmeticBoundarySymbol c m : ℂ) * A1 / (m : ℂ)
  let z : ℂ := ((Real.pi * (m : ℝ) : ℝ) : ℂ)
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast hm
  have hpC : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hplus : couplingSecondJet c S v m = (U + V) / z := by
    rw [jet_collection]
    dsimp [U, V, z, A0, B0, A1, B1]
    push_cast
    field_simp [hmC, hpC]
    <;> ring
  have hminus : couplingSecondJet c S v (-m) = (U - V) / z := by
    rw [jet_collection, arithmetic_boundary_symbol_neg]
    dsimp [U, V, z, A0, B0, A1, B1]
    push_cast
    field_simp [hmC, hpC]
    <;> ring
  have hz : ‖z‖ ^ 2 = Real.pi ^ 2 * (m : ℝ) ^ 2 := by
    dsimp [z]
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
    ring
  change ‖couplingSecondJet c S v m‖ ^ 2 + ‖couplingSecondJet c S v (-m)‖ ^ 2 =
    (2 / (Real.pi ^ 2 * (m : ℝ) ^ 2)) * (‖U‖ ^ 2 + ‖V‖ ^ 2)
  rw [hplus, hminus, norm_div, norm_div, div_pow, div_pow, ← add_div,
    parallelogram_law_with_norm ℂ U V, hz]
  ring

#print axioms arithmetic_boundary_symbol_neg
#print axioms arithmetic_second_jet_pair_energy

end D5.S3.Weil.ZetaBridge.WeilArithmeticCouplingParityGram
