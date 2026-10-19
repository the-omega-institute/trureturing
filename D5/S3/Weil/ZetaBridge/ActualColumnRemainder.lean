/- GID: D5/S3/Weil/ZetaBridge/ActualColumnRemainder
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaBridge/ActualColumnRemainder
   mirror-E: none(waiver:general-analytic-identity-and-tail-estimate)
   anchors: []
   utility: none
   digest: Actual weighted first-jet column error and paired infinite remainder. -/

/- SOURCE_ONLY_UNCOMPILED. Genuine weighted-column remainder declarations
migrated from ActualFullSymbolTail with their complete proofs. Both exterior
signs, arbitrary complex head coefficients and every separated cutoff remain.
Kernel, axioms, Reg source selection/enrollment, Scribe emission and required
CI have not been checked. No operator identification or RH positivity is claimed. -/
import D5.S3.Weil.ZetaBridge.WeilArithmeticCouplingJet
import D5.S3.Weil.ZetaBridge.WeilEvenFourierObservationTail
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Real

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Weil.ZetaBridge.ActualColumnRemainder
open scoped BigOperators
open D5.S3.Weil.ZetaBridge.WeilArithmeticCouplingJet

/-- The actual absolute first moment of the finite complex head. -/
def weightedHeadMass (S : Finset ℤ) (v : ℤ → ℂ) : ℝ :=
  ∑ n ∈ S, |(n : ℝ)| * ‖v n‖

/-- Exact paired remainder budget; no replacement of W by A times head mass. -/
def pairedRemainderBudget (c M : ℕ) (A : ℝ) (S : Finset ℤ) (v : ℤ → ℂ) : ℝ :=
  8 * arithmeticBoundaryBudget c ^ 2 * weightedHeadMass S v ^ 2 * ((M : ℝ) + 1) ^ 2 /
    (3 * Real.pi ^ 2 * (M : ℝ) ^ 3 * ((M : ℝ) + 1 - A) ^ 2)

/-- Weighted pointwise error at every actual separated integer exterior mode.
The owner theorem is applied with the individual singleton radius |n|. -/
theorem weighted_coupling_first_jet_error {c : ℕ} (hc : 2 ≤ c)
    (S : Finset ℤ) (v : ℤ → ℂ) {A : ℝ} (hA : 0 ≤ A)
    (hS : ∀ n ∈ S, |(n : ℝ)| ≤ A) {m : ℤ} (hm : A < |(m : ℝ)|) :
    ‖couplingColumn c S v m - couplingFirstJet c S v m‖ ≤
      2 * arithmeticBoundaryBudget c * weightedHeadMass S v /
        (Real.pi * |(m : ℝ)| * (|(m : ℝ)| - A)) := by
  classical
  have hB : 0 ≤ arithmeticBoundaryBudget c :=
    (abs_nonneg _).trans (arithmetic_boundary_symbol_bound hc 0).2
  have hm0 : 0 < |(m : ℝ)| := lt_of_le_of_lt hA hm
  have hgap : 0 < |(m : ℝ)| - A := sub_pos.mpr hm
  have hsingle (n : ℤ) (hn : n ∈ S) :
      ‖couplingColumn c {n} v m - couplingFirstJet c {n} v m‖ ≤
        (2 * arithmeticBoundaryBudget c * |(n : ℝ)| /
          (Real.pi * |(m : ℝ)| * (|(m : ℝ)| - A))) * ‖v n‖ := by
    have hlocal := arithmetic_coupling_first_jet_error hc ({n} : Finset ℤ) v
      (abs_nonneg (n : ℝ)) (by
        intro l hl
        simpa only [Finset.mem_singleton.mp hl] using (le_refl |(n : ℝ)|))
      (lt_of_le_of_lt (hS n hn) hm)
    simp only [Finset.sum_singleton] at hlocal
    have hd : Real.pi * |(m : ℝ)| * (|(m : ℝ)| - A) ≤
        Real.pi * |(m : ℝ)| * (|(m : ℝ)| - |(n : ℝ)|) :=
      mul_le_mul_of_nonneg_left (by linarith [hS n hn]) (by positivity)
    exact hlocal.trans (mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_left (by positivity) (by positivity) hd) (norm_nonneg _))
  have hid : couplingColumn c S v m - couplingFirstJet c S v m =
      ∑ n ∈ S, (couplingColumn c {n} v m - couplingFirstJet c {n} v m) := by
    simp only [couplingColumn, couplingFirstJet, Finset.sum_singleton,
      Finset.sum_sub_distrib]
  rw [hid]
  calc
    _ ≤ ∑ n ∈ S, ‖couplingColumn c {n} v m - couplingFirstJet c {n} v m‖ :=
      norm_sum_le _ _
    _ ≤ ∑ n ∈ S, (2 * arithmeticBoundaryBudget c * |(n : ℝ)| /
        (Real.pi * |(m : ℝ)| * (|(m : ℝ)| - A))) * ‖v n‖ :=
      Finset.sum_le_sum hsingle
    _ = (2 * arithmeticBoundaryBudget c /
        (Real.pi * |(m : ℝ)| * (|(m : ℝ)| - A))) * weightedHeadMass S v := by
      rw [weightedHeadMass, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n _
      ring
    _ = _ := by ring

private theorem weighted_mass_nonneg (S : Finset ℤ) (v : ℤ → ℂ) :
    0 ≤ weightedHeadMass S v :=
  Finset.sum_nonneg (fun _ _ => mul_nonneg (abs_nonneg _) (norm_nonneg _))

private def remainderConstant (c M : ℕ) (A : ℝ) (S : Finset ℤ) (v : ℤ → ℂ) : ℝ :=
  2 * arithmeticBoundaryBudget c * weightedHeadMass S v * ((M : ℝ) + 1) /
    (Real.pi * ((M : ℝ) + 1 - A))

private theorem remainder_square_majorant {c M : ℕ} (hc : 2 ≤ c)
    (S : Finset ℤ) (v : ℤ → ℂ) {A : ℝ} (hA : 0 ≤ A)
    (hS : ∀ n ∈ S, |(n : ℝ)| ≤ A) (hsep : A < (M : ℝ) + 1)
    (j : ℕ) (m : ℤ) (hm : |(m : ℝ)| = ((M + j + 1 : ℕ) : ℝ)) :
    ‖couplingColumn c S v m - couplingFirstJet c S v m‖ ^ 2 ≤
      remainderConstant c M A S v ^ 2 / ((M + j + 1 : ℕ) : ℝ) ^ 4 := by
  let t : ℝ := ((M + j + 1 : ℕ) : ℝ)
  have ht : (M : ℝ) + 1 ≤ t := by
    dsimp [t]
    push_cast
    linarith [Nat.cast_nonneg (α := ℝ) j]
  have hgap : 0 < t - A := by linarith
  have hd : 0 < (M : ℝ) + 1 - A := sub_pos.mpr hsep
  have ht0 : 0 < t := by linarith
  have hB : 0 ≤ arithmeticBoundaryBudget c :=
    (abs_nonneg _).trans (arithmetic_boundary_symbol_bound hc 0).2
  have hW := weighted_mass_nonneg S v
  have herr := weighted_coupling_first_jet_error hc S v hA hS
    (m := m) (by rw [hm]; exact lt_of_lt_of_le hsep ht)
  rw [hm] at herr
  have hratio : t / (t - A) ≤ ((M : ℝ) + 1) / ((M : ℝ) + 1 - A) := by
    apply (div_le_div_iff₀ hgap hd).mpr
    nlinarith [mul_nonneg hA (sub_nonneg.mpr ht)]
  have hnorm : ‖couplingColumn c S v m - couplingFirstJet c S v m‖ ≤
      remainderConstant c M A S v / t ^ 2 := by
    calc
      _ ≤ 2 * arithmeticBoundaryBudget c * weightedHeadMass S v /
          (Real.pi * t * (t - A)) := herr
      _ = (2 * arithmeticBoundaryBudget c * weightedHeadMass S v / (Real.pi * t ^ 2)) *
          (t / (t - A)) := by
        field_simp [Real.pi_ne_zero, ht0.ne', hgap.ne']
        <;> ring
      _ ≤ (2 * arithmeticBoundaryBudget c * weightedHeadMass S v / (Real.pi * t ^ 2)) *
          (((M : ℝ) + 1) / ((M : ℝ) + 1 - A)) :=
        mul_le_mul_of_nonneg_left hratio (by positivity)
      _ = _ := by
        unfold remainderConstant
        field_simp [Real.pi_ne_zero, ht0.ne', hd.ne']
        <;> ring
  calc
    _ ≤ (remainderConstant c M A S v / t ^ 2) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    _ = _ := by dsimp [t]; simp only [div_pow, ← pow_mul]

private theorem remainder_budget_eq {c M : ℕ} {A : ℝ}
    (hM : 0 < M) (hsep : A < (M : ℝ) + 1) (S : Finset ℤ) (v : ℤ → ℂ) :
    2 * remainderConstant c M A S v ^ 2 / (3 * (M : ℝ) ^ 3) =
      pairedRemainderBudget c M A S v := by
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hd : (M : ℝ) + 1 - A ≠ 0 := (sub_pos.mpr hsep).ne'
  unfold remainderConstant pairedRemainderBudget
  field_simp [Real.pi_ne_zero, hMR.ne', hd]
  <;> ring

/-- Both signs of the actual weighted first-jet remainder, summed to infinity.
Every separated cutoff A<M+1 is admitted; M>0 pays the inverse-fourth tail. -/
theorem paired_first_jet_remainder_tail {c M : ℕ} (hc : 2 ≤ c) (hM : 0 < M)
    (S : Finset ℤ) (v : ℤ → ℂ) {A : ℝ} (hA : 0 ≤ A)
    (hS : ∀ n ∈ S, |(n : ℝ)| ≤ A) (hsep : A < (M : ℝ) + 1) :
    Summable (fun j : ℕ =>
      ‖couplingColumn c S v ((M + j + 1 : ℕ) : ℤ) -
        couplingFirstJet c S v ((M + j + 1 : ℕ) : ℤ)‖ ^ 2 +
      ‖couplingColumn c S v (-((M + j + 1 : ℕ) : ℤ)) -
        couplingFirstJet c S v (-((M + j + 1 : ℕ) : ℤ))‖ ^ 2) ∧
    (∑' j : ℕ,
      (‖couplingColumn c S v ((M + j + 1 : ℕ) : ℤ) -
        couplingFirstJet c S v ((M + j + 1 : ℕ) : ℤ)‖ ^ 2 +
        ‖couplingColumn c S v (-((M + j + 1 : ℕ) : ℤ)) -
          couplingFirstJet c S v (-((M + j + 1 : ℕ) : ℤ))‖ ^ 2)) ≤
      pairedRemainderBudget c M A S v := by
  let e : ℕ → ℝ := fun j =>
    ‖couplingColumn c S v ((M + j + 1 : ℕ) : ℤ) -
      couplingFirstJet c S v ((M + j + 1 : ℕ) : ℤ)‖ ^ 2 +
    ‖couplingColumn c S v (-((M + j + 1 : ℕ) : ℤ)) -
      couplingFirstJet c S v (-((M + j + 1 : ℕ) : ℤ))‖ ^ 2
  have he (j : ℕ) : e j ≤
      (2 * remainderConstant c M A S v ^ 2) *
        (1 / ((M : ℝ) + (j : ℝ) + 1) ^ 4) := by
    have hcast : (0 : ℝ) ≤ ((M + j + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    have hp := remainder_square_majorant hc S v hA hS hsep j
      ((M + j + 1 : ℕ) : ℤ) (by
        simpa only [Int.cast_natCast] using abs_of_nonneg hcast)
    have hn := remainder_square_majorant hc S v hA hS hsep j
      (-((M + j + 1 : ℕ) : ℤ)) (by
        simpa only [Int.cast_neg, abs_neg, Int.cast_natCast] using abs_of_nonneg hcast)
    calc
      e j ≤ remainderConstant c M A S v ^ 2 / ((M + j + 1 : ℕ) : ℝ) ^ 4 +
          remainderConstant c M A S v ^ 2 / ((M + j + 1 : ℕ) : ℝ) ^ 4 := add_le_add hp hn
      _ = _ := by push_cast; ring
  have hpartial (k : ℕ) : (∑ j ∈ Finset.range k, e j) ≤ pairedRemainderBudget c M A S v := by
    have hfourth := WeilEvenFourierObservationTail.inverse_fourth_partial_le hM k
    have hterminal : 0 ≤ 1 / (3 * ((M : ℝ) + (k : ℝ)) ^ 3) := by positivity
    have hfourth' : (∑ j ∈ Finset.range k, 1 / ((M : ℝ) + (j : ℝ) + 1) ^ 4) ≤
        1 / (3 * (M : ℝ) ^ 3) := by linarith
    calc
      _ ≤ ∑ j ∈ Finset.range k, (2 * remainderConstant c M A S v ^ 2) *
          (1 / ((M : ℝ) + (j : ℝ) + 1) ^ 4) := Finset.sum_le_sum (fun j _ => he j)
      _ = (2 * remainderConstant c M A S v ^ 2) *
          (∑ j ∈ Finset.range k, 1 / ((M : ℝ) + (j : ℝ) + 1) ^ 4) := (Finset.mul_sum _ _ _).symm
      _ ≤ (2 * remainderConstant c M A S v ^ 2) * (1 / (3 * (M : ℝ) ^ 3)) :=
        mul_le_mul_of_nonneg_left hfourth' (by positivity)
      _ = pairedRemainderBudget c M A S v := by
        simpa only [div_eq_mul_inv, one_mul] using remainder_budget_eq (c := c) hM hsep S v
  have hnon (j : ℕ) : 0 ≤ e j := add_nonneg (sq_nonneg _) (sq_nonneg _)
  exact ⟨summable_of_sum_range_le hnon hpartial,
    Real.tsum_le_of_sum_range_le hnon hpartial⟩

end D5.S3.Weil.ZetaBridge.ActualColumnRemainder
