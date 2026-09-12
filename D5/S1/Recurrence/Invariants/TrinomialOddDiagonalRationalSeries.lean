/- GID: D5/S1/Recurrence/Invariants/TrinomialOddDiagonalRationalSeries
   generality: G
   mirror-B: D5/B/S1/Recurrence/Invariants/TrinomialOddDiagonalRationalSeries
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [Mathlib.RingTheory.PowerSeries.Expand, Mathlib.RingTheory.PowerSeries.Inverse, Mathlib.RingTheory.PowerSeries.WellKnown, Mathlib.Tactic.LinearCombination, Mathlib.Tactic.Ring]
   utility: none
   digest: Odd trinomial diagonals have Schulte's rational generating series. -/

import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S1.Recurrence.Invariants.TrinomialOddDiagonalRationalSeries

open Finset

/-- The `r`-th coefficient in row `m` of OEIS A027907. -/
def trinomial (m r : Nat) : Rat :=
  Polynomial.coeff ((1 + Polynomial.X + Polynomial.X ^ 2) ^ m) r

/-- Werner Schulte's odd diagonal sum in the trinomial triangle. -/
def diagonal (n : Nat) : Rat :=
  ∑ j ∈ range (n / 2 + 1), trinomial (n + 1 - j) (2 * j + 1)

/-- The rational generating function defining OEIS A077864. -/
def generatingSeries : PowerSeries Rat :=
  ((1 - PowerSeries.X) *
    (1 - PowerSeries.X - 2 * PowerSeries.X ^ 2 - PowerSeries.X ^ 3))⁻¹

/-- The `n`-th coefficient of OEIS A077864. -/
def a (n : Nat) : Rat :=
  PowerSeries.coeff n generatingSeries

open PowerSeries

/-- The Schulte diagonal is an odd coefficient of a geometric power series. -/
theorem odd_trinomial_diagonal_coeff (n : Nat) :
    coeff (2 * n + 3)
        ((1 - X ^ 2 * (1 + X + X ^ 2 : PowerSeries Rat))⁻¹) =
      ∑ j ∈ range (n / 2 + 1), trinomial (n + 1 - j) (2 * j + 1) := by
  let p : Polynomial Rat := 1 + Polynomial.X + Polynomial.X ^ 2
  let u : PowerSeries Rat := X ^ 2 * (p : PowerSeries Rat)
  let G : PowerSeries Rat := (1 - u)⁻¹
  have hu0 : constantCoeff u = 0 := by simp [u]
  have hu : HasSubst u := .of_constantCoeff_zero hu0
  have hgeom : G = (PowerSeries.mk 1 : PowerSeries Rat).subst u := by
    symm
    apply (eq_inv_iff_mul_eq_one (by simp [u])).mpr
    have h := congrArg (substAlgHom hu) (mk_one_mul_one_sub_eq_one Rat)
    rw [← coe_substAlgHom hu]
    simpa only [map_mul, map_sub, map_one, substAlgHom_X hu] using h
  have hcoeff_u (m k : Nat) :
      coeff k (u ^ m) =
        if 2 * m ≤ k then Polynomial.coeff (p ^ m) (k - 2 * m) else 0 := by
    change coeff k ((X ^ 2 * (p : PowerSeries Rat)) ^ m) = _
    rw [mul_pow, ← pow_mul, coeff_X_pow_mul']
    split_ifs with h
    · simpa using (Polynomial.coeff_coe (p ^ m) (k - 2 * m))
    · rfl
  have hcut :
      coeff (2 * n + 3) G = ∑ m ∈ range (n + 2), coeff (2 * n + 3) (u ^ m) := by
    rw [hgeom, coeff_subst' hu]
    simp only [coeff_mk, Pi.one_apply, one_smul]
    rw [finsum_eq_sum_of_support_subset _ (s := range (n + 2))]
    intro m hm
    by_contra hmem
    have hmn : n + 2 ≤ m := by simpa using hmem
    apply hm
    change coeff (2 * n + 3) (u ^ m) = 0
    rw [hcoeff_u, if_neg (by omega)]
  have hterms (j : Nat) (hj : j < n + 2) :
      coeff (2 * n + 3) (u ^ (n + 1 - j)) =
        trinomial (n + 1 - j) (2 * j + 1) := by
    rw [hcoeff_u, if_pos (by omega)]
    congr 1
    omega
  have hG : G = (1 - X ^ 2 * (1 + X + X ^ 2 : PowerSeries Rat))⁻¹ := by
    simp [G, u, p]
  rw [← hG]
  calc
    coeff (2 * n + 3) G =
        ∑ m ∈ range (n + 2), coeff (2 * n + 3) (u ^ m) := hcut
    _ = ∑ j ∈ range (n + 2), coeff (2 * n + 3) (u ^ (n + 1 - j)) :=
      (sum_range_reflect (fun m => coeff (2 * n + 3) (u ^ m)) (n + 2)).symm
    _ = ∑ j ∈ range (n + 2), trinomial (n + 1 - j) (2 * j + 1) := by
      apply sum_congr rfl
      intro j hj
      exact hterms j (by simpa using hj)
    _ = ∑ j ∈ range (n / 2 + 1), trinomial (n + 1 - j) (2 * j + 1) := by
      apply (sum_subset (by
        intro j hj
        simp only [mem_range] at hj ⊢
        omega) ?_).symm
      intro j hjwide hjshort
      have hj : n / 2 + 1 ≤ j := by simpa using hjshort
      apply Polynomial.coeff_eq_zero_of_natDegree_lt
      calc
        (p ^ (n + 1 - j)).natDegree ≤ (n + 1 - j) * 2 :=
          Polynomial.natDegree_pow_le_of_le _ (by
            dsimp only [p]
            refine (Polynomial.natDegree_add_le _ _).trans ?_
            apply max_le
            · refine (Polynomial.natDegree_add_le _ _).trans ?_
              simp
            · simp)
        _ < 2 * j + 1 := by omega

/-- Werner Schulte's 2015 conjecture on OEIS A077864. -/
theorem schulte_a077864 (n : Nat) :
    a n = ∑ j ∈ range (n / 2 + 1), trinomial (n + 1 - j) (2 * j + 1) := by
  let minus : PowerSeries Rat := 1 - X ^ 2 - X ^ 3 - X ^ 4
  let plus : PowerSeries Rat := 1 - X ^ 2 + X ^ 3 - X ^ 4
  let G : PowerSeries Rat := minus⁻¹
  let reflected : PowerSeries Rat := rescale (-1) G
  let expanded : PowerSeries Rat := expand 2 (by decide) generatingSeries
  have hminus : G * minus = 1 := by
    exact PowerSeries.inv_mul_cancel minus (by simp [minus])
  have hplus : reflected * plus = 1 := by
    have h := congrArg (rescale (-1 : Rat)) hminus
    have hreflect : rescale (-1 : Rat) minus = plus := by
      dsimp only [minus, plus]
      simp only [map_sub, map_one, map_pow, rescale_neg_one_X]
      ring
    simpa only [map_mul, map_one, reflected, hreflect] using h
  have hexpanded : expanded * (minus * plus) = 1 := by
    have h := congrArg (expand 2 (by decide : 2 ≠ 0) (R := Rat))
      (PowerSeries.inv_mul_cancel
        ((1 - X) * (1 - X - 2 * X ^ 2 - X ^ 3) : PowerSeries Rat) (by simp))
    simp only [map_mul, map_sub, map_one, map_ofNat, map_pow, expand_X] at h
    change expanded * (minus * plus) = 1
    rw [show expanded = expand 2 (by decide) generatingSeries by rfl]
    rw [show generatingSeries =
        ((1 - X) * (1 - X - 2 * X ^ 2 - X ^ 3) : PowerSeries Rat)⁻¹ by
      rfl]
    convert h using 1
    all_goals
      dsimp only [minus, plus]
      ring
  have hproduct : (G * reflected) * (minus * plus) = 1 := by
    calc
      (G * reflected) * (minus * plus) = (G * minus) * (reflected * plus) := by ring
      _ = 1 := by rw [hminus, hplus, one_mul]
  have hdenom : minus * plus ≠ 0 := by
    intro hzero
    have h := congrArg constantCoeff hzero
    norm_num [minus, plus] at h
  have heq : expanded = G * reflected := by
    apply mul_right_cancel₀ hdenom
    exact hexpanded.trans hproduct.symm
  have hodd : 2 * X ^ 3 * expanded = G - reflected := by
    calc
      2 * X ^ 3 * expanded = 2 * X ^ 3 * (G * reflected) := by rw [heq]
      _ = G * (reflected * plus) - (G * minus) * reflected := by
        dsimp only [minus, plus]
        ring
      _ = G - reflected := by rw [hminus, hplus, mul_one, one_mul]
  have hcoeff := congrArg (coeff (2 * n + 3)) hodd
  dsimp only [reflected] at hcoeff
  rw [show 2 * X ^ 3 * expanded = X ^ 3 * (PowerSeries.C 2 * expanded) by
    simp only [map_ofNat]; ring] at hcoeff
  simp only [coeff_X_pow_mul', if_pos (by omega : 3 ≤ 2 * n + 3),
    coeff_C_mul, map_sub, coeff_rescale] at hcoeff
  have hindex : 2 * n + 3 - 3 = 2 * n := by omega
  rw [hindex] at hcoeff
  dsimp only [expanded] at hcoeff
  rw [coeff_expand_mul] at hcoeff
  have hsign : (-1 : Rat) ^ (2 * n + 3) = -1 := by
    rw [show 2 * n + 3 = 2 * (n + 1) + 1 by omega, pow_add, pow_mul]
    norm_num
  rw [hsign] at hcoeff
  have haG : a n = coeff (2 * n + 3) G := by
    dsimp only [a]
    linear_combination hcoeff / 2
  have hGform :
      G = (1 - X ^ 2 * (1 + X + X ^ 2 : PowerSeries Rat))⁻¹ := by
    dsimp only [G, minus]
    congr 1
    ring
  rw [hGform] at haG
  exact haG.trans (odd_trinomial_diagonal_coeff n)

#print axioms odd_trinomial_diagonal_coeff
#print axioms schulte_a077864

end D5.S1.Recurrence.Invariants.TrinomialOddDiagonalRationalSeries
