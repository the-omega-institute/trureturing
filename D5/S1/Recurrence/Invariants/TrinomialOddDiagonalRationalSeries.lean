/- GID: D5/S1/Recurrence/Invariants/TrinomialOddDiagonalRationalSeries
   generality: G
   mirror-B: D5/B/S1/Recurrence/Invariants/TrinomialOddDiagonalRationalSeries
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [Mathlib.RingTheory.PowerSeries.Expand, Mathlib.RingTheory.PowerSeries.Inverse, Mathlib.RingTheory.PowerSeries.WellKnown, Mathlib.Tactic.LinearCombination]
   utility: none
   digest: Odd trinomial diagonals have Schulte's rational generating series. -/

import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.Tactic.LinearCombination

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

example (n : Nat) :
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

end D5.S1.Recurrence.Invariants.TrinomialOddDiagonalRationalSeries
