/- GID: D5/S3/Combinatorics/CylindricPartition/LiUncuGaussian
   generality: G
   mirror-B: D5/B/S3/Combinatorics/CylindricPartition/LiUncuGaussian
   mirror-E: none(waiver:gaussian-polynomial-induction)
   anchors: [mathlib/module/Mathlib.Tactic]
   utility: none
   digest: Inductive Gaussian identities for the finite cylindric partition formula. -/

import D5.S3.Combinatorics.CylindricPartition.LiUncuDefs
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.CylindricPartition.LiUncu

open Polynomial LiUncuDefs

/-- The q-Pascal recursion has no support above the upper index. -/
theorem gauss_zero_of_lt (a b : ℕ) (hab : a < b) : gauss a b = 0 := by
  induction a generalizing b with
  | zero =>
      cases b with
      | zero => omega
      | succ b => simp [gauss]
  | succ a ih =>
      cases b with
      | zero => omega
      | succ b =>
          rw [gauss, ih (b + 1) (by omega), ih b (by omega)]
          simp

/-- The second q-Pascal recursion follows by induction, including the support edges. -/
theorem gauss_pascal_dual (a b : ℕ) :
    gauss (a + 1) (b + 1) = X ^ (b + 1) * gauss a (b + 1) + gauss a b := by
  have diagonal (a : ℕ) : gauss a a = 1 := by
    induction a with
    | zero => rfl
    | succ a ih =>
        rw [gauss, gauss_zero_of_lt a (a + 1) (by omega), Nat.sub_self]
        simpa using ih
  have column (a : ℕ) : gauss (a + 1) 1 = X * gauss a 1 + 1 := by
    induction a with
    | zero => simp [gauss]
    | succ a ih =>
        have hrec : gauss (a + 1) 1 = gauss a 1 + X ^ a := by simp [gauss]
        calc
          gauss (a + 2) 1 = gauss (a + 1) 1 + X ^ (a + 1) := by simp [gauss]
          _ = X * gauss a 1 + 1 + X ^ (a + 1) := by rw [ih]
          _ = X * (gauss a 1 + X ^ a) + 1 := by rw [pow_succ]; ring
          _ = X * gauss (a + 1) 1 + 1 := by rw [← hrec]
  induction a generalizing b with
  | zero =>
      cases b with
      | zero => simp [gauss]
      | succ b => simp [gauss]
  | succ a ih =>
      cases b with
      | zero => simpa [gauss] using column (a + 1)
      | succ b =>
          by_cases hb : b + 1 ≤ a
          · have powers :
                (X : ℤ[X]) ^ (a - b) * X ^ (b + 1) =
                  X ^ (b + 2) * X ^ (a - (b + 1)) := by
              rw [← pow_add, ← pow_add]
              congr 1
              omega
            calc
              gauss (a + 2) (b + 2) =
                  gauss (a + 1) (b + 2) +
                    X ^ (a - b) * gauss (a + 1) (b + 1) := by
                    rw [gauss, show a + 1 - (b + 1) = a - b by omega]
              _ = X ^ (b + 2) * gauss a (b + 2) + gauss a (b + 1) +
                  X ^ (a - b) * (X ^ (b + 1) * gauss a (b + 1) + gauss a b) := by
                    rw [ih (b + 1), ih b]
              _ = X ^ (b + 2) *
                  (gauss a (b + 2) + X ^ (a - (b + 1)) * gauss a (b + 1)) +
                    (gauss a (b + 1) + X ^ (a - b) * gauss a b) := by
                    rw [mul_add, ← mul_assoc, powers]
                    ring
              _ = X ^ (b + 2) * gauss (a + 1) (b + 2) +
                    gauss (a + 1) (b + 1) := by rw [gauss, gauss]
          · by_cases he : b = a
            · subst b
              rw [diagonal, gauss_zero_of_lt (a + 1) (a + 2) (by omega), diagonal]
              simp
            · rw [gauss_zero_of_lt (a + 2) (b + 2) (by omega),
                  gauss_zero_of_lt (a + 1) (b + 2) (by omega),
                  gauss_zero_of_lt (a + 1) (b + 1) (by omega)]
              simp

/-- Complementing the lower index preserves the Gaussian polynomial. -/
theorem gauss_symmetry (a b : ℕ) (hab : b ≤ a) : gauss a b = gauss a (a - b) := by
  have diagonal (a : ℕ) : gauss a a = 1 := by
    induction a with
    | zero => rfl
    | succ a ih =>
        rw [gauss, gauss_zero_of_lt a (a + 1) (by omega), Nat.sub_self]
        simpa using ih
  induction a generalizing b with
  | zero =>
      have hb : b = 0 := by omega
      subst b
      rfl
  | succ a ih =>
      cases b with
      | zero => simpa [gauss] using (diagonal (a + 1)).symm
      | succ b =>
          by_cases hb : b = a
          · subst b
            simpa [gauss] using diagonal (a + 1)
          · have hba : b + 1 ≤ a := by omega
            have he : a - b = (a - (b + 1)) + 1 := by omega
            rw [gauss, ih (b + 1) hba, ih b (by omega)]
            rw [show a + 1 - (b + 1) = a - b by omega]
            conv_rhs => rw [he, gauss_pascal_dual]
            rw [← he]
            ring

/-- Removing a rim from a Gaussian rectangle gives its polynomial hook identity. -/
theorem gauss_hook (a b : ℕ) (hab : b ≤ a) :
    (1 - X ^ (a - b)) * gauss a b = (1 - X ^ a) * gauss (a - 1) b := by
  induction a generalizing b with
  | zero => simp
  | succ a ih =>
      cases b with
      | zero => simp [gauss]
      | succ b =>
          by_cases hb : b = a
          · subst b
            rw [Nat.sub_self, pow_zero, sub_self, zero_mul,
              show a + 1 - 1 = a by omega, gauss_zero_of_lt a (a + 1) (by omega)]
            simp
          · have hba : b + 1 ≤ a := by omega
            have ha : 1 ≤ a := by omega
            have relation :
                (1 - X ^ (a - b)) * gauss a b =
                  (1 - X ^ (b + 1)) * gauss a (b + 1) := by
              rw [ih b (by omega)]
              have hc := ih (a - (b + 1)) (by omega)
              rw [show a - (a - (b + 1)) = b + 1 by omega,
                gauss_symmetry a (a - (b + 1)) (by omega),
                gauss_symmetry (a - 1) (a - (b + 1)) (by omega),
                show a - 1 - (a - (b + 1)) = b by omega,
                show a - (a - (b + 1)) = b + 1 by omega] at hc
              exact hc.symm
            rw [show a + 1 - (b + 1) = a - b by omega,
              show a + 1 - 1 = a by omega, gauss]
            have hp : (X : ℤ[X]) ^ (a - b) * X ^ (b + 1) = X ^ (a + 1) := by
              rw [← pow_add]
              congr 1
              omega
            calc
              _ = (1 - X ^ (a - b)) * gauss a (b + 1) +
                  X ^ (a - b) * ((1 - X ^ (a - b)) * gauss a b) := by ring
              _ = (1 - X ^ (a - b)) * gauss a (b + 1) +
                  X ^ (a - b) * ((1 - X ^ (b + 1)) * gauss a (b + 1)) := by
                    rw [relation]
              _ = (1 - X ^ (a - b) * X ^ (b + 1)) * gauss a (b + 1) := by ring
              _ = _ := by rw [hp]

end D5.S3.Combinatorics.CylindricPartition.LiUncu
