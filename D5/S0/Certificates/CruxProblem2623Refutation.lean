/- GID: D5/S0/Certificates/CruxProblem2623Refutation
   generality: I
   mirror-B: D5/B/S0/Certificates/CruxProblem2623Refutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S0/Certificates/CruxProblem2623Refutation.claim; result=D5/S0/Certificates/CruxProblem2623Refutation.result; claim=D5/S0/Certificates/CruxProblem2623Refutation.claim
   digest: Crux Problem 2623 fails for cyclic data (1, 2, 1, 2) at n = 4 and k = 1. -/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Certificates.CruxProblem2623Refutation

/-!
Crux Problem 2623 asks whether a cyclic ratio sum decreases with the length of
its consecutive blocks. The four-cycle `(1, 2, 1, 2)` refutes the assertion at
the interior index `k = 1`.
-/

/-- The cyclic ratio sum printed in Crux Problem 2623. -/
noncomputable def S {n : ℕ} [NeZero n] (x : ZMod n → ℝ) (k : ℕ) : ℝ :=
  ∑ j : ZMod n,
    (∑ i ∈ Finset.range (k + 1), x (j + (i : ZMod n))) /
      (∑ i ∈ Finset.range (k + 1), x (j + ((i + 1 : ℕ) : ZMod n)))

/-- The universal monotonicity assertion posed in Crux Problem 2623. -/
def claim : Prop :=
  ∀ (n : ℕ) (hn : 2 ≤ n),
    letI : NeZero n := ⟨by omega⟩
    ∀ (x : ZMod n → ℝ),
      (∀ j, 0 < x j) →
      ∀ k : ℕ, k + 2 ≤ n → S x (k + 1) ≤ S x k

/-- The assertion fails for `n = 4`, `k = 1`, and cyclic data `(1, 2, 1, 2)`. -/
theorem result : ¬ claim := by
  intro hclaim
  let x : ZMod 4 → ℝ := fun j => if j = 0 ∨ j = 2 then 1 else 2
  have hx : ∀ j, 0 < x j := by
    intro j
    simp only [x]
    split <;> norm_num
  have h := hclaim 4 (by norm_num) x hx 1 (by norm_num)
  simp only [S] at h
  let e : Fin 4 ≃ ZMod 4 := Equiv.refl _
  rw [← Equiv.sum_comp e] at h
  rw [← Equiv.sum_comp e] at h
  have he (j : Fin 4) : e j = j := rfl
  simp_rw [he] at h
  simp only [Fin.sum_univ_four, Finset.sum_range_succ] at h
  simp +decide only [x] at h
  norm_num at h

end D5.S0.Certificates.CruxProblem2623Refutation
