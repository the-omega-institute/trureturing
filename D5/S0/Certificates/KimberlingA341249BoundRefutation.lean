/- GID: D5/S0/Certificates/KimberlingA341249BoundRefutation
   generality: I
   mirror-B: D5/B/S0/Certificates/KimberlingA341249BoundRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S0/Certificates/KimberlingA341249BoundRefutation.claim; result=D5/S0/Certificates/KimberlingA341249BoundRefutation.result; claim=D5/S0/Certificates/KimberlingA341249BoundRefutation.claim
   digest: The n=2 term refutes the OEIS A341249 upper bound 2. -/

/-
result:
  proof_shape: bind-only (root-two bounds, floor intervals, and normalization).
  escape_witness: none.
  admission_basis: open-problem-resolution (#18673; Refuted).
  Direct frozen dependencies: none (pinned Mathlib only).
The public result is the designated refutation result (`basis=refutes`) and is
exempt from four-slot escape registration (CLAUDE.md §3.9).
-/

import Mathlib.Analysis.Real.Sqrt

/-! The positive-index strict bound in OEIS A341249 fails at the second term. -/

set_option autoImplicit false

namespace D5.S0.Certificates.KimberlingA341249BoundRefutation

/-- The real constant `r = 2 + sqrt(2)` in OEIS A341249. -/
noncomputable def r : ℝ := 2 + Real.sqrt 2

/-- The real constant `s = sqrt(2)` in OEIS A341249. -/
noncomputable def s : ℝ := Real.sqrt 2

/-- OEIS A341249: `a(n) = floor(r*floor(s*n))`. -/
noncomputable def a (n : ℕ) : ℤ := ⌊r * (⌊s * n⌋ : ℝ)⌋

/-- OEIS A341249: "Conjecture:  1 < r*s*n - a(n) < 2 for n >= 1." -/
def claim : Prop := ∀ n : ℕ, 1 ≤ n → 1 < r * s * n - a n ∧ r * s * n - a n < 2

/-- At `n = 2`, the difference is `4 * sqrt(2) - 2 > 2`. -/
theorem result : ¬ claim := by
  intro h
  have hslo : 1 < Real.sqrt 2 := Real.one_lt_sqrt_two
  have hshi : Real.sqrt 2 < 3 / 2 := Real.sqrt_two_lt_three_halves
  have hinner : ⌊s * (2 : ℕ)⌋ = (2 : ℤ) := by
    apply Int.floor_eq_iff.mpr
    dsimp [s]
    constructor <;> norm_num
    linarith
  have ha : a 2 = 6 := by
    unfold a
    rw [hinner]
    apply Int.floor_eq_iff.mpr
    dsimp [r]
    constructor <;> norm_num <;> linarith
  have hsquare : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hvalue : r * s * (2 : ℕ) - a 2 = 4 * Real.sqrt 2 - 2 := by
    rw [ha]
    dsimp [r, s]
    norm_num
    nlinarith [hsquare]
  have hh := (h 2 (by norm_num)).2
  rw [hvalue] at hh
  linarith

end D5.S0.Certificates.KimberlingA341249BoundRefutation
