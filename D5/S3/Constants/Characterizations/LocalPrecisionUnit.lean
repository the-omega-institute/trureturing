/- GID: D5/S3/Constants/Characterizations/LocalPrecisionUnit
   generality: G
   mirror-B: D5/B/S3/Constants/Characterizations/LocalPrecisionUnit
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The normalized p-adic precision equation has log p as its unique real solution. -/

import Mathlib

/- Library-search audit trail (2026-08-28):
   * Repository searches found no declaration combining the normalized p-adic equation, its
     named unique real solution, and the associated complex-power identity.
   * Pinned mathlib's definition was opened and checked: `Padic.norm_p` states exactly
     `‖(p : ℚ_[p])‖ = (p : ℝ)⁻¹`, so its normalization agrees with the source convention.
   * The proof directly reuses `Padic.norm_p`, `Real.exp_injective`, and
     `Complex.cpow_def_of_ne_zero`; Loogle found the first as the exact normalization hit but
     no full uniqueness theorem. LeanSearch and Reservoir API attempts returned HTTP 404,
     while authenticated GitHub code search found only mathlib copies of the same primitive. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Constants.Characterizations.LocalPrecisionUnit

/-- For a prime `p`, `Real.log p` satisfies the normalized p-adic precision equation and is
its unique real solution. The same logarithmic unit expresses every complex prime weight
`p ^ (-s)` as an exponential. -/
theorem local_precision_unit_unique (p : ℕ) [hp : Fact p.Prime] :
    ((Real.exp (-Real.log (p : ℝ)) = ‖(p : ℚ_[p])‖ ∧
          ‖(p : ℚ_[p])‖ = (p : ℝ)⁻¹) ∧
        ∀ ell : ℝ,
          (Real.exp (-ell) = ‖(p : ℚ_[p])‖ ∧
              ‖(p : ℚ_[p])‖ = (p : ℝ)⁻¹) →
            ell = Real.log (p : ℝ)) ∧
      ∀ s : ℂ,
        (p : ℂ) ^ (-s) =
          Complex.exp (-s * (Real.log (p : ℝ) : ℂ)) := by
  have hpReal : 0 < (p : ℝ) := by
    exact_mod_cast hp.out.pos
  constructor
  · constructor
    · constructor
      · rw [Padic.norm_p, Real.exp_neg, Real.exp_log hpReal]
      · exact Padic.norm_p
    · intro ell hell
      apply neg_injective
      apply Real.exp_injective
      calc
        Real.exp (-ell) = ‖(p : ℚ_[p])‖ := hell.1
        _ = (p : ℝ)⁻¹ := hell.2
        _ = Real.exp (-Real.log (p : ℝ)) := by
          rw [Real.exp_neg, Real.exp_log hpReal]
  · intro s
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hp.out.ne_zero)]
    rw [← Complex.natCast_log]
    congr 1
    ring

/-- Reverse probe: the two public uniqueness conjuncts recover an `ExistsUnique` statement
whose witness is the named logarithmic unit. -/
example (p : ℕ) [Fact p.Prime] :
    ∃! ell : ℝ,
      Real.exp (-ell) = ‖(p : ℚ_[p])‖ ∧
        ‖(p : ℚ_[p])‖ = (p : ℝ)⁻¹ := by
  have h := local_precision_unit_unique p
  exact ⟨Real.log (p : ℝ), h.1.1, h.1.2⟩

/-- Trivialization probe: zero cannot solve the normalized equation for a prime channel. -/
example (p : ℕ) [Fact p.Prime] :
    ¬ (Real.exp (-(0 : ℝ)) = ‖(p : ℚ_[p])‖ ∧
      ‖(p : ℚ_[p])‖ = (p : ℝ)⁻¹) := by
  rintro ⟨hzero, _⟩
  have hone : (1 : ℝ) = ‖(p : ℚ_[p])‖ := by
    simpa using hzero
  have hlt : ‖(p : ℚ_[p])‖ < (1 : ℝ) := Padic.norm_p_lt_one
  linarith

/-- The other trivial base is excluded by the public prime-index type. -/
example : ¬ ∃ _h : Fact (Nat.Prime 1), True := by
  rintro ⟨h, _⟩
  exact Nat.not_prime_one h.out

#print axioms local_precision_unit_unique

end D5.S3.Constants.Characterizations.LocalPrecisionUnit
