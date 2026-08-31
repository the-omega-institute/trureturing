/- GID: D5/S3/PrimeForms/QuadraticCharacterSeparation
   generality: G
   mirror-B: D5/B/S3/PrimeForms/QuadraticCharacterSeparation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Distinct quadratic sign characters separate exactly where their product is minus one. -/

import Mathlib

/- Library-search audit trail (2026-09-01):
   * The atom ledger is still residual-open with no coverage or formalization receipt.
   * Repository searches found nearby quadratic-character profile redundancy,
     quadratic-observer kernel bounds, finite conjugacy-class rates, and prime
     counting-density examples; none states the pointwise product separation
     criterion for two distinct quadratic characters.
   * Pinned Mathlib supplies finite-unit arithmetic for `(ZMod 3)ˣ`, but no
     Chebotarev theorem or natural/Dirichlet prime-density API.  This module
     therefore formalizes the algebraic character-separation clause only; the
     source's analytic density transfer remains an explicit external obligation.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.PrimeForms.QuadraticCharacterSeparation

private abbrev Sign := (ZMod 3)ˣ

private theorem sign_separation_iff (a b : Sign) :
    a ≠ b ↔ a * b = (-1 : Sign) := by
  revert a b
  decide

private theorem sign_product_eq_one_iff (a b : Sign) :
    a * b = 1 ↔ a = b := by
  constructor
  · intro h
    by_contra hab
    have hminus : a * b = (-1 : Sign) :=
      (sign_separation_iff a b).mp hab
    have hneg : (-1 : Sign) ≠ 1 := by decide
    exact hneg (hminus.symm.trans h)
  · rintro rfl
    have hsq : ∀ x : Sign, x * x = 1 := by
      intro x
      revert x
      decide
    exact hsq a

/-- Distinct quadratic sign characters have a nontrivial product, and their
values differ exactly when that product takes the value `-1`. -/
theorem quadratic_character_separation
    {G : Type*} [Group G]
    (χ₁ χ₂ : G →* Sign) (hχ : χ₁ ≠ χ₂) :
    let χ := χ₁ * χ₂
    χ ≠ 1 ∧ ∀ g : G, χ₁ g ≠ χ₂ g ↔ χ g = (-1 : Sign) := by
  let χ : G →* Sign := χ₁ * χ₂
  have hnontrivial : χ ≠ 1 := by
    intro hχone
    apply hχ
    apply MonoidHom.ext
    intro g
    have hprod : χ₁ g * χ₂ g = 1 := by
      change χ g = 1
      rw [hχone]
      rfl
    exact (sign_product_eq_one_iff (χ₁ g) (χ₂ g)).mp hprod
  refine ⟨?_, ?_⟩
  · exact hnontrivial
  · intro g
    exact sign_separation_iff (χ₁ g) (χ₂ g)

#print axioms quadratic_character_separation

end D5.S3.PrimeForms.QuadraticCharacterSeparation
