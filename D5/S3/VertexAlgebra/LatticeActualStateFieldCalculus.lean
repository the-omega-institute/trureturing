/- GID: D5/S3/VertexAlgebra/LatticeActualStateFieldCalculus
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeActualStateFieldCalculus
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual Borcherds and residue identities give mode commutators and normal state products. -/

import D5.S3.VertexAlgebra.LatticeActualVertexAlgebra

/-
Actual lattice mode calculus, derived from the saved all-integer Borcherds
proof and residue reconstruction, with no compatibility assumptions.

The actual construction is attributed to Bakalov--Kac, math/0402315v1,
section 4.1, equations (4.12)--(4.16), DOI 10.1142/9789812702562_0001.
The imported residue and Jacobi sources retain their Apache 2.0 copyright
and Carnahan / Matsuo--Nagatomo attribution. This is a native checkpoint,
not an official acceptance or completion of the persistent research goal.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

namespace D5.S3.VertexAlgebra.LatticeActualStateFieldCalculus
open LatticeGeneratingFieldLocality LatticeAllStateField
open LatticeAllStateReconstruction LatticeAllStateJacobi FieldNormalProduct
open StateFieldResidueReconstruction (integerBinomial)
open scoped BigOperators VertexOperator
noncomputable section

/-- Truncation of the actual field gives finite support before any binomial
factor is introduced. This also works for negative upper binomial indices. -/
theorem nonnegative_products_finite (D : LatticeData) (a b : Carrier D) :
    Function.HasFiniteSupport (fun j : ℕ => mu D a j b) := by
  classical
  refine BddAbove.finite (bddAbove_def.mpr ?_)
  refine ⟨(-((HahnModule.of ℂ).symm (Y D a b)).order - 1).toNat, ?_⟩
  intro j member
  contrapose! member
  have vanish : mu D a j b = 0 := by
    apply VertexOperator.ncoeff_eq_zero_of_lt_order
    omega
  simp only [Function.mem_support, vanish, ne_eq, not_true_eq_false, not_false_eq_true]

def commutatorTerm (D : LatticeData) (a b : Carrier D) (p q : ℤ) (j : ℕ) :
    Module.End ℂ (Carrier D) :=
  integerBinomial p j • ((Y D (mu D a j b))[[p + q - j]])

theorem commutator_terms_finite (D : LatticeData) (a b : Carrier D) (p q : ℤ) :
    Function.HasFiniteSupport (commutatorTerm D a b p q) := by
  classical
  apply (nonnegative_products_finite D a b).subset
  intro j member
  contrapose! member
  have zeroState : mu D a j b = 0 := by
    simpa only [Function.mem_support, not_not] using member
  simp [commutatorTerm, zeroState]

/-- Full integer commutator extraction from genuine actual Borcherds. -/
theorem mode_commutator (D : LatticeData) (a b : Carrier D) (p q : ℤ) :
    ((Y D a)[[p]]) * ((Y D b)[[q]]) -
        ((Y D b)[[q]]) * ((Y D a)[[p]]) =
      ∑ᶠ j : ℕ, commutatorTerm D a b p q j := by
  classical
  apply LinearMap.ext
  intro c
  have h := (borcherds D a b c p q 0).2.2.2
  have right : (∑ᶠ j : ℕ,
      (((-1 : ℂ)^j) * integerBinomial 0 j) •
        (mu D a (p + 0 - j) (mu D b (q + j) c) -
          StateFieldResidueReconstruction.epsilon 0 •
            mu D b (q + 0 - j) (mu D a (p + j) c))) =
      mu D a p (mu D b q c) - mu D b q (mu D a p c) := by
    rw [finsum_eq_single _ 0]
    · simp [integerBinomial, StateFieldResidueReconstruction.epsilon]
    · intro j different
      simp [integerBinomial, Ring.choose_zero_pos ℤ (Nat.pos_of_ne_zero different)]
  rw [right] at h
  have evaluation : (∑ᶠ j : ℕ, commutatorTerm D a b p q j) c =
      ∑ᶠ j : ℕ, jacobiLeftTerm D p q 0 a b c j := by
    change (LinearMap.applyₗ c) (∑ᶠ j : ℕ, commutatorTerm D a b p q j) = _
    rw [map_finsum (LinearMap.applyₗ c) (commutator_terms_finite D a b p q)]
    apply finsum_congr
    intro j
    simp only [commutatorTerm, jacobiLeftTerm, mu, zero_add,
      LinearMap.applyₗ_apply_apply, LinearMap.smul_apply]
  rw [evaluation]
  exact h.symm

theorem one_mode_commutator (D : LatticeData) (a b : Carrier D) (q : ℤ) :
    ((Y D a)[[1]]) * ((Y D b)[[q]]) -
        ((Y D b)[[q]]) * ((Y D a)[[1]]) =
      ((Y D (mu D a 0 b))[[q + 1]]) +
        ((Y D (mu D a 1 b))[[q]]) := by
  rw [mode_commutator]
  have finite : (∑ᶠ j : ℕ, commutatorTerm D a b 1 q j) =
      ∑ j ∈ Finset.range 2, commutatorTerm D a b 1 q j := by
    apply finsum_eq_sum_of_support_subset
    intro j member
    by_contra outside
    have vanish : (1 : ℕ).choose j = 0 := Nat.choose_eq_zero_of_lt (by simpa using outside)
    have choose : Ring.choose (1 : ℤ) j = 0 := by
      change Ring.choose ((1 : ℕ) : ℤ) j = 0
      rw [Ring.choose_natCast, vanish]
      rfl
    exact member (by simp [commutatorTerm, integerBinomial, choose])
  rw [finite]
  simp [Finset.sum_range_succ, commutatorTerm, integerBinomial,
    Ring.choose_one_right, add_comm q 1]

theorem minus_one_binomial (j : ℕ) :
    (-1 : ℂ)^j * integerBinomial (-1) j = 1 := by
  have choose : integerBinomial (-1) j = (-1 : ℂ)^j := by
    unfold integerBinomial
    rw [Ring.choose_neg', Ring.multichoose_one]
    simp [Units.smul_def, Int.cast_negOnePow_natCast]
  rw [choose, ← pow_add, ← two_mul, pow_mul]
  norm_num

/-- Actual state product / normal field compatibility is a theorem, obtained
from the proved residue iterate at -1; it is never a premise of this file. -/
theorem minus_one_product_field (D : LatticeData) (a b : Carrier D) :
    Y D (mu D a (-1) b) = (normalMinusOne (Y D a) (Y D b)).1 := by
  apply HVertexOperator.coeff_inj
  funext power
  apply LinearMap.ext
  intro c
  rw [VertexOperator.coeff_eq_ncoeff, VertexOperator.coeff_eq_ncoeff,
    (normalMinusOne (Y D a) (Y D b)).2]
  have h := (stateField_iterate D a b c (-1) (-power - 1)).2.2
  dsimp only at h
  have weight (j : ℕ) : (-1 : ℂ)^j * ((Ring.choose (-1) j : ℤ) : ℂ) = 1 :=
    minus_one_binomial j
  simp_rw [weight] at h
  simpa only [mu, one_smul, show (-1 : ℂ)^(-1 : ℤ) = -1 by norm_num,
    neg_smul, one_smul, sub_neg_eq_add,
    show ∀ j : ℕ, (-1 : ℤ) - j = -(j : ℤ) - 1 by intro j; omega,
    show ∀ j : ℕ, (-1 : ℤ) + (-power - 1) - j = -power - 1 - j - 1 by intro j; omega]
    using h

end
end D5.S3.VertexAlgebra.LatticeActualStateFieldCalculus
