/- GID: D5/S3/VertexAlgebra/LatticeActualGeneratorLocality
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeActualGeneratorLocality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The actual lattice cocycle and creation coefficients obey the signed contraction laws. -/

import D5.S3.VertexAlgebra.LatticeAllStateField

/-
Actual lattice generator identities, on every finite-rank integral symmetric
lattice with even diagonal, including rank zero. No positivity or invertibility.
The lower-matrix and integral cocycle symmetrization proofs are adapted verbatim
from LatticeTwistedGroundRealization at immutable commit
bfd9ff0f15397a4fb933f36d701a60d325d84b08, sha256
f7032c03d6edd67435d766c9e0c503774dd50561742e3c6e95f722b657f47781.
All field identities below use the actual coefficient definitions.
References: Bakalov--Kac math/0402315v1, section 4.1.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.LatticeActualGeneratorLocality
open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration
open FieldNormalProduct MvPolynomial
open scoped BigOperators VertexOperator
noncomputable section

 theorem bilinear_symmetric (D : LatticeData) (α β : Charge D) :
    bilinear D α β = bilinear D β α := by
  rw [bilinear, bilinear, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [D.symmetric j i]
  ring

@[simp] theorem bilinear_add_left (D : LatticeData) (α β δ : Charge D) :
    bilinear D (α + β) δ = bilinear D α δ + bilinear D β δ := by
  simp [bilinear, add_mul, Finset.sum_add_distrib]

@[simp] theorem bilinear_add_right (D : LatticeData) (α β δ : Charge D) :
    bilinear D α (β + δ) = bilinear D α β + bilinear D α δ := by
  simp [bilinear, mul_add, Finset.sum_add_distrib]

def lowerMatrix (D : LatticeData) : Matrix (Fin D.rank) (Fin D.rank) ℤ :=
  fun i j => (if j < i then D.G i j else 0) +
    (if j = i then halfDiagonal D i else 0)

theorem lower_matrix_formula (D : LatticeData) (a b : Charge D) :
    lowerCocycleExponent D a b = ∑ i, ∑ j, a i * lowerMatrix D i j * b j := by
  classical
  unfold lowerCocycleExponent
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [lowerMatrix, mul_add, add_mul, Finset.sum_add_distrib]
  congr 1
  · rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro j hj
    split_ifs <;> ring
  · rw [Finset.sum_eq_single i]
    · simp only [ite_true]
      ring
    · intro j hj hji
      simp [hji]
    · simp

theorem lower_matrix_symmetrization (D : LatticeData) :
    lowerMatrix D + (lowerMatrix D).transpose = D.G := by
  ext i j
  change lowerMatrix D i j + lowerMatrix D j i = D.G i j
  by_cases hij : i = j
  · subst j
    obtain ⟨k, hk⟩ := D.even_diagonal i
    simp only [lowerMatrix, lt_self_iff_false, if_false, if_true, zero_add, halfDiagonal]
    omega
  · rcases lt_or_gt_of_ne hij with hij | hji
    · simp [lowerMatrix, hij, ne_of_lt hij, (ne_of_lt hij).symm,
        not_lt_of_gt hij, D.symmetric i j]
    · simp [lowerMatrix, hji, ne_of_gt hji, (ne_of_gt hji).symm,
        not_lt_of_gt hji]

theorem integral_cocycle_symmetrization (D : LatticeData) (a b : Charge D) :
    lowerCocycleExponent D a b + lowerCocycleExponent D b a = bilinear D a b := by
  rw [lower_matrix_formula, lower_matrix_formula]
  unfold bilinear
  conv_lhs => rhs; rw [Finset.sum_comm]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  have h := congrFun (congrFun (lower_matrix_symmetrization D) i) j
  change lowerMatrix D i j + lowerMatrix D j i = D.G i j at h
  rw [← h]
  ring

theorem integral_cocycle_square (D : LatticeData) (a : Charge D) :
    lowerCocycleExponent D a a = bilinear D a a / 2 := by
  have h := integral_cocycle_symmetrization D a a
  omega


theorem paritySign_add (a b : ℤ) : paritySign (a + b) = paritySign a * paritySign b := by
  by_cases ha : Even a <;> by_cases hb : Even b <;>
    simp [paritySign, Int.even_add, ha, hb]

@[simp] theorem paritySign_square (a : ℤ) : paritySign a * paritySign a = 1 := by
  unfold paritySign
  split_ifs <;> ring

@[simp] theorem epsilon_add_left (D : LatticeData) (α β δ : Charge D) :
    epsilon D (α + β) δ = epsilon D α δ * epsilon D β δ := by
  unfold epsilon
  rw [show lowerCocycleExponent D (α + β) δ =
      lowerCocycleExponent D α δ + lowerCocycleExponent D β δ by
    simp [lowerCocycleExponent, add_mul, mul_add, Finset.sum_add_distrib]
    <;> ring]
  exact paritySign_add _ _

@[simp] theorem epsilon_add_right (D : LatticeData) (α β δ : Charge D) :
    epsilon D α (β + δ) = epsilon D α β * epsilon D α δ := by
  unfold epsilon
  rw [show lowerCocycleExponent D α (β + δ) =
      lowerCocycleExponent D α β + lowerCocycleExponent D α δ by
    simp [lowerCocycleExponent, mul_add, Finset.sum_add_distrib]
    <;> ring]
  exact paritySign_add _ _

/-- The actual sign, including coincident charges, obeys the required skew law. -/
theorem epsilon_skew (D : LatticeData) (α β : Charge D) :
    epsilon D α β = paritySign (bilinear D α β) * epsilon D β α := by
  rw [← integral_cocycle_symmetrization, paritySign_add]
  unfold epsilon
  rw [mul_assoc, paritySign_square, mul_one]

/-- Both product signs are computed from the actual cocycle, on every sector. -/
theorem epsilon_ordered (D : LatticeData) (α β δ : Charge D) :
    epsilon D α (β + δ) * epsilon D β δ =
      epsilon D α β * epsilon D (α + β) δ := by
  rw [epsilon_add_right, epsilon_add_left]
  ring

/-- Evenness of every lattice norm follows from the actual cocycle identity. -/
theorem bilinear_self_even (D : LatticeData) (α : Charge D) :
    Even (bilinear D α α) :=
  ⟨lowerCocycleExponent D α α, (integral_cocycle_symmetrization D α α).symm⟩

@[simp] theorem actual_modes (D : LatticeData) (α : Charge D) (m : ℤ) :
    (actualField D α)[[m]] = rawCoeff D α (-m - 1) := by
  rw [actualField, VertexOperator.ncoeff_of_coeff]

@[simp] theorem neutral_modes (D : LatticeData) (i : Fin D.rank) (m : ℤ) :
    (neutralField D i)[[m]] = neutralMode D i m := by
  rw [neutralField, VertexOperator.ncoeff_of_coeff]
  rw [show -(-m - 1) - 1 = m by omega]

/-- Full contraction law, with the library's integer choose and sign convention. -/
theorem actual_contraction_binomial (D : LatticeData) (α β : Charge D)
    (t : ℤ) (j : ℕ) :
    (translatedPolynomial D α (creationCoeff D β t)).coeff j =
      ((-1 : ℂ)^j * (Ring.choose (bilinear D α β) j : ℤ)) •
        creationCoeff D β (t - j) := by
  rw [(actual_creation_coefficient_transport D α β).2.1]
  rw [PowerSeries.coeff_rescale, PowerSeries.binomialSeries_coeff (R := ℤ)]
  simp [zsmul_eq_mul]

/-- Contraction on each actual coefficient has finite support, even for negative pairing. -/
theorem actual_contraction_finite (D : LatticeData) (α β : Charge D) (t : ℤ) :
    Function.HasFiniteSupport (fun j : ℕ =>
      ((-1 : ℂ)^j * (Ring.choose (bilinear D α β) j : ℤ)) •
        creationCoeff D β (t - j)) := by
  classical
  have h : Function.support (fun j : ℕ =>
      ((-1 : ℂ)^j * (Ring.choose (bilinear D α β) j : ℤ)) •
        creationCoeff D β (t - j)) ⊆ Finset.range (t.toNat + 1) := by
    intro j hj
    apply Finset.mem_range.mpr
    by_contra hn
    have ht : t - (j : ℤ) < 0 := by omega
    exact hj (by simp [creationCoeff, ht])
  exact (Finset.finite_toSet _).subset h

end
end D5.S3.VertexAlgebra.LatticeActualGeneratorLocality
