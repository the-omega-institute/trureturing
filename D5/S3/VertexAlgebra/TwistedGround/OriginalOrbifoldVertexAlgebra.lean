/- GID: D5/S3/VertexAlgebra/TwistedGround/OriginalOrbifoldVertexAlgebra
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/OriginalOrbifoldVertexAlgebra
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The original fixed and negative twisted sectors carry a state-field vertex algebra. -/

import D5.S3.VertexAlgebra.LatticeActualVertexAlgebra
import D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMIdentity
import D5.S3.VertexAlgebra.TwistedGround.OriginalOrbifoldFaithfulness
import D5.S3.VertexAlgebra.TwistedGround.OriginalOrbifoldJacobi

/-! The original rank-24 four-point identity closes the state-field axioms
on the sum of the fixed and negative twisted sectors. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalOrbifoldVertexAlgebra

open LatticeGeneratingFieldLocality (LatticeData)
open LatticeActualVertexAlgebra (StateFieldVertexAlgebra)
open OriginalOrbifoldField OriginalOrbifoldTranslation
open StateField.BorcherdsPermutations
open StateFieldResidueReconstruction (epsilon integerBinomial)
open scoped BigOperators VertexOperator

noncomputable section

section Locality

open FieldNormalProductLocality (commutator delta deltaEnd)

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

private theorem product_nat (μ : Modes V) (a b c : V) (p q : ℤ) (N : ℕ) :
    product μ a b c p q N = ∑ j ∈ Finset.range (N + 1),
      ((-1 : ℂ)^j * (N.choose j : ℂ)) • μ (p + (N : ℤ) - j) a (μ (q + j) b c) := by
  simp only [product, integerBinomial, Ring.choose_natCast, Int.cast_natCast]
  apply finsum_eq_sum_of_support_subset
  intro j hj
  by_contra hout
  have hchoose : N.choose j = 0 := Nat.choose_eq_zero_of_lt (by simpa using hout)
  exact hj (by simp [hchoose])

private theorem delta_commutator_eq_products (Y₀ : V →ₗ[ℂ] VertexOperator ℂ V)
    (a b c : V) (p q : ℤ) (N : ℕ) :
    ((deltaEnd ^ N) (commutator (Y₀ a) (Y₀ b))) p q c =
      product (modesOfStateField Y₀) a b c p q N -
        epsilon N • product (modesOfStateField Y₀) b a c q p N := by
  rw [product_nat, product_nat, FieldDeltaBinomial.delta_binomial, LinearMap.sum_apply]
  simp only [FieldNormalProductLocality.commutator, LinearMap.smul_apply, LinearMap.sub_apply,
    Module.End.mul_apply, smul_sub, Finset.sum_sub_distrib, modesOfStateField,
    LinearMap.comp_apply, LinearMap.proj_apply]
  congr 1
  rw [Finset.smul_sum]
  conv_rhs => rw [← Finset.sum_range_reflect]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' : j ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  simp only [Nat.add_sub_cancel, Nat.choose_symm hj', epsilon, zpow_natCast, smul_smul]
  have hsplit : (-1 : ℂ)^N = (-1 : ℂ)^j * (-1 : ℂ)^(N - j) := by
    rw [← pow_add, Nat.add_sub_of_le hj']
  have hsquare : (-1 : ℂ)^(N - j) * (-1 : ℂ)^(N - j) = 1 := by
    rw [← mul_pow]
    norm_num
  have hsign : (-1 : ℂ)^N * ((-1 : ℂ)^(N - j) * (N.choose j : ℂ)) =
      (-1 : ℂ)^j * (N.choose j : ℂ) := by
    rw [hsplit, ← mul_assoc, mul_assoc ((-1 : ℂ)^j), hsquare, mul_one]
  rw [hsign, Int.natCast_sub hj']
  rw [show q + (N : ℤ) - ((N : ℤ) - j) = q + j by omega,
    show p + ((N : ℤ) - j) = p + N - j by omega]

private theorem locality_of_borcherds (Y₀ : V →ₗ[ℂ] VertexOperator ℂ V)
    (trunc : LowerTruncated (modesOfStateField Y₀))
    (jacobi : ∀ (a b c : V) (p q r : ℤ), defect (modesOfStateField Y₀) a b c p q r = 0)
    (a b : V) : ∃ N : ℕ, delta^[N] (commutator (Y₀ a) (Y₀ b)) = 0 := by
  obtain ⟨bound, tail⟩ := trunc a b
  refine ⟨bound.toNat, ?_⟩
  let N := bound.toNat
  change delta^[N] (commutator (Y₀ a) (Y₀ b)) = 0
  have hdelta : (deltaEnd ^ N) (commutator (Y₀ a) (Y₀ b)) = 0 := by
    funext p q
    apply LinearMap.ext
    intro c
    have h := jacobi a b c p q N
    have hiter : iterate (modesOfStateField Y₀) a b c p q N = 0 := by
      unfold iterate
      apply finsum_eq_zero_of_forall_eq_zero
      intro j
      rw [tail _ (show bound ≤ (N : ℤ) + j by dsimp [N]; omega),
        map_zero, LinearMap.zero_apply, smul_zero]
    rw [delta_commutator_eq_products]
    simpa only [defect, hiter, sub_zero, Pi.zero_apply, LinearMap.zero_apply] using h
  rw [Module.End.pow_apply] at hdelta
  exact hdelta

end Locality

variable (D : LatticeData) (hu : IsUnit D.G.det)
  (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (h24 : D.rank = 24)

local notation "μ" => modesOfStateField (Y D hu hD)

private theorem original_truncation : LowerTruncated μ := by
  intro a b
  obtain ⟨N, tail⟩ := mode_tail D hu hD a b
  refine ⟨N, fun n hn => ?_⟩
  change ((Y D hu hD a)[[n]]) b = 0
  rw [Y_ncoeff]
  exact tail n hn

include h24

private theorem original_defect (a b c : Carrier D hu) (p q r : ℤ) :
    defect μ a b c p q r = 0 :=
  OriginalOrbifoldJacobi.defect_all hD h24
    (OriginalFourMChargeCoset.original_fourM_jacobi D hu hD h24)
    (MixedIntertwiner.fixedParitySlice_faithful D hu hD h24) a b c p q r

/-- The original fields satisfy Borcherds for all states and every signed integer triple. -/
theorem original_borcherds (a b c : Carrier D hu) (p q r : ℤ) :
    let left : ℕ → Carrier D hu := fun i => integerBinomial p i •
      ((Y D hu hD (((Y D hu hD a)[[r+i]]) b))[[p+q-i]]) c
    let first : ℕ → Carrier D hu := fun i =>
      ((-1 : ℂ)^i * integerBinomial r i) • ((Y D hu hD a)[[p+r-i]])
        (((Y D hu hD b)[[q+i]]) c)
    let second : ℕ → Carrier D hu := fun i =>
      ((-1 : ℂ)^i * integerBinomial r i) •
        (epsilon r • ((Y D hu hD b)[[q+r-i]]) (((Y D hu hD a)[[p+i]]) c))
    Function.HasFiniteSupport left ∧ Function.HasFiniteSupport first ∧
      Function.HasFiniteSupport second ∧
        (∑ᶠ i : ℕ, left i) = ∑ᶠ i : ℕ, ((-1 : ℂ)^i * integerBinomial r i) •
          (((Y D hu hD a)[[p+r-i]]) (((Y D hu hD b)[[q+i]]) c) -
            epsilon r • ((Y D hu hD b)[[q+r-i]]) (((Y D hu hD a)[[p+i]]) c)) :=
  (defect_eq_zero_iff_borcherds μ (original_truncation D hu hD) a b c p q r).mp
    (original_defect D hu hD h24 a b c p q r)

/-- The state-field vertex algebra on the original fixed and negative twisted sectors. -/
def originalVertexAlgebra : StateFieldVertexAlgebra (Carrier D hu) where
  stateField := Y D hu hD
  vacuum := vacuumState D hu
  translation := T D hu
  vacuum_field := by
    apply HVertexOperator.coeff_inj
    funext k
    apply LinearMap.ext
    intro b
    rw [VertexOperator.coeff_eq_ncoeff, vacuum_ncoeff]
    change (if -k - 1 = -1 then b else 0) =
      (if k = 0 then LinearMap.id else (0 : Module.End ℂ (Carrier D hu))) b
    by_cases hk : k = 0
    · subst k
      simp
    · rw [ite_eq_right (show -k - 1 ≠ -1 by omega), ite_eq_right hk, LinearMap.zero_apply]
  creation a := by
    simpa only [ite_true] using creation_ncoeff D hu hD a (-1) le_rfl
  creativity a n hn := by
    simpa only [ite_eq_right (show n ≠ -1 by omega)] using
      creation_ncoeff D hu hD a n (by omega)
  translation_vacuum := T_vacuum D hu
  covariance a n := Y_covariance D hu hD h24 n a
  locality := locality_of_borcherds (Y D hu hD) (original_truncation D hu hD)
    (original_defect D hu hD h24)
  borcherds := original_borcherds D hu hD h24

#print axioms original_borcherds
#print axioms originalVertexAlgebra

end
end D5.S3.VertexAlgebra.TwistedGround.OriginalOrbifoldVertexAlgebra
