/- GID: D5/S3/VertexAlgebra/TwistedGround/OriginalFourMJacobi
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/OriginalFourMJacobi
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The original Jacobi identity for three negative twisted states at all signed modes. -/

import D5.S3.VertexAlgebra.TwistedGround.OriginalFourMReduction
import D5.S3.VertexAlgebra.TwistedGround.ActualOddGradeOrthogonality
import D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMVariableSupport
import Batteries.Tactic.OpenPrivate

/-! The native charge-coset crossing supplies the scalar Jacobi identity at the
matching detector degree. Energy orthogonality handles the other degrees. -/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators TensorProduct VertexOperator

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalFourMChargeCoset

open LatticeGeneratingFieldLocality LatticeHalfFock
open LatticeHalfFockChargedCoefficients LatticeHalfFockChargedTensorCoefficients
open LatticeHalfFockGradedTrace LatticeInvolution LatticeTwistedGroundRealization
open HalfFock.LatticeHalfFockParityField MixedIntertwiner
open LatticeTwistedGroundRealization.SignQuotient
open OriginalFourMInputs
open OperatorAlgebra (chargeOperator)
open private groundForm lower_power_tmul from
  D5.S3.VertexAlgebra.TwistedGround.OriginalFourMChargeCoset
open private jacobiResidual jacobi_residual_zero_iff from
  D5.S3.VertexAlgebra.TwistedGround.OriginalFourMReduction

open LatticeAllStateField LatticePositiveEnergy ActualChargedAdjoint
open LatticeHalfFockCorrectedField ActualOddGradeOrthogonality
open FourPoint.OriginalFourMActualChart (Puncture)
open OriginalFourMVariableSupport (arbitrary_occupation_identityK)
open private T lowering_eigen from D5.S3.VertexAlgebra.TwistedGround.MixedIntertwiner
open private sourceGradePairingEquiv from
  D5.S3.VertexAlgebra.TwistedGround.OriginalFourMContraction
open private actualInputBasis actual_input_basis_energy from
  D5.S3.VertexAlgebra.TwistedGround.MixedJacobiFinite

/-- The three finite actual scalar channels evaluated at a single detector. -/
private def originalJacobiScalarAt (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (H K L : ℕ) (m n r : ℤ) (u v w : paritySpace D hu (-1))
    (detector : ActualTensor D hu) : Prop :=
  let iterate (d : ActualTensor D hu) : ℂ :=
    ∑ j ∈ Finset.range ((H : ℤ)+(K : ℤ)-r).toNat,
      Ring.choose (m : ℂ) j * fourMScalar D hu hD (r+(j : ℤ)) (m+n-(j : ℤ)) u v w.val d
  let first (d : ActualTensor D hu) : ℂ :=
    ∑ j ∈ Finset.range ((K : ℤ)+(L : ℤ)-n).toNat,
      ∑ ell ∈ Finset.range ((H : ℤ)+(K : ℤ)+(L : ℤ)-m-n-r-3).toNat,
        Ring.choose (r : ℂ) j * (-1 : ℂ)^(m+r+(ell : ℤ)+1) * (ell.factorial : ℂ)⁻¹ *
          fourMScalar D hu hD (n+(j : ℤ)) (m+r-(j : ℤ)+(ell : ℤ)) v w u.val
            ((T D hu ^ ell) d)
  let second (d : ActualTensor D hu) : ℂ :=
    ∑ j ∈ Finset.range ((H : ℤ)+(L : ℤ)-m).toNat,
      ∑ ell ∈ Finset.range ((H : ℤ)+(K : ℤ)+(L : ℤ)-m-n-r-3).toNat,
        Ring.choose (r : ℂ) j * (-1 : ℂ)^(n+(ell : ℤ)+1) * (ell.factorial : ℂ)⁻¹ *
          fourMScalar D hu hD (m+(j : ℤ)) (n+r-(j : ℤ)+(ell : ℤ)) u w v.val
            ((T D hu ^ ell) d)
  iterate detector = first detector - second detector

set_option maxHeartbeats 4000000 in
/-- The native charge-coset expansion at a pure tensor detector. -/
private theorem original_jacobi_scalar_at_tensor_iff (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (h24 : D.rank = 24)
    (H K L : ℕ) (m n r : ℤ) (u v w : paritySpace D hu (-1))
    (P Q R : Oscillator D) (x y z : ActualGround D hu)
    (huP : u.val = P ⊗ₜ[ℂ] x) (hvQ : v.val = Q ⊗ₜ[ℂ] y) (hwR : w.val = R ⊗ₜ[ℂ] z)
    (huH : actualTensorL0 D hu u.val = (H : ℂ) • u.val)
    (hvK : actualTensorL0 D hu v.val = (K : ℂ) • v.val)
    (hwL : actualTensorL0 D hu w.val = (L : ℂ) • w.val)
    (S : Oscillator D) (d : ActualGround D hu) :
    originalJacobiScalarAt D hu hD H K L m n r u v w (S ⊗ₜ[ℂ] d) ↔
      (∑ a : ModTwoCharge D, channelA D hu H K m n r P Q R S a *
        groundForm D hu y (chargeOperator D (groundRepresentation D hu) a x) *
        groundForm D hu d (chargeOperator D (groundRepresentation D hu) a z)) =
      (∑ b : ModTwoCharge D, channelB D hu H K L m n r P Q R S b *
        groundForm D hu z (chargeOperator D (groundRepresentation D hu) b y) *
        groundForm D hu d (chargeOperator D (groundRepresentation D hu) b x)) -
      (∑ a : ModTwoCharge D, channelD D hu H K L m n r P Q R S a *
        groundForm D hu z (chargeOperator D (groundRepresentation D hu) a x) *
        groundForm D hu d (chargeOperator D (groundRepresentation D hu) a y)) := by
  classical
  let iterate (d : ActualTensor D hu) : ℂ :=
    ∑ j ∈ Finset.range ((H : ℤ)+(K : ℤ)-r).toNat,
      Ring.choose (m : ℂ) j * fourMScalar D hu hD (r+(j : ℤ)) (m+n-(j : ℤ)) u v w.val d
  let first (d : ActualTensor D hu) : ℂ :=
    ∑ j ∈ Finset.range ((K : ℤ)+(L : ℤ)-n).toNat,
      ∑ ell ∈ Finset.range ((H : ℤ)+(K : ℤ)+(L : ℤ)-m-n-r-3).toNat,
        Ring.choose (r : ℂ) j * (-1 : ℂ)^(m+r+(ell : ℤ)+1) * (ell.factorial : ℂ)⁻¹ *
          fourMScalar D hu hD (n+(j : ℤ)) (m+r-(j : ℤ)+(ell : ℤ)) v w u.val
            ((T D hu ^ ell) d)
  let second (d : ActualTensor D hu) : ℂ :=
    ∑ j ∈ Finset.range ((H : ℤ)+(L : ℤ)-m).toNat,
      ∑ ell ∈ Finset.range ((H : ℤ)+(K : ℤ)+(L : ℤ)-m-n-r-3).toNat,
        Ring.choose (r : ℂ) j * (-1 : ℂ)^(n+(ell : ℤ)+1) * (ell.factorial : ℂ)⁻¹ *
          fourMScalar D hu hD (m+(j : ℤ)) (n+r-(j : ℤ)+(ell : ℤ)) u w v.val
            ((T D hu ^ ell) d)
  have leftExpansion (S : Oscillator D) (d : ActualGround D hu) :
      iterate (S ⊗ₜ[ℂ] d) =
      ∑ a : ModTwoCharge D, channelA D hu H K m n r P Q R S a *
        groundForm D hu y (chargeOperator D (groundRepresentation D hu) a x) *
        groundForm D hu d (chargeOperator D (groundRepresentation D hu) a z) := by
    dsimp only [iterate]
    simp only [channelA, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    rw [hwR, fourM_factorization D hu hD h24 H K (r+(j : ℤ)) (m+n-(j : ℤ))
      u v P Q R S x y z d huP hvQ huH hvK]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    ring
  have firstExpansion (S : Oscillator D) (d : ActualGround D hu) :
      first (S ⊗ₜ[ℂ] d) =
      ∑ a : ModTwoCharge D, channelB D hu H K L m n r P Q R S a *
        groundForm D hu z (chargeOperator D (groundRepresentation D hu) a y) *
        groundForm D hu d (chargeOperator D (groundRepresentation D hu) a x) := by
    dsimp only [first]
    simp only [channelB, Finset.sum_mul, Finset.mul_sum]
    conv_rhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro ell hell
    rw [huP, lower_power_tmul,
      fourM_factorization D hu hD h24 K L (n+(j : ℤ)) (m+r-(j : ℤ)+(ell : ℤ))
        v w Q R P ((oscillatorLower D ^ ell) S) y z x d hvQ hwR hvK hwL]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    ring
  have secondExpansion (S : Oscillator D) (d : ActualGround D hu) :
      second (S ⊗ₜ[ℂ] d) =
      ∑ a : ModTwoCharge D, channelD D hu H K L m n r P Q R S a *
        groundForm D hu z (chargeOperator D (groundRepresentation D hu) a x) *
        groundForm D hu d (chargeOperator D (groundRepresentation D hu) a y) := by
    dsimp only [second]
    simp only [channelD, Finset.sum_mul, Finset.mul_sum]
    conv_rhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro ell hell
    rw [hvQ, lower_power_tmul,
      fourM_factorization D hu hD h24 H L (m+(j : ℤ)) (n+r-(j : ℤ)+(ell : ℤ))
        u w P R Q ((oscillatorLower D ^ ell) S) x z y d huP hwR huH hwL]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    ring
  change (iterate (S ⊗ₜ[ℂ] d) = first (S ⊗ₜ[ℂ] d) - second (S ⊗ₜ[ℂ] d)) ↔ _
  rw [leftExpansion, firstExpansion, secondExpansion]

private theorem fourM_corrected_mode_energy (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (h24 : D.rank = 24)
    (H K L : ℕ) (k t : ℤ) (u v w : paritySpace D hu (-1))
    (huH : actualTensorL0 D hu u.val = (H : ℂ) • u.val)
    (hvK : actualTensorL0 D hu v.val = (K : ℂ) • v.val)
    (hwL : actualTensorL0 D hu w.val = (L : ℂ) • w.val) :
    let out := (correctedField D hu (originalI D hu hD k u v).val).coeff (-2*t-2) w.val
    actualTensorL0 D hu out = (((H : ℤ)+K+L-k-t-2 : ℤ) : ℂ) • out := by
  let h : ℤ := (H : ℤ)+K-k-1
  have ha : (originalI D hu hD k u v).val ∈ grade D h := by
    rw [originalI_homogeneous D hu hD h24 H K k u v huH hvK]
    exact ((sourceGradePairingEquiv D hu hD h).symm
      (normalizedCoefficient D hu k u v h)).property.1
  have e := original_mode_integer_energy D hu h (L : ℤ) t
    (originalI D hu hD k u v).val ha w.val (by simpa only [Int.cast_natCast] using hwL)
  have he : (L : ℤ)+h-t-1 = (H : ℤ)+K+L-k-t-2 := by
    dsimp [h]
    ring
  rwa [he] at e

set_option maxHeartbeats 4000000 in
private theorem scalar_at_different_degree (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (h24 : D.rank = 24)
    (H K L : ℕ) (m n r : ℤ) (u v w : paritySpace D hu (-1))
    (huH : actualTensorL0 D hu u.val = (H : ℂ) • u.val)
    (hvK : actualTensorL0 D hu v.val = (K : ℂ) • v.val)
    (hwL : actualTensorL0 D hu w.val = (L : ℂ) • w.val)
    (d : ActualTensor D hu) (q : ℤ)
    (hd : actualTensorL0 D hu d = ((D.rank : ℂ) / 16 + (q : ℂ) / 2) • d)
    (hne : q ≠ 2 * ((H : ℤ) + K + L - m - n - r - 2) - 3) :
    originalJacobiScalarAt D hu hD H K L m n r u v w d := by
  let N : ℤ := (H : ℤ)+K+L-m-n-r-2
  change q ≠ 2*N-3 at hne
  have vanish (A B C : ℕ) (k t : ℤ) (a b c : paritySpace D hu (-1))
      (ea : actualTensorL0 D hu a.val = (A : ℂ) • a.val)
      (eb : actualTensorL0 D hu b.val = (B : ℂ) • b.val)
      (ec : actualTensorL0 D hu c.val = (C : ℂ) • c.val)
      (ell : ℕ) (hmode : (A : ℤ)+B+C-k-t-2 = N-(ell : ℤ)) :
      fourMScalar D hu hD k t a b c.val ((T D hu ^ ell) d) = 0 := by
    let out := (correctedField D hu (originalI D hu hD k a b).val).coeff (-2*t-2) c.val
    have e : actualTensorL0 D hu out = (((A : ℤ)+B+C-k-t-2 : ℤ) : ℂ) • out :=
      fourM_corrected_mode_energy D hu hD h24 A B C k t a b c ea eb ec
    have ho : actualTensorL0 D hu out =
        ((D.rank : ℂ) / 16 + ((2*(N-(ell : ℤ))-3 : ℤ) : ℂ) / 2) • out := by
      rw [e, hmode]
      congr 1
      rw [h24]
      push_cast
      ring
    exact actualForm_oddGrade_orthogonal D hu _ _ _ _
      (lowering_eigen D hu q d hd ell) ho (by omega)
  dsimp only [originalJacobiScalarAt]
  have hleft :
      (∑ j ∈ Finset.range ((H : ℤ)+(K : ℤ)-r).toNat,
        Ring.choose (m : ℂ) j * fourMScalar D hu hD (r+(j : ℤ)) (m+n-(j : ℤ))
          u v w.val d) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    have hj := vanish H K L (r+(j : ℤ)) (m+n-(j : ℤ)) u v w huH hvK hwL 0
      (by dsimp [N]; omega)
    rw [show fourMScalar D hu hD (r+(j : ℤ)) (m+n-(j : ℤ)) u v w.val d = 0 from
      by simpa only [pow_zero, Module.End.one_apply] using hj, mul_zero]
  rw [hleft]
  apply Eq.symm
  apply sub_eq_zero.mpr
  trans (0 : ℂ)
  · apply Finset.sum_eq_zero
    intro j _
    apply Finset.sum_eq_zero
    intro ell _
    rw [vanish K L H (n+(j : ℤ)) (m+r-(j : ℤ)+(ell : ℤ)) v w u hvK hwL huH ell
      (by dsimp [N]; omega), mul_zero]
  · symm
    apply Finset.sum_eq_zero
    intro j _
    apply Finset.sum_eq_zero
    intro ell _
    rw [vanish H L K (m+(j : ℤ)) (n+r-(j : ℤ)+(ell : ℤ)) u w v huH hwL hvK ell
      (by dsimp [N]; omega), mul_zero]

set_option maxHeartbeats 4000000 in
private theorem scalar_at_of_basis (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (H K L : ℕ) (m n r : ℤ) (u v w : paritySpace D hu (-1))
    (hb : ∀ i, originalJacobiScalarAt D hu hD H K L m n r u v w (actualAmbientBasis D hu i)) :
    ∀ d, originalJacobiScalarAt D hu hD H K L m n r u v w d := by
  let good : Submodule ℂ (ActualTensor D hu) := {
    carrier := {d | originalJacobiScalarAt D hu hD H K L m n r u v w d}
    zero_mem' := by
      change originalJacobiScalarAt D hu hD H K L m n r u v w 0
      simp [originalJacobiScalarAt, fourMScalar]
    add_mem' := by
      intro d e hd he
      change originalJacobiScalarAt D hu hD H K L m n r u v w d at hd
      change originalJacobiScalarAt D hu hD H K L m n r u v w e at he
      change originalJacobiScalarAt D hu hD H K L m n r u v w (d+e)
      dsimp only [originalJacobiScalarAt, fourMScalar] at hd he ⊢
      simp only [map_add, LinearMap.add_apply, mul_add, Finset.sum_add_distrib] at hd he ⊢
      linear_combination hd + he
    smul_mem' := by
      intro c d hd
      change originalJacobiScalarAt D hu hD H K L m n r u v w d at hd
      change originalJacobiScalarAt D hu hD H K L m n r u v w (c • d)
      dsimp only [originalJacobiScalarAt, fourMScalar] at hd ⊢
      simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, mul_left_comm _ c,
        ← Finset.mul_sum, ← mul_sub, hd]
  }
  have hspan : Submodule.span ℂ (Set.range (actualAmbientBasis D hu)) ≤ good :=
    Submodule.span_le.mpr (by
      rintro _ ⟨i, rfl⟩
      exact hb i)
  rw [(actualAmbientBasis D hu).span_eq] at hspan
  intro d
  exact hspan (Submodule.mem_top : d ∈ (⊤ : Submodule ℂ (ActualTensor D hu)))

private theorem single_ground_ne_zero (D : LatticeData) (hu : IsUnit D.G.det)
    (a : LatticeTwistedGroundRealization.Half (groundRank D hu)) :
    (Pi.single a (1 : ℂ) : ActualGround D hu) ≠ 0 := by
  intro h
  exact (one_ne_zero : (1 : ℂ) ≠ 0)
    (by simpa only [Pi.single_eq_same, Pi.zero_apply] using congrFun h a)

set_option maxHeartbeats 4000000 in
private theorem jacobi_on_basis_tensors (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (h24 : D.rank = 24)
    (H K L : ℕ) (m n r : ℤ) (u v w : paritySpace D hu (-1))
    (a b c : OddMonomial D)
    (x y z : LatticeTwistedGroundRealization.Half (groundRank D hu))
    (huP : u.val = MvPolynomial.monomial a 1 ⊗ₜ[ℂ] Pi.single x 1)
    (hvQ : v.val = MvPolynomial.monomial b 1 ⊗ₜ[ℂ] Pi.single y 1)
    (hwR : w.val = MvPolynomial.monomial c 1 ⊗ₜ[ℂ] Pi.single z 1)
    (huH : actualTensorL0 D hu u.val = (H : ℂ) • u.val)
    (hvK : actualTensorL0 D hu v.val = (K : ℂ) • v.val)
    (hwL : actualTensorL0 D hu w.val = (L : ℂ) • w.val) :
    originalJacobi D hu hD m n r u v w := by
  let N : ℤ := (H : ℤ)+K+L-m-n-r-2
  by_cases low : N < 2
  · exact original_jacobi_below_two D hu hD h24 H K L m n r u v w huH hvK hwL low
  apply (original_jacobi_scalar_finite D hu hD h24 H K L m n r u v w huH hvK hwL).mpr
  change ∀ d, originalJacobiScalarAt D hu hD H K L m n r u v w d
  apply scalar_at_of_basis
  rintro ⟨s, t⟩
  have ed : actualTensorL0 D hu (actualAmbientBasis D hu (s, t)) =
      ((D.rank : ℂ) / 16 + ((oddWeight D s : ℤ) : ℂ) / 2) • actualAmbientBasis D hu (s, t) := by
    simpa only [Int.cast_natCast] using actual_basis_eigenvalue D hu s t
  have off (hne : (oddWeight D s : ℤ) ≠ 2*N-3) :=
    scalar_at_different_degree D hu hD h24 H K L m n r u v w huH hvK hwL
      (actualAmbientBasis D hu (s, t)) (oddWeight D s) ed hne
  -- Even detector grades are orthogonal to the odd output grades, also
  -- after lowering, which subtracts an even integer from the detector grade.
  by_cases even : oddWeight D s % 2 = 0
  · exact off (by omega)
  by_cases hm : (oddWeight D s : ℤ) = 2*N-3
  · have hd : actualTensorL0 D hu (actualAmbientBasis D hu (s, t)) =
        (N.toNat : ℂ) • actualAmbientBasis D hu (s, t) := by
      have hN : (N.toNat : ℤ) = N := Int.toNat_of_nonneg (by omega)
      have hcast : (N.toNat : ℂ) = (N : ℂ) := by exact_mod_cast hN
      rw [ed, hm]
      congr 1
      rw [h24, hcast]
      push_cast
      ring
    let occ : Puncture → Exponent D
      | .P => a
      | .Q => b
      | .R => c
      | .S => s
    let weight : Puncture → ℕ
      | .P => H
      | .Q => K
      | .R => L
      | .S => N.toNat
    let groundIndex : Puncture → LatticeTwistedGroundRealization.Half (groundRank D hu)
      | .P => x
      | .Q => y
      | .R => z
      | .S => t
    let ground : Puncture → ActualGround D hu := fun i => Pi.single (groundIndex i) 1
    have hg (i : Puncture) : ground i ≠ 0 := single_ground_ne_zero D hu (groundIndex i)
    have he (i : Puncture) :
        actualTensorL0 D hu (MvPolynomial.monomial (occ i) 1 ⊗ₜ[ℂ] ground i) =
          (weight i : ℂ) • (MvPolynomial.monomial (occ i) 1 ⊗ₜ[ℂ] ground i) := by
      cases i
      · rw [huP] at huH
        exact huH
      · rw [hvQ] at hvK
        exact hvK
      · rw [hwR] at hwL
        exact hwL
      · rw [actual_basis_apply D hu s t] at hd
        exact hd
    have hmode : (weight .S : ℤ) = weight .P + weight .Q + weight .R - (m+n+r) - 2 := by
      dsimp only [weight]
      rw [Int.toNat_of_nonneg (show 0 ≤ N by omega)]
      dsimp only [N]
      push_cast <;> ring
    have crossing := arbitrary_occupation_identityK D hu hD h24 occ weight ground hg he
      m n r hmode
    rw [actual_basis_apply D hu s t]
    apply (original_jacobi_scalar_at_tensor_iff D hu hD h24 H K L m n r u v w
      (MvPolynomial.monomial a 1) (MvPolynomial.monomial b 1) (MvPolynomial.monomial c 1)
      (Pi.single x 1) (Pi.single y 1) (Pi.single z 1) huP hvQ hwR huH hvK hwL
      (MvPolynomial.monomial s 1) (Pi.single t 1)).mpr
    exact (coset_ground_elimination D hu h24 H K L m n r
      (MvPolynomial.monomial a 1) (MvPolynomial.monomial b 1) (MvPolynomial.monomial c 1)
      (MvPolynomial.monomial s 1)).mpr crossing
      (Pi.single x 1) (Pi.single y 1) (Pi.single z 1) (Pi.single t 1)
  · exact off hm

set_option maxHeartbeats 4000000 in
/-- All three original negative twisted inputs satisfy the original vector
Jacobi identity at every signed mode triple. -/
theorem original_jacobi (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (h24 : D.rank = 24)
    (m n r : ℤ) (u v w : paritySpace D hu (-1)) :
    originalJacobi D hu hD m n r u v w := by
  apply (jacobi_residual_zero_iff D hu hD m n r u v w).mp
  rw [input_trilinear_expansion]
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j _
  apply Finset.sum_eq_zero
  intro k _
  have hi := actual_input_basis_energy D hu h24 u i
  have hj := actual_input_basis_energy D hu h24 v j
  have hk := actual_input_basis_energy D hu h24 w k
  have law := jacobi_on_basis_tensors D hu hD h24 _ _ _ m n r
    (actualInputBasis D hu u i) (actualInputBasis D hu v j) (actualInputBasis D hu w k)
    i.val.1 j.val.1 k.val.1 i.val.2 j.val.2 k.val.2
    (actual_basis_apply D hu i.val.1 i.val.2)
    (actual_basis_apply D hu j.val.1 j.val.2)
    (actual_basis_apply D hu k.val.1 k.val.2) hi hj hk
  rw [(jacobi_residual_zero_iff D hu hD m n r _ _ _).mpr law, smul_zero]

end D5.S3.VertexAlgebra.TwistedGround.OriginalFourMChargeCoset
