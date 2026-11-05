/- GID: D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostStateFieldIterate
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/LatticeMatterGhostStateFieldIterate
   mirror-E: none(waiver:original-matter-ghost-signed-iterate)
   anchors: []
   utility: none
   digest: Unrestricted signed integer iterate on the original matter/ghost tensor states. -/

/-
Copyright (c) 2025 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the repository root LICENSE.
The residue telescope retains the attributed vertexAlg supplier provenance.
Classical signed Dong locality and creative uniqueness identify the actual
integer mode product on the original tensor state carrier. No literature
novelty, full three-integer Borcherds identity or string-theory completion is claimed.
proof_shape: stateField_iterate: content
admission_basis: escape-witness
escape_witness: Original parity covariance fixes the product parity; signed
residue locality, creation and original translation feed the original tensor
creative_unique theorem. Four actual parity components yield unrestricted
braiding, with finite action support before every sum exchange.
-/

import D5.S3.VertexAlgebra.Lattice.LatticeMatterGhostBRSTDerivation
import D5.S3.VertexAlgebra.SignedFields.SignedFieldResidueLocality

/-! Integer residue closure and unrestricted braiding of the original tensor fields. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators TensorProduct VertexOperator

namespace D5.S3.VertexAlgebra.LatticeMatterGhostStateFieldIterate
open LatticeGeneratingFieldLocality LatticeMatterGhostCoupling
open LatticeMatterGhostStateField
open FieldNormalProductLocality SignedFieldNormalProductLocality SignedFieldResidueLocality
open StateFieldResidueReconstruction (integerBinomial epsilon)
open private parity_square creative_unique local_sub from
  D5.S3.VertexAlgebra.Lattice.LatticeMatterGhostBRSTDerivation

noncomputable section

private theorem residue_creation (s : ℂ) (r : ℤ) (D : LatticeData) (a b : State D) : (((residueField s r (Y D a) (Y D b)).operator) [[-1]]) (vacuum D) = ((Y D a) [[r]]) b ∧ ∀ index : ℤ, 0 ≤ index → (((residueField s r (Y D a) (Y D b)).operator) [[index]]) (vacuum D) = 0 := by

    have rightZero (index : ℤ) : residueRight r index (Y D a) (Y D b) (vacuum D) = 0 := by
      unfold residueRight; apply finsum_eq_zero_of_forall_eq_zero; intro offset; rw [(stateField_vacuum_creation D).2.2.1 a offset (by omega)]
      simp
    constructor
    · rw [(residueField s r (Y D a) (Y D b)).coefficient, residueCoefficient, rightZero, smul_zero, sub_zero]
      unfold residueLeft; rw [finsum_eq_single _ 0]
      · simp [integerBinomial, (stateField_vacuum_creation D).2.1 b]
      · intro offset distinct
        rw [(stateField_vacuum_creation D).2.2.1 b (-1 + (offset : ℤ)) (by omega)]; simp
    · intro index nonnegative
      rw [(residueField s r (Y D a) (Y D b)).coefficient, residueCoefficient, rightZero, smul_zero, sub_zero]; unfold residueLeft
      apply finsum_eq_zero_of_forall_eq_zero; intro offset; rw [(stateField_vacuum_creation D).2.2.1 b (index + (offset : ℤ)) (by omega)]; simp


private theorem residueClosure (D : LatticeData) (a b : State D) (p q : ℕ)
    (ha : parity D a = (-1 : ℂ) ^ p • a)
    (hb : parity D b = (-1 : ℂ) ^ q • b) (r : ℤ) :
    Y D (((Y D a) [[r]]) b) =
      (residueField ((-1 : ℂ) ^ (p * q)) r (Y D a) (Y D b)).operator := by
  let field := (residueField ((-1 : ℂ) ^ (p * q)) r (Y D a) (Y D b)).operator
  let product := ((Y D a) [[r]]) b
  let difference := field - Y D product
  have productParity : parity D product = (-1 : ℂ) ^ (p + q) • product := by
    have law := LinearMap.congr_fun (stateField_parity D a r) b
    simp only [Module.End.mul_apply] at law
    rw [ha, hb, map_smul, map_smul] at law
    simp only [Pi.smul_apply, LinearMap.smul_apply, map_smul, smul_smul] at law
    simpa only [product, pow_add, mul_comm] using law
  have creativeDifference : ∀ n : ℤ, 0 ≤ n → (difference [[n]]) (vacuum D) = 0 := by
    intro n hn
    simp only [difference, field, map_sub, Pi.sub_apply, LinearMap.sub_apply,
      (residue_creation _ r D a b).2 n hn,
      (stateField_vacuum_creation D).2.2.1 product n hn, sub_self]
  have initial : (difference [[-1]]) (vacuum D) = 0 := by
    simp only [difference, field, product, map_sub, Pi.sub_apply, LinearMap.sub_apply,
      (residue_creation _ r D a b).1, (stateField_vacuum_creation D).2.1, sub_self]
  have covariance (n : ℤ) :
      translation D * (difference [[n]]) - (difference [[n]]) * translation D =
        -(n : ℂ) • (difference [[n - 1]]) := by
    simp only [difference, map_sub, Pi.sub_apply]
    calc
      _ = (translation D * (field [[n]]) - (field [[n]]) * translation D) -
        (translation D * ((Y D product) [[n]]) -
          ((Y D product) [[n]]) * translation D) := by
          simp only [mul_sub, sub_mul]
          abel
      _ = _ := by
        rw [residue_translation _ r (Y D a) (Y D b) (translation D)
          (stateField_covariance D a) (stateField_covariance D b), stateField_covariance]
        module
  have crossLocality (c : State D) (t : ℕ)
      (hc : parity D c = (-1 : ℂ) ^ t • c) :
      ∃ N : ℕ, delta^[N]
        (signedComm ((-1 : ℂ) ^ ((p + q) * t)) difference (Y D c)) = 0 := by
    have sign : ((-1 : ℂ) ^ (p * t)) * ((-1 : ℂ) ^ (q * t)) =
        (-1 : ℂ) ^ ((p + q) * t) := by rw [← pow_add, Nat.add_mul]
    have first := residue_locality ((-1 : ℂ) ^ (p * q))
      ((-1 : ℂ) ^ (p * t)) ((-1 : ℂ) ^ (q * t)) (Y D a) (Y D b) (Y D c)
      (stateField_locality D a c p t ha hc)
      (stateField_locality D b c q t hb hc)
      (stateField_locality D a b p q ha hb) r
    rw [sign] at first
    exact local_sub _ field (Y D product) (Y D c) first
      (stateField_locality D product c (p + q) t productParity hc)
  have vanished := creative_unique D (p + q) difference
    creativeDifference initial covariance crossLocality
  exact (sub_eq_zero.mp vanished).symm

private abbrev leftSum (D : LatticeData) (r n : ℤ) (a b c : State D) :=
  residueLeft r n (Y D a) (Y D b) c
private abbrev rightSum (D : LatticeData) (r n : ℤ) (a b c : State D) :=
  residueRight r n (Y D a) (Y D b) c

private theorem homogeneous_iterate (D : LatticeData) (a b c : State D) (p q : ℕ)
    (ha : parity D a = (-1 : ℂ) ^ p • a)
    (hb : parity D b = (-1 : ℂ) ^ q • b) (r n : ℤ) :
    (((Y D (((Y D a) [[r]]) b)) [[n]]) c) =
      leftSum D r n a b c - (epsilon r * (-1 : ℂ) ^ (p * q)) • rightSum D r n a b c := by
  rw [residueClosure D a b p q ha hb r, (residueField _ r (Y D a) (Y D b)).coefficient]
  rfl

private theorem left_add_left (D : LatticeData) (r n : ℤ) (a b d c : State D) :
    leftSum D r n (a + d) b c =
      leftSum D r n a b c + leftSum D r n d b c := by
  dsimp only [leftSum, residueLeft]
  simp only [map_add, Pi.add_apply, LinearMap.add_apply, smul_add]
  rw [finsum_add_distrib ((residueField 1 r (Y D a) (Y D b)).left_finite n c)
    ((residueField 1 r (Y D d) (Y D b)).left_finite n c)]

private theorem left_add_right (D : LatticeData) (r n : ℤ) (a b d c : State D) :
    leftSum D r n a (b + d) c =
      leftSum D r n a b c + leftSum D r n a d c := by
  dsimp only [leftSum, residueLeft]
  simp only [map_add, Pi.add_apply, LinearMap.add_apply, smul_add]
  rw [finsum_add_distrib ((residueField 1 r (Y D a) (Y D b)).left_finite n c)
    ((residueField 1 r (Y D a) (Y D d)).left_finite n c)]

private theorem right_add_right (D : LatticeData) (r n : ℤ) (a b d c : State D) :
    rightSum D r n a (b + d) c =
      rightSum D r n a b c + rightSum D r n a d c := by
  dsimp only [rightSum, residueRight]
  simp only [map_add, Pi.add_apply, LinearMap.add_apply, smul_add]
  rw [finsum_add_distrib ((residueField 1 r (Y D a) (Y D b)).right_finite n c)
    ((residueField 1 r (Y D a) (Y D d)).right_finite n c)]

private theorem right_sub_right (D : LatticeData) (r n : ℤ) (a b d c : State D) :
    rightSum D r n a (b - d) c =
      rightSum D r n a b c - rightSum D r n a d c := by
  dsimp only [rightSum, residueRight]
  simp only [map_sub, Pi.sub_apply, LinearMap.sub_apply, smul_sub]
  rw [finsum_sub_distrib ((residueField 1 r (Y D a) (Y D b)).right_finite n c)
    ((residueField 1 r (Y D a) (Y D d)).right_finite n c)]

/-- Every original tensor state and every pair of integer modes, with the
parity involution in the unrestricted reverse braiding and finite action sums. -/
theorem stateField_iterate (D : LatticeData) (a b c : State D) (r n : ℤ) :
    let a0 := (2 : ℂ)⁻¹ • (a + parity D a)
    let a1 := (2 : ℂ)⁻¹ • (a - parity D a)
    let w : ℕ → ℂ := fun i => ((-1 : ℂ) ^ i) * ((Ring.choose r i : ℤ) : ℂ)
    let left : ℕ → State D := fun i =>
      w i • (((Y D a) [[r - (i : ℤ)]]) (((Y D b) [[n + (i : ℤ)]]) c))
    let right0 : ℕ → State D := fun i =>
      w i • (((Y D b) [[r + n - (i : ℤ)]]) (((Y D a0) [[(i : ℤ)]]) c))
    let right1 : ℕ → State D := fun i =>
      w i • (((Y D (parity D b)) [[r + n - (i : ℤ)]]) (((Y D a1) [[(i : ℤ)]]) c))
    Function.HasFiniteSupport left ∧ Function.HasFiniteSupport right0 ∧
      Function.HasFiniteSupport right1 ∧
      (((Y D (((Y D a) [[r]]) b)) [[n]]) c) =
        (∑ᶠ i : ℕ, left i) - ((-1 : ℂ) ^ r) •
          ((∑ᶠ i : ℕ, right0 i) + (∑ᶠ i : ℕ, right1 i)) := by
  let a0 := (2 : ℂ)⁻¹ • (a + parity D a)
  let a1 := (2 : ℂ)⁻¹ • (a - parity D a)
  let b0 := (2 : ℂ)⁻¹ • (b + parity D b)
  let b1 := (2 : ℂ)⁻¹ • (b - parity D b)
  have even (x : State D) :
      parity D ((2 : ℂ)⁻¹ • (x + parity D x)) =
        (-1 : ℂ)^0 • ((2 : ℂ)⁻¹ • (x + parity D x)) := by
    rw [map_smul, map_add, parity_square]
    simp only [pow_zero, one_smul]
    congr 1
    abel
  have odd (x : State D) :
      parity D ((2 : ℂ)⁻¹ • (x - parity D x)) =
        (-1 : ℂ)^1 • ((2 : ℂ)⁻¹ • (x - parity D x)) := by
    rw [map_smul, map_sub, parity_square]
    norm_num only [pow_one]
    module
  have aSplit : a = a0 + a1 := by dsimp [a0, a1]; module
  have bSplit : b = b0 + b1 := by dsimp [b0, b1]; module
  have paritySplit : parity D b = b0 - b1 := by dsimp [b0, b1]; module
  dsimp only
  refine ⟨(residueField 1 r (Y D a) (Y D b)).left_finite n c,
    (residueField 1 r (Y D a0) (Y D b)).right_finite n c,
    (residueField 1 r (Y D a1) (Y D (parity D b))).right_finite n c, ?_⟩
  change (((Y D (((Y D a) [[r]]) b)) [[n]]) c) =
    leftSum D r n a b c - epsilon r •
      (rightSum D r n a0 b c + rightSum D r n a1 (parity D b) c)
  have lhs : (((Y D (((Y D a) [[r]]) b)) [[n]]) c) =
      (((Y D (((Y D a0) [[r]]) b0)) [[n]]) c) +
      (((Y D (((Y D a0) [[r]]) b1)) [[n]]) c) +
      ((((Y D (((Y D a1) [[r]]) b0)) [[n]]) c) +
        (((Y D (((Y D a1) [[r]]) b1)) [[n]]) c)) := by
    conv_lhs => rw [aSplit, bSplit]
    simp only [map_add, Pi.add_apply, LinearMap.add_apply]
    abel
  have left : leftSum D r n a b c =
      leftSum D r n a0 b0 c + leftSum D r n a0 b1 c +
        (leftSum D r n a1 b0 c + leftSum D r n a1 b1 c) := by
    rw [aSplit, left_add_left, bSplit, left_add_right, left_add_right]
  have right0 : rightSum D r n a0 b c =
      rightSum D r n a0 b0 c + rightSum D r n a0 b1 c := by
    rw [bSplit, right_add_right]
  have right1 : rightSum D r n a1 (parity D b) c =
      rightSum D r n a1 b0 c - rightSum D r n a1 b1 c := by
    rw [paritySplit, right_sub_right]
  rw [lhs, left, right0, right1,
    homogeneous_iterate D a0 b0 c 0 0 (even a) (even b),
    homogeneous_iterate D a0 b1 c 0 1 (even a) (odd b),
    homogeneous_iterate D a1 b0 c 1 0 (odd a) (even b),
    homogeneous_iterate D a1 b1 c 1 1 (odd a) (odd b)]
  norm_num only [Nat.zero_mul, Nat.mul_zero, Nat.one_mul, pow_zero, pow_one, mul_one,
    mul_neg, mul_one]
  module

end
end D5.S3.VertexAlgebra.LatticeMatterGhostStateFieldIterate
