/- GID: D5/S3/Quantum/Fermionic/BcGhostStateFieldIterate
   generality: I
   mirror-B: D5/B/S3/Quantum/Fermionic/BcGhostStateFieldIterate
   mirror-E: none(waiver:algebraic-ghost-signed-iterate)
   anchors: []
   utility: none
   digest: Signed integer residue closure on the original ghost occupation carrier. -/

/-
Copyright (c) 2025 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the repository root LICENSE.
The generic signed residue constructor, locality and covariance are supplied by
SignedFieldResidueLocality, with its attributed ScottCarnahan/vertexAlg source.
The reverse residue has its actual homogeneous super sign throughout.
-/

/-
proof_shape: stateField_iterate: content
escape_witness: Actual vacuum creation and signed occupation-basis uniqueness
identify the generic residue with the field of the actual all-integer mode product.
admission_basis: escape-witness
-/

import D5.S3.Quantum.Fermionic.BcGhostStateFieldLocality
import D5.S3.VertexAlgebra.StateFieldResidueReconstruction
import D5.S3.VertexAlgebra.BinomialKernelDelta

/-! Generic signed residues reconstructed as actual occupation-state fields. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators VertexOperator
open D5.S3.Quantum.Fermionic.CountableOccupationFock
open D5.S3.Quantum.Fermionic.BcGhostFock
open D5.S3.Quantum.Fermionic.BcGhostStateField
open D5.S3.Quantum.Fermionic.BcGhostStateFieldLocality
open D5.S3.VertexAlgebra.FieldNormalProduct
open D5.S3.VertexAlgebra.FieldNormalProductLocality
open D5.S3.VertexAlgebra.StateFieldResidueReconstruction (integerBinomial epsilon)
open private signedNormalMinusOne derivative_modes forward_finite reverse_finite from
  D5.S3.Quantum.Fermionic.BcGhostStateField
open private signedComm from
  D5.S3.Quantum.Fermionic.BcGhostStateFieldLocality
open private parity_ket from D5.S3.Quantum.Fermionic.CountableOccupationFock

noncomputable section
namespace D5.S3.Quantum.Fermionic.BcGhostStateFieldIterate

private def residueLeft (r n : ℤ) (a b vector : Fock) : Fock :=
  D5.S3.VertexAlgebra.SignedFieldResidueLocality.residueLeft r n (Y a) (Y b) vector

private def residueRight (r n : ℤ) (a b vector : Fock) : Fock :=
  D5.S3.VertexAlgebra.SignedFieldResidueLocality.residueRight r n (Y a) (Y b) vector

private def residueCoefficient (s : ℂ) (r n : ℤ) (a b vector : Fock) : Fock :=
  D5.S3.VertexAlgebra.SignedFieldResidueLocality.residueCoefficient s r n (Y a) (Y b) vector

private structure ResidueField (s : ℂ) (r : ℤ) (a b : Fock) where
  operator : VertexOperator ℂ Fock
  coefficient : ∀ n vector, (operator [[n]]) vector = residueCoefficient s r n a b vector
  left_finite : ∀ n vector, Function.HasFiniteSupport (fun offset : ℕ =>
    (((-1 : ℂ) ^ offset) * integerBinomial r offset) • ((Y a) [[r - offset]]) (((Y b) [[n + offset]]) vector))
  right_finite : ∀ n vector, Function.HasFiniteSupport (fun offset : ℕ =>
    (((-1 : ℂ) ^ offset) * integerBinomial r offset) • ((Y b) [[r + n - offset]]) (((Y a) [[offset]]) vector))

private def residueField (s : ℂ) (r : ℤ) (a b : Fock) : ResidueField s r a b :=
  let field := D5.S3.VertexAlgebra.SignedFieldResidueLocality.residueField s r (Y a) (Y b)
  { operator := field.operator
    coefficient := field.coefficient
    left_finite := field.left_finite
    right_finite := field.right_finite }

private theorem binomial (value : ℤ → ℤ → Module.End ℂ Fock) (order : ℕ) (first second : ℤ) : ((deltaEnd ^ order) value) first second = ∑ offset ∈ Finset.range (order + 1), (((-1 : ℂ) ^
    offset) * (order.choose offset : ℂ)) • value (first + (order : ℤ) - offset) (second + offset) := by
  exact D5.S3.VertexAlgebra.FieldDeltaBinomial.delta_binomial value order first second

private theorem residue_translation (s : ℂ) (r : ℤ) (a b : Fock) (index : ℤ) : BcGhostVirasoro.L (-1) * (((residueField s r a b).operator) [[index]]) - (((residueField s r a b).operator) [[index]]) * BcGhostVirasoro.L (-1) = -(index : ℂ) • (((residueField s r a
    b).operator) [[index - 1]]) := by
  exact D5.S3.VertexAlgebra.SignedFieldResidueLocality.residue_translation s r (Y a) (Y b)
    (BcGhostVirasoro.L (-1)) (stateField_translation.2 a) (stateField_translation.2 b) index

private theorem residue_creation (s : ℂ) (r : ℤ) (a b : Fock) :
    (((residueField s r a b).operator) [[-1]]) vacuum = ((Y a) [[r]]) b ∧
    ∀ index : ℤ, 0 ≤ index →
      (((residueField s r a b).operator) [[index]]) vacuum = 0 := by
  have rightZero (index : ℤ) : residueRight r index a b vacuum = 0 := by
    unfold residueRight D5.S3.VertexAlgebra.SignedFieldResidueLocality.residueRight
    apply finsum_eq_zero_of_forall_eq_zero
    intro offset
    rw [stateField_creation.2.2.1 a offset (by omega)]
    simp
  constructor
  · rw [(residueField s r a b).coefficient, residueCoefficient,
      D5.S3.VertexAlgebra.SignedFieldResidueLocality.residueCoefficient,
      ← residueLeft, ← residueRight, rightZero, smul_zero, sub_zero]
    unfold residueLeft D5.S3.VertexAlgebra.SignedFieldResidueLocality.residueLeft
    rw [finsum_eq_single _ 0]
    · simp [integerBinomial, stateField_creation.2.1 b]
    · intro offset distinct
      rw [stateField_creation.2.2.1 b (-1 + (offset : ℤ)) (by omega)]
      simp
  · intro index nonnegative
    rw [(residueField s r a b).coefficient, residueCoefficient,
      D5.S3.VertexAlgebra.SignedFieldResidueLocality.residueCoefficient,
      ← residueLeft, ← residueRight, rightZero, smul_zero, sub_zero]
    unfold residueLeft D5.S3.VertexAlgebra.SignedFieldResidueLocality.residueLeft
    apply finsum_eq_zero_of_forall_eq_zero
    intro offset
    rw [stateField_creation.2.2.1 b (index + (offset : ℤ)) (by omega)]
    simp

private theorem signed_uniqueness (operator : VertexOperator ℂ Fock)
    (sign : Finset ℕ → ℂ)
    (creativeOperator : ∀ index : ℤ, 0 ≤ index → (operator [[index]]) vacuum = 0)
    (initial : (operator [[-1]]) vacuum = 0)
    (covariant : ∀ index : ℤ,
      BcGhostVirasoro.L (-1) * (operator [[index]]) -
        (operator [[index]]) * BcGhostVirasoro.L (-1) =
          -(index : ℂ) • (operator [[index - 1]]))
    (locality : ∀ S : Finset ℕ, ∃ order : ℕ,
      delta^[order] (signedComm (sign S) operator (Y (ket S))) = 0) :
    operator = 0 := by
  classical
  have vacuumNegative (degree : ℕ) : (operator [[-(degree : ℤ) - 1]]) vacuum = 0 := by
    induction degree with
    | zero => simpa using initial
    | succ degree inductionHypothesis =>
      have law := congrArg (fun endomorphism : Module.End ℂ Fock => endomorphism vacuum) (covariant (-(degree : ℤ) - 1))
      simp only [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply, inductionHypothesis, stateField_translation.1, map_zero, sub_self] at law
      rw [show -(degree : ℤ) - 1 - 1 = -((degree + 1 : ℕ) : ℤ) - 1 by omega] at law
      have scalar : -((-(degree : ℤ) - 1 : ℤ) : ℂ) = (degree : ℂ) + 1 := by push_cast; ring
      rw [scalar] at law
      have nonzero : (degree : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero degree
      exact (smul_eq_zero.mp law.symm).resolve_left nonzero
  have vacuumZero (index : ℤ) : (operator [[index]]) vacuum = 0 := by
    by_cases nonnegative : 0 ≤ index
    · exact creativeOperator index nonnegative
    · let degree := (-index - 1).toNat
      rw [show index = -(degree : ℤ) - 1 by dsimp [degree]; omega]
      exact vacuumNegative degree
  have allModes (index : ℤ) (state : Finset ℕ) : (operator [[index]]) (ket state) = 0 := by
    obtain ⟨order, killed⟩ := locality state
    change (deltaEnd : Module.End ℂ (ℤ → ℤ → Module.End ℂ Fock))^[order] (signedComm (sign state) operator (Y (ket state))) = 0 at killed
    rw [← Module.End.pow_apply] at killed
    have coefficient := congrArg (fun distribution : ℤ → ℤ → Module.End ℂ Fock =>
        distribution (index - order) (-1) vacuum) killed
    rw [binomial, LinearMap.sum_apply] at coefficient; simp only [LinearMap.smul_apply] at coefficient
    have simplify : (∑ offset ∈ Finset.range (order + 1), (((-1 : ℂ) ^ offset) * (order.choose offset : ℂ)) • signedComm (sign state) operator (Y (ket state)) (index -
      order + (order : ℤ) - offset) (-1 + offset) vacuum) = (operator [[index]]) (ket state) := by
      rw [Finset.sum_eq_single 0]
      · simp only [pow_zero, Nat.choose_zero_right, Nat.cast_one, mul_one, one_smul, Nat.cast_zero, sub_zero, add_zero, show index - (order : ℤ) + order = index by omega,
        signedComm,
        D5.S3.VertexAlgebra.SignedFieldNormalProductLocality.signedComm,
        LinearMap.sub_apply, LinearMap.smul_apply, Module.End.mul_apply, vacuumZero, map_zero, smul_zero, sub_zero, stateField_creation.2.1 (ket state)]
      · intro offset member distinct
        have vanish : ((Y (ket state)) [[-1 + (offset : ℤ)]]) vacuum = 0 := stateField_creation.2.2.1 (ket state) _ (by omega)
        simp only [signedComm,
          D5.S3.VertexAlgebra.SignedFieldNormalProductLocality.signedComm,
          LinearMap.sub_apply, LinearMap.smul_apply, Module.End.mul_apply, vanish, vacuumZero, map_zero, smul_zero, sub_self]
      · simp
    rw [simplify] at coefficient; exact coefficient
  have endZero (index : ℤ) : (operator [[index]]) = 0 := by
    apply Finsupp.lhom_ext
    intro S z
    have hs : Finsupp.single S z = z • ket S := by simp [ket]
    rw [hs, map_smul, allModes, smul_zero]
    rfl
  apply HVertexOperator.coeff_inj
  funext power
  rw [VertexOperator.coeff_eq_ncoeff, VertexOperator.coeff_eq_ncoeff, endZero]
  simp

private theorem negativeResidue (s : ℂ) (a b : Fock) (degree : ℕ) : (residueField s (-(degree : ℤ) - 1) a b).operator = (signedNormalMinusOne s (dividedDerivative degree (Y a)) (Y b)).1 := by
  exact D5.S3.VertexAlgebra.SignedFieldResidueLocality.negativeResidue s (Y a) (Y b) degree

private theorem residueLocality (a b c : Fock) (p q t : ℕ)
    (ha : parity a = (-1 : ℂ) ^ p • a)
    (hb : parity b = (-1 : ℂ) ^ q • b)
    (hc : parity c = (-1 : ℂ) ^ t • c) (r : ℤ) :
    ∃ N, delta^[N] (signedComm ((-1 : ℂ) ^ ((p + q) * t))
      (residueField ((-1 : ℂ) ^ (p * q)) r a b).operator (Y c)) = 0 := by
  have result :=
  D5.S3.VertexAlgebra.SignedFieldResidueLocality.residue_locality
    ((-1 : ℂ) ^ (p * q)) ((-1 : ℂ) ^ (p * t)) ((-1 : ℂ) ^ (q * t))
    (Y a) (Y b) (Y c) (stateField_locality a c p t ha hc)
    (stateField_locality b c q t hb hc) (stateField_locality a b p q ha hb) r
  simpa only [← pow_add, ← Nat.add_mul, signedComm, residueField] using result

private theorem residueClosure (a b : Fock) (p q : ℕ)
    (ha : parity a = (-1 : ℂ) ^ p • a)
    (hb : parity b = (-1 : ℂ) ^ q • b) (r : ℤ) :
    Y (((Y a) [[r]]) b) = (residueField ((-1 : ℂ) ^ (p * q)) r a b).operator := by
  classical
  let field := (residueField ((-1 : ℂ) ^ (p * q)) r a b).operator
  let product := ((Y a) [[r]]) b
  let difference := field - Y product
  have productParity : parity product = (-1 : ℂ) ^ (p + q) • product := by
    have law := LinearMap.congr_fun (stateField_parity a r) b
    simp only [Module.End.mul_apply] at law
    rw [ha, hb, map_smul, map_smul] at law
    simp only [Pi.smul_apply, LinearMap.smul_apply, map_smul, smul_smul] at law
    simpa only [product, pow_add, mul_comm] using law
  have creativeDifference : ∀ index : ℤ, 0 ≤ index → (difference [[index]]) vacuum = 0 := by
    intro index nonnegative
    simp only [difference, field, map_sub, Pi.sub_apply, LinearMap.sub_apply,
      (residue_creation _ r a b).2 index nonnegative,
      stateField_creation.2.2.1 product index nonnegative, sub_self]
  have initial : (difference [[-1]]) vacuum = 0 := by
    simp only [difference, field, product, map_sub, Pi.sub_apply, LinearMap.sub_apply,
      (residue_creation _ r a b).1, stateField_creation.2.1, sub_self]
  have covariance (index : ℤ) :
      BcGhostVirasoro.L (-1) * (difference [[index]]) -
        (difference [[index]]) * BcGhostVirasoro.L (-1) =
          -(index : ℂ) • (difference [[index - 1]]) := by
    simp only [difference, map_sub, Pi.sub_apply]
    calc
      _ = (BcGhostVirasoro.L (-1) * (field [[index]]) -
          (field [[index]]) * BcGhostVirasoro.L (-1)) -
        (BcGhostVirasoro.L (-1) * ((Y product) [[index]]) -
          ((Y product) [[index]]) * BcGhostVirasoro.L (-1)) := by
          simp only [mul_sub, sub_mul]
          abel
      _ = _ := by rw [residue_translation, stateField_translation.2]; module
  have crossLocality (S : Finset ℕ) : ∃ N, delta^[N]
      (signedComm ((-1 : ℂ) ^ ((p + q) * S.card)) difference (Y (ket S))) = 0 := by
    obtain ⟨M, hM⟩ := residueLocality a b (ket S) p q S.card ha hb (parity_ket S) r
    obtain ⟨N, hN⟩ := stateField_locality product (ket S) (p + q) S.card
      productParity (parity_ket S)
    let degree := max M N
    change (deltaEnd : Module.End ℂ (ℤ → ℤ → Module.End ℂ Fock))^[M]
      (signedComm ((-1 : ℂ) ^ ((p + q) * S.card)) field (Y (ket S))) = 0 at hM
    change (deltaEnd : Module.End ℂ (ℤ → ℤ → Module.End ℂ Fock))^[N]
      (signedComm ((-1 : ℂ) ^ ((p + q) * S.card)) (Y product) (Y (ket S))) = 0 at hN
    rw [← Module.End.pow_apply] at hM hN
    have firstHigh := Module.End.pow_map_zero_of_le (le_max_left M N) hM
    have secondHigh := Module.End.pow_map_zero_of_le (le_max_right M N) hN
    have split : signedComm ((-1 : ℂ) ^ ((p + q) * S.card)) difference (Y (ket S)) =
        signedComm ((-1 : ℂ) ^ ((p + q) * S.card)) field (Y (ket S)) -
          signedComm ((-1 : ℂ) ^ ((p + q) * S.card)) (Y product) (Y (ket S)) := by
      funext i j
      simp only [signedComm,
        D5.S3.VertexAlgebra.SignedFieldNormalProductLocality.signedComm,
        difference, map_sub, Pi.sub_apply, mul_sub, sub_mul,
        smul_sub]
      abel
    refine ⟨degree, ?_⟩
    change (deltaEnd : Module.End ℂ (ℤ → ℤ → Module.End ℂ Fock))^[degree] _ = 0
    rw [← Module.End.pow_apply, split, map_sub, firstHigh, secondHigh, sub_self]
  have vanished := signed_uniqueness difference (fun S => (-1 : ℂ) ^ ((p + q) * S.card))
    creativeDifference initial covariance crossLocality
  exact (sub_eq_zero.mp vanished).symm

/-- The full signed all-integer iterate identity on the original ghost carrier,
including genuine finite support for both coefficient sums. -/
theorem stateField_iterate (a b c : Fock) (p q : ℕ)
    (ha : parity a = (-1 : ℂ) ^ p • a)
    (hb : parity b = (-1 : ℂ) ^ q • b) (r n : ℤ) :
    let left : ℕ → Fock := fun i =>
      (((-1 : ℂ) ^ i) * ((Ring.choose r i : ℤ) : ℂ)) •
        (((Y a) [[r - (i : ℤ)]]) (((Y b) [[n + (i : ℤ)]]) c))
    let right : ℕ → Fock := fun i =>
      (((-1 : ℂ) ^ i) * ((Ring.choose r i : ℤ) : ℂ)) •
        (((Y b) [[r + n - (i : ℤ)]]) (((Y a) [[(i : ℤ)]]) c))
    Function.HasFiniteSupport left ∧ Function.HasFiniteSupport right ∧
      (((Y (((Y a) [[r]]) b)) [[n]]) c) =
        (∑ᶠ i : ℕ, left i) -
          (((-1 : ℂ) ^ r) * ((-1 : ℂ) ^ (p * q))) • (∑ᶠ i : ℕ, right i) := by
  dsimp
  let field := residueField ((-1 : ℂ) ^ (p * q)) r a b
  refine ⟨field.left_finite n c, field.right_finite n c, ?_⟩
  rw [residueClosure a b p q ha hb r, field.coefficient]
  rfl

end D5.S3.Quantum.Fermionic.BcGhostStateFieldIterate
