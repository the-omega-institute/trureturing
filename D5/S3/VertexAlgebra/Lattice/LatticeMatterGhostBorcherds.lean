/- GID: D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostBorcherds
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/LatticeMatterGhostBorcherds
   mirror-E: none(waiver:original-tensor-borcherds)
   anchors: []
   utility: none
   digest: Signed all-integer Borcherds identity for unrestricted original tensor states. -/

/-
Copyright (c) 2025 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the repository root LICENSE.
The high-index coefficient argument and descending-distance induction adapt
the pinned BcGhostBorcherds supplier, itself adapting LatticeAllStateJacobi
and PolynomialFockJacobi. The original vertexAlg source is
ScottCarnahan/vertexAlg revision 4453e34ec390e82a0c789c731ada8f9a6e86bdea,
VertexAlg/VertexBasic/VertexOperator.lean. See Matsuo--Nagatomo,
hep-th/9706118v1, Proposition 1.5.5 and Theorem 5.4.1.
The tensor support and Pascal terms are reused from
LatticeMatterGhostSignedBorcherds. Signed residue closure and the homogeneous
iterate are supplied by LatticeMatterGhostStateFieldIterate.
No ghost-carrier theorem is transported to the tensor carrier, and no
literature novelty or string-theory completion is claimed.
proof_shape: borcherds: content
admission_basis: escape-witness
escape_witness: Actual tensor locality and truncation produce the high-index
seed; the native iterate and supported tensor Pascal recurrence propagate
it through negative first indices. Four supported parity components give
the unrestricted reverse braiding on the original state space.
-/

import D5.S3.VertexAlgebra.Lattice.LatticeMatterGhostSignedBorcherds
import D5.S3.VertexAlgebra.Lattice.LatticeMatterGhostStateFieldIterate
import Batteries.Tactic.OpenPrivate

/-! Unrestricted all-integer Borcherds identity on the original tensor carrier. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators VertexOperator

namespace D5.S3.VertexAlgebra.LatticeMatterGhostBorcherds

open LatticeGeneratingFieldLocality (LatticeData)
open LatticeMatterGhostCoupling (State)
open LatticeMatterGhostStateField
open LatticeMatterGhostSignedBorcherds
  (mu_D jacobiLeftTerm jacobiRightFirstTerm jacobiRightSecondTerm
)
open FieldNormalProductLocality SignedFieldNormalProductLocality
open StateFieldResidueReconstruction (integerBinomial epsilon)
open SignedFieldResidueLocality (residueLeft residueRight)
open private third_sequence_finite left_support right_first_support p_zero_left
  coupled_discrepancy_recurrence from
  D5.S3.VertexAlgebra.Lattice.LatticeMatterGhostSignedBorcherds
open private homogeneous_iterate leftSum rightSum from
  D5.S3.VertexAlgebra.Lattice.LatticeMatterGhostStateFieldIterate
open private parity_square from
  D5.S3.VertexAlgebra.Lattice.LatticeMatterGhostBRSTDerivation

noncomputable section

private abbrev tensorLeft (D : LatticeData) (p q r : ℤ) (a b c : State D) :=
  ∑ᶠ i : ℕ, jacobiLeftTerm D p q r a b c i

private abbrev tensorForward (D : LatticeData) (p q r : ℤ) (a b c : State D) :=
  ∑ᶠ i : ℕ, jacobiRightFirstTerm D p q r a b c i

private abbrev reverseTerm (D : LatticeData) (p q r : ℤ)
    (a b c : State D) (i : ℕ) : State D :=
  (((-1 : ℂ)^i) * integerBinomial r i) •
    mu_D D b (q + r - i) (mu_D D a (p + i) c)

private abbrev tensorReverse (D : LatticeData) (p q r : ℤ) (a b c : State D) :=
  ∑ᶠ i : ℕ, reverseTerm D p q r a b c i

private theorem reverse_finite (D : LatticeData) (a b c : State D) (p q r : ℤ) :
    Function.HasFiniteSupport (reverseTerm D p q r a b c) :=
  (third_sequence_finite D a b c p q r).smul_right
    (fun i : ℕ => ((-1 : ℂ)^i) * integerBinomial r i)

private theorem reverse_scaled (D : LatticeData) (a b c : State D)
    (s : ℂ) (p q r : ℤ) :
    (∑ᶠ i : ℕ, jacobiRightSecondTerm D s p q r a b c i) =
      (epsilon r * s) • tensorReverse D p q r a b c := by
  rw [smul_finsum' (epsilon r * s) (reverse_finite D a b c p q r)]
  apply finsum_congr
  intro i
  exact smul_comm _ _ _

set_option maxHeartbeats 4000000 in
-- Retain the supplier budget for supported coefficient and scalar normalization.
private theorem homogeneous_borcherds (D : LatticeData) (a b c : State D)
    (pa pb : ℕ)
    (ha : parity D a = (-1 : ℂ)^pa • a)
    (hb : parity D b = (-1 : ℂ)^pb • b) (p q r : ℤ) :
    tensorLeft D p q r a b c = tensorForward D p q r a b c -
      (epsilon r * (-1 : ℂ)^(pa * pb)) • tensorReverse D p q r a b c := by
  classical
  let superSign : ℂ := (-1 : ℂ)^(pa * pb)
  let discrepancy : ℤ → ℤ → ℤ → State D :=
    LatticeMatterGhostSignedBorcherds.discrepancy D superSign a b c
  have binomial (value : ℤ → ℤ → Module.End ℂ (State D)) (order : ℕ)
      (first second : ℤ) : ((deltaEnd ^ order) value) first second =
        ∑ offset ∈ Finset.range (order + 1),
          (((-1 : ℂ)^offset) * (order.choose offset : ℂ)) •
            value (first+(order : ℤ)-offset) (second+offset) :=
    D5.S3.VertexAlgebra.FieldDeltaBinomial.delta_binomial value order first second
  obtain ⟨localityOrder, localityLaw⟩ := stateField_locality D a b pa pb ha hb
  let supportCutoff : ℕ := (-((HahnModule.of ℂ).symm ((Y D a) b)).order).toNat
  let cutoff : ℕ := localityOrder + supportCutoff
  have killedLocal : (deltaEnd ^ localityOrder) (signedComm superSign (Y D a) (Y D b)) = 0 := by
    rw [Module.End.pow_apply]
    change delta^[localityOrder] (fun m n =>
      ((Y D a) [[m]]) * ((Y D b) [[n]]) - ((-1 : ℂ) ^ (pa * pb)) •
        (((Y D b) [[n]]) * ((Y D a) [[m]]))) = 0
    exact localityLaw
  have highSeed : ∀ first second parameter : ℤ, (cutoff : ℤ) ≤ parameter →
      discrepancy first second parameter = 0 := by
    change ∀ first second parameter : ℤ, (cutoff : ℤ) ≤ parameter →
      (∑ᶠ offset : ℕ, jacobiLeftTerm D first second parameter a b c offset) -
        (∑ᶠ offset : ℕ, jacobiRightFirstTerm D first second parameter a b c offset) +
        (∑ᶠ offset : ℕ, jacobiRightSecondTerm D superSign first second parameter a b c offset) = 0
    have positiveProduct (degree : ℕ) (first second : ℤ) (vector : State D) :
        (∑ᶠ offset : ℕ, jacobiRightFirstTerm D first second degree a b vector offset) -
          (∑ᶠ offset : ℕ, jacobiRightSecondTerm D superSign first second degree a b vector offset) =
            ((deltaEnd ^ degree) (signedComm superSign (Y D a) (Y D b))) first second vector := by
      have chooseNat (offset : ℕ) : integerBinomial degree offset = (degree.choose offset : ℂ) := by
        simp [integerBinomial, Ring.choose_natCast]
      have firstSum : (∑ᶠ offset : ℕ, jacobiRightFirstTerm D first second degree a b vector offset) =
          ∑ offset ∈ Finset.range (degree + 1),
            (((-1 : ℂ) ^ offset) * (degree.choose offset : ℂ)) •
              ((Y D a) [[first + degree - offset]]) (((Y D b) [[second + offset]]) vector) := by
        unfold jacobiRightFirstTerm mu_D
        simp_rw [chooseNat]
        apply finsum_eq_sum_of_support_subset
        intro offset member
        by_contra outside
        have zeroChoose : degree.choose offset = 0 := Nat.choose_eq_zero_of_lt (by simpa using outside)
        exact member (by simp [zeroChoose])
      have secondSum : (∑ᶠ offset : ℕ, jacobiRightSecondTerm D superSign first second degree a b vector offset) =
          (epsilon (degree : ℤ) * superSign) •
            ∑ offset ∈ Finset.range (degree + 1),
              (((-1 : ℂ) ^ offset) * (degree.choose offset : ℂ)) •
                ((Y D b) [[second + degree - offset]]) (((Y D a) [[first + offset]]) vector) := by
        unfold jacobiRightSecondTerm mu_D
        simp_rw [chooseNat]
        rw [Finset.smul_sum]
        simp_rw [smul_comm (epsilon (degree : ℤ) * superSign)]
        apply finsum_eq_sum_of_support_subset
        intro offset member
        by_contra outside
        have zeroChoose : degree.choose offset = 0 := Nat.choose_eq_zero_of_lt (by simpa using outside)
        exact member (by simp [zeroChoose])
      rw [firstSum, secondSum, binomial, LinearMap.sum_apply]
      simp only [LinearMap.smul_apply, signedComm, Module.End.mul_apply,
        LinearMap.sub_apply, smul_sub, Finset.sum_sub_distrib]
      apply congrArg (fun z : State D =>
        (∑ offset ∈ Finset.range (degree + 1),
          (((-1 : ℂ) ^ offset) * (degree.choose offset : ℂ)) •
            ((Y D a) [[first + degree - offset]]) (((Y D b) [[second + offset]]) vector)) -
          z)
      rw [Finset.smul_sum, ← Finset.sum_range_reflect]
      apply Finset.sum_congr rfl
      intro offset member
      have within : offset ≤ degree := by simpa using Finset.mem_range.mp member
      simp only [Nat.add_sub_cancel, Nat.choose_symm within, smul_smul, epsilon,
        zpow_natCast]
      have signs : (-1 : ℂ) ^ degree *
          ((-1 : ℂ) ^ (degree - offset) * (degree.choose offset : ℂ)) =
            (-1 : ℂ) ^ offset * (degree.choose offset : ℂ) := by
        have split : (-1 : ℂ) ^ degree =
            (-1 : ℂ) ^ offset * (-1 : ℂ) ^ (degree - offset) := by
          rw [← pow_add, Nat.add_sub_of_le within]
        rw [split]
        have squared : ((-1 : ℂ) ^ (degree - offset)) ^ 2 = 1 := by
          rw [← pow_mul, mul_comm, pow_mul]
          norm_num
        calc
          _ = (-1 : ℂ) ^ offset * (((-1 : ℂ) ^ (degree - offset)) ^ 2) *
              (degree.choose offset : ℂ) := by ring
          _ = _ := by rw [squared]; ring
      have signedSigns : ((-1 : ℂ) ^ degree * superSign) *
          ((-1 : ℂ) ^ (degree - offset) * (degree.choose offset : ℂ)) =
          ((-1 : ℂ) ^ offset * (degree.choose offset : ℂ)) * superSign := by
        calc
          _ = superSign * ((-1 : ℂ) ^ degree *
              ((-1 : ℂ) ^ (degree - offset) * (degree.choose offset : ℂ))) := by ring
          _ = _ := by rw [signs]; ring
      rw [signedSigns]
      push_cast [Int.natCast_sub within]
      rw [show second + (degree : ℤ) - ((degree : ℤ) - offset) = second + offset by omega,
        show first + ((degree : ℤ) - offset) = first + degree - offset by omega]
    intro first second parameter high
    have stateZero (offset : ℕ) : mu_D D a (parameter + offset) b = 0 := by
      apply VertexOperator.ncoeff_eq_zero_of_lt_order
      have hbound : (supportCutoff : ℤ) ≤ parameter := by
        dsimp [cutoff, supportCutoff] at high ⊢
        omega
      dsimp [supportCutoff] at hbound
      omega
    have leftZero : (∑ᶠ offset : ℕ, jacobiLeftTerm D first second parameter a b c offset) = 0 := by
      apply finsum_eq_zero_of_forall_eq_zero
      intro offset
      rw [jacobiLeftTerm, stateZero]
      simp [mu_D]
    have rightZero : (∑ᶠ offset : ℕ, jacobiRightFirstTerm D first second parameter a b c offset) -
        (∑ᶠ offset : ℕ, jacobiRightSecondTerm D superSign first second parameter a b c offset) = 0 := by
      obtain ⟨degree, rfl⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ parameter by dsimp [cutoff] at high; omega)
      rw [positiveProduct]
      have vanish : (deltaEnd ^ degree) (signedComm superSign (Y D a) (Y D b)) = 0 := by
        obtain ⟨extra, equality⟩ := Nat.exists_eq_add_of_le (show localityOrder ≤ degree by omega)
        rw [equality, pow_add, (Commute.refl deltaEnd).pow_pow localityOrder extra |>.eq,
          Module.End.mul_apply, killedLocal, map_zero]
      rw [vanish]
      rfl
    rw [leftZero, sub_eq_zero.mp rightZero]
    abel
  have zeroSeed (q r : ℤ) : discrepancy 0 q r = 0 := by
    change tensorLeft D 0 q r a b c - tensorForward D 0 q r a b c +
      (∑ᶠ i : ℕ, jacobiRightSecondTerm D superSign 0 q r a b c i) = 0
    dsimp only [tensorLeft]
    rw [p_zero_left, reverse_scaled]
    have iterate := homogeneous_iterate D a b c pa pb ha hb r q
    have seed : mu_D D (mu_D D a r b) q c =
        tensorForward D 0 q r a b c -
          (epsilon r * superSign) • tensorReverse D 0 q r a b c := by
      simpa only [leftSum, rightSum, residueLeft, residueRight,
        tensorForward, tensorReverse, reverseTerm, jacobiRightFirstTerm,
        mu_D, zero_add, add_comm r q] using iterate
    rw [seed]
    abel
  have recurrence (u v w : ℤ) :
      discrepancy (u + 1) v w =
        discrepancy u (v + 1) w + discrepancy u v (w + 1) :=
    coupled_discrepancy_recurrence D superSign a b c u v w
  have allIndices : ∀ p q r : ℤ, discrepancy p q r = 0 := by
    have positive (degree : ℕ) : ∀ q r : ℤ, discrepancy degree q r = 0 := by
      induction degree with
      | zero => exact zeroSeed
      | succ degree inductionHypothesis =>
        intro q r
        rw [Nat.cast_add, Nat.cast_one, recurrence,
          inductionHypothesis, inductionHypothesis, add_zero]
    have negative (distance : ℕ) : ∀ magnitude : ℕ, ∀ q : ℤ,
        discrepancy (-(magnitude : ℤ)) q ((cutoff : ℤ) - distance) = 0 := by
      induction distance with
      | zero =>
        intro magnitude q
        exact highSeed _ _ _ (by omega)
      | succ distance outerHypothesis =>
        intro magnitude
        induction magnitude with
        | zero => intro q; exact zeroSeed _ _
        | succ magnitude innerHypothesis =>
          intro q
          have law := recurrence (-((magnitude + 1 : ℕ) : ℤ)) (q - 1)
            ((cutoff : ℤ) - (distance + 1 : ℕ))
          rw [show -((magnitude + 1 : ℕ) : ℤ) + 1 = -(magnitude : ℤ) by omega,
            show q - 1 + 1 = q by omega,
            show (cutoff : ℤ) - (distance + 1 : ℕ) + 1 = (cutoff : ℤ) - distance by omega,
            innerHypothesis, outerHypothesis, add_zero] at law
          exact law.symm
    intro p q r
    by_cases nonnegative : 0 ≤ p
    · obtain ⟨degree, rfl⟩ := Int.eq_ofNat_of_zero_le nonnegative
      exact positive degree q r
    · by_cases high : (cutoff : ℤ) ≤ r
      · exact highSeed p q r high
      · let magnitude := (-p).toNat
        let distance := ((cutoff : ℤ) - r).toNat
        have pEquality : p = -(magnitude : ℤ) := by dsimp [magnitude]; omega
        have rEquality : r = (cutoff : ℤ) - distance := by dsimp [distance]; omega
        rw [pEquality, rEquality]
        exact negative distance magnitude q
  have law := allIndices p q r
  change tensorLeft D p q r a b c - tensorForward D p q r a b c +
    (∑ᶠ i : ℕ, jacobiRightSecondTerm D superSign p q r a b c i) = 0 at law
  rw [reverse_scaled] at law
  change tensorLeft D p q r a b c = tensorForward D p q r a b c -
    (epsilon r * superSign) • tensorReverse D p q r a b c
  apply sub_eq_zero.mp
  calc
    _ = tensorLeft D p q r a b c - tensorForward D p q r a b c +
        (epsilon r * superSign) • tensorReverse D p q r a b c := by abel
    _ = 0 := law

set_option maxHeartbeats 4000000 in
-- Retain the supplier budget for supported coefficient and scalar normalization.
/-- Full signed Borcherds identity for the original tensor field, with no
homogeneity or lattice-metric hypothesis. All four actual coefficient
families have pointwise finite support. The reverse braiding is expressed
by the original parity involution and its scalar-half projections. -/
theorem borcherds (D : LatticeData) (a b c : State D) (p q r : ℤ) :
    let a0 := (2 : ℂ)⁻¹ • (a + parity D a)
    let a1 := (2 : ℂ)⁻¹ • (a - parity D a)
    let w : ℕ → ℂ := fun i => ((-1 : ℂ)^i) * integerBinomial r i
    Function.HasFiniteSupport (jacobiLeftTerm D p q r a b c) ∧
    Function.HasFiniteSupport (jacobiRightFirstTerm D p q r a b c) ∧
    Function.HasFiniteSupport (fun i : ℕ =>
      w i • mu_D D b (q + r - i) (mu_D D a0 (p + i) c)) ∧
    Function.HasFiniteSupport (fun i : ℕ =>
      w i • mu_D D (parity D b) (q + r - i) (mu_D D a1 (p + i) c)) ∧
    (∑ᶠ i : ℕ, jacobiLeftTerm D p q r a b c i) =
      ∑ᶠ i : ℕ, w i •
        (mu_D D a (p + r - i) (mu_D D b (q + i) c) -
          epsilon r •
            (mu_D D b (q + r - i) (mu_D D a0 (p + i) c) +
              mu_D D (parity D b) (q + r - i) (mu_D D a1 (p + i) c))) := by
  classical
  let a0 := (2 : ℂ)⁻¹ • (a + parity D a)
  let a1 := (2 : ℂ)⁻¹ • (a - parity D a)
  let b0 := (2 : ℂ)⁻¹ • (b + parity D b)
  let b1 := (2 : ℂ)⁻¹ • (b - parity D b)
  let w : ℕ → ℂ := fun i => ((-1 : ℂ)^i) * integerBinomial r i
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
  have finiteLeft (x y : State D) :
      Function.HasFiniteSupport (jacobiLeftTerm D p q r x y c) :=
    left_support D x y c p q r
  have finiteForward (x y : State D) :
      Function.HasFiniteSupport (jacobiRightFirstTerm D p q r x y c) :=
    right_first_support D x y c p q r
  have right0Finite := reverse_finite D a0 b c p q r
  have right1Finite := reverse_finite D a1 (parity D b) c p q r
  dsimp only
  refine ⟨finiteLeft a b, finiteForward a b, right0Finite, right1Finite, ?_⟩
  have fourSum {f f00 f01 f10 f11 : ℕ → State D}
      (h00 : Function.HasFiniteSupport f00) (h01 : Function.HasFiniteSupport f01)
      (h10 : Function.HasFiniteSupport f10) (h11 : Function.HasFiniteSupport f11)
      (pointwise : ∀ i, f i = f00 i + f01 i + (f10 i + f11 i)) :
      (∑ᶠ i : ℕ, f i) = (∑ᶠ i : ℕ, f00 i) + (∑ᶠ i : ℕ, f01 i) +
        ((∑ᶠ i : ℕ, f10 i) + (∑ᶠ i : ℕ, f11 i)) := by
    simp_rw [pointwise]
    have outer := finsum_add_distrib (h00.add h01) (h10.add h11)
    simp only [Pi.add_apply] at outer
    rw [finsum_add_distrib h00 h01, finsum_add_distrib h10 h11] at outer
    exact outer
  have left : tensorLeft D p q r a b c =
      tensorLeft D p q r a0 b0 c + tensorLeft D p q r a0 b1 c +
        (tensorLeft D p q r a1 b0 c + tensorLeft D p q r a1 b1 c) := by
    apply fourSum (finiteLeft a0 b0) (finiteLeft a0 b1)
      (finiteLeft a1 b0) (finiteLeft a1 b1)
    intro i
    dsimp only [jacobiLeftTerm, mu_D]
    conv_lhs => rw [aSplit, bSplit]
    simp only [map_add, Pi.add_apply, LinearMap.add_apply, smul_add]
    abel
  have forward : tensorForward D p q r a b c =
      tensorForward D p q r a0 b0 c + tensorForward D p q r a0 b1 c +
        (tensorForward D p q r a1 b0 c + tensorForward D p q r a1 b1 c) := by
    apply fourSum (finiteForward a0 b0) (finiteForward a0 b1)
      (finiteForward a1 b0) (finiteForward a1 b1)
    intro i
    dsimp only [jacobiRightFirstTerm, mu_D]
    conv_lhs => rw [aSplit, bSplit]
    simp only [map_add, Pi.add_apply, LinearMap.add_apply, smul_add]
    abel
  have reverse0 : tensorReverse D p q r a0 b c =
      tensorReverse D p q r a0 b0 c + tensorReverse D p q r a0 b1 c := by
    dsimp only [tensorReverse]
    rw [← finsum_add_distrib (reverse_finite D a0 b0 c p q r)
      (reverse_finite D a0 b1 c p q r)]
    apply finsum_congr
    intro i
    dsimp only [reverseTerm, mu_D]
    conv_lhs => rw [bSplit]
    simp only [map_add, Pi.add_apply, LinearMap.add_apply, smul_add]
  have reverse1 : tensorReverse D p q r a1 (parity D b) c =
      tensorReverse D p q r a1 b0 c - tensorReverse D p q r a1 b1 c := by
    dsimp only [tensorReverse]
    rw [← finsum_sub_distrib (reverse_finite D a1 b0 c p q r)
      (reverse_finite D a1 b1 c p q r)]
    apply finsum_congr
    intro i
    dsimp only [reverseTerm, mu_D]
    conv_lhs => rw [paritySplit]
    simp only [map_sub, Pi.sub_apply, LinearMap.sub_apply, smul_sub]
  have law : tensorLeft D p q r a b c = tensorForward D p q r a b c -
      epsilon r • (tensorReverse D p q r a0 b c +
        tensorReverse D p q r a1 (parity D b) c) := by
    rw [left, forward, reverse0, reverse1,
      homogeneous_borcherds D a0 b0 c 0 0 (even a) (even b),
      homogeneous_borcherds D a0 b1 c 0 1 (even a) (odd b),
      homogeneous_borcherds D a1 b0 c 1 0 (odd a) (even b),
      homogeneous_borcherds D a1 b1 c 1 1 (odd a) (odd b)]
    norm_num only [Nat.zero_mul, Nat.mul_zero, Nat.one_mul,
      pow_zero, pow_one, mul_one, mul_neg, mul_one]
    module
  have combinedFinite : Function.HasFiniteSupport (fun i : ℕ =>
      epsilon r • (reverseTerm D p q r a0 b c i +
        reverseTerm D p q r a1 (parity D b) c i)) :=
    (right0Finite.add right1Finite).smul_right (fun _ => epsilon r)
  have rhs :
      (∑ᶠ i : ℕ, w i •
        (mu_D D a (p + r - i) (mu_D D b (q + i) c) -
          epsilon r •
            (mu_D D b (q + r - i) (mu_D D a0 (p + i) c) +
              mu_D D (parity D b) (q + r - i) (mu_D D a1 (p + i) c)))) =
        tensorForward D p q r a b c - epsilon r •
          (tensorReverse D p q r a0 b c +
            tensorReverse D p q r a1 (parity D b) c) := by
    have pointwise (i : ℕ) :
        w i • (mu_D D a (p + r - i) (mu_D D b (q + i) c) -
          epsilon r •
            (mu_D D b (q + r - i) (mu_D D a0 (p + i) c) +
              mu_D D (parity D b) (q + r - i) (mu_D D a1 (p + i) c))) =
        jacobiRightFirstTerm D p q r a b c i -
          epsilon r • (reverseTerm D p q r a0 b c i +
            reverseTerm D p q r a1 (parity D b) c i) := by
      dsimp only [w, jacobiRightFirstTerm, reverseTerm]
      module
    simp_rw [pointwise]
    have factor := smul_finsum' (epsilon r) (right0Finite.add right1Finite)
    simp only [Pi.add_apply] at factor
    rw [finsum_sub_distrib (finiteForward a b) combinedFinite,
      ← factor, finsum_add_distrib right0Finite right1Finite]
  exact law.trans rhs.symm

end
end D5.S3.VertexAlgebra.LatticeMatterGhostBorcherds

