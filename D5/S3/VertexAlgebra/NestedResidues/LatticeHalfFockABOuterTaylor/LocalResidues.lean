/- GID: D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockABOuterTaylor/LocalResidues
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/NestedResidues/LatticeHalfFockABOuterTaylor/LocalResidues
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Signed local residues and the finite original Taylor convolution. -/
import D5.S3.VertexAlgebra.NestedResidues.BinaryLaurentEvaluation

/-! Complete-field residue calculus with the original signed Laurent powers.
Classical local-field calculus: Matsuo--Nagatomo; twisted lattice setting:
Bakalov--Kac, math/0402315. Hahn operations: mathlib, Apache 2.0.
This is a formalized synthesis and application, with no literature novelty claim.
Consumed boundary helpers are not independent mathematical endpoints.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000


namespace D5.S3.VertexAlgebra.LatticeHalfFockNestedQReadout
open LatticeHalfFockLeftCurrentTransport LatticeHalfFockClearedTaylorReadout
open NestedResidues.ContextualKernelExtraction
open UniformGradedLocalCorrelator
open SupportedFieldWords.OrderedWords SupportedFieldWords.OrderedDistribution
open CollisionRationalExpansions.OrderedRationalExpansion
open LatticeGeneratingFieldLocality LatticeHalfFockChargedTensorCoefficients
open LatticeFiniteNegativeGeneration LatticeSugawaraCurrents
open scoped BigOperators VertexOperator
open LatticeHalfFockChargedCollision.WeightedLocalCorrelator
noncomputable section


def orderedResidueWeight (k B : ℤ) : ℂ :=
  if B < 0 then BinomialKernelDelta.chooseSign k (-B - 1).toNat else 0

private theorem signed_residue_balance (A B k : ℤ) (total : A + B + k = -2) :
    fusedResidueWeight A k = orderedResidueWeight k B -
      StateFieldResidueReconstruction.epsilon k * orderedResidueWeight k A := by
  by_cases negative : k < 0
  · let m := (-k - 1).toNat
    have kform : k = -(m : ℤ) - 1 := by dsimp [m]; omega
    have h := LatticeHalfFockClearedTaylorReadout.signed_kernel_choose m A
    have bform : B = (m : ℤ) - A - 1 := by omega
    simpa only [fusedResidueWeight, orderedResidueWeight, if_pos negative,
      kform, if_pos (show -(m : ℤ) - 1 < 0 by omega), bform, show -((m : ℤ) - A - 1) - 1 = A - m by omega,
      show (m : ℤ) - A - 1 < 0 ↔ 0 ≤ A - m by omega,
      show A < 0 ↔ 0 ≤ -A - 1 by omega,
      show -(-(m : ℤ) - 1) - 1 = m by omega, Int.toNat_natCast] using h.symm
  · obtain ⟨degree, kform⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ k by omega)
    subst k
    have chooseNat (j : ℕ) : BinomialKernelDelta.chooseSign (degree : ℤ) j =
        (-1 : ℂ) ^ j * (degree.choose j : ℂ) := by
      simp [BinomialKernelDelta.chooseSign, Ring.choose_natCast]
    unfold fusedResidueWeight orderedResidueWeight
    rw [if_neg (by omega)]
    by_cases hA : A < 0
    · by_cases hB : B < 0
      · rw [if_pos hA, if_pos hB, chooseNat, chooseNat]
        let a := (-A - 1).toNat
        let b := (-B - 1).toNat
        have split : degree = a + b := by dsimp [a, b]; omega
        have symmetry : degree.choose b = degree.choose a := by
          rw [split, Nat.choose_symm_add]
        have sign : StateFieldResidueReconstruction.epsilon (degree : ℤ) *
            (-1 : ℂ) ^ a = (-1 : ℂ) ^ b := by
          rw [StateFieldResidueReconstruction.epsilon, zpow_natCast, split,
            pow_add]
          have square : (-1 : ℂ) ^ a * (-1 : ℂ) ^ a = 1 := by
            rw [← mul_pow]; norm_num
          calc
            _ = ((-1 : ℂ) ^ a * (-1 : ℂ) ^ a) * (-1 : ℂ) ^ b := by ring
            _ = _ := by rw [square, one_mul]
        change 0 = (-1 : ℂ) ^ b * (degree.choose b : ℂ) -
          StateFieldResidueReconstruction.epsilon (degree : ℤ) *
            ((-1 : ℂ) ^ a * (degree.choose a : ℂ))
        rw [symmetry, ← mul_assoc, sign, sub_self]
      · rw [if_pos hA, if_neg hB, chooseNat,
          Nat.choose_eq_zero_of_lt (show degree < (-A - 1).toNat by omega)]
        simp
    · rw [if_neg hA]
      by_cases hB : B < 0
      · rw [if_pos hB, chooseNat,
          Nat.choose_eq_zero_of_lt (show degree < (-B - 1).toNat by omega)]
        simp
      · simp [if_neg hB]

theorem finite_collision_balance (P : LabelledPolynomial ℂ 3)
    (gamma d r : ℤ) (L M N degree : ℕ)
    (antidiagonal : (degree : ℤ) = L + M + N - d - r - 2) :
    (∑ u ∈ Finset.range (degree + 1), collisionTaylor P gamma u (degree - u) *
      fusedResidueWeight ((u : ℤ) - M) (d - L)) =
    (∑ u ∈ Finset.range (degree + 1), collisionTaylor P gamma u (degree - u) *
      orderedResidueWeight (d - L) ((degree - u : ℕ) + r - N)) -
    StateFieldResidueReconstruction.epsilon (d - L) *
      ∑ u ∈ Finset.range (degree + 1), collisionTaylor P gamma u (degree - u) *
        orderedResidueWeight (d - L) ((u : ℤ) - M) := by
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro u hu
  have bound : u ≤ degree := by simpa using Finset.mem_range.mp hu
  have total : ((u : ℤ) - M) + ((degree - u : ℕ) + r - N) + (d - L) = -2 := by
    rw [Int.natCast_sub bound]
    omega
  rw [signed_residue_balance _ _ _ total]
  ring

end
end D5.S3.VertexAlgebra.LatticeHalfFockNestedQReadout

namespace D5.S3.VertexAlgebra.LatticeHalfFockOuterTaylorEvaluation
open LatticeHalfFockLeftCurrentTransport LatticeHalfFockNestedQReadout
open UniformGradedLocalCorrelator
open SupportedFieldWords.OrderedWords SupportedFieldWords.OrderedDistribution
open CollisionRationalExpansions.OrderedRationalExpansion
open CollisionLaurentKernels.LaurentCollision
open LatticeGeneratingFieldLocality LatticeHalfFockChargedTensorCoefficients
open LatticeFiniteNegativeGeneration LatticeSugawaraCurrents
open scoped BigOperators VertexOperator RatFunc
open LatticeHalfFockChargedCollision.WeightedLocalCorrelator
noncomputable section


/-- Exact finite convolution of the original signed diagonal weights with
an independent signed pole. The arbitrary sequence is retained on its
original Taylor coordinate. -/
private theorem finite_signed_outer_convolution (d k : ℤ) (t : ℕ) (F : ℕ → ℂ) :
    (∑ j ∈ Finset.range (t + 1), BinomialKernelDelta.chooseSign d j *
      ∑ u ∈ Finset.range (t - j + 1),
        F u * BinomialKernelDelta.chooseSign k (t - j - u)) =
    ∑ u ∈ Finset.range (t + 1),
      F u * BinomialKernelDelta.chooseSign (d + k) (t - u) := by
  let S (p : ℤ) : PowerSeries ℂ :=
    PowerSeries.rescale (-1) (PowerSeries.binomialSeries ℂ p)
  have coeff (p : ℤ) (u : ℕ) :
      PowerSeries.coeff u (S p) = BinomialKernelDelta.chooseSign p u := by
    simp [S, PowerSeries.coeff_rescale, PowerSeries.binomialSeries_coeff,
      BinomialKernelDelta.chooseSign, zsmul_eq_mul]
  have add (p q : ℤ) : S (p + q) = S p * S q := by
    simp [S, PowerSeries.binomialSeries_add]
  have eqn : S d * (PowerSeries.mk F * S k) = PowerSeries.mk F * S (d + k) := by
    rw [add]
    ring
  have h := congrArg (PowerSeries.coeff t) eqn
  simp only [PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, coeff,
    PowerSeries.coeff_mk] at h
  exact h


/- proof_shape: finite_forward_outer_taylor: content
   admission_basis: escape-witness
   escape_witness: the finite signed convolution is reindexed onto the original Taylor triangle.
   consumer: forward_weighted_identity -/
/-- The finite signed forward outer Taylor reindexing, including empty
negative antidiagonals. The pole order L is independent of the inner cutoff. -/
theorem finite_forward_outer_taylor (P : LabelledPolynomial ℂ 3)
    (gamma d degree : ℤ) (L t : ℕ) :
    (∑ j ∈ Finset.range (t + 1), BinomialKernelDelta.chooseSign d j *
      ∑ v ∈ Finset.range (t - j + 1),
        (if (v : ℤ) ≤ degree then collisionTaylor P gamma (degree - v).toNat v else 0) *
          BinomialKernelDelta.chooseSign (-(L : ℤ)) (t - j - v)) =
      ∑ u ∈ Finset.range (degree + 1).toNat,
        collisionTaylor P gamma u (degree - u).toNat *
          orderedResidueWeight (d - L) (degree - u - t - 1) := by
  rw [finite_signed_outer_convolution]
  rw [show d + -(L : ℤ) = d - L by omega]
  by_cases negative : degree < 0
  · have empty : (degree + 1).toNat = 0 := by omega
    simp only [empty, Finset.range_zero, Finset.sum_empty]
    apply Finset.sum_eq_zero
    intro v member
    rw [if_neg (by omega), zero_mul]
  · obtain ⟨N, rfl⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ degree by omega)
    have cutoff : ((N : ℤ) + 1).toNat = N + 1 := by omega
    rw [cutoff]
    have first :
        (∑ v ∈ Finset.range (t + 1),
          (if (v : ℤ) ≤ (N : ℤ) then collisionTaylor P gamma ((N : ℤ) - v).toNat v else 0) *
            BinomialKernelDelta.chooseSign (d - L) (t - v)) =
        ∑ v ∈ Finset.range (N + 1), if v ≤ t then
          collisionTaylor P gamma (N - v) v *
            BinomialKernelDelta.chooseSign (d - L) (t - v) else 0 := by
      calc
        _ = ∑ v ∈ Finset.range (t + 1), if v ≤ N then
            collisionTaylor P gamma (N - v) v *
              BinomialKernelDelta.chooseSign (d - L) (t - v) else 0 := by
          apply Finset.sum_congr rfl
          intro v hv
          split_ifs with h h'
          · congr 2
            omega
          · omega
          · omega
          · simp
        _ = _ := finite_rectangle_cut t N _
    rw [first]
    conv_rhs => rw [← Finset.sum_range_reflect]
    apply Finset.sum_congr rfl
    intro v member
    have bound : v ≤ N := by simpa using Finset.mem_range.mp member
    have index : (N : ℤ) - (N - v : ℕ) = v := by omega
    simp only [Nat.add_sub_cancel] 
    rw [index, Int.toNat_natCast]
    unfold orderedResidueWeight
    by_cases inside : v ≤ t
    · rw [if_pos inside, if_pos (by omega), show (-(↑v - ↑t - 1) - 1 : ℤ).toNat = t - v by omega]
    · rw [if_neg inside, if_neg (by omega), mul_zero]

end
end D5.S3.VertexAlgebra.LatticeHalfFockOuterTaylorEvaluation

namespace D5.S3.VertexAlgebra.NestedResidues.LatticeHalfFockABLocalResidue
open LatticeHalfFockLeftCurrentTransport LatticeHalfFockNestedQReadout
open LatticeHalfFockOuterTaylorEvaluation UniformGradedLocalCorrelator
open LatticeGeneratingFieldLocality LatticeHalfFockChargedTensorCoefficients
open LatticeFiniteNegativeGeneration LatticeSugawaraCurrents
open CollisionRationalExpansions.OrderedRationalExpansion
open LabelledRationalClearing.GlobalRationalCurry
open LabelledRationalClearing.PairDifferenceLocalization
  (remainingVariable remainingVariable_injective curry_variable_z
    curry_variable_remaining curryPolynomial_single)
open OrderedCollisionCoordinates.LocalResidueCurrying
open OrderedCollisionCoordinates.OrderedCoefficientCompatibility
open scoped BigOperators VertexOperator RatFunc
open LatticeHalfFockChargedCollision.WeightedLocalCorrelator
noncomputable section


def monomialConstant (e : Exponent 3) (c : ℂ) : ABField :=
  algebraMap _ ABField (AddMonoidAlgebra.single (fun j : Remaining (1 : Fin 3) => e j.val) c)


private theorem translate_variable {E : Type*} [Field E] (a : E) :
    IsFractionRing.ringEquivOfRingEquiv
      (Polynomial.algEquivAevalXAddC a).toRingEquiv (RatFunc.X : RatFunc E) =
        RatFunc.X + RatFunc.C a := by
  rw [← RatFunc.algebraMap_X, IsFractionRing.ringEquivOfRingEquiv_algebraMap]
  simp [Polynomial.algEquivAevalXAddC_apply]

private theorem ab_local_monomial (D : LatticeData) (a b : Carrier D)
    (K : ℕ) (e : Exponent 3) (c : ℂ) (w : ℤ) :
    localRational ℂ (1 : Fin 3) ⟨2, by decide⟩
      (LabelledRationalClearing.WeightedActualQ.globalDiagonal ℂ (1 : Fin 3)
        ⟨2, by decide⟩ ^ w * originalRational D a b K (AddMonoidAlgebra.single e c)) =
      RatFunc.C (monomialConstant e c * (y - z) ^ (-((vectorFrequencyBound D b + 1 : ℕ) : ℤ)) *
          (-1 : ABField) ^ (-((vectorFrequencyBound D a + 1 : ℕ) : ℤ))) *
        (RatFunc.X + RatFunc.C z) ^ e 1 * RatFunc.X ^ (w - K) *
        (RatFunc.X + RatFunc.C (z - y)) ^ (-((vectorFrequencyBound D a + 1 : ℕ) : ℤ)) := by
  classical
  have pairs : labelledPairs 3 = {(0, 1), (0, 2), (1, 2)} := by decide
  have clear : LatticeHalfFockChargedCollision.WeightedLocalCorrelator.weightedClearingPolynomial (threeOrders D a b K) =
      pairPolynomial (0 : Fin 3) 1 ^ (vectorFrequencyBound D a + 1) *
      pairPolynomial (0 : Fin 3) 2 ^ (vectorFrequencyBound D b + 1) *
      pairPolynomial (1 : Fin 3) 2 ^ K := by
    simp [LatticeHalfFockChargedCollision.WeightedLocalCorrelator.weightedClearingPolynomial, pairs, threeOrders]
    ring
  unfold originalRational
  rw [clear]
  simp only [localRational, RingHom.comp_apply, map_mul, map_div₀, map_pow, map_zpow₀,
    LabelledRationalClearing.WeightedActualQ.globalDiagonal,
    curryRational, IsFractionRing.lift_algebraMap]
  rw [curryPolynomial_single]
  have mapv := curry_variable_z ℂ (1 : Fin 3)
  have mapy := curry_variable_remaining ℂ (1 : Fin 3) ⟨0, by decide⟩
  have mapz := curry_variable_remaining ℂ (1 : Fin 3) ⟨2, by decide⟩
  have mapvl := mapv
  have mapzl := mapz
  change curryPolynomial ℂ (1 : Fin 3) (UniformGradedLocalCorrelator.variablePolynomial 1) = _
    at mapv
  change curryPolynomial ℂ (1 : Fin 3) (UniformGradedLocalCorrelator.variablePolynomial 0) = _
    at mapy
  change curryPolynomial ℂ (1 : Fin 3) (UniformGradedLocalCorrelator.variablePolynomial 2) = _
    at mapz
  simp only [UniformGradedLocalCorrelator.pairPolynomial,
    LabelledRationalClearing.PairDifferenceLocalization.pairPolynomial,
    map_sub, mapv, mapy, mapz, mapvl, mapzl]
  simp only [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    map_mul, map_zpow₀, OrderedCollisionResidues.LocalResidueLinear.translate_constant]
  simp only [translate, translate_variable]
  change ((RatFunc.X + RatFunc.C z - RatFunc.C z) ^ w *
    (RatFunc.C (monomialConstant e c) * (RatFunc.X + RatFunc.C z) ^ e 1 /
      ((RatFunc.C y - (RatFunc.X + RatFunc.C z)) ^ (vectorFrequencyBound D a + 1) *
        (RatFunc.C y - RatFunc.C z) ^ (vectorFrequencyBound D b + 1) *
        (RatFunc.X + RatFunc.C z - RatFunc.C z) ^ K))) = _
  rw [show RatFunc.C y - (RatFunc.X + RatFunc.C z) =
      RatFunc.C (-1 : ABField) * (RatFunc.X + RatFunc.C (z - y)) by
    simp only [map_neg, map_one, map_sub]; ring]
  simp only [add_sub_cancel_right, mul_pow, ← map_sub]
  rw [zpow_sub₀ RatFunc.X_ne_zero]
  simp only [zpow_neg, zpow_natCast, div_eq_mul_inv, mul_inv_rev]
  ring

/-- Finite complete A/B residue of one signed Laurent monomial. The zero
branch is the genuine rational high-weight tail, independent of actual locality. -/
def abMonomialValue (D : LatticeData) (a b : Carrier D) (K : ℕ)
    (e : Exponent 3) (c : ℂ) (w : ℤ) : ABField :=
  let L : ℤ := vectorFrequencyBound D a + 1
  let M : ℤ := vectorFrequencyBound D b + 1
  if w - (K : ℤ) < 0 then
    (monomialConstant e c * (y - z) ^ (-M) * (-1 : ABField) ^ (-L)) *
      (z ^ e 1 * (z - y) ^ (-L)) *
      ∑ u ∈ Finset.range ((-(w - (K : ℤ)) - 1).toNat + 1),
        z⁻¹ ^ u * ((Ring.choose (e 1) u : ℤ) : ABField) *
          ((z - y)⁻¹ ^ ((-(w - (K : ℤ)) - 1).toNat - u) *
            ((Ring.choose (-L) ((-(w - (K : ℤ)) - 1).toNat - u) : ℤ) : ABField))
  else 0

private theorem z_nonzero : z ≠ 0 := by
  change algebraMap (CoefficientPolynomial ℂ (1 : Fin 3)) ABField
    (AddMonoidAlgebra.single (Pi.single ⟨2, by decide⟩ (1 : ℤ)) (1 : ℂ)) ≠ 0
  exact (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr (by simp)

private theorem zy_nonzero : z - y ≠ 0 := by
  apply sub_ne_zero.mpr
  intro h
  have labels := remainingVariable_injective ℂ (1 : Fin 3) h
  have impossible := congrArg Subtype.val labels
  exact (by decide : (2 : Fin 3) ≠ 0) impossible

private theorem ab_monomial_residue (D : LatticeData) (a b : Carrier D)
    (K : ℕ) (e : Exponent 3) (c : ℂ) (w : ℤ) :
    localResidue ℂ (1 : Fin 3) ⟨2, by decide⟩
      (LabelledRationalClearing.WeightedActualQ.globalDiagonal ℂ (1 : Fin 3)
        ⟨2, by decide⟩ ^ w * originalRational D a b K (AddMonoidAlgebra.single e c)) =
      abMonomialValue D a b K e c w := by
  classical
  unfold localResidue
  rw [ab_local_monomial]
  have mapC (h : ABField) : algebraMap (RatFunc ABField) (LaurentSeries ABField) (RatFunc.C h) =
      HahnSeries.C h := by
    rw [← RatFunc.algebraMap_C,
      ← IsScalarTower.algebraMap_apply (Polynomial ABField) (RatFunc ABField)
        (LaurentSeries ABField)]
    simp [Polynomial.algebraMap_hahnSeries_apply]
  simp only [map_mul, map_zpow₀, map_add, RatFunc.coe_X]
  simp_rw [mapC]
  simp only [← map_zpow₀ (HahnSeries.C : ABField →+* LaurentSeries ABField)]
  rw [← map_mul (HahnSeries.C : ABField →+* LaurentSeries ABField),
    ← map_mul (HahnSeries.C : ABField →+* LaurentSeries ABField)]
  rw [show ∀ (h : ABField) (p k q : ℤ),
      HahnSeries.C h * (HahnSeries.single 1 1 + HahnSeries.C z) ^ p *
          (HahnSeries.single 1 1 : LaurentSeries ABField) ^ k *
          (HahnSeries.single 1 1 + HahnSeries.C (z - y)) ^ q =
        HahnSeries.single k h * ((HahnSeries.single 1 1 + HahnSeries.C z) ^ p *
          (HahnSeries.single 1 1 + HahnSeries.C (z - y)) ^ q) by
    intro h p k q
    rw [← RatFunc.single_zpow, HahnSeries.C_apply]
    calc
      _ = (HahnSeries.single 0 h * HahnSeries.single k (1 : ABField)) *
          ((HahnSeries.single 1 1 + HahnSeries.C z) ^ p *
            (HahnSeries.single 1 1 + HahnSeries.C (z - y)) ^ q) := by ring
      _ = _ := by rw [HahnSeries.single_mul_single, zero_add, mul_one]
  ]
  exact local_laurent_pair_residue z (z - y) _ z_nonzero zy_nonzero _ _ _

/-- The COMPLETE source/source local residue of the original finite Laurent
numerator, for every signed weight. No original variable exponent is restricted.
In particular every term, hence the complete residue, vanishes for w ≥ K. -/
private theorem ab_laurent_residue (D : LatticeData) (a b : Carrier D)
    (K : ℕ) (P : LabelledPolynomial ℂ 3) (w : ℤ) :
    localResidue ℂ (1 : Fin 3) ⟨2, by decide⟩
      (LabelledRationalClearing.WeightedActualQ.globalDiagonal ℂ (1 : Fin 3)
        ⟨2, by decide⟩ ^ w * originalRational D a b K P) =
      ∑ e ∈ P.coeff.support, abMonomialValue D a b K e (P.coeff e) w := by
  classical
  let residue := OrderedCollisionResidues.CollisionResidueMaps.localResidueHom
    ℂ 1 0 (1 : Fin 3) ⟨2, by decide⟩
  have splitP : (∑ e ∈ P.coeff.support, AddMonoidAlgebra.single e (P.coeff e)) = P :=
    AddMonoidAlgebra.sum_coeff_single P
  have splitR :
      LabelledRationalClearing.WeightedActualQ.globalDiagonal ℂ (1 : Fin 3)
          ⟨2, by decide⟩ ^ w * originalRational D a b K P =
      ∑ e ∈ P.coeff.support,
        LabelledRationalClearing.WeightedActualQ.globalDiagonal ℂ (1 : Fin 3)
          ⟨2, by decide⟩ ^ w *
          originalRational D a b K (AddMonoidAlgebra.single e (P.coeff e)) := by
    unfold originalRational
    rw [← Finset.mul_sum, ← Finset.sum_div, ← map_sum, splitP]
  change residue _ = _
  rw [splitR, map_sum]
  apply Finset.sum_congr rfl
  intro e he
  exact ab_monomial_residue D a b K e (P.coeff e) w

/-- The original z mode shift, as a Laurent monomial in the remaining labels. -/
def zShift (ell : ℕ) : ABField :=
  algebraMap (CoefficientPolynomial ℂ (1 : Fin 3)) ABField
    (AddMonoidAlgebra.single (Pi.single ⟨2, by decide⟩ (-(ell : ℤ))) 1)

/-- The COMPLETE binary rational field G, with independent fractional cutoff I.
The ordinary A/B residue is formed before it is multiplied by the z mode shift. -/
def completeAB (s w : ℤ) (I : ℕ) (R : CommonRational ℂ 3) : ABField :=
  ∑ ell ∈ Finset.range ((I : ℤ) - w).toNat,
    algebraMap ℂ ABField (Ring.choose (-(s : ℂ) / 2) ell) * zShift ell *
      localResidue ℂ (1 : Fin 3) ⟨2, by decide⟩
        (LabelledRationalClearing.WeightedActualQ.globalDiagonal ℂ (1 : Fin 3)
          ⟨2, by decide⟩ ^ (w + ell) * R)


private theorem coefficient_shift (reverse : Bool) (ell : ℕ) (F : ABField) (a b : ℤ) :
    let tau : Fin 2 ≃ Remaining (1 : Fin 3) :=
      if reverse then (Equiv.swap 0 1).trans (finSuccAboveEquiv 1) else finSuccAboveEquiv 1
    (coefficientHahn ℂ 1 1 1 tau (zShift ell * F)).coeff
        (SupportedFieldWords.OrderedWords.exponents 2 (if reverse then ![b, a] else ![a, b])) =
      (coefficientHahn ℂ 1 1 1 tau F).coeff
        (SupportedFieldWords.OrderedWords.exponents 2
          (if reverse then ![b + ell, a] else ![a, b + ell])) := by
  dsimp only
  let tau : Fin 2 ≃ Remaining (1 : Fin 3) :=
    if reverse then (Equiv.swap 0 1).trans (finSuccAboveEquiv 1) else finSuccAboveEquiv 1
  have shift : coefficientHahn ℂ 1 1 1 tau (zShift ell) =
      HahnSeries.single (SupportedFieldWords.OrderedWords.exponents 2
        (if reverse then ![-(ell : ℤ), 0] else ![0, -(ell : ℤ)])) 1 := by
    unfold zShift coefficientHahn
    rw [IsFractionRing.lift_algebraMap]
    change SupportedFieldWords.FiniteConvolution.scalarPolynomial
      ((AddMonoidAlgebra.domCongr ℂ ℂ (remainingExponents 1 1 (1 : Fin 3) tau))
        (AddMonoidAlgebra.single (Pi.single ⟨2, by decide⟩ (-(ell : ℤ))) 1)) = _
    rw [AddMonoidAlgebra.domCongr_single,
      SupportedFieldWords.FiniteConvolution.scalarPolynomial_single]
    apply congrArg (fun g =>
      (HahnSeries.single g (1 : ℂ) : HahnSeries (SupportedFieldWords.OrderedWords.Indices 2) ℂ))
    apply congrArg (SupportedFieldWords.OrderedDistribution.exponentAddEquiv 2)
    have h0 : (finSuccAboveEquiv (1 : Fin 3)) (0 : Fin 2) = ⟨0, by decide⟩ := rfl
    have h1 : (finSuccAboveEquiv (1 : Fin 3)) (1 : Fin 2) = ⟨2, by decide⟩ := rfl
    cases reverse <;> ext i <;> fin_cases i <;>
      simp [tau, Equiv.swap_apply_def, h0, h1]
  rw [map_mul, shift, HahnSeries.coeff_single_mul, one_mul]
  congr 1
  change (SupportedFieldWords.OrderedDistribution.exponentAddEquiv 2) _ -
    (SupportedFieldWords.OrderedDistribution.exponentAddEquiv 2) _ =
    (SupportedFieldWords.OrderedDistribution.exponentAddEquiv 2) _
  rw [← map_sub]
  apply congrArg (SupportedFieldWords.OrderedDistribution.exponentAddEquiv 2)
  cases reverse <;> ext i <;> fin_cases i <;> simp

private theorem ab_map_same :
    coefficientHahn ℂ 2 0 (1 : Fin 3) (finSuccAboveEquiv 1) =
      coefficientHahn ℂ 1 1 (1 : Fin 3) (finSuccAboveEquiv 1) := rfl

private theorem source_order_left (s w k l : ℤ) (I : ℕ) (R : CommonRational ℂ 3) :
    lastSourceLocalQ 1 true s w I k l R =
      ∑ ell ∈ Finset.range ((I : ℤ) - w).toNat,
        Ring.choose (-(s : ℂ) / 2) ell *
          (coefficientHahn ℂ 1 1 (1 : Fin 3) (finSuccAboveEquiv 1)
            (localResidue ℂ (1 : Fin 3) ⟨2, by decide⟩
              (LabelledRationalClearing.WeightedActualQ.globalDiagonal ℂ (1 : Fin 3)
                ⟨2, by decide⟩ ^ (w + ell) * R))).coeff
            (SupportedFieldWords.OrderedWords.exponents 2 ![-l - 1, -k + ell - 1]) := by
  rfl

private theorem source_order_right (s w k l : ℤ) (I : ℕ) (R : CommonRational ℂ 3) :
    lastSourceLocalQ 1 false s w I k l R =
      ∑ ell ∈ Finset.range ((I : ℤ) - w).toNat,
        Ring.choose (-(s : ℂ) / 2) ell *
          (coefficientHahn ℂ 1 1 (1 : Fin 3) ((Equiv.swap 0 1).trans (finSuccAboveEquiv 1))
            (localResidue ℂ (1 : Fin 3) ⟨2, by decide⟩
              (LabelledRationalClearing.WeightedActualQ.globalDiagonal ℂ (1 : Fin 3)
                ⟨2, by decide⟩ ^ (w + ell) * R))).coeff
            (SupportedFieldWords.OrderedWords.exponents 2 ![-k + ell - 1, -l - 1]) := by
  rfl

/- proof_shape: ab_complete_remaining_orders: content
   admission_basis: escape-witness
   escape_witness: The signed rational A/B residue is evaluated before its
   finite numerator sum. Its genuine zero tail and the Laurent z mode shift
   identify both remaining Hahn orders of the same complete binary G. -/
set_option maxHeartbeats 1000000 in
-- Keep the complete signed rational coefficient telescope during elaboration.
/-- Both genuine remaining orders of the complete G are evaluated from the
same finite signed A/B residues. I is independent of the denominator cutoff K;
this does not assert an identification with an actual field at a different I. -/
theorem ab_complete_remaining_orders (D : LatticeData) (a b : Carrier D)
    (K I : ℕ) (P : LabelledPolynomial ℂ 3) (s w k l : ℤ) :
    (localResidue ℂ (1 : Fin 3) ⟨2, by decide⟩
      (LabelledRationalClearing.WeightedActualQ.globalDiagonal ℂ (1 : Fin 3)
        ⟨2, by decide⟩ ^ w * originalRational D a b K P) =
      ∑ e ∈ P.coeff.support, abMonomialValue D a b K e (P.coeff e) w) ∧
    ((K : ℤ) ≤ w → localResidue ℂ (1 : Fin 3) ⟨2, by decide⟩
      (LabelledRationalClearing.WeightedActualQ.globalDiagonal ℂ (1 : Fin 3)
        ⟨2, by decide⟩ ^ w * originalRational D a b K P) = 0) ∧
    lastSourceLocalQ 1 true s w I k l (originalRational D a b K P) =
      (coefficientHahn ℂ 2 0 (1 : Fin 3) (finSuccAboveEquiv 1)
        (completeAB s w I (originalRational D a b K P))).coeff
          (SupportedFieldWords.OrderedWords.exponents 2 ![-l - 1, -k - 1]) ∧
    lastSourceLocalQ 1 false s w I k l (originalRational D a b K P) =
      (coefficientHahn ℂ 1 1 (1 : Fin 3) ((Equiv.swap 0 1).trans (finSuccAboveEquiv 1))
        (completeAB s w I (originalRational D a b K P))).coeff
          (SupportedFieldWords.OrderedWords.exponents 2 ![-k - 1, -l - 1]) := by
  classical
  refine ⟨ab_laurent_residue D a b K P w, ?_, ?_, ?_⟩
  · intro high
    rw [ab_laurent_residue]
    apply Finset.sum_eq_zero
    intro e he
    simp only [abMonomialValue, ite_eq_right (show ¬ w - (K : ℤ) < 0 by omega)]
  · rw [source_order_left]
    unfold completeAB
    simp only [map_sum, HahnSeries.coeff_sum, ab_map_same]
    apply Finset.sum_congr rfl
    intro ell hell
    rw [map_mul, map_mul, coefficient_scalar 1 1 1 (finSuccAboveEquiv 1),
      mul_assoc, HahnSeries.C_apply, HahnSeries.coeff_single_mul, sub_zero]
    congr 1
    have shifted := coefficient_shift false ell
      (localResidue ℂ (1 : Fin 3) ⟨2, by decide⟩
        (LabelledRationalClearing.WeightedActualQ.globalDiagonal ℂ (1 : Fin 3)
          ⟨2, by decide⟩ ^ (w + ell) * originalRational D a b K P)) (-l - 1) (-k - 1)
    dsimp only at shifted
    rw [map_mul] at shifted
    simpa only [Bool.false_eq_true, ite_false,
      show -k - 1 + (ell : ℤ) = -k + ell - 1 by omega] using shifted.symm
  · rw [source_order_right]
    unfold completeAB
    simp only [map_sum, HahnSeries.coeff_sum]
    apply Finset.sum_congr rfl
    intro ell hell
    rw [map_mul, map_mul, coefficient_scalar 1 1 1 ((Equiv.swap 0 1).trans (finSuccAboveEquiv 1)),
      mul_assoc, HahnSeries.C_apply, HahnSeries.coeff_single_mul, sub_zero]
    congr 1
    have shifted := coefficient_shift true ell
      (localResidue ℂ (1 : Fin 3) ⟨2, by decide⟩
        (LabelledRationalClearing.WeightedActualQ.globalDiagonal ℂ (1 : Fin 3)
          ⟨2, by decide⟩ ^ (w + ell) * originalRational D a b K P)) (-l - 1) (-k - 1)
    dsimp only at shifted
    rw [map_mul] at shifted
    simpa only [ite_true, show -k - 1 + (ell : ℤ) = -k + ell - 1 by omega] using shifted.symm

private abbrev LaurentImage : Subring ABField :=
  (algebraMap (CoefficientPolynomial ℂ (1 : Fin 3)) ABField).range

private theorem scalar_image (c : ℂ) : algebraMap ℂ ABField c ∈ LaurentImage := by
  refine ⟨algebraMap ℂ (CoefficientPolynomial ℂ (1 : Fin 3)) c, ?_⟩
  exact (IsScalarTower.algebraMap_apply ℂ (CoefficientPolynomial ℂ (1 : Fin 3)) ABField c).symm

private theorem int_image (c : ℤ) : (c : ABField) ∈ LaurentImage := by
  simpa only [map_intCast] using scalar_image (c : ℂ)

private theorem variable_zpow_image (i : Remaining (1 : Fin 3)) (p : ℤ) :
    remainingVariable ℂ (1 : Fin 3) i ^ p ∈ LaurentImage := by
  let m : Multiplicative (Remaining (1 : Fin 3) → ℤ) →* ABField :=
    (algebraMap (CoefficientPolynomial ℂ (1 : Fin 3)) ABField).toMonoidHom.comp
      (AddMonoidAlgebra.of ℂ (Remaining (1 : Fin 3) → ℤ))
  refine ⟨AddMonoidAlgebra.single (p • Pi.single i (1 : ℤ)) 1, ?_⟩
  have h := m.map_zpow (Multiplicative.ofAdd (Pi.single i (1 : ℤ))) p
  change algebraMap (CoefficientPolynomial ℂ (1 : Fin 3)) ABField
    (AddMonoidAlgebra.single (p • (Pi.single i (1 : ℤ) : Remaining (1 : Fin 3) → ℤ)) 1) =
    remainingVariable ℂ (1 : Fin 3) i ^ p at h
  exact h

private theorem sign_zpow_image (p : ℤ) : (-1 : ABField) ^ p ∈ LaurentImage := by
  have h := scalar_image ((-1 : ℂ) ^ p)
  simpa only [map_zpow₀, map_neg, map_one] using h

private theorem yz_nonzero : y - z ≠ 0 := by
  exact sub_ne_zero.mpr (sub_ne_zero.mp zy_nonzero).symm

/-- A pole bound specifies a Laurent numerator on the unchanged original
remaining labels. It makes no assertion about locality of ordered halves. -/
private def HasABPoleBound (H : ℕ) (F : ABField) : Prop :=
  ∃ Q : CoefficientPolynomial ℂ (1 : Fin 3),
    F = algebraMap _ ABField Q / (y - z) ^ H

set_option maxHeartbeats 1000000 in
-- Normalize the full finite signed residue without reducing its original parameters.
private theorem ab_monomial_pole (D : LatticeData) (a b : Carrier D)
    (K : ℕ) (e : Exponent 3) (c : ℂ) (w : ℤ) (H : ℕ)
    (bound : vectorFrequencyBound D a + 1 + (vectorFrequencyBound D b + 1) +
      ((K : ℤ) - w - 1).toNat ≤ H) :
    (y - z) ^ H * abMonomialValue D a b K e c w ∈ LaurentImage := by
  classical
  unfold abMonomialValue
  dsimp only
  split_ifs with low
  · rw [← mul_assoc, Finset.mul_sum]
    apply LaurentImage.sum_mem
    intro u hu
    let L : ℤ := vectorFrequencyBound D a + 1
    let M : ℤ := vectorFrequencyBound D b + 1
    let v : ℕ := (-(w - (K : ℤ)) - 1).toNat - u
    have member := Finset.mem_range.mp hu
    have nonnegative : 0 ≤ (H : ℤ) - M - L - v := by
      dsimp [v, L, M]
      omega
    have oriented (p : ℤ) : (z - y) ^ p = (-1 : ABField) ^ p * (y - z) ^ p := by
      rw [← mul_zpow]
      congr 1
      ring
    have sign : (-1 : ABField) ^ (-L) * (z - y) ^ (-L) = (y - z) ^ (-L) := by
      rw [← mul_zpow]
      congr 1
      ring
    have normalized :
        (y - z) ^ H *
          ((monomialConstant e c * (y - z) ^ (-M) * (-1 : ABField) ^ (-L)) *
            (z ^ e 1 * (z - y) ^ (-L))) *
          (z⁻¹ ^ u * ((Ring.choose (e 1) u : ℤ) : ABField) *
            ((z - y)⁻¹ ^ v * ((Ring.choose (-L) v : ℤ) : ABField))) =
        monomialConstant e c * z ^ e 1 * z ^ (-(u : ℤ)) *
          ((Ring.choose (e 1) u : ℤ) : ABField) *
          ((Ring.choose (-L) v : ℤ) : ABField) * (-1 : ABField) ^ (-(v : ℤ)) *
          (y - z) ^ ((H : ℤ) - M - L - v) := by
      have orient' : (z - y)⁻¹ ^ v =
          (-1 : ABField) ^ (-(v : ℤ)) * ((y - z) ^ v)⁻¹ := by
        calc
          _ = (z - y) ^ (-(v : ℤ)) := by simp only [zpow_neg, zpow_natCast, inv_pow]
          _ = (-1 : ABField) ^ (-(v : ℤ)) * (y - z) ^ (-(v : ℤ)) := oriented _
          _ = _ := congrArg (fun q => (-1 : ABField) ^ (-(v : ℤ)) * q)
            (by simp only [zpow_neg, zpow_natCast])
      rw [orient']
      calc
        _ = monomialConstant e c * z ^ e 1 * (z⁻¹ ^ u) *
            ((Ring.choose (e 1) u : ℤ) : ABField) * ((Ring.choose (-L) v : ℤ) : ABField) *
            (-1 : ABField) ^ (-(v : ℤ)) *
            ((y - z) ^ H * (y - z) ^ (-M) *
              ((-1 : ABField) ^ (-L) * (z - y) ^ (-L)) * ((y - z) ^ v)⁻¹) := by ring
        _ = _ := by
          rw [sign, zpow_sub₀ yz_nonzero, zpow_sub₀ yz_nonzero, zpow_sub₀ yz_nonzero]
          simp only [zpow_neg, zpow_natCast, inv_pow, div_eq_mul_inv]
    change (y - z) ^ H *
      ((monomialConstant e c * (y - z) ^ (-M) * (-1 : ABField) ^ (-L)) *
        (z ^ e 1 * (z - y) ^ (-L))) *
      (z⁻¹ ^ u * ((Ring.choose (e 1) u : ℤ) : ABField) *
        ((z - y)⁻¹ ^ v * ((Ring.choose (-L) v : ℤ) : ABField))) ∈ _
    rw [normalized]
    apply LaurentImage.mul_mem
    · exact LaurentImage.mul_mem
        (LaurentImage.mul_mem
          (LaurentImage.mul_mem
            (LaurentImage.mul_mem
              (LaurentImage.mul_mem ⟨_, rfl⟩ (variable_zpow_image ⟨2, by decide⟩ (e 1)))
              (variable_zpow_image ⟨2, by decide⟩ (-(u : ℤ))))
            (int_image _)) (int_image _)) (sign_zpow_image _)
    · obtain ⟨t, ht⟩ := Int.eq_ofNat_of_zero_le nonnegative
      rw [ht, zpow_natCast]
      apply LaurentImage.pow_mem
      exact LaurentImage.sub_mem
        (by simpa only [zpow_one, y] using variable_zpow_image ⟨0, by decide⟩ 1)
        (by simpa only [zpow_one, z] using variable_zpow_image ⟨2, by decide⟩ 1)
  · simp only [mul_zero]
    exact LaurentImage.zero_mem

/- proof_shape: ab_complete_pole_bound: content
   admission_basis: escape-witness
   escape_witness: Each signed monomial residue has local Taylor degree
   K-w-ell-1. After its COMPLETE residue is formed, multiplication by
   (y-z)^(L+M+(K-w-1).toNat) leaves a Laurent polynomial in the original
   remaining labels. Closure under the finite numerator and fractional sums
   supplies one binary numerator at the asserted pole order. -/
set_option maxHeartbeats 1000000 in
-- Keep the complete signed rational coefficient telescope during elaboration.
/-- The complete binary rational G has the stated pole bound, at the
original P,K and any independent I. In the forward branch w=r+j this is exactly
L+M+(K-r-j-1).toNat. Zero/empty polynomials and signed degrees stay in scope. -/
theorem ab_complete_pole_bound (D : LatticeData) (a b : Carrier D)
    (K I : ℕ) (P : LabelledPolynomial ℂ 3) (s w : ℤ) :
    HasABPoleBound
      (vectorFrequencyBound D a + 1 + (vectorFrequencyBound D b + 1) +
        ((K : ℤ) - w - 1).toNat)
      (completeAB s w I (originalRational D a b K P)) := by
  classical
  let H := vectorFrequencyBound D a + 1 + (vectorFrequencyBound D b + 1) +
    ((K : ℤ) - w - 1).toNat
  have numerator : (y - z) ^ H * completeAB s w I (originalRational D a b K P) ∈
      LaurentImage := by
    unfold completeAB
    rw [Finset.mul_sum]
    apply LaurentImage.sum_mem
    intro ell hell
    have residue : (y - z) ^ H *
        localResidue ℂ (1 : Fin 3) ⟨2, by decide⟩
          (LabelledRationalClearing.WeightedActualQ.globalDiagonal ℂ (1 : Fin 3)
            ⟨2, by decide⟩ ^ (w + ell) * originalRational D a b K P) ∈ LaurentImage := by
      rw [ab_laurent_residue, Finset.mul_sum]
      apply LaurentImage.sum_mem
      intro e he
      apply ab_monomial_pole
      dsimp [H]
      omega
    have shift : zShift ell ∈ LaurentImage := ⟨_, rfl⟩
    convert LaurentImage.mul_mem
      (LaurentImage.mul_mem (scalar_image (Ring.choose (-(s : ℂ) / 2) ell)) shift)
      residue using 1
    ring
  obtain ⟨Q, hQ⟩ := numerator
  refine ⟨Q, ?_⟩
  apply (eq_div_iff (pow_ne_zero _ yz_nonzero)).mpr
  rw [hQ, mul_comm]

end
end D5.S3.VertexAlgebra.NestedResidues.LatticeHalfFockABLocalResidue

