/- GID: D5/S3/Weil/CayleyLaguerre/TruncatedCircleMomentBridge
   generality: G
   mirror-B: D5/B/S3/Weil/TestFunctions/TruncatedCircleMomentBridge
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Represent positive truncated Toeplitz moments by an atomic circle measure. -/

import D5.S3.Weil.TestFunctions.ToeplitzContactSupport
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.InnerProductSpace.JointEigenspace
import Mathlib.Analysis.Matrix.Order

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix MeasureTheory Set
open scoped BigOperators ComplexConjugate ComplexOrder ENNReal NNReal MatrixOrder

namespace D5.S3.Weil.CayleyLaguerre.TruncatedCircleMomentBridge

noncomputable local instance circleMeasurableSpace : MeasurableSpace Circle := borel Circle
local instance circleBorelSpace : BorelSpace Circle := ⟨rfl⟩

theorem truncated_circle_moment_of_posSemidef
    (N : Nat)
    (r : Int -> Complex)
    (hermitian : forall k, r (-k) = star (r k))
    (positive : Matrix.PosSemidef
      (fun j k : Fin (N + 1) => r ((j : Int) - (k : Int)))) :
    exists sigma : FiniteMeasure Circle,
      forall k : Int, k.natAbs <= N ->
        (∫ z : Circle, (z : Complex) ^ (-k) ∂(sigma : Measure Circle)) = r k := by
  classical
  let residualToeplitz : Matrix (Fin (N + 1)) (Fin (N + 1)) Complex :=
    fun j k => r ((j : Int) - (k : Int))
  have residualPositive : residualToeplitz.PosSemidef := positive
  obtain ⟨X, factorization⟩ :=
    CStarAlgebra.nonneg_iff_eq_star_mul_self.mp residualPositive.nonneg
  let V := EuclideanSpace Complex (Fin (N + 1))
  let gramVector : Fin (N + 1) -> V := fun j =>
    WithLp.toLp 2 (fun i => X i j)
  have gramIdentity (j k : Fin (N + 1)) :
      inner Complex (gramVector j) (gramVector k) = residualToeplitz j k := by
    calc
      inner Complex (gramVector j) (gramVector k) =
          ∑ i, star (X i j) * X i k := by
            rw [PiLp.inner_apply]
            simp [gramVector, mul_comm]
      _ = (star X * X) j k := by
            simp [Matrix.mul_apply]
      _ = residualToeplitz j k := by rw [← factorization]
  let sourceVector : Fin N -> V := fun j => gramVector j.castSucc
  let targetVector : Fin N -> V := fun j => gramVector j.succ
  have shiftedGram :
      Matrix.gram Complex sourceVector = Matrix.gram Complex targetVector := by
    ext j k
    simp only [Matrix.gram_apply, sourceVector, targetVector, gramIdentity, residualToeplitz]
    congr 1
    simp
  let sourceCombination : (Fin N -> Complex) →ₗ[Complex] V :=
    Fintype.linearCombination Complex sourceVector
  let targetCombination : (Fin N -> Complex) →ₗ[Complex] V :=
    Fintype.linearCombination Complex targetVector
  have combinationInner (a b : Fin N -> Complex) :
      inner Complex (sourceCombination a) (sourceCombination b) =
        inner Complex (targetCombination a) (targetCombination b) := by
    simp only [sourceCombination, targetCombination, Fintype.linearCombination_apply]
    rw [← Matrix.star_dotProduct_gram_mulVec sourceVector a b]
    rw [← Matrix.star_dotProduct_gram_mulVec targetVector a b]
    rw [shiftedGram]
  have kernelInclusion : sourceCombination.ker <= targetCombination.ker := by
    intro a ha
    rw [LinearMap.mem_ker] at ha ⊢
    apply (inner_self_eq_zero (𝕜 := Complex)).mp
    rw [← combinationInner]
    simp [ha]
  let quotientToTarget :
      ((Fin N -> Complex) ⧸ sourceCombination.ker) →ₗ[Complex] V :=
    sourceCombination.ker.liftQ targetCombination kernelInclusion
  let shiftMap : sourceCombination.range →ₗ[Complex] V :=
    quotientToTarget.comp sourceCombination.quotKerEquivRange.symm.toLinearMap
  have shiftMap_source (a : Fin N -> Complex) :
      shiftMap ⟨sourceCombination a, LinearMap.mem_range_self sourceCombination a⟩ =
        targetCombination a := by
    simp only [shiftMap, LinearMap.comp_apply, quotientToTarget]
    change sourceCombination.ker.liftQ targetCombination kernelInclusion
      (sourceCombination.quotKerEquivRange.symm
        ⟨sourceCombination a, LinearMap.mem_range_self sourceCombination a⟩) = _
    rw [LinearMap.quotKerEquivRange_symm_apply_image]
    rfl
  have shiftMap_inner (x y : sourceCombination.range) :
      inner Complex (shiftMap x) (shiftMap y) = inner Complex x y := by
    obtain ⟨a, ha⟩ := x.property
    obtain ⟨b, hb⟩ := y.property
    change inner Complex (shiftMap x) (shiftMap y) = inner Complex (x : V) (y : V)
    let xa : sourceCombination.range :=
      ⟨sourceCombination a, LinearMap.mem_range_self sourceCombination a⟩
    let yb : sourceCombination.range :=
      ⟨sourceCombination b, LinearMap.mem_range_self sourceCombination b⟩
    have hxa : x = xa := Subtype.ext ha.symm
    have hyb : y = yb := Subtype.ext hb.symm
    rw [hxa, hyb]
    change inner Complex (shiftMap xa) (shiftMap yb) =
      inner Complex (sourceCombination a) (sourceCombination b)
    rw [shiftMap_source, shiftMap_source]
    exact combinationInner a b |>.symm
  let shiftIsometry : sourceCombination.range →ₗᵢ[Complex] V :=
    LinearMap.isometryOfInner (𝕜 := Complex) (E := sourceCombination.range)
      (E' := V) shiftMap shiftMap_inner
  let extendedShift : V →ₗᵢ[Complex] V := shiftIsometry.extend
  have extendedShiftSurjective : Function.Surjective extendedShift :=
    LinearMap.surjective_of_injective extendedShift.injective
  let unitaryShift : V ≃ₗᵢ[Complex] V :=
    LinearIsometryEquiv.ofSurjective extendedShift extendedShiftSurjective
  have shiftAction (j : Fin N) :
      unitaryShift (gramVector j.castSucc) = gramVector j.succ := by
    let a : Fin N -> Complex := Pi.single j 1
    have sourceEval : sourceCombination a = gramVector j.castSucc := by
      simp [sourceCombination, sourceVector, a]
    have targetEval : targetCombination a = gramVector j.succ := by
      simp [targetCombination, targetVector, a]
    let s : sourceCombination.range :=
      ⟨gramVector j.castSucc, ⟨a, sourceEval⟩⟩
    change extendedShift (gramVector j.castSucc) = gramVector j.succ
    calc
      extendedShift (gramVector j.castSucc) = shiftIsometry s := by
        exact LinearIsometry.extend_apply shiftIsometry s
      _ = shiftMap s := rfl
      _ = targetCombination a := by
        rw [show s = ⟨sourceCombination a,
          LinearMap.mem_range_self sourceCombination a⟩ from Subtype.ext sourceEval.symm]
        exact shiftMap_source a
      _ = gramVector j.succ := targetEval
  have orbitIdentity (k : Nat) (hk : k <= N) :
      (unitaryShift ^[k]) (gramVector 0) =
        gramVector ⟨k, Nat.lt_succ_of_le hk⟩ := by
    induction k with
    | zero => simp
    | succ k ih =>
        have hkN : k < N := Nat.lt_of_succ_le hk
        let j : Fin N := ⟨k, hkN⟩
        rw [Function.iterate_succ_apply']
        rw [ih (Nat.le_of_lt hkN)]
        have hsource : (⟨k, Nat.lt_succ_of_le (Nat.le_of_lt hkN)⟩ : Fin (N + 1)) =
            j.castSucc := Fin.ext rfl
        rw [hsource, shiftAction]
        apply congrArg gramVector
        apply Fin.ext
        rfl
  let U : V →ₗ[Complex] V := unitaryShift.toLinearMap
  let Uinv : V →ₗ[Complex] V := unitaryShift.symm.toLinearMap
  let realPart : V →ₗ[Complex] V :=
    (2 : Complex)⁻¹ • (U + Uinv)
  let imaginaryPart : V →ₗ[Complex] V :=
    (2 * Complex.I)⁻¹ • (U - Uinv)
  have realPartSymmetric : realPart.IsSymmetric := by
    intro x y
    simp only [realPart, LinearMap.smul_apply, LinearMap.add_apply,
      inner_smul_left, inner_add_left, inner_smul_right, inner_add_right]
    have innerU : inner Complex (U x) y = inner Complex x (Uinv y) :=
      unitaryShift.inner_map_eq_flip x y
    have innerUinv : inner Complex (Uinv x) y = inner Complex x (U y) :=
      unitaryShift.symm.inner_map_eq_flip x y
    rw [innerU, innerUinv]
    simp only [map_inv₀, map_ofNat]
    ring
  have imaginaryPartSymmetric : imaginaryPart.IsSymmetric := by
    intro x y
    simp only [imaginaryPart, LinearMap.smul_apply, LinearMap.sub_apply,
      inner_smul_left, inner_sub_left, inner_smul_right, inner_sub_right]
    have innerU : inner Complex (U x) y = inner Complex x (Uinv y) :=
      unitaryShift.inner_map_eq_flip x y
    have innerUinv : inner Complex (Uinv x) y = inner Complex x (U y) :=
      unitaryShift.symm.inner_map_eq_flip x y
    rw [innerU, innerUinv]
    rw [map_inv₀, map_mul, map_ofNat, Complex.conj_I]
    ring
  have realImaginaryCommute : Commute realPart imaginaryPart := by
    have commuteInverse : Commute U Uinv := by
      rw [Commute]
      apply LinearMap.ext
      intro x
      simp [U, Uinv]
    have sumDiff : Commute (U + Uinv) (U - Uinv) := by
      exact ((Commute.refl U).sub_right commuteInverse).add_left
        (commuteInverse.symm.sub_right (Commute.refl Uinv))
    exact (sumDiff.smul_left (2 : Complex)⁻¹).smul_right (2 * Complex.I)⁻¹
  let JointIndex := Module.End.Eigenvalues imaginaryPart ×
    Module.End.Eigenvalues realPart
  let jointSpace : JointIndex -> Submodule Complex V := fun i =>
    Module.End.eigenspace realPart (i.2 : Complex) ⊓
      Module.End.eigenspace imaginaryPart (i.1 : Complex)
  have jointOrthogonal : OrthogonalFamily Complex (fun i => jointSpace i)
      (fun i => (jointSpace i).subtypeₗᵢ) := by
    apply OrthogonalFamily.of_pairwise
    intro i j hij v hv w hw
    have hCoordinate : (i.1 : Complex) ≠ (j.1 : Complex) ∨
        (i.2 : Complex) ≠ (j.2 : Complex) := by
      by_contra h
      push Not at h
      exact hij (Prod.ext (Subtype.ext h.1) (Subtype.ext h.2))
    change v ∈ Module.End.eigenspace realPart (i.2 : Complex) ⊓
      Module.End.eigenspace imaginaryPart (i.1 : Complex) at hv
    change w ∈ Module.End.eigenspace realPart (j.2 : Complex) ⊓
      Module.End.eigenspace imaginaryPart (j.1 : Complex) at hw
    obtain hFirst | hSecond := hCoordinate
    · exact imaginaryPartSymmetric.orthogonalFamily_eigenspaces.pairwise
        hFirst hv.2 w hw.2
    · exact realPartSymmetric.orthogonalFamily_eigenspaces.pairwise
        hSecond hv.1 w hw.1
  have jointSpacesSpan : (⨆ i, jointSpace i) = ⊤ := by
    apply top_unique
    rw [← realPartSymmetric.iSup_iSup_eigenspace_inf_eigenspace_eq_top_of_commute
      imaginaryPartSymmetric realImaginaryCommute]
    apply iSup_le
    intro a
    apply iSup_le
    intro b
    by_cases ha : Module.End.HasEigenvalue realPart a
    · by_cases hb : Module.End.HasEigenvalue imaginaryPart b
      · let i : JointIndex := (⟨b, hb⟩, ⟨a, ha⟩)
        convert le_iSup (fun i : JointIndex => jointSpace i) i using 1
        · rfl
      · rw [Module.End.hasEigenvalue_iff.not_left.mp hb]
        exact (inf_le_right :
          (Module.End.eigenspace realPart a ⊓ (⊥ : Submodule Complex V)) ≤ ⊥).trans bot_le
    · rw [Module.End.hasEigenvalue_iff.not_left.mp ha]
      exact (inf_le_left :
        ((⊥ : Submodule Complex V) ⊓ Module.End.eigenspace imaginaryPart b) ≤ ⊥).trans bot_le
  have jointDecomposition : DirectSum.IsInternal jointSpace := by
    apply jointOrthogonal.isInternal_iff.mpr
    rw [Submodule.orthogonal_eq_bot_iff, jointSpacesSpan]
  have finrankV : Module.finrank Complex V = N + 1 := by simp [V]
  let eigenbasis : OrthonormalBasis (Fin (N + 1)) Complex V :=
    jointDecomposition.subordinateOrthonormalBasis finrankV jointOrthogonal
  let jointEigenvalue : Fin (N + 1) -> JointIndex := fun i =>
    jointDecomposition.subordinateOrthonormalBasisIndex finrankV i jointOrthogonal
  have eigenbasisJoint (i : Fin (N + 1)) :
      eigenbasis i ∈ jointSpace (jointEigenvalue i) := by
    exact jointDecomposition.subordinateOrthonormalBasis_subordinate
      finrankV i jointOrthogonal
  let spectralPointValue : Fin (N + 1) -> Complex := fun i =>
    (jointEigenvalue i).2.val + Complex.I * (jointEigenvalue i).1.val
  have unitary_eq_parts (x : V) :
      U x = realPart x + Complex.I • imaginaryPart x := by
    have coefficientIdentity :
        Complex.I * (2 * Complex.I)⁻¹ = (2 : Complex)⁻¹ := by
      field_simp
    simp only [realPart, imaginaryPart, LinearMap.smul_apply, LinearMap.add_apply,
      LinearMap.sub_apply, smul_smul, coefficientIdentity]
    module
  have eigenAction (i : Fin (N + 1)) :
      unitaryShift (eigenbasis i) = spectralPointValue i • eigenbasis i := by
    have hJoint := eigenbasisJoint i
    change eigenbasis i ∈
      Module.End.eigenspace realPart ((jointEigenvalue i).2 : Complex) ⊓
      Module.End.eigenspace imaginaryPart ((jointEigenvalue i).1 : Complex) at hJoint
    have hReal := Module.End.mem_eigenspace_iff.mp hJoint.1
    have hImaginary := Module.End.mem_eigenspace_iff.mp hJoint.2
    change U (eigenbasis i) = _
    rw [unitary_eq_parts, hReal, hImaginary]
    simp only [spectralPointValue, add_smul, mul_smul]
  have spectralPointNorm (i : Fin (N + 1)) : ‖spectralPointValue i‖ = 1 := by
    have normIdentity := unitaryShift.norm_map (eigenbasis i)
    rw [eigenAction, norm_smul, eigenbasis.norm_eq_one, mul_one] at normIdentity
    exact normIdentity
  let spectralPoint : Fin (N + 1) -> Circle := fun i =>
    ⟨spectralPointValue i, mem_sphere_zero_iff_norm.mpr (spectralPointNorm i)⟩
  let coefficient : Fin (N + 1) -> Complex := fun i =>
    inner Complex (eigenbasis i) (gramVector 0)
  let weight : Fin (N + 1) -> NNReal := fun i =>
    ⟨Complex.normSq (coefficient i), Complex.normSq_nonneg _⟩
  let atomicMeasure : Measure Circle :=
    ∑ i, (weight i : ENNReal) • Measure.dirac (spectralPoint i)
  have atomicFinite : IsFiniteMeasure atomicMeasure := by
    constructor
    simp [atomicMeasure]
  let sigma : FiniteMeasure Circle := ⟨atomicMeasure, atomicFinite⟩
  have eigenPower (i : Fin (N + 1)) (k : Nat) :
      (U ^ k) (eigenbasis i) = spectralPointValue i ^ k • eigenbasis i := by
    rw [Module.End.pow_apply]
    induction k with
    | zero => simp
    | succ k ih =>
        rw [Function.iterate_succ_apply', ih]
        change unitaryShift (spectralPointValue i ^ k • eigenbasis i) = _
        rw [map_smul, eigenAction]
        simp only [smul_smul, pow_succ]
  have orbitPower (k : Nat) (hk : k <= N) :
      (U ^ k) (gramVector 0) = gramVector ⟨k, Nat.lt_succ_of_le hk⟩ := by
    rw [Module.End.pow_apply]
    induction k with
    | zero => simp
    | succ k ih =>
        have hkN : k < N := Nat.lt_of_succ_le hk
        let j : Fin N := ⟨k, hkN⟩
        rw [Function.iterate_succ_apply', ih (Nat.le_of_lt hkN)]
        have hsource : (⟨k, Nat.lt_succ_of_le (Nat.le_of_lt hkN)⟩ : Fin (N + 1)) =
            j.castSucc := Fin.ext rfl
        rw [hsource]
        change unitaryShift (gramVector j.castSucc) = _
        rw [shiftAction]
        apply congrArg gramVector
        apply Fin.ext
        rfl
  have spectralExpansion (k : Nat) :
      (U ^ k) (gramVector 0) =
        ∑ i, coefficient i •
          (spectralPointValue i ^ k • eigenbasis i) := by
    nth_rw 1 [← eigenbasis.sum_repr' (gramVector 0)]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_smul, eigenPower]
  have innerSpectralExpansion (k : Nat) :
      inner Complex (gramVector 0) ((U ^ k) (gramVector 0)) =
        ∑ i, (weight i : Real) * spectralPointValue i ^ k := by
    rw [spectralExpansion]
    rw [inner_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [inner_smul_right, smul_smul]
    change coefficient i * spectralPointValue i ^ k *
        inner Complex (gramVector 0) (eigenbasis i) =
      ((weight i : Real) : Complex) * spectralPointValue i ^ k
    have hInner : inner Complex (gramVector 0) (eigenbasis i) =
        star (coefficient i) := by
      exact (inner_conj_symm (gramVector 0) (eigenbasis i)).symm
    have hWeight : ((weight i : Real) : Complex) =
        coefficient i * star (coefficient i) := by
      change (Complex.normSq (coefficient i) : Complex) = _
      simpa only [RCLike.star_def] using (Complex.mul_conj (coefficient i)).symm
    rw [hInner, hWeight]
    ring
  have atomicPowerIntegral (k : Nat) :
      (∫ z : Circle, (z : Complex) ^ k ∂(sigma : Measure Circle)) =
        ∑ i, (weight i : Real) * spectralPointValue i ^ k := by
    change (∫ z : Circle, (z : Complex) ^ k ∂atomicMeasure) = _
    rw [integral_finsetSum_measure]
    · apply Finset.sum_congr rfl
      intro i _
      rw [integral_smul_measure, integral_dirac]
      simp [spectralPoint]
    · intro i _
      exact Integrable.smul_measure
        (integrable_dirac (a := spectralPoint i)
          (f := fun z : Circle => (z : Complex) ^ k)
          (show ‖((spectralPoint i : Circle) : Complex) ^ k‖ₑ < ∞ from enorm_lt_top))
        ENNReal.coe_ne_top
  have negativeMoment (k : Nat) (hk : k <= N) :
      (∫ z : Circle, (z : Complex) ^ k ∂(sigma : Measure Circle)) = r (-(k : Int)) := by
    rw [atomicPowerIntegral, ← innerSpectralExpansion]
    rw [orbitPower k hk, gramIdentity]
    simp [residualToeplitz]
  have positiveMoment (k : Nat) (hk : k <= N) :
      (∫ z : Circle, (z : Complex) ^ (-(k : Int)) ∂(sigma : Measure Circle)) =
        r (k : Int) := by
    have integrandConj (z : Circle) :
        (z : Complex) ^ (-(k : Int)) = star ((z : Complex) ^ k) := by
      rw [_root_.zpow_neg, zpow_natCast]
      rw [← Circle.coe_pow, ← Circle.coe_inv, Circle.coe_inv_eq_conj]
      simp only [RCLike.star_def]
    calc
      (∫ z : Circle, (z : Complex) ^ (-(k : Int)) ∂(sigma : Measure Circle)) =
          ∫ z : Circle, star ((z : Complex) ^ k) ∂(sigma : Measure Circle) := by
            apply integral_congr_ae
            filter_upwards [] with z
            exact integrandConj z
      _ = star (∫ z : Circle, (z : Complex) ^ k ∂(sigma : Measure Circle)) :=
        integral_conj
      _ = star (r (-(k : Int))) := by rw [negativeMoment k hk]
      _ = r (k : Int) := by rw [hermitian]; simp
  refine ⟨sigma, ?_⟩
  intro k hk
  cases k with
  | ofNat n =>
      simpa using positiveMoment n (by simpa using hk)
  | negSucc n =>
      have hn : n + 1 <= N := by simpa using hk
      simpa only [Int.negSucc_eq, neg_neg, ← Int.natCast_one, ← Int.natCast_add,
        zpow_natCast] using
        negativeMoment (n + 1) hn


#print axioms truncated_circle_moment_of_posSemidef

end D5.S3.Weil.CayleyLaguerre.TruncatedCircleMomentBridge
