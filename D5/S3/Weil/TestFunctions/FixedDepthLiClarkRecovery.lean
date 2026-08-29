/- GID: D5/S3/Weil/TestFunctions/FixedDepthLiClarkRecovery
   generality: G
   mirror-B: D5/B/S3/Weil/TestFunctions/FixedDepthLiClarkRecovery
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Fixed-depth Li-Clark Toeplitz matrices inherit exponential moment recovery. -/

import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Int.Lemmas
import Mathlib.LinearAlgebra.Matrix.StdBasis

/- Library-search audit trail (2026-08-29):
   * D5 searches for fixed-depth Li-Clark recovery, Toeplitz entrywise asymptotics,
     and least-eigenvalue convergence found no exact owner.
   * `FiniteWindowHaarFloorInterval` supplies a related two-sided estimate, but its
     Rayleigh-floor helper is private and its public premise is a tail-sum bound.
   * Body-shape searches for `fun j k => moment (j - k)` found no canonical D5
     Toeplitz constructor. No new definition or abbreviation is introduced here.
   * Pinned Mathlib supplies finite `IsBigO.sum`, `Matrix.single`, the Hermitian
     spectral theorem, Rayleigh quotient bounds, and exponential-polynomial decay. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Weil.TestFunctions.FixedDepthLiClarkRecovery

open Asymptotics Filter Matrix Set
open scoped BigOperators ComplexConjugate Matrix.Norms.L2Operator

private theorem matrix_isBigO_of_entrywise
    {N : Nat} {A : Real -> Matrix (Fin (N + 1)) (Fin (N + 1)) Complex}
    {g : Real -> Real}
    (h : forall i j, (fun x => A x i j) =O[atTop] g) :
    A =O[atTop] g := by
  classical
  let E : Fin (N + 1) -> Fin (N + 1) ->
      Matrix (Fin (N + 1)) (Fin (N + 1)) Complex :=
    fun i j => Matrix.single i j 1
  have hterm (i j : Fin (N + 1)) :
      (fun x => A x i j • E i j) =O[atTop] g := by
    simpa using (h i j).smul (isBigO_const_one Real (E i j) atTop)
  have hsum :
      (fun x => ∑ i, ∑ j, A x i j • E i j) =O[atTop] g := by
    apply IsBigO.sum
    intro i _hi
    apply IsBigO.sum
    intro j _hj
    exact hterm i j
  convert hsum using 1
  funext x
  ext i j
  simp_rw [Matrix.sum_apply]
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single j]
    · simp [E]
    · intro b _hb hb
      simp [E, hb]
    · simp
  · intro a _ha ha
    simp [E, ha]
  · simp

private theorem rayleigh_floor_eq_smallest_eigenvalue
    {N : Nat} {A : Matrix (Fin (N + 1)) (Fin (N + 1)) Complex}
    (hA : A.IsHermitian) :
    (⨅ x : {x : EuclideanSpace Complex (Fin (N + 1)) // x ≠ 0},
      (Matrix.toEuclideanCLM (𝕜 := Complex) A).rayleighQuotient x) =
      hA.eigenvalues₀ ⟨N, by simp⟩ := by
  let lastIndex : Fin (Fintype.card (Fin (N + 1))) := ⟨N, by simp⟩
  let T := Matrix.toEuclideanCLM (𝕜 := Complex) A
  let hT : A.toEuclideanLin.IsSymmetric :=
    Matrix.isSymmetric_toEuclideanLin_iff.mpr hA
  have floorBounded :
      BddBelow (Set.range fun x :
          {x : EuclideanSpace Complex (Fin (N + 1)) // x ≠ 0} =>
        T.rayleighQuotient x) := by
    refine ⟨-‖T‖, ?_⟩
    rintro value ⟨x, rfl⟩
    exact (abs_le.mp (T.rayleighQuotient_le_norm x)).1
  have floorIsEigenvalue :
      Module.End.HasEigenvalue A.toEuclideanLin
        ((⨅ x : {x : EuclideanSpace Complex (Fin (N + 1)) // x ≠ 0},
          T.rayleighQuotient x : Real) : Complex) := by
    change Module.End.HasEigenvalue A.toEuclideanLin
      ((⨅ x : {x : EuclideanSpace Complex (Fin (N + 1)) // x ≠ 0},
        RCLike.re (inner Complex (A.toEuclideanLin x) x) / ‖(x :
          EuclideanSpace Complex (Fin (N + 1)))‖ ^ 2 : Real) : Complex)
    exact hT.hasEigenvalue_iInf_of_finiteDimensional
  obtain ⟨i, eigenvalueAtI⟩ :=
    hT.exists_eigenvalues_eq finrank_euclideanSpace floorIsEigenvalue
  have smallestLeFloor :
      hA.eigenvalues₀ lastIndex ≤
        ⨅ x : {x : EuclideanSpace Complex (Fin (N + 1)) // x ≠ 0},
          T.rayleighQuotient x := by
    have eigenvalueAtIReal :
        hA.eigenvalues₀ i =
          ⨅ x : {x : EuclideanSpace Complex (Fin (N + 1)) // x ≠ 0},
            T.rayleighQuotient x := by
      apply Complex.ofReal_injective
      simp [Matrix.IsHermitian.eigenvalues₀] at eigenvalueAtI ⊢
      exact eigenvalueAtI
    calc
      hA.eigenvalues₀ lastIndex ≤ hA.eigenvalues₀ i :=
        hA.eigenvalues₀_antitone (by
          apply Fin.le_iff_val_le_val.mpr
          have indexBound := i.isLt
          simp only [Fintype.card_fin] at indexBound
          simp only [lastIndex]
          omega)
      _ = _ := eigenvalueAtIReal
  let x : EuclideanSpace Complex (Fin (N + 1)) :=
    hT.eigenvectorBasis finrank_euclideanSpace lastIndex
  have xNonzero : x ≠ 0 :=
    (hT.eigenvectorBasis finrank_euclideanSpace).orthonormal.ne_zero lastIndex
  have xNorm : ‖x‖ = 1 :=
    (hT.eigenvectorBasis finrank_euclideanSpace).orthonormal.1 lastIndex
  have operatorAtX : A.toEuclideanLin x =
      (hA.eigenvalues₀ lastIndex : Complex) • x := by
    convert hT.apply_eigenvectorBasis finrank_euclideanSpace lastIndex using 1
    all_goals simp [x, Matrix.IsHermitian.eigenvalues₀]
  have rayleighAtX : T.rayleighQuotient x = hA.eigenvalues₀ lastIndex := by
    have operatorAtX' : T x = (hA.eigenvalues₀ lastIndex : Complex) • x :=
      operatorAtX
    rw [ContinuousLinearMap.rayleighQuotient]
    rw [ContinuousLinearMap.reApplyInnerSelf_apply, operatorAtX', inner_smul_left,
      inner_self_eq_norm_sq_to_K, xNorm]
    norm_num
  have floorLeSmallest :
      (⨅ y : {y : EuclideanSpace Complex (Fin (N + 1)) // y ≠ 0},
        T.rayleighQuotient y) ≤ hA.eigenvalues₀ lastIndex := by
    simpa [rayleighAtX] using
      (ciInf_le floorBounded (⟨x, xNonzero⟩ :
        {y : EuclideanSpace Complex (Fin (N + 1)) // y ≠ 0}))
  exact le_antisymm floorLeSmallest smallestLeFloor

private theorem smallest_eigenvalue_difference_le
    {N : Nat} {A B : Matrix (Fin (N + 1)) (Fin (N + 1)) Complex}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    |hA.eigenvalues₀ ⟨N, by simp⟩ - hB.eigenvalues₀ ⟨N, by simp⟩| ≤
      ‖Matrix.toEuclideanCLM (𝕜 := Complex) (A - B)‖ := by
  let trueOperator := Matrix.toEuclideanCLM (𝕜 := Complex) A
  let windowOperator := Matrix.toEuclideanCLM (𝕜 := Complex) B
  let trueFloor :=
    ⨅ x : {x : EuclideanSpace Complex (Fin (N + 1)) // x ≠ 0},
      trueOperator.rayleighQuotient x
  let windowFloor :=
    ⨅ x : {x : EuclideanSpace Complex (Fin (N + 1)) // x ≠ 0},
      windowOperator.rayleighQuotient x
  let errorRadius := ‖Matrix.toEuclideanCLM (𝕜 := Complex) (A - B)‖
  letI : Nonempty {x : EuclideanSpace Complex (Fin (N + 1)) // x ≠ 0} :=
    ⟨⟨WithLp.toLp 2 (Pi.single 0 1), by simp⟩⟩
  have trueFloorBounded :
      BddBelow (Set.range fun x :
          {x : EuclideanSpace Complex (Fin (N + 1)) // x ≠ 0} =>
        trueOperator.rayleighQuotient x) := by
    refine ⟨-‖trueOperator‖, ?_⟩
    rintro value ⟨x, rfl⟩
    exact (abs_le.mp (trueOperator.rayleighQuotient_le_norm x)).1
  have windowFloorBounded :
      BddBelow (Set.range fun x :
          {x : EuclideanSpace Complex (Fin (N + 1)) // x ≠ 0} =>
        windowOperator.rayleighQuotient x) := by
    refine ⟨-‖windowOperator‖, ?_⟩
    rintro value ⟨x, rfl⟩
    exact (abs_le.mp (windowOperator.rayleighQuotient_le_norm x)).1
  have operatorDifference :
      trueOperator - windowOperator =
        Matrix.toEuclideanCLM (𝕜 := Complex) (A - B) := by
    simp [trueOperator, windowOperator]
  have quotientDifference (x :
      {x : EuclideanSpace Complex (Fin (N + 1)) // x ≠ 0}) :
      |trueOperator.rayleighQuotient x - windowOperator.rayleighQuotient x| ≤
        errorRadius := by
    have quotientIdentity :
        (trueOperator - windowOperator).rayleighQuotient x =
          trueOperator.rayleighQuotient x - windowOperator.rayleighQuotient x := by
      rw [sub_eq_add_neg, ContinuousLinearMap.rayleighQuotient_add]
      simp [sub_eq_add_neg]
    rw [← quotientIdentity, operatorDifference]
    exact (Matrix.toEuclideanCLM (𝕜 := Complex) (A - B)).rayleighQuotient_le_norm x
  have lowerInterval : windowFloor - errorRadius ≤ trueFloor := by
    apply le_ciInf
    intro x
    have windowFloorLe := ciInf_le windowFloorBounded x
    have differenceBounds := abs_le.mp (quotientDifference x)
    dsimp only [trueFloor, windowFloor]
    linarith
  have reverseLowerInterval : trueFloor - errorRadius ≤ windowFloor := by
    apply le_ciInf
    intro x
    have trueFloorLe := ciInf_le trueFloorBounded x
    have differenceBounds := abs_le.mp (quotientDifference x)
    dsimp only [trueFloor, windowFloor]
    linarith
  have upperInterval : trueFloor ≤ windowFloor + errorRadius := by
    linarith
  have trueFloorEq : trueFloor = hA.eigenvalues₀ ⟨N, by simp⟩ :=
    rayleigh_floor_eq_smallest_eigenvalue hA
  have windowFloorEq : windowFloor = hB.eigenvalues₀ ⟨N, by simp⟩ :=
    rayleigh_floor_eq_smallest_eigenvalue hB
  rw [trueFloorEq, windowFloorEq] at lowerInterval upperInterval
  exact abs_le.mpr ⟨by linarith, by linarith⟩

set_option maxHeartbeats 800000 in
/-- Fixed-order recovery of the Li coefficients transfers to the operator norm of
the constructed Li-Clark Toeplitz matrices and to their smallest eigenvalues. -/
theorem fixed_depth_li_clark_recovery
    (N : Nat) (liCoefficient : Nat -> Real)
    (windowLiCoefficient : Real -> Nat -> Real) :
    let trueMoment : Int -> Complex := fun k =>
      ((liCoefficient (k + 1).natAbs - 2 * liCoefficient k.natAbs +
          liCoefficient (k - 1).natAbs) / (2 * liCoefficient 1) : Real)
    let windowMoment : Real -> Int -> Complex := fun L k =>
      ((windowLiCoefficient L (k + 1).natAbs -
          2 * windowLiCoefficient L k.natAbs +
          windowLiCoefficient L (k - 1).natAbs) /
        (2 * liCoefficient 1) : Real)
    let rate : Real -> Real := fun L => Real.exp (-L) * L ^ (N - 1)
    (forall k : Int, k.natAbs <= N ->
      (fun L => trueMoment k - windowMoment L k) =O[atTop] rate) ->
    let trueToeplitz : Matrix (Fin (N + 1)) (Fin (N + 1)) Complex :=
      fun j k => trueMoment (((j : Nat) : Int) - ((k : Nat) : Int))
    let windowToeplitz : Real -> Matrix (Fin (N + 1)) (Fin (N + 1)) Complex :=
      fun L j k => windowMoment L (((j : Nat) : Int) - ((k : Nat) : Int))
    let trueHermitian : trueToeplitz.IsHermitian := by
      apply Matrix.IsHermitian.ext
      intro i j
      change star (trueMoment (((j : Nat) : Int) - ((i : Nat) : Int))) =
        trueMoment (((i : Nat) : Int) - ((j : Nat) : Int))
      have evenMoment (k : Int) : trueMoment (-k) = trueMoment k := by
        dsimp only [trueMoment]
        rw [show -k + 1 = -(k - 1) by omega,
          show -k - 1 = -(k + 1) by omega]
        simp only [Int.natAbs_neg]
        push_cast
        ring
      rw [show (((i : Nat) : Int) - ((j : Nat) : Int)) =
          -(((j : Nat) : Int) - ((i : Nat) : Int)) by omega, evenMoment]
      dsimp only [trueMoment]
      simp
    let windowHermitian : forall L, (windowToeplitz L).IsHermitian := by
      intro L
      apply Matrix.IsHermitian.ext
      intro i j
      change star (windowMoment L (((j : Nat) : Int) - ((i : Nat) : Int))) =
        windowMoment L (((i : Nat) : Int) - ((j : Nat) : Int))
      have evenMoment (k : Int) : windowMoment L (-k) = windowMoment L k := by
        dsimp only [windowMoment]
        rw [show -k + 1 = -(k - 1) by omega,
          show -k - 1 = -(k + 1) by omega]
        simp only [Int.natAbs_neg]
        push_cast
        ring
      rw [show (((i : Nat) : Int) - ((j : Nat) : Int)) =
          -(((j : Nat) : Int) - ((i : Nat) : Int)) by omega, evenMoment]
      dsimp only [windowMoment]
      simp
    (fun L => ‖Matrix.toEuclideanCLM (𝕜 := Complex)
        (trueToeplitz - windowToeplitz L)‖) =O[atTop] rate ∧
      (fun L =>
        (windowHermitian L).eigenvalues₀ ⟨N, by simp⟩ -
          trueHermitian.eigenvalues₀ ⟨N, by simp⟩) =O[atTop] rate ∧
      Tendsto (fun L => (windowHermitian L).eigenvalues₀ ⟨N, by simp⟩)
        atTop (nhds (trueHermitian.eigenvalues₀ ⟨N, by simp⟩)) := by
  dsimp only
  intro momentRecovery
  let trueMoment : Int -> Complex := fun k =>
    ((liCoefficient (k + 1).natAbs - 2 * liCoefficient k.natAbs +
        liCoefficient (k - 1).natAbs) / (2 * liCoefficient 1) : Real)
  let windowMoment : Real -> Int -> Complex := fun L k =>
    ((windowLiCoefficient L (k + 1).natAbs -
        2 * windowLiCoefficient L k.natAbs +
        windowLiCoefficient L (k - 1).natAbs) /
      (2 * liCoefficient 1) : Real)
  let rate : Real -> Real := fun L => Real.exp (-L) * L ^ (N - 1)
  let trueToeplitz : Matrix (Fin (N + 1)) (Fin (N + 1)) Complex :=
    fun j k => trueMoment (((j : Nat) : Int) - ((k : Nat) : Int))
  let windowToeplitz : Real -> Matrix (Fin (N + 1)) (Fin (N + 1)) Complex :=
    fun L j k => windowMoment L (((j : Nat) : Int) - ((k : Nat) : Int))
  have trueHermitian : trueToeplitz.IsHermitian := by
    apply Matrix.IsHermitian.ext
    intro i j
    change star (trueMoment (((j : Nat) : Int) - ((i : Nat) : Int))) =
      trueMoment (((i : Nat) : Int) - ((j : Nat) : Int))
    have evenMoment (k : Int) : trueMoment (-k) = trueMoment k := by
      dsimp only [trueMoment]
      rw [show -k + 1 = -(k - 1) by omega,
        show -k - 1 = -(k + 1) by omega]
      simp only [Int.natAbs_neg]
      push_cast
      ring
    rw [show (((i : Nat) : Int) - ((j : Nat) : Int)) =
        -(((j : Nat) : Int) - ((i : Nat) : Int)) by omega, evenMoment]
    dsimp only [trueMoment]
    simp
  have windowHermitian : forall L, (windowToeplitz L).IsHermitian := by
    intro L
    apply Matrix.IsHermitian.ext
    intro i j
    change star (windowMoment L (((j : Nat) : Int) - ((i : Nat) : Int))) =
      windowMoment L (((i : Nat) : Int) - ((j : Nat) : Int))
    have evenMoment (k : Int) : windowMoment L (-k) = windowMoment L k := by
      dsimp only [windowMoment]
      rw [show -k + 1 = -(k - 1) by omega,
        show -k - 1 = -(k + 1) by omega]
      simp only [Int.natAbs_neg]
      push_cast
      ring
    rw [show (((i : Nat) : Int) - ((j : Nat) : Int)) =
        -(((j : Nat) : Int) - ((i : Nat) : Int)) by omega, evenMoment]
    dsimp only [windowMoment]
    simp
  let matrixError : Real -> Matrix (Fin (N + 1)) (Fin (N + 1)) Complex :=
    fun L => trueToeplitz - windowToeplitz L
  have entryRecovery (i j : Fin (N + 1)) :
      (fun L => matrixError L i j) =O[atTop] rate := by
    have indexBound :
        Int.natAbs (((i : Nat) : Int) - ((j : Nat) : Int)) <= N :=
      Int.natAbs_coe_sub_coe_le_of_le (by omega) (by omega)
    simpa [matrixError, trueToeplitz, windowToeplitz, trueMoment, windowMoment, rate] using
      momentRecovery (((i : Nat) : Int) - ((j : Nat) : Int)) indexBound
  have matrixRecovery : matrixError =O[atTop] rate :=
    matrix_isBigO_of_entrywise entryRecovery
  have operatorRecovery :
      (fun L => ‖Matrix.toEuclideanCLM (𝕜 := Complex)
        (trueToeplitz - windowToeplitz L)‖) =O[atTop] rate := by
    change (fun L => ‖matrixError L‖) =O[atTop] rate
    exact matrixRecovery.norm_left
  let floorError : Real -> Real := fun L =>
    (windowHermitian L).eigenvalues₀ ⟨N, by simp⟩ -
      trueHermitian.eigenvalues₀ ⟨N, by simp⟩
  have floorDominated : floorError =O[atTop] matrixError := by
    apply IsBigO.of_bound 1
    filter_upwards with L
    dsimp only [floorError, matrixError]
    rw [one_mul]
    change |(windowHermitian L).eigenvalues₀ ⟨N, by simp⟩ -
        trueHermitian.eigenvalues₀ ⟨N, by simp⟩| ≤
      ‖Matrix.toEuclideanCLM (𝕜 := Complex)
        (trueToeplitz - windowToeplitz L)‖
    rw [abs_sub_comm]
    exact smallest_eigenvalue_difference_le trueHermitian (windowHermitian L)
  have floorRecovery : floorError =O[atTop] rate :=
    floorDominated.trans matrixRecovery
  have rateTendsto : Tendsto rate atTop (nhds 0) := by
    simpa [rate, mul_comm] using
      Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero (N - 1)
  have floorErrorTendsto : Tendsto floorError atTop (nhds 0) :=
    floorRecovery.trans_tendsto rateTendsto
  refine ⟨operatorRecovery, ?_, ?_⟩
  · exact floorRecovery
  · apply tendsto_sub_nhds_zero_iff.mp
    exact floorErrorTendsto

#print axioms fixed_depth_li_clark_recovery

end D5.S3.Weil.TestFunctions.FixedDepthLiClarkRecovery
