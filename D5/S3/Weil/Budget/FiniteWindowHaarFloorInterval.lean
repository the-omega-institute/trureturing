/- GID: D5/S3/Weil/Budget/FiniteWindowHaarFloorInterval
   generality: G
   mirror-B: D5/B/S3/Weil/Budget/FiniteWindowHaarFloorInterval
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A finite Toeplitz operator-norm estimate gives a two-sided Haar-floor interval. -/

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.Matrix.Spectrum

/- Library-search audit trail (2026-08-29):
   * D5 searches for finite-window Haar floors, least Toeplitz eigenvalues,
     and two-sided Hermitian perturbation intervals found no exact owner.
   * `D5.S3.Weil.ZetaLinear.Weyl.weyl_posIndexAbove_le` is a related
     thresholded positive-index result, but does not state the required
     two-sided least-eigenvalue interval.
   * Body-shape searches for Toeplitz matrices of the form
     `fun j k => moment (j - k)` found no canonical D5 construction to import.
   * Pinned Mathlib exact hits `Matrix.toEuclideanCLM`,
     `ContinuousLinearMap.rayleighQuotient_le_norm`, `ciInf_le`, `le_ciInf`,
     and the finite-dimensional Hermitian spectral theorem supply the proof. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Weil.Budget.FiniteWindowHaarFloorInterval

open Filter Matrix Set
open scoped BigOperators ComplexConjugate Matrix.Norms.L2Operator

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
      simpa [Matrix.IsHermitian.eigenvalues₀, hT] using eigenvalueAtI
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
    (hT.eigenvectorBasis finrank_euclideanSpace).orthonormal.ne_zero
      lastIndex
  have xNorm : ‖x‖ = 1 :=
    (hT.eigenvectorBasis finrank_euclideanSpace).orthonormal.1
      lastIndex
  have operatorAtX : A.toEuclideanLin x =
      (hA.eigenvalues₀ lastIndex : Complex) • x := by
    simpa [x, Matrix.IsHermitian.eigenvalues₀, hT] using
      hT.apply_eigenvectorBasis finrank_euclideanSpace lastIndex
  have rayleighAtX : T.rayleighQuotient x = hA.eigenvalues₀ lastIndex := by
    have operatorAtX' : T x = (hA.eigenvalues₀ lastIndex : Complex) • x := by
      exact operatorAtX
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

/-- Let true and windowed moments construct their Toeplitz matrices, and let
the source tail sum bound their operator-norm difference. The smallest true
eigenvalue lies in the corresponding closed interval around the windowed
smallest eigenvalue. -/
theorem finite_window_haar_floor_interval
    (N : Nat) (moment windowMoment : Int -> Complex) (tail : Nat -> Real)
    (momentHermitian : ∀ k, star (moment k) = moment (-k))
    (windowMomentHermitian : ∀ k, star (windowMoment k) = windowMoment (-k))
    (operatorError :
      ‖Matrix.toEuclideanCLM (𝕜 := Complex)
        ((fun j k : Fin (N + 1) =>
            moment (((j : Nat) : Int) - ((k : Nat) : Int))) -
          (fun j k : Fin (N + 1) =>
            windowMoment (((j : Nat) : Int) - ((k : Nat) : Int))))‖ ≤
        2 * ∑ k ∈ Finset.Icc 1 N, tail k) :
    let trueToeplitz : Matrix (Fin (N + 1)) (Fin (N + 1)) Complex :=
      fun j k => moment (((j : Nat) : Int) - ((k : Nat) : Int))
    let windowToeplitz : Matrix (Fin (N + 1)) (Fin (N + 1)) Complex :=
      fun j k => windowMoment (((j : Nat) : Int) - ((k : Nat) : Int))
    let trueHermitian : trueToeplitz.IsHermitian := by
      apply Matrix.IsHermitian.ext
      intro i j
      change star (moment (((j : Nat) : Int) - ((i : Nat) : Int))) =
        moment (((i : Nat) : Int) - ((j : Nat) : Int))
      rw [momentHermitian]
      congr 1
      omega
    let windowHermitian : windowToeplitz.IsHermitian := by
      apply Matrix.IsHermitian.ext
      intro i j
      change star (windowMoment (((j : Nat) : Int) - ((i : Nat) : Int))) =
        windowMoment (((i : Nat) : Int) - ((j : Nat) : Int))
      rw [windowMomentHermitian]
      congr 1
      omega
    windowHermitian.eigenvalues₀ ⟨N, by simp⟩ -
          2 * ∑ k ∈ Finset.Icc 1 N, tail k ≤
        trueHermitian.eigenvalues₀ ⟨N, by simp⟩ ∧
      trueHermitian.eigenvalues₀ ⟨N, by simp⟩ ≤
        windowHermitian.eigenvalues₀ ⟨N, by simp⟩ +
          2 * ∑ k ∈ Finset.Icc 1 N, tail k := by
  dsimp only
  let trueToeplitz : Matrix (Fin (N + 1)) (Fin (N + 1)) Complex :=
    fun j k => moment (((j : Nat) : Int) - ((k : Nat) : Int))
  let windowToeplitz : Matrix (Fin (N + 1)) (Fin (N + 1)) Complex :=
    fun j k => windowMoment (((j : Nat) : Int) - ((k : Nat) : Int))
  have trueHermitian : trueToeplitz.IsHermitian := by
    apply Matrix.IsHermitian.ext
    intro i j
    change star (moment (((j : Nat) : Int) - ((i : Nat) : Int))) =
      moment (((i : Nat) : Int) - ((j : Nat) : Int))
    rw [momentHermitian]
    congr 1
    omega
  have windowHermitian : windowToeplitz.IsHermitian := by
    apply Matrix.IsHermitian.ext
    intro i j
    change star (windowMoment (((j : Nat) : Int) - ((i : Nat) : Int))) =
      windowMoment (((i : Nat) : Int) - ((j : Nat) : Int))
    rw [windowMomentHermitian]
    congr 1
    omega
  let trueOperator := Matrix.toEuclideanCLM (𝕜 := Complex) trueToeplitz
  let windowOperator := Matrix.toEuclideanCLM (𝕜 := Complex) windowToeplitz
  let trueFloor :=
    ⨅ x : {x : EuclideanSpace Complex (Fin (N + 1)) // x ≠ 0},
      trueOperator.rayleighQuotient x
  let windowFloor :=
    ⨅ x : {x : EuclideanSpace Complex (Fin (N + 1)) // x ≠ 0},
      windowOperator.rayleighQuotient x
  let errorRadius := 2 * ∑ k ∈ Finset.Icc 1 N, tail k
  have operatorNormError : ‖trueOperator - windowOperator‖ ≤ errorRadius := by
    have operatorDifference :
        trueOperator - windowOperator =
          Matrix.toEuclideanCLM (𝕜 := Complex) (trueToeplitz - windowToeplitz) := by
      simp [trueOperator, windowOperator]
    rw [operatorDifference]
    convert operatorError using 1 <;> rfl
  letI : Nonempty
      {x : EuclideanSpace Complex (Fin (N + 1)) // x ≠ 0} :=
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
  have quotientDifference (x :
      {x : EuclideanSpace Complex (Fin (N + 1)) // x ≠ 0}) :
      |trueOperator.rayleighQuotient x - windowOperator.rayleighQuotient x| ≤
        errorRadius := by
    have quotientIdentity :
        (trueOperator - windowOperator).rayleighQuotient x =
          trueOperator.rayleighQuotient x - windowOperator.rayleighQuotient x := by
      rw [sub_eq_add_neg,
        ContinuousLinearMap.rayleighQuotient_add]
      simp [sub_eq_add_neg]
    rw [← quotientIdentity]
    exact (trueOperator - windowOperator).rayleighQuotient_le_norm x |>.trans
      operatorNormError
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
  have trueFloorEq : trueFloor = trueHermitian.eigenvalues₀ ⟨N, by simp⟩ := by
    exact rayleigh_floor_eq_smallest_eigenvalue trueHermitian
  have windowFloorEq :
      windowFloor = windowHermitian.eigenvalues₀ ⟨N, by simp⟩ := by
    exact rayleigh_floor_eq_smallest_eigenvalue windowHermitian
  rw [trueFloorEq, windowFloorEq] at lowerInterval upperInterval
  simpa [errorRadius] using And.intro lowerInterval upperInterval

#print axioms finite_window_haar_floor_interval

end D5.S3.Weil.Budget.FiniteWindowHaarFloorInterval
