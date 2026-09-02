/- GID: D5/S3/Constants/FiniteStieltjesOperatorRealization
   generality: G
   mirror-B: D5/B/S3/Constants/FiniteStieltjesOperatorRealization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite positive Stieltjes moments have positive Hankel matrices and a positive diagonal operator realization. -/

import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

/- Library-search audit trail (2026-09-02):
   * Six-way repository retrieval searched `Stieltjes`, finite atomic moments,
     Hankel positivity, diagonal/operator moment realizations, symbol/body
     variants, digestion receipts and residual indexes, generalized Gram
     factorizations, and all commits on `origin/lane/math/*` beyond `origin/dev`.
     `HankelJacobiDeterminant` defines Hankel determinants, while the observer
     Hankel and Weil moment modules prove rank, convergence, or transport
     results; none states this finite positive moment/operator package.
   * The exact pinned-Mathlib hit `Matrix.posSemidef_gram` proves that every
     finite Gram matrix is positive semidefinite. `PiLp.inner_apply`,
     `Module.End.pow_apply`, and `Real.sq_sqrt` provide the remaining
     coordinate, operator-power, and nonnegative square-root identities.
   * The source's RH and xi equivalences are not claimed here: the repository
     has no frozen square-folded xi Stieltjes representation or relative-trace
     formula producing its positive weights. The theorem formalizes the
     unconditional finite positive-atomic core needed by that proposed route.
 -/

open scoped InnerProductSpace

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Constants.FiniteStieltjesOperatorRealization

/-- The power moments of finitely many real nodes with real weights. -/
def finiteMoment {ι : Type*} [Fintype ι]
    (node weight : ι -> Real) (n : Nat) : Real :=
  ∑ i, weight i * node i ^ n

/-- The Hankel truncation whose `(p,q)` entry is moment `p+q`. -/
def finiteHankel {ι : Type*} [Fintype ι]
    (node weight : ι -> Real) (k : Nat) :
    Matrix (Fin (k + 1)) (Fin (k + 1)) Real :=
  fun p q => finiteMoment node weight (p.1 + q.1)

/-- The real quadratic form of a finite Hankel truncation. -/
def hankelQuadraticForm {ι : Type*} [Fintype ι]
    (node weight : ι -> Real) (k : Nat)
    (coefficients : Fin (k + 1) -> Real) : Real :=
  dotProduct coefficients
    (Matrix.mulVec (finiteHankel node weight k) coefficients)

/-- The Gram vector associated with one monomial degree. -/
noncomputable def momentVector {ι : Type*} [Fintype ι]
    (node weight : ι -> Real) (n : Nat) : EuclideanSpace Real ι :=
  WithLp.toLp 2 fun i => Real.sqrt (weight i) * node i ^ n

/-- Coordinatewise multiplication by the finite Stieltjes nodes. -/
def diagonalOperator {ι : Type*} [Fintype ι]
    (node : ι -> Real) : Module.End Real (EuclideanSpace Real ι) where
  toFun vector := WithLp.toLp 2 fun i => node i * vector i
  map_add' left right := by
    ext i
    simp [mul_add]
  map_smul' scalar vector := by
    ext i
    change node i * (scalar * vector i) = scalar * (node i * vector i)
    ring

/-- The vector whose coordinates are the square roots of the weights. -/
noncomputable def rootWeightVector {ι : Type*} [Fintype ι]
    (weight : ι -> Real) : EuclideanSpace Real ι :=
  WithLp.toLp 2 fun i => Real.sqrt (weight i)

/-- An endomorphism is nonnegative when all of its real quadratic pairings are nonnegative. -/
def IsNonnegativeOperator {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
    (operator : Module.End Real E) : Prop :=
  forall vector, 0 <= inner Real (operator vector) vector

private theorem finite_hankel_eq_gram {ι : Type*} [Fintype ι]
    (node weight : ι -> Real) (weight_nonnegative : forall i, 0 <= weight i)
    (k : Nat) :
    finiteHankel node weight k =
      Matrix.gram Real (fun p : Fin (k + 1) => momentVector node weight p.1) := by
  classical
  ext p q
  rw [Matrix.gram_apply, PiLp.inner_apply]
  simp only [finiteHankel, finiteMoment, momentVector]
  apply Finset.sum_congr rfl
  intro i _
  rw [Real.inner_apply]
  change
    weight i * node i ^ (p.1 + q.1) =
      (Real.sqrt (weight i) * node i ^ p.1) *
        (Real.sqrt (weight i) * node i ^ q.1)
  rw [pow_add]
  calc
    weight i * (node i ^ p.1 * node i ^ q.1) =
        Real.sqrt (weight i) ^ 2 *
          (node i ^ p.1 * node i ^ q.1) := by
      rw [Real.sq_sqrt (weight_nonnegative i)]
    _ = (Real.sqrt (weight i) * node i ^ p.1) *
          (Real.sqrt (weight i) * node i ^ q.1) := by ring

private theorem finite_hankel_posSemidef {ι : Type*} [Fintype ι]
    (node weight : ι -> Real) (weight_nonnegative : forall i, 0 <= weight i)
    (k : Nat) :
    (finiteHankel node weight k).PosSemidef := by
  rw [finite_hankel_eq_gram node weight weight_nonnegative k]
  exact Matrix.posSemidef_gram Real _

private theorem diagonal_operator_power_apply {ι : Type*} [Fintype ι]
    (node : ι -> Real) (n : Nat) (vector : EuclideanSpace Real ι) (i : ι) :
    (((diagonalOperator node) ^ n) vector) i = node i ^ n * vector i := by
  induction n with
  | zero => simp
  | succ n induction_hypothesis =>
      rw [pow_succ', Module.End.mul_apply]
      change node i * ((((diagonalOperator node) ^ n) vector) i) =
        node i ^ (n + 1) * vector i
      rw [induction_hypothesis, pow_succ]
      ring

private theorem diagonal_operator_nonnegative {ι : Type*} [Fintype ι]
    (node : ι -> Real) (node_nonnegative : forall i, 0 <= node i) :
    IsNonnegativeOperator (diagonalOperator node) := by
  intro vector
  rw [PiLp.inner_apply]
  apply Finset.sum_nonneg
  intro i _
  rw [Real.inner_apply]
  change 0 <= (node i * vector i) * vector i
  nlinarith [node_nonnegative i, sq_nonneg (vector i)]

private theorem moment_eq_operator_pairing {ι : Type*} [Fintype ι]
    (node weight : ι -> Real) (weight_nonnegative : forall i, 0 <= weight i)
    (n : Nat) :
    finiteMoment node weight n =
      inner Real
        (((diagonalOperator node) ^ n) (rootWeightVector weight))
        (rootWeightVector weight) := by
  classical
  rw [PiLp.inner_apply]
  simp only [finiteMoment, diagonal_operator_power_apply, rootWeightVector]
  apply Finset.sum_congr rfl
  intro i _
  rw [Real.inner_apply]
  change
    weight i * node i ^ n =
      (node i ^ n * Real.sqrt (weight i)) * Real.sqrt (weight i)
  calc
    weight i * node i ^ n =
        Real.sqrt (weight i) ^ 2 * node i ^ n := by
      rw [Real.sq_sqrt (weight_nonnegative i)]
    _ = (node i ^ n * Real.sqrt (weight i)) *
          Real.sqrt (weight i) := by ring

/-- Finite nonnegative Stieltjes nodes and weights give positive semidefinite
Hankel truncations and an explicit nonnegative diagonal operator realization.
The zero coefficient vector and zero state explicitly attain equality in the
two nonnegativity assertions. -/
theorem finite_stieltjes_operator_realization
    {ι : Type*} [Fintype ι]
    (node weight : ι -> Real)
    (node_nonnegative : forall i, 0 <= node i)
    (weight_nonnegative : forall i, 0 <= weight i) :
    (forall k,
      (finiteHankel node weight k).PosSemidef /\
        hankelQuadraticForm node weight k 0 = 0) /\
      exists operator : Module.End Real (EuclideanSpace Real ι),
        exists vector : EuclideanSpace Real ι,
          IsNonnegativeOperator operator /\
          inner Real (operator 0) 0 = 0 /\
          (forall state i, operator state i = node i * state i) /\
          forall n, finiteMoment node weight n =
            inner Real ((operator ^ n) vector) vector := by
  constructor
  · intro k
    exact
      ⟨finite_hankel_posSemidef node weight weight_nonnegative k,
        by simp [hankelQuadraticForm]⟩
  · refine
      ⟨diagonalOperator node, rootWeightVector weight,
        diagonal_operator_nonnegative node node_nonnegative, by simp, ?_, ?_⟩
    · intro state i
      rfl
    · exact moment_eq_operator_pairing node weight weight_nonnegative

#print axioms finite_stieltjes_operator_realization

end D5.S3.Constants.FiniteStieltjesOperatorRealization
