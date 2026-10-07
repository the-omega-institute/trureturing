/- GID: D5/S3/Quantum/Recovery/LiJiangPolarPairOptimalityRefutation
   generality: G
   mirror-B: D5/B/S3/Quantum/Recovery/LiJiangPolarPairOptimalityRefutation
   mirror-E: none(waiver:finite-algebraic-proof)
   anchors: []
   utility: none
   digest: A feasible qubit rank-one encoder strictly improves the source polar pair. -/

/- Stage-A judgement:
   proof_shape: bind-only
   escape_witness: none
   admission_basis: open-problem-resolution
   Direct frozen dependencies: none
-/

import D5.S3.Quantum.Foundation.FiniteKrausRepresentation
import D5.S3.QuantumBounds.PeritoTsirelson
import D5.S3.Quantum.Information.PartialTraceMutualInformation
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
Li–Jiang, arXiv:2609.00778v1, Eqs.18–23 and supplement S60, asks after S64
whether the polar encoder and right partial trace pair is exactly optimal at fixed p>0.
The definitions below retain the full dominance assertion over dimension, noise parameter,
unit auxiliary vector and arbitrary completely positive trace-nonincreasing pairs with
input-first encoder Choi rank at most one. Fidelity is the canonical-purification overlap
before any output trace normalization.

At d=2 and p=9/13, a feasible single-Kraus encoder with columns
(24|00> - 7|11>)/25 and |10> has strictly larger fidelity. The proof derives the
source noise, positive Gram root, polar columns and both fidelities from these definitions.
-/

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped BigOperators CStarAlgebra ComplexOrder MatrixOrder Kronecker
open D5.S3.Quantum.Foundation.FiniteKrausChannel
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open D5.S3.QuantumBounds.PeritoTsirelson

namespace D5.S3.Quantum.Recovery.LiJiangPolarPairOptimalityRefutation

/-- Source Eq.18 parameters. -/
def lambda1 (d : ℕ) (p : ℝ) : ℝ := 1 - p / ((d : ℝ)^2 - 2)
def lambda4 (d : ℕ) (p : ℝ) : ℝ := ((d : ℝ)^2 - 1 + p) / (d : ℝ)^2
def lambda5 (d : ℕ) (p : ℝ) : ℝ := (1 - p) / (d : ℝ)^2
def lambda2 (d : ℕ) (p : ℝ) : ℝ :=
  (1 - lambda1 d p) * ((d : ℝ)^2 * lambda1 d p - 1) /
    ((d : ℝ)^2 * lambda4 d p)
def lambda3 (d : ℕ) (p : ℝ) : ℝ :=
  2 * (1 - lambda1 d p)^2 / ((d : ℝ)^2 * lambda4 d p)

/-- The positive source matrix Q in Eq.18. -/
def sourceQ (d : ℕ) (p : ℝ) : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  (Real.sqrt (d : ℝ) : ℂ) •
    ((Real.sqrt (lambda4 d p / ((d : ℝ)^2 - 1)) : ℂ) • (1 - maxEntangled (Fin d)) +
     (Real.sqrt (lambda5 d p) : ℂ) • maxEntangled (Fin d))

/-- I_L tensor bra(j), tracing out the right factor. -/
def sourceD (d : ℕ) (j : Fin d) : Matrix (Fin d) (Fin d × Fin d) ℂ :=
  fun a b => if a = b.1 ∧ j = b.2 then 1 else 0

def sourceB (d : ℕ) (p : ℝ) (ij : Fin d × Fin d) :
    Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  sourceQ d p * (sourceD d ij.1).conjTranspose * sourceD d ij.2

/-- Eq.22, including its actual adjoint B_ij†. -/
def sourceE (d : ℕ) (p : ℝ) (ij : Fin d × Fin d) :
    Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  ((Real.sqrt (lambda4 d p))⁻¹ : ℂ) •
    (Matrix.vecMulVec (fun a => if a = ij then (1 : ℂ) else 0)
       (star (maxEntangledVector (Fin d))) -
     (Real.sqrt (lambda5 d p) : ℂ) • (sourceB d p ij).conjTranspose)

def rightTrace (d : ℕ) : PhyslibLeaf.MatrixMap (Fin d × Fin d) (Fin d) ℂ where
  toFun := partialTraceRight
  map_add' := partialTraceRight_add
  map_smul' z X := by
    ext a b
    simp [partialTraceRight, Finset.mul_sum]

/-- Literal all-matrix Eq.23 action, without postselection normalization. -/
def sourceNoise (d : ℕ) (p : ℝ) :
    PhyslibLeaf.MatrixMap (Fin d × Fin d) (Fin d × Fin d) ℂ where
  toFun X :=
    (lambda3 d p : ℂ) • (Matrix.trace X • (1 : Matrix _ _ ℂ)) +
    ((lambda1 d p - lambda3 d p : ℝ) : ℂ) •
      Matrix.kronecker (partialTraceRight (sourceQ d p * X * sourceQ d p))
        (1 : Matrix (Fin d) (Fin d) ℂ) +
    (lambda2 d p : ℂ) • ∑ ij, sourceE d p ij * X * (sourceE d p ij).conjTranspose
  map_add' X Y := by
    ext a b
    simp [Matrix.trace_add, partialTraceRight_add,
      Matrix.kroneckerMap_apply, Matrix.sum_apply, Finset.sum_add_distrib,
      smul_eq_mul, add_mul, mul_add]
    ring
  map_smul' z X := by
    have htrace : partialTraceRight (z • (sourceQ d p * X * sourceQ d p)) =
        z • partialTraceRight (sourceQ d p * X * sourceQ d p) := by
      ext a b
      simp [partialTraceRight, Finset.mul_sum]
    ext a b
    simp [Matrix.trace_smul, htrace,
      Matrix.kroneckerMap_apply, Matrix.sum_apply, smul_eq_mul,
      Finset.mul_sum]
    simp only [← Finset.mul_sum]
    ring

/-- Source S60 column matrix Q(I tensor chi). -/
def sourceC (d : ℕ) (p : ℝ) (chi : Fin d → ℂ) :
    Matrix (Fin d × Fin d) (Fin d) ℂ :=
  sourceQ d p * Matrix.of (fun (a : Fin d × Fin d) (b : Fin d) => if a.1 = b then chi a.2 else 0)

/-- S60 polar encoder, using the actual ordered positive root and matrix inverse. -/
def sourcePolar (d : ℕ) (p : ℝ) (chi : Fin d → ℂ) :
    Matrix (Fin d × Fin d) (Fin d) ℂ :=
  let C := sourceC d p chi
  C * (CStarMatrix.ofMatrix.symm
    (CFC.sqrt (CStarMatrix.ofMatrix (C.conjTranspose * C))))⁻¹

/-- Matrix action of the canonical all-amplification completely positive carrier. -/
def matrixAction {a b : Type*} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b]
    (f : CompletelyPositiveMap (CStarMatrix a a ℂ) (CStarMatrix b b ℂ)) :
    PhyslibLeaf.MatrixMap a b ℂ :=
  CStarMatrix.ofMatrixₗ.symm.toLinearMap.comp
    (f.toLinearMap.comp CStarMatrix.ofMatrixₗ.toLinearMap)

/-- Original trace-nonincreasing constraint on every positive semidefinite input. -/
def TraceNonincreasing {a b : Type*} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b]
    (f : CompletelyPositiveMap (CStarMatrix a a ℂ) (CStarMatrix b b ℂ)) : Prop :=
  ∀ X : Matrix a a ℂ, X.PosSemidef → (Matrix.trace (matrixAction f X)).re ≤ (Matrix.trace X).re

/-- Source input-first Choi convention, converted from the library's output-first convention. -/
def inputFirstChoi {a b : Type*} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b] (f : PhyslibLeaf.MatrixMap a b ℂ) :
    Matrix (a × b) (a × b) ℂ :=
  Matrix.reindex (Equiv.prodComm b a) (Equiv.prodComm b a)
    (PhyslibLeaf.MatrixMap.choi_matrix f)

/-- Genuine canonical-purification overlap for I/d. No output trace renormalization. -/
def entanglementFidelity (d : ℕ) (f : PhyslibLeaf.MatrixMap (Fin d) (Fin d) ℂ) : ℝ :=
  let psi := maxEntangledVector (Fin d)
  (dotProduct (star psi)
    ((PhyslibLeaf.MatrixMap.kron f LinearMap.id
      (maxEntangled (Fin d))).mulVec psi)).re

/-- Full original dominance reading of the fixed-p polar-pair optimality question. -/
def claim : Prop :=
  ∀ d : ℕ, 2 ≤ d → ∀ p : ℝ, 0 < p → p < 1 →
  ∀ chi : Fin d → ℂ, (∑ i, Complex.normSq (chi i)) = 1 →
  ∀ C : CompletelyPositiveMap (CStarMatrix (Fin d) (Fin d) ℂ)
      (CStarMatrix (Fin d × Fin d) (Fin d × Fin d) ℂ),
  ∀ D : CompletelyPositiveMap (CStarMatrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
      (CStarMatrix (Fin d) (Fin d) ℂ),
    TraceNonincreasing C → TraceNonincreasing D →
    (inputFirstChoi (matrixAction C)).rank ≤ 1 →
    entanglementFidelity d ((matrixAction D).comp
      ((sourceNoise d p).comp (matrixAction C))) ≤
    entanglementFidelity d ((rightTrace d).comp ((sourceNoise d p).comp
      (PhyslibLeaf.MatrixMap.of_kraus
        (fun _ : Unit => sourcePolar d p chi) (fun _ : Unit => sourcePolar d p chi))))

set_option maxRecDepth 4000 in
set_option maxHeartbeats 4000000 in
/-- The full source polar-pair dominance assertion fails. -/
theorem result : Not claim := by
  classical
  let A : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ := Matrix.of
    (fun a b => if a = b then (if a.1 = a.2 then 3 else 4)
      else if a.1 = a.2 ∧ b.1 = b.2 then -1 else 0)
  let T (ij : Fin 2 × Fin 2) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
    (1/2 : ℂ) •
      (13 • Matrix.vecMulVec (fun a => if a = ij then (1:ℂ) else 0)
        (fun b : Fin 2 × Fin 2 => if b.1 = b.2 then (1:ℂ) else 0) -
      (sourceD 2 ij.2).conjTranspose * sourceD 2 ij.1 * A)
  let R (st : Fin 2 × Fin 2) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
    Matrix.kronecker (1 : Matrix (Fin 2) (Fin 2) ℂ) (Matrix.single st.1 st.2 1) * A
  let K : ((Fin 2 × Fin 2) × (Fin 2 × Fin 2)) ⊕
      ((Fin 2 × Fin 2) ⊕ (Fin 2 × Fin 2)) →
        Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ := fun r =>
    match r with
    | .inl ab => (Real.sqrt 702 / 104 : ℂ) • Matrix.single ab.1 ab.2 1
    | .inr (.inl st) => (Real.sqrt 245 / 104 : ℂ) • R st
    | .inr (.inr ij) => (Real.sqrt 21 / 104 : ℂ) • T ij

  have hQ : sourceQ 2 (9/13) =
    ((Real.sqrt 26)⁻¹ : ℂ) •
      A := by
    have hl1 : lambda1 2 (9/13) = 17/26 := by norm_num [lambda1]
    have hl4 : lambda4 2 (9/13) = 12/13 := by norm_num [lambda4]
    have hl5 : lambda5 2 (9/13) = 1/13 := by norm_num [lambda5]
    have hs2 : Real.sqrt 2 ^ 2 = 2 := by norm_num
    have hs26 : Real.sqrt 26 ^ 2 = 26 := by norm_num
    have hn2 : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
    have hn26 : Real.sqrt 26 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
    have ha : Real.sqrt 2 * Real.sqrt (4/13) = 4 / Real.sqrt 26 := by
      have hr : Real.sqrt (4/13) ^ 2 = 4/13 := Real.sq_sqrt (by norm_num)
      have hp : 0 ≤ Real.sqrt 2 * Real.sqrt (4/13) := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      have hq : 0 ≤ 4 / Real.sqrt 26 := by positivity
      have heq : (Real.sqrt 2 * Real.sqrt (4/13)) ^ 2 = (4 / Real.sqrt 26) ^ 2 := by
        rw [mul_pow, div_pow, hs2, hs26, hr]
        norm_num
      nlinarith
    have hb : Real.sqrt 2 * Real.sqrt (1/13) = 2 / Real.sqrt 26 := by
      have hr : Real.sqrt (1/13) ^ 2 = 1/13 := Real.sq_sqrt (by norm_num)
      have hp : 0 ≤ Real.sqrt 2 * Real.sqrt (1/13) := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      have hq : 0 ≤ 2 / Real.sqrt 26 := by positivity
      have heq : (Real.sqrt 2 * Real.sqrt (1/13)) ^ 2 = (2 / Real.sqrt 26) ^ 2 := by
        rw [mul_pow, div_pow, hs2, hs26, hr]
        norm_num
      nlinarith
    have hs2c : (Real.sqrt 2 : ℂ)^2 = 2 := by exact_mod_cast hs2
    have hn2c : (Real.sqrt 2 : ℂ) ≠ 0 := by exact_mod_cast hn2
    have hn26c : (Real.sqrt 26 : ℂ) ≠ 0 := by exact_mod_cast hn26
    have hac : (Real.sqrt 2 : ℂ) * (Real.sqrt (4/13) : ℂ) = 4 / (Real.sqrt 26 : ℂ) := by exact_mod_cast ha
    have hbc : (Real.sqrt 2 : ℂ) * (Real.sqrt (1/13) : ℂ) = 2 / (Real.sqrt 26 : ℂ) := by exact_mod_cast hb
    have hs2inv : ((Real.sqrt 2)⁻¹ : ℝ) * (Real.sqrt 2)⁻¹ = 1/2 := by
      rw [← mul_inv_rev, ← pow_two, hs2]
      norm_num
    have hpi : maxEntangled (Fin 2) = Matrix.of (fun a b : Fin 2 × Fin 2 =>
        if a.1 = a.2 ∧ b.1 = b.2 then (1/2 : ℂ) else 0) := by
      ext ⟨a,b⟩ ⟨c,d⟩
      fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
        norm_num [maxEntangled, maxEntangledVector, Fintype.card_fin, Matrix.vecMulVec,
          ← Complex.ofReal_mul, hs2inv, Matrix.of_apply]
      all_goals rw [← mul_inv_rev, ← pow_two, hs2c]
      all_goals norm_num
    have hQform : sourceQ 2 (9/13) =
        (Real.sqrt 2 : ℂ) •
          ((Real.sqrt (4/13) : ℂ) • (1 - maxEntangled (Fin 2)) +
           (Real.sqrt (1/13) : ℂ) • maxEntangled (Fin 2)) := by
      simp only [sourceQ, hl4, hl5]
      norm_num only
    rw [hQform, smul_add, smul_smul, smul_smul, hac, hbc, hpi]
    ext ⟨a,b⟩ ⟨c,d⟩
    fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
      norm_num [A, Matrix.smul_apply, Matrix.one_apply, Matrix.of_apply,
        Matrix.add_apply, Matrix.sub_apply]
    all_goals ring

  have hA : A.conjTranspose = A := by
      ext ⟨a,b⟩ ⟨c,d⟩
      fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
        norm_num [A, Matrix.conjTranspose_apply]

  have hEraw : ∀ ij, sourceE 2 (9/13) ij =
      (Real.sqrt 78 : ℂ)⁻¹ • ((1/2:ℂ) •
        (13 • Matrix.vecMulVec (fun a => if a=ij then (1:ℂ) else 0)
          (fun b : Fin 2 × Fin 2 => if b.1=b.2 then (1:ℂ) else 0) -
          (sourceD 2 ij.2).conjTranspose * sourceD 2 ij.1 * A.conjTranspose)) := by
    have h4 : lambda4 2 (9/13) = 12/13 := by norm_num [lambda4]
    have h5 : lambda5 2 (9/13) = 1/13 := by norm_num [lambda5]
    have hs2 : Real.sqrt 2 ^ 2 = 2 := by norm_num
    have hs26 : Real.sqrt 26 ^ 2 = 26 := by norm_num
    have hs78 : Real.sqrt 78 ^ 2 = 78 := by norm_num
    have hs4 : Real.sqrt (12/13) ^ 2 = 12/13 := Real.sq_sqrt (by norm_num)
    have hs5 : Real.sqrt (1/13) ^ 2 = 1/13 := Real.sq_sqrt (by norm_num)
    have ha : (Real.sqrt (12/13))⁻¹ * (Real.sqrt 2)⁻¹ = 13 / (2 * Real.sqrt 78) := by
      have hp : 0 ≤ (Real.sqrt (12/13))⁻¹ * (Real.sqrt 2)⁻¹ := by positivity
      have hq : 0 ≤ 13 / (2 * Real.sqrt 78) := by positivity
      have heq : ((Real.sqrt (12/13))⁻¹ * (Real.sqrt 2)⁻¹)^2 = (13/(2*Real.sqrt 78))^2 := by
        rw [mul_pow, inv_pow, inv_pow, div_pow, mul_pow, hs2, hs4, hs78]
        norm_num
      nlinarith
    have hb : (Real.sqrt (12/13))⁻¹ * Real.sqrt (1/13) * (Real.sqrt 26)⁻¹ = 1 / (2 * Real.sqrt 78) := by
      have hp : 0 ≤ (Real.sqrt (12/13))⁻¹ * Real.sqrt (1/13) * (Real.sqrt 26)⁻¹ := by positivity
      have hq : 0 ≤ 1 / (2 * Real.sqrt 78) := by positivity
      have heq : ((Real.sqrt (12/13))⁻¹ * Real.sqrt (1/13) * (Real.sqrt 26)⁻¹)^2 = (1/(2*Real.sqrt 78))^2 := by
        rw [mul_pow, mul_pow, inv_pow, inv_pow, div_pow, mul_pow, hs26, hs4, hs5, hs78]
        norm_num
      nlinarith
    have hac : ((Real.sqrt (12/13))⁻¹ : ℂ) * ((Real.sqrt 2)⁻¹ : ℂ) = 13 / (2 * (Real.sqrt 78 : ℂ)) := by exact_mod_cast ha
    have hbc : ((Real.sqrt (12/13))⁻¹ : ℂ) * (Real.sqrt (1/13) : ℂ) * ((Real.sqrt 26)⁻¹ : ℂ) = 1 / (2 * (Real.sqrt 78 : ℂ)) := by exact_mod_cast hb
    classical
    let delta : Fin 2 × Fin 2 → ℂ := fun b => if b.1=b.2 then 1 else 0
    have hpsi : star (maxEntangledVector (Fin 2)) =
        ((Real.sqrt 2 : ℂ)⁻¹) • delta := by
      ext ⟨a,b⟩
      fin_cases a <;> fin_cases b <;>
        norm_num [maxEntangledVector, Fintype.card_fin, Pi.star_apply, delta, Complex.ofReal_inv]
    have hvec (ij : Fin 2 × Fin 2) :
        Matrix.vecMulVec (fun a => if a=ij then (1:ℂ) else 0) (star (maxEntangledVector (Fin 2))) =
          ((Real.sqrt 2 : ℂ)⁻¹) • Matrix.vecMulVec (fun a => if a=ij then (1:ℂ) else 0) delta := by
      rw [hpsi]
      ext a b
      simp only [Matrix.vecMulVec, Matrix.of_apply, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul]
      ring
    have hd1 : (Real.sqrt (12/13) : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹ =
        (Real.sqrt 78 : ℂ)⁻¹ * (1/2) * 13 := by rw [hac]; ring
    have hd2 : (Real.sqrt (12/13) : ℂ)⁻¹ * (Real.sqrt (1/13) : ℂ) * (Real.sqrt 26 : ℂ)⁻¹ =
        (Real.sqrt 78 : ℂ)⁻¹ * (1/2) := by rw [hbc]; ring
    intro ij
    simp only [sourceE, h4, h5, hvec, sourceB, hQ, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_smul, Matrix.conjTranspose_conjTranspose,
      Complex.star_def, map_inv₀, Complex.conj_ofReal, Matrix.smul_mul,
      smul_sub, smul_smul, Matrix.mul_assoc]
    rw [hd1, ← mul_assoc, hd2]
    ext a b
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.sub_apply, delta]
    ring

  have hE : ∀ ij, sourceE 2 (9/13) ij = (Real.sqrt 78 : ℂ)⁻¹ • T ij := by
    simpa only [T, hA] using hEraw

  have hK : (∑ r, (K r).conjTranspose * K r) = 1 := by
    have hint : (2808 : ℂ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) +
        (490 : ℂ) • (A*A) + (21 : ℂ) • ∑ ij, (T ij).conjTranspose * T ij = (10816:ℂ) • 1 := by
      ext ⟨a,b⟩ ⟨c,d⟩
      fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
        norm_num [A, T, sourceD, Matrix.mul_apply, Matrix.conjTranspose_apply, map_ofNat,
          Matrix.vecMulVec, Matrix.single, Matrix.sum_apply, Fintype.sum_prod_type,
          Fin.sum_univ_two, Matrix.one_apply]
    have hreplace : (∑ ab : (Fin 2 × Fin 2) × (Fin 2 × Fin 2),
        (Matrix.single ab.1 ab.2 (1:ℂ)).conjTranspose * Matrix.single ab.1 ab.2 1) =
        (4:ℂ) • 1 := by
      ext ⟨a,b⟩ ⟨c,d⟩
      fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
        norm_num [Matrix.mul_apply, Matrix.conjTranspose_apply, map_ofNat, Matrix.single,
          Matrix.sum_apply, Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.one_apply]
    have hreset : ∑ st, (R st).conjTranspose * R st = (2:ℂ) • (A*A) := by
      ext ⟨a,b⟩ ⟨c,d⟩
      fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
        norm_num [R, A, Matrix.mul_apply, Matrix.conjTranspose_apply, map_ofNat, Matrix.single,
          Matrix.sum_apply, Matrix.kroneckerMap_apply, Fintype.sum_prod_type,
          Fin.sum_univ_two, Matrix.one_apply]
    have hscale (q : ℝ) (hq : 0 ≤ q)
        (M : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
        ((Real.sqrt q / 104 : ℂ) • M).conjTranspose * ((Real.sqrt q / 104 : ℂ) • M) =
          (q / 10816 : ℂ) • (M.conjTranspose * M) := by
      rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
      have hcoeff : star (Real.sqrt q / 104 : ℂ) * (Real.sqrt q / 104 : ℂ) = (q / 10816 : ℂ) := by
        simp only [star_div₀, Complex.star_def, Complex.conj_ofReal, map_ofNat]
        calc
          _ = (Real.sqrt q : ℂ)^2 / (104:ℂ)^2 := by ring
          _ = _ := by rw [← Complex.ofReal_pow, Real.sq_sqrt hq]; norm_num
      rw [hcoeff]
    simp only [K, Fintype.sum_sum_type]
    simp_rw [hscale 702 (by norm_num), hscale 245 (by norm_num), hscale 21 (by norm_num)]
    simp only [← Finset.smul_sum, hreplace, hreset, smul_smul]
    have h := congrArg ((10816:ℂ)⁻¹ • ·) hint
    norm_num [smul_add, smul_smul] at h ⊢
    simpa only [add_assoc] using h

  have hNoise : PhyslibLeaf.MatrixMap.of_kraus K K = sourceNoise 2 (9/13) := by
    classical
    have hscalar (q : ℝ) (hq : 0 ≤ q) :
        (Real.sqrt q / 104 : ℂ) * star (Real.sqrt q / 104 : ℂ) = (q / 10816 : ℂ) := by
      simp only [star_div₀, Complex.star_def, Complex.conj_ofReal, map_ofNat]
      calc
        _ = (Real.sqrt q : ℂ)^2 / (104:ℂ)^2 := by ring
        _ = _ := by rw [← Complex.ofReal_pow, Real.sq_sqrt hq]; norm_num
    have hscale (q : ℝ) (hq : 0 ≤ q)
        (M X : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
        ((Real.sqrt q / 104 : ℂ) • M) * X * ((Real.sqrt q / 104 : ℂ) • M).conjTranspose =
          (q / 10816 : ℂ) • (M * X * M.conjTranspose) := by
      rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.smul_mul,
        Matrix.mul_smul, smul_smul, hscalar q hq]
    have hreplace (X : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
        (∑ ab : (Fin 2 × Fin 2) × (Fin 2 × Fin 2),
         Matrix.single ab.1 ab.2 1 * X * (Matrix.single ab.1 ab.2 (1:ℂ)).conjTranspose) =
         Matrix.trace X • 1 := by
      ext ⟨a,b⟩ ⟨c,d⟩
      fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
        simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.single,
          Matrix.sum_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
          Matrix.trace, Matrix.diag_apply]
    have hreset (X : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
        (∑ st : Fin 2 × Fin 2, R st * X * (R st).conjTranspose) =
        Matrix.kronecker (partialTraceRight (A*X*A)) (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
      dsimp only [R]
      simp only [Matrix.conjTranspose_mul, hA]
      ext ⟨a,b⟩ ⟨c,d⟩
      fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
        simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.single,
          Matrix.sum_apply, Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.one_apply,
          Matrix.kroneckerMap_apply, partialTraceRight]
      all_goals ring
    have hs26 : (Real.sqrt 26 : ℂ)^2 = 26 := by norm_num [← Complex.ofReal_pow]
    have hs78 : (Real.sqrt 78 : ℂ)^2 = 78 := by norm_num [← Complex.ofReal_pow]
    have h26 : (Real.sqrt 26 : ℂ)⁻¹ * (Real.sqrt 26 : ℂ)⁻¹ = 1/26 := by
      rw [← mul_inv_rev, ← pow_two, hs26]; norm_num
    have h78 : (Real.sqrt 78 : ℂ)⁻¹ * (Real.sqrt 78 : ℂ)⁻¹ = 1/78 := by
      rw [← mul_inv_rev, ← pow_two, hs78]; norm_num
    have hpartial (z : ℂ) (X : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
        partialTraceRight (z • X) = z • partialTraceRight X := by
      ext a b
      simp [partialTraceRight]
      ring
    apply LinearMap.ext
    intro X
    change (∑ r, K r * X * (K r).conjTranspose) = (sourceNoise 2 (9/13)) X
    simp only [K, Fintype.sum_sum_type,
      hscale 702 (by norm_num), hscale 245 (by norm_num), hscale 21 (by norm_num),
      ← Finset.smul_sum, hreplace, hreset]
    simp only [sourceNoise, hQ, hE, Matrix.conjTranspose_smul,
      Complex.star_def, map_inv₀, Complex.conj_ofReal, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      h26, h78, hpartial]
    ext a b
    norm_num [lambda1, lambda2, lambda3, lambda4,
      Matrix.kroneckerMap_apply, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul,
      Finset.mul_sum]
    ring

  let V (x y : ℝ) : Matrix (Fin 2 × Fin 2) (Fin 2) ℂ := Matrix.of
    (fun a b => if b=0 then (if a=(0,0) then (x:ℂ) else if a=(1,1) then (y:ℂ) else 0)
      else if a=(1,0) then 1 else 0)

  have hPolar : sourcePolar 2 (9/13) (fun i => if i=0 then 1 else 0) =
      V (3/Real.sqrt 10) (-1/Real.sqrt 10) := by
    have hAdef : A = Matrix.of (fun a b : Fin 2 × Fin 2 =>
      if a=b then (if a.1=a.2 then 3 else 4)
      else if a.1=a.2 ∧ b.1=b.2 then -1 else 0) := rfl
    classical
    let chi : Fin 2 → ℂ := fun i => if i=0 then 1 else 0
    let C := sourceC 2 (9/13) chi
    let G : Matrix (Fin 2) (Fin 2) ℂ := Matrix.diagonal
      (fun i => if i=0 then 10/26 else 16/26)
    let H : Matrix (Fin 2) (Fin 2) ℂ := Matrix.diagonal
      (fun i => ((if i=0 then Real.sqrt 10 / Real.sqrt 26 else 4 / Real.sqrt 26 : ℝ) : ℂ))
    let Hinv : Matrix (Fin 2) (Fin 2) ℂ := Matrix.diagonal
      (fun i => ((if i=0 then Real.sqrt 26 / Real.sqrt 10 else Real.sqrt 26 / 4 : ℝ) : ℂ))
    have hs10 : (Real.sqrt 10 : ℂ)^2 = 10 := by norm_num [← Complex.ofReal_pow]
    have hs26 : (Real.sqrt 26 : ℂ)^2 = 26 := by norm_num [← Complex.ofReal_pow]
    have hn10 : (Real.sqrt 10 : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 (by norm_num : (0:ℝ)<10)))
    have hn26 : (Real.sqrt 26 : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 (by norm_num : (0:ℝ)<26)))
    have hC : C = ((Real.sqrt 26)⁻¹ : ℂ) • (A * (sourceD 2 0).conjTranspose) := by
      dsimp [C, sourceC, chi]
      rw [hQ, Matrix.smul_mul]
      congr 2
      ext ⟨a,b⟩ c
      fin_cases a <;> fin_cases b <;> fin_cases c <;>
        norm_num [sourceD, Matrix.conjTranspose_apply, Matrix.of_apply]
    have hG : C.conjTranspose * C = G := by
      rw [hC, hAdef]
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [G, sourceD, Matrix.mul_apply, Matrix.conjTranspose_apply, map_ofNat,
          Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.diagonal_apply,
          Matrix.smul_apply, Matrix.of_apply, ← Complex.ofReal_inv]
      all_goals field_simp
      all_goals ring_nf
      all_goals norm_num [hs26]
    have hHpos : 0 ≤ CStarMatrix.ofMatrix H := by
      apply map_nonneg CStarMatrix.ofMatrixStarAlgEquiv
      apply Matrix.PosSemidef.nonneg
      apply Matrix.PosSemidef.diagonal
      intro i
      fin_cases i <;> simp only [H, if_true, if_false]
      all_goals apply Complex.zero_le_real.mpr
      all_goals positivity
    have hHsq : H * H = G := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [H, G, Matrix.mul_apply, Matrix.diagonal_apply, Fin.sum_univ_two]
      all_goals field_simp
      all_goals ring_nf
      all_goals norm_num [hs10,hs26]
    have hsqrt : CFC.sqrt (CStarMatrix.ofMatrix (C.conjTranspose * C)) = CStarMatrix.ofMatrix H := by
      apply CFC.sqrt_unique _ hHpos
      change H*H = C.conjTranspose*C
      rw [hG,hHsq]
    have hleft : Hinv*H=1 := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [H, Hinv, Matrix.mul_apply, Matrix.diagonal_apply, Matrix.one_apply,
          Fin.sum_univ_two, hn10, hn26]
      all_goals field_simp
      all_goals ring
    have hright : H*Hinv=1 := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [H, Hinv, Matrix.mul_apply, Matrix.diagonal_apply, Matrix.one_apply,
          Fin.sum_univ_two, hn10, hn26]
      all_goals field_simp
      all_goals ring
    let P : Matrix (Fin 2 × Fin 2) (Fin 2) ℂ := Matrix.of
      (fun a b => if b=0 then (if a=(0,0) then ((3/Real.sqrt 10:ℝ):ℂ)
        else if a=(1,1) then ((-1/Real.sqrt 10:ℝ):ℂ) else 0)
        else if a=(1,0) then 1 else 0)
    have hfactor : C = P * H := by
      rw [hC,hAdef]
      ext ⟨a,b⟩ c
      fin_cases a <;> fin_cases b <;> fin_cases c <;>
        norm_num [P, H, sourceD, Matrix.mul_apply, Matrix.conjTranspose_apply,
          Matrix.smul_apply, Matrix.of_apply, Matrix.diagonal_apply,
          Fintype.sum_prod_type, Fin.sum_univ_two, hn10, hn26]
      all_goals field_simp
      all_goals ring
    have hinv : H⁻¹ = Hinv := Matrix.inv_eq_left_inv hleft
    change sourcePolar 2 (9/13) chi = P
    change C * (CStarMatrix.ofMatrix.symm (CFC.sqrt (CStarMatrix.ofMatrix (C.conjTranspose*C))))⁻¹ = P
    rw [hsqrt]
    change C * H⁻¹ = P
    rw [hinv, hfactor, Matrix.mul_assoc, hright, Matrix.mul_one]

  have hFidelity (d : ℕ) (hd : 0 < d) {k : Type} [Fintype k]
    (L : k → Matrix (Fin d) (Fin d) ℂ) :
    entanglementFidelity d (PhyslibLeaf.MatrixMap.of_kraus L L) =
      (d : ℝ)⁻¹ ^ 2 * ∑ r, Complex.normSq (Matrix.trace (L r)) := by
    classical
    let c : ℂ := (Real.sqrt (d : ℝ))⁻¹
    have hcstar : star c = c := by simp [c]
    let : NeZero d := ⟨Nat.ne_of_gt hd⟩
    have hcc : c*c = ((d : ℝ)⁻¹ : ℝ) := by
      simpa [Matrix.single_kronecker_single, Matrix.transpose_single,
        Matrix.trace_mul_single, maxEntangled, maxEntangledVector,
        Fintype.card_fin, Matrix.vecMulVec, c] using
        max_entangled_trace (Fin d) (Matrix.single 0 0 1) (Matrix.single 0 0 1)
    let delta : Fin d × Fin d → ℂ := fun a => if a.1 = a.2 then 1 else 0
    have hpsi : maxEntangledVector (Fin d) = c • delta := by
      ext a
      simp [maxEntangledVector, Fintype.card_fin, c, delta]
    have hproj : maxEntangled (Fin d) =
        (c*c) • Matrix.vecMulVec delta (star delta) := by
      ext a b
      simp [maxEntangled, hpsi, Matrix.vecMulVec, hcstar, Pi.star_apply, star_mul]
      ring
    have hmap : PhyslibLeaf.MatrixMap.kron (PhyslibLeaf.MatrixMap.of_kraus L L) LinearMap.id
        (maxEntangled (Fin d)) =
        (c*c) • PhyslibLeaf.MatrixMap.choi_matrix (PhyslibLeaf.MatrixMap.of_kraus L L) := by
      rw [hproj, map_smul]
      congr 1
      exact (PhyslibLeaf.MatrixMap.choi_matrix_eq_map_proj _).symm
    have hcontract (M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
        dotProduct (star (maxEntangledVector (Fin d)))
          (M.mulVec (maxEntangledVector (Fin d))) =
          (c*c) * ∑ a : Fin d, ∑ b : Fin d, M (a,a) (b,b) := by
      simp [hpsi, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, delta,
        hcstar, Finset.mul_sum, Finset.sum_mul, Pi.star_apply,
        apply_ite, mul_assoc, mul_comm, mul_left_comm]
    dsimp only [entanglementFidelity]
    rw [hmap, hcontract]
    simp only [Matrix.smul_apply, smul_eq_mul, ← Finset.mul_sum]
    rw [hcc, PhyslibLeaf.MatrixMap.choi_of_kraus]
    simp only [Matrix.sum_apply, Matrix.vecMulVec, Matrix.of_apply]
    have hsum : (∑ a : Fin d, ∑ b : Fin d, ∑ r : k,
        L r a a * star (L r b b)) =
        ∑ r : k, Matrix.trace (L r) * star (Matrix.trace (L r)) := by
      simp only [Matrix.trace, Matrix.diag_apply, star_sum, Finset.sum_mul, Finset.mul_sum]
      calc
        _ = ∑ a : Fin d, ∑ r : k, ∑ b : Fin d, L r a a * star (L r b b) := by
          apply Finset.sum_congr rfl
          intro a ha
          rw [Finset.sum_comm]
        _ = ∑ r : k, ∑ a : Fin d, ∑ b : Fin d, L r a a * star (L r b b) := by
          rw [Finset.sum_comm]
        _ = _ := by
          apply Finset.sum_congr rfl
          intro r hr
          rw [Finset.sum_comm]
    rw [hsum]
    simp [Complex.mul_conj, Finset.mul_sum, pow_two, mul_assoc]

  have hEncoder {a b : Type} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b] (V : Matrix b a ℂ)
    (hV : V.conjTranspose * V = 1) :
    ∃ C : QuantumChannel a b,
      matrixAction C.toCompletelyPositiveMap =
        PhyslibLeaf.MatrixMap.of_kraus (fun _ : Unit => V) (fun _ : Unit => V) ∧
      TraceNonincreasing C.toCompletelyPositiveMap ∧
      (inputFirstChoi (matrixAction C.toCompletelyPositiveMap)).rank ≤ 1 := by
    classical
    obtain ⟨C,hC⟩ := finite_kraus_quantum_channel (fun _ : Unit => V) (by simpa using hV)
    have hmap : matrixAction C.toCompletelyPositiveMap =
        PhyslibLeaf.MatrixMap.of_kraus (fun _ : Unit => V) (fun _ : Unit => V) := by
      ext X i j
      change CStarMatrix.ofMatrix.symm (C.toCompletelyPositiveMap (CStarMatrix.ofMatrix X)) i j = _
      rw [hC]
      simp [PhyslibLeaf.MatrixMap.of_kraus]
    refine ⟨C,hmap,?_,?_⟩
    · intro X hX
      change (Matrix.trace (C.toCompletelyPositiveMap (CStarMatrix.ofMatrix X))).re ≤ _
      rw [C.trace_preserving]
      exact le_rfl
    · rw [inputFirstChoi, Matrix.rank_reindex, hmap, PhyslibLeaf.MatrixMap.choi_of_kraus]
      simpa using Matrix.rank_vecMulVec_le (fun x : b×a => V x.1 x.2)
        (fun x : b×a => star (V x.1 x.2))

  have hRight (d : ℕ) (X : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
      (rightTrace d) X = ∑ j, sourceD d j * X * (sourceD d j).conjTranspose := by
    classical
    ext a b
    simp [rightTrace, partialTraceRight, sourceD, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.sum_apply, Fintype.sum_prod_type, Finset.sum_ite_eq, ite_and, apply_ite]

  have hDcomplete (d : ℕ) : ∑ j, (sourceD d j).conjTranspose * sourceD d j = 1 := by
    classical
    ext ⟨a,b⟩ ⟨c,e⟩
    simp [sourceD, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.sum_apply,
      Matrix.one_apply, ite_and, apply_ite, eq_comm]
    by_cases hac : a=c <;> by_cases hbe : b=e <;> simp [hac,hbe]

  have hComp {a b c : Type} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b] [Fintype c] [DecidableEq c]
    (second : QuantumChannel b c) (first : QuantumChannel a b) :
    matrixAction (second.comp first).toCompletelyPositiveMap =
      (matrixAction second.toCompletelyPositiveMap).comp
        (matrixAction first.toCompletelyPositiveMap) := by
    ext X i j
    change CStarMatrix.ofMatrix.symm ((second.comp first).toCompletelyPositiveMap
      (CStarMatrix.ofMatrix X)) i j = _
    rw [QuantumChannel.comp_apply]
    rfl

  have hComposite {k : Type} [Fintype k]
      (K : k → Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
      (V : Matrix (Fin 2 × Fin 2) (Fin 2) ℂ) :
      PhyslibLeaf.MatrixMap.of_kraus (fun jr : Fin 2 × k => sourceD 2 jr.1 * K jr.2 * V)
        (fun jr : Fin 2 × k => sourceD 2 jr.1 * K jr.2 * V) =
      (PhyslibLeaf.MatrixMap.of_kraus (sourceD 2) (sourceD 2)).comp
        ((PhyslibLeaf.MatrixMap.of_kraus K K).comp
          (PhyslibLeaf.MatrixMap.of_kraus (fun _ : Unit => V) (fun _ : Unit => V))) := by
    classical
    ext X i j
    simp [PhyslibLeaf.MatrixMap.of_kraus, LinearMap.comp_apply,
      Matrix.conjTranspose_mul,
      Matrix.mul_assoc, Fintype.sum_prod_type, Finset.sum_add_distrib]

  have hIsometry (x y : ℝ) (hxy : x^2+y^2=1) : (V x y).conjTranspose * V x y=1 := by
    have hc : (x:ℂ)^2+(y:ℂ)^2=1 := by exact_mod_cast hxy
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [V, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
        Matrix.one_apply, Fintype.sum_prod_type, Fin.sum_univ_two]
    linear_combination hc

  have hTracePolynomial (x y : ℝ) :
      (1/4:ℝ) * (∑ j : Fin 2, ∑ r, Complex.normSq (Matrix.trace (sourceD 2 j * K r * V x y))) =
      (132*x^2+210*x+76*y^2-98*y+181)/832 := by
    dsimp only [K, R, T, A, V]
    have hs702 : Real.sqrt 702 ^ 2 = 702 := by norm_num
    have hs245 : Real.sqrt 245 ^ 2 = 245 := by norm_num
    have hs21 : Real.sqrt 21 ^ 2 = 21 := by norm_num
    simp [Fintype.sum_sum_type, Fintype.sum_prod_type, Fin.sum_univ_two,
      sourceD, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.of_apply, Matrix.smul_apply, Matrix.single, Matrix.vecMulVec,
      Matrix.kroneckerMap_apply, Matrix.one_apply, Complex.normSq_apply]
    ring_nf
    rw [hs702,hs245,hs21]
    ring

  obtain ⟨N, hNraw⟩ := finite_kraus_quantum_channel K hK
  have hN : matrixAction N.toCompletelyPositiveMap = sourceNoise 2 (9/13) := by
    apply LinearMap.ext
    intro X
    change CStarMatrix.ofMatrix.symm (N.toCompletelyPositiveMap (CStarMatrix.ofMatrix X)) = _
    rw [hNraw]
    change (PhyslibLeaf.MatrixMap.of_kraus K K) X = _
    rw [hNoise]
  obtain ⟨D, hDraw⟩ := finite_kraus_quantum_channel (sourceD 2) (hDcomplete 2)
  have hD : matrixAction D.toCompletelyPositiveMap = rightTrace 2 := by
    apply LinearMap.ext
    intro X
    change CStarMatrix.ofMatrix.symm (D.toCompletelyPositiveMap (CStarMatrix.ofMatrix X)) = _
    rw [hDraw]
    exact (hRight 2 X).symm
  have hDTNI : TraceNonincreasing D.toCompletelyPositiveMap := by
    intro X hX
    change (Matrix.trace (D.toCompletelyPositiveMap (CStarMatrix.ofMatrix X))).re ≤ _
    rw [D.trace_preserving]
    exact le_rfl
  have hRightMap : rightTrace 2 = PhyslibLeaf.MatrixMap.of_kraus (sourceD 2) (sourceD 2) := by
    apply LinearMap.ext
    intro X
    exact hRight 2 X
  have hObjective (x y : ℝ) (hxy : x^2+y^2=1) :
      entanglementFidelity 2 ((rightTrace 2).comp ((sourceNoise 2 (9/13)).comp
        (PhyslibLeaf.MatrixMap.of_kraus (fun _ : Unit => V x y) (fun _ : Unit => V x y)))) =
      (132*x^2+210*x+76*y^2-98*y+181)/832 := by
    obtain ⟨C,hC,hCTNI,hCRank⟩ := hEncoder (V x y) (hIsometry x y hxy)
    let S := D.comp (N.comp C)
    have hS : matrixAction S.toCompletelyPositiveMap =
        (rightTrace 2).comp ((sourceNoise 2 (9/13)).comp
          (PhyslibLeaf.MatrixMap.of_kraus (fun _ : Unit => V x y) (fun _ : Unit => V x y))) := by
      dsimp only [S]
      rw [hComp, hComp, hD, hN, hC]
    have h48 : matrixAction S.toCompletelyPositiveMap =
        PhyslibLeaf.MatrixMap.of_kraus
          (fun jr : Fin 2 × (((Fin 2 × Fin 2) × (Fin 2 × Fin 2)) ⊕
              ((Fin 2 × Fin 2) ⊕ (Fin 2 × Fin 2))) => sourceD 2 jr.1 * K jr.2 * V x y)
          (fun jr : Fin 2 × (((Fin 2 × Fin 2) × (Fin 2 × Fin 2)) ⊕
              ((Fin 2 × Fin 2) ⊕ (Fin 2 × Fin 2))) => sourceD 2 jr.1 * K jr.2 * V x y) := by
      rw [hS, hRightMap, ← hNoise, hComposite]
    calc
      _ = entanglementFidelity 2 (matrixAction S.toCompletelyPositiveMap) := by rw [hS]
      _ = (1/4:ℝ) * (∑ j : Fin 2, ∑ r, Complex.normSq
          (Matrix.trace (sourceD 2 j * K r * V x y))) := by
        rw [h48, hFidelity 2 (by norm_num)]
        norm_num [Fintype.sum_prod_type]
      _ = _ := hTracePolynomial x y
  have hVunit : (3 / Real.sqrt 10 : ℝ)^2 + (-1 / Real.sqrt 10)^2=1 := by
    rw [div_pow, div_pow]
    norm_num
  have hVvalue :
      (132*(3/Real.sqrt 10)^2+210*(3/Real.sqrt 10)+76*(-1/Real.sqrt 10)^2-
        98*(-1/Real.sqrt 10)+181)/832 = (1537/4160 : ℝ)+7*Real.sqrt 10/80 := by
    have hs : Real.sqrt 10 ^ 2 = 10 := by norm_num
    have hn : Real.sqrt 10 ≠ 0 := by positivity
    have hs3 : Real.sqrt 10 ^ 3 = 10 * Real.sqrt 10 := by
      calc
        _ = Real.sqrt 10 ^ 2 * Real.sqrt 10 := by ring
        _ = _ := by rw [hs]
    field_simp
    ring_nf
    nlinarith
  have hWunit : (24/25 : ℝ)^2+(-7/25)^2=1 := by norm_num
  have hWvalue :
      (132*(24/25)^2+210*(24/25)+76*(-7/25)^2-98*(-7/25)+181)/832 =
        (336031/520000 : ℝ) := by norm_num
  have hVscore := (hObjective (3/Real.sqrt 10) (-1/Real.sqrt 10) hVunit).trans hVvalue
  have hWscore := (hObjective (24/25) (-7/25) hWunit).trans hWvalue
  have hStrict : (1537/4160 : ℝ) + 7 * Real.sqrt 10 / 80 < 336031/520000 := by
    have hs : Real.sqrt 10 ^ 2 = 10 := by norm_num
    have hn : 0 ≤ Real.sqrt 10 := Real.sqrt_nonneg _
    have hsq : (10279 : ℝ)^2 - 10 * 3250^2 = 32841 := by norm_num
    have ht : 3250 * Real.sqrt 10 < 10279 := by nlinarith
    have hGap : (336031/520000:ℝ) - (1537/4160 + 7*Real.sqrt 10/80) =
        7*(10279-3250*Real.sqrt 10)/260000 := by ring
    have hGapPos : (0:ℝ) < 7*(10279-3250*Real.sqrt 10)/260000 := by linarith
    linarith
  intro hclaim
  obtain ⟨C,hC,hCTNI,hCRank⟩ := hEncoder (V (24/25) (-7/25)) (hIsometry _ _ hWunit)
  have hchi : (∑ i : Fin 2, Complex.normSq (if i=0 then (1:ℂ) else 0))=1 := by
    norm_num [Fin.sum_univ_two, Complex.normSq_apply]
  have h := hclaim 2 (by norm_num) (9/13) (by norm_num) (by norm_num)
    (fun i => if i=0 then 1 else 0) hchi C.toCompletelyPositiveMap D.toCompletelyPositiveMap
    hCTNI hDTNI hCRank
  rw [hC, hD, hPolar, hWscore, hVscore] at h
  exact (not_le_of_gt hStrict) h

end D5.S3.Quantum.Recovery.LiJiangPolarPairOptimalityRefutation
