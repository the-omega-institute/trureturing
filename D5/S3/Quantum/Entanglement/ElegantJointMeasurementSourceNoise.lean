/- GID: D5/S3/Quantum/Entanglement/ElegantJointMeasurementSourceNoise
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/ElegantJointMeasurementSourceNoise
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Physical elegant joint measurements on three independently noisy singlet sources. -/

import D5.S3.Quantum.Entanglement.TriangleIndependentSourceNoise
import Mathlib.Tactic
import Mathlib.NumberTheory.Zsqrtd.GaussianInt

/-
The EJM basis is the singlet plus the three Cartesian triplets with tetrahedral
signs. Its vectors have a common 1/(2 sqrt 2) normalization, so the effects are
exact complex rational matrices (1/8) u u*. Source noise is a separate
white-noise mixture on each bipartite singlet before the tensor Born rule.
The exact three-visibility law is the missing physical realization bridge for
triangle inflation certificates, not a global interpolation of tables.
admission_basis: escape-witness
ejm_noise_probability: proof_shape: content; escape_witness: contracting the
three independently noisy singlet matrices with the cyclic EJM effects yields
the equality-pattern polynomial with three independently variable visibilities.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace D5.S3.Quantum.Entanglement.ElegantJointMeasurementSourceNoise

open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Entanglement.TriangleIndependentSourceNoise
open scoped CStarAlgebra ComplexOrder MatrixOrder Kronecker

/-- The four tetrahedral sign vectors, with product of signs equal to one. -/
def tetraX (j : Fin 4) : ℂ := if j.val < 2 then 1 else -1
def tetraY (j : Fin 4) : ℂ := if j.val = 0 ∨ j.val = 2 then 1 else -1
def tetraZ (j : Fin 4) : ℂ := if j.val = 0 ∨ j.val = 3 then 1 else -1

/-- Unnormalized EJM vectors in computational qubit order 00,01,10,11.
Multiplication by 1/(2 sqrt 2) gives the orthonormal elegant joint basis. -/
def ejmVector (j : Fin 4) (q : Bool × Bool) : ℂ :=
  if q.1 then
    if q.2 then -tetraX j + Complex.I * tetraY j else tetraZ j - 1
  else
    if q.2 then tetraZ j + 1 else tetraX j + Complex.I * tetraY j

/-- EJM outcome projectors, without introducing square roots into the entries. -/
def ejmEffect (j : Fin 4) : Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  (1 / 8 : ℝ) • Matrix.vecMulVec (ejmVector j) (star (ejmVector j))

private theorem ejm_effect_complete : ∑ j, ejmEffect j = 1 := by
  ext ⟨a, b⟩ ⟨c, d⟩
  cases a <;> cases b <;> cases c <;> cases d <;>
    norm_num [ejmEffect, ejmVector, tetraX, tetraY, tetraZ,
      Matrix.vecMulVec_apply, Matrix.one_apply, Fin.sum_univ_succ,
      Complex.real_smul, Complex.ext_iff]

/-- The actual four-outcome EJM measurement on two qubits. -/
def ejm : LocalPOVM (Bool × Bool) (Fin 4) where
  effect := ejmEffect
  positive j := (Matrix.posSemidef_vecMulVec_self_star (ejmVector j)).smul (by norm_num)
  complete := ejm_effect_complete

/-- Unnormalized two-qubit singlet: |01> - |10>. -/
def singletVector (q : Bool × Bool) : ℂ :=
  if q.1 then if q.2 then 0 else -1 else if q.2 then 1 else 0

/-- The physical singlet density matrix. -/
def singlet : DensityState (Bool × Bool) := by
  let m : Matrix (Bool × Bool) (Bool × Bool) ℂ :=
    (1 / 2 : ℝ) • Matrix.vecMulVec singletVector (star singletVector)
  refine ⟨CStarMatrix.ofMatrix m, ?_, ?_⟩
  · exact map_nonneg CStarMatrix.ofMatrixStarAlgEquiv
      ((Matrix.posSemidef_vecMulVec_self_star singletVector).smul
        (by norm_num : (0 : ℝ) ≤ 1 / 2)).nonneg
  · change Matrix.trace m = 1
    norm_num [m, Matrix.trace, Matrix.diag, Matrix.vecMulVec_apply,
      singletVector, Fintype.sum_prod_type, Fintype.sum_bool,
      Complex.real_smul]

/-- Two-qubit white noise I/4, separately applied to each edge. -/
def whiteNoise : DensityState (Bool × Bool) := by
  let m : Matrix (Bool × Bool) (Bool × Bool) ℂ := (1 / 4 : ℝ) • 1
  refine ⟨CStarMatrix.ofMatrix m, ?_, ?_⟩
  · exact map_nonneg CStarMatrix.ofMatrixStarAlgEquiv
      (Matrix.PosSemidef.one.smul (by norm_num : (0 : ℝ) ≤ 1 / 4)).nonneg
  · change Matrix.trace m = 1
    norm_num [m, Matrix.trace, Matrix.diag, Matrix.one_apply,
      Fintype.sum_prod_type, Fintype.sum_bool, Complex.real_smul]

/-- Actual cyclic EJM Born distribution of independent noisy singlet sources.
The arguments are the AB, BC and CA source visibilities, respectively. -/
def ejmProbability (x y z : ℝ) : Fin 4 → Fin 4 → Fin 4 → ℝ :=
  noisyTriangle whiteNoise singlet whiteNoise singlet whiteNoise singlet
    ejm ejm ejm x y z

/-- The exact physical law: shared equality patterns distinguish which edge
remains visible. This is independently affine in each source visibility. -/
def ejmNoiseTable (x y z : ℝ) (a b c : Fin 4) : ℝ :=
  (if a = b ∧ b = c then
      4 + 3 * (x + y + z) + 3 * (x * y + x * z + y * z) + 3 * x * y * z
    else if a = b then
      4 + 3 * x - y - z - (x * y + x * z + y * z) - x * y * z
    else if b = c then
      4 - x + 3 * y - z - (x * y + x * z + y * z) - x * y * z
    else if c = a then
      4 - x - y + 3 * z - (x * y + x * z + y * z) - x * y * z
    else
      4 - (x + y + z) + (x * y + x * z + y * z) + x * y * z) / 256

private def integerEjmVector (j : Fin 4) (q : Bool × Bool) : GaussianInt :=
  let sx : ℤ := if j.val < 2 then 1 else -1
  let sy : ℤ := if j.val = 0 ∨ j.val = 2 then 1 else -1
  let sz : ℤ := if j.val = 0 ∨ j.val = 3 then 1 else -1
  if q.1 then
    if q.2 then ⟨-sx, sy⟩ else ⟨sz - 1, 0⟩
  else
    if q.2 then ⟨sz + 1, 0⟩ else ⟨sx, sy⟩

private def integerSinglet (q : Bool × Bool) : GaussianInt :=
  if q.1 then if q.2 then 0 else -1 else if q.2 then 1 else 0

private def integerSource (signal : Bool) : Matrix (Bool × Bool) (Bool × Bool) GaussianInt :=
  if signal then (2 : GaussianInt) • Matrix.vecMulVec integerSinglet (star integerSinglet) else 1

private def integerEffect (j : Fin 4) : Matrix (Bool × Bool) (Bool × Bool) GaussianInt :=
  Matrix.vecMulVec (integerEjmVector j) (star (integerEjmVector j))

private def integerBorn (i j k : Bool) (a b c : Fin 4) : GaussianInt :=
  Matrix.trace ((integerSource i ⊗ₖ (integerSource j ⊗ₖ integerSource k)) *
    (integerEffect a ⊗ₖ (integerEffect b ⊗ₖ integerEffect c)).submatrix
      (incidentWires Bool Bool Bool Bool Bool Bool)
      (incidentWires Bool Bool Bool Bool Bool Bool))

private abbrev sourceIndex :=
  (Bool × Bool) × ((Bool × Bool) × (Bool × Bool))

private def integerBornSparse (i j k : Bool) (a b c : Fin 4) : GaussianInt :=
  ∑ p : sourceIndex, ∑ q : sourceIndex,
    (integerSource i p.1 q.1) *
      ((integerSource j p.2.1 q.2.1) * (integerSource k p.2.2 q.2.2)) *
      (integerEffect a ⊗ₖ (integerEffect b ⊗ₖ integerEffect c)).submatrix
        (incidentWires Bool Bool Bool Bool Bool Bool)
        (incidentWires Bool Bool Bool Bool Bool Bool) q p

private theorem integerBorn_eq_sparse (i j k : Bool) (a b c : Fin 4) :
    integerBorn i j k a b c = integerBornSparse i j k a b c := by
  simp [integerBorn, integerBornSparse, Matrix.trace, Matrix.mul_apply,
    Matrix.submatrix_apply]

private def sourceRow (signal u v : Bool) : Bool × Bool :=
  if signal then (u, !u) else (u, v)

private def sourceCol (signal u v : Bool) : Bool × Bool :=
  if signal then (v, !v) else (u, v)

private def sourceCoeff (signal u v : Bool) : GaussianInt :=
  if signal then if u = v then 2 else -2 else 1

private theorem source_support_sum (signal : Bool)
    (f : (Bool × Bool) → (Bool × Bool) → GaussianInt) :
    (∑ p, ∑ q, integerSource signal p q * f q p) =
      ∑ u : Bool, ∑ v : Bool,
        sourceCoeff signal u v * f (sourceCol signal u v) (sourceRow signal u v) := by
  cases signal <;>
    simp [integerSource, integerSinglet, Matrix.vecMulVec_apply,
      Matrix.smul_apply, Matrix.one_apply, Fintype.sum_prod_type,
      sourceCoeff, sourceCol, sourceRow]
  all_goals ring

private theorem regroup_source_sum {α : Type} [Fintype α]
    (f : α → α → α → α → α → α → GaussianInt) :
    (∑ p : α × (α × α), ∑ q : α × (α × α),
      f p.1 q.1 p.2.1 q.2.1 p.2.2 q.2.2) =
      ∑ p₁, ∑ q₁, ∑ p₂, ∑ q₂, ∑ p₃, ∑ q₃,
        f p₁ q₁ p₂ q₂ p₃ q₃ := by
  simp only [Fintype.sum_prod_type]
  calc
    _ = ∑ p₁, ∑ p₂, ∑ q₁, ∑ p₃, ∑ q₂, ∑ q₃,
        f p₁ q₁ p₂ q₂ p₃ q₃ := by
      apply Finset.sum_congr rfl
      intro p₁ _
      apply Finset.sum_congr rfl
      intro p₂ _
      rw [Finset.sum_comm]
    _ = ∑ p₁, ∑ q₁, ∑ p₂, ∑ p₃, ∑ q₂, ∑ q₃,
        f p₁ q₁ p₂ q₂ p₃ q₃ := by
      apply Finset.sum_congr rfl
      intro p₁ _
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro p₁ _
      apply Finset.sum_congr rfl
      intro q₁ _
      apply Finset.sum_congr rfl
      intro p₂ _
      rw [Finset.sum_comm]

private def integerBornFast (i j k : Bool) (a b c : Fin 4) : GaussianInt :=
  ∑ u₁ : Bool, ∑ v₁ : Bool, ∑ u₂ : Bool, ∑ v₂ : Bool,
    ∑ u₃ : Bool, ∑ v₃ : Bool,
      sourceCoeff i u₁ v₁ * (sourceCoeff j u₂ v₂ * sourceCoeff k u₃ v₃) *
        (integerEffect a ⊗ₖ (integerEffect b ⊗ₖ integerEffect c)).submatrix
          (incidentWires Bool Bool Bool Bool Bool Bool)
          (incidentWires Bool Bool Bool Bool Bool Bool)
          (sourceCol i u₁ v₁, (sourceCol j u₂ v₂, sourceCol k u₃ v₃))
          (sourceRow i u₁ v₁, (sourceRow j u₂ v₂, sourceRow k u₃ v₃))

private theorem integerBorn_eq_fast (i j k : Bool) (a b c : Fin 4) :
    integerBorn i j k a b c = integerBornFast i j k a b c := by
  rw [integerBorn_eq_sparse]
  let e : sourceIndex → sourceIndex → GaussianInt :=
    (integerEffect a ⊗ₖ (integerEffect b ⊗ₖ integerEffect c)).submatrix
      (incidentWires Bool Bool Bool Bool Bool Bool)
      (incidentWires Bool Bool Bool Bool Bool Bool)
  let f := fun p₁ q₁ p₂ q₂ p₃ q₃ : Bool × Bool =>
    integerSource i p₁ q₁ * (integerSource j p₂ q₂ * integerSource k p₃ q₃) *
      e (q₁, (q₂, q₃)) (p₁, (p₂, p₃))
  change (∑ p : sourceIndex, ∑ q : sourceIndex,
    f p.1 q.1 p.2.1 q.2.1 p.2.2 q.2.2) = _
  rw [regroup_source_sum f]
  dsimp only [f]
  simp only [mul_assoc]
  simp_rw [← Finset.mul_sum]
  simp_rw [source_support_sum]
  simp only [Finset.mul_sum, integerBornFast, e, mul_assoc]

private theorem integer_vector_cast (j : Fin 4) (q : Bool × Bool) :
    (integerEjmVector j q : ℂ) = ejmVector j q := by
  rcases q with ⟨u, v⟩
  fin_cases j <;> cases u <;> cases v <;>
    norm_num [integerEjmVector, ejmVector, tetraX, tetraY, tetraZ,
      GaussianInt.toComplex_def']

private theorem integer_singlet_cast (q : Bool × Bool) :
    (integerSinglet q : ℂ) = singletVector q := by
  rcases q with ⟨u, v⟩
  cases u <;> cases v <;> simp [integerSinglet, singletVector]

private theorem source_cast (signal : Bool) :
    stateMatrix (if signal then singlet else whiteNoise) =
      (1 / 4 : ℝ) • (integerSource signal).map GaussianInt.toComplex := by
  have htwo : GaussianInt.toComplex (2 : GaussianInt) = (2 : ℂ) := by
    norm_num [GaussianInt.toComplex_def]
  cases signal
  · ext u v
    norm_num [stateMatrix, whiteNoise, integerSource, Matrix.map_one,
      Matrix.map_apply, Matrix.smul_apply, Complex.real_smul]
  · ext u v
    rcases u with ⟨u₁, u₂⟩
    rcases v with ⟨v₁, v₂⟩
    cases u₁ <;> cases u₂ <;> cases v₁ <;> cases v₂ <;>
      norm_num [stateMatrix, singlet, integerSource, Matrix.vecMulVec_apply,
        integerSinglet, singletVector, integer_singlet_cast,
        GaussianInt.toComplex_def', Matrix.map_apply, Matrix.smul_apply,
        Pi.smul_apply, smul_eq_mul, Complex.real_smul, htwo]

private theorem effect_cast (j : Fin 4) :
    ejm.effect j = (1 / 8 : ℝ) • (integerEffect j).map GaussianInt.toComplex := by
  ext u v
  simp [ejm, ejmEffect, integerEffect, Matrix.vecMulVec_apply,
    integer_vector_cast, map_mul]

private theorem endpoint_cast (i j k : Bool) (a b c : Fin 4) :
    triangleBorn (stateMatrix (if i then singlet else whiteNoise))
      (stateMatrix (if j then singlet else whiteNoise))
      (stateMatrix (if k then singlet else whiteNoise)) ejm ejm ejm a b c =
        ((integerBorn i j k a b c).re : ℝ) / 32768 := by
  let s : Matrix sourceIndex sourceIndex ℂ :=
    (integerSource i).map GaussianInt.toComplex ⊗ₖ
      ((integerSource j).map GaussianInt.toComplex ⊗ₖ
        (integerSource k).map GaussianInt.toComplex)
  let e : Matrix sourceIndex sourceIndex ℂ :=
    (integerEffect a).map GaussianInt.toComplex ⊗ₖ
      ((integerEffect b).map GaussianInt.toComplex ⊗ₖ
        (integerEffect c).map GaussianInt.toComplex)
  let w : sourceIndex → sourceIndex := incidentWires Bool Bool Bool Bool Bool Bool
  have hm : Matrix.trace (s * e.submatrix w w) =
      (integerBorn i j k a b c : ℂ) := by
    simp [s, e, w, integerBorn, Matrix.trace, Matrix.diag, Matrix.mul_apply,
      Matrix.submatrix_apply, map_sum, map_mul]
  have hlinear (S E : Matrix sourceIndex sourceIndex ℂ) (r t : ℝ) :
      Matrix.trace ((r • S) * (t • E).submatrix w w) =
        r • (t • Matrix.trace (S * E.submatrix w w)) := by
    have hsub : (t • E).submatrix w w = t • E.submatrix w w := by
      ext u v
      rfl
    rw [hsub, Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul,
      Matrix.trace_smul]
  calc
    _ = (Matrix.trace
        ((((1 / 4 : ℝ) * (1 / 4) * (1 / 4)) • s) *
          (((1 / 8 : ℝ) * (1 / 8) * (1 / 8)) • e).submatrix w w)).re := by
      simp only [triangleBorn, independentSources, outcomeEffect, source_cast,
        effect_cast, Matrix.smul_kronecker, Matrix.kronecker_smul, smul_smul]
      rfl
    _ = _ := by
      rw [hlinear, hm]
      simp only [Complex.smul_re, ← GaussianInt.intCast_re, smul_eq_mul]
      ring


private def endpointNumerator (i j k : Bool) (a b c : Fin 4) : ℤ :=
  let x : ℤ := if i then 1 else 0
  let y : ℤ := if j then 1 else 0
  let z : ℤ := if k then 1 else 0
  if a = b ∧ b = c then
    4 + 3 * (x + y + z) + 3 * (x * y + x * z + y * z) + 3 * x * y * z
  else if a = b then
    4 + 3 * x - y - z - (x * y + x * z + y * z) - x * y * z
  else if b = c then
    4 - x + 3 * y - z - (x * y + x * z + y * z) - x * y * z
  else if c = a then
    4 - x - y + 3 * z - (x * y + x * z + y * z) - x * y * z
  else
    4 - (x + y + z) + (x * y + x * z + y * z) + x * y * z

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- Kernel reduction checks all 512 source/outcome endpoints with 64 supported terms each.
private theorem integer_endpoint_evaluation :
    ∀ (i j k : Bool) (a b c : Fin 4),
      (integerBorn i j k a b c).re = 128 * endpointNumerator i j k a b c := by
  intro i j k a b c
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    fin_cases a <;> fin_cases b <;> fin_cases c <;>
      rw [integerBorn_eq_fast] <;> decide +kernel

private theorem endpoint_probability (i j k : Bool) (a b c : Fin 4) :
    triangleBorn (stateMatrix (if i then singlet else whiteNoise))
      (stateMatrix (if j then singlet else whiteNoise))
      (stateMatrix (if k then singlet else whiteNoise)) ejm ejm ejm a b c =
        (endpointNumerator i j k a b c : ℝ) / 256 := by
  rw [endpoint_cast, integer_endpoint_evaluation]
  push_cast
  ring

private theorem independent_expansion (x y z : ℝ) (a b c : Fin 4) :
    ejmProbability x y z a b c =
      ∑ i : Bool, ∑ j : Bool, ∑ k : Bool,
        (sourceWeight x i * sourceWeight y j * sourceWeight z k) *
          (endpointNumerator i j k a b c : ℝ) / 256 := by
  have h : ejmProbability x y z a b c =
      ∑ i : Bool, ∑ j : Bool, ∑ k : Bool,
        (sourceWeight x i * sourceWeight y j * sourceWeight z k) *
          triangleBorn (stateMatrix (if i then singlet else whiteNoise))
            (stateMatrix (if j then singlet else whiteNoise))
            (stateMatrix (if k then singlet else whiteNoise)) ejm ejm ejm a b c := by
    simp only [ejmProbability, noisyTriangle, triangleBorn, independentSources, sourceNoise,
      Matrix.add_kronecker, Matrix.kronecker_add, Matrix.smul_kronecker,
      Matrix.kronecker_smul, Matrix.add_mul, Matrix.smul_mul,
      Matrix.trace_add, Matrix.trace_smul, Complex.add_re, Complex.smul_re,
      Fintype.sum_bool, sourceWeight, Bool.false_eq_true, ↓reduceIte, smul_eq_mul]
    ring
  rw [h]
  simp_rw [endpoint_probability]
  simp only [mul_div_assoc]

/-- The polynomial is obtained from the actual six-qubit Born contraction.
No symmetry assumption or visibility bound is needed for this algebraic
identity; physical positivity uses visibilities in the unit interval. -/
theorem ejm_noise_probability (x y z : ℝ) (a b c : Fin 4) :
    ejmProbability x y z a b c = ejmNoiseTable x y z a b c := by
  rw [independent_expansion]
  simp only [Fintype.sum_bool, sourceWeight, Bool.false_eq_true, ↓reduceIte,
    endpointNumerator, ejmNoiseTable]
  split_ifs <;> push_cast <;> ring

#print axioms ejm_noise_probability

end D5.S3.Quantum.Entanglement.ElegantJointMeasurementSourceNoise
