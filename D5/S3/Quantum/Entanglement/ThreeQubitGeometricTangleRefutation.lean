/- GID: D5/S3/Quantum/Entanglement/ThreeQubitGeometricTangleRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/ThreeQubitGeometricTangleRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Entanglement/ThreeQubitGeometricTangleRefutation.claim; result=D5/S3/Quantum/Entanglement/ThreeQubitGeometricTangleRefutation.result; claim=D5/S3/Quantum/Entanglement/ThreeQubitGeometricTangleRefutation.claim
   digest: The type-4c canonical state on the Bloch-norm diagonal refutes the geometric tangle ansatz. -/

/-
proof_shape: result: bind-only (the universal claim is instantiated at the explicit canonical
  state and the resulting real equality is normalized by `norm_num`)
escape_witness: none
admission_basis: open-problem-resolution (#11500; Refuted)
Direct frozen dependencies: PartialTraceMutualInformation (partialTraceLeft/Right),
  ActualPureQubitGeometry (bloch); pinned Mathlib for the remaining normalization
-/

import D5.S3.Quantum.Information.PartialTraceMutualInformation
import D5.S3.Quantum.Information.ActualPureQubitGeometry

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Entanglement.ThreeQubitGeometricTangleRefutation

open scoped BigOperators
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open D5.S3.Quantum.Information.ActualPureQubitCostInfimum

/-!
The canonical tensor is the coefficient tensor of
`λ₀|000⟩ + λ₁ e^{iφ}|100⟩ + λ₂|101⟩ + λ₃|110⟩ + λ₄|111⟩`.
Its one-qubit matrices are finite-sum partial traces of the rank-one density matrix.
The Bloch convention is `ρ = (I + r·σ)/2`, with `y = −2 Im ρ₀₁`.
The three-tangle is four times the complex modulus of Cayley's quartic.
The full type-5 predicate includes all five amplitude and all five J-invariant conditions.
-/

structure CanonicalState where
  lambda0 : ℝ
  lambda1 : ℝ
  lambda2 : ℝ
  lambda3 : ℝ
  lambda4 : ℝ
  phi : ℝ

def isCanonical (ψ : CanonicalState) : Prop :=
  0 ≤ ψ.lambda0 ∧ ψ.lambda0 ≤ 1 ∧
  0 ≤ ψ.lambda1 ∧ ψ.lambda1 ≤ 1 ∧
  0 ≤ ψ.lambda2 ∧ ψ.lambda2 ≤ 1 ∧
  0 ≤ ψ.lambda3 ∧ ψ.lambda3 ≤ 1 ∧
  0 ≤ ψ.lambda4 ∧ ψ.lambda4 ≤ 1 ∧
  ψ.lambda0 ^ 2 + ψ.lambda1 ^ 2 + ψ.lambda2 ^ 2 + ψ.lambda3 ^ 2 + ψ.lambda4 ^ 2 = 1 ∧
  0 ≤ ψ.phi ∧ ψ.phi ≤ Real.pi

/-- The literal coefficient tensor, with qubit order A, B, C. -/
noncomputable def amplitudes (ψ : CanonicalState) (i j k : Fin 2) : ℂ :=
  if i = 0 then (if j = 0 ∧ k = 0 then (ψ.lambda0 : ℂ) else 0)
  else if j = 0 then
    (if k = 0 then (ψ.lambda1 : ℂ) * Complex.exp ((ψ.phi : ℂ) * Complex.I)
    else (ψ.lambda2 : ℂ))
  else if k = 0 then (ψ.lambda3 : ℂ) else (ψ.lambda4 : ℂ)

/-- The outer product |ψ⟩⟨ψ| on A × (B × C). -/
noncomputable def jointDensity (ψ : CanonicalState) :
    Matrix (Fin 2 × (Fin 2 × Fin 2)) (Fin 2 × (Fin 2 × Fin 2)) ℂ :=
  fun p q => amplitudes ψ p.1 p.2.1 p.2.2 *
    star (amplitudes ψ q.1 q.2.1 q.2.2)

noncomputable def rhoA (ψ : CanonicalState) : Matrix (Fin 2) (Fin 2) ℂ :=
  partialTraceRight (jointDensity ψ)

noncomputable def rhoB (ψ : CanonicalState) : Matrix (Fin 2) (Fin 2) ℂ :=
  partialTraceRight (partialTraceLeft (jointDensity ψ))

noncomputable def rhoC (ψ : CanonicalState) : Matrix (Fin 2) (Fin 2) ℂ :=
  partialTraceLeft (partialTraceLeft (jointDensity ψ))

/-- The three actual Bloch vectors, indexed A, B, C. -/
noncomputable def blochVectors (ψ : CanonicalState) :
    Fin 3 → EuclideanSpace ℝ (Fin 3) :=
  ![bloch (rhoA ψ), bloch (rhoB ψ), bloch (rhoC ψ)]

/-- Euclidean lengths of the three reduced-state Bloch vectors. -/
noncomputable def blochLengths (ψ : CanonicalState) : ℝ × ℝ × ℝ :=
  (Real.sqrt (∑ i : Fin 3, (blochVectors ψ 0 i) ^ 2),
    Real.sqrt (∑ i : Fin 3, (blochVectors ψ 1 i) ^ 2),
    Real.sqrt (∑ i : Fin 3, (blochVectors ψ 2 i) ^ 2))

/-- Cayley's 2 × 2 × 2 hyperdeterminant, as the full quartic in the eight amplitudes. -/
def cayley (t : Fin 2 → Fin 2 → Fin 2 → ℂ) : ℂ :=
  t 0 0 0 ^ 2 * t 1 1 1 ^ 2 + t 0 0 1 ^ 2 * t 1 1 0 ^ 2 +
    t 0 1 0 ^ 2 * t 1 0 1 ^ 2 + t 1 0 0 ^ 2 * t 0 1 1 ^ 2 -
    2 * (t 0 0 0 * t 0 0 1 * t 1 1 0 * t 1 1 1 +
      t 0 0 0 * t 0 1 0 * t 1 0 1 * t 1 1 1 +
      t 0 0 0 * t 1 0 0 * t 0 1 1 * t 1 1 1 +
      t 0 0 1 * t 0 1 0 * t 1 0 1 * t 1 1 0 +
      t 0 0 1 * t 1 0 0 * t 0 1 1 * t 1 1 0 +
      t 0 1 0 * t 1 0 0 * t 0 1 1 * t 1 0 1) +
    4 * (t 0 0 0 * t 0 1 1 * t 1 0 1 * t 1 1 0 +
      t 0 0 1 * t 0 1 0 * t 1 0 0 * t 1 1 1)

/-- Three-tangle as 4 |Hdet(t)| (arXiv v2, Eq. (10)). -/
noncomputable def tangle (ψ : CanonicalState) : ℝ := 4 * ‖cayley (amplitudes ψ)‖

/-- The five Acín invariants J₁,...,J₅; entry k is J_(k+1). -/
noncomputable def jInvariants (ψ : CanonicalState) : Fin 5 → ℝ :=
  let j1 := Complex.normSq ((ψ.lambda1 * ψ.lambda4 : ℝ) *
    Complex.exp ((ψ.phi : ℂ) * Complex.I) - (ψ.lambda2 * ψ.lambda3 : ℝ))
  ![j1, ψ.lambda0 ^ 2 * ψ.lambda2 ^ 2, ψ.lambda0 ^ 2 * ψ.lambda3 ^ 2,
    ψ.lambda0 ^ 2 * ψ.lambda4 ^ 2,
    ψ.lambda0 ^ 2 * (j1 + ψ.lambda2 ^ 2 * ψ.lambda3 ^ 2 -
      ψ.lambda1 ^ 2 * ψ.lambda4 ^ 2)]

def isGHZ (ψ : CanonicalState) : Prop := ψ.lambda0 * ψ.lambda4 ≠ 0

def isType5 (ψ : CanonicalState) : Prop :=
  ψ.lambda0 ≠ 0 ∧ ψ.lambda1 ≠ 0 ∧ ψ.lambda2 ≠ 0 ∧ ψ.lambda3 ≠ 0 ∧
    ψ.lambda4 ≠ 0 ∧ ∀ k : Fin 5, jInvariants ψ k ≠ 0

def normSquared (r : ℝ × ℝ × ℝ) : ℝ := r.1 ^ 2 + r.2.1 ^ 2 + r.2.2 ^ 2

/-- The source's main diagonal line in Euclidean three-space. -/
def V_line : Set (EuclideanSpace ℝ (Fin 3)) :=
  Set.range (fun t : ℝ => WithLp.toLp 2 ![t, t, t])

/-- The Bloch-length triple as a vector with the Euclidean metric. -/
def euclideanVector (r : ℝ × ℝ × ℝ) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 ![r.1, r.2.1, r.2.2]

/-- Euclidean distance from the Bloch-length vector to the main diagonal line. -/
noncomputable def distanceToDiagonal (r : ℝ × ℝ × ℝ) : ℝ :=
  Metric.infDist (euclideanVector r) V_line

def claim : Prop :=
  ∃ F : (ℝ × ℝ × ℝ) → ℝ,
    (∀ r, 0 ≤ F r) ∧
      ∀ ψ, isCanonical ψ → isGHZ ψ → ¬ isType5 ψ →
        tangle ψ = 1 - normSquared (blochLengths ψ) / 3 -
          distanceToDiagonal (blochLengths ψ) * F (blochLengths ψ)

theorem result : ¬ claim := by
  have hA (ψ : CanonicalState) : bloch (rhoA ψ) = WithLp.toLp 2
      ![2 * ψ.lambda0 * ψ.lambda1 * Real.cos ψ.phi,
        2 * ψ.lambda0 * ψ.lambda1 * Real.sin ψ.phi,
        ψ.lambda0 ^ 2 - (ψ.lambda1 ^ 2 + ψ.lambda2 ^ 2 +
          ψ.lambda3 ^ 2 + ψ.lambda4 ^ 2)] := by
    ext i
    fin_cases i <;>
      simp [bloch, rhoA, partialTraceRight, jointDensity, amplitudes,
        Fintype.sum_prod_type, Fin.sum_univ_two, Complex.mul_re, Complex.mul_im,
        Complex.exp_re, Complex.exp_im] <;>
      nlinarith [Real.sin_sq_add_cos_sq ψ.phi]
  have hB (ψ : CanonicalState) : bloch (rhoB ψ) = WithLp.toLp 2
      ![2 * (ψ.lambda1 * ψ.lambda3 * Real.cos ψ.phi + ψ.lambda2 * ψ.lambda4),
        -2 * ψ.lambda1 * ψ.lambda3 * Real.sin ψ.phi,
        ψ.lambda0 ^ 2 + ψ.lambda1 ^ 2 + ψ.lambda2 ^ 2 -
          ψ.lambda3 ^ 2 - ψ.lambda4 ^ 2] := by
    ext i
    fin_cases i <;>
      simp [bloch, rhoB, partialTraceRight, partialTraceLeft, jointDensity, amplitudes,
        Fin.sum_univ_two, Complex.mul_re, Complex.mul_im,
        Complex.exp_re, Complex.exp_im] <;>
      nlinarith [Real.sin_sq_add_cos_sq ψ.phi]
  have hC (ψ : CanonicalState) : bloch (rhoC ψ) = WithLp.toLp 2
      ![2 * (ψ.lambda1 * ψ.lambda2 * Real.cos ψ.phi + ψ.lambda3 * ψ.lambda4),
        -2 * ψ.lambda1 * ψ.lambda2 * Real.sin ψ.phi,
        ψ.lambda0 ^ 2 + ψ.lambda1 ^ 2 + ψ.lambda3 ^ 2 -
          ψ.lambda2 ^ 2 - ψ.lambda4 ^ 2] := by
    ext i
    fin_cases i <;>
      simp [bloch, rhoC, partialTraceLeft, jointDensity, amplitudes,
        Fin.sum_univ_two, Complex.mul_re, Complex.mul_im,
        Complex.exp_re, Complex.exp_im] <;>
      nlinarith [Real.sin_sq_add_cos_sq ψ.phi]
  have hdet (ψ : CanonicalState) : cayley (amplitudes ψ) =
      ((ψ.lambda0 ^ 2 * ψ.lambda4 ^ 2 : ℝ) : ℂ) := by
    simp [cayley, amplitudes]
  have htangle (ψ : CanonicalState) : tangle ψ = 4 * ψ.lambda0 ^ 2 * ψ.lambda4 ^ 2 := by
    rw [tangle, hdet, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
    ring
  intro h
  obtain ⟨F, _, hall⟩ := h
  let w : CanonicalState :=
    { lambda0 := 1 / 2
      lambda1 := 0
      lambda2 := 1 / 2
      lambda3 := 1 / 2
      lambda4 := 1 / 2
      phi := 0 }
  have hwCanonical : isCanonical w := by
    norm_num [isCanonical, w]
    exact Real.pi_nonneg
  have hwGHZ : isGHZ w := by
    norm_num [isGHZ, w]
  have hwNotType5 : ¬ isType5 w := by
    simp [isType5, w]
  have hwBloch : blochLengths w = (1 / 2, (1 / 2, 1 / 2)) := by
    simp [blochLengths, blochVectors, hA, hB, hC, w, Fin.sum_univ_succ]
    norm_num [Real.sqrt_eq_iff_mul_self_eq]
  have hwDistance : distanceToDiagonal (1 / 2, (1 / 2, 1 / 2)) = 0 := by
    apply Metric.infDist_zero_of_mem
    exact ⟨1 / 2, rfl⟩
  have heq := hall w hwCanonical hwGHZ hwNotType5
  rw [hwBloch, htangle, hwDistance] at heq
  norm_num [normSquared, w] at heq

#print axioms result

end D5.S3.Quantum.Entanglement.ThreeQubitGeometricTangleRefutation
