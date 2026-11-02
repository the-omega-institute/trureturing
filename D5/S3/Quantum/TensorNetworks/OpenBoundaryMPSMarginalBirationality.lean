/- GID: D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSMarginalBirationality
   generality: G
   mirror-B: D5/B/S3/Quantum/TensorNetworks/OpenBoundaryMPSMarginalBirationality
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Rational reconstruction of open-boundary binary bond-two matrix product states. -/

import Mathlib.RingTheory.Nullstellensatz
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSMarginalBirationality

open scoped BigOperators Matrix

noncomputable section

/-- Coherent amplitudes with independent left and right boundary vectors. -/
def mpsState (n : ℕ) (a₀ a₁ : Matrix (Fin 2) (Fin 2) ℂ)
    (b₀ b₁ : Fin 2 → ℂ) : (Fin n → Fin 2) → ℂ :=
  fun w => dotProduct b₀
    ((List.ofFn fun j => (![a₀, a₁] : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ) (w j)).prod
      *ᵥ b₁)

/-- The source's open-boundary, translation-invariant binary bond-two model. -/
def openBoundaryMPS (n : ℕ) : Set ((Fin n → Fin 2) → ℂ) :=
  {ψ | ∃ a₀ a₁ b₀ b₁, ψ = mpsState n a₀ a₁ b₀ b₁}

/-- All polynomial equations satisfied by the parametrized model. -/
def vanishingPolys (n : ℕ) : Ideal (MvPolynomial (Fin n → Fin 2) ℂ) :=
  MvPolynomial.vanishingIdeal ℂ (openBoundaryMPS n)

/-- The affine Zariski closure, defined by all equations of the image. -/
def closure (n : ℕ) : Set ((Fin n → Fin 2) → ℂ) :=
  MvPolynomial.zeroLocus ℂ (vanishingPolys n)

/-- Sum all coordinates outside the three consecutive sites starting at `a`. -/
def improperMarginal (n a : ℕ) (h : a + 3 ≤ n)
    (ψ : (Fin n → Fin 2) → ℂ) : (Fin 3 → Fin 2) → ℂ :=
  fun t => ∑ w : Fin n → Fin 2,
    if (fun j : Fin 3 => w ⟨a + j.val, by omega⟩) = t then ψ w else 0

/-- A rational inverse on the two nonempty principal open subsets. -/
def IsBirationalVia (n a : ℕ) (h : a + 3 ≤ n) : Prop :=
  ∃ (g q : MvPolynomial (Fin 3 → Fin 2) ℂ)
    (p : (Fin n → Fin 2) → MvPolynomial (Fin 3 → Fin 2) ℂ),
    (∃ ψ ∈ closure n, MvPolynomial.eval (improperMarginal n a h ψ) g ≠ 0) ∧
    (∀ t ∈ closure 3, MvPolynomial.eval t g ≠ 0 →
      MvPolynomial.eval t q ≠ 0 ∧
      (fun w => MvPolynomial.eval t (p w) / MvPolynomial.eval t q) ∈ closure n ∧
      MvPolynomial.eval (improperMarginal n a h
        (fun w => MvPolynomial.eval t (p w) / MvPolynomial.eval t q)) g ≠ 0 ∧
      improperMarginal n a h
        (fun w => MvPolynomial.eval t (p w) / MvPolynomial.eval t q) = t) ∧
    (∀ ψ ∈ closure n, MvPolynomial.eval (improperMarginal n a h ψ) g ≠ 0 →
      MvPolynomial.eval (improperMarginal n a h ψ) q ≠ 0 ∧
      (fun w => MvPolynomial.eval (improperMarginal n a h ψ) (p w) /
        MvPolynomial.eval (improperMarginal n a h ψ) q) = ψ)

/-- Critch–Morton Conjecture 8 under the preregistered affine formal reading. -/
def claim : Prop :=
  ∀ n a : ℕ, 4 ≤ n → ∀ h : a + 3 ≤ n,
    (vanishingPolys n).IsPrime ∧ (vanishingPolys 3).IsPrime ∧ IsBirationalVia n a h

private abbrev parameterIndex :=
  (Fin 2 × Fin 2 × Fin 2) ⊕ (Fin 2 ⊕ Fin 2)

private def parameterPolys (n : ℕ) (w : Fin n → Fin 2) :
    MvPolynomial parameterIndex ℂ :=
  dotProduct (fun i => MvPolynomial.X (Sum.inr (Sum.inl i)))
    ((List.ofFn fun j => (fun i k =>
      MvPolynomial.X (Sum.inl (w j, i, k)))).prod *ᵥ
      (fun i => MvPolynomial.X (Sum.inr (Sum.inr i))))

private lemma polynomial_image_prime {ι σ : Type*}
    (f : σ → MvPolynomial ι ℂ) :
    (MvPolynomial.vanishingIdeal ℂ
      (Set.range fun x : ι → ℂ => fun j => MvPolynomial.eval x (f j))).IsPrime := by
  sorry

private lemma parameter_image (n : ℕ) :
    openBoundaryMPS n =
      Set.range (fun x : parameterIndex → ℂ =>
        fun w => MvPolynomial.eval x (parameterPolys n w)) := by
  sorry

private lemma model_prime (n : ℕ) : (vanishingPolys n).IsPrime := by
  rw [vanishingPolys, parameter_image]
  exact polynomial_image_prime (parameterPolys n)

private lemma image_subset_closure (n : ℕ) : openBoundaryMPS n ⊆ closure n :=
  MvPolynomial.zeroLocus_vanishingIdeal_le _

private def coordinate (i j k : Fin 2) : MvPolynomial (Fin 3 → Fin 2) ℂ :=
  MvPolynomial.X ![i, j, k]

private def kernelMatrix : Matrix (Fin 4) (Fin 4) (MvPolynomial (Fin 3 → Fin 2) ℂ) :=
  !![coordinate 0 0 0, coordinate 0 0 1, -coordinate 0 0 0, -coordinate 1 0 0;
     coordinate 0 1 0, coordinate 0 1 1, -coordinate 0 0 1, -coordinate 1 0 1;
     coordinate 1 0 0, coordinate 1 0 1, -coordinate 0 1 0, -coordinate 1 1 0;
     coordinate 1 1 0, coordinate 1 1 1, -coordinate 0 1 1, -coordinate 1 1 1]

private def kernelMinor : Matrix (Fin 3) (Fin 3) (MvPolynomial (Fin 3 → Fin 2) ℂ) :=
  kernelMatrix.submatrix (Fin.castLE (by omega)) (Fin.castLE (by omega))

private def minorPoly : MvPolynomial (Fin 3 → Fin 2) ℂ := kernelMinor.det

private def cramerNumerator : Fin 3 → MvPolynomial (Fin 3 → Fin 2) ℂ :=
  kernelMinor.cramer (fun i => -kernelMatrix (Fin.castLE (by omega) i) 3)

private def leftNumerator : Fin 2 → MvPolynomial (Fin 3 → Fin 2) ℂ :=
  ![cramerNumerator 2, minorPoly]

private def rightKernelNumerator : Fin 2 → MvPolynomial (Fin 3 → Fin 2) ℂ :=
  ![cramerNumerator 0, cramerNumerator 1]

private def slicePoly (j : Fin 2) :
    Matrix (Fin 2) (Fin 2) (MvPolynomial (Fin 3 → Fin 2) ℂ) :=
  fun i k => coordinate i j k

private def basisNumerator :
    Matrix (Fin 2) (Fin 2) (MvPolynomial (Fin 3 → Fin 2) ℂ) :=
  fun i k => dotProduct leftNumerator (fun j => coordinate j i k)

private def matrixNumerator (j : Fin 2) :
    Matrix (Fin 2) (Fin 2) (MvPolynomial (Fin 3 → Fin 2) ℂ) :=
  slicePoly j * basisNumerator.adjugate

private def sumNumerator :
    Matrix (Fin 2) (Fin 2) (MvPolynomial (Fin 3 → Fin 2) ℂ) :=
  matrixNumerator 0 + matrixNumerator 1

private def boundaryNumerator : Fin 2 → MvPolynomial (Fin 3 → Fin 2) ℂ :=
  basisNumerator *ᵥ rightKernelNumerator

private def chartPoly : MvPolynomial (Fin 3 → Fin 2) ℂ :=
  minorPoly * basisNumerator.det * sumNumerator.det *
    (coordinate 0 0 0 * coordinate 1 0 1 - coordinate 0 0 1 * coordinate 1 0 0) *
    (coordinate 0 0 0 * coordinate 0 1 1 - coordinate 0 0 1 * coordinate 0 1 0)

private def denominator (n : ℕ) : MvPolynomial (Fin 3 → Fin 2) ℂ :=
  basisNumerator.det ^ 3 * sumNumerator.det ^ (n - 3)

private def numerator (n a : ℕ) (w : Fin n → Fin 2) :
    MvPolynomial (Fin 3 → Fin 2) ℂ :=
  dotProduct leftNumerator
    ((sumNumerator.adjugate ^ a *
      (List.ofFn fun j => matrixNumerator (w j)).prod *
      sumNumerator.adjugate ^ (n - 3 - a)) *ᵥ boundaryNumerator)

private def rationalInverse (n a : ℕ) (t : (Fin 3 → Fin 2) → ℂ) :
    (Fin n → Fin 2) → ℂ :=
  fun w => MvPolynomial.eval t (numerator n a w) / MvPolynomial.eval t (denominator n)

private def reconstructedLeft (t : (Fin 3 → Fin 2) → ℂ) : Fin 2 → ℂ :=
  fun i => MvPolynomial.eval t (leftNumerator i) / MvPolynomial.eval t minorPoly

private def reconstructedKernel (t : (Fin 3 → Fin 2) → ℂ) : Fin 2 → ℂ :=
  fun i => MvPolynomial.eval t (rightKernelNumerator i) / MvPolynomial.eval t minorPoly

private def reconstructedBasis (t : (Fin 3 → Fin 2) → ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i k => MvPolynomial.eval t (basisNumerator i k) / MvPolynomial.eval t minorPoly

private def reconstructedMatrix (t : (Fin 3 → Fin 2) → ℂ) (j : Fin 2) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  (fun i k => t ![i, j, k]) * (reconstructedBasis t)⁻¹

private def reconstructedRight (t : (Fin 3 → Fin 2) → ℂ) : Fin 2 → ℂ :=
  reconstructedBasis t *ᵥ reconstructedKernel t

private def reconstructedSum (t : (Fin 3 → Fin 2) → ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  reconstructedMatrix t 0 + reconstructedMatrix t 1

private lemma quartic_image (t : (Fin 3 → Fin 2) → ℂ) (ht : t ∈ openBoundaryMPS 3) :
    MvPolynomial.eval t kernelMatrix.det = 0 := by
  sorry

private lemma quartic_closure (t : (Fin 3 → Fin 2) → ℂ) (ht : t ∈ closure 3) :
    MvPolynomial.eval t kernelMatrix.det = 0 := by
  exact ht kernelMatrix.det (fun x hx => quartic_image x hx)

private lemma chart_reconstruction (t : (Fin 3 → Fin 2) → ℂ)
    (hquartic : MvPolynomial.eval t kernelMatrix.det = 0)
    (hg : MvPolynomial.eval t chartPoly ≠ 0) :
    (∀ i k : Fin 2, dotProduct (fun j => t ![i, k, j]) (reconstructedKernel t) =
      reconstructedBasis t i k) ∧
    (∀ i : Fin 2, (reconstructedLeft t) ᵥ* reconstructedMatrix t i =
      Pi.single i 1) ∧
    (∀ k : Fin 2, reconstructedMatrix t k *ᵥ reconstructedRight t =
      fun i => reconstructedBasis t i k) ∧
    mpsState 3 (reconstructedMatrix t 0) (reconstructedMatrix t 1)
      (reconstructedLeft t) (reconstructedRight t) = t ∧
    (reconstructedSum t).det ≠ 0 := by
  sorry

private lemma inverse_formula (n a : ℕ) (hn : 4 ≤ n) (h : a + 3 ≤ n)
    (t : (Fin 3 → Fin 2) → ℂ) (hg : MvPolynomial.eval t chartPoly ≠ 0) :
    MvPolynomial.eval t (denominator n) ≠ 0 ∧
    rationalInverse n a t =
      mpsState n (reconstructedMatrix t 0) (reconstructedMatrix t 1)
        ((reconstructedLeft t) ᵥ* ((reconstructedSum t)⁻¹ ^ a))
        (((reconstructedSum t)⁻¹ ^ (n - 3 - a)) *ᵥ reconstructedRight t) := by
  sorry

private lemma outside_sum (n a : ℕ) (h : a + 3 ≤ n)
    (a₀ a₁ : Matrix (Fin 2) (Fin 2) ℂ) (b₀ b₁ : Fin 2 → ℂ) :
    improperMarginal n a h (mpsState n a₀ a₁ b₀ b₁) =
      mpsState 3 a₀ a₁ (b₀ ᵥ* (a₀ + a₁) ^ a)
        ((a₀ + a₁) ^ (n - 3 - a) *ᵥ b₁) := by
  sorry

private lemma inverse_on_chart (n a : ℕ) (hn : 4 ≤ n) (h : a + 3 ≤ n)
    (t : (Fin 3 → Fin 2) → ℂ) (ht : t ∈ closure 3)
    (hg : MvPolynomial.eval t chartPoly ≠ 0) :
    MvPolynomial.eval t (denominator n) ≠ 0 ∧ rationalInverse n a t ∈ closure n ∧
      improperMarginal n a h (rationalInverse n a t) = t := by
  have hrec := chart_reconstruction t (quartic_closure t ht) hg
  have hformula := inverse_formula n a hn h t hg
  have hsum := outside_sum n a h (reconstructedMatrix t 0) (reconstructedMatrix t 1)
    ((reconstructedLeft t) ᵥ* ((reconstructedSum t)⁻¹ ^ a))
    (((reconstructedSum t)⁻¹ ^ (n - 3 - a)) *ᵥ reconstructedRight t)
  sorry

private lemma gauge_uniqueness_image (n a : ℕ) (hn : 4 ≤ n) (h : a + 3 ≤ n)
    (ψ : (Fin n → Fin 2) → ℂ) (hψ : ψ ∈ openBoundaryMPS n)
    (hg : MvPolynomial.eval (improperMarginal n a h ψ) chartPoly ≠ 0) :
    rationalInverse n a (improperMarginal n a h ψ) = ψ := by
  sorry

private lemma uniqueness_closure (n a : ℕ) (hn : 4 ≤ n) (h : a + 3 ≤ n)
    (himage : ∀ ψ ∈ openBoundaryMPS n,
      MvPolynomial.eval (improperMarginal n a h ψ) chartPoly ≠ 0 →
      rationalInverse n a (improperMarginal n a h ψ) = ψ)
    (ψ : (Fin n → Fin 2) → ℂ) (hψ : ψ ∈ closure n)
    (hg : MvPolynomial.eval (improperMarginal n a h ψ) chartPoly ≠ 0) :
    MvPolynomial.eval (improperMarginal n a h ψ) (denominator n) ≠ 0 ∧
      rationalInverse n a (improperMarginal n a h ψ) = ψ := by
  sorry

private def explicitTriple : (Fin 3 → Fin 2) → ℂ :=
  mpsState 3 !![1, 2; 3, 4] !![5, 6; 7, 8] ![1, 0] ![1, 2]

private lemma explicit_chart_nonempty :
    explicitTriple ∈ closure 3 ∧ MvPolynomial.eval explicitTriple chartPoly ≠ 0 := by
  sorry

/-- Every improper marginalization in Conjecture 8 has a rational inverse. -/
theorem result : claim := by
  intro n a hn h
  refine ⟨model_prime n, model_prime 3, chartPoly, denominator n, numerator n a, ?_, ?_, ?_⟩
  · obtain ⟨ht, hg⟩ := explicit_chart_nonempty
    obtain ⟨_, hf, hm⟩ := inverse_on_chart n a hn h explicitTriple ht hg
    exact ⟨rationalInverse n a explicitTriple, hf, hm ▸ hg⟩
  · intro t ht hg
    obtain ⟨hq, hf, hm⟩ := inverse_on_chart n a hn h t ht hg
    exact ⟨hq, hf, hm ▸ hg, hm⟩
  · exact uniqueness_closure n a hn h (gauge_uniqueness_image n a hn h)

end

end D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSMarginalBirationality
