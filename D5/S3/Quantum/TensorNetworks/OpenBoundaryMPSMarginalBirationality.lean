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
import Mathlib.Basic.Complex.Basic
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-! The affine model and its Cramer reconstruction on a principal open chart. -/

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
    ((List.ofFn fun j => Matrix.of (fun i k =>
      MvPolynomial.X (Sum.inl (w j, i, k)))).prod *ᵥ
      (fun i => MvPolynomial.X (Sum.inr (Sum.inr i))))

private lemma polynomial_image_prime {ι σ : Type*}
    (f : σ → MvPolynomial ι ℂ) :
    (MvPolynomial.vanishingIdeal ℂ
      (Set.range fun x : ι → ℂ => fun j => MvPolynomial.eval x (f j))).IsPrime := by
  let φ := MvPolynomial.eval₂Hom MvPolynomial.C f
  have heq : MvPolynomial.vanishingIdeal ℂ
      (Set.range fun x : ι → ℂ => fun j => MvPolynomial.eval x (f j)) =
      RingHom.ker φ := by
    ext p
    change (∀ y ∈ Set.range (fun x : ι → ℂ =>
      fun j => MvPolynomial.eval x (f j)), MvPolynomial.eval y p = 0) ↔ φ p = 0
    constructor
    · intro hp
      apply MvPolynomial.funext
      intro x
      have hx := hp _ ⟨x, rfl⟩
      simpa only [φ, MvPolynomial.coe_eval₂Hom, ← MvPolynomial.eval_assoc,
        Function.comp_def, map_zero] using hx
    · intro hp y hy
      obtain ⟨x, rfl⟩ := hy
      change MvPolynomial.eval (MvPolynomial.eval x ∘ f) p = 0
      rw [MvPolynomial.eval_assoc]
      change MvPolynomial.eval x (φ p) = 0
      rw [hp, map_zero]
  rw [heq]
  exact RingHom.ker_isPrime φ

private lemma parameter_eval (n : ℕ) (x : parameterIndex → ℂ) :
    (fun w => MvPolynomial.eval x (parameterPolys n w)) =
      mpsState n (Matrix.of fun i k => x (Sum.inl (0, i, k)))
        (Matrix.of fun i k => x (Sum.inl (1, i, k)))
        (fun i => x (Sum.inr (Sum.inl i))) (fun i => x (Sum.inr (Sum.inr i))) := by
  funext w
  have hprod : ((List.ofFn fun j => (Matrix.of fun i k =>
      (MvPolynomial.X (Sum.inl (w j, i, k)) : MvPolynomial parameterIndex ℂ))).prod).map
      (MvPolynomial.eval x) =
      (List.ofFn fun j => (![Matrix.of (fun i k => x (Sum.inl (0, i, k))),
        Matrix.of (fun i k => x (Sum.inl (1, i, k)))] :
          Fin 2 → Matrix (Fin 2) (Fin 2) ℂ) (w j)).prod := by
    change (MvPolynomial.eval x).mapMatrix _ = _
    rw [map_list_prod, List.map_ofFn]
    congr 1
    apply congrArg List.ofFn
    funext j
    ext i k
    change MvPolynomial.eval x (MvPolynomial.X (Sum.inl (w j, i, k))) = _
    rw [MvPolynomial.eval_X]
    generalize w j = b
    fin_cases b <;> rfl
  change MvPolynomial.eval x (dotProduct _ _) = dotProduct _ _
  rw [RingHom.map_dotProduct]
  apply congrArg₂ dotProduct
  · funext i
    exact MvPolynomial.eval_X _
  · funext i
    rw [Function.comp_apply, RingHom.map_mulVec]
    simp only [Function.comp_def, MvPolynomial.eval_X]
    rw [hprod]

private lemma parameter_image (n : ℕ) :
    openBoundaryMPS n =
      Set.range (fun x : parameterIndex → ℂ =>
        fun w => MvPolynomial.eval x (parameterPolys n w)) := by
  ext ψ
  constructor
  · rintro ⟨a₀, a₁, b₀, b₁, rfl⟩
    let x : parameterIndex → ℂ := Sum.elim
      (fun ijk => (![a₀, a₁] : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ) ijk.1 ijk.2.1 ijk.2.2)
      (Sum.elim b₀ b₁)
    refine ⟨x, ?_⟩
    change (fun w => MvPolynomial.eval x (parameterPolys n w)) = _
    rw [parameter_eval]
    rfl
  · rintro ⟨x, rfl⟩
    change (fun w => MvPolynomial.eval x (parameterPolys n w)) ∈ openBoundaryMPS n
    rw [parameter_eval]
    exact ⟨_, _, _, _, rfl⟩

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
  Matrix.of (fun i k => t ![i, j, k]) * (reconstructedBasis t)⁻¹

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

private lemma chart_denominator (n : ℕ) (t : (Fin 3 → Fin 2) → ℂ)
    (hg : MvPolynomial.eval t chartPoly ≠ 0) :
    MvPolynomial.eval t (denominator n) ≠ 0 := by
  have hv : MvPolynomial.eval t basisNumerator.det ≠ 0 := by
    intro hv
    apply hg
    simp only [chartPoly, map_mul, hv, mul_zero, zero_mul]
  have hc : MvPolynomial.eval t sumNumerator.det ≠ 0 := by
    intro hc
    apply hg
    simp only [chartPoly, map_mul, hc, mul_zero, zero_mul]
  simpa only [denominator, map_mul, map_pow] using
    mul_ne_zero (pow_ne_zero 3 hv) (pow_ne_zero (n - 3) hc)

private lemma inverse_formula (n a : ℕ) (hn : 4 ≤ n) (h : a + 3 ≤ n)
    (t : (Fin 3 → Fin 2) → ℂ) (hg : MvPolynomial.eval t chartPoly ≠ 0) :
    MvPolynomial.eval t (denominator n) ≠ 0 ∧
    rationalInverse n a t =
      mpsState n (reconstructedMatrix t 0) (reconstructedMatrix t 1)
        ((reconstructedLeft t) ᵥ* ((reconstructedSum t)⁻¹ ^ a))
        (((reconstructedSum t)⁻¹ ^ (n - 3 - a)) *ᵥ reconstructedRight t) := by
  refine ⟨chart_denominator n t hg, ?_⟩
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
  refine ⟨hformula.1, image_subset_closure n ?_, ?_⟩
  · exact ⟨_, _, _, _, hformula.2⟩
  · rw [hformula.2, outside_sum]
    have hunit : IsUnit (reconstructedSum t).det := isUnit_iff_ne_zero.mpr hrec.2.2.2.2
    have hl (k : ℕ) : (reconstructedSum t)⁻¹ ^ k * reconstructedSum t ^ k = 1 :=
      pow_mul_pow_eq_one k (Matrix.nonsing_inv_mul _ hunit)
    have hr (k : ℕ) : reconstructedSum t ^ k * (reconstructedSum t)⁻¹ ^ k = 1 :=
      pow_mul_pow_eq_one k (Matrix.mul_nonsing_inv _ hunit)
    change mpsState 3 _ _
      ((reconstructedLeft t ᵥ* ((reconstructedSum t)⁻¹ ^ a)) ᵥ* reconstructedSum t ^ a)
      (reconstructedSum t ^ (n - 3 - a) *ᵥ
        ((reconstructedSum t)⁻¹ ^ (n - 3 - a) *ᵥ reconstructedRight t)) = t
    rw [Matrix.vecMul_vecMul, Matrix.mulVec_mulVec, hl, hr,
      Matrix.vecMul_one, Matrix.one_mulVec]
    exact hrec.2.2.2.1

private lemma gauge_uniqueness_image (n a : ℕ) (hn : 4 ≤ n) (h : a + 3 ≤ n)
    (ψ : (Fin n → Fin 2) → ℂ) (hψ : ψ ∈ openBoundaryMPS n)
    (hg : MvPolynomial.eval (improperMarginal n a h ψ) chartPoly ≠ 0) :
    rationalInverse n a (improperMarginal n a h ψ) = ψ := by
  sorry

private def marginalCoordinate (n a : ℕ) (h : a + 3 ≤ n) (t : Fin 3 → Fin 2) :
    MvPolynomial (Fin n → Fin 2) ℂ :=
  ∑ w : Fin n → Fin 2,
    if (fun j : Fin 3 => w ⟨a + j.val, by omega⟩) = t then MvPolynomial.X w else 0

private lemma marginal_coordinate_eval (n a : ℕ) (h : a + 3 ≤ n)
    (ψ : (Fin n → Fin 2) → ℂ) (t : Fin 3 → Fin 2) :
    MvPolynomial.eval ψ (marginalCoordinate n a h t) = improperMarginal n a h ψ t := by
  classical
  rw [marginalCoordinate, map_sum]
  apply Finset.sum_congr rfl
  intro w _
  split <;> simp only [MvPolynomial.eval_X, map_zero]

private lemma marginal_pullback_eval (n a : ℕ) (h : a + 3 ≤ n)
    (ψ : (Fin n → Fin 2) → ℂ) (f : MvPolynomial (Fin 3 → Fin 2) ℂ) :
    MvPolynomial.eval ψ
      (MvPolynomial.eval₂Hom MvPolynomial.C (marginalCoordinate n a h) f) =
      MvPolynomial.eval (improperMarginal n a h ψ) f := by
  change MvPolynomial.eval ψ
    (MvPolynomial.eval₂ MvPolynomial.C (marginalCoordinate n a h) f) = _
  rw [← MvPolynomial.eval_assoc]
  apply congrArg (fun z => MvPolynomial.eval z f)
  funext t
  exact marginal_coordinate_eval n a h ψ t

private lemma uniqueness_closure (n a : ℕ) (hn : 4 ≤ n) (h : a + 3 ≤ n)
    (himage : ∀ ψ ∈ openBoundaryMPS n,
      MvPolynomial.eval (improperMarginal n a h ψ) chartPoly ≠ 0 →
      rationalInverse n a (improperMarginal n a h ψ) = ψ)
    (ψ : (Fin n → Fin 2) → ℂ) (hψ : ψ ∈ closure n)
    (hg : MvPolynomial.eval (improperMarginal n a h ψ) chartPoly ≠ 0) :
    MvPolynomial.eval (improperMarginal n a h ψ) (denominator n) ≠ 0 ∧
      rationalInverse n a (improperMarginal n a h ψ) = ψ := by
  classical
  refine ⟨chart_denominator n _ hg, ?_⟩
  funext w
  let φ := MvPolynomial.eval₂Hom MvPolynomial.C (marginalCoordinate n a h)
  let r := φ chartPoly * (φ (numerator n a w) - MvPolynomial.X w * φ (denominator n))
  have hr : r ∈ vanishingPolys n := by
    intro x hx
    change MvPolynomial.eval x r = 0
    dsimp only [r, φ]
    rw [map_mul, map_sub, map_mul, MvPolynomial.eval_X,
      marginal_pullback_eval, marginal_pullback_eval, marginal_pullback_eval]
    by_cases hgx : MvPolynomial.eval (improperMarginal n a h x) chartPoly = 0
    · rw [hgx, zero_mul]
    · have heq := congrFun (himage x hx hgx) w
      have hqx := chart_denominator n (improperMarginal n a h x) hgx
      have hmul := (div_eq_iff hqx).mp heq
      rw [hmul, sub_self, mul_zero]
  have hzero := hψ r hr
  change MvPolynomial.eval ψ r = 0 at hzero
  dsimp only [r, φ] at hzero
  rw [map_mul, map_sub, map_mul, MvPolynomial.eval_X,
    marginal_pullback_eval, marginal_pullback_eval, marginal_pullback_eval] at hzero
  exact (div_eq_iff (chart_denominator n _ hg)).mpr
    (sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_left hg))

private def explicitTriple : (Fin 3 → Fin 2) → ℂ :=
  mpsState 3 !![1, 2; 3, 4] !![5, 6; 7, 8] ![1, 0] ![1, 2]

private lemma explicit_chart_nonempty :
    explicitTriple ∈ closure 3 ∧ MvPolynomial.eval explicitTriple chartPoly ≠ 0 := by
  sorry

/-- Every improper marginalization in Conjecture 8 has a rational inverse. -/
theorem result : claim := by
  intro n a hn h
  refine ⟨model_prime n, model_prime 3, ?_⟩
  refine ⟨chartPoly, denominator n, numerator n a, ?_, ?_, ?_⟩
  · obtain ⟨ht, hg⟩ := explicit_chart_nonempty
    obtain ⟨_, hf, hm⟩ := inverse_on_chart n a hn h explicitTriple ht hg
    refine ⟨rationalInverse n a explicitTriple, hf, ?_⟩
    rw [hm]
    exact hg
  · intro t ht hg
    obtain ⟨hq, hf, hm⟩ := inverse_on_chart n a hn h t ht hg
    refine ⟨hq, hf, ?_, hm⟩
    change MvPolynomial.eval (improperMarginal n a h (rationalInverse n a t)) chartPoly ≠ 0
    rw [hm]
    exact hg
  · exact uniqueness_closure n a hn h (gauge_uniqueness_image n a hn h)

end

end D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSMarginalBirationality
