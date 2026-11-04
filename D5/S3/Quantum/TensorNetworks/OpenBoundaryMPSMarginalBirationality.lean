/- GID: D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSMarginalBirationality
   generality: G
   mirror-B: D5/B/S3/Quantum/TensorNetworks/OpenBoundaryMPSMarginalBirationality
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Rational reconstruction of open-boundary binary bond-two matrix product states. -/

import D5.S3.Analytic.Hunter.NCHunterPositivity

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
  funext w; rw [parameterPolys]
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
    change _ = FinVec.etaExpand (fun b : Fin 2 =>
      Matrix.of (fun i k => x (Sum.inl (b, i, k)))) (w j) i k
    rw [FinVec.etaExpand_eq]
    rfl
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

set_option maxRecDepth 4096 in
private lemma quartic_parameter_identity :
    MvPolynomial.eval₂Hom MvPolynomial.C (parameterPolys 3) kernelMatrix.det = 0 := by
  let a : Fin 2 → Matrix (Fin 2) (Fin 2) (MvPolynomial parameterIndex ℂ) :=
    fun i => Matrix.of fun j k => MvPolynomial.X (Sum.inl (i, j, k))
  let l : Fin 2 → MvPolynomial parameterIndex ℂ := fun i => MvPolynomial.X (Sum.inr (Sum.inl i))
  let r : Fin 2 → MvPolynomial parameterIndex ℂ := fun i => MvPolynomial.X (Sum.inr (Sum.inr i))
  let u : Matrix (Fin 2) (Fin 2) (MvPolynomial parameterIndex ℂ) :=
    Matrix.of fun i j => (l ᵥ* a i) j
  let v : Matrix (Fin 2) (Fin 2) (MvPolynomial parameterIndex ℂ) :=
    Matrix.of fun j k => (a k *ᵥ r) j
  let z := u.det • (v.adjugate *ᵥ r)
  let e := v.det • (l ᵥ* u.adjugate)
  let c : Fin 4 → MvPolynomial parameterIndex ℂ := ![z 0, z 1, e 0, e 1]
  let k := (MvPolynomial.eval₂Hom MvPolynomial.C (parameterPolys 3)).mapMatrix kernelMatrix
  have hk : k *ᵥ c = 0 := by
    funext i
    fin_cases i <;>
      norm_num [k, c, z, e, u, v, a, l, r, kernelMatrix, coordinate, parameterPolys,
        List.ofFn_succ, Matrix.mulVec, Matrix.vecMul, dotProduct, Matrix.mul_apply,
        Fin.sum_univ_succ, Matrix.det_fin_two, Matrix.adjugate_fin_two, smul_eq_mul,
        Matrix.vecHead, Matrix.vecTail, MvPolynomial.eval₂_neg] <;> ring
  have hc : c 2 ≠ 0 := by
    intro hc
    let x : parameterIndex → ℂ := Sum.elim
      (fun ijk => (![!![1, 0; 0, 1], !![0, 1; 1, 0]] :
        Fin 2 → Matrix (Fin 2) (Fin 2) ℂ) ijk.1 ijk.2.1 ijk.2.2)
      (Sum.elim ![1, 0] ![1, 0])
    have hx := congrArg (MvPolynomial.eval x) hc
    norm_num [c, e, v, u, a, l, r, x, Matrix.mulVec, Matrix.vecMul, dotProduct,
      Fin.sum_univ_two, Matrix.det_fin_two, Matrix.adjugate_fin_two, smul_eq_mul,
      Matrix.vecHead] at hx
  have hdet := Matrix.det_eq_zero_of_mulVec_eq_zero_of_mem_nonZeroDivisors hk
    (mem_nonZeroDivisors_iff_ne_zero.mpr hc)
  exact (RingHom.map_det _ _).trans hdet

private lemma quartic_image (t : (Fin 3 → Fin 2) → ℂ) (ht : t ∈ openBoundaryMPS 3) :
    MvPolynomial.eval t kernelMatrix.det = 0 := by
  rw [parameter_image] at ht
  obtain ⟨x, rfl⟩ := ht
  change MvPolynomial.eval (MvPolynomial.eval x ∘ parameterPolys 3) kernelMatrix.det = 0
  rw [MvPolynomial.eval_assoc]
  change MvPolynomial.eval x
    (MvPolynomial.eval₂Hom MvPolynomial.C (parameterPolys 3) kernelMatrix.det) = 0
  rw [quartic_parameter_identity, map_zero]

private lemma quartic_closure (t : (Fin 3 → Fin 2) → ℂ) (ht : t ∈ closure 3) :
    MvPolynomial.eval t kernelMatrix.det = 0 := by
  exact ht kernelMatrix.det (fun x hx => quartic_image x hx)

private lemma kernel_cramer_identity :
    kernelMatrix *ᵥ ![cramerNumerator 0, cramerNumerator 1, cramerNumerator 2, minorPoly] =
      ![0, 0, 0, kernelMatrix.det] := by
  have hc : kernelMinor *ᵥ cramerNumerator =
      minorPoly • (fun i => -kernelMatrix (Fin.castSucc i) 3) := Matrix.mulVec_cramer _ _
  have hf (j : Fin 3) :
      (![cramerNumerator 0, cramerNumerator 1, cramerNumerator 2, minorPoly] : Fin 4 → _)
        (Fin.castSucc j) = cramerNumerator j :=
    (congrFun (FinVec.etaExpand_eq
      (Fin.snoc (α := fun _ => _) cramerNumerator minorPoly)) (Fin.castSucc j)).trans
        (Fin.snoc_castSucc _ _ _)
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [kernelMatrix]
    norm_num [kernelMatrix, kernelMinor, minorPoly, cramerNumerator, Matrix.cramer_apply,
      Matrix.det_succ_row_zero, Fin.sum_univ_succ, Matrix.submatrix_apply,
      Matrix.mulVec, dotProduct, Matrix.updateCol_apply, Fin.succAbove] <;> ring
  · have hz : (![0, 0, 0, kernelMatrix.det] : Fin 4 → _) (Fin.castSucc j) = 0 := by
      fin_cases j <;> rfl
    rw [hz]
    change (∑ q : Fin 4, kernelMatrix (Fin.castSucc j) q *
        (![cramerNumerator 0, cramerNumerator 1, cramerNumerator 2, minorPoly] : Fin 4 → _) q) = 0
    rw [Fin.sum_univ_castSucc]
    simp only [hf]
    change (kernelMinor *ᵥ cramerNumerator) j + kernelMatrix (Fin.castSucc j) 3 * minorPoly = 0
    rw [hc]
    change minorPoly * (-kernelMatrix (Fin.castSucc j) 3) +
      kernelMatrix (Fin.castSucc j) 3 * minorPoly = 0
    ring

private lemma chart_scalars (t : (Fin 3 → Fin 2) → ℂ)
    (hg : MvPolynomial.eval t chartPoly ≠ 0) :
    let ε := MvPolynomial.eval t
    let d := ε minorPoly
    let v := ε basisNumerator.det
    let c := ε sumNumerator.det
    (reconstructedBasis t).det ≠ 0 ∧
    (∀ j, reconstructedMatrix t j = (d / v) • ε.mapMatrix (matrixNumerator j)) ∧
    reconstructedLeft t = d⁻¹ • (ε ∘ leftNumerator) ∧
    reconstructedRight t = (d⁻¹) ^ 2 • (ε ∘ boundaryNumerator) ∧
    (reconstructedSum t).det ≠ 0 ∧
    (reconstructedSum t)⁻¹ = (v / (d * c)) • ε.mapMatrix sumNumerator.adjugate := by
  dsimp only
  let ε := MvPolynomial.eval t
  let d := ε minorPoly
  let v := ε basisNumerator.det
  let c := ε sumNumerator.det
  simp only [chartPoly, map_mul, mul_ne_zero_iff] at hg
  have hd : d ≠ 0 := hg.1.1.1.1
  have hv : v ≠ 0 := hg.1.1.1.2
  have hc : c ≠ 0 := hg.1.1.2
  have hV : reconstructedBasis t = d⁻¹ • ε.mapMatrix basisNumerator := by
    ext i k
    change ε (basisNumerator i k) / d = d⁻¹ * ε (basisNumerator i k)
    rw [div_eq_mul_inv, mul_comm]
  have hVinv : (reconstructedBasis t)⁻¹ = (d / v) •
      (ε.mapMatrix basisNumerator).adjugate := by
    rw [hV, Matrix.inv_def, Matrix.det_smul, Matrix.adjugate_smul, Ring.inverse_eq_inv]
    simp only [Fintype.card_fin, Nat.reduceSub, pow_one, smul_smul]
    rw [← ε.map_det]
    apply congrArg (fun s : ℂ => s • (ε.mapMatrix basisNumerator).adjugate)
    change (d⁻¹ ^ 2 * v)⁻¹ * d⁻¹ = d / v
    field_simp
  have hB (j : Fin 2) : reconstructedMatrix t j =
      (d / v) • ε.mapMatrix (matrixNumerator j) := by
    have hs : ε.mapMatrix (slicePoly j) = Matrix.of (fun i k => t ![i, j, k]) := by
      ext i k
      change ε (slicePoly j i k) = t ![i, j, k]
      rw [slicePoly]; exact MvPolynomial.eval_X _
    rw [reconstructedMatrix, hVinv, mul_smul_comm, matrixNumerator, map_mul,
      ε.map_adjugate, hs]
  have hz : reconstructedKernel t = d⁻¹ • (ε ∘ rightKernelNumerator) := by
    funext i
    change ε (rightKernelNumerator i) / d = d⁻¹ * ε (rightKernelNumerator i)
    rw [div_eq_mul_inv, mul_comm]
  have hR : reconstructedRight t = d⁻¹ ^ 2 • (ε ∘ boundaryNumerator) := by
    rw [reconstructedRight, hV, hz, Matrix.smul_mulVec, Matrix.mulVec_smul, smul_smul]
    rw [pow_two]
    congr 1
    funext i
    exact (ε.map_mulVec basisNumerator rightKernelNumerator i).symm
  have hC : reconstructedSum t = (d / v) • ε.mapMatrix sumNumerator := by
    rw [reconstructedSum, hB, hB, ← smul_add, sumNumerator, map_add]
  refine ⟨?_, hB, ?_, hR, ?_, ?_⟩
  · rw [hV, Matrix.det_smul, ← ε.map_det]
    exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero hd)) hv
  · funext i
    change ε (leftNumerator i) / d = d⁻¹ * ε (leftNumerator i)
    rw [div_eq_mul_inv, mul_comm]
  · rw [hC, Matrix.det_smul, ← ε.map_det]
    exact mul_ne_zero (pow_ne_zero _ (div_ne_zero hd hv)) hc
  · rw [hC, Matrix.inv_def, Matrix.det_smul, Matrix.adjugate_smul, Ring.inverse_eq_inv]
    simp only [Fintype.card_fin, Nat.reduceSub, pow_one, smul_smul]
    rw [← ε.map_det, ← ε.map_adjugate]
    apply congrArg (fun s : ℂ => s • ε.mapMatrix sumNumerator.adjugate)
    change ((d / v) ^ 2 * c)⁻¹ * (d / v) = v / (d * c)
    field_simp

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
  have hraw := kernel_cramer_identity
  obtain ⟨hv, _, _, _, hc, _⟩ := chart_scalars t hg
  simp only [chartPoly, map_mul, mul_ne_zero_iff] at hg
  have hd : MvPolynomial.eval t minorPoly ≠ 0 := hg.1.1.1.1
  have hk (i k : Fin 2) :
      dotProduct (fun j => t ![i, k, j]) (reconstructedKernel t) =
        reconstructedBasis t i k := by
    let row : Fin 4 := ⟨2 * i.val + k.val, by omega⟩
    have hlast : MvPolynomial.eval t (![0, 0, 0, kernelMatrix.det] row) = 0 := by
      fin_cases i <;> fin_cases k <;> norm_num [row, hquartic]
    have heq := (congrArg (MvPolynomial.eval t) (congrFun hraw row)).trans hlast
    fin_cases i <;> fin_cases k <;>
      norm_num [row, kernelMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
        coordinate] at heq
    all_goals
      norm_num [reconstructedKernel, rightKernelNumerator, reconstructedBasis,
        basisNumerator, leftNumerator, dotProduct, Fin.sum_univ_two, coordinate]
      field_simp (disch := apply_rules [mul_ne_zero, pow_ne_zero, inv_ne_zero, hd])
      linear_combination heq
  have hunit : IsUnit (reconstructedBasis t).det := isUnit_iff_ne_zero.mpr hv
  have hlt (i : Fin 2) : reconstructedLeft t ᵥ* Matrix.of (fun j k => t ![j, i, k]) =
      fun k => reconstructedBasis t i k := by
    funext k
    simp only [Matrix.vecMul, reconstructedBasis.eq_1, basisNumerator.eq_1,
      RingHom.map_dotProduct, Function.comp_def, coordinate, MvPolynomial.eval_X]
    simp only [dotProduct, reconstructedLeft, Matrix.of_apply, div_eq_mul_inv,
      Finset.sum_mul, mul_right_comm]
  have hl (i : Fin 2) : reconstructedLeft t ᵥ* reconstructedMatrix t i = Pi.single i 1 := by
    rw [reconstructedMatrix, ← Matrix.vecMul_vecMul, hlt]
    change (reconstructedBasis t).row i ᵥ* (reconstructedBasis t)⁻¹ = _
    rw [← Matrix.single_one_vecMul i (reconstructedBasis t), Matrix.vecMul_vecMul,
      Matrix.mul_nonsing_inv _ hunit, Matrix.vecMul_one]
  have hr (k : Fin 2) : reconstructedMatrix t k *ᵥ reconstructedRight t =
      fun i => reconstructedBasis t i k := by
    rw [reconstructedMatrix, reconstructedRight, Matrix.mulVec_mulVec, Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ hunit, Matrix.mul_one]
    exact funext (fun i => hk i k)
  refine ⟨hk, hl, hr, ?_, hc⟩
  funext w
  have hm (j : Fin 2) : (![reconstructedMatrix t 0, reconstructedMatrix t 1] :
      Fin 2 → Matrix (Fin 2) (Fin 2) ℂ) j = reconstructedMatrix t j :=
    congrFun (FinVec.etaExpand_eq (reconstructedMatrix t)) j
  simp only [mpsState, List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil,
    mul_one, hm, ← Matrix.mulVec_mulVec]
  rw [Matrix.dotProduct_mulVec, hl, hr, single_one_dotProduct]
  change (reconstructedMatrix t (w 1) * reconstructedBasis t) (w 0) (w 2) = t w
  rw [reconstructedMatrix, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hunit, Matrix.mul_one]
  apply congrArg t
  exact FinVec.etaExpand_eq w

private lemma chart_denominator (n : ℕ) (t : (Fin 3 → Fin 2) → ℂ)
    (hg : MvPolynomial.eval t chartPoly ≠ 0) :
    MvPolynomial.eval t (denominator n) ≠ 0 := by
  simp only [chartPoly, map_mul, mul_ne_zero_iff] at hg
  have hv : MvPolynomial.eval t basisNumerator.det ≠ 0 := hg.1.1.1.2
  have hc : MvPolynomial.eval t sumNumerator.det ≠ 0 := hg.1.1.2
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
  obtain ⟨_, hB, hl, hr, _, hC⟩ := chart_scalars t hg
  let ε := MvPolynomial.eval t
  let d := ε minorPoly
  let v := ε basisNumerator.det
  let c := ε sumNumerator.det
  have hparts := hg
  simp only [chartPoly, map_mul, mul_ne_zero_iff] at hparts
  have hd : d ≠ 0 := hparts.1.1.1.1
  have hv : v ≠ 0 := hparts.1.1.1.2
  have hc : c ≠ 0 := hparts.1.1.2
  funext w
  let j := ε.mapMatrix sumNumerator.adjugate
  let u := (List.ofFn fun i => ε.mapMatrix (matrixNumerator (w i))).prod
  let l := ε ∘ leftNumerator
  let r := ε ∘ boundaryNumerator
  have hp : ε (numerator n a w) =
      dotProduct l ((j ^ a * u * j ^ (n - 3 - a)) *ᵥ r) := by
    have hprod : ε.mapMatrix (List.ofFn fun i => matrixNumerator (w i)).prod = u := by
      rw [map_list_prod, List.map_ofFn]
      rfl
    rw [numerator, ε.map_dotProduct]
    change dotProduct l _ = _
    apply congrArg (dotProduct l)
    funext i
    rw [Function.comp_apply, ε.map_mulVec]
    change (ε.mapMatrix (sumNumerator.adjugate ^ a *
      (List.ofFn fun i => matrixNumerator (w i)).prod *
        sumNumerator.adjugate ^ (n - 3 - a)) *ᵥ r) i = _
    rw [show ε.mapMatrix (sumNumerator.adjugate ^ a *
        (List.ofFn fun i => matrixNumerator (w i)).prod *
          sumNumerator.adjugate ^ (n - 3 - a)) =
        j ^ a * u * j ^ (n - 3 - a) from by
      rw [map_mul, map_mul, map_pow, map_pow, hprod]]
  have hm : (![reconstructedMatrix t 0, reconstructedMatrix t 1] :
      Fin 2 → Matrix (Fin 2) (Fin 2) ℂ) = reconstructedMatrix t :=
    FinVec.etaExpand_eq (reconstructedMatrix t)
  have hword : (List.ofFn fun i => reconstructedMatrix t (w i)).prod = (d / v) ^ n • u := by
    rw [show (fun i => reconstructedMatrix t (w i)) =
      (fun i => (d / v) • ε.mapMatrix (matrixNumerator (w i))) from
        funext (fun i => hB (w i))]
    rw [show (List.ofFn fun i => (d / v) • ε.mapMatrix (matrixNumerator (w i))) =
      (List.ofFn fun i => ε.mapMatrix (matrixNumerator (w i))).map ((d / v) • ·) from
        List.map_ofFn.symm]
    simpa only [List.length_ofFn] using
      (List.smul_prod (List.ofFn fun i => ε.mapMatrix (matrixNumerator (w i))) (d / v)).symm
  have hstate : mpsState n (reconstructedMatrix t 0) (reconstructedMatrix t 1)
      (reconstructedLeft t ᵥ* ((reconstructedSum t)⁻¹ ^ a))
      (((reconstructedSum t)⁻¹ ^ (n - 3 - a)) *ᵥ reconstructedRight t) w =
      (d⁻¹ * (v / (d * c)) ^ a * (d / v) ^ n *
        (v / (d * c)) ^ (n - 3 - a) * d⁻¹ ^ 2) * ε (numerator n a w) := by
    rw [hp]
    simp only [mpsState, hm]
    rw [hword, hl, hr, hC]
    simp only [smul_pow,
      Matrix.smul_vecMul, Matrix.vecMul_smul, Matrix.smul_mulVec, Matrix.mulVec_smul,
      smul_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul,
      ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]
    dsimp only [d, v, c, ε, j, u, l, r]
    ring
  change ε (numerator n a w) / ε (denominator n) = _
  rw [hstate]
  have hb : n - 3 = a + (n - 3 - a) := by omega
  have hn : n = a + (n - 3 - a) + 3 := by omega
  rw [denominator, map_mul, map_pow, map_pow]
  change ε (numerator n a w) / (v ^ 3 * c ^ (n - 3)) = _
  generalize hx : ε (numerator n a w) = x
  generalize he : n - 3 - a = b at *
  rw [hb, hn]
  simp only [pow_add, mul_pow, div_pow, inv_pow]
  field_simp (disch := apply_rules [mul_ne_zero, pow_ne_zero, inv_ne_zero, hd, hv, hc])

private lemma sum_append_words {r : Type*} [AddCommMonoid r] (a b : ℕ)
    (f : (Fin (a + b) → Fin 2) → r) :
    ∑ w, f w = ∑ u : Fin a → Fin 2, ∑ v : Fin b → Fin 2, f (Fin.append u v) := by
  rw [← (Fin.appendEquiv a b).sum_comp f, Fintype.sum_prod_type]
  rfl

private lemma word_append (a b : ℕ) (u : Fin a → Fin 2) (v : Fin b → Fin 2)
    (m : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ) :
    (List.ofFn fun j => m (Fin.append u v j)).prod =
      (List.ofFn fun j => m (u j)).prod * (List.ofFn fun j => m (v j)).prod := by
  exact GVHunter.word_eval_append m u v

private lemma sum_words (n : ℕ) (m : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ) :
    (∑ w : Fin n → Fin 2, (List.ofFn fun j => m (w j)).prod) = (m 0 + m 1) ^ n := by
  classical
  induction n with
  | zero => simp
  | succ n ih =>
    rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => Fin 2)).sum_comp]
    simp only [Fintype.sum_prod_type, Fin.consEquiv_apply, List.ofFn_succ,
      Fin.cons_zero, Fin.cons_succ, List.prod_cons]
    simp_rw [← Finset.mul_sum, ih]
    rw [Fin.sum_univ_two, ← add_mul, ← pow_succ']

private lemma outside_sum_exact (a b : ℕ)
    (a₀ a₁ : Matrix (Fin 2) (Fin 2) ℂ) (b₀ b₁ : Fin 2 → ℂ) :
    improperMarginal (a + (3 + b)) a (by omega)
      (mpsState (a + (3 + b)) a₀ a₁ b₀ b₁) =
      mpsState 3 a₀ a₁ (b₀ ᵥ* (a₀ + a₁) ^ a) ((a₀ + a₁) ^ b *ᵥ b₁) := by
  classical
  funext t
  change (∑ w, if (fun j : Fin 3 => w ⟨a + j.val, by omega⟩) = t then
    mpsState (a + (3 + b)) a₀ a₁ b₀ b₁ w else 0) = _
  rw [sum_append_words a (3 + b)]
  simp_rw [sum_append_words 3 b]
  have hmid (u : Fin a → Fin 2) (v : Fin 3 → Fin 2) (w : Fin b → Fin 2) :
      (fun j : Fin 3 => Fin.append u (Fin.append v w) ⟨a + j.val, by omega⟩) = v := by
    funext j
    change Fin.append u (Fin.append v w) (Fin.natAdd a (Fin.castAdd b j)) = v j
    rw [Fin.append_right, Fin.append_left]
  simp_rw [hmid]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]
  simp only [mpsState, word_append, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec]
  simp only [← sum_dotProduct, ← Matrix.sum_vecMul, ← Matrix.vecMul_sum, sum_words]
  rfl

private lemma outside_sum (n a : ℕ) (h : a + 3 ≤ n)
    (a₀ a₁ : Matrix (Fin 2) (Fin 2) ℂ) (b₀ b₁ : Fin 2 → ℂ) :
    improperMarginal n a h (mpsState n a₀ a₁ b₀ b₁) =
      mpsState 3 a₀ a₁ (b₀ ᵥ* (a₀ + a₁) ^ a)
        ((a₀ + a₁) ^ (n - 3 - a) *ᵥ b₁) := by
  have hn : n = a + (3 + (n - 3 - a)) := by omega
  generalize hb : n - 3 - a = b at *
  subst n
  exact outside_sum_exact a b a₀ a₁ b₀ b₁

private lemma inverse_on_chart (n a : ℕ) (hn : 4 ≤ n) (h : a + 3 ≤ n)
    (t : (Fin 3 → Fin 2) → ℂ) (ht : t ∈ closure 3)
    (hg : MvPolynomial.eval t chartPoly ≠ 0) :
    MvPolynomial.eval t (denominator n) ≠ 0 ∧ rationalInverse n a t ∈ closure n ∧
      improperMarginal n a h (rationalInverse n a t) = t := by
  have hrec := chart_reconstruction t (quartic_closure t ht) hg
  have hformula := inverse_formula n a hn h t hg
  refine ⟨hformula.1, MvPolynomial.zeroLocus_vanishingIdeal_le _ ?_, ?_⟩
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

private lemma kernel_vector_unique (t : (Fin 3 → Fin 2) → ℂ)
    (hd : MvPolynomial.eval t minorPoly ≠ 0) (v : Fin 4 → ℂ)
    (hv : (MvPolynomial.eval t).mapMatrix kernelMatrix *ᵥ v = 0) :
    v = (v 3 / MvPolynomial.eval t minorPoly) •
      (MvPolynomial.eval t ∘
        ![cramerNumerator 0, cramerNumerator 1, cramerNumerator 2, minorPoly]) := by
  let ε := MvPolynomial.eval t
  let d := ε minorPoly
  let a := ε.mapMatrix kernelMinor
  let x : Fin 3 → ℂ := fun i => v (Fin.castSucc i)
  let y : Fin 3 → ℂ := fun i => ε (cramerNumerator i)
  let b : Fin 3 → ℂ := fun i => ε (kernelMatrix (Fin.castSucc i) 3)
  have hd0 : d ≠ 0 := hd
  have hx : a *ᵥ x = (-v 3) • b := by
    funext i
    have he := congrFun hv (Fin.castSucc i)
    change (∑ j : Fin 4, ε (kernelMatrix (Fin.castSucc i) j) * v j) = 0 at he
    rw [Fin.sum_univ_castSucc] at he
    change (∑ j : Fin 3, ε (kernelMatrix (Fin.castSucc i) (Fin.castSucc j)) *
      v (Fin.castSucc j)) + ε (kernelMatrix (Fin.castSucc i) 3) * v 3 = 0 at he
    change (∑ j : Fin 3, ε (kernelMatrix (Fin.castSucc i) (Fin.castSucc j)) *
      v (Fin.castSucc j)) = -v 3 * ε (kernelMatrix (Fin.castSucc i) 3)
    linear_combination he
  have hy : a *ᵥ y = (-d) • b := by
    funext i
    have he := congrArg ε (congrFun kernel_cramer_identity (Fin.castSucc i))
    have hz : (![0, 0, 0, kernelMatrix.det] : Fin 4 → _) (Fin.castSucc i) = 0 := by
      fin_cases i <;> rfl
    rw [hz, map_zero] at he
    change ε (dotProduct (kernelMatrix (Fin.castSucc i))
      ![cramerNumerator 0, cramerNumerator 1, cramerNumerator 2, minorPoly]) = 0 at he
    rw [ε.map_dotProduct] at he
    rw [dotProduct, Fin.sum_univ_castSucc] at he
    simp only [Function.comp_apply] at he
    change (∑ j : Fin 3, ε (kernelMatrix (Fin.castSucc i) (Fin.castSucc j)) *
      ε (cramerNumerator j)) = -d * ε (kernelMatrix (Fin.castSucc i) 3)
    have heq (j : Fin 3) :
        (![cramerNumerator 0, cramerNumerator 1, cramerNumerator 2, minorPoly] : Fin 4 → _)
          (Fin.castSucc j) = cramerNumerator j :=
      (congrFun (FinVec.etaExpand_eq
        (Fin.snoc (α := fun _ => _) cramerNumerator minorPoly)) (Fin.castSucc j)).trans
          (Fin.snoc_castSucc _ _ _)
    simp only [heq] at he
    change (∑ j : Fin 3, ε (kernelMatrix (Fin.castSucc i) (Fin.castSucc j)) *
      ε (cramerNumerator j)) + ε (kernelMatrix (Fin.castSucc i) 3) * d = 0 at he
    linear_combination he
  have ha : IsUnit a.det := by
    rw [show a.det = ε minorPoly from (ε.map_det kernelMinor).symm]
    exact isUnit_iff_ne_zero.mpr hd
  have hxy : x = (v 3 / d) • y := by
    apply Matrix.mulVec_injective_iff_isUnit.mpr ((a.isUnit_iff_isUnit_det).mpr ha)
    rw [hx, Matrix.mulVec_smul, hy, smul_smul]
    apply congrArg (fun s : ℂ => s • b)
    field_simp (disch := apply_rules [mul_ne_zero, pow_ne_zero, inv_ne_zero, hd0])
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · change v 3 = (v 3 / d) * d
    field_simp (disch := apply_rules [mul_ne_zero, pow_ne_zero, inv_ne_zero, hd0])
  · change x j = (v 3 / d) * ε
      ((![cramerNumerator 0, cramerNumerator 1, cramerNumerator 2, minorPoly] : Fin 4 → _)
        (Fin.castSucc j))
    have heq : (![cramerNumerator 0, cramerNumerator 1, cramerNumerator 2, minorPoly] : Fin 4 → _)
        (Fin.castSucc j) = cramerNumerator j :=
      (congrFun (FinVec.etaExpand_eq
        (Fin.snoc (α := fun _ => _) cramerNumerator minorPoly)) (Fin.castSucc j)).trans
          (Fin.snoc_castSucc _ _ _)
    rw [heq]
    exact congrFun hxy j

private lemma triple_gauge (a₀ a₁ : Matrix (Fin 2) (Fin 2) ℂ) (l r : Fin 2 → ℂ)
    (hg : MvPolynomial.eval (mpsState 3 a₀ a₁ l r) chartPoly ≠ 0) :
    ∃ s : ℂ, s ≠ 0 ∧ ∃ u : Matrix (Fin 2) (Fin 2) ℂ, IsUnit u.det ∧
      reconstructedLeft (mpsState 3 a₀ a₁ l r) = s⁻¹ • (l ᵥ* u⁻¹) ∧
      (∀ j, reconstructedMatrix (mpsState 3 a₀ a₁ l r) j =
        s • (u * (![a₀, a₁] : Fin 2 → _) j * u⁻¹)) ∧
      reconstructedRight (mpsState 3 a₀ a₁ l r) = s⁻¹ ^ 2 • (u *ᵥ r) := by
  let t := mpsState 3 a₀ a₁ l r
  change MvPolynomial.eval t chartPoly ≠ 0 at hg
  simp only [chartPoly, map_mul, mul_ne_zero_iff] at hg
  let m : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ := ![a₀, a₁]
  let u : Matrix (Fin 2) (Fin 2) ℂ := Matrix.of fun i j => (l ᵥ* m i) j
  let v : Matrix (Fin 2) (Fin 2) ℂ := Matrix.of fun j k => (m k *ᵥ r) j
  have ht (j : Fin 2) : Matrix.of (fun i k => t ![i, j, k]) = u * m j * v := by
    ext i k
    simp only [t, mpsState, List.ofFn_succ, List.ofFn_zero, List.prod_cons,
      List.prod_nil, Matrix.cons_val_zero, mul_one, u, v, Matrix.of_apply]
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
      Matrix.dotProduct_mulVec]
    rfl
  have hdet : (u * m 0 * v).det ≠ 0 := by
    rw [← ht 0, Matrix.det_fin_two]
    simpa only [map_sub, map_mul, coordinate, MvPolynomial.eval_X, Matrix.of_apply] using
      hg.1.2
  simp only [Matrix.det_mul, mul_ne_zero_iff] at hdet
  have hu : IsUnit u.det := isUnit_iff_ne_zero.mpr hdet.1.1
  have hv : IsUnit v.det := isUnit_iff_ne_zero.mpr hdet.2
  let z := v⁻¹ *ᵥ r
  let e := l ᵥ* u⁻¹
  let k : Fin 4 → ℂ := ![z 0, z 1, e 0, e 1]
  have hz : v *ᵥ z = r := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hv, Matrix.one_mulVec]
  have he : e ᵥ* u = l := by
    rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hu, Matrix.vecMul_one]
  have hrow (i j : Fin 2) : dotProduct (fun k => t ![i, j, k]) z =
      dotProduct e (fun k => t ![k, i, j]) := by
    change ((Matrix.of (fun p q => t ![p, j, q])) *ᵥ z) i =
      (e ᵥ* Matrix.of (fun p q => t ![p, i, q])) j
    rw [ht, ht, ← Matrix.mulVec_mulVec, hz, ← Matrix.vecMul_vecMul,
      ← Matrix.vecMul_vecMul, he]
    rw [← Matrix.mulVec_mulVec]
    change dotProduct (u i) (m j *ᵥ r) = ((l ᵥ* m i) ᵥ* v) j
    rfl
  have hk : (MvPolynomial.eval t).mapMatrix kernelMatrix *ᵥ k = 0 := by
    have h00 := hrow 0 0; have h01 := hrow 0 1
    have h10 := hrow 1 0; have h11 := hrow 1 1
    norm_num [dotProduct, Fin.sum_univ_two] at h00 h01 h10 h11
    funext i
    fin_cases i <;> norm_num [kernelMatrix, coordinate, k, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ]
    · linear_combination h00
    · linear_combination h01
    · linear_combination h10
    · linear_combination h11
  have hd : MvPolynomial.eval t minorPoly ≠ 0 := hg.1.1.1.1
  have huniq := kernel_vector_unique t hd k hk
  have hs : k 3 ≠ 0 := by
    intro hs
    have hk0 : k = 0 := by rw [huniq, hs, zero_div, zero_smul]
    have hz0 : z = 0 := by
      funext i; fin_cases i
      · exact congrFun hk0 0
      · exact congrFun hk0 1
    have hr0 : r = 0 := by rw [← hz, hz0, Matrix.mulVec_zero]
    have hv0 : v = 0 := by ext i j; change (m j *ᵥ r) i = 0; rw [hr0, Matrix.mulVec_zero]; rfl
    exact hv.ne_zero (by rw [hv0, Matrix.det_zero])
  have hs0 : e 1 ≠ 0 := hs
  have hl : reconstructedLeft t = (k 3)⁻¹ • e := by
    have hh := congrFun huniq 2; have hh3 := congrFun huniq 3
    funext i; rw [reconstructedLeft, leftNumerator]; fin_cases i <;>
      norm_num [k, reconstructedLeft, leftNumerator, Function.comp_def] at hh hh3 ⊢ <;>
      field_simp (disch := apply_rules [mul_ne_zero, pow_ne_zero, inv_ne_zero, hs0, hd]) at hh hh3 ⊢ <;>
        linear_combination -hh
  have hzr : reconstructedKernel t = (k 3)⁻¹ • z := by
    have hh := congrFun huniq 0; have hh1 := congrFun huniq 1
    funext i; rw [reconstructedKernel, rightKernelNumerator]; fin_cases i <;>
      norm_num [k, reconstructedKernel, rightKernelNumerator, Function.comp_def] at hh hh1 ⊢ <;>
      field_simp (disch := apply_rules [mul_ne_zero, pow_ne_zero, inv_ne_zero, hs0, hd])
        at hh hh1 ⊢ <;>
      (first | linear_combination -hh | linear_combination -hh1)
  have hbase : reconstructedBasis t = (k 3)⁻¹ • (u * v) := by
    ext i j
    have hli : (reconstructedLeft t ᵥ* Matrix.of (fun p q => t ![p, i, q])) j =
        reconstructedBasis t i j := by
      simp only [Matrix.vecMul, reconstructedBasis.eq_1, basisNumerator.eq_1,
        RingHom.map_dotProduct, Function.comp_def, coordinate, MvPolynomial.eval_X]
      simp only [dotProduct, reconstructedLeft, Matrix.of_apply, div_eq_mul_inv,
        Finset.sum_mul, mul_right_comm]
    rw [← hli, hl, ht, Matrix.smul_vecMul, ← Matrix.vecMul_vecMul,
      ← Matrix.vecMul_vecMul, he]
    rfl
  have hbi : (reconstructedBasis t)⁻¹ = k 3 • (v⁻¹ * u⁻¹) := by
    apply Matrix.inv_eq_left_inv
    rw [hbase, smul_mul_smul_comm, mul_inv_cancel₀ hs, one_smul]
    simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hu,
      Matrix.nonsing_inv_mul _ hv]
  refine ⟨k 3, hs, u, hu, hl, ?_, ?_⟩
  · intro j
    rw [reconstructedMatrix, ht, hbi, mul_smul_comm]
    simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hv]
    rfl
  · rw [reconstructedRight, hbase, hzr, Matrix.smul_mulVec, Matrix.mulVec_smul,
      ← Matrix.mulVec_mulVec, hz, smul_smul, pow_two]

private lemma gauge_uniqueness_image (n a : ℕ) (hn : 4 ≤ n) (h : a + 3 ≤ n)
    (ψ : (Fin n → Fin 2) → ℂ) (hψ : ψ ∈ openBoundaryMPS n)
    (hg : MvPolynomial.eval (improperMarginal n a h ψ) chartPoly ≠ 0) :
    rationalInverse n a (improperMarginal n a h ψ) = ψ := by
  obtain ⟨a₀, a₁, α, β, rfl⟩ := hψ
  rw [outside_sum] at hg ⊢
  let m : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ := ![a₀, a₁]
  let s₀ := a₀ + a₁
  let b := n - 3 - a
  let t := mpsState 3 a₀ a₁ (α ᵥ* s₀ ^ a) (s₀ ^ b *ᵥ β)
  obtain ⟨s, hs, u, hu, hl, hm, hr⟩ := triple_gauge a₀ a₁
    (α ᵥ* s₀ ^ a) (s₀ ^ b *ᵥ β) hg
  let φ : Matrix (Fin 2) (Fin 2) ℂ →* Matrix (Fin 2) (Fin 2) ℂ :=
    { toFun := fun x => u * x * u⁻¹
      map_one' := by simp only [mul_one, Matrix.mul_nonsing_inv _ hu]
      map_mul' := by intro x y; simp only [Matrix.mul_assoc,
        Matrix.nonsing_inv_mul_cancel_left _ _ hu] }
  have hc : φ s₀ = s⁻¹ • reconstructedSum t := by
    rw [reconstructedSum, hm, hm, ← smul_add, smul_smul, inv_mul_cancel₀ hs, one_smul]
    change u * (a₀ + a₁) * u⁻¹ = u * a₀ * u⁻¹ + u * a₁ * u⁻¹
    rw [mul_add, add_mul]
  have hp (k : ℕ) : u * s₀ ^ k * u⁻¹ = s⁻¹ ^ k • reconstructedSum t ^ k := by
    change φ (s₀ ^ k) = _
    rw [map_pow, hc, smul_pow]
  have hpl (k : ℕ) : s₀ ^ k * u⁻¹ = s⁻¹ ^ k • (u⁻¹ * reconstructedSum t ^ k) := by
    have hh := congrArg (u⁻¹ * ·) (hp k)
    simpa only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hu,
      mul_smul_comm] using hh
  have hpr (k : ℕ) : u * s₀ ^ k = s⁻¹ ^ k • (reconstructedSum t ^ k * u) := by
    have hh := congrArg (· * u) (hp k)
    simpa only [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, mul_one, Matrix.smul_mul] using hh
  have hcu := isUnit_iff_ne_zero.mpr (chart_scalars t hg).2.2.2.2.1
  have hcancel (k : ℕ) : reconstructedSum t ^ k * (reconstructedSum t)⁻¹ ^ k = 1 ∧
      (reconstructedSum t)⁻¹ ^ k * reconstructedSum t ^ k = 1 :=
    ⟨pow_mul_pow_eq_one k (Matrix.mul_nonsing_inv _ hcu),
      pow_mul_pow_eq_one k (Matrix.nonsing_inv_mul _ hcu)⟩
  have hleft : reconstructedLeft t ᵥ* (reconstructedSum t)⁻¹ ^ a =
      (s⁻¹ * s⁻¹ ^ a) • (α ᵥ* u⁻¹) := by
    rw [hl, Matrix.smul_vecMul]
    simp only [Matrix.vecMul_vecMul]
    rw [hpl, Matrix.smul_mul, Matrix.vecMul_smul, smul_smul,
      Matrix.mul_assoc, (hcancel a).1, mul_one]
  have hright : (reconstructedSum t)⁻¹ ^ b *ᵥ reconstructedRight t =
      (s⁻¹ ^ 2 * s⁻¹ ^ b) • (u *ᵥ β) := by
    rw [hr, Matrix.mulVec_smul]
    simp only [Matrix.mulVec_mulVec]
    rw [hpr, mul_smul_comm, Matrix.smul_mulVec, smul_smul,
      ← Matrix.mul_assoc, (hcancel b).2, one_mul]
  rw [(inverse_formula n a hn h t hg).2]
  funext w
  have hword : (List.ofFn fun i => reconstructedMatrix t (w i)).prod =
      s ^ n • (u * (List.ofFn fun i => m (w i)).prod * u⁻¹) := by
    rw [show (fun i => reconstructedMatrix t (w i)) =
      (fun i => s • φ (m (w i))) from funext (fun i => hm (w i))]
    rw [show (List.ofFn fun i => s • φ (m (w i))) =
      (List.ofFn fun i => φ (m (w i))).map (s • ·) from List.map_ofFn.symm]
    rw [← List.smul_prod, List.length_ofFn]
    congr 1
    exact (show φ (List.ofFn fun i => m (w i)).prod = _ from
      by rw [map_list_prod, List.map_ofFn]; rfl).symm
  have he : (![reconstructedMatrix t 0, reconstructedMatrix t 1] :
      Fin 2 → Matrix (Fin 2) (Fin 2) ℂ) = reconstructedMatrix t :=
    FinVec.etaExpand_eq (reconstructedMatrix t)
  simp only [mpsState, he]
  rw [hword, hleft, hright]
  simp only [Matrix.smul_mulVec, Matrix.mulVec_smul, smul_smul,
    smul_dotProduct, dotProduct_smul, smul_eq_mul, Matrix.dotProduct_mulVec,
    Matrix.smul_vecMul, Matrix.vecMul_vecMul, Matrix.mul_assoc,
    Matrix.nonsing_inv_mul_cancel_left _ _ hu, Matrix.nonsing_inv_mul _ hu, Matrix.vecMul_one]
  have hnb : n = a + b + 3 := by dsimp [b]; omega
  rw [show s ^ n = s ^ a * s ^ b * s ^ 3 from by rw [hnb, pow_add, pow_add]]
  simp only [inv_pow]
  field_simp (disch := apply_rules [mul_ne_zero, pow_ne_zero, inv_ne_zero, hs])
  simp only [mul_one, m]

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

private lemma uniqueness_closure (n a : ℕ) (h : a + 3 ≤ n)
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

private lemma chart_nonempty :
    ∃ t ∈ closure 3, MvPolynomial.eval t chartPoly ≠ 0 := by
  let t := mpsState 3 !![1, 2; 3, 4] !![5, 6; 7, 8] ![1, 0] ![1, 2]
  refine ⟨t, MvPolynomial.zeroLocus_vanishingIdeal_le _ ⟨_, _, _, _, rfl⟩, ?_⟩
  have hx (i j k : Fin 2) : MvPolynomial.eval t (coordinate i j k) =
      ![![![145, 349], ![337, 829]], ![![489, 1173], ![1193, 2933]]] i j k := by
    rw [coordinate]
    fin_cases i <;> fin_cases j <;> fin_cases k <;>
      norm_num [coordinate, t, mpsState, List.ofFn_succ,
        Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have hd : MvPolynomial.eval t minorPoly = 387072 := by
    rw [minorPoly, kernelMinor]
    norm_num [minorPoly, Matrix.det_fin_three, kernelMinor, kernelMatrix,
      Matrix.submatrix_apply, hx]
  have hc (i : Fin 3) : MvPolynomial.eval t (cramerNumerator i) =
      ![118272, 10752, -1161216] i := by
    rw [cramerNumerator]; fin_cases i <;>
      norm_num [cramerNumerator, Matrix.cramer_apply, Matrix.det_fin_three,
      kernelMinor, kernelMatrix, Matrix.submatrix_apply, Matrix.updateCol_apply, hx]
  rw [chartPoly]; norm_num [chartPoly, Matrix.det_fin_two, sumNumerator, matrixNumerator,
    slicePoly, Matrix.adjugate_fin_two, basisNumerator, leftNumerator,
    dotProduct, Matrix.mul_apply, Fin.sum_univ_two, hd, hc, hx]

/-- Every improper marginalization in Conjecture 8 has a rational inverse. -/
theorem result : claim := by
  intro n a hn h
  refine ⟨model_prime n, model_prime 3, ?_⟩
  refine ⟨chartPoly, denominator n, numerator n a, ?_, ?_, ?_⟩
  · obtain ⟨t, ht, hg⟩ := chart_nonempty
    obtain ⟨_, hf, hm⟩ := inverse_on_chart n a hn h t ht hg
    refine ⟨rationalInverse n a t, hf, ?_⟩
    rw [hm]
    exact hg
  · intro t ht hg
    obtain ⟨hq, hf, hm⟩ := inverse_on_chart n a hn h t ht hg
    refine ⟨hq, hf, ?_, hm⟩
    change MvPolynomial.eval (improperMarginal n a h (rationalInverse n a t)) chartPoly ≠ 0
    rw [hm]
    exact hg
  · exact uniqueness_closure n a h (gauge_uniqueness_image n a hn h)

end

end D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSMarginalBirationality
