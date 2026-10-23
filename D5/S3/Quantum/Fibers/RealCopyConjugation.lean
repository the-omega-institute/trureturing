/- GID: D5/S3/Quantum/Fibers/RealCopyConjugation
   generality: G
   mirror-B: D5/B/S3/Quantum/Fibers/RealCopyConjugation
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Real joint statistics classify density-state conjugation orbits. -/

import D5.S3.Quantum.Information.PartialTraceMutualInformation
import D5.S3.Quantum.QuantumChannels.PositiveFilterTransposeRefutation
import Mathlib.LinearAlgebra.Matrix.Rank
import D5.S3.Quantum.Fibers.FiveModeRealResponse
import D5.S3.Quantum.Measurements.VisibleStateSpaceDimension
import D5.S3.Quantum.Measurement.BasisMeasurementProjection
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-! Real effects and independent copies in a specified real basis. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Matrix MatrixOrder ComplexOrder Kronecker

namespace D5.S3.Quantum.Fibers.RealCopyConjugation

open D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open D5.S3.Quantum.Fibers.FiveModeRealResponse
open D5.S3.Quantum.Fibers.FiveModeRealWaitSpan
open D5.S3.Quantum.Measurement.BasisMeasurementProjection
open D5.S3.Quantum.Entanglement.BipartiteSectorDecomposition

universe u

variable {n : Type u} [Fintype n] [DecidableEq n]

/-- Matrix coordinates of the native positive normalized state. -/
abbrev stateMatrix (rho : DensityState n) : Matrix n n ℂ :=
  CStarMatrix.ofMatrix.symm rho.1

/-- All real symmetric effects in the specified basis, with both operator bounds. -/
def RealEffect (n : Type*) [Fintype n] [DecidableEq n] :=
  {E : Matrix n n ℂ // E.PosSemidef ∧ (1 - E).PosSemidef ∧
    ∀ i j, (E i j).im = 0}

/-- The Born probability, including its physical interval bounds. -/
def probability (rho : DensityState n) (E : RealEffect n) : Set.Icc (0 : ℝ) 1 := by
  let X : Matrix n n ℂ := stateMatrix rho
  have hp := E.2.1.trace_mul_nonneg (density_posSemidef rho)
  have hq := E.2.2.1.trace_mul_nonneg (density_posSemidef rho)
  have ht : Matrix.trace ((1 - E.1) * X) = 1 - Matrix.trace (E.1 * X) := by
    have hX : Matrix.trace X = 1 := rho.2.2
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub, hX]
  refine ⟨(Matrix.trace (E.1 * X)).re, (Complex.nonneg_iff.mp hp).1, ?_⟩
  change 0 ≤ Matrix.trace ((1 - E.1) * X) at hq
  rw [ht] at hq
  have h := (Complex.nonneg_iff.mp hq).1
  simpa only [Complex.sub_re, Complex.one_re, sub_nonneg] using h

/-- Equality for the entire real effect interval, with no restricted measurement menu. -/
def SameRealStatistics (rho sigma : DensityState n) : Prop :=
  ∀ E : RealEffect n, probability rho E = probability sigma E

private theorem real_trace_pairing (E : RealEffect n) (X : Matrix n n ℂ) :
    (Matrix.trace (E.1 * X)).re =
      Matrix.trace (E.1.map Complex.re * X.map Complex.re) := by
  simp [Matrix.trace, Matrix.mul_apply, Complex.mul_re, E.2.2.2]

private def projectionEffect (P : Matrix n n ℂ) (hp : IsStarProjection P)
    (hr : ∀ i j, (P i j).im = 0) : RealEffect n :=
  ⟨P, Matrix.nonneg_iff_posSemidef.mp hp.nonneg,
    Matrix.nonneg_iff_posSemidef.mp hp.one_sub_nonneg, hr⟩

private def diagonalEffect (i : n) : RealEffect n :=
  projectionEffect (Matrix.single i i 1)
    ⟨by simp [IsIdempotentElem, Matrix.single_mul_single_same], by
      simp [IsSelfAdjoint, Matrix.star_eq_conjTranspose]⟩
    (by intro a b; simp [Matrix.single, apply_ite])

private def pairEffect (i j : n) (hij : i ≠ j) : RealEffect n := by
  let v : n → ℂ := Pi.single i 1 + Pi.single j 1
  let P : Matrix n n ℂ := (2 : ℂ)⁻¹ • Matrix.vecMulVec v (star v)
  have hv : star v ⬝ᵥ v = 2 := by
    simp [v, dotProduct_add, hij, Ne.symm hij]
    norm_num
  apply projectionEffect P
  · refine ⟨?_, ?_⟩
    · change P * P = P
      simp only [P, Matrix.smul_mul, Matrix.mul_smul,
        Matrix.vecMulVec_mul_vecMulVec, hv, Matrix.vecMulVec_smul, smul_smul]
      norm_num
    · exact ((Matrix.posSemidef_vecMulVec_self_star v).smul
        (Complex.nonneg_iff.mpr ⟨by norm_num, by norm_num⟩)).isHermitian
  · intro a b
    by_cases hai : a = i <;> by_cases haj : a = j <;>
      by_cases hbi : b = i <;> by_cases hbj : b = j <;>
      simp [P, v, Matrix.vecMulVec, Pi.single_apply, hai, haj, hbi, hbj, hij, Ne.symm hij]

private theorem statistics_iff_real (rho sigma : DensityState n) :
    SameRealStatistics rho sigma ↔
      (stateMatrix rho).map Complex.re =
        (stateMatrix sigma).map Complex.re := by
  constructor
  · intro h
    have hd (i : n) : (stateMatrix rho i i).re =
        (stateMatrix sigma i i).re := by
      have he := congrArg Subtype.val (h (diagonalEffect i))
      simpa [probability, diagonalEffect, projectionEffect, Matrix.trace_single_mul] using he
    ext i j
    by_cases hij : i = j
    · subst j; exact hd i
    have he := congrArg Subtype.val (h (pairEffect i j hij))
    change (Matrix.trace ((pairEffect i j hij).1 * stateMatrix rho)).re =
      (Matrix.trace ((pairEffect i j hij).1 * stateMatrix sigma)).re at he
    have hr := congrArg Complex.re ((density_posSemidef rho).isHermitian.apply i j)
    have hs := congrArg Complex.re ((density_posSemidef sigma).isHermitian.apply i j)
    simp only [Complex.star_def, Complex.conj_re] at hr hs
    have heq (X : Matrix n n ℂ) :
        Matrix.trace ((pairEffect i j hij).1 * X) =
          (2 : ℂ)⁻¹ * (X i i + X j i + X i j + X j j) := by
      change Matrix.trace (((2 : ℂ)⁻¹ • Matrix.vecMulVec
        (Pi.single i 1 + Pi.single j 1)
        (star (Pi.single i 1 + Pi.single j 1))) * X) = _
      rw [Matrix.smul_mul, Matrix.trace_smul, Matrix.vecMulVec_mul,
        Matrix.trace_vecMulVec]
      simp [add_dotProduct, Matrix.vecMul, mul_add]
      ring
    rw [heq, heq] at he
    norm_num [Complex.mul_re, Complex.add_re] at he
    change (stateMatrix rho i i).re + (stateMatrix rho j i).re +
      (stateMatrix rho i j).re + (stateMatrix rho j j).re =
      (stateMatrix sigma i i).re + (stateMatrix sigma j i).re +
      (stateMatrix sigma i j).re + (stateMatrix sigma j j).re at he
    change (stateMatrix rho j i).re = (stateMatrix rho i j).re at hr
    change (stateMatrix sigma j i).re = (stateMatrix sigma i j).re at hs
    change (stateMatrix rho i j).re = (stateMatrix sigma i j).re
    linarith [hd i, hd j]
  · intro h E
    apply Subtype.ext
    change (Matrix.trace (E.1 * stateMatrix rho)).re =
      (Matrix.trace (E.1 * stateMatrix sigma)).re
    rw [real_trace_pairing, real_trace_pairing, h]

/-- Conjugation in the specified real basis; positivity and normalization are preserved. -/
def conjugate (rho : DensityState n) : DensityState n :=
  ⟨CStarMatrix.ofMatrix (stateMatrix rho).transpose,
    map_nonneg CStarMatrix.ofMatrixStarAlgEquiv
      (density_posSemidef rho).transpose.nonneg,
    (Matrix.trace_transpose _).trans rho.2.2⟩

private theorem conjugate_apply (rho : DensityState n) (i j : n) :
    (conjugate rho).1 i j = star (stateMatrix rho i j) := by
  exact ((density_posSemidef rho).isHermitian.apply j i).symm

private theorem same_real_conjugate (rho : DensityState n) :
    SameRealStatistics rho (conjugate rho) := by
  apply (statistics_iff_real _ _).mpr
  ext i j
  simp [conjugate_apply]

private theorem real_product_marginal {m : Type*} [Fintype m] [DecidableEq m]
    (rho sigma : DensityState n) (eta theta : DensityState m)
    (h : (stateMatrix (productState rho eta)).map Complex.re =
      (stateMatrix (productState sigma theta)).map Complex.re) :
    (stateMatrix rho).map Complex.re =
      (stateMatrix sigma).map Complex.re := by
  have hc := congrArg (fun X : Matrix (n × m) (n × m) ℝ =>
    fun i j => ∑ b, X (i,b) (j,b)) h
  ext i j
  have he := congrFun (congrFun hc i) j
  have hr := congrArg (fun X : Matrix n n ℂ => (X i j).re)
    (partialTraceRight_kronecker (stateMatrix rho) (stateMatrix eta))
  have hs := congrArg (fun X : Matrix n n ℂ => (X i j).re)
    (partialTraceRight_kronecker (stateMatrix sigma) (stateMatrix theta))
  have htr : Matrix.trace (stateMatrix eta) = 1 := eta.2.2
  have hts : Matrix.trace (stateMatrix theta) = 1 := theta.2.2
  rw [htr, one_smul] at hr
  rw [hts, one_smul] at hs
  simp only [partialTraceRight, Complex.re_sum] at hr hs
  exact hr.symm.trans (he.trans hs)

private theorem square_products_sign {ι : Type*} (a b : ι → ℝ)
    (h : ∀ i j, a i * a j = b i * b j) : b = a ∨ b = -a := by
  by_cases ha : a = 0
  · left
    subst a
    funext i
    have hi := h i i
    simp only [Pi.zero_apply, zero_mul] at hi
    exact (mul_self_eq_zero.mp hi.symm)
  · obtain ⟨i, hi⟩ : ∃ i, a i ≠ 0 := Function.ne_iff.mp ha
    rcases mul_self_eq_mul_self_iff.mp (h i i).symm with hp | hp
    · left
      funext j
      apply mul_left_cancel₀ hi
      simpa only [hp] using (h i j).symm
    · right
      funext j
      have hj := h i j
      rw [hp] at hj
      change b j = -a j
      apply (mul_left_cancel₀ hi)
      nlinarith

/-- Complete real two-copy statistics determine exactly one conjugation orbit.
No assumption on rank, purity, nonzero imaginary part, or carrier size is made. -/
private theorem two_copy_classification (rho sigma : DensityState n) :
    SameRealStatistics (productState rho rho) (productState sigma sigma) ↔
      sigma = rho ∨ sigma = conjugate rho := by
  constructor
  · intro h
    have htwo := (statistics_iff_real _ _).mp h
    have hone := real_product_marginal rho sigma rho sigma htwo
    have him (p q : n × n) :
        (stateMatrix rho p.1 p.2).im *
          (stateMatrix rho q.1 q.2).im =
        (stateMatrix sigma p.1 p.2).im *
          (stateMatrix sigma q.1 q.2).im := by
      have ht := congrFun (congrFun htwo (p.1,q.1)) (p.2,q.2)
      have hp := congrFun (congrFun hone p.1) p.2
      have hq := congrFun (congrFun hone q.1) q.2
      change (stateMatrix rho p.1 p.2 * stateMatrix rho q.1 q.2).re =
        (stateMatrix sigma p.1 p.2 * stateMatrix sigma q.1 q.2).re at ht
      simp only [Complex.mul_re] at ht
      change (stateMatrix rho p.1 p.2).re = (stateMatrix sigma p.1 p.2).re at hp
      change (stateMatrix rho q.1 q.2).re = (stateMatrix sigma q.1 q.2).re at hq
      rw [hp, hq] at ht
      linarith
    rcases square_products_sign
      (fun p : n × n => (stateMatrix rho p.1 p.2).im)
      (fun p : n × n => (stateMatrix sigma p.1 p.2).im) him with hsign | hsign
    · left
      apply Subtype.ext
      ext i j
      apply Complex.ext
      · exact (congrFun (congrFun hone i) j).symm
      · exact congrFun hsign (i,j)
    · right
      apply Subtype.ext
      ext i j
      rw [conjugate_apply]
      apply Complex.ext
      · exact (congrFun (congrFun hone i) j).symm
      · exact congrFun hsign (i,j)
  · rintro (rfl | rfl)
    · intro E; rfl
    · apply (statistics_iff_real _ _).mpr
      ext p q
      change (stateMatrix rho p.1 q.1 * stateMatrix rho p.2 q.2).re =
        ((conjugate rho).1 p.1 q.1 * (conjugate rho).1 p.2 q.2).re
      simp only [conjugate_apply, Complex.star_def, ← map_mul, Complex.conj_re]

/-- Product-basis labels, with the singleton carrier for zero copies. -/
def CopyIndex (n : Type u) : ℕ → Type u
  | 0 => PUnit.{u + 1}
  | 1 => n
  | k + 2 => n × CopyIndex n (k + 1)

instance copyFintype (k : ℕ) : Fintype (CopyIndex n k) :=
  match k with
  | 0 => inferInstanceAs (Fintype PUnit.{u + 1})
  | 1 => inferInstanceAs (Fintype n)
  | k + 2 =>
    letI := copyFintype (k + 1)
    inferInstanceAs (Fintype (n × CopyIndex n (k + 1)))

instance copyDecidableEq (k : ℕ) : DecidableEq (CopyIndex n k) :=
  match k with
  | 0 => inferInstanceAs (DecidableEq PUnit.{u + 1})
  | 1 => inferInstanceAs (DecidableEq n)
  | k + 2 =>
    letI := copyDecidableEq (k + 1)
    inferInstanceAs (DecidableEq (n × CopyIndex n (k + 1)))

/-- Independent, identically prepared copies, formed by actual Kronecker products. -/
def copies (rho : DensityState n) : (k : ℕ) → DensityState (CopyIndex n k)
  | 0 => ⟨CStarMatrix.ofMatrix 1, by exact zero_le_one, by
    change Matrix.trace (1 : Matrix PUnit.{u + 1} PUnit.{u + 1} ℂ) = 1
    simp [Matrix.trace, Matrix.diag]⟩
  | 1 => rho
  | k + 2 => productState rho (copies rho (k + 1))

private theorem conjugate_copies (rho : DensityState n) :
    ∀ k, copies (conjugate rho) k = conjugate (copies rho k)
  | 0 => by apply Subtype.ext; rfl
  | 1 => rfl
  | k + 2 => by
    change productState (conjugate rho) (copies (conjugate rho) (k + 1)) = _
    rw [conjugate_copies rho (k + 1)]
    apply Subtype.ext
    exact congrArg CStarMatrix.ofMatrix
      (Matrix.kroneckerMap_transpose (fun z w : ℂ => z * w)
        (stateMatrix rho) (stateMatrix (copies rho (k + 1))))

private theorem real_product_tail {m : Type*} [Fintype m] [DecidableEq m]
    (rho sigma : DensityState n) (eta theta : DensityState m)
    (h : SameRealStatistics (productState rho eta) (productState sigma theta)) :
    SameRealStatistics eta theta := by
  apply (statistics_iff_real _ _).mpr
  have hreal := (statistics_iff_real _ _).mp h
  have hc := congrArg (fun X : Matrix (n × m) (n × m) ℝ =>
    fun i j => ∑ a, X (a,i) (a,j)) hreal
  ext i j
  have he := congrFun (congrFun hc i) j
  have hr := congrArg (fun X : Matrix m m ℂ => (X i j).re)
    (partialTraceLeft_kronecker (stateMatrix rho) (stateMatrix eta))
  have hs := congrArg (fun X : Matrix m m ℂ => (X i j).re)
    (partialTraceLeft_kronecker (stateMatrix sigma) (stateMatrix theta))
  have htr : Matrix.trace (stateMatrix rho) = 1 := rho.2.2
  have hts : Matrix.trace (stateMatrix sigma) = 1 := sigma.2.2
  rw [htr, one_smul] at hr
  rw [hts, one_smul] at hs
  simp only [partialTraceLeft, Complex.re_sum] at hr hs
  exact hr.symm.trans (he.trans hs)

private theorem copies_reduce (rho sigma : DensityState n) :
    ∀ k, SameRealStatistics (copies rho (k + 2)) (copies sigma (k + 2)) →
      SameRealStatistics (productState rho rho) (productState sigma sigma)
  | 0, h => h
  | k + 1, h => copies_reduce rho sigma k
      (real_product_tail rho sigma (copies rho (k + 2)) (copies sigma (k + 2)) h)

private theorem orbit_statistics (rho sigma : DensityState n)
    (h : sigma = rho ∨ sigma = conjugate rho) (k : ℕ) :
    SameRealStatistics (copies rho k) (copies sigma k) := by
  rcases h with rfl | rfl
  · intro E; rfl
  · rw [conjugate_copies]
    exact same_real_conjugate _

private theorem fixed_copy_classification (rho sigma : DensityState n)
    (k : ℕ) (hk : 2 ≤ k) :
    SameRealStatistics (copies rho k) (copies sigma k) ↔
      sigma = rho ∨ sigma = conjugate rho := by
  constructor
  · intro h
    cases k with
    | zero => omega
    | succ k => cases k with
      | zero => omega
      | succ k => exact (two_copy_classification rho sigma).mp (copies_reduce rho sigma k h)
  · intro h
    exact orbit_statistics rho sigma h k

private theorem conjugate_fixed_iff (rho : DensityState n) :
    conjugate rho = rho ↔ (stateMatrix rho).map Complex.im = 0 := by
  constructor
  · intro h
    ext i j
    have he := congrArg (fun r : DensityState n => (stateMatrix r i j).im) h
    change ((conjugate rho).1 i j).im = (stateMatrix rho i j).im at he
    rw [conjugate_apply] at he
    simp only [Complex.star_def, Complex.conj_im] at he
    change (stateMatrix rho i j).im = 0
    linarith
  · intro h
    apply Subtype.ext
    ext i j
    rw [conjugate_apply]
    apply Complex.ext
    · simp
    · have hi := congrFun (congrFun h i) j
      change (stateMatrix rho i j).im = 0 at hi
      change -(stateMatrix rho i j).im = (stateMatrix rho i j).im
      calc
        -(stateMatrix rho i j).im = -0 := congrArg Neg.neg hi
        _ = 0 := neg_zero
        _ = (stateMatrix rho i j).im := hi.symm

/-- Complete classification for actual density matrices and all real effects.
Each fixed number of copies at least two has precisely the conjugation-orbit
fiber. All positive copy counts give the same equivalence. The real stratum
is fixed and every indistinguishable state has the same rank. -/
theorem real_copy_classification (rho sigma : DensityState n) :
    (SameRealStatistics (copies rho 2) (copies sigma 2) ↔
      sigma = rho ∨ sigma = conjugate rho) ∧
    ((∀ k, 1 ≤ k → SameRealStatistics (copies rho k) (copies sigma k)) ↔
      sigma = rho ∨ sigma = conjugate rho) ∧
    (∀ k, 2 ≤ k → (SameRealStatistics (copies rho k) (copies sigma k) ↔
      sigma = rho ∨ sigma = conjugate rho)) ∧
    (conjugate rho = rho ↔ (stateMatrix rho).map Complex.im = 0) ∧
    (∀ k, 2 ≤ k → SameRealStatistics (copies rho k) (copies sigma k) →
      (stateMatrix sigma).rank = (stateMatrix rho).rank) := by
  refine ⟨two_copy_classification rho sigma, ?_, fixed_copy_classification rho sigma,
    conjugate_fixed_iff rho, ?_⟩
  · constructor
    · intro h
      exact (two_copy_classification rho sigma).mp (h 2 (by decide))
    · intro h k _
      exact orbit_statistics rho sigma h k
  · intro k hk h
    rcases (fixed_copy_classification rho sigma k hk).mp h with rfl | rfl
    · rfl
    · exact Matrix.rank_transpose (stateMatrix rho)

#print axioms real_copy_classification


/-! Five-mode boundary: the dimension is taken from the actual normalized density-state
carrier and its real statistical image, while the conjugation identification is retained as
an explicit quotient relation. -/

abbrev FiveModeState := DensityState (Fin 5)

def fiveModeRealCoordinate (rho : FiveModeState) : symmetricSpace :=
  ⟨(stateMatrix rho).map Complex.re,
    by
      ext i j
      have h := congrArg Complex.re ((density_posSemidef rho).isHermitian.apply i j)
      simpa using h⟩

def fiveModePhysicalImage : Set symmetricSpace := Set.range fiveModeRealCoordinate

def fiveModeNormalizedDirections : Submodule ℝ symmetricSpace :=
  LinearMap.ker ((Matrix.traceLinearMap (Fin 5) ℝ ℝ).comp symmetricSpace.subtype)

private theorem fiveModeRealCoordinate_trace_one (rho : FiveModeState) :
    Matrix.trace ((stateMatrix rho).map Complex.re) = 1 := by
  have ht := congrArg Complex.re rho.2.2
  change (∑ i, ((stateMatrix rho) i i).re) = 1 at ht
  change ∑ i, ((stateMatrix rho) i i).re = 1
  exact ht

private theorem fiveModeNormalizedDirections_finrank :
    Module.finrank ℝ fiveModeNormalizedDirections = 14 := by
  let rho : Matrix (Fin 5) (Fin 5) ℂ := Matrix.diagonal (fun _ => (1 / 5 : ℝ))
  have h := full_rank_blind_fiber_neighborhood rho
    (by
      apply Matrix.PosDef.diagonal
      intro i
      norm_num)
    (by simp [rho, Matrix.trace])
  exact h.2.1

private theorem fiveModePhysicalImage_direction :
    (affineSpan ℝ fiveModePhysicalImage).direction = fiveModeNormalizedDirections := by
  apply le_antisymm
  · rw [direction_affineSpan, vectorSpan_def, Submodule.span_le]
    rintro value ⟨first, ⟨rho, rfl⟩, second, ⟨sigma, rfl⟩, rfl⟩
    change fiveModeRealCoordinate rho - fiveModeRealCoordinate sigma ∈
      fiveModeNormalizedDirections
    apply LinearMap.mem_ker.mpr
    change Matrix.trace ((stateMatrix rho).map Complex.re -
      (stateMatrix sigma).map Complex.re) = 0
    rw [Matrix.trace_sub, fiveModeRealCoordinate_trace_one,
      fiveModeRealCoordinate_trace_one, sub_self]
  · intro value hvalue
    let D : symmetricSpace := value
    have hD : D ∈ fiveModeNormalizedDirections := hvalue
    let H : HermitianSpace 5 := ⟨D.1.map Complex.ofReal, by
      ext i j
      have h := congrArg Complex.ofReal (congrFun (congrFun D.2 i) j)
      simpa using h⟩
    have htrace : Matrix.trace H.1 = 0 := by
      have hDtrace : Matrix.trace D.1 = 0 := by
        exact (LinearMap.mem_ker.mp hD)
      change Matrix.trace (D.1.map Complex.ofReal) = 0
      simp only [Matrix.trace, Matrix.diag, Matrix.map_apply, Complex.ofReal_zero,
        Complex.ofReal_sum]
      simpa [Matrix.trace] using congrArg Complex.ofReal hDtrace
    let difference : traceZeroHermitian 5 := ⟨H, htrace⟩
    obtain ⟨eps, heps, plus, minus, hmatrices⟩ :=
      D5.S3.Quantum.Measurements.VisibleStateSpaceDimension.traceless_density_perturbations
        5 difference
    have hdiff : fiveModeRealCoordinate plus - fiveModeRealCoordinate minus =
        (2 * eps) • D := by
      apply Subtype.ext
      ext i j
      have hh := congrArg (fun X : Matrix (Fin 5) (Fin 5) ℂ => (X i j).re) hmatrices
      simp [fiveModeRealCoordinate, stateMatrix, H, difference, Matrix.sub_apply,
        Matrix.smul_apply, smul_eq_mul] at hh ⊢
      linarith
    have hvsub : fiveModeRealCoordinate plus - fiveModeRealCoordinate minus ∈
        vectorSpan ℝ fiveModePhysicalImage :=
      vsub_mem_vectorSpan ℝ ⟨plus, rfl⟩ ⟨minus, rfl⟩
    rw [hdiff] at hvsub
    have hs := (vectorSpan ℝ fiveModePhysicalImage).smul_mem (2 * eps)⁻¹ hvsub
    rw [smul_smul, inv_mul_cancel₀ (mul_ne_zero (by norm_num) heps.ne'), one_smul] at hs
    rw [direction_affineSpan]
    exact hs

/-- The normalized one-copy image is the actual real-statistics image; its affine direction
has real dimension 14. The dimension is the finrank of the trace-one symmetric carrier. -/
theorem five_mode_physical_image_dimension :
    Module.finrank ℝ (affineSpan ℝ fiveModePhysicalImage).direction = 14 ∧
    (∀ rho sigma : FiveModeState,
      SameRealStatistics rho sigma ↔ fiveModeRealCoordinate rho = fiveModeRealCoordinate sigma) := by
  refine ⟨by rw [fiveModePhysicalImage_direction, fiveModeNormalizedDirections_finrank], ?_⟩
  intro rho sigma
  constructor
  · intro h
    apply Subtype.ext
    exact (statistics_iff_real rho sigma).mp h
  · intro h
    apply (statistics_iff_real rho sigma).mpr
    exact congrArg Subtype.val h

/-- The orbit quotient is the literal quotient of actual density states by the two alternatives
returned by the statistical classification. -/
private theorem fiveModeConjugate_involutive (rho : FiveModeState) :
    conjugate (conjugate rho) = rho := by
  apply Subtype.ext
  change Matrix.transpose (Matrix.transpose (stateMatrix rho)) = stateMatrix rho
  simp

def fiveModeOrbitRel : Setoid FiveModeState where
  r rho sigma := sigma = rho ∨ sigma = conjugate rho
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro rho; exact Or.inl rfl
    · intro rho sigma h
      rcases h with h | h
      · exact Or.inl h.symm
      · right
        rw [h, fiveModeConjugate_involutive]
    · intro rho sigma tau h1 h2
      rcases h1 with h1 | h1
      · rcases h2 with h2 | h2
        · exact Or.inl (h2.trans h1)
        · have hc : conjugate sigma = conjugate rho :=
            congrArg (fun x : FiveModeState => conjugate x) h1
          exact (show tau = conjugate rho from h2.trans hc) |> Or.inr
      · rcases h2 with h2 | h2
        · exact Or.inr (h2.trans h1)
        · have hc : conjugate sigma = conjugate (conjugate rho) :=
            congrArg (fun x : FiveModeState => conjugate x) h1
          exact Or.inl (h2.trans (hc.trans (by rw [fiveModeConjugate_involutive])))

def fiveModeOrbitQuotient := Quotient fiveModeOrbitRel

def fiveModeOrbitProjection (rho : FiveModeState) : fiveModeOrbitQuotient :=
  Quotient.mk fiveModeOrbitRel rho

end D5.S3.Quantum.Fibers.RealCopyConjugation
