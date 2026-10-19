/- GID: D5/S3/Combinatorics/SpectralGraph/SixSupportLaplacianLowRoot
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/SixSupportLaplacianLowRoot
   mirror-E: none(waiver:source-only-positive-theorem)
   anchors: []
   utility: none
   digest: Positive-real six-support quotient low eigenvalue and sharp balanced threshold. -/

import D5.S3.Weil.ZetaLinear.Sylvester
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
The matrix and spectral questions are attributed to the public manuscript
`ideal-intersection-laplacian`, `paper/core/body.tex`, commit
`b93becea662a746badeadba42fdc3d3eb3db9382`, the six-support complement
quotient, uniform-low-root theorem and localization-sharpness proposition.
The Lean proofs here are independently authored. No graph-integrality
classification or priority claim is made.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix Finset Filter Topology

namespace D5.S3.Combinatorics.SpectralGraph.SixSupportLaplacianLowRoot

/-- Support order: `1,2,3,12,13,23`. -/
def quotient (a b c : ℝ) : Matrix (Fin 6) (Fin 6) ℝ :=
  !![b+c+b*c, -b, -c, 0, 0, -b*c;
     -a, a+c+a*c, -c, 0, -a*c, 0;
     -a, -b, a+b+a*b, -a*b, 0, 0;
     0, 0, -c, c, 0, 0;
     0, -b, 0, 0, b, 0;
     -a, 0, 0, 0, 0, a]

def weights (a b c : ℝ) : Fin 6 → ℝ := ![a,b,c,a*b,a*c,b*c]

private lemma energy (a b c : ℝ) (z : Fin 6 → ℝ) :
    dotProduct (fun i => weights a b c i * z i) (quotient a b c *ᵥ z) =
      a*b*(z 0-z 1)^2 + a*c*(z 0-z 2)^2 + b*c*(z 1-z 2)^2 +
      a*b*c*((z 0-z 5)^2+(z 1-z 4)^2+(z 2-z 3)^2) := by
  simp [dotProduct, mulVec, quotient, weights, Fin.sum_univ_succ]
  ring

private lemma constant_kernel (a b c t : ℝ) :
    quotient a b c *ᵥ (fun _ => t) = 0 := by
  ext i
  fin_cases i <;> simp [quotient, mulVec, dotProduct, Fin.sum_univ_succ] <;> ring

private lemma kernel_constant (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (z : Fin 6 → ℝ) (hz : quotient a b c *ᵥ z = 0) : ∃ t, z = fun _ => t := by
  have he := energy a b c z
  rw [hz] at he
  simp only [dotProduct_zero] at he
  have hab : 0 < a*b := mul_pos ha hb
  have hac : 0 < a*c := mul_pos ha hc
  have hbc : 0 < b*c := mul_pos hb hc
  have hp : 0 < a*b*c := mul_pos hab hc
  have htri : a*b*(z 0-z 1)^2 + a*c*(z 0-z 2)^2 + b*c*(z 1-z 2)^2 = 0 :=
    ((add_eq_zero_iff_of_nonneg (by positivity) (by positivity)).mp he.symm).1
  have hpend : (z 0-z 5)^2+(z 1-z 4)^2+(z 2-z 3)^2 = 0 := by
    have h := ((add_eq_zero_iff_of_nonneg (by positivity) (by positivity)).mp he.symm).2
    exact (mul_eq_zero.mp h).resolve_left hp.ne'
  have htri' := (add_eq_zero_iff_of_nonneg (by positivity) (by positivity)).mp htri
  have htri'' := (add_eq_zero_iff_of_nonneg (by positivity) (by positivity)).mp htri'.1
  have h01 : z 0 = z 1 := by
    have h := (mul_eq_zero.mp htri''.1).resolve_left hab.ne'
    nlinarith only [h]
  have h02 : z 0 = z 2 := by
    have h := (mul_eq_zero.mp htri''.2).resolve_left hac.ne'
    nlinarith only [h]
  have h05 : z 0 = z 5 := by
    nlinarith only [hpend, sq_nonneg (z 1-z 4), sq_nonneg (z 2-z 3)]
  have h14 : z 1 = z 4 := by
    nlinarith only [hpend, sq_nonneg (z 0-z 5), sq_nonneg (z 2-z 3)]
  have h23 : z 2 = z 3 := by
    nlinarith only [hpend, sq_nonneg (z 0-z 5), sq_nonneg (z 1-z 4)]
  refine ⟨z 0, ?_⟩
  ext i
  fin_cases i
  · rfl
  · exact h01.symm
  · exact h02.symm
  · exact h23.symm.trans h02.symm
  · exact h14.symm.trans h01.symm
  · exact h05.symm

/-- Exact energy and complete zero-kernel description on all positive real weights. -/
private theorem weighted_geometry (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (∀ z : Fin 6 → ℝ,
      dotProduct (fun i => weights a b c i * z i) (quotient a b c *ᵥ z) =
        a*b*(z 0-z 1)^2 + a*c*(z 0-z 2)^2 + b*c*(z 1-z 2)^2 +
        a*b*c*((z 0-z 5)^2+(z 1-z 4)^2+(z 2-z 3)^2)) ∧
    (∀ z, quotient a b c *ᵥ z = 0 ↔ ∃ t, z = fun _ => t) ∧
    quotient a b c *ᵥ (fun _ => (1 : ℝ)) = 0 ∧
    vecMul (weights a b c) (quotient a b c) = 0 := by
  refine ⟨energy a b c, ?_, constant_kernel a b c 1, ?_⟩
  · intro z
    exact ⟨kernel_constant a b c ha hb hc z, by rintro ⟨t,rfl⟩; exact constant_kernel a b c t⟩
  · ext i
    fin_cases i <;> simp [vecMul, dotProduct, quotient, weights, Fin.sum_univ_succ] <;> ring



/-- Reorder to `1,2,3,23,13,12`. -/
def supportPermutation : Equiv.Perm (Fin 6) where
  toFun := ![0,1,2,5,4,3]
  invFun := ![0,1,2,5,4,3]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

/-- Positive square-root weights in the reordered coordinates. -/
def rootWeights (a b c : ℝ) : Fin 6 → ℝ :=
  ![Real.sqrt a, Real.sqrt b, Real.sqrt c,
    Real.sqrt b * Real.sqrt c, Real.sqrt a * Real.sqrt c, Real.sqrt a * Real.sqrt b]

/-- Symmetric representative, with the paired diagonal in the order `a,b,c`. -/
def symmetric (a b c : ℝ) : Matrix (Fin 6) (Fin 6) ℝ :=
  let p := Real.sqrt a * Real.sqrt b * Real.sqrt c
  !![b+c+b*c, -Real.sqrt a*Real.sqrt b, -Real.sqrt a*Real.sqrt c, -p, 0, 0;
     -Real.sqrt a*Real.sqrt b, a+c+a*c, -Real.sqrt b*Real.sqrt c, 0, -p, 0;
     -Real.sqrt a*Real.sqrt c, -Real.sqrt b*Real.sqrt c, a+b+a*b, 0, 0, -p;
     -p, 0, 0, a, 0, 0;
     0, -p, 0, 0, b, 0;
     0, 0, -p, 0, 0, c]

private lemma symmetric_hermitian (a b c : ℝ) : (symmetric a b c).IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [symmetric, conjTranspose_apply]

private lemma rootWeights_pos (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (i : Fin 6) : 0 < rootWeights a b c i := by
  fin_cases i <;> dsimp [rootWeights] <;> positivity

private lemma intertwine (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    symmetric a b c * diagonal (rootWeights a b c) =
      diagonal (rootWeights a b c) *
        (quotient a b c).submatrix supportPermutation supportPermutation := by
  ext i j
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.submatrix_apply]
  change symmetric a b c i j * rootWeights a b c j =
    rootWeights a b c i * quotient a b c (![0,1,2,5,4,3] i) (![0,1,2,5,4,3] j)
  fin_cases i <;> fin_cases j <;>
    norm_num [symmetric, rootWeights, quotient] <;>
    ring_nf <;> simp [Real.sq_sqrt ha.le, Real.sq_sqrt hb.le, Real.sq_sqrt hc.le] <;> ring <;> simp

/-- The exact diagonal similarity, including the coordinate permutation. -/
private theorem diagonal_similarity (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    symmetric a b c = diagonal (rootWeights a b c) *
      (quotient a b c).submatrix supportPermutation supportPermutation *
        diagonal (fun i => (rootWeights a b c i)⁻¹) := by
  have hi : diagonal (rootWeights a b c) * diagonal (fun i => (rootWeights a b c i)⁻¹) =
      (1 : Matrix (Fin 6) (Fin 6) ℝ) := by
    rw [diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst j; simp [ne_of_gt (rootWeights_pos a b c ha hb hc i)]
    · simp [hij]
  rw [← intertwine a b c ha hb hc, Matrix.mul_assoc, hi, Matrix.mul_one]

/-- Transport a symmetric eigenvector to the original support order. -/
def toQuotientVector (a b c : ℝ) (z : Fin 6 → ℝ) : Fin 6 → ℝ :=
  fun i => z (supportPermutation.symm i) / rootWeights a b c (supportPermutation.symm i)

private lemma eigenvector_transport (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (e : ℝ) (z : Fin 6 → ℝ) (hz : z ≠ 0) (he : symmetric a b c *ᵥ z = e • z) :
    toQuotientVector a b c z ≠ 0 ∧
      quotient a b c *ᵥ toQuotientVector a b c z = e • toQuotientVector a b c z := by
  let d := rootWeights a b c
  let y := fun i => z i / d i
  have hdy : diagonal d *ᵥ y = z := by
    ext i
    rw [Matrix.mulVec_diagonal]
    dsimp [y, d]
    field_simp [ne_of_gt (rootWeights_pos a b c ha hb hc i)]
  have hy : (quotient a b c).submatrix supportPermutation supportPermutation *ᵥ y = e • y := by
    have h := congrArg (fun M : Matrix (Fin 6) (Fin 6) ℝ => M *ᵥ y)
      (intertwine a b c ha hb hc)
    rw [← mulVec_mulVec, hdy, he, ← mulVec_mulVec] at h
    ext i
    have hh := congrFun h i
    simp only [mulVec_diagonal, Pi.smul_apply, smul_eq_mul] at hh ⊢
    have hzi := congrFun hdy i
    simp only [mulVec_diagonal] at hzi
    apply mul_left_cancel₀ (rootWeights_pos a b c ha hb hc i).ne'
    change d i * _ = d i * _
    rw [← hh, ← hzi]
    ring
  refine ⟨?_, ?_⟩
  · intro hzero
    apply hz
    ext i
    have h := congrFun hzero (supportPermutation i)
    simpa [toQuotientVector, div_eq_zero_iff,
      ne_of_gt (rootWeights_pos a b c ha hb hc i)] using h
  · have h := Matrix.submatrix_mulVec_equiv (quotient a b c) y
      supportPermutation supportPermutation
    rw [hy] at h
    ext i
    have hh := congrFun h (supportPermutation.symm i)
    change (quotient a b c *ᵥ (y ∘ supportPermutation.symm)) i =
      e * y (supportPermutation.symm i)
    simpa only [Function.comp_apply, Equiv.apply_symm_apply, Pi.smul_apply, smul_eq_mul] using hh.symm



/-- Smaller balanced quadratic root. -/
def balancedLow (m : ℝ) : ℝ :=
  (m^2+4*m-m*Real.sqrt ((m+4)^2-12))/2

private def balancedHigh (m : ℝ) : ℝ :=
  (m^2+4*m+m*Real.sqrt ((m+4)^2-12))/2

private lemma balanced_scalar (m : ℝ) (hm : 1 ≤ m) :
    0 < balancedLow m ∧ balancedLow m < m ∧ balancedLow m < 3 ∧
    3*m/(m+4) < balancedLow m ∧
    balancedLow m = 6*m/(m+4+Real.sqrt ((m+4)^2-12)) ∧
    (balancedLow m)^2-(m^2+4*m)*balancedLow m+3*m^2 = 0 ∧
    balancedLow m < balancedHigh m ∧ m < balancedHigh m ∧ 3 < balancedHigh m := by
  have hm0 : 0 < m := lt_of_lt_of_le zero_lt_one hm
  have hd : 0 ≤ (m+4)^2-12 := by nlinarith
  have hs := Real.sq_sqrt hd
  have hs0 := Real.sqrt_nonneg ((m+4)^2-12)
  have hslt : Real.sqrt ((m+4)^2-12) < m+4 := by nlinarith
  have hsgt : m+2 < Real.sqrt ((m+4)^2-12) := by nlinarith
  have hsgt' : m-4 < Real.sqrt ((m+4)^2-12) := by nlinarith
  have hden : 0 < m+4+Real.sqrt ((m+4)^2-12) := by positivity
  have hr : balancedLow m = 6*m/(m+4+Real.sqrt ((m+4)^2-12)) := by
    apply (eq_div_iff hden.ne').2
    dsimp [balancedLow]
    nlinarith only [hs]
  have hp : 0 < balancedLow m := by rw [hr]; positivity
  have hsmall : balancedLow m < m := by
    dsimp [balancedLow]
    nlinarith only [mul_pos hm0 (sub_pos.mpr hsgt)]
  have hupper : balancedLow m < 3 := by
    rw [hr, div_lt_iff₀ hden]
    nlinarith only [hsgt']
  have hlower : 3*m/(m+4) < balancedLow m := by
    rw [hr, div_lt_div_iff₀ (by positivity : 0 < m+4) hden]
    nlinarith only [mul_pos hm0 (sub_pos.mpr hslt)]
  have hroot : (balancedLow m)^2-(m^2+4*m)*balancedLow m+3*m^2 = 0 := by
    dsimp [balancedLow]
    nlinarith only [congrArg (fun r : ℝ => (m^2/4)*r) hs]
  have hhigh : m < balancedHigh m := by
    dsimp [balancedHigh]
    nlinarith only [mul_pos hm0 (by linarith : 0 < m+2+Real.sqrt ((m+4)^2-12))]
  have hhigh3 : 3 < balancedHigh m := by
    dsimp [balancedHigh]
    have hmul := mul_le_mul_of_nonneg_left hsgt.le hm0.le
    nlinarith
  refine ⟨hp,hsmall,hupper,hlower,hr,hroot,?_,hhigh,hhigh3⟩
  exact hsmall.trans hhigh

private lemma balanced_factorization (m x : ℝ) :
    (x • (1 : Matrix (Fin 6) (Fin 6) ℝ) - quotient m m m).det =
      x*(x-m^2-m)*(x^2-(m^2+4*m)*x+3*m^2)^2 := by
  let P : Matrix (Fin 6) (Fin 6) ℝ :=
    !![1,0,1,0,1,0; 1,0,-1,0,0,0; 1,0,0,0,-1,0;
       0,1,0,0,0,-1; 0,1,0,-1,0,0; 0,1,0,1,0,1]
  let Q : Matrix (Fin 6) (Fin 6) ℝ :=
    !![1/3,1/3,1/3,0,0,0; 0,0,0,1/3,1/3,1/3;
       1/3,-2/3,1/3,0,0,0; 0,0,0,1/3,-2/3,1/3;
       1/3,1/3,-2/3,0,0,0; 0,0,0,-2/3,1/3,1/3]
  let J : Matrix (Fin 6) (Fin 6) ℝ :=
    !![m^2,-m^2,0,0,0,0; -m,m,0,0,0,0;
       0,0,m^2+3*m,-m^2,0,0; 0,0,-m,m,0,0;
       0,0,0,0,m^2+3*m,-m^2; 0,0,0,0,-m,m]
  have hPQ : P*Q = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [P,Q,Matrix.mul_apply,Matrix.one_apply,Fin.sum_univ_succ]
  have hP : P.det ≠ 0 := by
    have h := congrArg Matrix.det hPQ
    rw [Matrix.det_mul,Matrix.det_one] at h
    intro hz
    rw [hz,zero_mul] at h
    exact zero_ne_one h
  have hCP : quotient m m m*P = P*J := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [P,J,quotient,Matrix.mul_apply,Fin.sum_univ_succ] <;> ring
  have hXP : (x • 1-quotient m m m)*P = P*(x • 1-J) := by
    simp only [Matrix.sub_mul,Matrix.mul_sub,Matrix.smul_mul,Matrix.mul_smul,
      Matrix.one_mul,Matrix.mul_one,hCP]
  have hdet : (x • (1 : Matrix (Fin 6) (Fin 6) ℝ)-quotient m m m).det =
      (x • (1 : Matrix (Fin 6) (Fin 6) ℝ)-J).det := by
    have h := congrArg Matrix.det hXP
    simp only [Matrix.det_mul] at h
    rw [mul_comm P.det] at h
    exact mul_right_cancel₀ hP h
  rw [hdet]
  let e : Fin 6 ≃ Fin 2 × Fin 3 :=
    (finProdFinEquiv : Fin 3 × Fin 2 ≃ Fin 6).symm.trans (Equiv.prodComm _ _)
  let blocks : Fin 3 → Matrix (Fin 2) (Fin 2) ℝ :=
    ![!![x-m^2,m^2;m,x-m],
      !![x-(m^2+3*m),m^2;m,x-m],
      !![x-(m^2+3*m),m^2;m,x-m]]
  have hblocks : x • (1 : Matrix (Fin 6) (Fin 6) ℝ)-J =
      (Matrix.blockDiagonal blocks).submatrix e e := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [J,blocks,e,finProdFinEquiv,Fin.divNat,Fin.modNat,Matrix.blockDiagonal,Matrix.one_apply]
  rw [hblocks,Matrix.det_submatrix_equiv_self,Matrix.det_blockDiagonal]
  simp [blocks,Fin.prod_univ_succ,Matrix.det_fin_two]
  <;> ring

private lemma balanced_symmetric_eigenvector (m : ℝ) (hm : 1 ≤ m) :
    ∃ z : Fin 6 → ℝ, z ≠ 0 ∧ symmetric m m m *ᵥ z = balancedLow m • z := by
  have h := balanced_scalar m hm
  have hm0 : 0 < m := lt_of_lt_of_le zero_lt_one hm
  have hml : m-balancedLow m ≠ 0 := sub_ne_zero.mpr (ne_of_gt h.2.1)
  let p := Real.sqrt m * Real.sqrt m * Real.sqrt m
  have hp : p^2 = m^3 := by
    dsimp [p]
    calc
      _ = ((Real.sqrt m)^2)^3 := by ring
      _ = m^3 := by rw [Real.sq_sqrt hm0.le]
  let t := p / (m-balancedLow m)
  refine ⟨![1,-1,0,t,-t,0], ?_, ?_⟩
  · intro hz
    have hzero := congrFun hz 0
    norm_num at hzero
  · have ht : (m-balancedLow m)*t = p := by dsimp [t]; field_simp
    have hpt : p*t*(m-balancedLow m) = p^2 := by
      calc
        _ = p*((m-balancedLow m)*t) := by ring
        _ = p^2 := by rw [ht]; ring
    have ht' : (m^2+3*m-balancedLow m)-p*t = 0 := by
      apply mul_right_cancel₀ hml
      linear_combination h.2.2.2.2.2.1 - hp - hpt
    have hp_simple : p = m*Real.sqrt m := by
      dsimp [p]
      rw [← pow_two, Real.sq_sqrt hm0.le]
    rw [hp_simple] at ht ht'
    ext i
    fin_cases i <;>
      simp [symmetric, mulVec, dotProduct, Fin.sum_univ_succ, Pi.smul_apply, smul_eq_mul,
        ← pow_two, Real.sq_sqrt hm0.le] <;> linarith only [ht, ht']

private lemma balanced_eigenvalue_cases (m : ℝ) (hm : 1 ≤ m) (e : ℝ)
    (z : Fin 6 → ℝ) (hz : z ≠ 0) (he : quotient m m m *ᵥ z = e • z) :
    e = 0 ∨ e = m^2+m ∨ e = balancedLow m ∨ e = balancedHigh m := by
  have hdet : (e • (1 : Matrix (Fin 6) (Fin 6) ℝ) - quotient m m m).det = 0 := by
    apply Matrix.exists_mulVec_eq_zero_iff.mp
    refine ⟨z, hz, ?_⟩
    simp [Matrix.sub_mulVec, Matrix.smul_mulVec, he]
  rw [balanced_factorization] at hdet
  have hsq := Real.sq_sqrt (show 0 ≤ (m+4)^2-12 by nlinarith)
  have hfactor : e^2-(m^2+4*m)*e+3*m^2 =
      (e-balancedLow m)*(e-balancedHigh m) := by
    dsimp [balancedLow, balancedHigh]
    nlinarith only [congrArg (fun r : ℝ => (m^2/4)*r) hsq]
  rw [hfactor] at hdet
  rcases mul_eq_zero.mp hdet with hzero | hzero
  · rcases mul_eq_zero.mp hzero with hzero | hzero
    · exact Or.inl hzero
    · exact Or.inr (Or.inl (by linarith only [hzero]))
  · rcases mul_eq_zero.mp ((pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp hzero) with hl | hh
    · exact Or.inr (Or.inr (Or.inl (sub_eq_zero.mp hl)))
    · exact Or.inr (Or.inr (Or.inr (sub_eq_zero.mp hh)))

/-- The balanced smaller root is an actual quotient eigenvalue and is least among
all positive real quotient eigenvalues. -/
private theorem balanced_smallest (m : ℝ) (hm : 1 ≤ m) :
    (∃ z : Fin 6 → ℝ, z ≠ 0 ∧ quotient m m m *ᵥ z = balancedLow m • z) ∧
    0 < balancedLow m ∧ balancedLow m < m ∧
    3*m/(m+4) < balancedLow m ∧ balancedLow m < 3 ∧
    balancedLow m = 6*m/(m+4+Real.sqrt ((m+4)^2-12)) ∧
    (∀ e : ℝ, 0 < e → ∀ z : Fin 6 → ℝ, z ≠ 0 →
      quotient m m m *ᵥ z = e • z → balancedLow m ≤ e) ∧
    (∀ x : ℝ, (x • (1 : Matrix (Fin 6) (Fin 6) ℝ) - quotient m m m).det =
      x*(x-m^2-m)*(x^2-(m^2+4*m)*x+3*m^2)^2) ∧
    balancedLow m < m^2+m ∧
    m^2+m < (m^2+4*m+m*Real.sqrt ((m+4)^2-12))/2 := by
  have hm0 : 0 < m := lt_of_lt_of_le zero_lt_one hm
  have h := balanced_scalar m hm
  obtain ⟨z,hz,he⟩ := balanced_symmetric_eigenvector m hm
  have hc := eigenvector_transport m m m hm0 hm0 hm0 (balancedLow m) z hz he
  refine ⟨⟨toQuotientVector m m m z,hc⟩,h.1,h.2.1,h.2.2.2.1,h.2.2.1,h.2.2.2.2.1,?_,
    balanced_factorization m,?_,?_⟩
  · intro e he w hw hew
    rcases balanced_eigenvalue_cases m hm e w hw hew with he0 | hem | hel | heh
    · exact (he.ne' he0).elim
    · rw [hem]; nlinarith only [h.2.1, sq_nonneg m]
    · exact le_of_eq hel.symm
    · rw [heh]; exact h.2.2.2.2.2.2.1.le
  · nlinarith only [h.2.1, sq_pos_of_pos hm0]
  · have hs : m+2 < Real.sqrt ((m+4)^2-12) := by
      have hh := Real.sq_sqrt (show 0 ≤ (m+4)^2-12 by nlinarith)
      have hpos := Real.sqrt_nonneg ((m+4)^2-12)
      nlinarith
    nlinarith only [hm0,mul_pos hm0 (sub_pos.mpr hs)]

private lemma symmetric_energy (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (z : Fin 6 → ℝ) :
    dotProduct z (symmetric a b c *ᵥ z) =
      (Real.sqrt b*z 0-Real.sqrt a*z 1)^2 +
      (Real.sqrt c*z 0-Real.sqrt a*z 2)^2 +
      (Real.sqrt c*z 1-Real.sqrt b*z 2)^2 +
      (Real.sqrt b*Real.sqrt c*z 0-Real.sqrt a*z 3)^2 +
      (Real.sqrt a*Real.sqrt c*z 1-Real.sqrt b*z 4)^2 +
      (Real.sqrt a*Real.sqrt b*z 2-Real.sqrt c*z 5)^2 := by
  simp [dotProduct, mulVec, symmetric, Fin.sum_univ_succ]
  ring_nf
  simp [Real.sq_sqrt ha.le, Real.sq_sqrt hb.le, Real.sq_sqrt hc.le]
  <;> ring

/-- The full symmetric representative is positive semidefinite. -/
private theorem symmetric_psd (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (symmetric a b c).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (symmetric_hermitian a b c)
  intro z
  simp only [star_trivial]
  rw [symmetric_energy a b c ha hb hc z]
  positivity



/-- Energy, the connected kernel, positive semidefiniteness, exact similarity,
and actual-carrier eigenvector transport at all positive real weights. -/
theorem quotient_geometry (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    ((∀ z : Fin 6 → ℝ,
      dotProduct (fun i => weights a b c i * z i) (quotient a b c *ᵥ z) =
        a*b*(z 0-z 1)^2 + a*c*(z 0-z 2)^2 + b*c*(z 1-z 2)^2 +
        a*b*c*((z 0-z 5)^2+(z 1-z 4)^2+(z 2-z 3)^2)) ∧
    (∀ z, quotient a b c *ᵥ z = 0 ↔ ∃ t, z = fun _ => t) ∧
    quotient a b c *ᵥ (fun _ => (1 : ℝ)) = 0 ∧
    vecMul (weights a b c) (quotient a b c) = 0) ∧
    (symmetric a b c).PosSemidef ∧
    (symmetric a b c = diagonal (rootWeights a b c) *
      (quotient a b c).submatrix supportPermutation supportPermutation *
        diagonal (fun i => (rootWeights a b c i)⁻¹)) ∧
    (∀ e : ℝ, ∀ z : Fin 6 → ℝ, z ≠ 0 → symmetric a b c *ᵥ z = e • z →
      toQuotientVector a b c z ≠ 0 ∧
        quotient a b c *ᵥ toQuotientVector a b c z = e • toQuotientVector a b c z) := by
  exact ⟨weighted_geometry a b c ha hb hc, symmetric_psd a b c ha hb hc,
    diagonal_similarity a b c ha hb hc, eigenvector_transport a b c ha hb hc⟩

private lemma balanced_tendsto : Tendsto balancedLow atTop (𝓝 3) := by
  have hdiv : Tendsto (fun m : ℝ => 12/(m+4)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right atTop 4 tendsto_id)
  have hlower : Tendsto (fun m : ℝ => 3*m/(m+4)) atTop (𝓝 3) := by
    have h : Tendsto (fun m : ℝ => 3-12/(m+4)) atTop (𝓝 (3-0)) :=
      tendsto_const_nhds.sub hdiv
    simp only [sub_zero] at h
    apply h.congr'
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with m hm
    field_simp
    <;> ring
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower tendsto_const_nhds
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with m hm
    exact (balanced_scalar m hm).2.2.2.1.le
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with m hm
    exact (balanced_scalar m hm).2.2.1.le

/-- The balanced formula, strict bounds, complete factorization and sharp
uniform threshold, including the positive integer sequence. -/
theorem balanced_sharp_threshold :
    (∀ m : ℝ, 1 ≤ m →
      (∃ z : Fin 6 → ℝ, z ≠ 0 ∧ quotient m m m *ᵥ z = balancedLow m • z) ∧
      0 < balancedLow m ∧ balancedLow m < m ∧
      3*m/(m+4) < balancedLow m ∧ balancedLow m < 3 ∧
      balancedLow m = 6*m/(m+4+Real.sqrt ((m+4)^2-12)) ∧
      (∀ e : ℝ, 0 < e → ∀ z : Fin 6 → ℝ, z ≠ 0 →
        quotient m m m *ᵥ z = e • z → balancedLow m ≤ e) ∧
      (∀ x : ℝ, (x • (1 : Matrix (Fin 6) (Fin 6) ℝ) - quotient m m m).det =
        x*(x-m^2-m)*(x^2-(m^2+4*m)*x+3*m^2)^2) ∧
      balancedLow m < m^2+m ∧
      m^2+m < (m^2+4*m+m*Real.sqrt ((m+4)^2-12))/2) ∧
    Tendsto balancedLow atTop (𝓝 3) ∧
    Tendsto (fun n : ℕ => balancedLow (n : ℝ)) atTop (𝓝 3) ∧
    (∀ K : ℝ, K < 3 → ∃ n : ℕ, 1 ≤ n ∧ K < balancedLow n ∧
      ∃ z : Fin 6 → ℝ, z ≠ 0 ∧ quotient n n n *ᵥ z = balancedLow n • z) := by
  have hnat : Tendsto (fun n : ℕ => balancedLow (n : ℝ)) atTop (𝓝 3) :=
    balanced_tendsto.comp tendsto_natCast_atTop_atTop
  refine ⟨balanced_smallest, balanced_tendsto, hnat, ?_⟩
  intro K hK
  obtain ⟨n,hn,hKn⟩ := ((eventually_ge_atTop (1 : ℕ)).and
    (hnat.eventually (lt_mem_nhds hK))).exists
  exact ⟨n,hn,hKn,(balanced_smallest n (by exact_mod_cast hn)).1⟩

/-- A concrete two-dimensional negative plane when the second weight is at most three. -/
theorem small_second_negative_plane (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : a ≤ b) (hb3 : b ≤ 3) :
    ∃ t : ℝ, Function.Injective (fun u : Fin 2 → ℝ =>
        (![u 0,u 1,0,t*u 0,t*u 1,0] : Fin 6 → ℝ)) ∧
      ∀ u : Fin 2 → ℝ, u ≠ 0 →
        dotProduct (![u 0,u 1,0,t*u 0,t*u 1,0] : Fin 6 → ℝ)
          ((symmetric a b c - (3 : ℝ) • 1) *ᵥ ![u 0,u 1,0,t*u 0,t*u 1,0]) < 0 := by
  let p := Real.sqrt a * Real.sqrt b * Real.sqrt c
  let A := b+c+b*c
  let B := a+c+a*c
  let r := Real.sqrt a * Real.sqrt b
  let H := A+B+r+1
  let t := H/p
  have hp : 0 < p := by dsimp [p]; positivity
  have hpt : p*t = H := by dsimp [t]; field_simp
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hr : 0 ≤ r := by dsimp [r]; positivity
  refine ⟨t,?_,?_⟩
  · intro u v huv
    ext i
    fin_cases i
    · exact congrFun huv 0
    · exact congrFun huv 1
  · intro u hu
    have hu2 : 0 < (u 0)^2+(u 1)^2 := by
      by_contra! hle
      have h0 : u 0 = 0 := by nlinarith only [hle, sq_nonneg (u 1)]
      have h1 : u 1 = 0 := by nlinarith only [hle, sq_nonneg (u 0)]
      apply hu
      ext i
      fin_cases i <;> assumption
    have hd0 : (a-3)*(t*u 0)^2 ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith only [hab,hb3]) (sq_nonneg _)
    have hd1 : (b-3)*(t*u 1)^2 ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith only [hb3]) (sq_nonneg _)
    have hcross : -2*r*u 0*u 1 ≤ r*((u 0)^2+(u 1)^2) := by
      nlinarith only [mul_nonneg hr (sq_nonneg (u 0+u 1))]
    have hform : dotProduct (![u 0,u 1,0,t*u 0,t*u 1,0] : Fin 6 → ℝ)
        ((symmetric a b c - (3 : ℝ) • 1) *ᵥ ![u 0,u 1,0,t*u 0,t*u 1,0]) =
      (A-3)*(u 0)^2+(B-3)*(u 1)^2-2*r*u 0*u 1 -
        2*(p*t)*((u 0)^2+(u 1)^2)+(a-3)*(t*u 0)^2+(b-3)*(t*u 1)^2 := by
      simp [dotProduct, mulVec, symmetric, Fin.sum_univ_succ, Matrix.one_apply,
        Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, A,B,r,p]
      <;> ring
    rw [hform,hpt]
    dsimp [H]
    nlinarith only [hd0,hd1,hcross,hu2,
      mul_nonneg hA (sq_nonneg (u 0)),mul_nonneg hA (sq_nonneg (u 1)),
      mul_nonneg hB (sq_nonneg (u 0)),mul_nonneg hB (sq_nonneg (u 1)),
      mul_nonneg hr (sq_nonneg (u 0)),mul_nonneg hr (sq_nonneg (u 1))]


private lemma shift_form (a b c x : ℝ) (z : Fin 6 → ℝ) :
    dotProduct z ((symmetric a b c - x • 1) *ᵥ z) =
      (b+c+b*c-x)*(z 0)^2 + (a+c+a*c-x)*(z 1)^2 +
      (a+b+a*b-x)*(z 2)^2 -
      2*(Real.sqrt a*Real.sqrt b*z 0*z 1 + Real.sqrt a*Real.sqrt c*z 0*z 2 +
        Real.sqrt b*Real.sqrt c*z 1*z 2) -
      2*(Real.sqrt a*Real.sqrt b*Real.sqrt c)*(z 0*z 3+z 1*z 4+z 2*z 5) +
      (a-x)*(z 3)^2+(b-x)*(z 4)^2+(c-x)*(z 5)^2 := by
  simp [dotProduct,mulVec,symmetric,Fin.sum_univ_succ,Matrix.one_apply,
    Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul]
  <;> ring

private lemma transition_plane (a b c : ℝ) (ha : 0 < a) (ha3 : a ≤ 3)
    (hb3 : 3 < b) (hbc : b ≤ c) :
    ∃ B : Matrix (Fin 6) (Fin 2) ℝ, Function.Injective (B *ᵥ ·) ∧
      ∀ u : Fin 2 → ℝ, u ≠ 0 →
        dotProduct (B *ᵥ u) ((symmetric a b c - (3 : ℝ) • 1) *ᵥ (B *ᵥ u)) < 0 := by
  have hb : 0 < b := lt_trans (by norm_num) hb3
  have hc3 : 3 < c := hb3.trans_le hbc
  have hc : 0 < c := lt_trans (by norm_num) hc3
  let p := Real.sqrt a*Real.sqrt b*Real.sqrt c
  let M := b*c+b+c-3
  let r := -Real.sqrt a*(b+c)
  let q := (a-3)*(b+c)-3*a*b*c*(1/(b-3)+1/(c-3))
  have hp : 0 < p := by dsimp [p]; positivity
  have hM : 0 < M := by dsimp [M]; nlinarith only [mul_pos hb hc,hb3,hc3]
  have hq : q < 0 := by
    have hfirst : (a-3)*(b+c) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg
      (sub_nonpos.mpr ha3) (by positivity)
    have hlast : 0 < 3*a*b*c*(1/(b-3)+1/(c-3)) := by positivity
    dsimp [q]
    linarith only [hfirst,hlast]
  have hp2 : p^2 = a*b*c := by
    dsimp [p]
    calc
      _ = (Real.sqrt a)^2*(Real.sqrt b)^2*(Real.sqrt c)^2 := by ring
      _ = a*b*c := by rw [Real.sq_sqrt ha.le,Real.sq_sqrt hb.le,Real.sq_sqrt hc.le]
  let B : Matrix (Fin 6) (Fin 2) ℝ :=
    !![p/M,-r/M; 0,Real.sqrt b; 0,Real.sqrt c; 1,0;
       0,p*Real.sqrt b/(b-3); 0,p*Real.sqrt c/(c-3)]
  have hBu (u : Fin 2 → ℝ) : B *ᵥ u =
      ![(p*u 0-r*u 1)/M,Real.sqrt b*u 1,Real.sqrt c*u 1,u 0,
        p*Real.sqrt b*u 1/(b-3),p*Real.sqrt c*u 1/(c-3)] := by
    ext i
    fin_cases i <;> simp [B,mulVec,dotProduct,Fin.sum_univ_succ] <;> ring
  have hcompression (x y v : ℝ) :
      dotProduct (![x,Real.sqrt b*v,Real.sqrt c*v,y,
        p*Real.sqrt b*v/(b-3),p*Real.sqrt c*v/(c-3)] : Fin 6 → ℝ)
        ((symmetric a b c-(3 : ℝ) • 1) *ᵥ
          ![x,Real.sqrt b*v,Real.sqrt c*v,y,
            p*Real.sqrt b*v/(b-3),p*Real.sqrt c*v/(c-3)]) =
      M*x^2-2*p*x*y+2*r*x*v+(a-3)*y^2+q*v^2 := by
    rw [shift_form]
    simp only [Matrix.cons_val_zero,Matrix.cons_val_succ,Fin.reduceFinMk]
    dsimp [M,p,r,q]
    generalize hdb : b-3 = db
    generalize hdc : c-3 = dc
    have hdb0 : db ≠ 0 := by rw [← hdb]; exact (sub_pos.mpr hb3).ne'
    have hdc0 : dc ≠ 0 := by rw [← hdc]; exact (sub_pos.mpr hc3).ne'
    field_simp [hdb0,hdc0]
    subst db
    subst dc
    ring_nf
    simp only [Real.sq_sqrt ha.le,Real.sq_sqrt hb.le,Real.sq_sqrt hc.le,
      show (Real.sqrt b)^4 = b^2 by rw [show (4 : ℕ) = 2*2 from rfl,pow_mul,Real.sq_sqrt hb.le],
      show (Real.sqrt c)^4 = c^2 by rw [show (4 : ℕ) = 2*2 from rfl,pow_mul,Real.sq_sqrt hc.le]]
    <;> ring
  refine ⟨B,?_,?_⟩
  · intro u v huv
    change B *ᵥ u = B *ᵥ v at huv
    rw [hBu,hBu] at huv
    ext i
    fin_cases i
    · exact congrFun huv 3
    · have h := congrFun huv 1
      exact mul_left_cancel₀ (Real.sqrt_pos.2 hb).ne' h
  · intro u hu
    have hf : dotProduct (B *ᵥ u) ((symmetric a b c - (3 : ℝ) • 1) *ᵥ (B *ᵥ u)) =
        (a-3)*(u 0)^2+q*(u 1)^2-(p*u 0-r*u 1)^2/M := by
      rw [hBu,hcompression]
      have hcomplete : M*((p*u 0-r*u 1)/M)^2-
          2*(p*u 0-r*u 1)*((p*u 0-r*u 1)/M) = -(p*u 0-r*u 1)^2/M := by
        field_simp [hM.ne']
        <;> ring
      linear_combination hcomplete
    rw [hf]
    have h0 : (a-3)*(u 0)^2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg
      (sub_nonpos.mpr ha3) (sq_nonneg _)
    have h1 : q*(u 1)^2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hq.le (sq_nonneg _)
    have h2 : 0 ≤ (p*u 0-r*u 1)^2/M := div_nonneg (sq_nonneg _) hM.le
    by_cases hv : u 1 = 0
    · have hu0 : u 0 ≠ 0 := by
        intro h
        apply hu
        ext i
        fin_cases i <;> assumption
      have hstrict : 0 < (p*u 0-r*u 1)^2/M := by
        rw [hv,mul_zero,sub_zero]
        exact div_pos (sq_pos_of_ne_zero (mul_ne_zero hp.ne' hu0)) hM
      linarith only [h0,h1,hstrict]
    · have hstrict : q*(u 1)^2 < 0 := mul_neg_of_neg_of_pos hq (sq_pos_of_ne_zero hv)
      linarith only [h0,hstrict,h2]

private lemma scalar_completion (d p u y : ℝ) (hd : d ≠ 0) :
    d*y^2-2*p*u*y = d*(y-p*u/d)^2-p^2*u^2/d := by
  field_simp
  <;> ring

private lemma schur_diagonal (t r q x : ℝ) (ht : t ≠ 0) (htx : t-x ≠ 0) :
    r+q+r*q-x-t*r*q/(t-x) =
      (t+r+q)-x-x*(t*r*q)/(t*(t-x))-t := by
  field_simp
  <;> ring

/-- The exact Schur quadratic decomposition. The change of paired coordinates
is a translation with the displayed singleton coordinates fixed. -/
private lemma schur_form (a b c x : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hax : x < a) (hbx : x < b) (hcx : x < c) (z : Fin 6 → ℝ) :
    let p := Real.sqrt a*Real.sqrt b*Real.sqrt c
    let P := a*b*c
    let s := a+b+c
    dotProduct z ((symmetric a b c - x • 1) *ᵥ z) =
      (a-x)*(z 3-p*z 0/(a-x))^2 +
      (b-x)*(z 4-p*z 1/(b-x))^2 +
      (c-x)*(z 5-p*z 2/(c-x))^2 +
      (s-x-x*P/(a*(a-x)))*(z 0)^2 +
      (s-x-x*P/(b*(b-x)))*(z 1)^2 +
      (s-x-x*P/(c*(c-x)))*(z 2)^2 -
      (Real.sqrt a*z 0+Real.sqrt b*z 1+Real.sqrt c*z 2)^2 := by
  dsimp only
  let p := Real.sqrt a*Real.sqrt b*Real.sqrt c
  have hp : p^2 = a*b*c := by
    dsimp [p]
    calc
      _ = (Real.sqrt a)^2*(Real.sqrt b)^2*(Real.sqrt c)^2 := by ring
      _ = a*b*c := by rw [Real.sq_sqrt ha.le,Real.sq_sqrt hb.le,Real.sq_sqrt hc.le]
  have h0 := scalar_completion (a-x) p (z 0) (z 3) (sub_pos.mpr hax).ne'
  have h1 := scalar_completion (b-x) p (z 1) (z 4) (sub_pos.mpr hbx).ne'
  have h2 := scalar_completion (c-x) p (z 2) (z 5) (sub_pos.mpr hcx).ne'
  rw [hp] at h0 h1 h2
  have ha' := schur_diagonal a b c x ha.ne' (sub_pos.mpr hax).ne'
  have hb' := schur_diagonal b a c x hb.ne' (sub_pos.mpr hbx).ne'
  have hc' := schur_diagonal c a b x hc.ne' (sub_pos.mpr hcx).ne'
  have hs : (Real.sqrt a*z 0+Real.sqrt b*z 1+Real.sqrt c*z 2)^2 =
      a*(z 0)^2+b*(z 1)^2+c*(z 2)^2+
      2*(Real.sqrt a*Real.sqrt b*z 0*z 1+Real.sqrt a*Real.sqrt c*z 0*z 2+
        Real.sqrt b*Real.sqrt c*z 1*z 2) := by
    ring_nf
    simp [Real.sq_sqrt ha.le,Real.sq_sqrt hb.le,Real.sq_sqrt hc.le]
    <;> ring
  rw [shift_form,hs]
  dsimp [p] at h0 h1 h2
  linear_combination h0+h1+h2+(z 0)^2*ha'+(z 1)^2*hb'+(z 2)^2*hc'

private lemma large_first_plane (a b c : ℝ) (ha3 : 3 < a) (hab : a ≤ b) (hbc : b ≤ c) :
    ∃ B : Matrix (Fin 6) (Fin 2) ℝ, Function.Injective (B *ᵥ ·) ∧
      ∀ u : Fin 2 → ℝ, u ≠ 0 →
        dotProduct (B *ᵥ u) ((symmetric a b c - (3 : ℝ) • 1) *ᵥ (B *ᵥ u)) < 0 := by
  have hb3 := ha3.trans_le hab
  have hc3 := hb3.trans_le hbc
  have ha : 0 < a := lt_trans (by norm_num) ha3
  have hb : 0 < b := ha.trans_le hab
  have hc : 0 < c := hb.trans_le hbc
  let p := Real.sqrt a*Real.sqrt b*Real.sqrt c
  let B : Matrix (Fin 6) (Fin 2) ℝ :=
    !![1,0; 0,Real.sqrt b; 0,Real.sqrt c; p/(a-3),0;
       0,p*Real.sqrt b/(b-3); 0,p*Real.sqrt c/(c-3)]
  have hBu (u : Fin 2 → ℝ) : B *ᵥ u =
      ![u 0,Real.sqrt b*u 1,Real.sqrt c*u 1,p*u 0/(a-3),
        p*Real.sqrt b*u 1/(b-3),p*Real.sqrt c*u 1/(c-3)] := by
    ext i
    fin_cases i <;> simp [B,mulVec,dotProduct,Fin.sum_univ_succ] <;> ring
  refine ⟨B,?_,?_⟩
  · intro u v huv
    change B *ᵥ u = B *ᵥ v at huv
    rw [hBu,hBu] at huv
    ext i
    fin_cases i
    · exact congrFun huv 0
    · exact mul_left_cancel₀ (Real.sqrt_pos.2 hb).ne' (congrFun huv 1)
  · intro u hu
    have hf : dotProduct (B *ᵥ u) ((symmetric a b c - (3 : ℝ) • 1) *ᵥ (B *ᵥ u)) =
        -(b+c)/2*(u 0+2*Real.sqrt a*u 1)^2 -
        3/(2*a)*(2*b*c-a*(b+c))*(u 0)^2 -
        (3+9*b*c/(a*(a-3)))*(u 0)^2 -
        (3*(b+c)+9*a*c/(b-3)+9*a*b/(c-3))*(u 1)^2 := by
      rw [hBu,schur_form a b c 3 ha hb hc ha3 hb3 hc3]
      simp only [Matrix.cons_val_zero,Matrix.cons_val_succ,Fin.reduceFinMk]
      simp only [mul_assoc,sub_self,zero_pow,mul_zero,zero_add]
      dsimp [p]
      field_simp [ha.ne', (sub_pos.mpr ha3).ne', (sub_pos.mpr hb3).ne',
        (sub_pos.mpr hc3).ne']
      ring_nf
      simp [Real.sq_sqrt ha.le,Real.sq_sqrt hb.le,Real.sq_sqrt hc.le,
        show (Real.sqrt a)^4 = a^2 by rw [show (4 : ℕ) = 2*2 from rfl,pow_mul,Real.sq_sqrt ha.le],
        show (Real.sqrt b)^4 = b^2 by rw [show (4 : ℕ) = 2*2 from rfl,pow_mul,Real.sq_sqrt hb.le],
        show (Real.sqrt c)^4 = c^2 by rw [show (4 : ℕ) = 2*2 from rfl,pow_mul,Real.sq_sqrt hc.le]]
      <;> ring
    rw [hf]
    have hd : 0 ≤ 2*b*c-a*(b+c) := by
      nlinarith only [mul_le_mul_of_nonneg_right hab hc.le,
        mul_le_mul_of_nonneg_right (hab.trans hbc) hb.le]
    have h0 : 0 ≤ (b+c)/2*(u 0+2*Real.sqrt a*u 1)^2 := by positivity
    have h1 : 0 ≤ 3/(2*a)*(2*b*c-a*(b+c))*(u 0)^2 := by positivity
    have hca : 0 < 3+9*b*c/(a*(a-3)) := by positivity
    have hcb : 0 < 3*(b+c)+9*a*c/(b-3)+9*a*b/(c-3) := by positivity
    have h2 : 0 ≤ (3+9*b*c/(a*(a-3)))*(u 0)^2 := by positivity
    have h3 : 0 ≤ (3*(b+c)+9*a*c/(b-3)+9*a*b/(c-3))*(u 1)^2 := by positivity
    by_cases hx : u 0 = 0
    · have hy : u 1 ≠ 0 := by
        intro h
        apply hu
        ext i
        fin_cases i <;> assumption
      have hstrict := mul_pos hcb (sq_pos_of_ne_zero hy)
      nlinarith only [h0,h1,h2,hstrict]
    · have hstrict := mul_pos hca (sq_pos_of_ne_zero hx)
      nlinarith only [h0,h1,h3,hstrict]

private lemma plane_meets_kernel_orthogonal (B : Matrix (Fin 6) (Fin 2) ℝ)
    (k : Fin 6 → ℝ) :
    ∃ u : Fin 2 → ℝ, u ≠ 0 ∧ dotProduct k (B *ᵥ u) = 0 := by
  let d : Fin 2 → ℝ := fun j => dotProduct k (fun i => B i j)
  have hf (u : Fin 2 → ℝ) : dotProduct k (B *ᵥ u) = d 0*u 0+d 1*u 1 := by
    simp [d,dotProduct,mulVec,Fin.sum_univ_succ]
    <;> ring
  by_cases h0 : d 0 = 0
  · refine ⟨![1,0],?_,?_⟩
    · intro h; have := congrFun h 0; norm_num at this
    · rw [hf]; simp [h0]
  · refine ⟨![d 1,-d 0],?_,?_⟩
    · intro h; have hh := congrFun h 1; simp at hh; exact h0 hh
    · rw [hf]; simp; ring

private lemma low_eigenvalue_of_plane (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (B : Matrix (Fin 6) (Fin 2) ℝ)
    (hneg : ∀ u : Fin 2 → ℝ, u ≠ 0 →
      dotProduct (B *ᵥ u) ((symmetric a b c - (3 : ℝ) • 1) *ᵥ (B *ᵥ u)) < 0) :
    ∃ e : ℝ, 0 < e ∧ e < 3 ∧ ∃ z : Fin 6 → ℝ, z ≠ 0 ∧ quotient a b c *ᵥ z = e • z := by
  classical
  let S := symmetric a b c
  have hS : S.IsHermitian := symmetric_hermitian a b c
  have hg := quotient_geometry a b c ha hb hc
  have hPSD : S.PosSemidef := hg.2.1
  suffices hex : ∃ i : Fin 6, 0 < hS.eigenvalues i ∧ hS.eigenvalues i < 3 by
    obtain ⟨i,hi,hlt⟩ := hex
    have hw : (⇑(hS.eigenvectorBasis i) : Fin 6 → ℝ) ≠ 0 :=
      (WithLp.ofLp_eq_zero 2).ne.2 (hS.eigenvectorBasis.orthonormal.ne_zero i)
    exact ⟨hS.eigenvalues i,hi,hlt,toQuotientVector a b c _,
      hg.2.2.2 _ _ hw (hS.mulVec_eigenvectorBasis i)⟩
  by_contra! hno
  obtain ⟨u,hu,horth⟩ := plane_meets_kernel_orthogonal B (rootWeights a b c)
  let z := B *ᵥ u
  let U : Matrix (Fin 6) (Fin 6) ℝ := hS.eigenvectorUnitary
  let d := star U *ᵥ z
  have hd (i : Fin 6) (hi : hS.eigenvalues i = 0) : d i = 0 := by
    let w : Fin 6 → ℝ := ⇑(hS.eigenvectorBasis i)
    have hw : w ≠ 0 := (WithLp.ofLp_eq_zero 2).ne.2 (hS.eigenvectorBasis.orthonormal.ne_zero i)
    have he : symmetric a b c *ᵥ w = (0 : ℝ) • w := by
      simpa only [hi] using hS.mulVec_eigenvectorBasis i
    have hC := (hg.2.2.2 0 w hw he).2
    simp only [zero_smul] at hC
    obtain ⟨t,ht⟩ := (hg.1.2.1 _).mp hC
    have hwk : ∀ j, w j = t*rootWeights a b c j := by
      intro j
      have hh := congrFun ht (supportPermutation j)
      change w (supportPermutation.symm (supportPermutation j)) /
        rootWeights a b c (supportPermutation.symm (supportPermutation j)) = t at hh
      simp only [Equiv.symm_apply_apply] at hh
      exact (div_eq_iff (rootWeights_pos a b c ha hb hc j).ne').mp hh
    have heq : d i = dotProduct w z := by
      simp [d,U,mulVec,dotProduct,Matrix.star_apply,Matrix.IsHermitian.eigenvectorUnitary_apply,w]
    rw [heq]
    change (∑ j, w j*z j) = 0
    simp_rw [hwk,mul_assoc]
    rw [← mul_sum]
    change t * dotProduct (rootWeights a b c) z = 0
    rw [horth,mul_zero]
  have hform : dotProduct z (S *ᵥ z) = ∑ i, hS.eigenvalues i*(d i)^2 := by
    have hh := RHLinalg.hermForm_specMap hS id z
    rw [RHLinalg.specMap_id] at hh
    simpa [d,U,Real.norm_eq_abs,sq_abs] using hh
  have hnorm : dotProduct z z = ∑ i, (d i)^2 := by
    have hh := RHLinalg.sum_normSq_unitary_mulVec hS z
    simpa [d,U,dotProduct,Real.norm_eq_abs,sq_abs,pow_two] using hh.symm
  have hbound : 3*dotProduct z z ≤ dotProduct z (S *ᵥ z) := by
    rw [hform,hnorm,mul_sum]
    apply sum_le_sum
    intro i hi
    by_cases he : hS.eigenvalues i = 0
    · rw [hd i he]; simp
    · have hpos : 0 < hS.eigenvalues i := (hPSD.eigenvalues_nonneg i).lt_of_ne' he
      exact mul_le_mul_of_nonneg_right (hno i hpos) (sq_nonneg _)
  have hn := hneg u hu
  change dotProduct z ((S-(3 : ℝ) • 1) *ᵥ z) < 0 at hn
  rw [Matrix.sub_mulVec,Matrix.smul_mulVec,Matrix.one_mulVec,dotProduct_sub,dotProduct_smul] at hn
  simp only [smul_eq_mul] at hn
  linarith only [hbound,hn]

/-- Every ordered positive real triple has an actual nonzero real quotient
 eigenvector with eigenvalue strictly between zero and three. -/
theorem positive_real_low_eigenvalue (a b c : ℝ) (ha : 0 < a) (hab : a ≤ b) (hbc : b ≤ c) :
    ∃ e : ℝ, 0 < e ∧ e < 3 ∧ ∃ z : Fin 6 → ℝ, z ≠ 0 ∧ quotient a b c *ᵥ z = e • z := by
  by_cases hbal : a = b ∧ b = c ∧ 1 ≤ a
  · rcases hbal with ⟨habEq,hbcEq,ha1⟩
    have h := balanced_sharp_threshold.1 a ha1
    have heq : quotient a b c = quotient a a a := by
      rw [← hbcEq, ← habEq]
    rw [heq]
    exact ⟨balancedLow a,h.2.1,h.2.2.2.2.1,h.1⟩
  · have hb := ha.trans_le hab
    have hc := hb.trans_le hbc
    obtain ⟨B,hB,hneg⟩ : ∃ B : Matrix (Fin 6) (Fin 2) ℝ,
        Function.Injective (B *ᵥ ·) ∧ ∀ u : Fin 2 → ℝ, u ≠ 0 →
          dotProduct (B *ᵥ u) ((symmetric a b c-(3 : ℝ) • 1) *ᵥ (B *ᵥ u)) < 0 := by
      by_cases hb3 : b ≤ 3
      · obtain ⟨t,hinj,hneg⟩ := small_second_negative_plane a b c ha hb hc hab hb3
        let B : Matrix (Fin 6) (Fin 2) ℝ := !![1,0;0,1;0,0;t,0;0,t;0,0]
        have heq : (B *ᵥ ·) = fun u : Fin 2 → ℝ =>
            (![u 0,u 1,0,t*u 0,t*u 1,0] : Fin 6 → ℝ) := by
          funext u
          ext i
          fin_cases i <;> simp [B,mulVec,dotProduct,Fin.sum_univ_succ]
        exact ⟨B,by rw [heq]; exact hinj,by
          intro u hu
          rw [congrFun heq u]
          exact hneg u hu⟩
      · by_cases ha3 : a ≤ 3
        · exact transition_plane a b c ha ha3 (lt_of_not_ge hb3) hbc
        · exact large_first_plane a b c (lt_of_not_ge ha3) hab hbc
    exact low_eigenvalue_of_plane a b c ha hb hc B hneg


end D5.S3.Combinatorics.SpectralGraph.SixSupportLaplacianLowRoot
