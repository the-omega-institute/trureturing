/- GID: D5/S3/Quantum/Semigroups/WuRepeatedMiddleCubic
   generality: I
   mirror-B: D5/B/S3/Quantum/Semigroups/WuRepeatedMiddleCubic
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The cubic deficit for Wu's two literal signed modes with a repeated middle spectrum. -/

import D5.S3.Quantum.Semigroups.TwistedTwoModeOUComparison
import Mathlib.Analysis.MeanInequalities

/-! The repeated-middle reduction for Wu v1, Remark 3.15 (3.54)–(3.55).
The spectral order is (m,n,n,1), and a jump entry has target row and source column. -/

noncomputable section

open Matrix Kronecker
open scoped BigOperators Matrix
open D5.S3.Quantum.Semigroups.TwistedTwoModeOUComparison (modeJump)

namespace D5.S3.Quantum.Semigroups.WuRepeatedMiddleCubic

abbrev Occupation := Fin 2 × Fin 2
abbrev Frame := Matrix Occupation (Fin 4) ℂ

/-- Sum of the squared amplitudes of the two literal signed CAR jumps. -/
def weight (U : Frame) (i j : Fin 4) : ℝ :=
  ∑ k : Fin 2, Complex.normSq ((Uᴴ * modeJump k * U) i j)

private def mass (U : Frame) (i : Fin 4) (a b : Fin 2) : ℝ :=
  Complex.normSq (U (a,b) i)

private def evenMass (U : Frame) (i : Fin 4) : ℝ := mass U i 0 0 + mass U i 1 1
private def oddMass (U : Frame) (i : Fin 4) : ℝ := mass U i 0 1 + mass U i 1 0

/-- Diagonal of the occupation imbalance diag(1,0,0,-1) in the frame. -/
def imbalance (U : Frame) (i : Fin 4) : ℝ := mass U i 0 0 - mass U i 1 1

private theorem jump_zero :
    modeJump 0 = (!![0,1;0,0] : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ 1 := rfl

private theorem jump_one :
    modeJump 1 = diagonal (![-1,1] : Fin 2 → ℂ) ⊗ₖ
      (!![0,1;0,0] : Matrix (Fin 2) (Fin 2) ℂ) := rfl

private theorem normSq_mul_conj (z : ℂ) : (z * star z).re = Complex.normSq z := by
  rw [Complex.star_def, Complex.mul_conj', ← Complex.ofReal_pow, Complex.ofReal_re,
    Complex.normSq_eq_norm_sq]

private theorem normSq_conj_mul (z : ℂ) : (star z * z).re = Complex.normSq z := by
  rw [mul_comm, normSq_mul_conj]

private theorem column_mass (U : Frame) (hU : Uᴴ * U = 1) (i : Fin 4) :
    evenMass U i + oddMass U i = 1 := by
  have h := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ => (M i i).re) hU
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
    Fin.sum_univ_two, Complex.add_re, normSq_conj_mul, Matrix.one_apply_eq, Complex.one_re] at h
  unfold evenMass oddMass mass
  linarith

private theorem jump_diagonal (U : Frame) (i : Fin 4) :
    weight U i i = evenMass U i * oddMass U i := by
  simp [weight, Fin.sum_univ_two, jump_zero, jump_one, Matrix.mul_apply,
    Fintype.sum_prod_type, Matrix.conjTranspose_apply, Matrix.kroneckerMap_apply,
    evenMass, oddMass, mass,
    Complex.normSq_apply, Complex.mul_re, Complex.mul_im, Complex.add_re,
    Complex.add_im, Complex.conj_re, Complex.conj_im]
  ring

private def occupationSign (i : Occupation) : ℂ :=
  if i = (0,0) then 1 else if i = (1,1) then -1 else 0

private theorem incoming :
    ∑ k : Fin 2, modeJump k * (modeJump k)ᴴ = 1 + diagonal occupationSign := by
  ext ⟨a,b⟩ ⟨c,d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    norm_num [jump_zero, jump_one, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.kroneckerMap_apply, Matrix.one_apply, Fintype.sum_prod_type,
      Fin.sum_univ_two, occupationSign]

private theorem outgoing :
    ∑ k : Fin 2, (modeJump k)ᴴ * modeJump k = 1 - diagonal occupationSign := by
  ext ⟨a,b⟩ ⟨c,d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    norm_num [jump_zero, jump_one, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.kroneckerMap_apply, Matrix.one_apply, Fintype.sum_prod_type,
      Fin.sum_univ_two, occupationSign]

private theorem imbalance_conjugation (U : Frame) (i : Fin 4) :
    ((Uᴴ * diagonal occupationSign * U) i i).re = imbalance U i := by
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
    Fin.sum_univ_two, occupationSign, Matrix.diagonal_apply,
    imbalance, mass, Complex.normSq_apply, Complex.mul_re, Complex.add_re,
    Complex.conj_re, Complex.conj_im]
  ring

private theorem row_weight (U : Frame) (hU : Uᴴ * U = 1) (hUU : U * Uᴴ = 1) (i : Fin 4) :
    ∑ j, weight U i j = 1 + imbalance U i := by
  have hprod (k : Fin 2) :
      let A := Uᴴ * modeJump k * U
      A * Aᴴ = Uᴴ * (modeJump k * (modeJump k)ᴴ) * U := by
    dsimp
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc U Uᴴ, hUU, Matrix.one_mul]
  unfold weight
  rw [Finset.sum_comm]
  calc
    _ = ∑ k : Fin 2, ((Uᴴ * (modeJump k * (modeJump k)ᴴ) * U) i i).re := by
      apply Finset.sum_congr rfl
      intro k _
      rw [← hprod k]
      let A := Uᴴ * modeJump k * U
      change (∑ j, Complex.normSq (A i j)) = (∑ j, A i j * star (A i j)).re
      simp only [Fin.sum_univ_four, Complex.add_re, normSq_mul_conj]
    _ = _ := by
      have hsum : modeJump 0 * (modeJump 0)ᴴ +
          modeJump 1 * (modeJump 1)ᴴ = 1 + diagonal occupationSign := by
        simpa only [Fin.sum_univ_two] using incoming
      rw [Fin.sum_univ_two, ← Complex.add_re, ← Matrix.add_apply,
        ← Matrix.add_mul, ← Matrix.mul_add, hsum,
        Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hU, Matrix.add_apply,
        Complex.add_re, Matrix.one_apply_eq, Complex.one_re, imbalance_conjugation]

private theorem col_weight (U : Frame) (hU : Uᴴ * U = 1) (hUU : U * Uᴴ = 1) (i : Fin 4) :
    ∑ j, weight U j i = 1 - imbalance U i := by
  have hprod (k : Fin 2) :
      let A := Uᴴ * modeJump k * U
      Aᴴ * A = Uᴴ * ((modeJump k)ᴴ * modeJump k) * U := by
    dsimp
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc U Uᴴ, hUU, Matrix.one_mul]
  unfold weight
  rw [Finset.sum_comm]
  calc
    _ = ∑ k : Fin 2, ((Uᴴ * ((modeJump k)ᴴ * modeJump k) * U) i i).re := by
      apply Finset.sum_congr rfl
      intro k _
      rw [← hprod k]
      let A := Uᴴ * modeJump k * U
      change (∑ j, Complex.normSq (A j i)) = (∑ j, star (A j i) * A j i).re
      simp only [Fin.sum_univ_four, Complex.add_re, normSq_conj_mul]
    _ = _ := by
      have hsum : (modeJump 0)ᴴ * modeJump 0 +
          (modeJump 1)ᴴ * modeJump 1 = 1 - diagonal occupationSign := by
        simpa only [Fin.sum_univ_two] using outgoing
      rw [Fin.sum_univ_two, ← Complex.add_re, ← Matrix.add_apply,
        ← Matrix.add_mul, ← Matrix.mul_add, hsum,
        Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hU, Matrix.sub_apply,
        Complex.sub_re, Matrix.one_apply_eq, Complex.one_re, imbalance_conjugation]

/-- Both directions across the cut isolating column `i`. -/
def singletonMass (U : Frame) (i : Fin 4) : ℝ :=
  (∑ j, weight U i j) + (∑ j, weight U j i) - 2 * weight U i i

private theorem singleton_formula
    (U : Frame) (hU : Uᴴ * U = 1) (hUU : U * Uᴴ = 1) (i : Fin 4) :
    singletonMass U i = (3 + (2 * evenMass U i - 1)^2) / 2 := by
  rw [singletonMass, row_weight U hU hUU, col_weight U hU hUU, jump_diagonal]
  have h := column_mass U hU i
  rw [show oddMass U i = 1 - evenMass U i by linarith]
  ring

/-- The coordinate measured by a singleton cut of signed imbalance `R`. -/
def cutCoordinate (R : ℝ) : ℝ := max 0 (2 * |R| - 1)

private theorem singleton_bounds
    (U : Frame) (hU : Uᴴ * U = 1) (hUU : U * Uᴴ = 1) (i : Fin 4)
    (R : ℝ) (hR : |R| = |imbalance U i|) :
    let u := cutCoordinate R
    0 ≤ u ∧ u ≤ 1 ∧ (3 + u^2) / 2 ≤ singletonMass U i ∧ -(1+u)/2 ≤ R := by
  dsimp only
  have he : 0 ≤ evenMass U i := add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)
  have ho : 0 ≤ oddMass U i := add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)
  have hsum := column_mass U hU i
  have habs : |R| ≤ evenMass U i := by
    rw [hR, imbalance, abs_le]
    unfold evenMass mass
    constructor <;>
      linarith [Complex.normSq_nonneg (U (0,0) i), Complex.normSq_nonneg (U (1,1) i)]
  refine ⟨le_max_left _ _, max_le (by norm_num) (by linarith), ?_, ?_⟩
  · rw [singleton_formula U hU hUU i]
    have hu : cutCoordinate R ≤ |2 * evenMass U i - 1| :=
      max_le (abs_nonneg _) ((by linarith : 2*|R|-1 ≤ 2*evenMass U i-1).trans (le_abs_self _))
    have hs := pow_le_pow_left₀ (le_max_left 0 (2*|R|-1)) hu 2
    change cutCoordinate R ^ 2 ≤ |2 * evenMass U i - 1| ^ 2 at hs
    rw [sq_abs] at hs
    linarith
  · have hu := le_max_right 0 (2 * |R| - 1)
    change 2 * |R| - 1 ≤ cutCoordinate R at hu
    linarith [neg_abs_le R]

/-- Wu's coefficient at exponent three, extended to the tracial temperature. -/
def alpha (r : ℝ) : ℝ :=
  if r = 1 then 1/2 else 3 * (r^2 - 1) / (4 * (r^2+r+1) * Real.log r)

private def gibbsLow (r : ℝ) : ℝ := 1 / (1 + r^3)
private def gibbsHigh (r : ℝ) : ℝ := r^3 * gibbsLow r
private def gamma (r : ℝ) : ℝ := 9 / (4 * (1 + r^3))
private def h (r : ℝ) : ℝ :=
  gamma r * (r-1)^2 * (r+1) + alpha r * Real.log (4 * gibbsLow r * gibbsHigh r)
private def c (r : ℝ) : ℝ := gamma r * r * (r+1) / 2
private def e (r : ℝ) : ℝ := gamma r * r * (r-1) / 6
private def bias (r : ℝ) : ℝ :=
  2 * gamma r * r * (r-1) * (r^2 + 4*r + 1) / (3 * (r^2+r+1))

private def cutA (r v w : ℝ) : ℝ := c r * (w-v)^2 * (w+v)
private def cutB (r v w : ℝ) : ℝ := bias r * (w^3-v^3) + 2 * e r * (w-v)^3
private def kernel (r v w : ℝ) : ℝ :=
  bias r / 2 * (v^3-w^3) + c r * (v-w)^2 * (v+w) + e r * (v-w)^3

private def entropyPair (v w : ℝ) : ℝ :=
  (v^3+w^3) * Real.log ((v^3+w^3)/2) - v^3 * Real.log (v^3) - w^3 * Real.log (w^3)

/-- The cube root of the mass of a two-level block. -/
def blockRoot (v w : ℝ) : ℝ := (v^3+w^3) ^ (1/3 : ℝ)

private theorem blockRoot_cube {v w : ℝ} (hv : 0 ≤ v) (hw : 0 ≤ w) :
    blockRoot v w ^ 3 = v^3+w^3 := by
  unfold blockRoot
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  norm_num

private def total (m n : ℝ) : ℝ := m^3 + n^3 + n^3 + 1

private def entropy (m n : ℝ) : ℝ :=
  total m n * Real.log (total m n / 4) -
    m^3 * Real.log (m^3) - 2 * n^3 * Real.log (n^3)

/-- Exact one-mode cubic deficit with upper-eigenvector Bloch coordinate `z`. -/
def oneModeDeficit (r v w z : ℝ) : ℝ :=
  h r / 2 * (v^3+w^3) + alpha r * entropyPair v w +
    (cutA r v w * (1+z^2) + cutB r v w * z) / 2

private theorem entropy_split {m n : ℝ} (hm : 0 ≤ m) (hn : 0 ≤ n) :
    entropy m n = entropyPair m n + entropyPair n 1 +
      entropyPair (blockRoot m n) (blockRoot n 1) := by
  have htwo : 0 < (2 : ℝ) := by norm_num
  have hfour : 0 < (4 : ℝ) := by norm_num
  have hlog : ∀ s : ℝ, 0 ≤ s →
      s * Real.log (s/2) = s * Real.log s - s * Real.log 2 := by
    intro s hs
    rcases hs.eq_or_lt with hs | hs
    · simp [← hs]
    · rw [Real.log_div hs.ne' htwo.ne']
      ring
  unfold entropy entropyPair total
  rw [blockRoot_cube hm hn, blockRoot_cube hn zero_le_one]
  simp only [one_pow, Real.log_one, mul_zero, sub_zero]
  rw [hlog (m^3+n^3) (by positivity), hlog (n^3+1) (by positivity)]
  rw [show m^3 + n^3 + (n^3+1) = m^3+n^3+n^3+1 by ring]
  rw [hlog _ (by positivity), Real.log_div (by positivity : (m^3+n^3+n^3+1) ≠ 0) hfour.ne',
    show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul htwo.ne' htwo.ne']
  ring

private def levels (m n : ℝ) : Fin 4 → ℝ := ![m,n,n,1]

/-- The centered signed spectral deficit (certificate equation (2)). -/
def centeredDeficit (r : ℝ) (U : Frame) (m n : ℝ) : ℝ :=
  h r * total m n + alpha r * entropy m n +
    ∑ i, ∑ j, weight U i j * kernel r (levels m n i) (levels m n j)

private def crossE (r m n : ℝ) : ℝ := 3 * e r * (n-m) * (1-n) * (1-m)
private def crossZ (r m n : ℝ) : ℝ := c r * (n-m) * (1-n) * (m+2*n+1) - crossE r m n

private theorem frame_split
    (r : ℝ) (U : Frame) (hU : Uᴴ * U = 1) (hUU : U * Uᴴ = 1) (m n : ℝ) :
    (∑ i, ∑ j, weight U i j * kernel r (levels m n i) (levels m n j)) =
      cutA r m n * singletonMass U 0 + cutB r m n * (-imbalance U 0) +
      cutA r n 1 * singletonMass U 3 + cutB r n 1 * imbalance U 3 +
      crossZ r m n * (weight U 3 0 + weight U 0 3) + 2 * crossE r m n * weight U 3 0 := by
  have h0 : (∑ j, weight U j 0) - (∑ j, weight U 0 j) = 2 * (-imbalance U 0) := by
    rw [row_weight U hU hUU, col_weight U hU hUU]
    ring
  have h3 : (∑ j, weight U 3 j) - (∑ j, weight U j 3) = 2 * imbalance U 3 := by
    rw [row_weight U hU hUU, col_weight U hU hUU]
    ring
  simp only [Fin.sum_univ_four] at h0 h3
  have h0' := congrArg (fun v : ℝ => cutB r m n / 2 * v) h0
  have h3' := congrArg (fun v : ℝ => cutB r n 1 / 2 * v) h3
  simp only [cutB] at h0' h3'
  simp [Fin.sum_univ_four, levels, kernel, singletonMass, cutA, cutB, crossZ, crossE]
  linear_combination h0' + h3'

private theorem kernel_order (r v w : ℝ) :
    kernel r v w = cutA r v w - cutB r v w / 2 := by
  unfold kernel cutA cutB
  ring

private theorem kernel_modular (r v w : ℝ) :
    kernel r v w =
      (c r + e r + bias r / 2) * v^3 + (c r - e r - bias r / 2) * w^3 -
      gamma r * r^2 * v^2*w - gamma r * r * v*w^2 := by
  unfold kernel c e
  ring

/-- The Hölder gap multiplying the modular weight `γ r`. -/
def holder21 (m n : ℝ) : ℝ :=
  blockRoot m n * blockRoot n 1 ^ 2 - (m*n^2+n)

/-- The Hölder gap multiplying the modular weight `γ r²`. -/
def holder12 (m n : ℝ) : ℝ :=
  blockRoot m n ^ 2 * blockRoot n 1 - (m^2*n+n^2)

private theorem modular_split {r m n : ℝ} (hm : 0 ≤ m) (hn : 0 ≤ n) :
    kernel r m n + kernel r n 1 - kernel r (blockRoot m n) (blockRoot n 1) =
      gamma r * r * holder21 m n + gamma r * r^2 * holder12 m n := by
  simp only [kernel_modular, holder21, holder12, blockRoot_cube hm hn,
    blockRoot_cube hn zero_le_one]
  ring

private theorem holder_square_left {a b d f : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hd : 0 ≤ d) (hf : 0 ≤ f) :
    a^2*d + b^2*f ≤ blockRoot a b ^ 2 * blockRoot d f := by
  let x : Fin 2 → ℝ := ![a,b]
  let y : Fin 2 → ℝ := ![d,f]
  have hx (i : Fin 2) : 0 ≤ x i := by fin_cases i <;> assumption
  have hy (i : Fin 2) : 0 ≤ y i := by fin_cases i <;> assumption
  have hp : (3/2 : ℝ).HolderConjugate 3 := Real.holderConjugate_iff.mpr
    ⟨by norm_num, by norm_num⟩
  have bound := Real.inner_le_Lp_mul_Lq_of_nonneg Finset.univ
    (f := fun i => x i ^ 2) (g := y) hp (fun i _ => sq_nonneg _) (fun i _ => hy i)
  have hpw (i : Fin 2) : (x i ^ 2) ^ (3/2 : ℝ) = x i ^ 3 := by
    rw [← Real.rpow_natCast_mul (hx i)]
    norm_num
  have hroot : (a^3+b^3) ^ (2/3 : ℝ) = blockRoot a b ^ 2 := by
    unfold blockRoot
    rw [← Real.rpow_mul_natCast (by positivity)]
    congr 1
    norm_num
  simp_rw [hpw, show (3 : ℝ) = (3 : ℕ) by norm_num, Real.rpow_natCast] at bound
  norm_num [x, y, Fin.sum_univ_two] at bound
  rw [hroot] at bound
  simpa [blockRoot] using bound

private theorem holder_gaps {m n : ℝ} (hm : 0 ≤ m) (hn : 0 ≤ n) :
    0 ≤ holder21 m n ∧ 0 ≤ holder12 m n := by
  constructor
  · unfold holder21
    have h := holder_square_left hn zero_le_one hm hn
    nlinarith only [h]
  · unfold holder12
    have h := holder_square_left hm hn hn zero_le_one
    nlinarith only [h]

private def singletonLoss (r v w D R : ℝ) : ℝ :=
  cutA r v w * (D - (3 + cutCoordinate R ^ 2) / 2) +
    cutB r v w * (R + (1 + cutCoordinate R) / 2)

private theorem singleton_split (r v w D R : ℝ) :
    h r / 2 * (v^3+w^3) + alpha r * entropyPair v w + cutA r v w * D + cutB r v w * R =
      oneModeDeficit r v w (-cutCoordinate R) + kernel r v w + singletonLoss r v w D R := by
  rw [kernel_order]
  unfold oneModeDeficit singletonLoss
  ring

/-- The two singleton losses and the two contributions across the outer cuts. -/
def frameRemainder (r : ℝ) (U : Frame) (m n : ℝ) : ℝ :=
  singletonLoss r m n (singletonMass U 0) (-imbalance U 0) +
  singletonLoss r n 1 (singletonMass U 3) (imbalance U 3) +
  crossZ r m n * (weight U 3 0 + weight U 0 3) + 2 * crossE r m n * weight U 3 0

/-- Exact measured-cut decomposition, including the signed outer crossing.
The proof applies to every complex frame and allows either outer increment to be zero. -/
theorem repeated_middle_decomposition
    (r : ℝ) (U : Frame) (hU : Uᴴ * U = 1) (hUU : U * Uᴴ = 1)
    {m n : ℝ} (hm : 0 ≤ m) (hn : 0 ≤ n) :
    centeredDeficit r U m n =
      oneModeDeficit r m n (-cutCoordinate (-imbalance U 0)) +
      oneModeDeficit r n 1 (-cutCoordinate (imbalance U 3)) +
      oneModeDeficit r (blockRoot m n) (blockRoot n 1) (-1) +
      gamma r * r * holder21 m n + gamma r * r^2 * holder12 m n +
      frameRemainder r U m n := by
  rw [centeredDeficit, entropy_split hm hn, frame_split r U hU hUU]
  unfold frameRemainder
  have hlow := singleton_split r m n (singletonMass U 0) (-imbalance U 0)
  have hhigh := singleton_split r n 1 (singletonMass U 3) (imbalance U 3)
  have hbetween : oneModeDeficit r (blockRoot m n) (blockRoot n 1) (-1) =
      h r / 2 * ((m^3+n^3)+(n^3+1)) +
      alpha r * entropyPair (blockRoot m n) (blockRoot n 1) +
      kernel r (blockRoot m n) (blockRoot n 1) := by
    rw [kernel_order, oneModeDeficit, blockRoot_cube hm hn, blockRoot_cube hn zero_le_one]
    ring
  unfold total
  linear_combination hlow + hhigh - hbetween + modular_split (r := r) hm hn

private theorem cut_coefficients {r v w : ℝ} (hr : 1 ≤ r) (hv : 0 ≤ v) (hvw : v ≤ w) :
    0 ≤ cutA r v w ∧ 0 ≤ cutB r v w := by
  have hr0 : 0 ≤ r := zero_le_one.trans hr
  have hrt : 0 ≤ r-1 := sub_nonneg.mpr hr
  have hw := hv.trans hvw
  have hdiff : 0 ≤ w-v := sub_nonneg.mpr hvw
  have hcubes : 0 ≤ w^3-v^3 := sub_nonneg.mpr (pow_le_pow_left₀ hv hvw _)
  constructor <;> simp only [cutA, cutB, c, e, bias, gamma] <;> positivity

private theorem singleton_loss_nonneg {r v w D R : ℝ}
    (hr : 1 ≤ r) (hv : 0 ≤ v) (hvw : v ≤ w)
    (hD : (3 + cutCoordinate R ^ 2) / 2 ≤ D)
    (hR : -(1 + cutCoordinate R) / 2 ≤ R) :
    0 ≤ singletonLoss r v w D R := by
  obtain ⟨hA,hB⟩ := cut_coefficients hr hv hvw
  exact add_nonneg (mul_nonneg hA (by linarith)) (mul_nonneg hB (by linarith))

private theorem remainder_nonneg
    {r : ℝ} (hr : 1 ≤ r) (U : Frame) (hU : Uᴴ * U = 1) (hUU : U * Uᴴ = 1)
    {m n : ℝ} (hm : 0 ≤ m) (hmn : m ≤ n) (hn1 : n ≤ 1) :
    0 ≤ frameRemainder r U m n := by
  have h0 := singleton_bounds U hU hUU 0 (-imbalance U 0) (abs_neg _)
  have h3 := singleton_bounds U hU hUU 3 (imbalance U 3) rfl
  have hr0 : 0 ≤ r := zero_le_one.trans hr
  have hn := hm.trans hmn
  have hd0 := sub_nonneg.mpr hmn
  have hd2 := sub_nonneg.mpr hn1
  have hspan := sub_nonneg.mpr (hmn.trans hn1)
  have hrt := sub_nonneg.mpr hr
  have hγ : 0 ≤ gamma r := by unfold gamma; positivity
  have hE : 0 ≤ crossE r m n := by unfold crossE e; positivity
  have hZ : 0 ≤ crossZ r m n := by
    have he : 0 ≤ e r := by unfold e; positivity
    have hce : 3 * e r ≤ c r := by
      have hid : c r - 3 * e r = gamma r * r := by unfold c e; ring
      linarith [mul_nonneg hγ hr0]
    have hs : 1-m ≤ m+2*n+1 := by linarith
    have hle := mul_le_mul hce hs hspan (he.trans (by linarith : e r ≤ c r))
    have hle' := mul_le_mul_of_nonneg_left hle (mul_nonneg hd0 hd2)
    unfold crossZ crossE
    linarith only [show (n-m)*(1-n)*(3*e r*(1-m)) ≤
        (n-m)*(1-n)*(c r*(m+2*n+1)) from hle']
  have hW (i j) : 0 ≤ weight U i j :=
    Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _
  unfold frameRemainder
  exact add_nonneg (add_nonneg
    (add_nonneg (singleton_loss_nonneg hr hm hmn h0.2.2.1 h0.2.2.2)
      (singleton_loss_nonneg hr hn hn1 h3.2.2.1 h3.2.2.2))
    (mul_nonneg hZ (add_nonneg (hW 3 0) (hW 0 3))))
    (mul_nonneg (mul_nonneg (by norm_num) hE) (hW 3 0))

private def beta (r : ℝ) : ℝ := 3 * Real.log r

private def gibbsOccupation (r : ℝ) (a : Fin 2) : ℝ :=
  ![gibbsLow r, gibbsHigh r] a

private def gibbsLogColumn (r : ℝ) (U : Frame) (i : Fin 4) : ℝ :=
  ∑ o : Occupation, Complex.normSq (U o i) *
    Real.log (gibbsOccupation r o.1 * gibbsOccupation r o.2)

private theorem gibbs_log_column {r : ℝ} (hr : 1 ≤ r)
    (U : Frame) (hU : Uᴴ * U = 1) (i : Fin 4) :
    gibbsLogColumn r U i = Real.log (gibbsLow r * gibbsHigh r) - beta r * imbalance U i := by
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  have ha : gibbsLow r ≠ 0 := by unfold gibbsLow; positivity
  have hb : gibbsHigh r ≠ 0 := by unfold gibbsHigh gibbsLow; positivity
  have hratio : Real.log (gibbsHigh r) = beta r + Real.log (gibbsLow r) := by
    rw [gibbsHigh, Real.log_mul (pow_ne_zero _ hr0.ne') ha, Real.log_pow]
    norm_num [beta]
  have hmass := column_mass U hU i
  simp only [evenMass, oddMass, mass] at hmass
  simp [gibbsLogColumn, gibbsOccupation, Fintype.sum_prod_type, Fin.sum_univ_two,
    Real.log_mul ha ha, Real.log_mul ha hb, Real.log_mul hb ha, Real.log_mul hb hb,
    hratio, imbalance, mass]
  linear_combination (beta r + 2 * Real.log (gibbsLow r)) * hmass

private def energyKernel (r v w : ℝ) : ℝ :=
  gamma r * (r^3*v^3+w^3-r^2*v^2*w-r*v*w^2)

/-- Wu's normalized cubic deficit in the spectral coordinates of the original
energy and relative entropy. The pure energy terms count the incoming and
outgoing mass with weights `γ r³` and `γ`, respectively. -/
def sourceDeficit (r : ℝ) (U : Frame) (m n : ℝ) : ℝ :=
  (∑ i, ∑ j, weight U i j * energyKernel r (levels m n i) (levels m n j)) -
    alpha r * (m^3 * Real.log (m^3) + 2*n^3 * Real.log (n^3) -
      total m n * Real.log (total m n) -
        ∑ i, gibbsLogColumn r U i * levels m n i ^ 3)

private theorem centered_bias {r : ℝ} (hr : 1 ≤ r) :
    bias r + 2 * e r = gamma r * (r^3-1) - alpha r * beta r := by
  by_cases hr1 : r = 1
  · subst r
    norm_num [bias, e, gamma, alpha, beta]
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  have hlog := Real.log_ne_zero_of_pos_of_ne_one hr0 hr1
  have hd1 : (1 + r^3) ≠ 0 := by positivity
  have hd2 : (r^2+r+1) ≠ 0 := by positivity
  simp only [bias, e, gamma, alpha, ite_eq_right hr1, beta]
  field_simp
  ring

private theorem energy_centering {r : ℝ} (hr : 1 ≤ r) (v w W : ℝ) :
    W * energyKernel r v w =
      W * kernel r v w +
        (gamma r * (r-1)^2*(r+1) + alpha r * beta r) / 2 * (W*v^3) +
        (gamma r * (r-1)^2*(r+1) - alpha r * beta r) / 2 * (W*w^3) := by
  rw [kernel_modular]
  unfold energyKernel c
  linear_combination (W * (w^3-v^3) / 2) * centered_bias hr

private theorem source_eq_centered
    {r : ℝ} (hr : 1 ≤ r) (U : Frame) (hU : Uᴴ * U = 1) (hUU : U * Uᴴ = 1)
    {m n : ℝ} (hm : 0 ≤ m) (hn : 0 ≤ n) :
    sourceDeficit r U m n = centeredDeficit r U m n := by
  have hrow : (∑ i, ∑ j, weight U i j * levels m n i ^ 3) =
      ∑ i, (1 + imbalance U i) * levels m n i ^ 3 := by
    simp_rw [← Finset.sum_mul, row_weight U hU hUU]
  have hcol : (∑ i, ∑ j, weight U i j * levels m n j ^ 3) =
      ∑ j, (1 - imbalance U j) * levels m n j ^ 3 := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, col_weight U hU hUU]
  have ht : total m n ≠ 0 := by unfold total; positivity
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  have ha : gibbsLow r ≠ 0 := by unfold gibbsLow; positivity
  have hq : gibbsLow r * gibbsHigh r ≠ 0 :=
    mul_ne_zero ha (mul_ne_zero (pow_ne_zero _ hr0.ne') ha)
  have hlog : Real.log (4 * gibbsLow r * gibbsHigh r) =
      Real.log 4 + Real.log (gibbsLow r * gibbsHigh r) := by
    rw [mul_assoc, Real.log_mul (by norm_num) hq]
  unfold sourceDeficit centeredDeficit
  simp_rw [energy_centering hr, Finset.sum_add_distrib, ← Finset.mul_sum, hrow, hcol,
    gibbs_log_column hr U hU]
  rw [h, entropy, hlog, Real.log_div ht (by norm_num)]
  simp [Fin.sum_univ_four, levels, total]
  ring

/-- The exact one-mode premise of the repeated-middle reduction at temperature `r`. -/
def OneModeBound (r : ℝ) : Prop :=
  ∀ v w z : ℝ, 0 ≤ v → v ≤ w → -1 ≤ z → z ≤ 1 → 0 ≤ oneModeDeficit r v w z

/-- Wu's one-mode cubic inequality implies the two-mode repeated-middle bound.
Both modular Hölder gaps and the nonnegative frame remainder are retained. -/
theorem repeated_middle_lower_bound
    {r : ℝ} (hr : 1 ≤ r) (hone : OneModeBound r)
    (U : Frame) (hU : Uᴴ * U = 1) (hUU : U * Uᴴ = 1)
    {m n : ℝ} (hm : 0 ≤ m) (hmn : m ≤ n) (hn1 : n ≤ 1) :
    0 ≤ gamma r * r * holder21 m n + gamma r * r^2 * holder12 m n ∧
    0 ≤ frameRemainder r U m n ∧
    gamma r * r * holder21 m n + gamma r * r^2 * holder12 m n +
      frameRemainder r U m n ≤ sourceDeficit r U m n := by
  have hn := hm.trans hmn
  have hr0 := zero_le_one.trans hr
  have hγ : 0 ≤ gamma r := by unfold gamma; positivity
  have hY := holder_gaps hm hn
  refine ⟨add_nonneg (mul_nonneg (mul_nonneg hγ hr0) hY.1)
    (mul_nonneg (mul_nonneg hγ (sq_nonneg r)) hY.2),
    remainder_nonneg hr U hU hUU hm hmn hn1, ?_⟩
  have h0 := singleton_bounds U hU hUU 0 (-imbalance U 0) (abs_neg _)
  have h3 := singleton_bounds U hU hUU 3 (imbalance U 3) rfl
  have hlow := hone m n (-cutCoordinate (-imbalance U 0)) hm hmn
    (by linarith [h0.2.1]) (by linarith [h0.1])
  have hhigh := hone n 1 (-cutCoordinate (imbalance U 3)) hn hn1
    (by linarith [h3.2.1]) (by linarith [h3.1])
  have hs : blockRoot m n ≤ blockRoot n 1 := by
    unfold blockRoot
    apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
    linarith [pow_le_pow_left₀ hm hmn 3, pow_le_pow_left₀ hn hn1 3]
  have hbetween := hone (blockRoot m n) (blockRoot n 1) (-1)
    (Real.rpow_nonneg (by positivity) _) hs le_rfl (by norm_num)
  rw [source_eq_centered hr U hU hUU hm hn, repeated_middle_decomposition r U hU hUU hm hn]
  linarith

end D5.S3.Quantum.Semigroups.WuRepeatedMiddleCubic
