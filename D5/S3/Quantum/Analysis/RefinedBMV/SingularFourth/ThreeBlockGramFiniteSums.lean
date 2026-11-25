/- GID: D5/S3/Quantum/Analysis/RefinedBMV/SingularFourth/ThreeBlockGramFiniteSums
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Schur factorization and weighted finite geometric sums. -/

import D5.S3.Quantum.Analysis.RefinedBMV.SingularFourth.ThreeBlockGram

/-! The scalar Schur reduction and finite sums for the singular spectral certificate. -/

noncomputable section

set_option maxHeartbeats 1000000

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace RefinedBMV.ThreeBlockGram.Separated

/-- A symmetric real coefficient matrix, viewed over the complex numbers. -/
def block (a x b y z c : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![(a : ℂ), (x : ℂ), (y : ℂ);
    (x : ℂ), (b : ℂ), (z : ℂ);
    (y : ℂ), (z : ℂ), (c : ℂ)]

/-- Elimination of the first two positive pivots by an exact LDL* factorization. -/
theorem block_psd_of_schur (a x b y z c : ℝ)
    (ha : 0 < a) (hb : 0 < b - x^2/a)
    (hc : (z - x*y/a)^2 ≤ (b - x^2/a)*(c - y^2/a)) :
    (block a x b y z c).PosSemidef := by
  let B := b - x^2/a
  let E := z - x*y/a
  let C := c - y^2/a
  have hB : 0 < B := hb
  have hC : 0 ≤ C - E^2/B := by
    apply sub_nonneg.mpr
    apply (div_le_iff₀ hB).mpr
    simpa only [B, E, C, mul_comm] using hc
  let P : Matrix (Fin 3) (Fin 3) ℂ :=
    !![1, 0, 0; (↑(x/a) : ℂ), 1, 0; (↑(y/a) : ℂ), (↑(E/B) : ℂ), 1]
  let D : Matrix (Fin 3) (Fin 3) ℂ :=
    diagonal ![(a : ℂ), (B : ℂ), (↑(C-E^2/B) : ℂ)]
  have hD : D.PosSemidef := by
    apply posSemidef_diagonal_iff.mpr
    intro i
    fin_cases i
    · exact Complex.zero_le_real.mpr ha.le
    · exact Complex.zero_le_real.mpr hB.le
    · exact Complex.zero_le_real.mpr hC
  have hfac : P * D * Pᴴ = block a x b y z c := by
    have haC : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
    have hBC : (B : ℂ) ≠ 0 := by exact_mod_cast hB.ne'
    ext i j
    simp only [Matrix.mul_apply (M := P * D) (N := Pᴴ), Matrix.conjTranspose_apply,
      D, Matrix.mul_diagonal, Fin.sum_univ_three]
    fin_cases i <;> fin_cases j <;>
      simp [P, block, Complex.star_def] <;> push_cast <;>
      field_simp [haC, hBC] <;> simp only [B, E, C] <;>
      push_cast <;> field_simp [haC] <;> ring
  rw [← hfac]
  exact hD.mul_mul_conjTranspose_same P

/-- Positive semidefiniteness is preserved by real diagonal congruence. -/
theorem block_scale (a x b y z c u v t : ℝ)
    (h : (block a x b y z c).PosSemidef) :
    (block (u^2*a) (u*v*x) (v^2*b) (u*t*y) (v*t*z) (t^2*c)).PosSemidef := by
  let D : Matrix (Fin 3) (Fin 3) ℂ := diagonal ![(u : ℂ), (v : ℂ), (t : ℂ)]
  have hD : Dᴴ = D := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [D, Matrix.conjTranspose_apply, Matrix.diagonal_apply, Complex.star_def]
  have heq : D * block a x b y z c * Dᴴ =
      block (u^2*a) (u*v*x) (v^2*b) (u*t*y) (v*t*z) (t^2*c) := by
    rw [hD]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [D, block, Matrix.diagonal_mul, Matrix.mul_diagonal] <;> push_cast <;> ring
  rw [← heq]
  exact h.mul_mul_conjTranspose_same D

/-- The six weighted finite geometric sums appearing before the comparator
terms are subtracted. Throughout, L is p+1. -/
def rawS (L : ℕ) (r : ℝ) : ℝ := ∑ j ∈ Finset.range L, r^j
def rawU (L : ℕ) (r : ℝ) : ℝ := ∑ j ∈ Finset.range L, ((j:ℝ)+1)*r^j
def rawV (L : ℕ) (r : ℝ) : ℝ := ∑ j ∈ Finset.range L, ((L:ℝ)-j)*r^j
def rawF (L : ℕ) (r : ℝ) : ℝ :=
  ∑ j ∈ Finset.range L, ((j:ℝ)+1)*((j:ℝ)+2)/2*r^j
def rawG (L : ℕ) (r : ℝ) : ℝ :=
  ∑ j ∈ Finset.range L, ((L:ℝ)-j)*((L:ℝ)-j+1)/2*r^j
def rawW (L : ℕ) (r : ℝ) : ℝ :=
  ∑ j ∈ Finset.range L, ((j:ℝ)+1)*((L:ℝ)-j)*r^j

def M (L : ℝ) : ℝ := L*(L+1)/2
def N (L : ℝ) : ℝ := L*(L+1)*(L+2)/6

private theorem rawS_succ (L : ℕ) (r : ℝ) :
    rawS (L+1) r = rawS L r + r^L := by
  simp only [rawS, Finset.sum_range_succ]

private theorem rawU_succ (L : ℕ) (r : ℝ) :
    rawU (L+1) r = rawU L r + ((L:ℝ)+1)*r^L := by
  simp only [rawU, Finset.sum_range_succ]

private theorem rawF_succ (L : ℕ) (r : ℝ) :
    rawF (L+1) r = rawF L r + ((L:ℝ)+1)*((L:ℝ)+2)/2*r^L := by
  simp only [rawF, Finset.sum_range_succ]

private theorem rawV_succ (L : ℕ) (r : ℝ) :
    rawV (L+1) r = rawV L r + rawS (L+1) r := by
  rw [rawS_succ]
  unfold rawV rawS
  simp only [Finset.sum_range_succ, Nat.cast_add, Nat.cast_one]
  rw [← add_assoc, ← Finset.sum_add_distrib]
  congr 1
  · apply Finset.sum_congr rfl
    intro j _
    ring
  · ring

private theorem rawG_succ (L : ℕ) (r : ℝ) :
    rawG (L+1) r = rawG L r + rawV (L+1) r := by
  unfold rawG rawV
  simp only [Finset.sum_range_succ, Nat.cast_add, Nat.cast_one]
  rw [← add_assoc, ← Finset.sum_add_distrib]
  congr 1
  · apply Finset.sum_congr rfl
    intro j _
    ring
  · ring

private theorem rawW_succ (L : ℕ) (r : ℝ) :
    rawW (L+1) r = rawW L r + rawU (L+1) r := by
  rw [rawU_succ]
  unfold rawW rawU
  simp only [Finset.sum_range_succ, Nat.cast_add, Nat.cast_one]
  rw [← add_assoc, ← Finset.sum_add_distrib]
  congr 1
  · apply Finset.sum_congr rfl
    intro j _
    ring
  · ring

/-- Exact finite-sum tail formulas, obtained by induction without infinite sums.
For t=1-r and w=L*t the discarded tails are polynomial in r^L. -/
theorem finite_sum_forms (L : ℕ) (r : ℝ) :
    (1-r)*rawS L r = 1-r^L ∧
    (1-r)^2*rawU L r = 1-r^L*(1+(L:ℝ)*(1-r)) ∧
    (1-r)^2*rawV L r = (L:ℝ)*(1-r)-r+r*r^L ∧
    (1-r)^3*rawF L r =
      1-r^L*(1+(L:ℝ)*(1-r)+M L*(1-r)^2) ∧
    (1-r)^3*rawG L r =
      M L*(1-r)^2-(L:ℝ)*(1-r)*r+r^2*(1-r^L) ∧
    (1-r)^3*rawW L r =
      (L:ℝ)*(1-r)-2*r+r^L*r*((L:ℝ)*(1-r)+2) := by
  induction L with
  | zero => norm_num [rawS, rawU, rawV, rawF, rawG, rawW, M] <;> ring
  | succ L ih =>
    obtain ⟨hS,hU,hV,hF,hG,hW⟩ := ih
    have hS' : (1-r)*rawS (L+1) r = 1-r^(L+1) := by
      simp only [rawS_succ, mul_add, hS, pow_succ]
      ring
    have hU' : (1-r)^2*rawU (L+1) r =
        1-r^(L+1)*(1+((L+1:ℕ):ℝ)*(1-r)) := by
      rw [rawU_succ, mul_add, hU, pow_succ]
      push_cast
      ring
    have hV' : (1-r)^2*rawV (L+1) r =
        ((L+1:ℕ):ℝ)*(1-r)-r+r*r^(L+1) := by
      rw [rawV_succ, show (1-r)^2*(rawV L r+rawS (L+1) r) =
        (1-r)^2*rawV L r+(1-r)*((1-r)*rawS (L+1) r) by ring, hV, hS']
      push_cast
      rw [pow_succ]
      ring
    have hF' : (1-r)^3*rawF (L+1) r =
        1-r^(L+1)*(1+((L+1:ℕ):ℝ)*(1-r)+M ((L+1:ℕ):ℝ)*(1-r)^2) := by
      rw [rawF_succ, mul_add, hF, pow_succ]
      push_cast
      unfold M
      ring
    have hG' : (1-r)^3*rawG (L+1) r =
        M ((L+1:ℕ):ℝ)*(1-r)^2-((L+1:ℕ):ℝ)*(1-r)*r+r^2*(1-r^(L+1)) := by
      rw [rawG_succ, show (1-r)^3*(rawG L r+rawV (L+1) r) =
        (1-r)^3*rawG L r+(1-r)*((1-r)^2*rawV (L+1) r) by ring, hG, hV']
      push_cast
      simp only [M, pow_succ]
      ring
    have hW' : (1-r)^3*rawW (L+1) r =
        ((L+1:ℕ):ℝ)*(1-r)-2*r+r^(L+1)*r*(((L+1:ℕ):ℝ)*(1-r)+2) := by
      rw [rawW_succ, show (1-r)^3*(rawW L r+rawU (L+1) r) =
        (1-r)^3*rawW L r+(1-r)*((1-r)^2*rawU (L+1) r) by ring, hW, hU']
      push_cast
      rw [pow_succ]
      ring
    exact ⟨hS',hU',hV',hF',hG',hW'⟩

end RefinedBMV.ThreeBlockGram.Separated
