/- GID: D5/S3/Quantum/Matrix/ZhangThreeOperatorClarksonRefutation
   generality: G
   mirror-B: D5/B/S3/Quantum/Matrix/ZhangThreeOperatorClarksonRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Matrix/ZhangThreeOperatorClarksonRefutation.claim; result=D5/S3/Quantum/Matrix/ZhangThreeOperatorClarksonRefutation.result; claim=D5/S3/Quantum/Matrix/ZhangThreeOperatorClarksonRefutation.claim
   digest: Three matrices refute Zhang's three-operator Schatten inequality. -/

import D5.S3.Quantum.Schatten.Holder

/-! # A counterexample to the three-operator Clarkson–McCarthy conjecture

The Schatten norm is the frozen trace-functional-calculus norm. Its positive
real powers agree with sums of powers of singular values. Only the conjecture's
clause for real exponents at least two is asserted by `claim`.

Source: T. Zhang, arXiv:2410.21961v4, Conjecture `conj:sharp-inequality`.
Preregistration: https://github.com/the-omega-institute/trureturing/issues/22304
Admission basis: external open-problem resolution.
-/

noncomputable section

set_option linter.style.longLine false

open Matrix
open scoped BigOperators

namespace D5.S3.Quantum.Matrix.ZhangThreeOperatorClarksonRefutation

def claim : Prop :=
  ∀ p : ℝ, 2 ≤ p → ∀ (n : ℕ) (a b c : Matrix (Fin n) (Fin n) ℂ),
    schattenNorm (a + b + c) p ^ p + schattenNorm a p ^ p +
      schattenNorm b p ^ p + schattenNorm c p ^ p ≤
    ((3 : ℝ) ^ (p - 1) + 1) / (2 : ℝ) ^ p *
      (schattenNorm (a + b) p ^ p + schattenNorm (b + c) p ^ p +
        schattenNorm (c + a) p ^ p)

private def a : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, 0]
private def b : Matrix (Fin 2) (Fin 2) ℂ := !![0, 0; 0, 1]
private def c : Matrix (Fin 2) (Fin 2) ℂ := !![-(1 / 2), -(1 / 2); -(1 / 2), -(1 / 2)]

private lemma power_of_gram_charpoly (x : Matrix (Fin 2) (Fin 2) ℂ)
    (d : Fin 2 → ℝ) (hd : ∀ i, 0 ≤ d i)
    (hc : (xᴴ * x).charpoly = (diagonal (fun i => (d i : ℂ))).charpoly)
    {p : ℝ} (hp : 0 < p) :
    schattenNorm x p ^ p = ∑ i, d i ^ (p / 2) := by
  classical
  let hg := isHermitian_mul_conjTranspose_self xᴴ
  have hh : IsHermitian (diagonal (fun i => (d i : ℂ))) := by
    apply isHermitian_diagonal_iff.mpr
    intro i
    simp [isSelfAdjoint_iff]
  have he : hg.eigenvalues = hh.eigenvalues :=
    (hg.eigenvalues_eq_eigenvalues_iff (hB := hh)).mpr (by simpa using hc)
  obtain ⟨σ, hσ⟩ := hh.eigenvalues_eq_of_unitary_similarity_diagonal
    (U := (1 : Matrix (Fin 2) (Fin 2) ℂ)) (by simp) (f := d) (by simp)
  rw [schattenNorm_rpow_eq_sum_singularValues x hp]
  calc
    _ = ∑ i, singularValues x (σ i) ^ p := (Equiv.sum_comp σ _).symm
    _ = ∑ i, d i ^ (p / 2) := by
      apply Finset.sum_congr rfl
      intro i _
      change Real.sqrt (hg.eigenvalues (σ i)) ^ p = _
      rw [he, show hh.eigenvalues (σ i) = d i from congrFun hσ i,
        Real.sqrt_eq_rpow, ← Real.rpow_mul (hd i)]
      congr 1
      ring

private lemma left_side {p : ℝ} (hp : 0 < p) :
    schattenNorm (a + b + c) p ^ p + schattenNorm a p ^ p +
      schattenNorm b p ^ p + schattenNorm c p ^ p = 4 := by
  sorry

private lemma right_side {p : ℝ} (hp : 0 < p) :
    schattenNorm (a + b) p ^ p + schattenNorm (b + c) p ^ p +
      schattenNorm (c + a) p ^ p = 2 + (2 : ℝ) ^ (2 - p / 2) := by
  sorry

private lemma certified_bound :
    ((3 : ℝ) ^ ((9 / 4 : ℝ) - 1) + 1) / (2 : ℝ) ^ (9 / 4 : ℝ) *
      (2 + (2 : ℝ) ^ (2 - (9 / 4 : ℝ) / 2)) < 4 := by
  sorry

theorem result : ¬ claim := by
  intro h
  have hw := h (9 / 4) (by norm_num) 2 a b c
  rw [left_side (by norm_num), right_side (by norm_num)] at hw
  exact (not_le_of_gt certified_bound) hw

end D5.S3.Quantum.Matrix.ZhangThreeOperatorClarksonRefutation
