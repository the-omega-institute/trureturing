/- GID: D5/S3/Quantum/AURICOmega/TernaryComparisonReflection
   generality: G
   mirror-B: D5/B/S3/Quantum/AURICOmega/TernaryComparisonReflection
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Two-point reflection sequences are group powers, so equally spaced readings agree. -/

import D5.S3.Quantum.AURICOmega.TernaryComparisonGroup

/-! Reflection sequences of ternary comparison structures.

Starting from two points `a` and `b`, the reflection sequence reflects the previous point
through the current one: `x 0 = a`, `x 1 = b` and `x (n + 2) = tri (x (n + 1)) (x n) (x (n + 1))`.
In the group at `a`, where `tri x y z = x * y⁻¹ * z`, the sequence is `x n = b ^ n`. Left
translations of that group are transfers through `a`, under which the reading is invariant, so the
reading between `x m` and `x (m + n)` equals the reading between `a` and `x n`. -/

namespace D5.S3.Quantum.AURICOmega.TernaryComparisonReflection

open D5.S3.Quantum.AURICOmega.TernaryComparisonGroup

variable {M : Type*}

/-- The reflection sequence through `a` and `b`: it starts at `a`, then `b`, and each further
point is the reflection `tri (x (n + 1)) (x n) (x (n + 1))` of the point before last through the
last point. -/
def reflectionSeq (C : TernaryComparison M) (a b : M) : ℕ → M
  | 0 => a
  | 1 => b
  | n + 2 => C.tri (reflectionSeq C a b (n + 1)) (reflectionSeq C a b n)
      (reflectionSeq C a b (n + 1))

/-- The reflection sequence through `a` and `b` is the sequence of powers of `b` in the group at
`a`. -/
theorem reflectionSeq_eq_pow (C : TernaryComparison M) (a b : M) (n : ℕ) :
    reflectionSeq C a b n = (letI := C.groupAt a; b ^ n) := by
  let _ := C.groupAt a
  suffices h : ∀ k : ℕ,
      reflectionSeq C a b k = b ^ k ∧ reflectionSeq C a b (k + 1) = b ^ (k + 1) from (h n).1
  intro k
  induction k with
  | zero => exact ⟨(pow_zero b).symm, (pow_one b).symm⟩
  | succ k ih =>
    refine ⟨ih.2, ?_⟩
    change C.tri (reflectionSeq C a b (k + 1)) (reflectionSeq C a b k)
      (reflectionSeq C a b (k + 1)) = b ^ (k + 2)
    rw [C.tri_eq_mul_inv_mul a, ih.1, ih.2, pow_succ' b k, mul_inv_cancel_right, ← pow_succ',
      ← pow_succ']

/-- Readings along the reflection sequence depend only on the spacing: the reading between the
`m`-th and the `(m + n)`-th point equals the reading between the start `a` and the `n`-th point. -/
theorem kappa_reflectionSeq_add (C : TernaryComparison M) (a b : M) (m n : ℕ) :
    C.kappa (reflectionSeq C a b m) (reflectionSeq C a b (m + n)) =
      C.kappa a (reflectionSeq C a b n) := by
  let _ := C.groupAt a
  rw [reflectionSeq_eq_pow C a b m, reflectionSeq_eq_pow C a b (m + n),
    reflectionSeq_eq_pow C a b n, pow_add]
  have h := C.kappa_tri_left (b ^ m) a a (b ^ n)
  rw [C.tri_self_right] at h
  exact h

end D5.S3.Quantum.AURICOmega.TernaryComparisonReflection
