/- GID: D5/S0/Certificates/MotzkinConvolutionHankelRefutation
   generality: I
   mirror-B: D5/B/S0/Certificates/MotzkinConvolutionHankelRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: [mathlib/module/Mathlib.Combinatorics.Enumerative.Catalan.Basic, mathlib/module/Mathlib.LinearAlgebra.Matrix.Determinant.Basic]
   utility: kind=bounded-enumeration; basis=refutes=gid:D5/S0/Certificates/MotzkinConvolutionHankelRefutation.claim; result=D5/S0/Certificates/MotzkinConvolutionHankelRefutation.result; claim=D5/S0/Certificates/MotzkinConvolutionHankelRefutation.claim
   digest: Refutes the printed universal first chain of Conjecture 7, arXiv:2502.21050v1, at r=4,n=0; makes no claim against a possibly intended restriction r>=8. -/

import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Certificates.MotzkinConvolutionHankelRefutation

open scoped BigOperators

/-!
Wang–Zhang, *Hankel determinants for convolution powers of Motzkin numbers*,
arXiv:2502.21050v1, Conjecture 7, first equality chain:
`H_{3rn} = H_{3rn+1} = H_{3rn+r} = H_{3rn+r+1} = α`, with `|α| = 1`.
The printed text imposes no lower bound on `r`. The authors may have intended
`r ≥ 8`, since Theorems 1–6 cover `r = 2,3,4,5,6,7`; that intent is unverified.
We refute the printed universal first chain, not such an intended restriction.
Theorem 4 is corroboration only and is not used in this proof.
-/

/-- The source's formula `M_n = ∑_k choose(n,2k) C_k`.
Terms with `k > n` vanish, so the finite sum retains the whole formula. -/
def motzkin (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), (Nat.choose n (2 * k) * catalan k : ℕ)

/-- Coefficients of `M(x)^r`, by iterated Cauchy multiplication;
the zeroth power is the constant series one. -/
def convolutionPower : ℕ → ℕ → ℤ
  | 0, n => if n = 0 then 1 else 0
  | r + 1, n => ∑ k ∈ Finset.range (n + 1),
      convolutionPower r k * motzkin (n - k)

/-- The ordinary, unshifted Hankel determinant, including the empty determinant. -/
def hankel (a : ℕ → ℤ) (n : ℕ) : ℤ :=
  Matrix.det (fun i j : Fin n => a (i.val + j.val))

/-- The printed first chain for every residue-eligible `r` and every `n`.
For each pair the four entries must share the same sign `α`; there is no `r ≥ 8`
or positive-`n` hypothesis. Equality to a common `α` expresses the entire chain. -/
def claim : Prop :=
  ∀ r : ℕ, r % 3 = 1 ∨ r % 3 = 2 → ∀ n : ℕ,
    ∃ α : ℤ, |α| = 1 ∧
      hankel (convolutionPower r) (3 * r * n) = α ∧
      hankel (convolutionPower r) (3 * r * n + 1) = α ∧
      hankel (convolutionPower r) (3 * r * n + r) = α ∧
      hankel (convolutionPower r) (3 * r * n + r + 1) = α

-- The heartbeat allowance covers kernel evaluation of the 24 permutations
-- together with the recursive Cauchy sums; no external numerical oracle is used.
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 10000 in
/-- The permitted pair `r = 4, n = 0` forces the impossible equality `1 = -1`.
The finite numerical evidence is local to this proof, with no exported instance. -/
theorem result : ¬ claim := by
  intro h
  have hankel_four_eq_neg_one : hankel (convolutionPower 4) 4 = -1 := by
    decide +kernel
  obtain ⟨α, _, h0, _, h4, _⟩ := h 4 (Or.inl (by decide)) 0
  have impossible : (1 : ℤ) = -1 := calc
    1 = hankel (convolutionPower 4) 0 := Matrix.det_fin_zero.symm
    _ = α := h0
    _ = hankel (convolutionPower 4) 4 := h4.symm
    _ = -1 := hankel_four_eq_neg_one
  exact (by decide : (1 : ℤ) ≠ -1) impossible

#print axioms claim
#print axioms result

end D5.S0.Certificates.MotzkinConvolutionHankelRefutation
