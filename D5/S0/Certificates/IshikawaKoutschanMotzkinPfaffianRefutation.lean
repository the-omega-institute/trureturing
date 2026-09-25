/- GID: D5/S0/Certificates/IshikawaKoutschanMotzkinPfaffianRefutation
   generality: I
   mirror-B: D5/B/S0/Certificates/IshikawaKoutschanMotzkinPfaffianRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S0/Certificates/IshikawaKoutschanMotzkinPfaffianRefutation.claim; result=D5/S0/Certificates/IshikawaKoutschanMotzkinPfaffianRefutation.result; claim=D5/S0/Certificates/IshikawaKoutschanMotzkinPfaffianRefutation.claim
   digest: Refutes part (i) of Conjecture conj.gen of arXiv:1201.5253v2 at k = n = 2, where the Pfaffian is -8 and the printed product is 8; makes no claim against a sign-corrected statement. -/

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Matrix.Basic
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Tactic.NormNum

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Certificates.IshikawaKoutschanMotzkinPfaffianRefutation

open scoped BigOperators

/-!
Ishikawa–Koutschan, *Zeilberger's holonomic ansatz for Pfaffians*, arXiv:1201.5253v2,
Conjecture `conj.gen`, part (i): for all positive integers `n, k`,
`Pf((j-i) 𝓜^{(k)}_{i+j-2})_{1 ≤ i,j ≤ 2n}` equals `∏_{i<m} ∏_{j<k} (4ki+2j+k)` when
`m = n/k` is an integer, equals `(∏_{j=1}^{⌊k/2⌋} 1/(2j-k)) ∏_{i<m} ∏_{j=1}^{k} (4ki+2j-k)`
when `k` is odd and `m = (n+⌊k/2⌋)/k` is an integer, and is zero in all other cases.
Here `𝓜^{(k)}_i` is the number of Motzkin paths from `(0,0)` to `(i-1,k-1)`.
At `k = 1` this is the paper's Theorem `thm.pfMotz`; at `k = n = 2` the Pfaffian is `-8`
while the printed product is `8`. Part (ii) is not settled here.
-/

/-- The height change of a step: `0` is `U = (1,1)`, `1` is `H = (1,0)`, `2` is `D = (1,-1)`. -/
def stepRise (s : Fin 3) : ℤ := 1 - (s.val : ℤ)

/-- The height of a step word after its first `t` steps. -/
def heightAfter {len : ℕ} (w : Fin len → Fin 3) (t : ℕ) : ℤ :=
  ∑ i : Fin len, if i.val < t then stepRise (w i) else 0

/-- `𝓜^{(k)}_i`: the number of Motzkin paths from `(0,0)` to `(i-1,k-1)`, that is, step words
of length `i - 1` that never run below the axis and end at height `k - 1`. The value at `i = 0`
enters the matrix only on the diagonal, where it is multiplied by `j - i = 0`. -/
def motzkinTriangle (k i : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin (i - 1) → Fin 3)).filter fun w =>
    (∀ t ∈ Finset.range i, 0 ≤ heightAfter w t) ∧ heightAfter w (i - 1) = (k : ℤ) - 1).card

/-- The matrix `((j-i) 𝓜^{(k)}_{i+j-2})_{1 ≤ i,j ≤ 2n}`, indexed from zero. -/
def pfaffianMatrix (k n : ℕ) : Matrix (Fin (2 * n)) (Fin (2 * n)) ℤ :=
  fun p q => ((q.val : ℤ) - p.val) * motzkinTriangle k (p.val + q.val)

/-- The Pfaffian as defined in the source: the sum, over the partitions of `[2n]` into
two-element subsets `{σ(2i), σ(2i+1)}`, of the sign of the listing permutation `σ` times the
product of the paired entries. Each partition is listed once, with increasing pairs ordered by
their first elements. -/
def pfaffian {n : ℕ} (A : Matrix (Fin (2 * n)) (Fin (2 * n)) ℤ) : ℤ :=
  ∑ σ ∈ (Finset.univ : Finset (Equiv.Perm (Fin (2 * n)))).filter (fun σ =>
      (∀ i : Fin n, σ ⟨2 * i.val, by omega⟩ < σ ⟨2 * i.val + 1, by omega⟩) ∧
      ∀ i j : Fin n, i < j → σ ⟨2 * i.val, by omega⟩ < σ ⟨2 * j.val, by omega⟩),
    (Equiv.Perm.sign σ : ℤ) * ∏ i : Fin n, A (σ ⟨2 * i.val, by omega⟩) (σ ⟨2 * i.val + 1, by omega⟩)

/-- The printed right-hand side of part (i). -/
def printedValue (k n : ℕ) : ℚ :=
  if k ∣ n then
    ∏ i ∈ Finset.range (n / k), ∏ j ∈ Finset.range k, (4 * (k : ℚ) * i + 2 * j + k)
  else if k % 2 = 1 ∧ k ∣ n + k / 2 then
    (∏ j ∈ Finset.Icc 1 (k / 2), 1 / (2 * (j : ℚ) - k)) *
      ∏ i ∈ Finset.range ((n + k / 2) / k), ∏ j ∈ Finset.Icc 1 k, (4 * (k : ℚ) * i + 2 * j - k)
  else 0

/-- Part (i) of Conjecture `conj.gen`, for all positive integers `k` and `n`. -/
def claim : Prop :=
  ∀ k n : ℕ, 0 < k → 0 < n → (pfaffian (pfaffianMatrix k n) : ℚ) = printedValue k n

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in
/-- At `k = n = 2` the Pfaffian is `-8`, while the printed product is `2 · 4 = 8`. -/
theorem result : ¬ claim := by
  intro h
  have hpf : pfaffian (pfaffianMatrix 2 2) = -8 := by decide +kernel
  have hv : printedValue 2 2 = 8 := by
    simp [printedValue, Finset.prod_range_succ]
    norm_num
  have h22 := h 2 2 (by norm_num) (by norm_num)
  rw [hpf, hv] at h22
  norm_num at h22

#print axioms claim
#print axioms result

end D5.S0.Certificates.IshikawaKoutschanMotzkinPfaffianRefutation
