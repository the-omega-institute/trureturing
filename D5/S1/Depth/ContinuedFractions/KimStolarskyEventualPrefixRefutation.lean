/- GID: D5/S1/Depth/ContinuedFractions/KimStolarskyEventualPrefixRefutation
   generality: I
   mirror-B: D5/B/S1/Depth/ContinuedFractions/KimStolarskyEventualPrefixRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: [mathlib/module/Mathlib.Topology.Instances.Real.Lemmas]
   utility: kind=certified-instance; basis=refutes=gid:D5/S1/Depth/ContinuedFractions/KimStolarskyEventualPrefixRefutation.claim; result=D5/S1/Depth/ContinuedFractions/KimStolarskyEventualPrefixRefutation.result; claim=D5/S1/Depth/ContinuedFractions/KimStolarskyEventualPrefixRefutation.claim
   digest: The complete eventual three-prefix assertion fails at every index congruent to two modulo three. -/

import D5.S1.Depth.ContinuedFractions.QuadraticImpliesPeriodic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic

/-! The source is arXiv:2511.15133v1, Theorem 1 and Remark 4, and
Integers 26, A98, Theorem 1 and Remark 3. All three polynomial families,
the m+1 shift, ordinary floor-and-inverse continued fractions, and the
common eventual threshold are retained. Only the R conjunct is needed
for the refutation. The other root branches are not asserted separately.

proof_shape: result: bind-only (external open-problem resolution).
admission_basis: open-problem-resolution, issue #28129.
Private proof shapes: residue: bind-only, consumer result;
parameter_large: bind-only, consumer r_failure;
r_failure: bind-only, consumer result.
All private lemmas are consumed by result or by a consumed private lemma;
they organize algebra and modular arithmetic, not new upstream results.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Depth.ContinuedFractions.KimStolarskyEventualPrefixRefutation

open Filter
open scoped Topology BigOperators
open D5.S1.Depth.ContinuedFractions.QuadraticImpliesPeriodic



/-- The source triangular number, as a real. -/
noncomputable def triangular (j : ℕ) : ℝ := (j : ℝ) * ((j : ℝ) + 1) / 2

/-- The original odd L polynomial, before the conjecture's shift. -/
noncomputable def lOdd (m : ℕ) (x : ℝ) : ℝ :=
  (∑ j ∈ Finset.Icc 1 m, (2 * (j : ℝ) - 1) ^ 3) + x ^ 3 +
    ∑ j ∈ Finset.Icc 2 m, (2 * (j : ℝ) - 2 + ((j : ℝ) - 1) * x) ^ 3

/-- The original odd R polynomial, before the conjecture's shift. -/
noncomputable def rOdd (m : ℕ) (x : ℝ) : ℝ :=
  (triangular (2 * m - 1) + (1 + triangular (m - 1)) * x) ^ 2

/-- The original P sum; subtraction is in the real coefficient ring. -/
noncomputable def pOdd (m : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ Finset.Icc 0 m,
    (4 * (j : ℝ) + 1 + (j : ℝ) * x) *
      (((j : ℝ) + 1) * ((j : ℝ) - 2) + (j : ℝ) ^ 2 * x)

/-- The literal third source expression. -/
noncomputable def qOdd (m : ℕ) (x : ℝ) : ℝ := x * pOdd m x - x ^ 2 + x ^ 3

/-- The source subsequence m = 10^(2(2n+1)). -/
def parameter (n : ℕ) : ℕ := 10 ^ (4 * n + 2)

/-- Ordinary simple continued-fraction digits: floor each successive complete
quotient and invert its fractional part. Nonzero remainders prevent continuing
past termination; no restriction is imposed after the specified prefix. -/
def HasPrefix (x : ℝ) (digits : List ℝ) : Prop :=
  ∀ i (hi : i < digits.length),
    (⌊completeQuotient x i⌋ : ℝ) = digits[i] ∧
      (i + 1 < digits.length → Int.fract (completeQuotient x i) ≠ 0)

noncomputable def lDigits (n : ℕ) : List ℝ :=
  [4, 75 * 10 ^ (4 * n), 3, 4, 1, ((15 * 10 ^ (2 * n)) ^ 2 - 23) / 101]

noncomputable def rDigits (n : ℕ) : List ℝ :=
  [4, 50 * 10 ^ (4 * n) + 2, (⌊(parameter n : ℝ) / 7⌋ : ℝ) - 1]

noncomputable def qDigits (n : ℕ) : List ℝ :=
  [4, 75 * 10 ^ (4 * n), 3, (⌈(6 * (parameter n : ℝ) + 100) / 35⌉ : ℝ)]

/-- The complete source eventual conjunction, with actual real-root branches
of the three original polynomials tending to minus four. -/
def claim : Prop :=
  ∃ (l r q : ℕ → ℝ) (N : ℕ), 1 ≤ N ∧
    Tendsto l atTop (𝓝 (-4)) ∧ Tendsto r atTop (𝓝 (-4)) ∧
    Tendsto q atTop (𝓝 (-4)) ∧
    ∀ n, N ≤ n →
      lOdd (parameter n + 1) (l n) = 0 ∧
      rOdd (parameter n + 1) (r n) = 0 ∧
      qOdd (parameter n) (q n) = 0 ∧
      HasPrefix (-l n) (lDigits n) ∧
      HasPrefix (-r n) (rDigits n) ∧
      HasPrefix (-q n) (qDigits n)

private theorem residue (k : ℕ) : parameter (3 * k + 2) % 7 = 4 := by
  unfold parameter
  have he : 4 * (3 * k + 2) + 2 = 12 * k + 10 := by omega
  rw [he, pow_add, pow_mul]
  norm_num [Nat.mul_mod, Nat.pow_mod]

private theorem parameter_large (n : ℕ) : 10 < parameter n := by
  have h : (100 : ℕ) ≤ parameter n := by
    unfold parameter
    calc
      100 = 10 ^ 2 := by norm_num
      _ ≤ 10 ^ (4 * n + 2) := Nat.pow_le_pow_right (by decide) (by omega)
  omega

private theorem r_failure (n : ℕ) (hres : parameter n % 7 = 4)
    (x : ℝ) (hroot : rOdd (parameter n + 1) x = 0) :
    ¬ HasPrefix (-x) (rDigits n) := by
  intro hp
  let m : ℕ := parameter n
  let y : ℝ := -x
  let A : ℝ := 50 * 10 ^ (4 * n) + 2
  have hm : (10 : ℝ) < m := by exact_mod_cast parameter_large n
  have hD : 0 < (m : ℝ) ^ 2 + m + 2 := by positivity
  have hshift : 2 * (m + 1) - 1 = 2 * m + 1 := by omega
  have hlinear :
      ((2 * (m : ℝ) + 1) * (2 * (m : ℝ) + 2) / 2 +
        (1 + (m : ℝ) * ((m : ℝ) + 1) / 2) * x) = 0 := by
    have hsq := (sq_eq_zero_iff).mp hroot
    norm_num [rOdd, triangular, m, hshift, Nat.cast_add, Nat.cast_mul] at hsq
    nlinarith [hsq]
  have hy : y - 4 = (2 * (m : ℝ) - 6) / ((m : ℝ) ^ 2 + m + 2) := by
    apply (eq_div_iff (ne_of_gt hD)).2
    dsimp [y]
    nlinarith [hlinear]
  have hA : A = (m : ℝ) / 2 + 2 := by
    dsimp [A, m, parameter]
    push_cast
    rw [pow_add]
    norm_num
    ring
  have hf0 : (⌊y⌋ : ℝ) = 4 := (hp 0 (by simp [rDigits])).1
  have hy0 : Int.fract y = y - 4 := by rw [Int.fract, hf0]
  have hf1 : (⌊(y - 4)⁻¹⌋ : ℝ) = A := by
    have h := (hp 1 (by simp [rDigits])).1
    change (⌊completeQuotient y 1⌋ : ℝ) = A at h
    simpa only [completeQuotient, hy0] using h
  have hm3 : (m : ℝ) - 3 ≠ 0 := by linarith
  have hm6 : 2 * (m : ℝ) - 6 ≠ 0 := by linarith
  have hinv : (y - 4)⁻¹ = A + 7 / ((m : ℝ) - 3) := by
    rw [hy, hA]
    field_simp [hm3, hm6]
    <;> ring
  have hnext : (Int.fract (y - 4)⁻¹)⁻¹ = ((m : ℝ) - 3) / 7 := by
    rw [Int.fract, hf1, hinv]
    simp only [add_sub_cancel_left, inv_div]
  have hf2 : (⌊((m : ℝ) - 3) / 7⌋ : ℝ) = (⌊(m : ℝ) / 7⌋ : ℝ) - 1 := by
    have h := (hp 2 (by simp [rDigits])).1
    change (⌊completeQuotient y 2⌋ : ℝ) = (⌊(m : ℝ) / 7⌋ : ℝ) - 1 at h
    simpa only [completeQuotient, hy0, hnext] using h
  let q : ℕ := m / 7
  have hm_eq : m = 7 * q + 4 := by
    have hd := Nat.mod_add_div m 7
    dsimp [m] at hd ⊢
    omega
  have hm_real : (m : ℝ) = 7 * (q : ℝ) + 4 := by exact_mod_cast hm_eq
  have f1 : ⌊((m : ℝ) - 3) / 7⌋ = (q : ℤ) := by
    apply Int.floor_eq_iff.mpr
    push_cast
    rw [hm_real]
    constructor <;> linarith
  have f2 : ⌊(m : ℝ) / 7⌋ = (q : ℤ) := by
    apply Int.floor_eq_iff.mpr
    push_cast
    rw [hm_real]
    constructor <;> linarith
  rw [f1, f2] at hf2
  linarith

/-- Every proposed common threshold is defeated by n = 3N+2. -/
theorem result : ¬ claim := by
  rintro ⟨l, r, q, N, hN, hl, hr, hq, h⟩
  have hs := h (3 * N + 2) (by omega)
  exact r_failure (3 * N + 2) (residue N) (r (3 * N + 2)) hs.2.1 hs.2.2.2.2.1

#print axioms result

end D5.S1.Depth.ContinuedFractions.KimStolarskyEventualPrefixRefutation
