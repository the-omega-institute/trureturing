/- GID: D5/S3/PrimeForms/BronzeLadderLeg
   generality: G
   mirror-B: D5/B/S3/PrimeForms/BronzeLadderLeg
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The bronze ladder p is the integer sequence p 0 = 1, p 1 = 3, p (n+2) = 3·p(n+1) + p n, whose k-th term is the top-left entry of the k-th power of the crossing matrix [[3,1],[1,0]] of trace 3 and determinant -1. Its Cassini identity p n·p(n+2) - p(n+1)² = (-1)^n has right side (det T)^n = (-1)^n, and the leg identity 13·p(n+1)² - (3·p(n+1)+2·p n)² = 4·(-1)^(n+1) = -4·(-1)^n places the ladder points on the indefinite Pell conic 13x² - y² = ±4. -/

import Mathlib

namespace D5.S3.PrimeForms.BronzeLadderLeg

/-- The **bronze ladder** `p : ℕ → ℤ`, the integer sequence with `p 0 = 1`, `p 1 = 3` and
`p (n+2) = 3·p(n+1) + p n`. Each `p k` is the top-left entry of the `k`-th power of the crossing
matrix `[[3, 1], [1, 0]]` (trace `3`, determinant `-1`), the `√13` analogue of the Fibonacci/Pell
ladders. -/
def bronzeLadder : ℕ → ℤ
  | 0 => 1
  | 1 => 3
  | (n + 2) => 3 * bronzeLadder (n + 1) + bronzeLadder n

/-- **Cassini / determinant identity for the bronze ladder.** For every `n`,
`p n · p(n+2) - p(n+1)² = (-1)^n`. The right side `(-1)^n` is `(det T)^n` for the crossing matrix
`[[3,1],[1,0]]` of determinant `-1`; equivalently the left side is `det (T^(n+2))`. Proved by
induction. -/
theorem bronze_cassini (n : ℕ) :
    bronzeLadder n * bronzeLadder (n + 2) - bronzeLadder (n + 1) ^ 2 = (-1) ^ n := by
  induction n with
  | zero => norm_num [bronzeLadder]
  | succ k ih =>
      have e2 : bronzeLadder (k + 2) = 3 * bronzeLadder (k + 1) + bronzeLadder k := by
        simp [bronzeLadder]
      have e3 : bronzeLadder (k + 3) = 3 * bronzeLadder (k + 2) + bronzeLadder (k + 1) := by
        simp [bronzeLadder]
      rw [e2] at ih
      show bronzeLadder (k + 1) * bronzeLadder (k + 3) - bronzeLadder (k + 2) ^ 2 = (-1) ^ (k + 1)
      rw [e3, e2, pow_succ]
      linear_combination (-1 : ℤ) * ih

/-- **Leg identity for the bronze ladder.** The indefinite binary form `13x² - y²` evaluated at the
ladder point `(x, y) = (p(n+1), 3·p(n+1) + 2·p n)` equals `4·(-1)^(n+1)`, so every ladder point lies
on the Pell conic `13x² - y² = ±4` (alternating sign). The value `4·(-1)^(n+1)` is `-4` times the
Cassini value `p n · p(n+2) - p(n+1)² = (-1)^n`, so the identity is a one-line consequence of
`bronze_cassini` (the proof is `linear_combination (-4) * bronze_cassini`).

Only the ladder's arithmetic core is recorded here — the Cassini determinant and this leg identity.
The geometric crossing `(1, 2, 3^k) = M·T^k`, the spectral four-accumulation limit of the crossing
angles, and the wider narrative clauses of the source are not covered by these statements. -/
theorem bronze_leg (n : ℕ) :
    13 * bronzeLadder (n + 1) ^ 2 - (3 * bronzeLadder (n + 1) + 2 * bronzeLadder n) ^ 2
      = 4 * (-1) ^ (n + 1) := by
  have hc := bronze_cassini n
  have e2 : bronzeLadder (n + 2) = 3 * bronzeLadder (n + 1) + bronzeLadder n := by
    simp [bronzeLadder]
  rw [e2] at hc
  rw [pow_succ]
  linear_combination (-4 : ℤ) * hc

end D5.S3.PrimeForms.BronzeLadderLeg
