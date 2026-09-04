/- GID: D5/S0/Observation/MatrixTracePowerSum
   generality: G
   mirror-B: D5/B/S0/Observation/MatrixTracePowerSum
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   digest: Power traces of a two by two matrix are the power sums of any supplied Vieta pair. -/

/- Library-search audit trail (2026-09-03). Commands reproduced literally as run, each ending in
   `wc -l`; none truncated. Declaration patterns are the wide form. Names, where listed, are the
   output of the same command that produced the count, and files come from `git grep -l`.

   git grep -clE 'trace \([A-Za-z]+ \^ ' origin/dev -- 'D5/**/*.lean' | wc -l               -> 10
     All ten opened. The one that matters is
     D5/S0/Observation/PowerTraceCharacteristicPolynomialSaturation.lean, frozen, whose
     `power_trace_characteristic_polynomial_saturation` proves, for `[Field K]` and `n x n`,
     Cayley-Hamilton and the trace recurrence
     `trace (A ^ (n + m)) = -sum over k of charpoly.coeff k * trace (A ^ (k + m))`.
     **At `n = 2` that recurrence is the one this module also needs**, so the recurrence half is
     not new over a field; what is proved here and is absent there is the closed form below, and
     it is proved without a `Field` instance. That file is not restated or amended.
     Also opened: `twoColorTransfer_trace_pow`, private in
     D5/S1/Eigenstructure/MixedExclusionSpectrum.lean, which is
     `trace (twoColorTransfer ^ n) = 2 ^ n + (-1) ^ n + 0 ^ n` for one concrete 3x3 matrix,
     proved by diagonalisation rather than by Cayley-Hamilton; it is an instance of the same
     principle at a fixed matrix, not a general statement. The remaining eight concern golden
     and Fibonacci traces, a similarity countermodel, CRT recovery and a determinant-minus-one
     trace square; none states a closed form for power traces.

   git grep -clE 'trace \([A-Za-z]+ \^ [a-z]+\) *= *[a-z]+ \^ [a-z]+ \+ [a-z]+ \^ [a-z]+'
     origin/dev -- 'D5/**/*.lean' | wc -l                                                    -> 0
   git grep -clE 'trace [A-Za-z]+ = [a-z]+ \+ [a-z]+' origin/dev -- 'D5/**/*.lean' | wc -l   -> 0
     No file states the closed form, and no file takes trace and determinant as Vieta data.

   Upstream results used rather than reproved: `Matrix.trace_fin_two`, `Matrix.det_fin_two`,
   `Matrix.trace_sub`, `Matrix.trace_smul`, `Matrix.trace_one` and `Nat.twoStepInduction`. The
   two by two Cayley identity is proved here entrywise because searching the pinned mathlib for
   a usable form found only the general `Matrix.aeval_self_charpoly`, which is stated through
   `charpoly` and would need more unfolding at this size than the direct proof.

   Batteries, CSLib and TauCeti were searched for earlier nodes of this family and returned
   nothing; no separate query was issued here, so those are carried negatives rather than fresh
   ones. Zulip was not queried. Live unmerged mathlib pull requests could not be searched: the
   local pin exposes no `refs/pull/` data and this worker has no network.
-/

import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Power traces of a two by two matrix

If a two by two matrix has `trace M = a + b` and `det M = a * b` for some pair `a b` in the ring,
then `trace (M ^ k) = a ^ k + b ^ k` for every `k`.

The pair is supplied as a hypothesis rather than extracted, so no algebraically closed field is
needed and the statement holds over any commutative ring: whenever the characteristic roots
happen to live in the ring, this identifies the power traces with their power sums.

The frozen `PowerTraceCharacteristicPolynomialSaturation` in this same directory already gives,
for a field and any size, Cayley-Hamilton together with a recurrence among power traces. At size
two that recurrence yields this closed form in a few lines, so **over a field the closed form is
a corollary of it, not independent mathematics**. What is genuinely strengthened here is the
scope: no field is required. That is not cosmetic — over `ZMod 4`, the matrix `!![0, 2; 1, 3]`
has trace `3 = 1 + 2` and determinant `2 = 1 * 2`, so this theorem applies with `a = 1, b = 2`,
while the frozen one cannot be instantiated there, `ZMod 4` having a nonzero nilpotent and so
admitting no embedding into a field. The closed form remains useful here as a named statement;
its novelty claim is the ring generality.
-/

namespace D5.S0.Observation.MatrixTracePowerSum

variable {R : Type*} [CommRing R]

/-- The Cayley identity in size two, proved entrywise. -/
private theorem sq_eq (M : Matrix (Fin 2) (Fin 2) R) :
    M ^ 2 = Matrix.trace M • M - Matrix.det M • (1 : Matrix (Fin 2) (Fin 2) R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_two, Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two,
      Matrix.det_fin_two] <;> ring

/-- Shifting a power by two, in matrix form. -/
private theorem pow_add_two (M : Matrix (Fin 2) (Fin 2) R) (n : Nat) :
    M ^ (n + 2) = Matrix.trace M • M ^ (n + 1) - Matrix.det M • M ^ n := by
  calc M ^ (n + 2) = M ^ n * M ^ 2 := by rw [← pow_add]
    _ = M ^ n * (Matrix.trace M • M - Matrix.det M • (1 : Matrix (Fin 2) (Fin 2) R)) := by
        rw [sq_eq]
    _ = Matrix.trace M • (M ^ n * M) - Matrix.det M • (M ^ n * 1) := by
        rw [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_smul]
    _ = Matrix.trace M • M ^ (n + 1) - Matrix.det M • M ^ n := by
        rw [← pow_succ, mul_one]

/-- The same shift, read off on traces. -/
private theorem trace_pow_add_two (M : Matrix (Fin 2) (Fin 2) R) (n : Nat) :
    Matrix.trace (M ^ (n + 2))
      = Matrix.trace M * Matrix.trace (M ^ (n + 1))
        - Matrix.det M * Matrix.trace (M ^ n) := by
  rw [pow_add_two, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_smul,
    smul_eq_mul, smul_eq_mul]

/-- Power traces are the power sums of any pair carrying the trace and determinant of the
matrix. -/
theorem trace_pow_eq_add_pow (M : Matrix (Fin 2) (Fin 2) R) (a b : R)
    (htrace : Matrix.trace M = a + b) (hdet : Matrix.det M = a * b) (k : Nat) :
    Matrix.trace (M ^ k) = a ^ k + b ^ k := by
  induction k using Nat.twoStepInduction with
  | zero => norm_num [Matrix.trace_one]
  | one => simpa using htrace
  | more n ih0 ih1 =>
      rw [trace_pow_add_two, ih1, ih0, htrace, hdet]
      ring

end D5.S0.Observation.MatrixTracePowerSum
