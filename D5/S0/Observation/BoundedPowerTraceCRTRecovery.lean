/- GID: D5/S0/Observation/BoundedPowerTraceCRTRecovery
   generality: G
   mirror-B: D5/B/S0/Observation/BoundedPowerTraceCRTRecovery
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A matrix power trace in a known open integer interval is uniquely recovered from a CRT residue modulo a product wider than that interval. -/

import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Trace

/- Library-search audit trail (2026-08-24):
   * `rg -n -F 'bounded_int_unique_of_mod' D5 Golden/Frozen/accepted` returned no
     matches.
   * Repository searches for `chineseRemainder`, `ModEq`, and `trace` found
     `D5.S0.Observation.FiniteWindowCRTIndistinguishability`, which uses
     `Nat.chineseRemainderOfFinset` to assemble finite `ZMod` residue windows, and
     `D5.S3.ArithUnits.FiniteWindowResidues.finite_window_residues_realizable`, which
     proves existence below the product. Neither gives signed bounded uniqueness;
     the S3 theorem also cannot be imported into S0.
   * Pinned mathlib provides `ZMod.intCast_eq_intCast_iff`,
     `Int.eq_zero_of_abs_lt_dvd`, and `Matrix.trace`; `Nat.ModEq.eq_of_abs_lt` is
     restricted to naturals and assumes the difference bound directly. The proof
     reuses the first three basic machines; no exact signed bounded uniqueness theorem
     was found.
 -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Observation.BoundedPowerTraceCRTRecovery

/-- The single residue modulo the product modulus obtained after CRT assembly. -/
def crtImage (M : ℕ) (x : ℤ) : ZMod M :=
  x

/-- The integer trace of the `j`th power of an integer matrix. -/
def powerTrace {d : Type*} [Fintype d] [DecidableEq d]
    (A : Matrix d d ℤ) (j : ℕ) : ℤ :=
  Matrix.trace (A ^ j)

/-- Two integers in `(-B, B)` with the same residue modulo `M > 2B` are equal. -/
theorem bounded_int_unique_of_mod (M B : ℕ) (hM : 2 * B < M) (m n : ℤ)
    (hm : |m| < B) (hn : |n| < B) (h : m ≡ n [ZMOD M]) : m = n := by
  have hdiff : |n - m| < (M : ℤ) := calc
    |n - m| ≤ |n| + |m| := abs_sub n m
    _ < (B : ℤ) + B := add_lt_add hn hm
    _ = 2 * (B : ℤ) := (two_mul (B : ℤ)).symm
    _ < M := by exact_mod_cast hM
  have hzero : n - m = 0 := Int.eq_zero_of_abs_lt_dvd h.dvd hdiff
  exact (sub_eq_zero.mp hzero).symm

/-- A bounded matrix power trace is uniquely determined by its assembled CRT image. -/
theorem power_trace_unique_of_crt_image {d : Type*} [Fintype d] [DecidableEq d]
    (M B : ℕ) (hM : 2 * B < M) (A C : Matrix d d ℤ) (j : ℕ)
    (hA : |powerTrace A j| < B) (hC : |powerTrace C j| < B)
    (himage : crtImage M (powerTrace A j) = crtImage M (powerTrace C j)) :
    powerTrace A j = powerTrace C j := by
  apply bounded_int_unique_of_mod M B hM _ _ hA hC
  exact (ZMod.intCast_eq_intCast_iff _ _ M).mp (by simpa [crtImage] using himage)

example :
    powerTrace (0 : Matrix (Fin 2) (Fin 2) ℤ) 1 =
      powerTrace (Matrix.single 0 1 7 : Matrix (Fin 2) (Fin 2) ℤ) 1 := by
  apply power_trace_unique_of_crt_image 3 1 (by decide)
  all_goals simp [powerTrace, crtImage]

#print axioms bounded_int_unique_of_mod

end D5.S0.Observation.BoundedPowerTraceCRTRecovery
