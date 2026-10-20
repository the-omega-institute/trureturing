/- GID: D5/S3/Combinatorics/PerfectMatchings/DeformedJucysMurphyRow
   generality: I
   mirror-B: D5/B/S3/Combinatorics/PerfectMatchings/DeformedJucysMurphyRow
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Order.Partition.Finpartition]
   utility: none
   digest: Exact canonical occurrence row and native C1. -/

import D5.S3.Combinatorics.PerfectMatchings.DeformedJucysMurphyCuts

/-! The one canonical occurrence coefficient and its literal native action. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.PerfectMatchings.DeformedJucysMurphyRow

open Equiv
open D5.S0.Certificates.Combinatorics.DeformedJucysMurphyNoncommutation
open D5.S3.Combinatorics.PerfectMatchings.InvolutionOrbitSplit
open D5.S3.Combinatorics.PerfectMatchings.DeformedJucysMurphyWalk
open D5.S3.Combinatorics.PerfectMatchings.DeformedJucysMurphyCharge
open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-- Exact occurrence formula, indexed by a source partition and a target partition.
The ordered join sum removes two occurrences and divides by two. -/
noncomputable def rowCoefficient {K : Type*} [Field K] [CharZero K] (b : K)
    {k : ℕ} (rho lam : Nat.Partition k) : K :=
  ((rho.parts.map fun (r : ℕ) =>
      (r : K) / 2 * ∑ d ∈ Finset.Ioo 0 r,
        if lam.parts = (rho.parts.erase r) + {d, r - d} then 1 else 0).sum) +
  (1 + b) / 2 * ((rho.parts.map fun (r : ℕ) =>
    ((rho.parts.erase r).map fun (s : ℕ) =>
      (r : K) * (s : K) *
        if lam.parts = ((rho.parts.erase r).erase s) + {r + s} then 1 else 0).sum).sum) +
  b * ((rho.parts.map fun (r : ℕ) => (Nat.choose r 2 : K)).sum) *
    (if lam = rho then 1 else 0)


/-- The literal native operator has the occurrence row, for every actual output. -/
theorem native_row (b : RatFunc ℂ) {k : ℕ} (lam : Nat.Partition k) (p : P k) :
    S b k (indicator lam) p = rowCoefficient b (ct p) lam := by
  rw [native_counted_join_row, native_cut_count]
  simp only [rowCoefficient, indicator, eq_comm]

/-- C1 with the concrete coefficients c_lambda(rho) = rowCoefficient X rho lambda. -/
theorem native_C1 (k : ℕ) (lam : Nat.Partition k) :
    S (RatFunc.X : RatFunc ℂ) k (indicator lam) =
      fun p => rowCoefficient (RatFunc.X : RatFunc ℂ) (ct p) lam := by
  funext p
  exact native_row _ lam p




end D5.S3.Combinatorics.PerfectMatchings.DeformedJucysMurphyRow
