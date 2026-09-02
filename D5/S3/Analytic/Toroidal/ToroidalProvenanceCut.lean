/- GID: D5/S3/Analytic/Toroidal/ToroidalProvenanceCut
   generality: G
   mirror-B: D5/B/S3/Analytic/Toroidal/ToroidalProvenanceCut
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A selected nonzero twist makes period vanishing equivalent to base vanishing. -/

import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Data.Finset.Basic

/- Library-search audit trail (2026-09-02):
   * Exact searches for `ToroidalVanishingProfile`,
     `toroidalVanishingProfile`, `toroidal_provenance_cut`, and `twistZero`
     missed in both D5 and pinned Mathlib.
   * The `periodZero` search hits a proof-local `have` in
     `FiniteToroidalSpectralTomography`; it is not an addressable declaration.
   * Shape searches for a selected index, a period/base/twist factorization,
     and filtered zero membership found no addressable equal-or-stronger D5
     declaration. `toroidal_common_zero_locus` is instead a global set equality
     quantified over every index under pointwise family nonvanishing.
   * `rh_iff_all_toroidal_eisenstein_tempered` uses `mul_eq_zero` internally;
     that proof-local fact is not an addressable per-index characterization.
   * Pinned Mathlib supplies the exact constituents `mul_eq_zero` and
     `Finset.mem_filter`, which are used directly below. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Analytic.Toroidal.ToroidalProvenanceCut

/-- The selected toroidal indices and the two zero profiles at one point. -/
structure ToroidalVanishingProfile (Index : Type*) [DecidableEq Index] where
  selected : Finset Index
  periodZero : Finset Index
  twistZero : Finset Index

/-- Filter a selected family by period and twist vanishing at `s`. -/
def toroidalVanishingProfile
    {Index Point Scalar : Type*} [DecidableEq Index] [DecidableEq Scalar]
    [Zero Scalar] (selected : Finset Index)
    (period twist : Index → Point → Scalar) (s : Point) :
    ToroidalVanishingProfile Index where
  selected := selected
  periodZero := selected.filter fun i => period i s = 0
  twistZero := selected.filter fun i => twist i s = 0

/-- At a selected index with nonzero twist, the period-zero cut records exactly
base vanishing and certifies that the twist-zero profile does not contain the
index. -/
theorem toroidal_provenance_cut
    {Index Point Scalar : Type*} [DecidableEq Index] [DecidableEq Scalar]
    [MulZeroClass Scalar] [NoZeroDivisors Scalar]
    (selected : Finset Index) (period twist : Index → Point → Scalar)
    (base : Point → Scalar) (s : Point) (i : Index)
    (hi : i ∈ selected) (hfac : period i s = base s * twist i s)
    (htw : twist i s ≠ 0) :
    (i ∈ (toroidalVanishingProfile selected period twist s).periodZero ↔
        base s = 0) ∧
      i ∉ (toroidalVanishingProfile selected period twist s).twistZero := by
  constructor
  · constructor
    · intro hmem
      have hperiod := (Finset.mem_filter.mp hmem).2
      have hproduct : base s * twist i s = 0 := hfac.symm.trans hperiod
      exact (mul_eq_zero.mp hproduct).resolve_right htw
    · intro hbase
      exact Finset.mem_filter.mpr
        ⟨hi, hfac.trans (mul_eq_zero.mpr (Or.inl hbase))⟩
  · intro hmem
    exact htw (Finset.mem_filter.mp hmem).2

-- A concrete inhabitant of the profile carrier.
example : Nonempty (ToroidalVanishingProfile Bool) :=
  ⟨{
    selected := ∅
    periodZero := ∅
    twistZero := ∅
  }⟩

-- Concrete data witnessing simultaneous satisfiability of the hypotheses.
example :
    let selected : Finset Bool := {true}
    let period : Bool → Unit → Nat := fun _ _ => 6
    let twist : Bool → Unit → Nat := fun _ _ => 3
    let base : Unit → Nat := fun _ => 2
    true ∈ selected ∧
      period true () = base () * twist true () ∧ twist true () ≠ 0 := by
  decide

#print axioms toroidal_provenance_cut

end D5.S3.Analytic.Toroidal.ToroidalProvenanceCut
