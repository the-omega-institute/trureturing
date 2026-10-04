/- GID: D5/S1/Words/KAbelianLagrange/KAbelianLagrangeDefs
   generality: G
   mirror-B: D5/B/S1/Words/KAbelianLagrange/KAbelianLagrangeDefs
   mirror-E: none(waiver:k-abelian-lagrange-spectrum-statement-definition)
   anchors: [mathlib/module/Mathlib.NumberTheory.Real.Irrational, mathlib/module/Mathlib.Order.LiminfLimsup, mathlib/module/Mathlib.Data.ENNReal.Inv]
   utility: none
   digest: Peltomäki and Whiteland's k-abelian Lagrange spectrum of Sturmian words and its half-line question. -/

import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Order.LiminfLimsup
import Mathlib.Data.ENNReal.Inv
import D5.S1.Words.Mechanical.MechanicalFactorComplexity

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.KAbelianLagrange.KAbelianLagrangeDefs

open scoped ENNReal

/-! Fixed public statement: J. Peltomäki and M. A. Whiteland, *On k-abelian equivalence and
    generalized Lagrange spectra*, Acta Arith., arXiv:1809.09047v2, Section 3.2.  Two finite
    words are k-abelian equivalent when every nonempty word of length at most k occurs in them
    equally often.  For a Sturmian word of irrational slope α, `Ae(k,α,m)` is the largest e such
    that the word contains e consecutive pairwise k-abelian equivalent blocks of length m,
    `Ac_k(α) = limsup_m Ae(k,α,m)/m`, and `L_k` is the set of finite values of `Ac_k` over
    irrational slopes in (0,1).  The Question after Theorem 3.15 asks whether `L_k` contains a
    half-line when k > 1.  All Sturmian words of one irrational slope have the same factors, so
    the lower mechanical word `D5.S1.Words.Mechanical.lowerMechanicalWord α 0` of intercept zero
    represents the slope, and its blocks are `lowerMechanicalFactor α 0 m start`. -/

open D5.S1.Words.Mechanical

/-- Number of (possibly overlapping) occurrences of `v` in `u`. -/
def occurrences (u v : List Bool) : ℕ :=
  ((List.range (u.length + 1)).filter fun i =>
    i + v.length ≤ u.length ∧ (u.drop i).take v.length = v).length

/-- k-abelian equivalence of finite binary words. -/
def KAbelianEq (k : ℕ) (u v : List Bool) : Prop :=
  ∀ z : List Bool, 0 < z.length → z.length ≤ k → occurrences u z = occurrences v z

/-- The Sturmian word of slope `α` has `e` consecutive pairwise k-abelian equivalent blocks of
    length `m` starting at `start`. -/
def IsKAbelianPower (α : ℝ) (k m e start : ℕ) : Prop :=
  ∀ i j : ℕ, i < e → j < e →
    KAbelianEq k (lowerMechanicalFactor α 0 m (start + i * m))
      (lowerMechanicalFactor α 0 m (start + j * m))

/-- `Ae(k,α,m)`: the largest number of consecutive pairwise k-abelian equivalent blocks of
    length `m` in the Sturmian word of slope `α` (taken as `0` for `m = 0`). -/
noncomputable def ae (k : ℕ) (α : ℝ) (m : ℕ) : ℕ :=
  if m = 0 then 0 else sSup {e : ℕ | ∃ start : ℕ, IsKAbelianPower α k m e start}

/-- `Ac_k(α) = limsup_m Ae(k,α,m)/m`, valued in `[0,∞]`. -/
noncomputable def ac (k : ℕ) (α : ℝ) : ℝ≥0∞ :=
  Filter.limsup (fun m : ℕ => (ae k α m : ℝ≥0∞) / (m : ℝ≥0∞)) Filter.atTop

/-- `L_k`: the finite values of `Ac_k` at irrational slopes in `(0,1)`. -/
def spectrum (k : ℕ) : Set ℝ :=
  {t | ∃ α : ℝ, Irrational α ∧ 0 < α ∧ α < 1 ∧ ac k α ≠ ⊤ ∧ (ac k α).toReal = t}

/-- The Question after Theorem 3.15, existence form: for every `k ≥ 2` the spectrum `L_k`
    contains a half-line. -/
def claim : Prop :=
  ∀ k : ℕ, 2 ≤ k → ∃ B : ℝ, Set.Ioi B ⊆ spectrum k

end D5.S1.Words.KAbelianLagrange.KAbelianLagrangeDefs
