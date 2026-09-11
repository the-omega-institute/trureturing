/- GID: D5/S0/Certificates/DebSokalConjectureFourRefutation
   generality: I
   mirror-B: D5/B/S0/Certificates/DebSokalConjectureFourRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: [mathlib/module/Mathlib.Algebra.Polynomial.Eval.Defs, mathlib/module/Mathlib.Algebra.QuadraticDiscriminant, mathlib/module/Mathlib.Analysis.Complex.Order, mathlib/module/Mathlib.Data.Nat.Choose.Basic, mathlib/module/Mathlib.Tactic.NormNum, mathlib/module/Mathlib.Tactic.Ring]
   utility: kind=certified-instance; basis=refutes=gid:D5/S0/Certificates/DebSokalConjectureFourRefutation.claim; result=D5/S0/Certificates/DebSokalConjectureFourRefutation.result; claim=D5/S0/Certificates/DebSokalConjectureFourRefutation.claim
   digest: Refutes the printed universal non-real-zero clause of Deb--Sokal Conjecture 1.4(c), arXiv:2507.18959v1, at (r,n)=(3,3); literature-attested in Deb's 2023 UCL thesis section 6.5, not a new counterexample; Corollary 7.3 covers r>=4,n>=3 and the r=3 evidence starts at n>=4, whose restricted proposition is not refuted here. -/

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Analysis.Complex.Order
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Certificates.DebSokalConjectureFourRefutation

open Polynomial
open scoped BigOperators ComplexOrder

/-!
Deb--Sokal, arXiv:2507.18959v1, printed p.10, Conjecture 1.4(c): the
row-generating subset polynomials "have non-real complex zeros for r >= 3
and n >= 3". The claim below is precisely this universal clause; the separate
r=1,2 and log-concavity clauses are not needed for its refutation.

The numbers are defined by the paper's Lemma 1.1(b), equation (1.14), p.7.
Its initial conditions and recurrence determine them for every positive r.
The natural-number definition also gives an unused extension at r=0.
The k=0 successor row is zero, as the paper's k=-1 boundary requires.
Equation (1.18) defines the row polynomial by summing k=0,...,n.

Independent integer recomputation gives rows [1], [0,1], [0,1,10],
[0,1,35,280] at r=3. The last agrees with Appendix A.2, p.47:
35 = choose(6,2)*1 + 2*10 and 280 = choose(8,2)*10 + 3*0.
All finite certificates below are proof-local and kernel checked.

Provenance: literature-attested, independently checked on 2026-09-10.
Deb, Enumerative combinatorics, continued fractions and total positivity,
UCL PhD thesis (2023), section 6.5, p.281, explicitly records that s_(3,3)
has real zeroes and s_(3,4) has complex zeroes. This formalizes the falsity
of the printed 2025 universal clause, not the discovery of a new counterexample.
Corollary 7.3 of the paper, p.40, covers r>=4,n>=3, and the following r=3
computational remark starts at n>=4. The authors may have intended that
restricted range; this module makes no claim that it is false.
-/

/-- Higher-order Stirling subset numbers, via (1.14) and its initial conditions. -/
def stirlingSubset (r : ℕ) : ℕ → ℕ → ℕ :=
  Nat.rec (fun k => if k = 0 then 1 else 0) (fun n previous k =>
    match k with
    | 0 => 0
    | k + 1 =>
        (n + (r - 1) * (k + 1)).choose (r - 1) * previous k +
          (k + 1) * previous (k + 1))

/-- The row-generating polynomial s_(r,n) of equation (1.18), over the complex numbers. -/
noncomputable def rowPolynomial (r n : ℕ) : ℂ[X] :=
  ∑ k ∈ Finset.range (n + 1), C (stirlingSubset r n k : ℂ) * X ^ k

/-- The printed non-real-zero clause, with its complete universal range. -/
def claim : Prop :=
  ∀ r n : ℕ, 3 ≤ r → 3 ≤ n →
    ∃ z : ℂ, (rowPolynomial r n).eval z = 0 ∧ z.im ≠ 0

/-- The eligible row (3,3) has only real zeros, contradicting the printed clause. -/
theorem result : ¬ claim := by
  intro h
  obtain ⟨z, hz, hnonreal⟩ := h 3 3 (by decide) (by decide)
  -- Compute from the recurrence, not from an assumed table of coefficients.
  have values : stirlingSubset 3 3 0 = 0 ∧ stirlingSubset 3 3 1 = 1 ∧
      stirlingSubset 3 3 2 = 35 ∧ stirlingSubset 3 3 3 = 280 := by
    decide +kernel
  have row_eval : (rowPolynomial 3 3).eval z =
      z * (280 * (z * z) + 35 * z + 1) := by
    norm_num [rowPolynomial, Finset.sum_range_succ, values.1, values.2.1,
      values.2.2.1, values.2.2.2]
    ring
  rw [row_eval] at hz
  rcases mul_eq_zero.mp hz with hzero | hquad
  · exact hnonreal (by simp [hzero])
  · have hsquare := discrim_eq_sq_of_quadratic_eq_zero hquad
    -- The entire discriminant certificate is exact integer arithmetic.
    norm_num [discrim] at hsquare
    have him : (560 * z + 35).im = 0 :=
      Complex.sq_nonneg_iff.mp (by rw [← hsquare]; norm_num [Complex.nonneg_iff])
    norm_num [Complex.add_im, Complex.mul_im] at him
    exact hnonreal him

#print axioms claim
#print axioms result

end D5.S0.Certificates.DebSokalConjectureFourRefutation
