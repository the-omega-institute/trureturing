/- GID: D5/S1/Recurrence/Invariants/HannaSigmaProductExpModThreeCube
   generality: I
   mirror-B: D5/B/S1/Recurrence/Invariants/HannaSigmaProductExpModThreeCube
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The cubed sigma-product exponential has the Frobenius residue pattern. -/

/-
proof_shape: content (result), by inlining same-delivery helpers.
escape_witness: none.
admission_basis: open-problem-resolution (#18864; Proved).
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/19891
Direct frozen dependencies after inlining same-delivery helpers:
HannaLogarithmicPowerClosure.IntegralSeries;
CubicFifteenSubstitutionParity.prime_power_subst;
LinearExponentDyadicSupport.pow_change;
ParametricExponentialSquareCongruence.linear_ode_unique.
The claim is the conjunction stated in issue #18864 under rational coefficient
and integer congruence notation; the namespace follows this module.
utility: none; no finite certificate is used.
-/

import D5.S1.Recurrence.Invariants.HannaSigmaProductExpModThree
namespace D5.S1.Recurrence.Invariants.HannaSigmaProductExpModThreeCube

open PowerSeries D5.S1.Recurrence.Invariants.HannaSigmaProductExpModThree

/-- OEIS A382125 (P. D. Hanna), conjectures: "a(3*n) == A382124(n) (mod 3) for n >= 0; a(3*n+1) == 0
(mod 3) and a(3*n+2) == 0 (mod 3) for n >= 0". The terms are integers. -/
def claim : Prop :=
  (∀ n : ℕ, ∃ u v : ℤ, coeff (3 * n) B = u ∧ coeff n A = v ∧ u ≡ v [ZMOD 3]) ∧
    ∀ n : ℕ, ∃ u v : ℤ, coeff (3 * n + 1) B = u ∧ coeff (3 * n + 2) B = v ∧
      u ≡ 0 [ZMOD 3] ∧ v ≡ 0 [ZMOD 3]

end D5.S1.Recurrence.Invariants.HannaSigmaProductExpModThreeCube

namespace D5.S1.Recurrence.Invariants.HannaSigmaProductExpModThreeCube
open PowerSeries D5.S1.Recurrence.Invariants.HannaSigmaProductExpModThree

theorem result : claim := by
  constructor
  · intro n
    obtain ⟨u,v,hu,hv,hc⟩ := D5.S1.Recurrence.Invariants.HannaSigmaProductExpModThree.result n
    exact ⟨v,u,hv,hu,hc.symm⟩
  · intro n
    refine ⟨coeff (3*n+1) (integerSeries ^ 3), coeff (3*n+2) (integerSeries ^ 3),
      ?_, ?_, (cube_residues n).2.1, (cube_residues n).2.2⟩
    · rw [← integerCube_map, coeff_map]
      rfl
    · rw [← integerCube_map, coeff_map]
      rfl

end D5.S1.Recurrence.Invariants.HannaSigmaProductExpModThreeCube
