/- GID: D5/S1/Recurrence/Invariants/HannaLambertCubeModThreeConverse
   generality: G
   mirror-B: D5/B/S1/Recurrence/Invariants/HannaLambertCubeModThreeConverse
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The reciprocal reading gives Hanna's A382319 congruence modulo three. -/

/-
result:
  proof_shape: bind-only
  escape_witness: none
  admission_basis: open-problem-resolution (#18862; Proved)
Direct frozen dependencies (declaration statement_id, with same-delivery proofs expanded):
  D5/S1/Recurrence/Invariants/CubicFifteenSubstitutionParity.Agree
    sha256:e3cd9c09ab9c066077e3362c2145b9293441e263c1e4e0df7614ff40a3b1cb53;
  D5/S1/Recurrence/Invariants/CubicFifteenSubstitutionParity.agree_cube
    sha256:09f85dfa6fb94a0d91925170e623f1fc09a77c37573ca8ef780549de2ba54b7c;
  D5/S1/Recurrence/Invariants/CubicTernarySubstitutionParity.cube_congr_subst_three
    sha256:14abc582a4381fc7ae3eb29f70d25ef7066b4ebeb5ab09bbf99cfbb70914eab0.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/19096.
The proof applies HannaLambertCubeModThree.result and Int.ModEq.symm.
-/

import D5.S1.Recurrence.Invariants.HannaLambertCubeModThree

namespace D5.S1.Recurrence.Invariants.HannaLambertCubeModThreeConverse

open PowerSeries D5.S1.Recurrence.Invariants.HannaLambertCubeModThree

/-- OEIS A382319 (P. D. Hanna), conjecture: "a(n) == A382318(3*n) (mod 3) for n >= 0". The terms are
integers. -/
def claim : Prop :=
  (∃ A B, IsA382318 A ∧ IsA382319 B) ∧
    ∀ A B, IsA382318 A → IsA382319 B →
      ∀ n : ℕ, ∃ u v : ℤ, coeff n B = u ∧ coeff (3 * n) A = v ∧ u ≡ v [ZMOD 3]

end D5.S1.Recurrence.Invariants.HannaLambertCubeModThreeConverse

namespace D5.S1.Recurrence.Invariants.HannaLambertCubeModThreeConverse
open PowerSeries D5.S1.Recurrence.Invariants.HannaLambertCubeModThree

theorem result : claim := by
  refine ⟨D5.S1.Recurrence.Invariants.HannaLambertCubeModThree.result.1, ?_⟩
  intro A B hA hB n
  obtain ⟨u,v,hu,hv,hm⟩ := (D5.S1.Recurrence.Invariants.HannaLambertCubeModThree.result.2 A B hA hB).1 n
  exact ⟨v,u,hv,hu,hm.symm⟩

end D5.S1.Recurrence.Invariants.HannaLambertCubeModThreeConverse
