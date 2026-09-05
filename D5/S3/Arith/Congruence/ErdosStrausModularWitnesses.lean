/- GID: D5/S3/Arith/Congruence/ErdosStrausModularWitnesses
   generality: I
   mirror-B: D5/B/S3/Arith/Congruence/ErdosStrausModularWitnesses
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Five modular families have explicit positive Erdős--Straus witnesses. -/

import Mathlib.Tactic

/- Library-search audit trail (2026-09-05):
   * Repository searches for Erdős--Straus, Egyptian fractions, reciprocal triples,
     the five congruence classes, and the underlying rational identities found no
     equivalent frozen theorem. `PrimaryPseudoperfectPorts` concerns a different
     Egyptian-fraction characterization.
   * Digest, Blueprint, exact-module, generalized arithmetic, and all refreshed
     in-flight branch searches found no equivalent declaration or module.
   * Pinned Mathlib contains no Erdős--Straus witness family. The proof therefore
     constructs the requested denominators and verifies their rational identities
     with `field_simp` and `ring`.
   * Escape witness: the five parameterized rational calculations below are new
     explicit constructions, not consequences obtained by binding frozen facts. -/

namespace D5.S3.Arith.Congruence.ErdosStrausModularWitnesses

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Positive natural denominators solving the Erdős--Straus reciprocal equation. -/
def IsErdosStrausWitness (n x y z : ℕ) : Prop :=
  0 < n ∧ 0 < x ∧ 0 < y ∧ 0 < z ∧
    (4 : ℚ) / (n : ℚ) =
      1 / (x : ℚ) + 1 / (y : ℚ) + 1 / (z : ℚ)

/-- Explicit witnesses cover even integers, multiples of three, and the residue
classes two modulo three, three modulo four, and five modulo eight. The final
three clauses record the requested small-value checks. -/
theorem erdos_straus_modular_witnesses :
    (∀ q : ℕ, 0 < q →
      IsErdosStrausWitness (2 * q) q (2 * q) (2 * q)) ∧
    (∀ q : ℕ, 0 < q →
      IsErdosStrausWitness (3 * q) q (4 * q) (12 * q)) ∧
    (∀ k : ℕ,
      IsErdosStrausWitness (3 * k + 2) (k + 1) (3 * k + 2)
        ((3 * k + 2) * (k + 1))) ∧
    (∀ k : ℕ,
      IsErdosStrausWitness (4 * k + 3) (k + 1)
        (2 * (4 * k + 3) * (k + 1))
        (2 * (4 * k + 3) * (k + 1))) ∧
    (∀ k : ℕ,
      IsErdosStrausWitness (8 * k + 5) (2 * k + 2)
        ((8 * k + 5) * (k + 1))
        (2 * (8 * k + 5) * (k + 1))) ∧
    IsErdosStrausWitness 2 1 2 2 ∧
    IsErdosStrausWitness 5 2 5 10 ∧
    IsErdosStrausWitness 7 2 28 28 := by
  constructor
  · intro q hq
    refine ⟨by omega, hq, by omega, by omega, ?_⟩
    field_simp
    push_cast
    ring
  constructor
  · intro q hq
    refine ⟨by omega, by omega, by omega, by omega, ?_⟩
    field_simp
    push_cast
    ring
  constructor
  · intro k
    refine ⟨by omega, by omega, by omega, by positivity, ?_⟩
    field_simp
    push_cast
    ring
  constructor
  · intro k
    refine ⟨by omega, by omega, by positivity, by positivity, ?_⟩
    field_simp
    push_cast
    ring
  constructor
  · intro k
    refine ⟨by omega, by omega, by positivity, by positivity, ?_⟩
    field_simp
    push_cast
    ring
  norm_num [IsErdosStrausWitness]

#print axioms erdos_straus_modular_witnesses

end D5.S3.Arith.Congruence.ErdosStrausModularWitnesses
