# The subcubic model size

## Abstract

The subcubic model size

The actual duplicate-free clause family has at most (d+1)n members at maximum degree d. In a subcubic graph each clause has at most five vertices; the exact binary model uses at most 5n variables and 9n displayed constraints. These counts refer to the actual clause sets and feasibility predicate in ClauseModel.

**Theorem 1.1 (clauses card le).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/ClauseSizes.clauses_card_le`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/ClauseSizes.clauses_card_le` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem clauses_card_le (d : ℕ) (hd : ∀ v, DegreeCapacity.degree G v ≤ d) : (clauses G).card ≤ (d+1)*Fintype.card V.

**Theorem 1.2 (subcubic clause size).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/ClauseSizes.subcubic_clause_size`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/ClauseSizes.subcubic_clause_size` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem subcubic_clause_size (hd : ∀ v, DegreeCapacity.degree G v ≤ 3) (E : Finset V) (hE : E ∈ clauses G) : E.card ≤ 5.

**Theorem 1.3 (subcubic model size).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/ClauseSizes.subcubic_model_size`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/ClauseSizes.subcubic_model_size` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem subcubic_model_size (hd : ∀ v, DegreeCapacity.degree G v ≤ 3) : (clauses G).card ≤ 4*Fintype.card V ∧ Fintype.card V + (clauses G).card ≤ 5*Fintype.card V ∧ 2*(clauses G).card + Fintype.card V ≤ 9*Fintype.card V.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/ClauseSizes.clauses_card_le`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/ClauseSizes.subcubic_clause_size`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/ClauseSizes.subcubic_model_size`
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/ClauseModel](ClauseModel.md)
