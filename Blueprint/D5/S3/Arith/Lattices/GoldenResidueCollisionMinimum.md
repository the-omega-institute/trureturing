# Balanced Residue Collision Minimum

## Abstract

Balanced residue populations exactly minimize the number of colliding pairs.

**Theorem 1.1 (Exact minimum and attaining populations).**

Lean statement: `D5/S3/Arith/Lattices/GoldenResidueCollisionMinimum.balanced_collision_cost_minimum`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/GoldenResidueCollisionMinimum.balanced_collision_cost_minimum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let n objects occupy m residue classes, with m positive, and write n = mq + r with 0 <= r < m. For populations c_i summing to n, twice the number of colliding unordered pairs is the sum of c_i(c_i - 1). This sum is at least mq(q - 1) + 2rq. The lower bound is attained by assigning q + 1 objects to r classes and q objects to each remaining class. At one precision in the golden-tower collision calculation, m is 4^s. The theorem gives that precision's exact minimum; compatibility across precisions and field index claims require separate arguments.

## References

- Truth anchor: `D5/S3/Arith/Lattices/GoldenResidueCollisionMinimum.balanced_collision_cost_minimum`
