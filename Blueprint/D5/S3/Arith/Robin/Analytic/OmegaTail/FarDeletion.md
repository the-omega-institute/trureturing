# Far deletion at the second distinct-prime threshold

## Abstract

Centered prime excess and the logarithmic reserve retained after far deletion.

**Definition 1.1 (Continuous threshold).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaTail/FarDeletion.centeredThreshold`

*Formalization.* `D5/S3/Arith/Robin/Analytic/OmegaTail/FarDeletion.centeredThreshold` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At a real cutoff P, put l = log(P) and a(P) = P/l + P/l^2.

**Definition 1.2 (Strict rounded count).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaTail/FarDeletion.centeredCount`

*Formalization.* `D5/S3/Arith/Robin/Analytic/OmegaTail/FarDeletion.centeredCount` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Use the second-order selection count with parameter one at exp(P). For P > 1 this is k(P) = floor(a(P)) + 1, including integer values of a(P).

**Definition 1.3 (Real prime excess).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaTail/FarDeletion.primeExcess`

*Formalization.* `D5/S3/Arith/Robin/Analytic/OmegaTail/FarDeletion.primeExcess` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The difference e(P) = pi(P) - k(P) uses the number of primes at most P.

**Definition 1.4 (Natural deletion count).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaTail/FarDeletion.deletionCount`

*Formalization.* `D5/S3/Arith/Robin/Analytic/OmegaTail/FarDeletion.deletionCount` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The deletion cardinality is the natural subtraction pi(P) - k(P). Eventually its real cast equals e(P).

**Definition 1.5 (Continuous reserve).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaTail/FarDeletion.continuousReserve`

*Formalization.* `D5/S3/Arith/Robin/Analytic/OmegaTail/FarDeletion.continuousReserve` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The continuous reserve B0(P) is P - theta(P) + (pi(P) - a(P))*l.

**Definition 1.6 (Rounded reserve).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaTail/FarDeletion.roundedReserve`

*Formalization.* `D5/S3/Arith/Robin/Analytic/OmegaTail/FarDeletion.roundedReserve` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The rounded reserve Bk(P) is P - theta(P) + e(P)*l.

**Definition 1.7 (Far deletion reserve).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaTail/FarDeletion.safeReserve`

*Formalization.* `D5/S3/Arith/Robin/Analytic/OmegaTail/FarDeletion.safeReserve` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The reserve Dsafe(P) is P - theta(P) + e(P)*log(P/2).

**Theorem 1.8 (Centered prime and reserve limits).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaTail/FarDeletion.centered_reserve`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/OmegaTail/FarDeletion.centered_reserve` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

As the real cutoff P tends to infinity, e(P)/(P/l^3) tends to 2. On P > 1 the rounding error k(P) - a(P) is strictly positive and at most one. Eventually e(P) is nonnegative and is the real cast of the deletion count. Each of B0(P), Bk(P) and Dsafe(P), divided by P/l^2, tends to 2.

Subtract the first two terms of the frozen prime-counting expansion and divide by P/l^3. The fourth term and the normalized remainder tend to zero. The floor error is bounded on the same scale. The theta error divided by P/l^2 tends to zero, and log(P/2)/l tends to one.

**Theorem 1.9 (Existence and uniform log budget).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaTail/FarDeletion.far_deletion`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/OmegaTail/FarDeletion.far_deletion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every sufficiently large real P, the window J(P) consists of the primes in (P/2, 3P/4]. It admits a subset R of size e(P). For every such R, the primes at most P outside R number exactly k(P), and the sum of their logarithms is at most P - Dsafe(P).

On the common scale P/l the window capacity tends to 1/4 and the deletion count tends to zero. Every deleted prime contributes at least log(P/2), so subtracting the removed sum from theta(P) gives the uniform budget. The argument allows either sign of P - theta(P).

## References

- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaTail/FarDeletion.centeredCount`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaTail/FarDeletion.centeredThreshold`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaTail/FarDeletion.centered_reserve`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaTail/FarDeletion.continuousReserve`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaTail/FarDeletion.deletionCount`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaTail/FarDeletion.far_deletion`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaTail/FarDeletion.primeExcess`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaTail/FarDeletion.roundedReserve`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaTail/FarDeletion.safeReserve`
- Dependency: [D5/S3/Arith/Robin/Analytic/OmegaTail/Selection](Selection.md)
