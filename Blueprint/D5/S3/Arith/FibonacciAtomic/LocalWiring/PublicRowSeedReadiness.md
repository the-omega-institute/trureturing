# Sharp readiness when only the seed of a public row is unknown

## Abstract

When the binary recurrence width and coefficient row are authentic public inputs, only the finite seed must be learned. Its exact readiness threshold is the length of the mature physical birth prefix.

**Theorem 1.1 (Exactly enough mature bits for each of the three readiness tasks).**

$$v_{n}=F_{n}-1\ge r\quad (n\ge 2)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/LocalWiring/PublicRowSeedReadiness.public_row_seed_readiness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix the supplied order r and all coefficients. Every Fin r Boolean seed is allowed, even when the row has zero taps or is not a minimal presentation. The finite evaluator consumes XOR of AND products, proved equal to the binary dot product reduced modulo two. Output index zero is birth one, and order zero has the unique all-zero output.

At an attained cut n≥2 with its physical incidence or frontier already acquired, the threshold is equivalent to each of: exact current labels, all actual next-cut presence replies before an update, and the entire finite same-source Read/Update behavior. The inverse of the physical shape supplies the mature prefix; its first r bits install the public row.

A Read admits any physical word and returns only its presence bit. A completed update has the common acknowledgement and yields the actual successor support and labelled tree. Finite adaptive scripts depend only on previous accessible replies and their fixed independent local inputs, not on the task's labelled snapshots.

Below threshold, flip just the first hidden seed bit under the very same row. Current incidence is unchanged, but that birth is already in the labelled tree and is mature at the next cut. Some real physical word then has a different presence reply, so one update and that Read also distinguish finite behaviors. No bound on acquisition cost or identification of a private recurrence presentation is claimed.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/LocalWiring/PublicRowSeedReadiness.public_row_seed_readiness`
- Dependency: [D5/S3/Arith/FibonacciAtomic/LocalWiring/OrderedBirthPrefix](OrderedBirthPrefix.md)
