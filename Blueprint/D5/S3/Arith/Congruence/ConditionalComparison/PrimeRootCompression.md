# Prime-Root Compression and Original Inventory

## Abstract

An injection avoiding actual prime-root incidences compresses a whole odd distinct cover. Counting the original labels that obstruct this injection gives a lower bound in every count-minimal cover containing the two pure prime labels.

**Theorem 1.1 (An avoiding injection produces a smaller whole cover).**

Lean statement: `D5/S3/Arith/Congruence/ConditionalComparison/PrimeRootCompression.prime_root_compression`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/ConditionalComparison/PrimeRootCompression.prime_root_compression` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let F cover all natural numbers by n congruence classes with pairwise distinct odd moduli greater than one. Let p and q be distinct primes, with actual original indices donor and guard of moduli p and q. Let B consist of the first q-roots other than the guard's actual residue modulo q, and let sigma be an injection from B to the first p-roots.

Assume two avoidance conditions. For every b in B and every original whose modulus is divisible by both p and q and whose first q-root is b, sigma(b) differs from that original's first p-root. Also, for every actual pair of original numerical moduli p u and q u with u coprime to p q, sigma(b) differs from the p u original's first p-root for every b in B. Then there exist N less than n and an odd distinct covering system with N classes.

Factor the original common modulus as p^A R with p coprime to R. For every output point x outside the guard root, use one common Chinese-remainder source congruent to sigma(x modulo q) + p x modulo p^A and to x modulo R. Retain all p-free originals unchanged. Every mixed p q original has empty inverse. Each q-free p-bearing original of modulus p^a u with nonempty inverse gives one enclosing class of modulus q p^(a-1) u, with residue chosen from an actual inverse point. Injectivity of sigma and modular cancellation prove this enclosure using the full original cofactor phase.

The retained guard covers its entire root. Elsewhere, an original owner of the common source supplies an output owner. Cancellation proves distinctness of new labels; a new label equal to a retained label would be an excluded actual pair p u, q u. The pair with u equal to one makes the pure p donor inactive. All retained and transported labels are odd and greater than one, and the active original indices therefore give a strictly smaller cover.

The construction permits arbitrary original prime heights and literal, unnormalized residues. It requires neither an ordering of p and q nor a minimality assumption. Its conclusion is a strict class-count decrease, without a modulus-sum assertion.

**Theorem 1.2 (A total forbidden-incidence budget supplies a matching).**

Lean statement: `D5/S3/Arith/Congruence/ConditionalComparison/PrimeRootCompression.exists_injective_avoiding_of_forbidden_sum_lt`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/ConditionalComparison/PrimeRootCompression.exists_injective_avoiding_of_forbidden_sum_lt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let I be a finite type, let alpha be any type, let R be a finite subset of alpha, and assign a finite forbidden set F(i) to each i in I. If the cardinality of I is at most that of R and the sum of the cardinalities of F(i) is strictly less than the cardinality of R, there is an injective map f from I to alpha with f(i) in R and outside F(i) for every i. The forbidden sets need not be subsets of R.

Apply the finite Hall theorem to the allowed sets R minus F(i). If a subfamily S has too few neighbors N, every point of R minus N is forbidden for every member of S. The resulting rectangle has at least as many incidences as R has points, contradicting the strict total budget. This matching criterion is used below for the actual mixed-root exclusions.

**Theorem 1.3 (A minimal cover needs enough smaller-prime labels).**

Lean statement: `D5/S3/Arith/Congruence/ConditionalComparison/PrimeRootCompression.prime_bearing_count_lower`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/ConditionalComparison/PrimeRootCompression.prime_bearing_count_lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let F be an odd distinct covering system with n classes, and assume every odd distinct covering system with N classes has n at most N. Let p and q be primes with q less than p, and suppose F has actual original indices of moduli p and q. Then at least p minus q plus two original moduli are divisible by q. All original moduli and residues belong to this one F.

Partition the q-bearing originals into the p-free set C and the mixed set M. Every actual numerical pair p u, q u with u coprime to p q is paid by its q u member in C. Distinctness of the original labels makes its p u mate unique, so the reserved p-roots number at most the cardinality of C. Each member of M has just one first q-root and one first p-root; consequently the total mixed forbidden incidence over all non-guard q-roots is at most the cardinality of M.

If the q-bearing inventory were at most p minus q plus one, the unreserved p-roots would suffice for all non-guard q-roots, and the mixed forbidden incidence would be strictly smaller than their number. The matching criterion supplies the injection required by prime-root compression, contradicting global minimum class count. The bound uses disjoint parts of the same original inventory and assumes no exponent cap or modulus-sum minimality.

## References

- Truth anchor: `D5/S3/Arith/Congruence/ConditionalComparison/PrimeRootCompression.exists_injective_avoiding_of_forbidden_sum_lt`
- Truth anchor: `D5/S3/Arith/Congruence/ConditionalComparison/PrimeRootCompression.prime_bearing_count_lower`
- Truth anchor: `D5/S3/Arith/Congruence/ConditionalComparison/PrimeRootCompression.prime_root_compression`
