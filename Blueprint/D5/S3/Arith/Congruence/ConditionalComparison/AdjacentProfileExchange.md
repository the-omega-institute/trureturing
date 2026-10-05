# Adjacent Prime-Height Profile Exchange

## Abstract

Bounds on two adjacent prime-height layers permit one global tail exchange, reducing both the class count and the sum of actual covering moduli while retaining the full old coordinate.

**Theorem 1.1 (One whole replacement contracts every selected q-tail).**

Lean statement: `D5/S3/Arith/Congruence/ConditionalComparison/AdjacentProfileExchange.adjacent_profile_exchange`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/ConditionalComparison/AdjacentProfileExchange.adjacent_profile_exchange` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let finitely many progressions A_i = [r_i] modulo d_i cover all natural numbers, with every d_i greater than one. Repeated and even input moduli are allowed. Let p be an odd prime, q a prime, and H, G, W, k, A, B natural numbers. Suppose W is coprime to p q and every d_i divides p^H q^G W.

Assume every original with q-height greater than k has p-height at most A, and every original with q-height equal to k has p-height at most B. Fix an actual original donor of numerical modulus q^(k+1). If p^(A+B+1) is less than q, there is one finite output family covering all natural numbers, with moduli greater than one, strictly fewer classes, and a strictly smaller sum of numerical moduli. For these same output arrays, injectivity of the input modulus array implies injectivity of the output modulus array, and oddness of every input modulus implies oddness of every output modulus.

One fixed first-digit injection avoids the donor's actual next q digit and is reused for every q^k parent. Later blocks read A+1 base-p digits each. A single Chinese-remainder source uses x modulo q^k as its parent, inserts the encoded q-tail, and preserves x modulo the entire old p^H W. The code reads only the p-prefix needed by the transported originals, even when H exceeds the full code depth.

Every original of q-height at most k remains unchanged. For a deleted original p^a q^(k+t) m, its complete inverse ranges over all natural numbers. Whenever this inverse is nonempty, one chosen witness supplies an enclosure of numerical modulus p^(B+1+(t-1)(A+1)+a) q^k m. Two points of one inverse first recover the same literal parent, then the code prefix and cofactor phase. No private-region or deletion-hole mask is imposed.

The donor has empty inverse because its next digit is excluded. Every other original supplies at most one class, so the actual index set becomes strictly smaller. Coverage follows by taking an original owner of the same source for each output point. Each charged modulus contracts, and the omitted positive donor weight makes the total modulus sum strictly smaller.

A retained label below q-height k has a different q-valuation from every new label. A retained label at height k has p-height at most B, below every new height. Among new labels, quotient and remainder modulo A+1 recover the old p-height and removed q-depth, and cancellation recovers the cofactor. These comparisons prove conditional numerical distinctness. Odd input cofactors and the odd primes prove conditional oddness for the same family.

The theorem assumes neither irredundancy, private-region capacity, divisor closure, nor extremality. H may be zero or exceed the complete code depth; the period assumption is divisibility, not equality with an original least common multiple. A necessary profile inequality requires a separately justified minimality comparison. This exchange alone does not exclude all distinct odd covering systems.

## References

- Truth anchor: `D5/S3/Arith/Congruence/ConditionalComparison/AdjacentProfileExchange.adjacent_profile_exchange`
