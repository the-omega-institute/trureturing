# Unbounded four-prime tails, equality families and the old-method boundary.

## Abstract

Unbounded four-prime tails, equality families and the old-method boundary.

The same PR9 repeated-pair-product-tail source supplies these exact identities. All real a>=2 and all boundary parameters are included. For four arbitrary distinct primes and all positive integer a,b,c with b,c>=2a squared minus one, the actual ideal graph has an eigenvalue strictly between V-1 and V. The a=1 case is included: the general product inequality reduces to bc>0 for all positive tails. For a>=2, the natural truncated-subtraction bound transports exactly to the real uniform-tail inequality. These are applications of the general product theorem on all nonzero proper ideals. Failed sufficient criteria are not necessary-and-sufficient integrality tests.

**Theorem 1.1 (The exact four-prime inequality).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/Nikandish/RepeatedPairProductArithmetic.four_criterion`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/Nikandish/RepeatedPairProductArithmetic.four_criterion` (`✓ std3`). ∎

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

The general product condition is algebraically equivalent to bc >= (a squared minus one)(b+c)+(a-1)(2a-1), over all real parameters.

**Theorem 1.2 (The full uniform tail).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/Nikandish/RepeatedPairProductArithmetic.uniform_tail`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/Nikandish/RepeatedPairProductArithmetic.uniform_tail` (`✓ std3`). ∎

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

For every real a>=2 and b,c>=2a squared minus one, the four-prime criterion holds strictly, including both parameter boundaries.

**Theorem 1.3 (The entire equality family).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/Nikandish/RepeatedPairProductArithmetic.equality_family`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/Nikandish/RepeatedPairProductArithmetic.equality_family` (`✓ std3`). ∎

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

For every real a>=2, b=a squared and c=a to the fourth plus a squared minus 3a plus one are positive and satisfy the exact equality. This is an unbounded identity, not a fixed control.

**Theorem 1.4 (Every coordinate fails the earlier criterion).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/Nikandish/RepeatedPairProductArithmetic.old_criterion_fails`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/Nikandish/RepeatedPairProductArithmetic.old_criterion_fails` (`✓ std3`). ∎

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

For every real a>=2 the complete vector (a,a,2a squared minus one,2a squared minus one) fails all four choices of the earlier distinguished-coordinate sufficient criterion. The two source shifted-polynomial positivity identities prove the whole family. Failure of this earlier method asserts no integrality or priority.

## References

- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/Nikandish/RepeatedPairProductArithmetic.equality_family`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/Nikandish/RepeatedPairProductArithmetic.four_criterion`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/Nikandish/RepeatedPairProductArithmetic.old_criterion_fails`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/Nikandish/RepeatedPairProductArithmetic.uniform_tail`
- Dependency: [D5/S3/Combinatorics/SpectralGraph/Nikandish/RepeatedPairProductSpectrum](RepeatedPairProductSpectrum.md)
