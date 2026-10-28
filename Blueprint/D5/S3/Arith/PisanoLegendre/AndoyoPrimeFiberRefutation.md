# An isolated Pisano-Legendre balance refutes Question 5.2

## Abstract

The exact odd-prime fiber of the attained balance -1 for seeds (0,3) is {3}.

**Definition 1.1 (Exact odd-prime fibers).**

Lean statement: `D5/S3/Arith/PisanoLegendre/AndoyoPrimeFiberRefutation.fiber`

*Formalization.* `D5/S3/Arith/PisanoLegendre/AndoyoPrimeFiberRefutation.fiber` (`✓ std3`).

*Citation.* Jason D. Andoyo (2026). *(a,b)-Fibonacci-Legendre Cordial Graphs and k-Pisano-Legendre Primes*. DOI: [10.62072/acm.2026.09011](https://doi.org/10.62072/acm.2026.09011). URL: <https://arxiv.org/html/2601.10561v1>.

*Commentary.*

For integer seeds a,b and integer k, fiber(a,b,k) contains exactly natural primes p different from two for which K(p,a,b)=k. The imported recurrence F starts at index zero. Its least positive scalar period pi determines the index range 0 through pi-1, with multiplicity. The three Legendre counts partition this range, and K is the integer count at 1 minus the counts at -1 and 0.

**Definition 1.2 (The original universal assertion).**

$$\forall a \in \mathbb{Z},\; \forall b \in \mathbb{Z},\; (a,b) \ne (0,0) \Rightarrow \left(\forall k \in \mathbb{Z},\; k \in chi(a,b) \Rightarrow Set.Infinite (fiber(a,b,k))\right)$$

*Formalization.* `D5/S3/Arith/PisanoLegendre/AndoyoPrimeFiberRefutation.claim` (`✓ std3`).

*Citation.* Jason D. Andoyo (2026). *(a,b)-Fibonacci-Legendre Cordial Graphs and k-Pisano-Legendre Primes*. DOI: [10.62072/acm.2026.09011](https://doi.org/10.62072/acm.2026.09011). URL: <https://arxiv.org/html/2601.10561v1>.

*Commentary.*

Question 5.2 asks: Suppose that a and b are integers with (a,b) different from (0,0). For every k in chi(a,b), is the cardinality of the corresponding prime fiber aleph-zero? Here chi is the complete set of attained integer balances over odd primes. An infinite subset of the natural numbers is countably infinite. The source imposes no positivity, coprimality, individual nonzero-seed or nonzero-modulo-p restriction; primes dividing both seeds remain in scope.

**Theorem 1.3 (The universal assertion is false).**

$$\neg (\forall a \in \mathbb{Z},\; \forall b \in \mathbb{Z},\; (a,b) \ne (0,0) \Rightarrow \left(\forall k \in \mathbb{Z},\; k \in chi(a,b) \Rightarrow Set.Infinite (fiber(a,b,k))\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/PisanoLegendre/AndoyoPrimeFiberRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/andoyo-2026-pisano-question-5-2` (refuted) by `D5/S3/Arith/PisanoLegendre/AndoyoPrimeFiberRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"andoyo-2026-pisano-question-5-2","declaration_gid":"D5/S3/Arith/PisanoLegendre/AndoyoPrimeFiberRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Jason D. Andoyo (2026). *(a,b)-Fibonacci-Legendre Cordial Graphs and k-Pisano-Legendre Primes*. DOI: [10.62072/acm.2026.09011](https://doi.org/10.62072/acm.2026.09011). URL: <https://arxiv.org/html/2601.10561v1>.

*Commentary.*

Take a=0, b=3 and k=-1. Modulo three the recurrence is identically zero. Its least positive scalar period is one, so the counts are N(1)=N(-1)=0 and N(0)=1. Thus K=-1 is attained at three.

For arbitrary integer seeds, the recurrence satisfies F(n+1)^2-F(n)F(n+1)-F(n)^2=(-1)^n(b^2-ab-a^2). Finite invertible pair dynamics supplies a positive scalar period. At a period return the left-hand norm returns to its initial value. At an odd prime with nonzero initial norm, cancellation forces the least period to be even. For (0,3) that norm is nine, nonzero at every prime other than three.

The Legendre trichotomy gives pi=N(1)+N(-1)+N(0), hence K=2N(1)-pi. Every odd prime other than three therefore has even K and cannot realize -1. Combined with attainment, the exact fiber is {3}; its finiteness contradicts the original universal assertion. This is a symbolic obstruction over all primes, with no sampling bound.

Definitions 2.6 and 2.7, the odd-prime convention in Section 4, the definition of the prime fiber there, and Section 5 Question 5.2 supply the source interpretation. The argument does not settle infinitude for coprime seeds or assert worldwide priority.

## References

- Truth anchor: `D5/S3/Arith/PisanoLegendre/AndoyoPrimeFiberRefutation.claim`
- Truth anchor: `D5/S3/Arith/PisanoLegendre/AndoyoPrimeFiberRefutation.fiber`
- Truth anchor: `D5/S3/Arith/PisanoLegendre/AndoyoPrimeFiberRefutation.result`
- Dependency: [D5/S3/Arith/AndoyoPisanoSetCollision](../AndoyoPisanoSetCollision.md)
