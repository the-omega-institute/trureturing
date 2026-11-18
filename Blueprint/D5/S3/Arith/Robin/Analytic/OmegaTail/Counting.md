# The exponent supplied by fixed prime bins

## Abstract

The exponent supplied by fixed prime bins.

**Theorem 1.1 (Finite bin lower exponent).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaTail/Counting.finite_box_lower`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/OmegaTail/Counting.finite_box_lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix a finite inhabited family of disjoint positive intervals (a(j),b(j)], with positive masses r(j)<b(j)-a(j), sum r(j)=1, and lambda+sum r(j)*log(b(j))<0. For every epsilon>0, eventually log(tailCount(lambda,x))/scale(x) is at least sum (b(j)-a(j))*binEntropy(r(j)/(b(j)-a(j)))-epsilon. The prime number theorem gives actual prime capacities in intervals (a(j)*log(x),b(j)*log(x)]. Rounding and adjusting the first box produce exactly floor(threshold(lambda,x))+1 primes. The exact second-order logarithmic cost limit, rather than the first-order total alone, proves that all products fit under x. The finite product bound and moving binomial entropy asymptotic give the lower exponent.

## References

- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaTail/Counting.finite_box_lower`
- Dependency: [D5/S3/Arith/Robin/Analytic/OmegaTail/Entropy](Entropy.md)
- Dependency: [D5/S3/Arith/Robin/Analytic/OmegaTail/Lower](Lower.md)
- Dependency: [D5/S3/Arith/Robin/Analytic/OmegaTail/Selection](Selection.md)
