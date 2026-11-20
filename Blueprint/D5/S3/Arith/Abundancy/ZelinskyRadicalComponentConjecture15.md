# Zelinsky's Conjecture 15 is false

## Abstract

The radical component condition has relative density one among primitive non-deficient integers avoiding finitely many primes.

**Definition 1.1 (Conjecture 15).**

Lean statement: `D5/S3/Arith/Abundancy/ZelinskyRadicalComponentConjecture15.claim`

*Formalization.* `D5/S3/Arith/Abundancy/ZelinskyRadicalComponentConjecture15.claim` (`✓ std3`).

*Citation.* Joshua Zelinsky (2026). *Must a Primitive Non-Deficient Number Always Have a Small Component?*. DOI: [10.48550/arXiv.2005.12115](https://doi.org/10.48550/arXiv.2005.12115). URL: <https://arxiv.org/abs/2005.12115v5>.

*Commentary.*

For every nonempty finite set M of primes, Conjecture 15 asserts lim (B intersect C_M)(X)/C_M(X)=0, where C_M consists of primitive non-deficient integers divisible by no prime in M. The universal quantifier over M and its nonemptiness are retained.

**Theorem 1.2 (The relative limit is one, contradicting zero).**

Lean statement: `D5/S3/Arith/Abundancy/ZelinskyRadicalComponentConjecture15.result`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Abundancy/ZelinskyRadicalComponentConjecture15.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Joshua Zelinsky (2026). *Must a Primitive Non-Deficient Number Always Have a Small Component?*. DOI: [10.48550/arXiv.2005.12115](https://doi.org/10.48550/arXiv.2005.12115). URL: <https://arxiv.org/abs/2005.12115v5>.

*Commentary.*

For every finite prime set M, the odd squarefree lower bound gives C_M(X)>=X^(79/80) eventually. The relative density comparison gives (B intersect C_M)(X)/C_M(X) tending to one for each such M. In particular M={2} contradicts the universally asserted zero limit. No uniform threshold over all M is asserted or needed.

## References

- Truth anchor: `D5/S3/Arith/Abundancy/ZelinskyRadicalComponentConjecture15.claim`
- Truth anchor: `D5/S3/Arith/Abundancy/ZelinskyRadicalComponentConjecture15.result`
- Dependency: [D5/S3/Arith/Abundancy/ZelinskyRadicalComponentConjecture11](ZelinskyRadicalComponentConjecture11.md)
