# Zelinsky's Conjecture 13 is false

## Abstract

The radical component condition has relative density one among odd primitive non-deficient integers.

**Definition 1.1 (Conjecture 13).**

Lean statement: `D5/S3/Arith/Abundancy/ZelinskyRadicalComponentConjecture13.claim`

*Formalization.* `D5/S3/Arith/Abundancy/ZelinskyRadicalComponentConjecture13.claim` (`✓ std3`).

*Citation.* Joshua Zelinsky (2026). *Must a Primitive Non-Deficient Number Always Have a Small Component?*. DOI: [10.48550/arXiv.2005.12115](https://doi.org/10.48550/arXiv.2005.12115). URL: <https://arxiv.org/abs/2005.12115v5>.

*Commentary.*

Conjecture 13 asserts lim (B intersect C_O)(X)/C_O(X)=0, where C_O consists of the odd primitive non-deficient integers.

**Theorem 1.2 (The relative limit is one, contradicting zero).**

Lean statement: `D5/S3/Arith/Abundancy/ZelinskyRadicalComponentConjecture13.result`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Abundancy/ZelinskyRadicalComponentConjecture13.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Joshua Zelinsky (2026). *Must a Primitive Non-Deficient Number Always Have a Small Component?*. DOI: [10.48550/arXiv.2005.12115](https://doi.org/10.48550/arXiv.2005.12115). URL: <https://arxiv.org/abs/2005.12115v5>.

*Commentary.*

Take the empty excluded prime set in the odd squarefree lower bound. Its integers belong to C_O, so C_O(X)>=X^(79/80) eventually. The relative density comparison gives (B intersect C_O)(X)/C_O(X) tending to one. Uniqueness of limits refutes the asserted zero limit.

## References

- Truth anchor: `D5/S3/Arith/Abundancy/ZelinskyRadicalComponentConjecture13.claim`
- Truth anchor: `D5/S3/Arith/Abundancy/ZelinskyRadicalComponentConjecture13.result`
- Dependency: [D5/S3/Arith/Abundancy/ZelinskyRadicalComponentConjecture11](ZelinskyRadicalComponentConjecture11.md)
