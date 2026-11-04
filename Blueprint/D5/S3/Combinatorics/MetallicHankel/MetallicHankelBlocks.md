# Ordinary and Reversed Blocks of the Metallic Continuants

## Abstract

The ordinary and reversed transfers act on the same continuants returned by normal_family.

**Definition 1.1 (Ordered transfer products).**

Lean statement: `D5/S3/Combinatorics/MetallicHankel/MetallicHankelBlocks.transferPrefix`

*Formalization.* `D5/S3/Combinatorics/MetallicHankel/MetallicHankelBlocks.transferPrefix` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Guo-Niu Han, Emmanuel Pedon (2025). *Hankel continued fractions and Hankel determinants for q-deformed metallic numbers*. DOI: [10.48550/arXiv.2502.05993](https://doi.org/10.48550/arXiv.2502.05993). URL: <https://arxiv.org/abs/2502.05993v2>.

*Commentary.*

For a sequence A of two by two matrices over integral formal power series, define T(0)=I and T(p+1)=A(p)T(p). Thus later transitions multiply on the left.

**Definition 1.2 (The cyclic ordinary transition).**

Lean statement: `D5/S3/Combinatorics/MetallicHankel/MetallicHankelBlocks.ordinaryStep`

*Formalization.* `D5/S3/Combinatorics/MetallicHankel/MetallicHankelBlocks.ordinaryStep` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Guo-Niu Han, Emmanuel Pedon (2025). *Hankel continued fractions and Hankel determinants for q-deformed metallic numbers*. DOI: [10.48550/arXiv.2502.05993](https://doi.org/10.48550/arXiv.2502.05993). URL: <https://arxiv.org/abs/2502.05993v2>.

*Commentary.*

Given a natural L, degree indices k, integer signs b and denominator series D, A(p) has first row D(p), -b(p) X^(k(p+L-1)+k(p)+2) and second row 1,0. Natural subtraction is truncated at zero. At a positive period L the first exponent uses the last degree increment of the cycle.

**Theorem 1.3 (Exact ordinary block action).**

Lean statement: `D5/S3/Combinatorics/MetallicHankel/MetallicHankelBlocks.ordinary_blocks`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/MetallicHankel/MetallicHankelBlocks.ordinary_blocks` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Guo-Niu Han, Emmanuel Pedon (2025). *Hankel continued fractions and Hankel determinants for q-deformed metallic numbers*. DOI: [10.48550/arXiv.2502.05993](https://doi.org/10.48550/arXiv.2502.05993). URL: <https://arxiv.org/abs/2502.05993v2>.

*Commentary.*

Let n>=1. Supply L,k,b,D,Q with exactly the explicit cycle data, length, initial values Q(0)=1, Q(1)=D(0), and recurrence exported by normal_family. Set nu=1 for even n and 2 for odd n; set rho=2n(n+1) for even n and 4n(n+1) for odd n. For U=T(L)^nu, constantCoeff(trace U)=1 and det U=X^(2rho). For every K>=1, put p=(K nu)L. Then U^K(1,0)=(Q(p),Q(p-1)). Moreover every degree sequence s satisfying s(p+1)=s(p)+k(p)+1 has s(p)=s(p-1)+(n+1) at all these block endpoints. The exceptional n=1 cycle has length three and weight four; its chosen block is doubled. The proof derives the actual state cycle, the sign product and weight, then multiplies the supplied recurrence. No assertion that trace U itself equals one is made. Taking s(p)=K rho from normal_family gives the predecessor degree K rho-(n+1). MetallicHankelEndpointJets consumes this exact ordinary block action to construct arbitrary endpoint jets.

**Definition 1.4 (Reversal at a supplied support degree).**

Lean statement: `D5/S3/Combinatorics/MetallicHankel/MetallicHankelBlocks.reverseAt`

*Formalization.* `D5/S3/Combinatorics/MetallicHankel/MetallicHankelBlocks.reverseAt` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Guo-Niu Han, Emmanuel Pedon (2025). *Hankel continued fractions and Hankel determinants for q-deformed metallic numbers*. DOI: [10.48550/arXiv.2502.05993](https://doi.org/10.48550/arXiv.2502.05993). URL: <https://arxiv.org/abs/2502.05993v2>.

*Commentary.*

reverseAt(d,f) reflects the polynomial truncation through d. Its coefficient at r<=d is coeff(d-r,f), and every coefficient above d is zero. The support degree need not equal the actual degree; leading zero coefficients are retained.

**Theorem 1.5 (Coefficients of a specified-degree reversal).**

Lean statement: `D5/S3/Combinatorics/MetallicHankel/MetallicHankelBlocks.reverse_coeff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/MetallicHankel/MetallicHankelBlocks.reverse_coeff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Guo-Niu Han, Emmanuel Pedon (2025). *Hankel continued fractions and Hankel determinants for q-deformed metallic numbers*. DOI: [10.48550/arXiv.2502.05993](https://doi.org/10.48550/arXiv.2502.05993). URL: <https://arxiv.org/abs/2502.05993v2>.

*Commentary.*

For every d,r and integral series f, coeff(r,reverseAt(d,f)) is coeff(d-r,f) when r<=d and zero otherwise. The endpoint-jet proof consumes this supported coefficient identity to identify both common-degree reversals, including the fixed predecessor shift.

**Definition 1.6 (The reversed continuant transition).**

Lean statement: `D5/S3/Combinatorics/MetallicHankel/MetallicHankelBlocks.reversedStep`

*Formalization.* `D5/S3/Combinatorics/MetallicHankel/MetallicHankelBlocks.reversedStep` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Guo-Niu Han, Emmanuel Pedon (2025). *Hankel continued fractions and Hankel determinants for q-deformed metallic numbers*. DOI: [10.48550/arXiv.2502.05993](https://doi.org/10.48550/arXiv.2502.05993). URL: <https://arxiv.org/abs/2502.05993v2>.

*Commentary.*

For the same k,b,D, the reversed transition has first row reverseAt(k(p)+1,D(p)),-b(p) and second row 1,0. The off-diagonal entry has no power of X.

**Theorem 1.7 (Exact reversed block action).**

Lean statement: `D5/S3/Combinatorics/MetallicHankel/MetallicHankelBlocks.reversed_blocks`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/MetallicHankel/MetallicHankelBlocks.reversed_blocks` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Guo-Niu Han, Emmanuel Pedon (2025). *Hankel continued fractions and Hankel determinants for q-deformed metallic numbers*. DOI: [10.48550/arXiv.2502.05993](https://doi.org/10.48550/arXiv.2502.05993). URL: <https://arxiv.org/abs/2502.05993v2>.

*Commentary.*

Let n>=1 and supply the very same L,k,b,D,Q data and recurrence as ordinary_blocks, together with s(0)=0, s(p+1)=s(p)+k(p)+1 and support(Q(p))<=s(p). These are the data exported by normal_family. Put nu=1 for even n and 2 for odd n, and R=T_reversed(L)^nu. Then R evaluated at X=0 is the identity matrix. For every K>=1, with p=(K nu)L, R^K(1,0) is (reverseAt(s(p),Q(p)),reverseAt(s(p-1),Q(p-1))). The proof reverses the actual supported recurrence and identifies the complete constant monodromy from both basis vectors. It includes the exceptional golden n=1 cycle. Combined with ordinary_blocks and s(p)=K rho, the predecessor support degree is K rho-(n+1). No arbitrary-order endpoint polynomial or full Conjecture C is asserted here.

## References

- Truth anchor: `D5/S3/Combinatorics/MetallicHankel/MetallicHankelBlocks.ordinaryStep`
- Truth anchor: `D5/S3/Combinatorics/MetallicHankel/MetallicHankelBlocks.ordinary_blocks`
- Truth anchor: `D5/S3/Combinatorics/MetallicHankel/MetallicHankelBlocks.reverseAt`
- Truth anchor: `D5/S3/Combinatorics/MetallicHankel/MetallicHankelBlocks.reverse_coeff`
- Truth anchor: `D5/S3/Combinatorics/MetallicHankel/MetallicHankelBlocks.reversedStep`
- Truth anchor: `D5/S3/Combinatorics/MetallicHankel/MetallicHankelBlocks.reversed_blocks`
- Truth anchor: `D5/S3/Combinatorics/MetallicHankel/MetallicHankelBlocks.transferPrefix`
- Dependency: [D5/S3/Combinatorics/MetallicHankel/MetallicHankelData](MetallicHankelData.md)
