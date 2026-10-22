# Two-Branch Clearing

## Abstract

Both branches of the native contraction

D is an arbitrary finite integral symmetric even-diagonal lattice datum and a,b are unrestricted charges. Set g=B(a,b), m=(-g).toNat, n=g.toNat and N=g.natAbs=m+n. The exact native halfContraction is binomial_g(-s) times binomial_(-g)(s). Native binomial-series exponent addition proves the identities in PowerSeries Complex; no equality of rational functions is used to identify unregularized opposite iota expansions.

**Theorem 1.1 (Both branch factors).**

$$\operatorname{TwoBranchClearing}\left(D, a, b\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockBranchClearing.half_contraction_two_branch_clearing` (`✓ std3`). ∎

*Citation.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

Exactly (1-s)^m (1+s)^n h_g(s)=(1-s)^n (1+s)^m. The positive-g pole at s=-1 is retained; clearing only the s=1 branch is not sufficient.

**Theorem 1.2 (Physical clearing polynomial).**

$$\operatorname{PhysicalClearing}\left(D, a, b\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockBranchClearing.half_contraction_physical_clearing` (`✓ std3`). ∎

*Citation.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

Exactly (1-s^2)^N h_g(s)=P_g(s), where P_g=(1-s)^(2n) (1+s)^(2m). With z=x^2 and w=y^2, each physical coordinate shift is two cover-exponent units. This scalar identity is not itself an actual tensor coefficient-locality theorem.

**Theorem 1.3 (Polynomial branch reversal).**

$$\operatorname{ClearedReciprocity}\left(g\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockBranchClearing.cleared_polynomial_reciprocity` (`✓ std3`). ∎

*Citation.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

The fixed-degree reflection at 2N preserves P_g. Its degree is at most 2N; the physical reversal sign is (-1)^N=paritySign g and must be paired with the actual ground interchange. All-state twisted Jacobi, physical iterates, reconstructed twisted fields, orbifold intertwiners, Monster realization and string/AdS dynamics remain open. Classical provenance, zero novelty claim.

## References

- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockBranchClearing.cleared_polynomial_reciprocity`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockBranchClearing.half_contraction_physical_clearing`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockBranchClearing.half_contraction_two_branch_clearing`
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockChargedCoefficients](LatticeHalfFockChargedCoefficients.md)
