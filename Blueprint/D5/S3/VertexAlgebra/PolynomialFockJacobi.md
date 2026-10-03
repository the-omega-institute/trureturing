# Integer Fock Composition

## Abstract

The actual polynomial Fock fields satisfy integer residue closure and Borcherds identity.

Every state is an arbitrary complex polynomial in the countable Fock variables. Every mode parameter is an integer. Residues are genuine lower-truncated operator fields, with both coefficient sums finite on each input state. Generalized integer binomial coefficients and integer powers of minus one retain the negative-mode conventions. No bounded degree, second state-field map or assumed reconstruction law is used. This rank-one formal construction does not establish a Monster realization, module fusion, analytic CFT or spacetime dynamics.

**Theorem 1.1 (Nonnegative residues obey Dong cancellation).**

Lean statement: `D5/S3/VertexAlgebra/PolynomialFockJacobi.residue_nonnegative_locality`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/PolynomialFockJacobi.residue_nonnegative_locality` (`✓ std3`). ∎

*Citation.* Atsushi Matsuo; Kiyokazu Nagatomo (1997). *On axioms for a vertex algebra and locality of quantum fields*. URL: <https://arxiv.org/abs/hep-th/9706118v1>.

*Commentary.*

The double commutator is killed by the first pair's locality polynomial and by the product of the other two locality polynomials. Expanding the commuting coefficient shifts annihilates every finite term, giving an order independent of the vector. Evaluation gives locality of the actual residue field.

**Theorem 1.2 (Vacuum uniqueness relative to the existing Y).**

Lean statement: `D5/S3/VertexAlgebra/PolynomialFockJacobi.relative_vacuum_uniqueness`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/PolynomialFockJacobi.relative_vacuum_uniqueness` (`✓ std3`). ∎

*Citation.* Atsushi Matsuo; Kiyokazu Nagatomo (1997). *On axioms for a vertex algebra and locality of quantum fields*. URL: <https://arxiv.org/abs/hep-th/9706118v1>.

*Commentary.*

A creative field covariant under the actual L(-1), with zero initial vacuum state and local with every Y(u), is zero. The covariance recurrence kills the entire vacuum series. Extracting the other field's constant vacuum coefficient in locality kills every coefficient on every state. Membership in the image of Y is not a hypothesis.

**Theorem 1.3 (The same Y is closed under every integer residue).**

Lean statement: `D5/S3/VertexAlgebra/PolynomialFockJacobi.residue_closure`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/PolynomialFockJacobi.residue_closure` (`✓ std3`). ∎

*Citation.* Atsushi Matsuo; Kiyokazu Nagatomo (1997). *On axioms for a vertex algebra and locality of quantum fields*. URL: <https://arxiv.org/abs/hep-th/9706118v1>.

*Commentary.*

Y(mu(a,r,b)) equals R_r(Y(a),Y(b)) for every integer r. Nonnegative Dong cancellation and negative divided-derivative normal-product locality give relative locality. Supported coefficient telescoping proves covariance; vacuum coefficients prove creativity and initial state mu(a,r,b). Relative uniqueness identifies the resulting operator with Y.

**Theorem 1.4 (Borcherds identity for all states and integer modes).**

Lean statement: `D5/S3/VertexAlgebra/PolynomialFockJacobi.borcherds`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/PolynomialFockJacobi.borcherds` (`✓ std3`). ∎

*Citation.* Atsushi Matsuo; Kiyokazu Nagatomo (1997). *On axioms for a vertex algebra and locality of quantum fields*. URL: <https://arxiv.org/abs/hep-th/9706118v1>.

*Commentary.*

The left iterate sum and both composition branches have separate pointwise finite support. Closure supplies the p=0 seed; actual pairwise locality supplies the high-r region. Supported Pascal reindexing gives the three-term discrepancy recurrence. Induction on positive p and nested induction on negative p and the finite distance below the high-r boundary prove the exact law for every integer p,q,r.

## References

- Truth anchor: `D5/S3/VertexAlgebra/PolynomialFockJacobi.borcherds`
- Truth anchor: `D5/S3/VertexAlgebra/PolynomialFockJacobi.relative_vacuum_uniqueness`
- Truth anchor: `D5/S3/VertexAlgebra/PolynomialFockJacobi.residue_closure`
- Truth anchor: `D5/S3/VertexAlgebra/PolynomialFockJacobi.residue_nonnegative_locality`
- Dependency: [D5/S3/VertexAlgebra/PolynomialFockStateField](PolynomialFockStateField.md)
