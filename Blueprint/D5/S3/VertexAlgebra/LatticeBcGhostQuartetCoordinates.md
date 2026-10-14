# LatticeBcGhostQuartetCoordinates

## Abstract

Original-Q quartet prerequisites: LatticeBcGhostQuartetCoordinates

These are retained proofs from the accepted original-Q quartet source, not new mathematics produced by changing module names. The namespace remains D5.S3.VertexAlgebra.OriginalQQuartetSource. StatementSource.WithoutFormula renders declaration handles bound to the canonical scoped report, not displayed formula bodies; the source assumptions, proof bodies and noncomputable section are unchanged.

D is the original LatticeGeneratingFieldLocality.LatticeData, with arbitrary natural rank, integral symmetric Gram matrix and even diagonal. Carrier D is the finite-support sum over every integral charge of the actual complex oscillator polynomial space. State D is Carrier D tensor Fock Complex. The existing Fock, b, c, M, G, Q and J are used without replacement. No positivity, positive-energy cutoff, restricted charge spectrum, surrogate differential or assumed locality, Jacobi, spectrum or nilpotence is added. Isotropic and negative-norm charge sectors are not removed.

This retention establishes quartet prerequisites and per-mode identities, not a total K contraction, the cohomology of the full original Q, a physical no-ghost theorem, a string construction or AdS/CFT. Full-Q nilpotence is a separately previously accepted result outside this scoped graph, not imported or certified here. Wherever that separate route is invoked, both Gram-inverse equations and the rank-26 condition remain required; these are not premises of statements that do not use that route. The larger VOA/CFT/string/AdS goal remains active and open.

Native information-escape registration is unfinished under issue #15040. Mathematical kernel checking and scoped report binding do not imply declared_validated registration, frozen admission, CI, remote acceptance or independent canonical source/render approval.

For a square complex frame, coordinate(row,n)=sum_i frame(row,i) X(i,n), and coordinateSub is its actual polynomial evaluation homomorphism. The identity coordinateSub(frame)(coordinateSub(inverse)(P))=P uses only inverse*frame=1; the reversed composition uses only frame*inverse=1. Bijectivity uses both equations. The chain rule itself needs neither an inverse frame nor an inverse Gram matrix.

originalDerivative(u,n) is the finite sum of original weightedPartial_i(n) operators. coordinateDerivative(frame,u,n)=sum_row <u,frame(row)>_G pderiv_(row,n). Polynomial induction proves originalDerivative(u,n)(coordinateSub(P))=coordinateSub(coordinateDerivative(frame,u,n)(P)), using the original generator action and product rule.

At mode -(n+1), the directional polynomial current for frame(row) multiplies a substituted polynomial by its row coordinate. At mode n+1 it is (n+1) times the substituted coordinate derivative. At mode 0 it is scalar multiplication by <u,complexCharge(alpha)>_G. directionalCurrent_single gives the exact original charge-sum carrier action; tensor transport is not a different representation.

The unconsumed original_coordinate_current_bridge conjunction is not retained as a canonical theorem. Its already accepted source and compiled proof evidence remain intact in the immutable original archive. The separate coordinate, chain-rule and mode-action proofs are retained and consumed.

**Definition 1.1 (coordinate).**

Lean statement: `D5/S3/VertexAlgebra/LatticeBcGhostQuartetCoordinates.coordinate`

*Formalization.* `D5/S3/VertexAlgebra/LatticeBcGhostQuartetCoordinates.coordinate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Retained original construction on the unchanged carrier.

**Definition 1.2 (coordinateSub).**

Lean statement: `D5/S3/VertexAlgebra/LatticeBcGhostQuartetCoordinates.coordinateSub`

*Formalization.* `D5/S3/VertexAlgebra/LatticeBcGhostQuartetCoordinates.coordinateSub` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Retained original construction on the unchanged carrier.

**Definition 1.3 (originalDerivative).**

Lean statement: `D5/S3/VertexAlgebra/LatticeBcGhostQuartetCoordinates.originalDerivative`

*Formalization.* `D5/S3/VertexAlgebra/LatticeBcGhostQuartetCoordinates.originalDerivative` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Retained original construction on the unchanged carrier.

**Definition 1.4 (coordinateDerivative).**

Lean statement: `D5/S3/VertexAlgebra/LatticeBcGhostQuartetCoordinates.coordinateDerivative`

*Formalization.* `D5/S3/VertexAlgebra/LatticeBcGhostQuartetCoordinates.coordinateDerivative` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Retained original construction on the unchanged carrier.

**Definition 1.5 (directionalPolynomialCurrent).**

Lean statement: `D5/S3/VertexAlgebra/LatticeBcGhostQuartetCoordinates.directionalPolynomialCurrent`

*Formalization.* `D5/S3/VertexAlgebra/LatticeBcGhostQuartetCoordinates.directionalPolynomialCurrent` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Retained original construction on the unchanged carrier.

**Definition 1.6 (chargeCoefficient).**

Lean statement: `D5/S3/VertexAlgebra/LatticeBcGhostQuartetCoordinates.chargeCoefficient`

*Formalization.* `D5/S3/VertexAlgebra/LatticeBcGhostQuartetCoordinates.chargeCoefficient` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Retained original construction on the unchanged carrier.

**Theorem 1.7 (coordinateSub X).**

Lean statement: `D5/S3/VertexAlgebra/LatticeBcGhostQuartetCoordinates.coordinateSub_X`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeBcGhostQuartetCoordinates.coordinateSub_X` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Consumed normalization, transport or packaging helper, not a separately new mathematical result. Accepted source consumers: coordinateSub_coordinate, coordinateSub_inverse, directionalPolynomialCurrent_negative, matterEmbedding_X, matterEmbedding_X_coordinate, original_derivative_coordinate_chain_rule.

**Theorem 1.8 (coordinateSub coordinate).**

Lean statement: `D5/S3/VertexAlgebra/LatticeBcGhostQuartetCoordinates.coordinateSub_coordinate`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeBcGhostQuartetCoordinates.coordinateSub_coordinate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Consumed normalization, transport or packaging helper, not a separately new mathematical result. Accepted source consumers: coordinateSub_inverse.

**Theorem 1.9 (coordinate identity).**

Lean statement: `D5/S3/VertexAlgebra/LatticeBcGhostQuartetCoordinates.coordinate_identity`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeBcGhostQuartetCoordinates.coordinate_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Consumed normalization, transport or packaging helper, not a separately new mathematical result. Accepted source consumers: coordinateSub_inverse.

**Theorem 1.10 (coordinateSub inverse).**

Lean statement: `D5/S3/VertexAlgebra/LatticeBcGhostQuartetCoordinates.coordinateSub_inverse`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeBcGhostQuartetCoordinates.coordinateSub_inverse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Consumed normalization, transport or packaging helper, not a separately new mathematical result. Accepted source consumers: coordinateLinearEquiv, coordinateSub_bijective, matterAux_current, polynomialAux_coordinateSub.

**Theorem 1.11 (coordinateSub bijective).**

Lean statement: `D5/S3/VertexAlgebra/LatticeBcGhostQuartetCoordinates.coordinateSub_bijective`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeBcGhostQuartetCoordinates.coordinateSub_bijective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Consumed normalization, transport or packaging helper, not a separately new mathematical result. Accepted source consumers: coordinateEquiv, matterAux_sugawara_zero_commutator, original_Q_polarized_coordinate_consumer, original_coordinate_current_bridge.

**Theorem 1.12 (originalDerivative X).**

Lean statement: `D5/S3/VertexAlgebra/LatticeBcGhostQuartetCoordinates.originalDerivative_X`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeBcGhostQuartetCoordinates.originalDerivative_X` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Consumed normalization, transport or packaging helper, not a separately new mathematical result. Accepted source consumers: originalDerivative_coordinate.

**Theorem 1.13 (originalDerivative coordinate).**

Lean statement: `D5/S3/VertexAlgebra/LatticeBcGhostQuartetCoordinates.originalDerivative_coordinate`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeBcGhostQuartetCoordinates.originalDerivative_coordinate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Consumed normalization, transport or packaging helper, not a separately new mathematical result. Accepted source consumers: original_derivative_coordinate_chain_rule.

**Theorem 1.14 (coordinateDerivative X).**

Lean statement: `D5/S3/VertexAlgebra/LatticeBcGhostQuartetCoordinates.coordinateDerivative_X`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeBcGhostQuartetCoordinates.coordinateDerivative_X` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Consumed normalization, transport or packaging helper, not a separately new mathematical result. Accepted source consumers: original_derivative_coordinate_chain_rule.

**Theorem 1.15 (originalDerivative product).**

Lean statement: `D5/S3/VertexAlgebra/LatticeBcGhostQuartetCoordinates.originalDerivative_product`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeBcGhostQuartetCoordinates.originalDerivative_product` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Consumed normalization, transport or packaging helper, not a separately new mathematical result. Accepted source consumers: original_derivative_coordinate_chain_rule.

**Theorem 1.16 (coordinateDerivative product).**

Lean statement: `D5/S3/VertexAlgebra/LatticeBcGhostQuartetCoordinates.coordinateDerivative_product`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeBcGhostQuartetCoordinates.coordinateDerivative_product` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Consumed normalization, transport or packaging helper, not a separately new mathematical result. Accepted source consumers: original_derivative_coordinate_chain_rule.

**Theorem 1.17 (original derivative coordinate chain rule).**

Lean statement: `D5/S3/VertexAlgebra/LatticeBcGhostQuartetCoordinates.original_derivative_coordinate_chain_rule`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeBcGhostQuartetCoordinates.original_derivative_coordinate_chain_rule` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Retained substantive original proof; canonical naming supplies no additional mathematical novelty.

**Theorem 1.18 (directionalPolynomialCurrent negative).**

Lean statement: `D5/S3/VertexAlgebra/LatticeBcGhostQuartetCoordinates.directionalPolynomialCurrent_negative`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeBcGhostQuartetCoordinates.directionalPolynomialCurrent_negative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Consumed normalization, transport or packaging helper, not a separately new mathematical result. Accepted source consumers: original_bosonic_mode_number, original_coordinate_current_bridge, original_current_aux_coordinate.

**Theorem 1.19 (directionalPolynomialCurrent positive).**

Lean statement: `D5/S3/VertexAlgebra/LatticeBcGhostQuartetCoordinates.directionalPolynomialCurrent_positive`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeBcGhostQuartetCoordinates.directionalPolynomialCurrent_positive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Consumed normalization, transport or packaging helper, not a separately new mathematical result. Accepted source consumers: directionalCurrent_positive_transverse_zero, original_bosonic_mode_number, original_coordinate_current_bridge, original_current_aux_coordinate.

**Theorem 1.20 (directionalPolynomialCurrent zero).**

Lean statement: `D5/S3/VertexAlgebra/LatticeBcGhostQuartetCoordinates.directionalPolynomialCurrent_zero`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeBcGhostQuartetCoordinates.directionalPolynomialCurrent_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Consumed bind-only helper with an accepted-only omitted-wrapper consumer: D5.S3.VertexAlgebra.OriginalQQuartetSource.original_coordinate_current_bridge in TemporaryOriginalQuartet03. That wrapper remains omitted; this accepted-source reference does not establish retained-canonical liveness or standalone new-content credit.

**Theorem 1.21 (chargeCoefficient gramPair).**

Lean statement: `D5/S3/VertexAlgebra/LatticeBcGhostQuartetCoordinates.chargeCoefficient_gramPair`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeBcGhostQuartetCoordinates.chargeCoefficient_gramPair` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Consumed bind-only helper with an accepted-only omitted-wrapper consumer: D5.S3.VertexAlgebra.OriginalQQuartetSource.original_coordinate_current_bridge in TemporaryOriginalQuartet03. That wrapper remains omitted; this accepted-source reference does not establish retained-canonical liveness or standalone new-content credit.

**Theorem 1.22 (directionalCurrent single).**

Lean statement: `D5/S3/VertexAlgebra/LatticeBcGhostQuartetCoordinates.directionalCurrent_single`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeBcGhostQuartetCoordinates.directionalCurrent_single` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Consumed normalization, transport or packaging helper, not a separately new mathematical result. Accepted source consumers: directionalCurrent_positive_transverse_zero, matterAux_current, original_K_block_count, original_coordinate_current_bridge.

## References

- Truth anchor: `D5/S3/VertexAlgebra/LatticeBcGhostQuartetCoordinates.chargeCoefficient`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeBcGhostQuartetCoordinates.chargeCoefficient_gramPair`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeBcGhostQuartetCoordinates.coordinate`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeBcGhostQuartetCoordinates.coordinateDerivative`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeBcGhostQuartetCoordinates.coordinateDerivative_X`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeBcGhostQuartetCoordinates.coordinateDerivative_product`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeBcGhostQuartetCoordinates.coordinateSub`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeBcGhostQuartetCoordinates.coordinateSub_X`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeBcGhostQuartetCoordinates.coordinateSub_bijective`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeBcGhostQuartetCoordinates.coordinateSub_coordinate`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeBcGhostQuartetCoordinates.coordinateSub_inverse`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeBcGhostQuartetCoordinates.coordinate_identity`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeBcGhostQuartetCoordinates.directionalCurrent_single`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeBcGhostQuartetCoordinates.directionalPolynomialCurrent`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeBcGhostQuartetCoordinates.directionalPolynomialCurrent_negative`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeBcGhostQuartetCoordinates.directionalPolynomialCurrent_positive`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeBcGhostQuartetCoordinates.directionalPolynomialCurrent_zero`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeBcGhostQuartetCoordinates.originalDerivative`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeBcGhostQuartetCoordinates.originalDerivative_X`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeBcGhostQuartetCoordinates.originalDerivative_coordinate`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeBcGhostQuartetCoordinates.originalDerivative_product`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeBcGhostQuartetCoordinates.original_derivative_coordinate_chain_rule`
- Dependency: [D5/S3/VertexAlgebra/LatticeBcGhostPolarization](LatticeBcGhostPolarization.md)
