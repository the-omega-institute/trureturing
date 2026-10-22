# Carrier and hypotheses

## Abstract

Integer modes on the actual original BRST cohomology.

The carrier is the existing OriginalCohomology: the kernel of the unchanged original Q, divided by the pullback of its range into that kernel. Under both Gram inverse equations and rank 26, the existing critical nilpotence theorem places the entire original Q image in the kernel. No relative retract criterion is used.

The exact denominator. Write C = ker(Q) on the full original matter tensor ghost carrier and B = (range(Q)).comap(C.subtype). Then OriginalCohomology is C/B; in ambient-vector notation the denominator is ker(Q) intersect range(Q), not an arbitrary boundary space. This quotient and the mode products below make sense for every D and H. Only after H times Gram = 1, Gram times H = 1 and rank(D) = 26 are all imposed does original_image_in_cycles identify B with the entire original-Q image inside the cycles. Both inverse equations and the rank condition are retained for that physical square-zero interpretation. There is no altered, truncated or conjugated differential.

The original number operator. On an occupation basis vector e_S of the ghost factor, BcGhostNumber.J multiplies by the number of odd occupied sites minus the number of even occupied sites. On a finite linear combination it is the sum of these signed occupation eigenactions, and J_D acts as identity on matter tensor this same J. The b field mode n is physical b(n-1), while the c field mode n is physical c(n+2), for all integer n. The existing J_b/J_c commutators, the site-field divided derivatives and the right-nested signed normal recursion imply the ghost Ward identity. In each residue the ordered sums have finite support separately on v and Jv; map_finsum and finite-support sum subtraction justify the commutator term by term, without a state-independent cutoff. The canonical basisWord and stateField_expansion extend it to every full ghost state. The actual tensor mode convolution uses indices i and n-1-i, and its three finite-support instances extend the identity to arbitrary full tensor states. Thus J_D(Y_D(a)_n v) = Y_D(J_D a)_n v + Y_D(a)_n(J_D v), for every integer n, with no parity or degree-eigenvector premise.

Number stability of the actual pullback quotient. The existing original-charge identity [J_D,Q] = Q says J_D(Qw) = Q(J_D w + w) on arbitrary full states w. It also says Q(J_D u)=0 whenever Qu=0. These are the same J/Q applications supplied in the existing OriginalBrstReassembly namespace, whose local uses here come directly from J_Q_commutator rather than from duplicate named general theorems or a second number operator. Restricting J_D to C gives cycleJ. If a cycle u is the boundary Qw, then J_D u = Q(J_D w+w); hence cycleJ preserves the literal B. Submodule.mapQ therefore defines the endomorphism cohomologyJ on the existing C/B, and cohomologyJ([u]) = [J_D u]. The preimage w need not be a cycle. Number stability itself needs neither Gram inverses nor critical rank.

All-mode quotient covariance. The product at integer mode n is the existing bilinear descent product_n([u],[v]) = [Y_D(u)_n v], for closed representatives u,v. Both boundary-slot obligations are the existing original-Q derivation proofs, including the signed parity splitting for mixed states; the number argument does not replace those obligations by assumptions. Apply the full tensor Ward identity to u,v, use that J_D preserves cycles and B, and project into C/B. Quotient induction in both arguments gives cohomologyJ(product_n(x,y)) = product_n(cohomologyJ(x),y) + product_n(x,cohomologyJ(y)), for arbitrary quotient classes x,y and every integer n. The plus sign is correct because ghost number acts evenly, even when the states have mixed parity. The -1 topological product is a specialization of this all-mode law, not a new quotient product.

Exact integer eigenvalue premises. Let r,s be arbitrary integers. If cohomologyJ(x) = r x and cohomologyJ(y) = s y, with complex scalar casts, quotient covariance and bilinearity imply cohomologyJ(product_n(x,y)) = (r+s) product_n(x,y) for every integer n. In particular, actual original cycles u,v satisfying J_D u = r u and J_D v = s v supply such eigenclasses through the literal quotient map, and their product has degree r+s. No assertion is made that every quotient eigenclass has an exactly homogeneous original representative, or that arbitrary classes split into integer eigenspaces. Those representative-existence and integer direct-sum questions are separate from this conditional consequence. Ghost number is not conformal energy, and no energy positivity premise has been inserted.

Parity, locality and physical scope. The locality supplier is LatticeBcGhostCohomologyLocality, which reopens the LatticeBcGhostCohomologyFields namespace and proves superLocal. It requires parity_p(x)=x and parity_q(y)=y and supplies a locality order killing the supercommutator of the actual quotient fields with exchange sign (-1) raised to p*q, on every input class and all two integer modes. Projected homogeneous original representatives and the actual tensor-field locality prove this statement; no ghost-number decomposition is used. This locality result and the quotient modes do not themselves need critical rank or a Gram inverse, whereas interpreting them as the physical nilpotent original BRST cohomology requires both inverse equations and rank 26. The representative action cohomologyJ([u])=[J_D u] does not establish equality with a separately transported Jbar. No B0 second-order law, bracket Jacobi identity or full VOA/CFT/fusion/string/AdS completion follows from the present number covariance alone; the full-cycle B0 representative remains B0(P0 u), not B0 u on arbitrary full cycles.

**Theorem 1.1 (Actual odd differential and parity).**

Lean statement: `D5/S3/VertexAlgebra/LatticeBcGhostCohomologyModes.Q_parityPart`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeBcGhostCohomologyModes.Q_parityPart` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original Q exchanges the actual parity projections. Arbitrary mixed cycles and boundaries therefore split into actual even and odd cycles and boundaries.

**Theorem 1.2 (Boundary in the input slot).**

Lean statement: `D5/S3/VertexAlgebra/LatticeBcGhostCohomologyModes.cycleMode_boundary_right`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeBcGhostCohomologyModes.cycleMode_boundary_right` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a closed mixed state, the signed difference of its projected modes on a boundary preimage is an explicit original-Q preimage of the mode product.

**Theorem 1.3 (Boundary in the state slot).**

Lean statement: `D5/S3/VertexAlgebra/LatticeBcGhostCohomologyModes.cycleMode_boundary_left`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeBcGhostCohomologyModes.cycleMode_boundary_left` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual mixed derivation law gives an explicit original-Q preimage whenever the other argument is closed.

**Theorem 1.4 (Genuine complex bilinear descent).**

Lean statement: `D5/S3/VertexAlgebra/LatticeBcGhostCohomologyModes.product_mk`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeBcGhostCohomologyModes.product_mk` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Mathlib LinearMap.liftQ₂ constructs the descended bilinear integer modes after both boundary obligations are proved. Changing either closed representative by an original-Q boundary leaves the quotient result unchanged.

**Theorem 1.5 (Every original Q image is a zero class at critical rank).**

Lean statement: `D5/S3/VertexAlgebra/LatticeBcGhostCohomologyModes.boundaryCycle_class_zero`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeBcGhostCohomologyModes.boundaryCycle_class_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This endpoint explicitly retains both Gram inverse equations and rank 26; the square-zero input is the existing theorem for the original Q, not an assumed or conjugated differential.

**Theorem 1.6 (Pointwise lower truncation).**

Lean statement: `D5/S3/VertexAlgebra/LatticeBcGhostCohomologyModes.product_lower_truncation`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeBcGhostCohomologyModes.product_lower_truncation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual tensor field bound descends on each pair of quotient states. No uniform state-independent cutoff is asserted.

## References

- Truth anchor: `D5/S3/VertexAlgebra/LatticeBcGhostCohomologyModes.Q_parityPart`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeBcGhostCohomologyModes.boundaryCycle_class_zero`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeBcGhostCohomologyModes.cycleMode_boundary_left`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeBcGhostCohomologyModes.cycleMode_boundary_right`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeBcGhostCohomologyModes.product_lower_truncation`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeBcGhostCohomologyModes.product_mk`
- Dependency: [D5/S3/VertexAlgebra/LatticeBcGhostBrstGhostNumber](LatticeBcGhostBrstGhostNumber.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeBcGhostBrstStateField](LatticeBcGhostBrstStateField.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeBcGhostNeutralCohomology](LatticeBcGhostNeutralCohomology.md)
