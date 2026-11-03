# Canonical occupation sewing

## Abstract

Ungrouped absolute occupation summability for the literal canonical lattice fields.

The lattice data D, three integral charges, four external oscillator polynomials, and both signed offsets are arbitrary. For every complex q with norm less than one, including zero, the sum of the norms of the literal occupation terms converges. No rank, Gram positivity, growth, summability or energy-cutoff hypothesis is added.

**Definition 1.1 (Factorial coordinate form).**

Lean statement: `D5/S3/VertexAlgebra/Sewing/CanonicalOccupation.H`

*Formalization.* `D5/S3/VertexAlgebra/Sewing/CanonicalOccupation.H` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The existing FactorialFockMetric.inner. Its monomial diagonal is the product of occupation factorials; it is used for dual-coordinate resolution. No invariant BPZ or physical unitarity property is asserted.

**Definition 1.2 (Canonical scalar contraction).**

Lean statement: `D5/S3/VertexAlgebra/Sewing/CanonicalOccupation.A`

*Formalization.* `D5/S3/VertexAlgebra/Sewing/CanonicalOccupation.A` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The product of the actual canonical outer matrix coefficient with the actual inner coefficient divided by its factorial coordinate weight. The intermediate charge is beta+gamma and the mode shifts are r+level(d) and s-level(d).

**Definition 1.3 (Radially damped occupation term).**

Lean statement: `D5/S3/VertexAlgebra/Sewing/CanonicalOccupation.sewnTerm`

*Formalization.* `D5/S3/VertexAlgebra/Sewing/CanonicalOccupation.sewnTerm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The exact scalar contraction A multiplied by q to the occupation energy. Every occupation is retained separately.

**Theorem 1.4 (Absolute canonical occupation summability).**

Lean statement: `D5/S3/VertexAlgebra/Sewing/CanonicalOccupation.canonical_sewing_summable`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sewing/CanonicalOccupation.canonical_sewing_summable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every D, alpha, beta, gamma, u, v, w, p, r, s and q with norm(q)<1, Summable holds for d mapped to norm(sewnTerm D alpha beta gamma u v w p r s q d). The proof first derives the factorial creation coefficient from the actual polynomial derivative identity. Both branches of normalMinusOne give a finite exact coefficient recurrence, including the charge zero mode. Induction on the actual descendant word yields a row bound C(1+level(d))^K L^degree(d) and a complementary column bound S(1+level(d))^J times the product of (B/(k+1))^d(i,k)/d(i,k)!. Their product is summable after polynomial/geometric absorption. A finite expansion in the four external polynomials and exact cancellation of the inner factorial coordinate weight identify the literal canonical summands. All estimates are uniform in the signed modes and are proved before internal occupations are summed.

The original field definitions and normal products retain their Bakalov--Kac, Matsuo--Nagatomo and Carnahan attributions through the imported sources. Mathlib supplies multivariate polynomial derivatives, finite-support products, exponential and geometric estimates, and summability comparison. The repository integer-occupation character is used only after an actual-coefficient estimate. This is a new formal coefficient-estimate and summability proof in the repository; no external-literature novelty is claimed.

This scalar factorial-coordinate result includes rank-one Gram [2] and keeps arbitrary lattice data because the proof needs no additional restriction. It does not identify the form with BPZ, prove an invariant Hilbert metric, vector or operator convergence, boundary convergence, analytic channel reassociation, full CFT sewing, a Monster construction, or a string/AdS correspondence. Grouping by homogeneous energy and identifying radial canonical products remain separate downstream obligations.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Sewing/CanonicalOccupation.A`
- Truth anchor: `D5/S3/VertexAlgebra/Sewing/CanonicalOccupation.H`
- Truth anchor: `D5/S3/VertexAlgebra/Sewing/CanonicalOccupation.canonical_sewing_summable`
- Truth anchor: `D5/S3/VertexAlgebra/Sewing/CanonicalOccupation.sewnTerm`
- Dependency: [D5/S3/VertexAlgebra/Sewing/CanonicalOccupationRow](CanonicalOccupationRow.md)
