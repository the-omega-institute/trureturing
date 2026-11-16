# Finite multiplier sums in a simple ring.

## Abstract

Finite multiplier sums in a simple ring.

`D5/S3/FiniteGroups/GroupAlgebra/TwoSidedIdeal/SpanAsSum`

The statement and proof are reused from AxiomMath/Stacks contributors, revision 5ed82d14634e8d9576bb844c7bd4e3da66d450e7, Apache-2.0. The source retains the exact upstream paths and SHA-256 hashes. This is classical algebra used for the actual finite-group representation image; no new algebra theorem is claimed.

$\forall R \in Type*,\; [Ring\left(R\right)], [IsSimpleRing\left(R\right)], \forall a \in R,\; \left(\neg a = 0\right) \Rightarrow \left(\exists n \in Nat,\; \exists x \in Fin\left(n\right) \to R,\; \exists y \in Fin\left(n\right) \to R,\; \sum_{i:Fin\left(n\right)} x\left(i\right) \cdot a \cdot y\left(i\right) = 1\right)$

In a simple ring, every nonzero element generates the unit two-sided ideal. Membership in a generated two-sided ideal is expressed by a finite sum of left and right multiples. Applying this to one gives the displayed finite multiplier identity. It normalizes a nonzero coefficient in the tensor-simplicity proof; the length is existential and no bounded search is used.
