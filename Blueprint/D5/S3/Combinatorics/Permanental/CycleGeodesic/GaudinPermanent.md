# GaudinPermanent

## Abstract

The Cauchy permanent equals a Gaudin determinant by interpolation and induction.

**Definition 1.1 (cauchy).**

$$\forall n \in \mathbb{N},\; \forall x \in \operatorname{Fin}\left(n\right) \to \mathbb{C},\; \forall y \in \operatorname{Fin}\left(n\right) \to \mathbb{C},\; \forall i \in \operatorname{Fin}\left(n\right),\; \forall j \in \operatorname{Fin}\left(n\right),\; \operatorname{cauchy}\left(x, y, i, j\right) = \left(x\left(i\right) - y\left(j\right)\right)^{-1}$$

*Formalization.* `D5/S3/Combinatorics/Permanental/CycleGeodesic/GaudinPermanent.cauchy` (`✓ std3`).

*Citation.* Alexandre Faribault, Dirk Schuricht (2012). *On the determinant representations of Gaudin models’ scalar products and form factors*. DOI: [10.1088/1751-8113/45/48/485202](https://doi.org/10.1088/1751-8113/45/48/485202). URL: <https://arxiv.org/abs/1207.2352v2>.

*Commentary.*

The reciprocal-difference matrix uses zero-based row and column parameters.

**Definition 1.2 (baryDerivative).**

$$\forall V \in Type,\; [\operatorname{Fintype}\left(V\right)] [\operatorname{DecidableEq}\left(V\right)] \forall x \in V \to \mathbb{C},\; \forall i \in V,\; \forall j \in V,\; \operatorname{baryDerivative}\left(x, i, j\right) = if (i = j) then \sum_{k \in \operatorname{Finset.erase}\left(\operatorname{Finset.univ}, i\right)} (\left(x\left(i\right) - x\left(k\right)\right)^{-1}) else \left(x\left(i\right) - x\left(j\right)\right)^{-1}$$

*Formalization.* `D5/S3/Combinatorics/Permanental/CycleGeodesic/GaudinPermanent.baryDerivative` (`✓ std3`).

*Citation.* Alexandre Faribault, Dirk Schuricht (2012). *On the determinant representations of Gaudin models’ scalar products and form factors*. DOI: [10.1088/1751-8113/45/48/485202](https://doi.org/10.1088/1751-8113/45/48/485202). URL: <https://arxiv.org/abs/1207.2352v2>.

*Commentary.*

The diagonal is the sum of the reciprocal node differences; the off-diagonal entries are their individual reciprocals.

**Definition 1.3 (gaudin).**

$$\forall V \in Type,\; \forall W \in Type,\; [\operatorname{Fintype}\left(V\right)] [\operatorname{DecidableEq}\left(V\right)] [\operatorname{Fintype}\left(W\right)] \forall x \in V \to \mathbb{C},\; \forall y \in W \to \mathbb{C},\; \operatorname{gaudin}\left(x, y\right) = \operatorname{Matrix.diagonal}\left(fun (i:V) \mapsto (\sum_{j:W} (\left(x\left(i\right) - y\left(j\right)\right)^{-1}))\right) - \operatorname{baryDerivative}\left(x\right)$$

*Formalization.* `D5/S3/Combinatorics/Permanental/CycleGeodesic/GaudinPermanent.gaudin` (`✓ std3`).

*Citation.* Alexandre Faribault, Dirk Schuricht (2012). *On the determinant representations of Gaudin models’ scalar products and form factors*. DOI: [10.1088/1751-8113/45/48/485202](https://doi.org/10.1088/1751-8113/45/48/485202). URL: <https://arxiv.org/abs/1207.2352v2>.

*Commentary.*

Subtracting the barycentric differentiation matrix gives the Gaudin matrix in the reciprocal-difference sign convention.

**Theorem 1.4 (gaudin_mulVec).**

$$\forall V \in Type,\; \forall W \in Type,\; [\operatorname{Fintype}\left(V\right)] [\operatorname{DecidableEq}\left(V\right)] [\operatorname{Fintype}\left(W\right)] \forall x \in V \to \mathbb{C},\; \forall y \in W \to \mathbb{C},\; \forall p \in \mathbb{C}[X],\; \left((\operatorname{Function.Injective}\left(x\right)) \land (\operatorname{Polynomial.degree}\left(p\right) < \operatorname{Fintype.card}\left(V\right))\right) \Rightarrow \operatorname{Matrix.mulVec}\left(\operatorname{gaudin}\left(x, y\right), fun (i:V) \mapsto \operatorname{Lagrange.nodalWeight}\left(\operatorname{Finset.univ}, x, i\right) \cdot \operatorname{Polynomial.eval}\left(x\left(i\right), p\right)\right) = fun (i:V) \mapsto \operatorname{Lagrange.nodalWeight}\left(\operatorname{Finset.univ}, x, i\right) \cdot \left((\sum_{j:W} (\left(x\left(i\right) - y\left(j\right)\right)^{-1})) \cdot \operatorname{Polynomial.eval}\left(x\left(i\right), p\right) - \operatorname{Polynomial.eval}\left(x\left(i\right), \operatorname{Polynomial.derivative}\left(p\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Permanental/CycleGeodesic/GaudinPermanent.gaudin_mulVec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor Rivin (2026). *Permanents of matrix ensembles: computation, distribution, and geometry*. URL: <https://arxiv.org/abs/2602.10141v3>.

*Commentary.*

Differentiating Lagrange interpolation describes the action on weighted polynomial evaluations.

**Theorem 1.5 (nodal_derivative_nonroot).**

$$\forall V \in Type,\; [\operatorname{Fintype}\left(V\right)] \forall y \in V \to \mathbb{C},\; \forall z \in \mathbb{C},\; \left(\forall j \in V,\; z \ne y\left(j\right)\right) \Rightarrow \operatorname{Polynomial.eval}\left(z, \operatorname{Polynomial.derivative}\left(\operatorname{Lagrange.nodal}\left(\operatorname{Finset.univ}, y\right)\right)\right) = \operatorname{Polynomial.eval}\left(z, \operatorname{Lagrange.nodal}\left(\operatorname{Finset.univ}, y\right)\right) \cdot (\sum_{j:V} (\left(z - y\left(j\right)\right)^{-1}))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Permanental/CycleGeodesic/GaudinPermanent.nodal_derivative_nonroot` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor Rivin (2026). *Permanents of matrix ensembles: computation, distribution, and geometry*. URL: <https://arxiv.org/abs/2602.10141v3>.

*Commentary.*

Away from every node, differentiating the nodal product gives its logarithmic derivative.

**Theorem 1.6 (gaudin_permanent).**

$$\forall n \in \mathbb{N},\; \forall x \in \operatorname{Fin}\left(n\right) \to \mathbb{C},\; \forall y \in \operatorname{Fin}\left(n\right) \to \mathbb{C},\; \operatorname{Function.Injective}\left(x\right) \Rightarrow \left(\left(\forall i \in \operatorname{Fin}\left(n\right),\; \forall j \in \operatorname{Fin}\left(n\right),\; x\left(i\right) \ne y\left(j\right)\right) \Rightarrow \operatorname{Matrix.det}\left(\operatorname{gaudin}\left(x, y\right)\right) = \operatorname{Matrix.permanent}\left(\operatorname{cauchy}\left(x, y\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Permanental/CycleGeodesic/GaudinPermanent.gaudin_permanent` (`✓ std3`). ∎

*Citation.* Alexandre Faribault, Dirk Schuricht (2012). *On the determinant representations of Gaudin models’ scalar products and form factors*. DOI: [10.1088/1751-8113/45/48/485202](https://doi.org/10.1088/1751-8113/45/48/485202). URL: <https://arxiv.org/abs/1207.2352v2>.

*Commentary.*

The row nodes are distinct and avoid every column parameter. Column parameters may repeat. Interpolating a determinant polynomial after its top coefficient vanishes reduces the identity to the permanent expansion at the preceding order.

## References

- Truth anchor: `D5/S3/Combinatorics/Permanental/CycleGeodesic/GaudinPermanent.baryDerivative`
- Truth anchor: `D5/S3/Combinatorics/Permanental/CycleGeodesic/GaudinPermanent.cauchy`
- Truth anchor: `D5/S3/Combinatorics/Permanental/CycleGeodesic/GaudinPermanent.gaudin`
- Truth anchor: `D5/S3/Combinatorics/Permanental/CycleGeodesic/GaudinPermanent.gaudin_mulVec`
- Truth anchor: `D5/S3/Combinatorics/Permanental/CycleGeodesic/GaudinPermanent.gaudin_permanent`
- Truth anchor: `D5/S3/Combinatorics/Permanental/CycleGeodesic/GaudinPermanent.nodal_derivative_nonroot`
