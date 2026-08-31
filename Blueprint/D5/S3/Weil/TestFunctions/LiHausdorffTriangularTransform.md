# Li-Hausdorff Triangular Transform

## Abstract

Li coefficients form an invertible lower-triangular transform of trace moments.

**Theorem 1.1 (Finite-prefix transform and its first inverse coordinates).**

$$\left(\forall N \in \operatorname{Natural}\left(\right),\; \operatorname{BlockTriangular}\left(\operatorname{liHausdorffMatrix}\left(N\right), \operatorname{toDual}\left(\operatorname{Fin}\left(N\right)\right)\right)\right) \land \left(\left(\forall N \in \operatorname{Natural}\left(\right),\; \operatorname{Bijective}\left(\operatorname{mulVec}\left(\operatorname{liHausdorffMatrix}\left(N\right)\right)\right)\right) \land \left(\left(\forall N \in \operatorname{Natural}\left(\right), p \in \operatorname{Fin}\left(N\right) \to \operatorname{Real}\left(\right), i \in \operatorname{Fin}\left(N\right),\; \operatorname{mulVec}\left(\operatorname{liHausdorffMatrix}\left(N\right), p\right)\left(i\right) = \left(\operatorname{val}\left(i\right) + 1\right) \cdot \sum_{j \in \operatorname{Iic}\left(i\right)} \frac{\operatorname{pow}\left(-1, \operatorname{val}\left(j\right) + 2\right) \cdot \operatorname{pow}\left(4, \operatorname{val}\left(j\right) + 1\right)}{\operatorname{val}\left(j\right) + 1} \cdot \operatorname{choose}\left(\operatorname{val}\left(i\right) + \operatorname{val}\left(j\right) + 1, \operatorname{val}\left(i\right) - \operatorname{val}\left(j\right)\right) \cdot p\left(j\right)\right) \land \left(\forall p \in \operatorname{Fin}\left(3\right) \to \operatorname{Real}\left(\right),\; \operatorname{let} lambda: \operatorname{Fin}\left(3\right) \to \operatorname{Real}\left(\right) = \operatorname{mulVec}\left(\operatorname{liHausdorffMatrix}\left(3\right), p\right); p\left(0\right) = \frac{lambda\left(0\right)}{4} \land \left(p\left(1\right) = \frac{4 \cdot lambda\left(0\right) - lambda\left(1\right)}{16} \land p\left(2\right) = \frac{lambda\left(2\right) + 15 \cdot lambda\left(0\right) - 6 \cdot lambda\left(1\right)}{64}\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/TestFunctions/LiHausdorffTriangularTransform.li_hausdorff_triangular_transform` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The one-indexed coefficient formula constructs a matrix on every finite prefix. Its entries above the diagonal vanish, while every diagonal entry is nonzero, so the induced vector map is bijective. Direct normalization of the three-dimensional prefix yields the three displayed inverse-coordinate identities.

## References

- Truth anchor: `D5/S3/Weil/TestFunctions/LiHausdorffTriangularTransform.li_hausdorff_triangular_transform`
