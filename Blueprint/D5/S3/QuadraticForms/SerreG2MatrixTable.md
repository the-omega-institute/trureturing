# Integral G2 matrix relations

## Abstract

Integral matrices for the standard seven-dimensional G2 representation.

**Definition 1.1 (Fourteen integral matrices).**

$$\forall (i : \operatorname{Fin}\left(14\right)), (\operatorname{Matrix}\left(\operatorname{Fin}\left(7\right), \operatorname{Fin}\left(7\right), \operatorname{Int}\left(\right)\right))$$

*Formalization.* `D5/S3/QuadraticForms/SerreG2MatrixTable.basisMatrix` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Two coroot matrices and six positive and six negative root matrices are given with integer entries. They are classical representation data. They do not define the standard Serre object or assume its dimension.

**Definition 1.2 (Integral bracket coefficients).**

$$\forall (i : \operatorname{Fin}\left(14\right)), (\forall (j : \operatorname{Fin}\left(14\right)), (\operatorname{Fin}\left(14\right) \to \operatorname{Int}\left(\right)))$$

*Formalization.* `D5/S3/QuadraticForms/SerreG2MatrixTable.coefficients` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The integral structure constants describe each commutator in the fourteen matrices. The complete table is consumed by the scalar-extension and actual Serre-correspondence proof.

**Theorem 1.3 (Kernel-checked integral bracket identities).**

$$\forall (i : \operatorname{Fin}\left(14\right)), (\forall (j : \operatorname{Fin}\left(14\right)), (\operatorname{lie}\left(\operatorname{basisMatrix}\left(i\right), \operatorname{basisMatrix}\left(j\right)\right) = \operatorname{Finset}.\operatorname{sum}\left(\operatorname{Finset}.\operatorname{univ}\left(\right), (fun t \mapsto \operatorname{zsmul}\left(\operatorname{coefficients}\left(i, j, t\right), \operatorname{basisMatrix}\left(t\right)\right))\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/SerreG2MatrixTable.bracket` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every matrix identity is proved by Lean kernel reduction of its scalar entries. External code only generated the candidate data. The companion module transports these identities to every characteristic-zero field and constructs the genuine Serre map. These are classical G2 facts, with the KMV application credited to Haobo Ma then Wenlin Zhang; no priority is claimed.

## References

- Truth anchor: `D5/S3/QuadraticForms/SerreG2MatrixTable.basisMatrix`
- Truth anchor: `D5/S3/QuadraticForms/SerreG2MatrixTable.bracket`
- Truth anchor: `D5/S3/QuadraticForms/SerreG2MatrixTable.coefficients`
