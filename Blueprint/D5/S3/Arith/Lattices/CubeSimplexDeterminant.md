# CubeSimplexDeterminant

## Abstract

The absolute augmented determinant on a cube is bounded by its largest value on sign matrices.

**Definition 1.1 (signMatrix).**

$$\forall (d : \mathbb{N}), \forall (V : \operatorname{Matrix} (\operatorname{Fin} d) (\operatorname{Fin} (d + 1)) \operatorname{Bool}), \operatorname{signMatrix} d V = (\operatorname{fun} i j \mapsto \operatorname{if} V i j \operatorname{then} 1 \operatorname{else} - 1)$$

*Formalization.* `D5/S3/Arith/Lattices/CubeSimplexDeterminant.signMatrix` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The absolute augmented determinant on a cube is bounded by its largest value on sign matrices.

**Definition 1.2 (delta).**

$$\forall (d : \mathbb{N}), \operatorname{delta} d = (\operatorname{Finset} . \operatorname{univ} . \operatorname{sup} (\operatorname{fun} V : \operatorname{Matrix} (\operatorname{Fin} d) (\operatorname{Fin} (d + 1)) \operatorname{Bool} \mapsto (\operatorname{augment} (\operatorname{signMatrix} d V)) . \operatorname{det} . \operatorname{natAbs}))$$

*Formalization.* `D5/S3/Arith/Lattices/CubeSimplexDeterminant.delta` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The absolute augmented determinant on a cube is bounded by its largest value on sign matrices.

**Theorem 1.3 (augment map).**

$$\forall \{R S : \operatorname{Type}\}, [\operatorname{CommRing} R] [\operatorname{CommRing} S] \forall \{d : \mathbb{N}\}, \forall (f : \operatorname{RingHom} R S), \forall (M : \operatorname{Matrix} (\operatorname{Fin} d) (\operatorname{Fin} (d + 1)) R), \operatorname{augment} (M . \operatorname{map} f) = (\operatorname{augment} M) . \operatorname{map} f$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/CubeSimplexDeterminant.augment_map` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The absolute augmented determinant on a cube is bounded by its largest value on sign matrices.

**Theorem 1.4 (augmented det smul).**

$$\forall \{R : \operatorname{Type}\}, [\operatorname{CommRing} R] \forall \{d : \mathbb{N}\}, \forall (c : R), \forall (M : \operatorname{Matrix} (\operatorname{Fin} d) (\operatorname{Fin} (d + 1)) R), (\operatorname{augment} (c \cdot M)) . \operatorname{det} =  c^{d} * (\operatorname{augment} M) . \operatorname{det}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/CubeSimplexDeterminant.augmented_det_smul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The absolute augmented determinant on a cube is bounded by its largest value on sign matrices.

**Theorem 1.5 (augmented det integer box bound).**

$$\forall \{d m : \mathbb{N}\}, (1 \le m) \to \forall (M : \operatorname{Matrix} (\operatorname{Fin} d) (\operatorname{Fin} (d + 1)) \mathbb{Z}), (\forall i j , | M i j | \le m) \to | (\operatorname{augment} M) . \operatorname{det} | \le (\operatorname{delta} d : \mathbb{Z}) *  (m : \mathbb{Z})^{d}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/CubeSimplexDeterminant.augmented_det_integer_box_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The absolute augmented determinant on a cube is bounded by its largest value on sign matrices.

**Theorem 1.6 (augmented det affine).**

$$\forall \{R : \operatorname{Type}\}, [\operatorname{CommRing} R] \forall \{d : \mathbb{N}\}, \forall (c : R), \forall (a : \operatorname{Fin} d \to R), \forall (M : \operatorname{Matrix} (\operatorname{Fin} d) (\operatorname{Fin} (d + 1)) R), (\operatorname{augment} (\operatorname{Matrix} . \operatorname{of} (\operatorname{fun} i j \mapsto c * M i j + a i))) . \operatorname{det} =  c^{d} * (\operatorname{augment} M) . \operatorname{det}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/CubeSimplexDeterminant.augmented_det_affine` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The absolute augmented determinant on a cube is bounded by its largest value on sign matrices.

**Theorem 1.7 (exists maximizing sign simplex).**

$$\forall (d : \mathbb{N}), \exists V : \operatorname{Matrix} (\operatorname{Fin} d) (\operatorname{Fin} (d + 1)) \mathbb{Z} , (\forall i j , | V i j | \le 1) \land | (\operatorname{augment} V) . \operatorname{det} | = \operatorname{delta} d \land (\operatorname{augment} V) . \operatorname{det} \neq 0 \land (\forall j , 0 \le (\operatorname{augment} V) . \operatorname{det} * \operatorname{cofactor} V j)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/CubeSimplexDeterminant.exists_maximizing_sign_simplex` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The absolute augmented determinant on a cube is bounded by its largest value on sign matrices.

**Theorem 1.8 (primitive cofactor admissible).**

$$\forall \{d m : \mathbb{N}\}, \forall (M : \operatorname{Matrix} (\operatorname{Fin} d) (\operatorname{Fin} (d + 1)) \mathbb{Z}), (\forall i j , | M i j | \le m) \to ((\operatorname{augment} M) . \operatorname{det} \neq 0) \to \forall (s : \mathbb{Z}), (s = 1 \lor s = - 1) \to (\forall j , 0 < s * \operatorname{cofactor} M j) \to (\operatorname{Finset} . \operatorname{univ} . \operatorname{gcd} (\operatorname{cofactor} M) = 1) \to (\operatorname{augment} M) . \operatorname{det} . \operatorname{natAbs} \in \operatorname{lengths} d m (d + 1)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/CubeSimplexDeterminant.primitive_cofactor_admissible` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The absolute augmented determinant on a cube is bounded by its largest value on sign matrices.

## References

- Truth anchor: `D5/S3/Arith/Lattices/CubeSimplexDeterminant.augment_map`
- Truth anchor: `D5/S3/Arith/Lattices/CubeSimplexDeterminant.augmented_det_affine`
- Truth anchor: `D5/S3/Arith/Lattices/CubeSimplexDeterminant.augmented_det_integer_box_bound`
- Truth anchor: `D5/S3/Arith/Lattices/CubeSimplexDeterminant.augmented_det_smul`
- Truth anchor: `D5/S3/Arith/Lattices/CubeSimplexDeterminant.delta`
- Truth anchor: `D5/S3/Arith/Lattices/CubeSimplexDeterminant.exists_maximizing_sign_simplex`
- Truth anchor: `D5/S3/Arith/Lattices/CubeSimplexDeterminant.primitive_cofactor_admissible`
- Truth anchor: `D5/S3/Arith/Lattices/CubeSimplexDeterminant.signMatrix`
- Dependency: [D5/S3/Arith/Lattices/CofactorKernel](CofactorKernel.md)
