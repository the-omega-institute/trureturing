# The Dimension-Three Hesse SIC Certificate

## Abstract

Nine explicit qutrit vectors form the dimension-three Hesse SIC configuration.

**Theorem 1.1 (Nine Hesse vectors have constant overlap and resolve the identity).**

$$\forall r: Fin(9),\ \left\lVert v_{r} \right\rVert^{2} = 1,\\\land (\forall r, s: Fin(9),\ r \neq s \Rightarrow \lvert \langle v_{r}, v_{s} \rangle \rvert^{2} = \frac{1}{4}),\\\land \sum_{r: Fin(9)} v_{r} v_{r}^{*} = 3 I_{3}.$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumContext/HesseSicCertificate.hesse_sic_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let omega=exp(2 pi i/3). For k=0,1,2, the nine vectors are (0,1,-omega^k)/sqrt(2), (-omega^k,0,1)/sqrt(2), and (1,-omega^k,0)/sqrt(2), in that order. The Lean definitions hesseVector and hesseKet give these coordinates as functions on Fin 9 and as vectors in the complex Euclidean space on Fin 3.

Every vector has two coordinates of modulus one over sqrt two, so its squared norm is one. Within one support block, the complete off-diagonal table reduces to 1+omega or 1+omega^2, up to a unit phase. Across blocks, two vectors meet in exactly one coordinate. The squared modulus is therefore exactly one quarter for every distinct ordered pair.

For the rank-one projector sum, each diagonal entry receives six contributions of one half and is therefore three. Each off-diagonal entry is minus one half times 1+omega+omega^2, or its conjugate, and vanishes. Thus all nine matrix entries agree with three times the three-dimensional identity matrix.

The Lean proof evaluates the full finite tables from the displayed coordinates and proves the required cube-root identities from the complex exponential. It uses no numerical approximation, frozen D5 theorem, unchecked evaluator, private axiom, or restatement of the dimension-twenty-four Zauner modular certificate.

## References

- Truth anchor: `D5/S3/QuantumContext/HesseSicCertificate.hesse_sic_certificate`
