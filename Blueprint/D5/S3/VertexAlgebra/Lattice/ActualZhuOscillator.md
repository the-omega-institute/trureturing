# Literal lattice Zhu source relations

## Abstract

ActualZhuOscillator

The native carrier is the complete finite-support sum over integral lattice charges of the complex oscillator polynomial algebra. O is the original literal span of circles with unrestricted second state. Positive definiteness is the sole extra lattice hypothesis for quotient multiplication. No restriction to nonzero rank, nonzero charge, a preferred dual class or a unique minimum is imposed.

Dong, Li and Mason, Certain associative algebras similar to U(sl2) and Zhu's algebra A(V_L), DOI 10.1006/jabr.1997.7112, arXiv q-alg/9605032v1, Theorem 3.4 and Remark 2.11, supply the classical lattice Zhu framework. The native fields, grading, creation and translation retain their original definitions. The quotient product and literal circle relations use the original binomial coefficient choose(m,i).

ActualZhuGroundCurrent and ActualZhuProduct supply the current grade and complete higher circles. Their fixed-numerator Pascal rows reduce every negative current to mode minus one in the literal quotient. ActualZhuCurrentNormalForm uses this reduction for arbitrary oscillator tails.

**Theorem 1.1 (Complete higher-circle row).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/ActualZhuOscillator.current_higherCircle`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/ActualZhuOscillator.current_higherCircle` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The weight-one higher circle is the full Pascal sum of fixed-numerator neighboring negative-current rows, with no omitted binomial terms.

**Theorem 1.2 (Triangular fixed-numerator elimination).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/ActualZhuOscillator.current_pair_mem_zhuO`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/ActualZhuOscillator.current_pair_mem_zhuO` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Strong induction separates the leading fixed-numerator row from the complete higher circle; every remaining row has a strictly smaller index.

**Theorem 1.3 (Physical negative-current reduction).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/ActualZhuOscillator.negative_current_class`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/ActualZhuOscillator.negative_current_class` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original state v, pi(h_i(-n-1)v)=(-1)^n pi(h_i(-1)v).

**Theorem 1.4 (Arbitrary oscillator tails).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/ActualZhuOscillator.oscillator_variable_class`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/ActualZhuOscillator.oscillator_variable_class` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The reduction applies to single(delta,X(i,n)p) for every charge and oscillator polynomial, including the zero polynomial.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Lattice/ActualZhuOscillator.current_higherCircle`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/ActualZhuOscillator.current_pair_mem_zhuO`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/ActualZhuOscillator.negative_current_class`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/ActualZhuOscillator.oscillator_variable_class`
- Dependency: [D5/S3/VertexAlgebra/Lattice/ActualZhuGroundCurrent](ActualZhuGroundCurrent.md)
