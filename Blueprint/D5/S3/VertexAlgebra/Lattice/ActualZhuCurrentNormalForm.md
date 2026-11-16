# Literal lattice Zhu source relations

## Abstract

ActualZhuCurrentNormalForm

The native carrier is the complete finite-support sum over integral lattice charges of the complex oscillator polynomial algebra. O is the original literal span of circles with unrestricted second state. Positive definiteness is the sole extra lattice hypothesis for quotient multiplication. No restriction to nonzero rank, nonzero charge, a preferred dual class or a unique minimum is imposed.

Dong, Li and Mason, Certain associative algebras similar to U(sl2) and Zhu's algebra A(V_L), DOI 10.1006/jabr.1997.7112, arXiv q-alg/9605032v1, Theorem 3.4 and Remark 2.11, supply the classical lattice Zhu framework. The native fields, grading, creation and translation retain their original definitions. The quotient product and literal circle relations use the original binomial coefficient choose(m,i).

ActualZhuAlgebra supplies associativity on the original quotient. ActualZhuGroundCurrent and ActualZhuOscillator supply the ground and higher-mode current identities. The resulting all-charge polynomial normal form is used by ActualZhuCurrentRelations and ActualZhuTransitionSpan to span the source quotient before applying any representation.

**Definition 1.1 (Neutral current class).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/ActualZhuCurrentNormalForm.H`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/ActualZhuCurrentNormalForm.H` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The class of the original current state in the full literal Zhu quotient.

**Definition 1.2 (Charged ground class).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/ActualZhuCurrentNormalForm.E`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/ActualZhuCurrentNormalForm.E` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The class of single(delta,1) for every integral charge.

**Theorem 1.3 (Native left action).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/ActualZhuCurrentNormalForm.oscillator_left_current`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/ActualZhuCurrentNormalForm.oscillator_left_current` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The left current subtracts the charge pairing when expressed as insertion of X(i,0).

**Theorem 1.4 (All-charge right-current transport).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/ActualZhuCurrentNormalForm.oscillator_right_current`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/ActualZhuCurrentNormalForm.oscillator_right_current` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Polynomial induction extends the direct ground right-current law to every oscillator tail using associativity and negative-current reduction, without a generic skew tower.

**Theorem 1.5 (Neutral currents commute).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/ActualZhuCurrentNormalForm.currents_commute`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/ActualZhuCurrentNormalForm.currents_commute` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The neutral specialization of right-current transport identifies both orders with the same oscillator product.

**Definition 1.6 (Current subalgebra).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/ActualZhuCurrentNormalForm.currentAlgebra`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/ActualZhuCurrentNormalForm.currentAlgebra` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

C is Algebra.adjoin over the complex numbers of the range of H. Only this subalgebra is given a commutative ring structure; Q remains possibly noncommutative.

**Definition 1.7 (Generator inside C).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/ActualZhuCurrentNormalForm.currentGenerator`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/ActualZhuCurrentNormalForm.currentGenerator` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each H_i is regarded as an element of the generated current subalgebra.

**Definition 1.8 (Physical polynomial evaluation).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/ActualZhuCurrentNormalForm.oscillatorEvaluation`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/ActualZhuCurrentNormalForm.oscillatorEvaluation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The complex algebra map from the original oscillator polynomials to C sends X(i,n) to (-1)^n H_i.

**Theorem 1.9 (Literal all-charge oscillator normal form).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/ActualZhuCurrentNormalForm.oscillator_normal_form`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/ActualZhuCurrentNormalForm.oscillator_normal_form` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every delta and p, pi(single(delta,p))=E_delta times oscillatorEvaluation(p). Equality is in the original source quotient, with no bottom-action kernel replacement.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Lattice/ActualZhuCurrentNormalForm.E`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/ActualZhuCurrentNormalForm.H`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/ActualZhuCurrentNormalForm.currentAlgebra`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/ActualZhuCurrentNormalForm.currentGenerator`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/ActualZhuCurrentNormalForm.currents_commute`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/ActualZhuCurrentNormalForm.oscillatorEvaluation`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/ActualZhuCurrentNormalForm.oscillator_left_current`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/ActualZhuCurrentNormalForm.oscillator_normal_form`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/ActualZhuCurrentNormalForm.oscillator_right_current`
- Dependency: [D5/S3/VertexAlgebra/Lattice/ActualZhuOscillator](ActualZhuOscillator.md)
