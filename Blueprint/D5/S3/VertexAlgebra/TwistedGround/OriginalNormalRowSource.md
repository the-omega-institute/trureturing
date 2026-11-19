# Original three-slot normal Gaussian Laurent row

## Abstract

Original three-slot normal Gaussian Laurent row

These are finite algebraic identities on the original lattice oscillator carrier. No positivity, analytic convergence, frequency cutoff or charge truncation is assumed. The determinant-unit hypothesis is retained exactly where the original normal and corrected operators require it.

**Definition 1.1 (affineLaurent).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalNormalRowSource.affineLaurent`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/OriginalNormalRowSource.affineLaurent` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

A Laurent polynomial supported at the original occupation weight, with amplitude given by the independent finite affine Gaussian coefficient.

**Definition 1.2 (normalMatrix).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalNormalRowSource.normalMatrix`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/OriginalNormalRowSource.normalMatrix` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

The symmetric three-slot kernel has source/input, source/output and input/output blocks from the original signed currents and Gram matrix. Its source/source, input/input and output/output blocks vanish.

**Definition 1.3 (normalMean).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalNormalRowSource.normalMean`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/OriginalNormalRowSource.normalMean` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

The source mean is zero; input and output means are the original negative charge pairings.

**Definition 1.4 (normalWeight).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalNormalRowSource.normalWeight`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/OriginalNormalRowSource.normalWeight` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

Source frequency r has weight -2r; an input mode has weight minus (2n+1), and an output mode has weight plus (2n+1).

**Theorem 1.5 (original_normal_row_finite).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalNormalRowSource.original_normal_row_finite`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalNormalRowSource.original_normal_row_finite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

For every finite embedding into the original oscillator indices, all three occupations, arbitrary charge, every integer exponent and the original determinant-unit hypothesis, the actual signed Wick row of oscillatorNormal equals the product of all three factorial weights times the ordinary Gaussian Laurent coefficient at e+chargeNorm(a).

**Definition 1.6 (normalLaurentRow).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalNormalRowSource.normalLaurentRow`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/OriginalNormalRowSource.normalLaurentRow` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

Use exactly the union of the three occupation supports, including the empty union. The finite polynomial exponential is summed through total occupation degree, and the auxiliary coordinate is specialized by a bounded coefficient sum.

**Theorem 1.7 (original_normal_row).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalNormalRowSource.original_normal_row`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalNormalRowSource.original_normal_row` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

The same normal-row identity holds for every original source, input and detector occupation, with no finite-frequency replacement of the carrier.

**Theorem 1.8 (original_corrected_normal_convolution).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalNormalRowSource.original_corrected_normal_convolution`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalNormalRowSource.original_corrected_normal_convolution` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

The actual oscillatorCorrected row is the finite sum over original charged Corr shifts and residual occupations, with coefficient_delta(Corr_s), the residual factorial and the normal Laurent row at e+2s+chargeNorm(a). Both external factorials remain outside the sum.

The proof compares the actual charged seed and signed-current recurrences with the independently defined Gaussian moments. Finite mode reindexing, the actual Gram-colour contraction and strong occupation induction identify the row. Restricted-coordinate and native-exponential normalization give the same coefficients on enlarged finite supports.

Attribution: finite Gaussian/Wick calculus and factorial Fock normalization are classical. The lattice and twisted-current suppliers retain their FLM, Dong--Nagatomo and Bakalov--Kac attributions. The exact composition on the original repository carrier is repo-derived; no external novelty is asserted. The bibliographic background does not supply an uninspected theorem or replace these proofs.

The downstream original identityK and two-row sewing remain open, with all four external factorials, both chargeScalar factors, one left average and the original inverse -Ginv/(k+1). These row identities do not establish VOA or Jacobi axioms, crossing, Monster, CFT, BRST, string dynamics or a physical realization.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalNormalRowSource.affineLaurent`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalNormalRowSource.normalLaurentRow`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalNormalRowSource.normalMatrix`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalNormalRowSource.normalMean`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalNormalRowSource.normalWeight`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalNormalRowSource.original_corrected_normal_convolution`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalNormalRowSource.original_normal_row`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalNormalRowSource.original_normal_row_finite`
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/ElementaryGaussianContraction](ElementaryGaussianContraction.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/OriginalChargedRowSource](OriginalChargedRowSource.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/OriginalFourMChargeCoset](OriginalFourMChargeCoset.md)
