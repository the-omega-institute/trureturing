# Six-column square-lattice strip

## Abstract

Square-lattice strip transfer.

**Definition 1.1 (between).**

$$\operatorname{\mathit{ProperTransfer}}.\operatorname{\mathit{between}} = \operatorname{\mathit{Finset}}.\operatorname{\mathit{diag}}\left((\operatorname{\mathit{Finset}}.\operatorname{\mathit{univ}}: \operatorname{\mathit{Finset}}\left(\operatorname{\mathit{Fin}}\left(6\right)\right))\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/SquareStripDefects/ProperTransfer.between` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229457: six-column square-lattice defective three-colourings*. URL: <https://oeis.org/A229457>.

*Commentary.*

Each pair joins the same column in consecutive rows; horizontal bonds join adjacent columns in one row.

**Definition 1.2 (cl).**

$$\forall p: \operatorname{\mathit{Fin}}\left(6\right) \to \operatorname{\mathit{Fin}}\left(3\right), (\operatorname{\mathit{ProperTransfer}}.\operatorname{\mathit{cl}}\left(p\right) = (\operatorname{\mathit{Fin}}.\operatorname{\mathit{mk}}\left(\operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(\operatorname{\mathit{HardinA233127SquareStrip}}.\operatorname{\mathit{boundaryClass}}\left((\operatorname{\mathit{true}}, \operatorname{\mathit{true}}), p\right)\right) - 1\right): \operatorname{\mathit{Fin}}\left(10\right)))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/SquareStripDefects/ProperTransfer.cl` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229457: six-column square-lattice defective three-colourings*. URL: <https://oeis.org/A229457>.

*Commentary.*

The ten saturated proper-row classes use indices zero through nine. Natural subtraction truncates at zero.

**Definition 1.3 (T).**

$$\forall i: \operatorname{\mathit{Fin}}\left(10\right), (\forall j: \operatorname{\mathit{Fin}}\left(10\right), (\operatorname{\mathit{ProperTransfer}}.\operatorname{T}\left(i, j\right) = \operatorname{\mathit{Int}}.\operatorname{\mathit{ediv}}\left(\operatorname{\mathit{HardinA233127SquareStrip}}.\operatorname{\mathit{transfer}}\left((\operatorname{\mathit{Fin}}.\operatorname{\mathit{mk}}\left(\operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(i\right) + 1\right): \operatorname{\mathit{Fin}}\left(11\right)), (\operatorname{\mathit{Fin}}.\operatorname{\mathit{mk}}\left(\operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(j\right) + 1\right): \operatorname{\mathit{Fin}}\left(11\right))\right), 64\right)))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/SquareStripDefects/ProperTransfer.T` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229457: six-column square-lattice defective three-colourings*. URL: <https://oeis.org/A229457>.

*Commentary.*

This is the ten by ten saturated submatrix of the square scanner, with integer division by 64.

**Theorem 1.4 (raw successors).**

$$\forall p: \operatorname{\mathit{Fin}}\left(6\right) \to \operatorname{\mathit{Fin}}\left(3\right), ((\operatorname{\mathit{HardinThinGraphTransport}}.\operatorname{\mathit{proper}}\left(p\right)) \implies (\forall j: \operatorname{\mathit{Fin}}\left(11\right), (64 \cdot \sum_{r: \operatorname{\mathit{Fin}}\left(6\right) \to \operatorname{\mathit{Fin}}\left(3\right)} (((\operatorname{\mathit{if}} ((\operatorname{\mathit{HardinThinGraphTransport}}.\operatorname{\mathit{proper}}\left(r\right)) \land ((\forall i: \operatorname{\mathit{Fin}}\left(6\right), (p\left(i\right) \ne r\left(i\right))) \land (\operatorname{\mathit{HardinA233127SquareStrip}}.\operatorname{\mathit{boundaryClass}}\left((\operatorname{\mathit{true}}, \operatorname{\mathit{true}}), r\right) = j))) \operatorname{\mathit{then}} (1) \operatorname{\mathit{else}} (0)): \operatorname{\mathit{Int}})) = \operatorname{\mathit{HardinA233127SquareStrip}}.\operatorname{\mathit{transfer}}\left(\operatorname{\mathit{HardinA233127SquareStrip}}.\operatorname{\mathit{boundaryClass}}\left((\operatorname{\mathit{true}}, \operatorname{\mathit{true}}), p\right), j\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/SquareStripDefects/ProperTransfer.raw_successors` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229457: six-column square-lattice defective three-colourings*. URL: <https://oeis.org/A229457>.

*Commentary.*

Every labelled three-colour row has exactly 64 individual-colour scanner realizations. The scanner sum is transported through that fibre identity and the existing exact row-count theorem.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/SquareStripDefects/ProperTransfer.T`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/SquareStripDefects/ProperTransfer.between`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/SquareStripDefects/ProperTransfer.cl`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/SquareStripDefects/ProperTransfer.raw_successors`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233127Certificate](../../../Combinatorics/TraceAvoidingArrays/HardinA233127Certificate.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233127CertificateZero](../../../Combinatorics/TraceAvoidingArrays/HardinA233127CertificateZero.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233127Rows](../../../Combinatorics/TraceAvoidingArrays/HardinA233127Rows.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233175PairStrip](../../../Combinatorics/TraceAvoidingArrays/HardinA233175PairStrip.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255LiteralBridge](../../../Combinatorics/TraceAvoidingArrays/HardinA233255LiteralBridge.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255PairTransfer](../../../Combinatorics/TraceAvoidingArrays/HardinA233255PairTransfer.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255ShapeSymmetry](../../../Combinatorics/TraceAvoidingArrays/HardinA233255ShapeSymmetry.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinThinGraphTransport](../../../Combinatorics/TraceAvoidingArrays/HardinThinGraphTransport.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229584StripData](../StripDefects/HardinA229584StripData.md)
