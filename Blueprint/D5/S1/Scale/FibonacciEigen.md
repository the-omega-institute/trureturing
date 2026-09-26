# Fibonacci Substitution Spectrum

## Abstract

The Fibonacci substitution has two golden eigenpairs and an exact contracting error.

**Theorem 1.1 (Golden eigenpairs and contracting error).**

$$\forall n \in \mathbb{N},\ \operatorname{expandingEigenvector}\neq 0 \land \operatorname{fibonacciSubstitution}\operatorname{expandingEigenvector}=\varphi\operatorname{expandingEigenvector} \land \operatorname{contractingEigenvector}\neq 0 \land \operatorname{fibonacciSubstitution}\operatorname{contractingEigenvector}=\operatorname{contractingEigenvalue}\operatorname{contractingEigenvector} \land (F_{n}\varphi-F_{n+1})=-\operatorname{contractingEigenvalue}^{n}$$

*Proof.* Machine-checked in Lean as `D5/S1/Scale/FibonacciEigen.fibonacci_substitution_spec` (`✓ std3`). ∎

*Citation.* Thomas Koshy (2001). *Fibonacci and Lucas Numbers with Applications*. DOI: [10.1002/9781118033067](https://doi.org/10.1002/9781118033067).

*Commentary.*

The explicit substitution matrix has nonzero expanding and contracting eigenvectors, and the same theorem gives the exact signed Fibonacci error for every natural index.

Residue-period applications of the same substitution: `D5/L/renault2013periodrankorder`. PCL in the existing WSS dossier separates sampling stride, external prime-period coupling and native factor multiplicities. It gives exact joint-period thresholds, arbitrary-depth auxiliary period carriers, and the paired ternary block periods. Those are ordinary mathematical results with their own rank and lifting proofs, not conclusions of this real-eigenpair Lean theorem. The formal statement and provenance above remain unchanged; no WSS prime is constructed by this link.

Cubic reciprocity on the same integer block depths: `D5/L/dunn2024cubicreciprocity`. GCR in the existing WSS dossier proves single-layer and interlevel cubic-character balances, individual earlier-prime conditions and a Kummer interpretation. Under a P-squared Q-cubed block factorization it constrains the square factor. These are ordinary proofs using classical reciprocity, not conclusions of this Lean declaration. No WSS example, elimination of that pattern or kernel certification is claimed.

The continuation GCR.7-GCR.12 retains both conjugate prime directions, the inert-prime-two balance and the resulting normal Kummer extension. It derives rational cubic conditions on the square factor, proves their comparison-prime compatibility and gives an exact irreducible cubic Thue descent with its original Lucas-coordinate condition. Source roles remain in `D5/L/dunn2024cubicreciprocity`. These are ordinary mathematical statements; the Lean declaration, authored formula and provenance above are unchanged.

GIR in that same companion Library note constructs actual independent points on two fixed elliptic curves from the golden blocks, with exact common-field degrees, discriminants and an orthogonal generated height lattice. It also constructs a cubic order whose maximal-order index has exactly the original WSS prime support in each block. These ordinary proofs use separately credited classical inputs; no rank oracle, WSS existence result or additional Lean conclusion is asserted by this context link.

GNT in the same companion computes the exact local normalization modules, conductor and intrinsic point-blowup chain of that order. Its arithmetic differential module is identified with the earlier Fibonacci mapping-torus torsion, and its marked three-torus cover has explicit cone homology. Complex torus links are separate comparison models, not mixed-characteristic analytic identifications. These are ordinary proofs; no new WSS prime or additional Lean conclusion is asserted.

GMI derives the exact generator-index form of the same order and proves that every golden layer is nonmonogenic. It classifies all pure-three-power generator indices and proves a localization obstruction at the actual third block. The regular maximal block nineteen refutes using this power-basis failure as a WSS witness. Local algebra generation and local index-form solvability are separated. Sources and full ordinary proofs remain in the companion; the authored Lean statement and provenance are unchanged.

GTC computes the dyadic splitting and exact local generator counts of the same golden field tower. It proves sharp common-index recurrences, global attaining elements and quadratic index-valuation growth. The full ordinary proofs and classical finite-field generator source are recorded in `D5/L/first2017separablegenerators`. This tower-presentation obstruction is distinct from the block normalization index detecting WSS; it adds no WSS witness or conclusion to this Lean theorem.

GGL in the same finite-generator companion adds the ramified three-adic decomposition and constructs one common integer generating tuple. It determines the exact global generator counts of both golden towers and the exact change after inverting three. The local-order boundary audit credits the parallel GoldenPrimePeriodBounds and GoldenPrimePowerOrder sources without treating their starting depth as one. These ordinary proofs do not add a Lean conclusion or a WSS prime-family decision to this declaration.

## References

- Truth anchor: `D5/S1/Scale/FibonacciEigen.fibonacci_substitution_spec`
- Dependency: [D5/S0/Carrier/GoldenRatio](../../S0/Carrier/GoldenRatio.md)
