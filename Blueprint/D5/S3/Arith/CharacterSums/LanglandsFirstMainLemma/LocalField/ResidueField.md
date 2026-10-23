# Residue fields, trace and norm

## Abstract

Canonical residue fields and the actual algebraic norm and trace used by character pullback.

**Definition 1.1 (Algebraic norm).**

Lean statement: `D5/S3/Arith/CharacterSums/LanglandsFirstMainLemma/LocalField/ResidueField.residueNorm`

*Formalization.* `D5/S3/Arith/CharacterSums/LanglandsFirstMainLemma/LocalField/ResidueField.residueNorm` (`✓ std3`).

*Citation.* fukubillueda-web contributors (2026). *epsilon_FML finite-field Hasse–Davenport supplier*. URL: <https://github.com/fukubillueda-web/epsilon_FML/tree/b91ad93900a5e6d9207a4e6166ac94bb3bbcf3ed>.

*Commentary.*

For fields k and K, a finite underlying type K, and Algebra k K, residueNorm k K is the multiplicative map Algebra.norm k from K to k. It is the actual algebraic norm; the name does not require k and K to be presented as residue fields of local fields.

**Definition 1.2 (Algebraic trace).**

Lean statement: `D5/S3/Arith/CharacterSums/LanglandsFirstMainLemma/LocalField/ResidueField.residueTrace`

*Formalization.* `D5/S3/Arith/CharacterSums/LanglandsFirstMainLemma/LocalField/ResidueField.residueTrace` (`✓ std3`).

*Citation.* fukubillueda-web contributors (2026). *epsilon_FML finite-field Hasse–Davenport supplier*. URL: <https://github.com/fukubillueda-web/epsilon_FML/tree/b91ad93900a5e6d9207a4e6166ac94bb3bbcf3ed>.

*Commentary.*

Under the same hypotheses, residueTrace k K is the k-linear map Algebra.trace k K. After the inclusion into K, trace is the sum and norm is the product of x^(|k|^i) for 0 ≤ i < Module.finrank k K. The module also supplies their composition laws in scalar towers.

CharacterAPI uses residueNorm in normMulChar and residueTrace in traceAddChar. HasseDavenportLift then evaluates these pullbacks in gaussPolynomialWeight_minpoly_power and in the final lift. The local-field part of this module separately defines ResidueField F as the canonical valuation-ring quotient and reduction as congruence modulo lattice F 1; Extension imports that interface as well.

Source: epsilon_FML at immutable commit b91ad93900a5e6d9207a4e6166ac94bb3bbcf3ed, LanglandsFirstMainLemma/LocalField/ResidueField.lean; Apache-2.0. The exact license and original source hashes are in Library/Fourier/epsilonfml2026hassedavenport.md. These are attributed upstream definitions and results, not an open-problem resolution.

Supplier escape registration remains unfinished under https://github.com/the-omega-institute/trureturing/issues/5214: the original finite-field character/norm/trace telescope has no supplied faithful enrolled template with compiled audit evidence. This narrative does not complete that audit.

## References

- Truth anchor: `D5/S3/Arith/CharacterSums/LanglandsFirstMainLemma/LocalField/ResidueField.residueNorm`
- Truth anchor: `D5/S3/Arith/CharacterSums/LanglandsFirstMainLemma/LocalField/ResidueField.residueTrace`
- Dependency: [D5/S3/Arith/CharacterSums/LanglandsFirstMainLemma/LocalField/UnitFiltration](UnitFiltration.md)
