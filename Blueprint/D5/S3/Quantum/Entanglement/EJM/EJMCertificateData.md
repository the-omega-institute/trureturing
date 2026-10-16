# The actual coefficient functions used by every certificate consumer

## Abstract

Original EJM integer coefficient data and its earned local invariances.

The literal coefficient data comes from fast-inflation commit 01fcd357ee715dcff721f6a5381aedd2985c5696, data/ejm_224_nl_certificate.txt, SHA256 35c0221dea06ba6daf3f8d9a8e01914bc87eaabc8307491fe927173f9a94b20e. The ten-coordinate and nine-coordinate dictionaries contain 4588 and 1192 integer coefficients. CoefficientTree is an explicit binary dictionary with empty and key/value/left/right node constructors. A coefficient is attached to an entire equality-pattern and local-coordinate orbit with no orbit-size multiplier. The four exported invariance theorems concern these original lookup definitions. Merely defining the dictionaries supplies no coefficient amplitude, exact contraction receipt, positive inflation-score margin or nonlocality theorem. Each such numerical or actual-context acceptance obligation must be discharged by the corresponding kernel-checked consumer.

**Definition 1.1 (Original integer dictionary interpretation).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMCertificateData.get`

*Formalization.* `D5/S3/Quantum/Entanglement/EJM/EJMCertificateData.get` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A matching key returns its stored integer. A smaller query descends left and a larger query descends right; an empty lookup returns zero. This executable interpretation is the original function used by later amplitude and contraction checks.

**Definition 1.2 (The full equality-pattern code).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMCertificateData.pattern`

*Formalization.* `D5/S3/Quantum/Entanglement/EJM/EJMCertificateData.pattern` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The code folds the equality test of every ordered coordinate pair into a natural number. Its definition retains the complete pairwise outcome equality relation; it does not enumerate an orbit or attach an orbit-size weight.

**Definition 1.3 (Twelve actual ten-coordinate maps).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMCertificateData.trianglePerm`

*Formalization.* `D5/S3/Quantum/Entanglement/EJM/EJMCertificateData.trianglePerm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The literal table gives the twelve local coordinate maps used by the triangle coefficient lookup. All subsequent orbit keys and symmetry proofs use this same table.

**Definition 1.4 (Twelve actual nine-coordinate maps).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMCertificateData.singletonPerm`

*Formalization.* `D5/S3/Quantum/Entanglement/EJM/EJMCertificateData.singletonPerm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The singleton coefficient lookup uses this literal twelve-map table in its original nine-coordinate order.

**Definition 1.5 (The minimum equality-pattern code across the given local maps).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMCertificateData.orbitKey`

*Formalization.* `D5/S3/Quantum/Entanglement/EJM/EJMCertificateData.orbitKey` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For an event and twelve supplied coordinate maps, the key is the finite minimum of their equality-pattern codes. This definition selects the dictionary query; it is not a positivity or amplitude certificate.

**Definition 1.6 (Composition indices for the actual triangle maps).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMCertificateData.triangleMul`

*Formalization.* `D5/S3/Quantum/Entanglement/EJM/EJMCertificateData.triangleMul` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The explicit twelve-by-twelve table records the composition index used in the local-coordinate invariance proof. The private proof checks its relationship to the actual triangle coordinate functions.

**Definition 1.7 (Composition indices for the actual singleton maps).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMCertificateData.singletonMul`

*Formalization.* `D5/S3/Quantum/Entanglement/EJM/EJMCertificateData.singletonMul` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The corresponding explicit composition table is used by the singleton coordinate invariance proof, together with the checked finite surjectivity of each multiplication row.

**Definition 1.8 (The complete original triangle coefficient dictionary).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMCertificateData.triangleCoefficients`

*Formalization.* `D5/S3/Quantum/Entanglement/EJM/EJMCertificateData.triangleCoefficients` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The public tree assembles the literal 4588-entry original dictionary. Private parts organize the same tree; their presence is data storage, not proof that any score bound is valid.

**Definition 1.9 (The complete original singleton coefficient dictionary).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMCertificateData.singletonCoefficients`

*Formalization.* `D5/S3/Quantum/Entanglement/EJM/EJMCertificateData.singletonCoefficients` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This public tree assembles the literal 1192-entry original singleton dictionary. Actual numerical consumers must use this interpretation and discharge their exact assertions about it.

**Definition 1.10 (Original ten-coordinate integer coefficient function).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMCertificateData.F1`

*Formalization.* `D5/S3/Quantum/Entanglement/EJM/EJMCertificateData.F1` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

F1 queries triangleCoefficients at the original triangle orbit key of its ten-coordinate event. Missing dictionary keys return zero according to the same interpreter.

**Definition 1.11 (Original nine-coordinate integer coefficient function).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMCertificateData.F2`

*Formalization.* `D5/S3/Quantum/Entanglement/EJM/EJMCertificateData.F2` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

F2 queries singletonCoefficients at the original singleton orbit key of its nine-coordinate event. The coefficient function itself contains no centered-score head sum or singleton factor 64.

**Theorem 1.12 (F1 is invariant under an injective common outcome map).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMCertificateData.F1_relabel`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/EJM/EJMCertificateData.F1_relabel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every event and injective map of the four outcome labels, relabeling every coordinate preserves the original F1 value because it preserves every pairwise equality test.

**Theorem 1.13 (F2 is invariant under an injective common outcome map).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMCertificateData.F2_relabel`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/EJM/EJMCertificateData.F2_relabel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The same equality-pattern argument preserves the original F2 lookup under a common injective outcome relabeling.

**Theorem 1.14 (F1 is invariant under each actual local coordinate map).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMCertificateData.F1_coordinate`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/EJM/EJMCertificateData.F1_coordinate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The checked composition and surjectivity of the actual finite coordinate tables reindex the orbit-key minimum, preserving F1 under each of the twelve triangle maps.

**Theorem 1.15 (F2 is invariant under each actual local coordinate map).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMCertificateData.F2_coordinate`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/EJM/EJMCertificateData.F2_coordinate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The corresponding original singleton coordinate action preserves the orbit-key minimum and the actual F2 value. These invariances supply symmetry premises, not numerical score bounds.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMCertificateData.F1`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMCertificateData.F1_coordinate`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMCertificateData.F1_relabel`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMCertificateData.F2`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMCertificateData.F2_coordinate`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMCertificateData.F2_relabel`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMCertificateData.get`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMCertificateData.orbitKey`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMCertificateData.pattern`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMCertificateData.singletonCoefficients`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMCertificateData.singletonMul`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMCertificateData.singletonPerm`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMCertificateData.triangleCoefficients`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMCertificateData.triangleMul`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMCertificateData.trianglePerm`
