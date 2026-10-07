# Part II A1ScalarSupply

## Abstract

Part II A1ScalarSupply.

**Theorem 1.1 (actual SL2 scalar product).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/PartIIA1ScalarSupply.actual_SL2_scalar_product`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/PartIIA1ScalarSupply.actual_SL2_scalar_product` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive q, M > q(2q+1), and finite field of size greater than 2(2q+1)^q, every bare automorphism tuple of SL2 satisfies PartIIScalarProductInput at length 4M. For every positive divisor tuple e of q, one actual correction tuple precedes all targets, and the ordered values use powers q/e. Sylow conjugacy and root-pair reconstruction derive all root laws.

**Theorem 1.2 (actual PSL2 scalar product).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/PartIIA1ScalarSupply.actual_PSL2_scalar_product`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/PartIIA1ScalarSupply.actual_PSL2_scalar_product` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the same q, length and field bounds, every bare PSL2 automorphism tuple satisfies the literal scalar PRODUCT at length 4M with one correction before all targets and exact q/e powers. Sylow conjugacy in the centre quotient and direct root reconstruction require neither a lift nor an automorphism-classification oracle.

**Theorem 1.3 (uniform PSL2 scalar products).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/PartIIA1ScalarSupply.uniform_PSL2_scalar_products`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/PartIIA1ScalarSupply.uniform_PSL2_scalar_products` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each positive q, M = q(2q+1)+1 gives length 4M and cutoff [2(2q+1)^q]^4, chosen before every finite field, bare PSL2 automorphism tuple and divisor sequence. Above that actual group-cardinality cutoff, the literal scalar PRODUCT holds with its global correction-before-target order.

**Theorem 1.4 (actual PSL2 twisted product).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/PartIIA1ScalarSupply.actual_PSL2_twisted_product`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/PartIIA1ScalarSupply.actual_PSL2_twisted_product` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite field of size greater than six, arbitrary prescribed pairs of PSL2 automorphism tuples have actual ordered twisted PRODUCT coverage at length sixteen. The q=1 scalar result and Lemma 4.1 construct genuine group witnesses; a root-image or perfectness oracle is unnecessary.

**Theorem 1.5 (uniform PSL2 transitive coverage).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/PartIIA1ScalarSupply.uniform_PSL2_transitive_coverage`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/PartIIA1ScalarSupply.uniform_PSL2_transitive_coverage` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive q set L = 4[q(2q+1)+1], m = 36L(q+36), and C = max([2(2q+1)^q]^4,6^4). Above C in actual PSL2 cardinality, every finite nonempty coordinate rank and every genuine compatible component/permutation automorphism tuple satisfy PrescribedCommutatorCoverage. The literal coordinate equation is retained. Mixed powered-component reconstruction consumes the proved scalar and sixteen-fold twisted products; no separate transitivity hypothesis is needed by this endpoint.

Nikolov and Segal, On finitely generated profinite groups, I: Strong completeness and uniform bounds, Annals of Mathematics 165 (2007), 171-238, DOI 10.4007/annals.2007.165.171, Section 10, Proposition 10.2 and equations (45)-(50) (pages 228-232). Part II: Products in quasisimple groups, Annals of Mathematics 165 (2007), 239-273, DOI 10.4007/annals.2007.165.239, Theorem 1.2, Lemma 4.1 (pages 247-248), and Lemma 7.1(a) with its A1 application (pages 257-261). These are formal adaptations and consequences of published mathematics, with explicit matrix, fixed-field and Sylow arguments. No originality claim or redistribution of the papers is made. Arbitrary automorphisms are handled for the A1 family; other finite-simple families, the full uniform scalar supplier, quasisimple central covers, all-length Proposition 10.2, uniform width and restricted Burnside bounds, and full strong completeness remain open.

## References

- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/PartIIA1ScalarSupply.actual_PSL2_scalar_product`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/PartIIA1ScalarSupply.actual_PSL2_twisted_product`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/PartIIA1ScalarSupply.actual_SL2_scalar_product`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/PartIIA1ScalarSupply.uniform_PSL2_scalar_products`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/PartIIA1ScalarSupply.uniform_PSL2_transitive_coverage`
- Dependency: [D5/S3/FiniteGroups/NikolovSegal/PartIILemma41](PartIILemma41.md)
- Dependency: [D5/S3/FiniteGroups/NikolovSegal/PartIIPSL2RootNormalization](PartIIPSL2RootNormalization.md)
- Dependency: [D5/S3/FiniteGroups/NikolovSegal/PartIISL2RootSylow](PartIISL2RootSylow.md)
