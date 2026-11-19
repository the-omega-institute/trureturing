# Canonical finite maxima for H0 compositions

## Abstract

Canonical finite maxima for H0 compositions

For every finite index type I and arbitrary directed port relation R, including the empty family and same-block entries, the original H0 family has SF two equal to 6|I| and beta two equal to 5|I|. Restriction to actual H0 fibers gives the beta upper bound; a whole bipartition side attains the lower bound. No connectivity or cycle restriction is introduced.

**Theorem 1.1 (sf family).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/Families/CompositionParameters.sf_family`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/Families/CompositionParameters.sf_family` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact declaration: theorem sf_family {I : Type*} [Fintype I] [DecidableEq I] (R : I → I → Prop) : SF (Amplification.family R) 2 = 6 * Fintype.card I.

**Theorem 1.2 (beta family).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/Families/CompositionParameters.beta_family`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/Families/CompositionParameters.beta_family` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact declaration: theorem beta_family {I : Type*} [Fintype I] [DecidableEq I] (R : I → I → Prop) : beta (Amplification.family R) 2 = 5 * Fintype.card I.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/Families/CompositionParameters.beta_family`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/Families/CompositionParameters.sf_family`
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/ExactCard](../ExactCard.md)
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/Semantics](../Semantics.md)
