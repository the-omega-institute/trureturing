# Recovering Balance and Labels

## Abstract

List-level imbalance and label injectivity show that zero-charge paths yield balanced choices without identifying distinct signed sectors.

**Theorem 1.1 (Choice imbalance equals ordered form flow).**

Lean statement: `D5/S3/Combinatorics/Zigzag/DecodedBalance.imbalance_eq_formsFlow`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Zigzag/DecodedBalance.imbalance_eq_formsFlow` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The choice function is read as its exact ordered list of labels. A finite-sum reindexing matches its per-vertex out-minus-in imbalance with formsFlow beginning at class two, so the path flow theorem speaks about the source's actual balance predicate.

**Theorem 1.2 (Even labels uniquely determine a path).**

Lean statement: `D5/S3/Combinatorics/Zigzag/DecodedBalance.evenPathForms_injective`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Zigzag/DecodedBalance.evenPathForms_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The first label recovers the signed start and each later low/high pair recovers the indexed transition, including coincident endpoint pairs. Recursive tail injectivity reconstructs the even antipodal terminal. This proves a property of labelled paths, not merely of the weighted transfer graph.

**Theorem 1.3 (Odd labels uniquely determine a path).**

Lean statement: `D5/S3/Combinatorics/Zigzag/DecodedBalance.oddPathForms_injective`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Zigzag/DecodedBalance.oddPathForms_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The same reconstruction uses the odd singleton terminal, whose table differs from the even pair. The separate theorem prevents an even-boundary argument from silently standing in for the odd inverse.

**Theorem 1.4 (The even zero-charge map is injective).**

Lean statement: `D5/S3/Combinatorics/Zigzag/DecodedBalance.evenZeroPathChoices_injective`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Zigzag/DecodedBalance.evenZeroPathChoices_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A zero-charge path maps to a Balanced choice because its boundary flow vanishes at every nonzero residue. Equal choices give equal form lists, and the distinct sector starts plus path-label injectivity give equal paths. Odd zero-charge paths have the analogous separately proved map and injectivity.

## References

- Truth anchor: `D5/S3/Combinatorics/Zigzag/DecodedBalance.evenPathForms_injective`
- Truth anchor: `D5/S3/Combinatorics/Zigzag/DecodedBalance.evenZeroPathChoices_injective`
- Truth anchor: `D5/S3/Combinatorics/Zigzag/DecodedBalance.imbalance_eq_formsFlow`
- Truth anchor: `D5/S3/Combinatorics/Zigzag/DecodedBalance.oddPathForms_injective`
- Dependency: [D5/S3/Combinatorics/Zigzag/ChoiceClassification](ChoiceClassification.md)
- Dependency: [D5/S3/Combinatorics/Zigzag/PathEncoding](PathEncoding.md)
