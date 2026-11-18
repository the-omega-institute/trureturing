# The actual all-scalar-center comparison

## Abstract

Every scalar center of the existing six-return word is controlled by the actual minus-identity count in separately doubled integer intervals, including real widths.

Fix a nonzero modulus c, alternating coefficients a1,a2 in ZMod c, and a scalar gamma with gamma squared equal to 1. The source uses the existing sixReturnWord, scalarReturn, ReturnRows, literalRowBox and minusSolutions. Every integer row remains an individual solution, even when its letters have equal residues. No primality, unit-coordinate or injectivity hypothesis enters this comparison.

**Theorem 1.1 (Original scalar counts in integer intervals).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiScalarCenters.scalarSolutions_card_le_minus_doubled`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/PascadiScalarCenters.scalarSolutions_card_le_minus_doubled` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For separate natural widths X,Y, the cardinality of the actual scalar-gamma solution set is at most 64 times minusSolutions c (2X) (2Y) a1 a2. The input equation is the existing sixReturnWord equal to scalarReturn gamma, not an abstract center-count supplier.

Construct the upper and lower integer homomorphisms into SL(2,ZMod c). A pair of the original transfer matrices equals minus the corresponding upper/lower product, so all six original letters give minus the group word. The original even-row cyclic order is exactly y2,y0,y1. The scalar -gamma gives an explicitly central group element; its determinant is 1 because gamma squared is 1.

Expand the cube of the two actual interval measures. An explicit bijection between ReturnRows and triples of integer pairs identifies its coefficient at scalar -gamma with the original integer solution cardinality, keeping every collision multiplicity. Apply the proved actual interval central comparison. The identity group coefficient is the original minus-identity count because the six-letter realization has the overall minus sign.

**Theorem 1.2 (Floors enumerate the real-width integer box exactly).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiScalarCenters.mem_scalarSolutionsReal`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/PascadiScalarCenters.mem_scalarSolutionsReal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For nonnegative real X,Y, membership in scalarSolutionsReal is equivalent to the three actual integer first-row coordinates satisfying real absolute value at most X, the three second-row coordinates satisfying absolute value at most Y, and the unchanged original six-return equation. Natural floors only enumerate these integer intervals; they neither reduce letters modulo c nor replace a real bound with a larger integer bound.

**Theorem 1.3 (Separate doubling for arbitrary nonnegative real widths).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiScalarCenters.scalarSolutionsReal_card_le_minus_doubled`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/PascadiScalarCenters.scalarSolutionsReal_card_le_minus_doubled` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary nonnegative real X,Y, the actual scalar-gamma count is at most 64 times the original minus-identity count with natural widths floor(2X),floor(2Y). Thus the upper bound uses the literal integer letters in the separately doubled real intervals.

Apply the natural-width result to floor(X),floor(Y). Embed each resulting doubled integer box into the actual box with real bounds 2X,2Y using floor(X)<=X and floor(Y)<=Y, then use cardinality monotonicity. This proves the real-width endpoint without assuming X,Y integral.

This module proves the all-center comparison with the exact original counts. It does not assert the later prime-cube upper bound for minusSolutions, sum over scalar roots, or the final uniform moment estimate; those need their own counting and parameter estimates. The constant 64 is the product of the six factors of 2 from the proved interval sandwich.

## References

- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiScalarCenters.mem_scalarSolutionsReal`
- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiScalarCenters.scalarSolutionsReal_card_le_minus_doubled`
- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiScalarCenters.scalarSolutions_card_le_minus_doubled`
- Dependency: [D5/S3/Arith/CharacterSums/PascadiIntervalAutocorrelation](PascadiIntervalAutocorrelation.md)
- Dependency: [D5/S3/Arith/CharacterSums/PascadiMinusRows](PascadiMinusRows.md)
