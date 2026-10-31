# The exact connected source grade embeds in the actual diagram quotient

## Abstract

The exact connected source grade embeds in the actual diagram quotient

**Definition 1.1 (Actual connectivity, original genus, and every label population).**

Lean statement: `D5/S3/Combinatorics/Graph/Jacobi/ConnectedFlagGrade.flagGrade`

*Formalization.* `D5/S3/Combinatorics/Graph/Jacobi/ConnectedFlagGrade.flagGrade` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The grade of a finite cyclic flag diagram records whether its actual incidence graph is connected, its original edge-pair Euler genus, and the number of flags with each ordinary color or numbered anchor label. Selecting a true connectivity coordinate and the required genus and populations gives the connected fixed-grade source on this carrier. The exceptional bare topological circle remains a separate source case.

**Definition 1.2 (The same literal AS, IHX, CL, and flag-isomorphism generators).**

Lean statement: `D5/S3/Combinatorics/Graph/Jacobi/ConnectedFlagGrade.GradeRelator`

*Formalization.* `D5/S3/Combinatorics/Graph/Jacobi/ConnectedFlagGrade.GradeRelator` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A finite linear combination on a grade fiber is a GradeRelator exactly when its inclusion in the free space of all actual diagrams is a literal ActualRelator. The construction uses the same geometric generators and introduces no normalization-kernel relation. AS and both IHX branches preserve actual connectivity by transferring incidence walks through the local rotor tables. Explicit permutations conjugate the rotor cycles and preserve the number of actual owner orbits. Edge pairing is unchanged, so original genus is preserved. CL keeps the graph and exchanges exactly two ordinary labels, preserving every population.

**Definition 1.3 (The quotient within one exact source grade).**

Lean statement: `D5/S3/Combinatorics/Graph/Jacobi/ConnectedFlagGrade.GradedJacobiSpace`

*Formalization.* `D5/S3/Combinatorics/Graph/Jacobi/ConnectedFlagGrade.GradedJacobiSpace` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

GradedJacobiSpace is the rational free space on the exact grade fiber, divided by the span of its literal source generators. The original connectivity, genus and label populations are conditions on its actual diagram basis; they are not supplied as an abstract homogeneity assumption.

**Definition 1.4 (The natural quotient inclusion).**

Lean statement: `D5/S3/Combinatorics/Graph/Jacobi/ConnectedFlagGrade.gradeInclusion`

*Formalization.* `D5/S3/Combinatorics/Graph/Jacobi/ConnectedFlagGrade.gradeInclusion` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The inclusion sends a source basis diagram to the same actual diagram in the all-diagram AS, IHX and ordinary-CL quotient. A coordinate projection back to the fiber sends every all-diagram generator either to zero or to the same literal source generator, because every term of each actual relation has one exact grade.

**Theorem 1.5 (The source inclusion reflects zero).**

Lean statement: `D5/S3/Combinatorics/Graph/Jacobi/ConnectedFlagGrade.gradeInclusion_injective`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Jacobi/ConnectedFlagGrade.gradeInclusion_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every exact connectivity, Euler-genus and label-population grade, the natural quotient inclusion is injective. The proof constructs a left inverse on the quotients from the literal basis projection and the checked grade invariance of every actual relation. Thus a source class maps to zero exactly when it was already zero in that exact source quotient. This supplies the missing finite-flag connected fixed-genus quotient comparison; it does not by itself establish the global skeleton presentation, the insertion normal form, the exceptional bare-circle case or the full four-loop theorem.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Jacobi/ConnectedFlagGrade.GradeRelator`
- Truth anchor: `D5/S3/Combinatorics/Graph/Jacobi/ConnectedFlagGrade.GradedJacobiSpace`
- Truth anchor: `D5/S3/Combinatorics/Graph/Jacobi/ConnectedFlagGrade.flagGrade`
- Truth anchor: `D5/S3/Combinatorics/Graph/Jacobi/ConnectedFlagGrade.gradeInclusion`
- Truth anchor: `D5/S3/Combinatorics/Graph/Jacobi/ConnectedFlagGrade.gradeInclusion_injective`
- Dependency: [D5/S3/Combinatorics/Graph/Jacobi/FlagEulerBridge](FlagEulerBridge.md)
