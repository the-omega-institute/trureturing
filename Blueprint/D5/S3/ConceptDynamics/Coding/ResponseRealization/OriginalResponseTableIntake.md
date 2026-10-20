# Intake of the original automorphism into the response construction

## Abstract

Original automorphism windows yield total finite tables and the same actual forward and inverse history maps.

V,E are arbitrary finite types with decidable vertex equality and discrete topologies on both V and E. G is essential and h is the original FullAut G. Natural radii a,b,c,d come with hab:Controls G h.val a b and hcd:Controls G h.val.symm c d. The module does not prove the existence of those controls; the preserved original application obtains them from fullAut_has_two_windows.

For every positive legal word, the private realization chooses an actual bi-infinite history realizing that word at time zero, using every_prescribed_word_has_actual_history. table reads the original h of that chosen realization at time a. table_apply translates the chosen history so its whole controlled interval matches an arbitrary history around any integer i; Controls gives equal outputs and commute_translate moves the readout back to coordinate a. This is a total table on all legal words, with no supplied-image restriction.

tables packages that construction for h and h inverse, with the same graph and four radii. actualWitness uses exactly h.val and h.val.symm and supplies their table equations, both inverse laws, both continuity fields and both unit-shift equations. It introduces no substitute conjugacy.

OriginalRootKernelCheck locally chooses the two windows once, forms pair=tables G hG h a b c d hab hcd and witness=actualWitness G hG h hab hcd, and passes both to OriginalPositiveWordAssembly.positive_word. That source application connects arbitrary native h to the original-domain word. OriginalRootPeriod6Base imports and opens this intake but has no use of tables or actualWitness in its body. None of this is evidence that the fullroot has finished native verification.

**Remark 1.1 (tables).**

Lean statement: `D5/S3/ConceptDynamics/Coding/ResponseRealization/OriginalResponseTableIntake.tables`

*Formalization.* `D5/S3/ConceptDynamics/Coding/ResponseRealization/OriginalResponseTableIntake.tables` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The TablePair contains the actual realization-based forward table for h and backward table for h inverse. The preserved original application and actualWitness consume it; this is predecessor reuse rather than another finite-window theorem.

**Remark 1.2 (actualWitness).**

Lean statement: `D5/S3/ConceptDynamics/Coding/ResponseRealization/OriginalResponseTableIntake.actualWitness`

*Formalization.* `D5/S3/ConceptDynamics/Coding/ResponseRealization/OriginalResponseTableIntake.actualWitness` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Supplies SameTableConjugacy of those exact tables with the original h and h inverse. All ten fields are explicit in source. The preserved original application passes the same witness to positive_word; downstream response reduction projects its seam and history laws.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResponseRealization/OriginalResponseTableIntake.actualWitness`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResponseRealization/OriginalResponseTableIntake.tables`
- Dependency: [D5/S3/ConceptDynamics/Coding/ResponseGraphs/OriginalResponseGraph](../ResponseGraphs/OriginalResponseGraph.md)
