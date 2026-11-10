# Compiler

## Abstract

The original Gamma/two-filling compiler constructs a computed parent certificate with separate main and core sequences.

**Definition 1.1 (CompilerPermission).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/Compiler.CompilerPermission`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/Compiler.CompilerPermission` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The exact original permission: Gamma, or no vertical pair in EITHER actual child list together with a core vertex different from the interface. 

**Definition 1.2 (finishCore).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/Compiler.finishCore`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/Compiler.finishCore` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The terminal core schedule returns an ORIGINAL parent vertex. The e=p case consumes genuine Gamma and the nonempty original R. It also covers X=empty. 

**Definition 1.3 (compileParent).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/Compiler.compileParent`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/Compiler.compileParent` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Full original parent constructor on literal original grounds. Main uses the child main and P0/P1. Separate starts on Cout ALONE, uses Q0/Q1, the child core list, and the computed terminal cone/Gamma list. Cout and critical faces are filled from their explicit constructions, rather than supplied as hypotheses. 

**Theorem 1.4 (compileParent_critical).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/Compiler.compileParent_critical`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/Compiler.compileParent_critical` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact computed critical family is exposed by reduction of the actual constructor. This equation is consumed by the wheel one-step consequences. 

**Theorem 1.5 (compiler_main_fixed).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/Compiler.compiler_main_fixed`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/Compiler.compiler_main_fixed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Whole-endpoint coordinate fixedness uses the real native homotopy; no parallel simulated realization or homotopy is introduced. 

**Theorem 1.6 (collapseCone_orderedPairs).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/Compiler.collapseCone_orderedPairs`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/Compiler.collapseCone_orderedPairs` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The descending cone is an actual rectangle on the original ground. 

**Definition 1.7 (finishVertex).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/Compiler.finishVertex`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/Compiler.finishVertex` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The actual original terminal vertex, specified independently of any certificate: preserve p away from e, otherwise use the same finite choice as terminalAtInterface. 

**Definition 1.8 (finishFacePairs).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/Compiler.finishFacePairs`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/Compiler.finishFacePairs` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The entire terminal face list on the full original ground. Gamma is used only when e=p and X is nonempty; the X-empty case is the original Y-simplex. 

**Definition 1.9 (finishPairSchedule).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/Compiler.finishPairSchedule`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/Compiler.finishPairSchedule` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The terminal block selected by `finishCore`, with both the e=p Gamma branch and the original-vertex cone branch made explicit. 

**Theorem 1.10 (finishPairSchedule_faces).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/Compiler.finishPairSchedule_faces`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/Compiler.finishPairSchedule_faces` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Proof irrelevance identifies the chosen right Gamma from any existing Nonempty permission with the same choice in rightGammaPairs. No equality with a particular supplied witness is asserted. 

**Theorem 1.11 (finishCore_orderedPairs).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/Compiler.finishCore_orderedPairs`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/Compiler.finishCore_orderedPairs` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact list extraction for the private terminal constructor in the same owner. The proof follows its two tests and uses only the actual cone and Gamma/fibre schedules. 

**Theorem 1.12 (compileParent_vertex).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/Compiler.compileParent_vertex`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/Compiler.compileParent_vertex` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Computed parent vertex is consumed by the independent row seed recursion. 

**Theorem 1.13 (compileParent_main_orderedPairs).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/Compiler.compileParent_main_orderedPairs`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/Compiler.compileParent_main_orderedPairs` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Full main list: child-main replay, then the ordered filling blocks. 

**Theorem 1.14 (compileParent_separate_orderedPairs).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/Compiler.compileParent_separate_orderedPairs`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/Compiler.compileParent_separate_orderedPairs` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Full separate/core list: collars on `Cout` alone, child-core replay, then the original-vertex cone/Gamma terminal block, including e=p and X=∅. 

**Definition 1.15 (ParentExpansion).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/Compiler.ParentExpansion`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/Compiler.ParentExpansion` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Public endpoint consumed by row-history code. The two equalities are kept together so neither the main nor the separate recursion can be dropped. 

**Theorem 1.16 (compileParent_consumed_expansion).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/Compiler.compileParent_consumed_expansion`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/Compiler.compileParent_consumed_expansion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original-label source declaration consumed by the native compiler and row construction. 

## References

- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/Compiler.CompilerPermission`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/Compiler.ParentExpansion`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/Compiler.collapseCone_orderedPairs`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/Compiler.compileParent`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/Compiler.compileParent_consumed_expansion`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/Compiler.compileParent_critical`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/Compiler.compileParent_main_orderedPairs`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/Compiler.compileParent_separate_orderedPairs`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/Compiler.compileParent_vertex`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/Compiler.compiler_main_fixed`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/Compiler.finishCore`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/Compiler.finishCore_orderedPairs`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/Compiler.finishFacePairs`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/Compiler.finishPairSchedule`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/Compiler.finishPairSchedule_faces`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/Compiler.finishVertex`
- Dependency: [D5/S3/Geometry/OriginalLabelTwoSum/CompilerStages](CompilerStages.md)
- Dependency: [D5/S3/Geometry/OriginalLabelTwoSum/Cone](Cone.md)
