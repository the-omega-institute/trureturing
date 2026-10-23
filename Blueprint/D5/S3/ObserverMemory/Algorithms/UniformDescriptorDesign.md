# Finite common-descriptor design and budget syntax

## Abstract

Finite common-descriptor design and budget syntax.

The descriptor tuple is selected before source quantification. Every source may have its own terminal epoch and phase witnesses. Shared compares all admitted sources at each common halt, across charts and across independently quantified terminal epochs. Feasibility is an intermediate native property and contains no assumption of solver correctness or installed outputs.

**Definition 1.1 (Validity includes unreachable reads).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/UniformDescriptorDesign.ValidFormula`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/UniformDescriptorDesign.ValidFormula` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The conjunction checks every read occurrence and its fixed descriptor block. An unreachable read is not exempt. Empty read conjunctions are true.

**Definition 1.2 (Every admitted original source reaches a halt).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/UniformDescriptorDesign.Total`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/UniformDescriptorDesign.Total` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For each chart, universally quantify its complete source tuple, require admission, and take the finite disjunction of H over all halt controls. An empty halt list gives false inside each admitted implication. Empty source families remain vacuous.

**Definition 1.3 (Two independent whole-source blocks).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/UniformDescriptorDesign.Shared`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/UniformDescriptorDesign.Shared` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The first tuple embeds in the left source block and the second tuple in a separate right block. Both H formulas share the outer descriptor tuple and bind separate terminal epochs. Admission is required for both sources before whole-row Same is interpreted.

For a fixed halt, the original Reach query is the finite chart disjunction of exists n, Adm_eta(n) and H_eta,h(n;delta), with the common descriptor tuple held free. Empty charts give false. The installation's chartSource solves the admitted tuple and terminal epoch query, and sourceSearch uses List.findSome? over every chart. This directly supplies the UDB.18 query and its complete default branch without an additional unused formula declaration.

**Definition 1.4 (One common descriptor choice).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/UniformDescriptorDesign.Phi`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/UniformDescriptorDesign.Phi` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The natural descriptor existential encloses Total, Shared and Valid, with no source-dependent descriptor choices. The result has Fin zero free coordinates.

**Definition 1.5 (The actual closed budget sentence).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/UniformDescriptorDesign.Psi`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/UniformDescriptorDesign.Psi` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The finite fold ranges over candidates of every size one through K and every graph/type assignment. Each disjunct is Phi. This is an actual closed Presburger formula, built with explicit finite products and folds; no solver interface or decision assumption is present.

**Definition 1.6 (Native eventuality on the original family).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/UniformDescriptorDesign.NativeTotal`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/UniformDescriptorDesign.NativeTotal` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every original source has its own finite native Run to a genuine halt. Epochs are unbounded and need not agree between sources.

**Definition 1.7 (Complete rows agree at every shared halt).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/UniformDescriptorDesign.NativeShared`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/UniformDescriptorDesign.NativeShared` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

All source pairs and all independently chosen halt epochs are quantified. This proves row constancy on each halt support. It does not assert that an arbitrary preloaded row equals that constant.

**Theorem 1.8 (Every occurrence has its exact validity predicate).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/UniformDescriptorDesign.valid_correct`

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/UniformDescriptorDesign.valid_correct` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original finite validity fold is equivalent to Valid on the exact descriptor blocks. Formula.realize_relabel and the existing finite-fold semantics supply this consumed validity binding.

**Theorem 1.9 (Native feasibility of the closed descriptor sentence).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/UniformDescriptorDesign.phi_correct`

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/UniformDescriptorDesign.phi_correct` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original Phi sentence is equivalent to Feasible. The installation completeness proof directly consumes the original semantic bridge, including exact native support and the original source chart surjectivity.

**Theorem 1.10 (Exact Valid Total and Shared semantics).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/UniformDescriptorDesign.design_correct`

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/UniformDescriptorDesign.design_correct` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Validity has its exact local predicate semantics. Under a valid Real-compatible literal assignment, Total is equivalent to native halting for every original source and Shared is equivalent to complete-row constancy on every native shared halt support. The disjoint admitted chart bijection supplies every original source; Same is used only on two admitted tuples.

**Definition 1.11 (Native graph feasibility before extraction).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/UniformDescriptorDesign.Feasible`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/UniformDescriptorDesign.Feasible` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

There is one valid numeric descriptor tuple whose supplied common realizations give native Total and Shared. No correct output or recovery conclusion is assumed. A later constructor must obtain a reaching admitted source, install its complete target row, and then use Shared.

**Theorem 1.12 (Exact bounded candidate feasibility).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/UniformDescriptorDesign.budget_correct`

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/UniformDescriptorDesign.budget_correct` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Psi is true precisely when one complete typed candidate of a positive size at most K is Feasible. This closes finite arithmetic construction and its native semantic characterization. UniformDescriptorInstallation consumes this characterization to produce eager literals and complete rows, and to prove original successful-table necessity and task correspondence.

## References

- Truth anchor: `D5/S3/ObserverMemory/Algorithms/UniformDescriptorDesign.Feasible`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/UniformDescriptorDesign.NativeShared`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/UniformDescriptorDesign.NativeTotal`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/UniformDescriptorDesign.Phi`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/UniformDescriptorDesign.Psi`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/UniformDescriptorDesign.Shared`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/UniformDescriptorDesign.Total`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/UniformDescriptorDesign.ValidFormula`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/UniformDescriptorDesign.budget_correct`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/UniformDescriptorDesign.design_correct`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/UniformDescriptorDesign.phi_correct`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/UniformDescriptorDesign.valid_correct`
- Dependency: [D5/S3/ObserverMemory/Algorithms/UniformDescriptorSupport](UniformDescriptorSupport.md)
