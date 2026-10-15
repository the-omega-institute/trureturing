# NativeWholeRowPlan

## Abstract

Native finite whole-row criterion and lawful source fibers

The finite preprocessing uses frontierList, classList, variableList, presentation, patternList, allPatterns and feasibleList to retain every cell and every variable. all_patterns_complete proves exhaustive enumeration; delta and delta_legal retain the complete joint old-class disequalities. boundList, collapse, allGround and groundBindings implement the normalized finite unifier classification used by planPair. pairPlans, exteriorVariables, cellPass, cellBudget, analyze and K0 combine it into the complete criterion and budget. pair_plan_correct supplies the semantic equality test, and the admitted-cell and whole-fiber service theorems use the successful criterion to select correct comparisons and attain that budget.

prefixAddresses, representative, phaseOneTasks, taskQueries, phaseOneQueries and taskOffset generate and locate the paid first-phase blocks. phaseOneReply, decodePattern and selectedPatterns recover the actual unique cell, as proved by phase_one_patterns_correct; phase_one_uniform_bound counts its calls. bindingAddress, bindingQueries, planQueries and phaseTwoQueries generate current-epoch template probes, while bindingsCheck, planCheck, pairReplies and relationReply reconstruct equality from their replies. pair_plan_correct and selected_cell_record_correct prove that renderRecord returns the entire original record. two_phase_uniform_bound bounds both query phases; recordRow recovers the least-index canonical row from that record.

**Theorem 1.1 (Row-Determined Representative Subtrees).**

$$\forall C: LiteralRow, (\forall v: \operatorname{Valuation}\left(\operatorname{Classes}\left(C\right), Source\right), (\forall d: \operatorname{Classes}\left(C\right), (\operatorname{subtree}\left(\operatorname{representative}\left(C, d\right), \operatorname{evaluateRow}\left(\operatorname{extend}\left(C, v\right), C\right)\right) = \operatorname{some}\left(\operatorname{v}\left(d\right)\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeWholeRowPlan.representative_subtree` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every literal row C, arbitrary complete class valuation v and appearing class d, the original canonical representative address reaches exactly v(d) in the filled row. Values need not be injective or images. Labels may be sparse, and every repeated occurrence uses its same class value. Native root experiments use these exact legal addresses on the entire actual fiber.

**Definition 1.2 (presentation).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeWholeRowPlan.presentation`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeWholeRowPlan.presentation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The structural frontier list and sorted retained class labels enumerate every original variable, including unused classes. An explicit list-index equivalence transports finPresentation without choice extraction.

**Definition 1.3 (feasibleList).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeWholeRowPlan.feasibleList`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeWholeRowPlan.feasibleList` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This executable list represents the complete finite feasible family. History is invariant throughout each cell, and every old class participates in feasibility.

**Definition 1.4 (planPair).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeWholeRowPlan.planPair`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeWholeRowPlan.planPair` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Run the actual finite unifier with occurs-check. Native failure rejects equality. Old-disequality collapse has priority over groundness. Genuine normalized bound keys are tested for empty variable support; free identity coordinates are excluded. pair_plan_correct turns this classification into an exact test of new-hole equality under all old disequalities, and selected_cell_record_correct uses those tests to recover the complete new record.

**Definition 1.5 (analyze).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeWholeRowPlan.analyze`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeWholeRowPlan.analyze` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The entire criterion checks exterior freedom and every reached unordered pair in every feasible cell. An empty feasible family gives vacuous success without an inhabited-source service premise. The successful checker result supplies stationary_cell_service and stationary_whole_fiber_service with the condition that every selected cell has a concrete exterior and only lawful ground-template comparisons. The problem is the executable ground-binding criterion and attaining stationary whole-row service of sparse literal history Theorem 74.4, with the complete retained fiber rather than a finite list of sources.

**Definition 1.6 (A ground-binding whole-row input).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeWholeRowPlan.groundBindingInput`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeWholeRowPlan.groundBindingInput` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Let G be ((alpha,beta),(beta,alpha)). The old cut is P={L}, its complete row is (hole 0,G), the new cut is Q={L,R}, and H is empty. groundBindingInput stores exactly that row, Q and H. The old fiber is every (z,G), with z an arbitrary finite nonempty Boolean tree, so its one old class is unbounded and the new target is the complete two-hole row. The checker enumerates 11 raw cells and 11 feasible cells, returns passes=true and maximum template cost 4, and gives K0=10. New-hole equality is precisely z=G; in the branch cell it requires all four genuine ground bindings, while constructor conflict rejects equality in a leaf cell. The closed successful-check fact is unconditional here. Every frontier variable occurs in the left pattern term, and solver soundness against the fixed ground sibling forces the image of every occurring variable to be ground; therefore every cell passes. This closes (analyze C Q H).passes=true and discharges the successful-check premise of stationary_whole_fiber_service. With base (G,G) and this P,Q,H, its exact specialization gives a terminating compiled stationary controller for every original source having this complete old row, equivalently every arbitrary finite nonempty Boolean tree z in (z,G), and every certified epoch N, with the proved call bound K0(input). The concrete evaluation reports templateMaximum=4 and K0=10; 15 complete runtime executions report 7 calls at epoch zero and 9 calls at epochs one through four. These numerical values are runtime measurements, not newly closed kernel numeral equalities. This is an application to the same whole-row service problem of Theorem 74.4, rather than a bound on z or a subtree-equality port. Actual equal and unequal sources exercise both complete partitions: (G,G) returns canonical names [0,0], and (((beta,beta),(beta,alpha)),G) returns [0,1]. Each uses 7 calls at epoch zero and 9 calls at epochs one through four. The returned exterior is (hole L,hole R), with all four ordered equality pairs in the equal case and only the two diagonals in the unequal case. These executions illustrate the universally quantified service theorem; they do not establish the original serial-update equivalence or resource optimality.

**Definition 1.7 (K0).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeWholeRowPlan.K0`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeWholeRowPlan.K0` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The uniform raw budget is twice the old-class count times two to the required depth minus one, plus the maximum complete ground-template leaf sum over feasible cells. Every repeated issued physical query remains charged.

**Definition 1.8 (recordRow).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeWholeRowPlan.recordRow`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeWholeRowPlan.recordRow` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The complete record contains the concrete exterior and every ordered equality pair. Canonical names are the least related reached indices rather than dense class ranks.

**Theorem 1.9 (all patterns complete).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeWholeRowPlan.all_patterns_complete`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeWholeRowPlan.all_patterns_complete` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The complete native statement is retained with its exact quantified scope and all premises. Native statement: theorem all_patterns_complete (C : LiteralRow) (d : Nat) (η : Patterns C d) : η ∈ allPatterns C d

**Theorem 1.10 (delta legal).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeWholeRowPlan.delta_legal`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeWholeRowPlan.delta_legal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

All distinct old-class pairs belong to the same Delta, including classes unused by a selected new equation. Native statement: theorem delta_legal {C : LiteralRow} {d : Nat} (η : Patterns C d) (v : Variables η → Source) : Diseq (delta η) v ↔ Function.Injective (oldValues η v)

**Theorem 1.11 (phase one uniform bound).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeWholeRowPlan.phase_one_uniform_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeWholeRowPlan.phase_one_uniform_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The complete native statement is retained with its exact quantified scope and all premises. Native statement: theorem phase_one_uniform_bound (C : LiteralRow) (d N : Nat) : (phaseOneQueries C d N).length ≤ 2 * (labels C).card * (2^d-1)

**Theorem 1.12 (two phase uniform bound).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeWholeRowPlan.two_phase_uniform_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeWholeRowPlan.two_phase_uniform_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The complete native statement is retained with its exact quantified scope and all premises. Native statement: theorem two_phase_uniform_bound (C : LiteralRow) (Q : CutSet) (H : History) (η : Patterns C (requiredDepth Q H)) (mem : η ∈ feasiblePatterns C (requiredDepth Q H) H) (N : Nat) : (phaseOneQueries C (requiredDepth Q H) N).length + (phaseTwoQueries Q η N).length ≤ K0 C Q H

**Theorem 1.13 (phase one patterns correct).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeWholeRowPlan.phase_one_patterns_correct`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeWholeRowPlan.phase_one_patterns_correct` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The retained representative reaches the actual old-class subtree. Original-present transport, paid block slicing and the supplied decoder identify the unique depth pattern, including early leaves and absent relative addresses. Native statement: theorem phase_one_patterns_correct (C : LiteralRow) (v : Classes C → Source) (d N : Nat) : selectedPatterns C d N ((phaseOneQueries C d N).map (fun q => readout q (substitution^[N] (evaluateRow (NativeCutFibers.extend C v) C)))) = fun b => (NativeDepthPatterns.decompose d (v b)).1

**Theorem 1.14 (pair plan correct).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeWholeRowPlan.pair_plan_correct`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeWholeRowPlan.pair_plan_correct` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The same all-solutions parameterization retains every original variable and old inequality. Actual delayed-template probes decide ground bindings against all finite competing sources. Native statement: theorem pair_plan_correct {C : LiteralRow} {d : Nat} (η : Patterns C d) (v : Variables η → Source) (legal : Diseq (delta η) v) (q r : Address) (A B : Term (Variables η)) (passing : (planPair (presentation η) (delta η) q r A B).kind ≠ .feasibleNonground) (N : Nat) : let plan := planPair (presentation η) (delta η) q r A B planCheck N plan ((planQueries η N plan).map (fun a => readout a (substitution^[N] (evaluate v (wholeTerm η))))) = true ↔ NativeTermUnification.evaluate v A = NativeTermUnification.evaluate v B

**Theorem 1.15 (selected cell record correct).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeWholeRowPlan.selected_cell_record_correct`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeWholeRowPlan.selected_cell_record_correct` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The entire second-phase chronological reply list yields the full literal record: concrete exterior, sorted reached holes, diagonals and every symmetrized equality pair. Native statement: theorem selected_cell_record_correct {C : LiteralRow} (Q : CutSet) (H : History) (hQ : CutPrefixFree Q) (η : Patterns C (requiredDepth Q H)) (pass : cellPass Q η = true) (v : Variables η → Source) (legal : Diseq (delta η) v) (N : Nat) : renderRecord Q η N ((phaseTwoQueries Q η N).map (fun a => readout a (substitution^[N] (evaluate v (wholeTerm η))))) = literalRecord Q (evaluate v (wholeTerm η))

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeWholeRowPlan.K0`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeWholeRowPlan.all_patterns_complete`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeWholeRowPlan.analyze`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeWholeRowPlan.delta_legal`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeWholeRowPlan.feasibleList`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeWholeRowPlan.groundBindingInput`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeWholeRowPlan.pair_plan_correct`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeWholeRowPlan.phase_one_patterns_correct`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeWholeRowPlan.phase_one_uniform_bound`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeWholeRowPlan.planPair`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeWholeRowPlan.presentation`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeWholeRowPlan.recordRow`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeWholeRowPlan.representative_subtree`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeWholeRowPlan.selected_cell_record_correct`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeWholeRowPlan.two_phase_uniform_bound`
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/DelayedTemplateCertificate](DelayedTemplateCertificate.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace](NativeGroundSolutionSpace.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/NativeHistoryCells](NativeHistoryCells.md)
