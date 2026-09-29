# CyclicStackFamily

## Abstract

Occurrence-scoped consumer families retain twenty-six original cyclic-stack laws on unbounded domains.

**Definition 1.1 (One role over complete domains).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/CyclicStackFamily.singleObservation`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/CyclicStackFamily.singleObservation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The shared constructor takes arbitrary parameter, state and output types, with a sole Unit role and Empty anchors. Concrete families retain all natural numbers, lists and dependent parameter tuples from their source laws. Each actual realization observes the relevant process, drain, sorting, gap, candidate, assembly or fibre operation; rejected realizations are operands for separate Reg proofs.

**Definition 1.2 (Process decomposition).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/CyclicStackFamily.runArena`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/CyclicStackFamily.runArena` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The top-level signature uses the whole input list as parameter and the whole stack as state, returning a list. actual reads process input stack. runArena equates that readout to the output and remaining stack of run, concatenated without changing run.

`D5/S1/Words/Patterns/CyclicStackPreimagesCore.process_eq_run`: runArena preserves the complete process decomposition.

**Definition 1.3 (Process permutation).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/CyclicStackFamily.permArena`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/CyclicStackFamily.permArena` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Over the same input and stack domains, permArena requires the observed output to be a permutation of input ++ stack. The shared rejected realization returns the empty list; the source law and a law-breaking instance are obligations of the Reg registration.

`D5/S1/Words/Patterns/CyclicStackPreimagesCore.process_perm`: permArena retains the original permutation law.

`D5/S1/Words/Patterns/CyclicStackPreimagesCore.process_append`: Append observes process (pre ++ suffix) stack and retains the canonical run pre stack and process suffix continuation on the right.

`D5/S1/Words/Patterns/CyclicStackPreimagesCore.drain_low_over_high`: DrainLow observes drain low (high :: stack), retaining the low/high inequalities and the canonical process-output sublist premise.

`D5/S1/Words/Patterns/CyclicStackPreimagesCore.no_two_lows_after_high`: TwoLows intervenes in the output-sublist premise of the contradiction law, retaining both low bounds, distinctness and the high bound.

`D5/S1/Words/Patterns/CyclicStackPreimagesCore.pending_low_forces_high_increase`: HighIncrease observes process (next :: input) (low :: high :: stack) in its sublist premise, from which the law still requires high < next.

`D5/S1/Words/Patterns/CyclicStackPreimagesCore.drain_high_while_low_remains`: DrainHigh reuses DrainLow's signature and drain realization; future-low membership, inequalities and the canonical process premise stay fixed.

`D5/S1/Words/Patterns/CyclicStackPreimagesCore.pending_low_drains_only_low_while_low_remains`: DrainPending observes the drain of the pending low/high stack and requires ([low], high :: stack), preserving the canonical process premise and every future-low condition.

`D5/S1/Words/Patterns/CyclicStackPreimagesCore.process_pending_low_while_low_remains`: ProcessPending reuses HighIncrease's observation in the conclusion, retaining canonical process in both its premise and right-hand continuation.

`D5/S1/Words/Patterns/CyclicStackPreimagesCore.no_lows_before_first_high`: InitialLows observes cyclicStackSort (pre ++ high :: rest) in the success premise and retains the conclusion pre = [] and all low/high bounds.

`D5/S1/Words/Patterns/CyclicStackPreimagesInvariants.gapped_filters_slots`: Gaps observes gapSlots m input in all three conclusions: reconstruction by assembleGaps, length agreement with highEntries, and filterMap recovery of lowEntries, under the original Gapped premise.

`D5/S1/Words/Patterns/CyclicStackPreimagesInvariants.success_perm_range`: SuccessPerm observes cyclicStackSort input in the success premise and retains permutation with range' 1 n.

`D5/S1/Words/Patterns/CyclicStackPreimagesInvariants.successful_gapped`: SuccessGapped reuses that sorting observation, retaining n ≥ 2 and the Gapped (n/2) conclusion.

`D5/S1/Words/Patterns/CyclicStackPreimagesInvariants.successful_lows_pairwise`: LowOrder observes lowEntries (n/2) input in the strict pairwise-order conclusion; Gapped and canonical sorting success remain premises.

`D5/S1/Words/Patterns/CyclicStackPreimagesInvariants.options_one_none`: OneNone observes slots.filterMap id in the filter premise, retaining the length premise and the bounded omitted-index witness for insertNone.

`D5/S1/Words/Patterns/CyclicStackPreimagesInvariants.candidateSlots_even`: EvenSlots observes candidateSlots m 0 m and retains equality to the mapped range of low entries for every m.

`D5/S1/Words/Patterns/CyclicStackPreimagesInvariants.candidateSlots_odd`: OddSlots observes candidateSlots omitted 0 (m+1), retaining omitted < m+1 and equality to insertNone omitted (range' 1 m).

`D5/S1/Words/Patterns/CyclicStackPreimagesInvariants.candidate_eq_assemble`: CandidateAssembly observes candidate m highCount omitted with all three natural parameters, retaining the canonical assembleGaps and candidateSlots expression.

`D5/S1/Words/Patterns/CyclicStackPreimagesInvariants.filledUntilLast_map_some`: FilledSome observes lows.map some under FilledUntilLast for every low list.

`D5/S1/Words/Patterns/CyclicStackPreimagesInvariants.filledUntilLast_insertNone_last`: FilledLast observes insertNone lows.length lows under the same predicate without restricting the list.

`D5/S1/Words/Patterns/CyclicStackPreimagesInvariants.successful_highs_of_filled_until_last`: HighOrder observes highEntries (n/2) input in the strict pairwise-order conclusion, preserving Gapped, FilledUntilLast and canonical sorting success.

`D5/S1/Words/Patterns/CyclicStackPreimagesFinalLow.successful_high_entries_final_low`: FinalHighs reuses the high-entry observation and retains the exact high range under Gapped, EndsWithLow and canonical sorting success.

`D5/S1/Words/Patterns/CyclicStackPreimagesFinalLow.assemble_insert_none_ends`: AssemblyEnds observes assembleGaps highs (insertNone omitted lows), retaining all length, omitted-index and low-bound premises of EndsWithLow.

`D5/S1/Words/Patterns/CyclicStackPreimagesCandidates.oddCandidate_lower_bound`: OddFibre observes the full fibre (2m+1) and retains its length lower bound m+1 for every positive m.

`D5/S1/Words/Patterns/CyclicStackPreimagesCandidates.evenCandidate_lower_bound`: EvenFibre observes the full fibre (2m) and retains the length lower bound one for every positive m.

`D5/S1/Words/Patterns/CyclicStackPreimages.zhan_bie_conjectures_3_4`: FibreCount reuses the even-fibre observation in the first conjunct and retains the canonical odd fibre in the second: for m ≥ 2 the lengths are one and m+1 respectively.

Each family is an occurrence-scoped intervention. Canonical process and other operation occurrences remain wherever the source model keeps them, including the premises of DrainLow, DrainHigh, DrainPending and ProcessPending. This is not a uniform global process-replacement claim. Source binding must reconstruct each full original statement, including its implicit parameters, hypotheses, bounds and all conjuncts.

The corresponding five Reg/D5/S1/Words/Patterns source mirrors carry the bridge, actual-law, variation, sensitivity and actual observational-dependence proofs, reusing Reg/Support/CyclicStackFamily where applicable. These repository-derived consumer definitions add no theorem wrappers and make no novelty, coverage or freeze claim. A raw open residual means unknown residual information, not infinity, undecidability or completeness.

## References

- Truth anchor: `D5/S1/Words/Patterns/CyclicStackPreimages.zhan_bie_conjectures_3_4`
- Truth anchor: `D5/S1/Words/Patterns/CyclicStackPreimagesCandidates.evenCandidate_lower_bound`
- Truth anchor: `D5/S1/Words/Patterns/CyclicStackPreimagesCandidates.oddCandidate_lower_bound`
- Truth anchor: `D5/S1/Words/Patterns/CyclicStackPreimagesCore.drain_high_while_low_remains`
- Truth anchor: `D5/S1/Words/Patterns/CyclicStackPreimagesCore.drain_low_over_high`
- Truth anchor: `D5/S1/Words/Patterns/CyclicStackPreimagesCore.no_lows_before_first_high`
- Truth anchor: `D5/S1/Words/Patterns/CyclicStackPreimagesCore.no_two_lows_after_high`
- Truth anchor: `D5/S1/Words/Patterns/CyclicStackPreimagesCore.pending_low_drains_only_low_while_low_remains`
- Truth anchor: `D5/S1/Words/Patterns/CyclicStackPreimagesCore.pending_low_forces_high_increase`
- Truth anchor: `D5/S1/Words/Patterns/CyclicStackPreimagesCore.process_append`
- Truth anchor: `D5/S1/Words/Patterns/CyclicStackPreimagesCore.process_eq_run`
- Truth anchor: `D5/S1/Words/Patterns/CyclicStackPreimagesCore.process_pending_low_while_low_remains`
- Truth anchor: `D5/S1/Words/Patterns/CyclicStackPreimagesCore.process_perm`
- Truth anchor: `D5/S1/Words/Patterns/CyclicStackPreimagesFinalLow.assemble_insert_none_ends`
- Truth anchor: `D5/S1/Words/Patterns/CyclicStackPreimagesFinalLow.successful_high_entries_final_low`
- Truth anchor: `D5/S1/Words/Patterns/CyclicStackPreimagesInvariants.candidateSlots_even`
- Truth anchor: `D5/S1/Words/Patterns/CyclicStackPreimagesInvariants.candidateSlots_odd`
- Truth anchor: `D5/S1/Words/Patterns/CyclicStackPreimagesInvariants.candidate_eq_assemble`
- Truth anchor: `D5/S1/Words/Patterns/CyclicStackPreimagesInvariants.filledUntilLast_insertNone_last`
- Truth anchor: `D5/S1/Words/Patterns/CyclicStackPreimagesInvariants.filledUntilLast_map_some`
- Truth anchor: `D5/S1/Words/Patterns/CyclicStackPreimagesInvariants.gapped_filters_slots`
- Truth anchor: `D5/S1/Words/Patterns/CyclicStackPreimagesInvariants.options_one_none`
- Truth anchor: `D5/S1/Words/Patterns/CyclicStackPreimagesInvariants.success_perm_range`
- Truth anchor: `D5/S1/Words/Patterns/CyclicStackPreimagesInvariants.successful_gapped`
- Truth anchor: `D5/S1/Words/Patterns/CyclicStackPreimagesInvariants.successful_highs_of_filled_until_last`
- Truth anchor: `D5/S1/Words/Patterns/CyclicStackPreimagesInvariants.successful_lows_pairwise`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/CyclicStackFamily.permArena`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/CyclicStackFamily.runArena`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/CyclicStackFamily.singleObservation`
- Dependency: [D5/S1/Words/Patterns/CyclicStackPreimages](../../../S1/Words/Patterns/CyclicStackPreimages.md)
- Dependency: [D5/S3/ConceptDynamics/InformationEscape/DependentFamily](DependentFamily.md)
