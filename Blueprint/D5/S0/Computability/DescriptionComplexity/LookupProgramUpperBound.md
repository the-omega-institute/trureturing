# Lookup Program Upper Bound

## Abstract

A lookup compiler bounds the least cost of a total program consistent with a record.

**Theorem 1.1 (A table-lookup program bounds the spectrum bottom).**

$$\begin{gathered}\forall Record, TotalProgram: \operatorname{Type},\\{}\forall consistent: TotalProgram \to Record \to \operatorname{Prop},\\{}\forall programCost: TotalProgram \to \operatorname{Nat},\\{}\forall recordComplexity: Record \to \operatorname{Nat}, overhead: \operatorname{Nat},\\{}\forall compiler: \operatorname{LookupCompiler}(Record, TotalProgram, consistent, programCost, recordComplexity, overhead),\\{}\forall record: Record,\\{}\operatorname{spectrumBottom}(compiler, record) \leq \operatorname{recordComplexity}(record) + overhead.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S0/Computability/DescriptionComplexity/LookupProgramUpperBound.lookup_program_upper_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A LookupCompiler assigns each finite record a total program that agrees with the record. Its cost field states that this explicit lookup program uses at most the record-description cost plus a fixed overhead.

The spectrum bottom is the least natural-number cost among all total programs consistent with the record. The compiled lookup program is a member of that class, so minimality gives the displayed upper bound.

Pinned Mathlib has no matching description-complexity model. The proof therefore keeps the program and consistency semantics explicit while reusing Nat.find_min' for the least-witness inequality.

## References

- Truth anchor: `D5/S0/Computability/DescriptionComplexity/LookupProgramUpperBound.lookup_program_upper_bound`
