# Literal Occurrence Compilation and Arbitrary Continuations

## Abstract

Finite CNF occurrence graphs with exact native continuation prefixes.

A Formula(n) is an ordered finite list of clauses over Fin(n). A clause is an ordered list of variable-polarity pairs. Every clause width is allowed. The source representation Conventional.Formula has finite binary-word names; BinaryNames.denseFormula renumbers exactly its distinct appearing names using the original rightmost-occurrence deduplication order. It retains every clause, polarity and occurrence. Repeated variables, repeated clauses, tautologies, empty clauses and the empty conjunction are included.

The fixed literal for index i is the original NativeBooleanAssignmentBanks.literal(n,i): RLL followed by the i-th word among the first n lexicographic words of length Nat.clog 2 (max 2 n). The same actual source u is used at every occurrence. assignment(n,u,i) is true precisely when readout(literal(n,i),substitution(u)) is branch. Positive literals accept branch alone; negative literals accept alpha, beta and absent. No restriction on replies, source height or source profile is imposed.

Targets are internal(i), success and failure. A Read record stores one complete literal address and a successor for each of the four replies. records(base,f) concatenates one record for every occurrence in input order, including unreachable occurrences. Within a clause, an accepting reply selects the next clause entry and another reply selects the next literal or failure. The empty conjunction entry is success. An empty clause entry is failure. These entries are compile-time labels and require zero transitions.

occurrences(f) is the sum of the clause lengths. evaluate(f,u) is the ordinary conjunction of the clause evaluations under assignment(n,u). resolve(place,S,F) maps internal(i) to place(i) and the two external labels to S and F. Installed(C,place,S,F,rs) requires each record (i,r) in rs to map to a native running state q with place(i)=inl(q), C.addr(q)=r.address and C.next(q,reply)=resolve(place,S,F,r.next(reply)) for every reply. Thus installation concerns the actual native Controller fields, rather than an abstract transition list.

**Theorem 1.1 (Prefix in Any Controller Containing the Records).**

$$\forall n: Nat, (\forall Q, H: Type, (\forall C: \operatorname{Controller}\left(Q, H\right), (\forall place: (Nat) \to K, (\forall S, F: K, (\forall u: Source, (\forall f: \operatorname{Formula}\left(n\right), ((\operatorname{Installed}\left(C, place, S, F, \operatorname{records}\left(0, f\right)\right)) \implies ((\operatorname{length}\left(\operatorname{records}\left(0, f\right)\right) = \operatorname{occurrences}\left(f\right)) \land (\operatorname{map}\left(fst, \operatorname{records}\left(0, f\right)\right) = \operatorname{range}\left(\operatorname{occurrences}\left(f\right)\right)) \land (\operatorname{Nonempty}\left(\operatorname{EvalsToInTime}\left(\operatorname{step}\left(C, u\right), \operatorname{resolve}\left(place, S, F, \operatorname{entry}\left(0, f\right)\right), \operatorname{some}\left(\operatorname{ite}\left(\operatorname{evaluate}\left(f, u\right), S, F\right)\right), \operatorname{occurrences}\left(f\right)\right)\right))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/CNF/OccurrenceCompiler.installed_prefix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Here K=Q+H is the original Controller state space. step(C,u,inl(q)) is some(C.next(q,readout(C.addr(q),substitution(u)))); step(C,u,inr(h)) is none. EvalsToInTime counts these actual native Read transitions and can end at a running state. Nonempty removes the choice of a particular bounded-run certificate from the proposition. The statement requires no termination or transition property of S or F, which can coincide or label loop Reads. The proof takes one actual transition for a tested literal, stops on its first satisfying reply, and composes the resulting clause prefixes.

The record identifiers are exactly 0 through occurrences(f)-1. The installed table premise includes every record, even when an entry or an earlier reply makes it unreachable. For a concrete disjoint installation these records are distinct running states. The general prefix statement also applies to any faithful relocation satisfying Installed.

plug(rs,C,S,F) has running states Fin(length(rs))+Q and the same Halt type H. embed maps an old running state q to inl(inr(q)) and an old Halt h to inr(h). The new state inl(i) stores rs[i]'s literal and resolves its four successors. placement(rs,F,i) is inl(inl(i)) when i is in range, and embed(F) otherwise. Valid(entry,rs) says every internal entry label is in range, and every internal successor j of a record i satisfies i<j<length(rs). This proves that compiled references never use the total extension outside the fragment.

For a conventional formula f, sourceAssignment(f,u,name) applies the original source assignment to NativeBooleanAssignmentBanks.localIndex(occurrences(f),name). The assignment domain is exactly the appearing-name subtype. Its size depends on distinct spellings, not the numeric magnitude of a name. slotMap(rs,F) abbreviates the function i:Fin(length(rs)) mapped to placement(rs,F,value(i)). Let dense=denseFormula(f), rs=records(0,dense), and linked=plug(rs,C,S,F) in the following statement. M is length(Conventional.occurrences(f)); these definitions also apply when M=0.

**Theorem 1.2 (Exact Installed Compiler on Every Actual Source).**

$$\forall f: Conventional.Formula, (\forall Q, H: Type, (\forall C: \operatorname{Controller}\left(Q, H\right), (\forall S, F: \operatorname{Sum}\left(Q, H\right), (\forall u: Source, ((\operatorname{length}\left(rs\right) = M) \land (\operatorname{map}\left(fst, rs\right) = \operatorname{range}\left(\operatorname{length}\left(rs\right)\right)) \land (\operatorname{Valid}\left(\operatorname{entry}\left(0, dense\right), rs\right)) \land (\operatorname{Injective}\left(\operatorname{slotMap}\left(rs, F\right)\right)) \land (\operatorname{Installed}\left(linked, \operatorname{placement}\left(rs, F\right), \operatorname{embed}\left(S\right), \operatorname{embed}\left(F\right), rs\right)) \land (\forall q: Q, ((\operatorname{addr}\left(linked, \operatorname{inr}\left(q\right)\right) = \operatorname{addr}\left(C, q\right)) \land (\forall r: Reply, (\operatorname{next}\left(linked, \operatorname{inr}\left(q\right), r\right) = \operatorname{embed}\left(\operatorname{next}\left(C, q, r\right)\right))))) \land (\operatorname{out}\left(linked\right) = \operatorname{out}\left(C\right)) \land (\operatorname{Nonempty}\left(\operatorname{EvalsToInTime}\left(\operatorname{step}\left(linked, u\right), \operatorname{resolve}\left(\operatorname{placement}\left(rs, F\right), \operatorname{embed}\left(S\right), \operatorname{embed}\left(F\right), \operatorname{entry}\left(0, dense\right)\right), \operatorname{some}\left(\operatorname{embed}\left(\operatorname{ite}\left(\operatorname{Conventional.evaluate}\left(f, \operatorname{sourceAssignment}\left(f, u\right)\right), S, F\right)\right)\right), M\right)\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/CNF/OccurrenceCompiler.native_occurrence_compiler` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

There are exactly M distinct new running states, one per original literal occurrence. Every original ambient literal, every original successor after the label embedding, and the entire Halt output function are preserved. The endpoint is the embedded supplied S when the original formula is true under sourceAssignment(f,u), and the embedded supplied F otherwise. Empty entries are aliases, so a continuation Read or Halt can already be the endpoint at zero calls. Reaching a continuation does not consume its transition or assert that it terminates.

Forward internal indices and the clause induction bound the prefix by M charged occurrence calls on the one stationary source. All four successors are specified independently of the observed reply. The statement is unbounded symbolic correctness for arbitrary finite CNFs and arbitrary supplied native tables. These conclusions specify native control flow; serialized byte bounds and finite-machine construction time require additional results. The source interpretation and lexicographic literals reuse the original definitions; no assignment-realizability theorem is needed.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/CNF/OccurrenceCompiler.installed_prefix`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/CNF/OccurrenceCompiler.native_occurrence_compiler`
- Dependency: [D5/S0/Computability/DenseClauseConversion](../../../../../S0/Computability/DenseClauseConversion.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/FiniteMenu/NativeBooleanAssignmentBanks](../FiniteMenu/NativeBooleanAssignmentBanks.md)
