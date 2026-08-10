# Closure Readings Are Unreachable

## Abstract

No computable total reading decides a nontrivial behavior-level closure predicate.

**Theorem 1.1 (No same-layer reading decides closure).**

$$\neg\exists \ \text{computable total} C, \forall c, C(c) = 1 \iff c\in \operatorname{Closed}.$$

*Proof.* Machine-checked in Lean as `D5/S0/Computability/ClosureUndecidable.closure_reading_unreachable` (`✓ std3`). ∎

*Citation.* Henry Gordon Rice (1953). *Classes of recursively enumerable sets and their decision problems*. DOI: [10.1090/S0002-9947-1953-0053041-6](https://doi.org/10.1090/S0002-9947-1953-0053041-6).

*Commentary.*

Let a closure predicate on partial recursive codes be taken at the same layer as the objects it judges: whether a code counts as closed depends only on the behavior the code describes, so codes of equal evaluation are equi-closed. If the predicate is nontrivial - some code is closed and some code is not - then no total computable reading decides it. A reading that lives in the same kernel as its objects can therefore never certify closure across the board: the deciding hand would itself be a code, and the fixed-point diagonal builds a code that consults the reading on itself and enacts the opposite verdict, contradicting either answer.

The library was searched before proving: the pinned Mathlib already holds Rice's theorem in exactly this shape, as an equivalence between decidability of a behavior-respecting code predicate and the triviality of that predicate, proved from the second recursion theorem. The Lean declaration is a declared thin honest wrapper: it applies the upstream equivalence and discharges the two trivial branches against the nontriviality witnesses. The scope is honest - the statement formalizes the same-layer clause of the source theorem; its cross-layer relativization is a separate frontier item.

**Theorem 1.2 (The empty-ledger reading is unreachable).**

$$\neg\exists \ \text{computable total} C, \forall c, C(c) = 1 \iff \operatorname{eval}(c) = \varnothing.$$

*Proof.* Machine-checked in Lean as `D5/S0/Computability/ClosureUndecidable.empty_ledger_reading_unreachable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The wrapper is instantiated at the concrete closure predicate of the source proof: the empty-ledger behavior, a code whose described program certifies nothing because its evaluation is everywhere undefined. That predicate respects behavior by construction, the everywhere-undefined behavior has a code, and the total identity behavior supplies a code outside the class - so the predicate is nontrivial and no total computable reading decides it. The instantiation keeps the wrapper honest: the primary theorem is quantified over all same-layer closure predicates, and this witness exercises it on the one the diagonal argument toggles against. The statement is assembled in the repository from the wrapped theorem, so it is conservatively recorded as repository-derived.

## References

- Truth anchor: `D5/S0/Computability/ClosureUndecidable.closure_reading_unreachable`
- Truth anchor: `D5/S0/Computability/ClosureUndecidable.empty_ledger_reading_unreachable`
