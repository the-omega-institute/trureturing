# Searchable Window Decision

## Abstract

A searchable input window gives a Boolean decision for every decidable universal test.

**Theorem 1.1 (Searchable windows decide universal Boolean tests).**

$$((\forall q, C(\operatorname{select}(q))) \land (\forall q, (\exists z, C(z) \land q(z) = true) \Rightarrow q(\operatorname{select}(q)) = true)) \Rightarrow p(sut(\operatorname{select}((z \mapsto \neg p(sut(z)))))) = true \iff (\forall z, C(z) \Rightarrow p(sut(z)) = true).$$

*Proof.* Machine-checked in Lean as `D5/S0/Computability/Searchability/SearchableWindowDecision.searchable_window_forall_decidable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The search premise supplies a selector for every Boolean query. Its selected point lies in C, and whenever an in-domain point satisfies the query, the selected point satisfies it as well. The system function is total and the output test is Boolean.

The decision queries the selector for a counterexample to the test. If one exists, selector completeness makes the chosen test false. If none exists, selector membership makes the chosen test true, which is equivalent to universal truth throughout C.

Pinned packages and the repository were searched before proving. The finite-type universal-decision instance does not cover infinite searchable windows, and no selection-functional implementation was found, so the selector laws remain explicit theorem premises.

This theorem closes only the finite-decision clause of the source atom. The independent claim that an infinite searchable space exists remains residual and is not asserted here.

## References

- Truth anchor: `D5/S0/Computability/Searchability/SearchableWindowDecision.searchable_window_forall_decidable`
