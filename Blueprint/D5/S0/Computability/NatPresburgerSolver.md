# Executable native decisions and Option solutions

## Abstract

Constructive Option contracts cover fixed parameters and all-coordinate solving.

BF(m,n) is the native finite-context bounded formula type, and NatTuple(r)=Fin r->Nat. test decides satisfaction for a complete free/bound valuation. solveBounded fixes the free valuation and returns Option(NatTuple(n)); solveAll returns Option(NatTuple(m+n)). Every statement below keeps the original native Realize semantics.

Existential closure, relabeling and witness extraction reuse the supplied native exs, relabel and Encodable.choose implementations. There is no new custom tuple enumeration or quantifier-elimination procedure. The search predicate is the executable Bool test. Proof-only classical reasoning does not replace the computational decision path.

These interfaces are useful for extracting finite natural assignments and for deciding formulas with arbitrary alternation and nested negation. They establish executable Lean definitions and exact semantic contracts. They do not establish a recursion-theoretic Computable theorem, a complexity estimate, or a uniform practical runtime bound. Encodable search cost depends on the tuple encoding; semantic correctness alone is not a measurement of runtime completion.

**Theorem 1.1 (Boolean native decision).**

$$\forall m \in Nat,\; \forall n \in Nat,\; \forall p \in \operatorname{BF}\left(m, n\right),\; \forall v \in \operatorname{NatTuple}\left(m\right),\; \forall xs \in \operatorname{NatTuple}\left(n\right),\; (\operatorname{test}\left(p, v, xs\right) = true) \iff (\operatorname{Realize}\left(p, v, xs\right))$$

*Proof.* Machine-checked in Lean as `D5/S0/Computability/NatPresburgerSolver.test_correct` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Vladimir Reshetnikov (2026). *ProveIt executable integer Presburger arithmetic*. URL: <https://github.com/VladimirReshetnikov/ProveIt/tree/ec9ab2ffd49f8861022d6f3d4c30205545a3386d/Logic/PresburgerArithmetic/Lean/PresburgerArithmetic>.

*Commentary.*

test calls the upstream integer decideHolds on compile(p) and environment(v,xs). Its contract composes the upstream Bool equivalence with compile_correct. realizeDecidable branches on the computed Bool; it does not use a classical proposition decision instance.

**Theorem 1.2 (A returned bound tuple satisfies the native formula).**

$$\forall m \in Nat,\; \forall n \in Nat,\; \forall p \in \operatorname{BF}\left(m, n\right),\; \forall v \in \operatorname{NatTuple}\left(m\right),\; \forall xs \in \operatorname{NatTuple}\left(n\right),\; (\operatorname{solveBounded}\left(p, v\right) = \operatorname{some}\left(xs\right)) \implies (\operatorname{Realize}\left(p, v, xs\right))$$

*Proof.* Machine-checked in Lean as `D5/S0/Computability/NatPresburgerSolver.solve_bounded_sound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Vladimir Reshetnikov (2026). *ProveIt executable integer Presburger arithmetic*. URL: <https://github.com/VladimirReshetnikov/ProveIt/tree/ec9ab2ffd49f8861022d6f3d4c30205545a3386d/Logic/PresburgerArithmetic/Lean/PresburgerArithmetic>.

*Commentary.*

solveBounded first tests native existential closure p.exs at the empty bound valuation, using the supplied realize_exs equivalence. Only in the positive branch does Encodable.choose select a finite tuple satisfying test=true; test_correct proves its original native satisfaction.

**Theorem 1.3 (Returning some is equivalent to existence).**

$$\forall m \in Nat,\; \forall n \in Nat,\; \forall p \in \operatorname{BF}\left(m, n\right),\; \forall v \in \operatorname{NatTuple}\left(m\right),\; (\exists xs \in \operatorname{NatTuple}\left(n\right),\; \operatorname{solveBounded}\left(p, v\right) = \operatorname{some}\left(xs\right)) \iff (\exists xs \in \operatorname{NatTuple}\left(n\right),\; \operatorname{Realize}\left(p, v, xs\right))$$

*Proof.* Machine-checked in Lean as `D5/S0/Computability/NatPresburgerSolver.solve_bounded_exists_some_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Vladimir Reshetnikov (2026). *ProveIt executable integer Presburger arithmetic*. URL: <https://github.com/VladimirReshetnikov/ProveIt/tree/ec9ab2ffd49f8861022d6f3d4c30205545a3386d/Logic/PresburgerArithmetic/Lean/PresburgerArithmetic>.

*Commentary.*

The right-to-left implication constructs the positive solver branch from any satisfying tuple. The left-to-right implication uses returned-some soundness. The statement quantifies the returned tuple existentially; it does not say that every satisfying tuple is the chosen tuple.

**Theorem 1.4 (None exactly means no satisfying bound tuple).**

$$\forall m \in Nat,\; \forall n \in Nat,\; \forall p \in \operatorname{BF}\left(m, n\right),\; \forall v \in \operatorname{NatTuple}\left(m\right),\; (\operatorname{solveBounded}\left(p, v\right) = none) \iff (\neg (\exists xs \in \operatorname{NatTuple}\left(n\right),\; \operatorname{Realize}\left(p, v, xs\right)))$$

*Proof.* Machine-checked in Lean as `D5/S0/Computability/NatPresburgerSolver.solve_bounded_none_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Vladimir Reshetnikov (2026). *ProveIt executable integer Presburger arithmetic*. URL: <https://github.com/VladimirReshetnikov/ProveIt/tree/ec9ab2ffd49f8861022d6f3d4c30205545a3386d/Logic/PresburgerArithmetic/Lean/PresburgerArithmetic>.

*Commentary.*

Option case analysis converts the existence-of-some contract into this exact failure contract. Fin n->Nat has its supplied Encodable instance even when n=0; its empty function is the unique zero-dimensional tuple.

**Theorem 1.5 (Returned coordinates split into the original free and bound parts).**

$$\forall m \in Nat,\; \forall n \in Nat,\; \forall p \in \operatorname{BF}\left(m, n\right),\; \forall w \in \operatorname{NatTuple}\left(m + n\right),\; (\operatorname{solveAll}\left(p\right) = \operatorname{some}\left(w\right)) \implies (\operatorname{Realize}\left(p, \operatorname{free}\left(w, m, n\right), \operatorname{bound}\left(w, m, n\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S0/Computability/NatPresburgerSolver.solve_all_sound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Vladimir Reshetnikov (2026). *ProveIt executable integer Presburger arithmetic*. URL: <https://github.com/VladimirReshetnikov/ProveIt/tree/ec9ab2ffd49f8861022d6f3d4c30205545a3386d/Logic/PresburgerArithmetic/Lean/PresburgerArithmetic>.

*Commentary.*

solveAll directly applies native BoundedFormula.relabel with Sum.inr, promoting the original free coordinates into the bound context before solveBounded. free(w,m,n)=w o Fin.castAdd n reads indices 0 through m-1. bound(w,m,n)=w o Fin.natAdd m reads indices m through m+n-1. Native realize_relabel proves the original coordinate split.

**Theorem 1.6 (Some exists exactly when the original formula has a full tuple).**

$$\forall m \in Nat,\; \forall n \in Nat,\; \forall p \in \operatorname{BF}\left(m, n\right),\; (\exists w \in \operatorname{NatTuple}\left(m + n\right),\; \operatorname{solveAll}\left(p\right) = \operatorname{some}\left(w\right)) \iff (\exists w \in \operatorname{NatTuple}\left(m + n\right),\; \operatorname{Realize}\left(p, \operatorname{free}\left(w, m, n\right), \operatorname{bound}\left(w, m, n\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S0/Computability/NatPresburgerSolver.solve_all_exists_some_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Vladimir Reshetnikov (2026). *ProveIt executable integer Presburger arithmetic*. URL: <https://github.com/VladimirReshetnikov/ProveIt/tree/ec9ab2ffd49f8861022d6f3d4c30205545a3386d/Logic/PresburgerArithmetic/Lean/PresburgerArithmetic>.

*Commentary.*

This is existence over the full Fin(m+n) tuple. Both quantifiers refer to the same coordinate convention. Multiple solutions are allowed and a successful solver chooses one of them.

**Theorem 1.7 (None exactly means no full native tuple).**

$$\forall m \in Nat,\; \forall n \in Nat,\; \forall p \in \operatorname{BF}\left(m, n\right),\; (\operatorname{solveAll}\left(p\right) = none) \iff (\neg (\exists w \in \operatorname{NatTuple}\left(m + n\right),\; \operatorname{Realize}\left(p, \operatorname{free}\left(w, m, n\right), \operatorname{bound}\left(w, m, n\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S0/Computability/NatPresburgerSolver.solve_all_none_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Vladimir Reshetnikov (2026). *ProveIt executable integer Presburger arithmetic*. URL: <https://github.com/VladimirReshetnikov/ProveIt/tree/ec9ab2ffd49f8861022d6f3d4c30205545a3386d/Logic/PresburgerArithmetic/Lean/PresburgerArithmetic>.

*Commentary.*

The fixed-parameter none contract transports through native realize_relabel. With m=0 only the bound part remains; with n=0 only the promoted free part remains; with m=n=0 both parts are the empty function.

## References

- Truth anchor: `D5/S0/Computability/NatPresburgerSolver.solve_all_exists_some_iff`
- Truth anchor: `D5/S0/Computability/NatPresburgerSolver.solve_all_none_iff`
- Truth anchor: `D5/S0/Computability/NatPresburgerSolver.solve_all_sound`
- Truth anchor: `D5/S0/Computability/NatPresburgerSolver.solve_bounded_exists_some_iff`
- Truth anchor: `D5/S0/Computability/NatPresburgerSolver.solve_bounded_none_iff`
- Truth anchor: `D5/S0/Computability/NatPresburgerSolver.solve_bounded_sound`
- Truth anchor: `D5/S0/Computability/NatPresburgerSolver.test_correct`
- Dependency: [D5/S0/Computability/NatPresburgerCompiler](NatPresburgerCompiler.md)
- Dependency: [D5/S0/Computability/PresburgerDecision](PresburgerDecision.md)
