# Finite native constraints for literal navigation

## Abstract

NativeLiteralPathConstraints

**Definition 1.1 (Native labels and tree names).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeLiteralPathConstraints.Atom`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeLiteralPathConstraints.Atom` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A term leaf is a native alpha or beta label, an original-source epoch coordinate, or an auxiliary tree name. Term is the free ordered binary tree on these atoms. The function label selects a native leaf, original selects an epoch coordinate, and auxiliary selects a bound tree name.

**Definition 1.2 (Finite ordered constructor terms).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeLiteralPathConstraints.Term`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeLiteralPathConstraints.Term` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Terms contain only ordered pairs and the three kinds of leaf names. All occurrences of original refer to the same tree u. The natural function e assigns the substitution exponent to each coordinate; coordinates have no common upper bound.

**Definition 1.3 (Native labelled leaves).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeLiteralPathConstraints.label`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeLiteralPathConstraints.label` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

True is alpha and false is beta. Labels are literal finite constructor terms.

**Definition 1.4 (One shared original source).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeLiteralPathConstraints.original`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeLiteralPathConstraints.original` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An original coordinate i denotes the iterate of the same u at exponent e(i). It does not denote a separately chosen source.

**Definition 1.5 (Auxiliary tree names).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeLiteralPathConstraints.auxiliary`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeLiteralPathConstraints.auxiliary` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Auxiliary indices refer to the current existential tree environment.

**Definition 1.6 (Term interpretation).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeLiteralPathConstraints.value`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeLiteralPathConstraints.value` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

value u e x interprets labels and ordered pairs literally, original i as substitution iterated e(i) times on u, and auxiliary i as x(i). No source replacement occurs in this interpretation.

**Definition 1.7 (Opening an existential tree binder).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeLiteralPathConstraints.push`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeLiteralPathConstraints.push` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A new bound tree has index zero. Every previous auxiliary tree moves to its successor index.

**Definition 1.8 (Preserving names under a tree binder).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeLiteralPathConstraints.lift`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeLiteralPathConstraints.lift` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

lift increments auxiliary indices, preserves original-source coordinates and labels, and commutes with ordered pairs.

**Definition 1.9 (Finite native formula grammar).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeLiteralPathConstraints.Formula`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeLiteralPathConstraints.Formula` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The grammar has falsehood, constructor equality, binary conjunction, binary disjunction and existential tree quantification. It contains no Read predicate, variable address, source oracle or program predicate. Its satisfaction relation Holds is Formula.Holds with the formula argument last. Existential tree quantification ranges over actual finite native trees, using push for its environment; the epoch environment is retained through every tree quantifier.

**Definition 1.10 (Actual ordered child constraints).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeLiteralPathConstraints.pairStep`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeLiteralPathConstraints.pairStep` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Descent binds the two ordered children and equates their pair to the entire current term. One child is selected by the next literal address bit, while the other remains an existential sibling.

**Definition 1.11 (Four-reply literal navigation).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeLiteralPathConstraints.compile`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeLiteralPathConstraints.compile` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At the root, alpha and beta require their labelled leaves; branch requires two children; absent is false. At a nonempty word, a present reply requires pair descent. Absence permits either labelled leaf at the current strict prefix or recursive descent through an actual pair. Thus an absent endpoint is never assigned a default tree.

**Theorem 1.12 (Exact native navigation constraints).**

$$\forall u: Source, (\forall e: Nat \to Nat, (\forall x: Nat \to Source, (\forall p: Address, (\forall y: Reply, (\forall V: Term, ((\operatorname{Holds}\left(u, e, x, \operatorname{compile}\left(p, y, V\right)\right)) \iff (\operatorname{readout}\left(p, \operatorname{value}\left(u, e, x, V\right)\right) = y)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeLiteralPathConstraints.compile_exact` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original finite tree, epoch environment, auxiliary environment, literal finite address, reply and term, satisfaction of the compiled formula is equivalent to the actual four-valued readout of that interpreted term. This includes the empty address and all four replies.

Induction follows the literal address. A pair equation fixes both actual children and preserves the full current tree; the recursive formula follows the selected child. Every absence alternative ends at a labelled leaf on a strict prefix. The auxiliary trees therefore describe subtrees of the same actual interpreted tree in both directions.

The construction is finite and structurally recursive. The statement is an extensional semantic equivalence; it does not assert a partial-recursive encoding theorem for the whole formula generator or an enumeration theorem for observer programs.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeLiteralPathConstraints.Atom`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeLiteralPathConstraints.Formula`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeLiteralPathConstraints.Term`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeLiteralPathConstraints.auxiliary`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeLiteralPathConstraints.compile`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeLiteralPathConstraints.compile_exact`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeLiteralPathConstraints.label`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeLiteralPathConstraints.lift`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeLiteralPathConstraints.original`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeLiteralPathConstraints.pairStep`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeLiteralPathConstraints.push`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeLiteralPathConstraints.value`
- Dependency: [D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition](../ActualTreeReadoutAcquisition.md)
