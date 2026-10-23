# Native Class Root Simulation

## Abstract

Finite native dialogues compile to legal class-root experiments on truthful fixed actual representatives.

Sources are finite ordered Boolean trees and rho is the original substitution. For a finite prefix-free cut P and source T, let C=canonicalRow(P,T). ImageValues(C) contains every injective class valuation whose filled complete row is an actual image; OriginFiber(P,C) contains every finite origin with complete current row C. Types take the values some(true), some(false), and none for alpha, beta, and branch. Chart(C) is the set of admissible assignments. Dialogue is the existing finite four-reply native reader tree with complete row outputs. The notation replies(t) means the function a ↦ readout(a,t); valuations and origins are coerced to their underlying values in formulas.

**Definition 1.1 (Legal Three-Reply Experiment Trees).**

$$\forall C: LiteralRow, (\forall O: Type, ((\operatorname{stop}\left(\right): O \to \operatorname{RootTree}\left(C, O\right)) \land (\operatorname{ask}\left(\right): \operatorname{Classes}\left(C\right) \to \operatorname{RootTree}\left(C, O\right) \to \operatorname{RootTree}\left(C, O\right) \to \operatorname{RootTree}\left(C, O\right) \to \operatorname{RootTree}\left(C, O\right))))$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeClassRootSimulation.RootTree` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A root tree has a complete output at a stop and exactly three continuations at a query of an appearing class. There is no absent root reply and no query constructor when the class set is empty.

**Definition 1.2 (Stationary Native Execution).**

$$\forall O: Type, (\forall f: Address \to Reply, ((\forall o: O, (\operatorname{nativeRun}\left(f, \operatorname{stop}\left(o\right)\right) = (o, 0))) \land (\forall a: Address, (\forall A: \operatorname{Dialogue}\left(O\right), (\forall B: \operatorname{Dialogue}\left(O\right), (\forall E: \operatorname{Dialogue}\left(O\right), (\forall D: \operatorname{Dialogue}\left(O\right), (\operatorname{nativeRun}\left(f, \operatorname{read}\left(a, A, B, E, D\right)\right) = \operatorname{increment}\left(\operatorname{nativeRun}\left(f, \operatorname{choose}\left(\operatorname{f}\left(a\right), A, B, E, D\right)\right)\right)))))))))$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeClassRootSimulation.nativeRun` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Execution follows the actual alpha, beta, branch, or absent continuation. The pair records the terminal output and invocation count; increment(o,n)=(o,n+1). The register reply function stays fixed; every visited read counts once, including repeats and absences.

**Definition 1.3 (Joint Root Execution).**

$$\forall C: LiteralRow, (\forall O: Type, (\forall theta: \operatorname{Classes}\left(C\right) \to \operatorname{Option}\left(Bool\right), ((\forall o: O, (\operatorname{rootRun}\left(theta, \operatorname{stop}\left(o\right)\right) = (o, 0))) \land (\forall d: \operatorname{Classes}\left(C\right), (\forall A: \operatorname{RootTree}\left(C, O\right), (\forall B: \operatorname{RootTree}\left(C, O\right), (\forall E: \operatorname{RootTree}\left(C, O\right), (\operatorname{rootRun}\left(theta, \operatorname{ask}\left(d, A, B, E\right)\right) = \operatorname{increment}\left(\operatorname{rootRun}\left(theta, \operatorname{chooseRoot}\left(\operatorname{theta}\left(d\right), A, B, E\right)\right)\right)))))))))$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeClassRootSimulation.rootRun` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Execution follows the same unchanged joint assignment at every vertex. The function chooseRoot selects the alpha, beta, or branch child for some(true), some(false), or none. Every visited class query counts once. Early stops use no invocation.

**Definition 1.4 (Native Path Budget).**

$$\forall O: Type, ((\forall o: O, (\operatorname{nativeDepth}\left(\operatorname{stop}\left(o\right)\right) = 0)) \land (\forall a: Address, (\forall A: \operatorname{Dialogue}\left(O\right), (\forall B: \operatorname{Dialogue}\left(O\right), (\forall E: \operatorname{Dialogue}\left(O\right), (\forall D: \operatorname{Dialogue}\left(O\right), (\operatorname{nativeDepth}\left(\operatorname{read}\left(a, A, B, E, D\right)\right) = \operatorname{max}\left(\operatorname{nativeDepth}\left(A\right), \operatorname{nativeDepth}\left(B\right), \operatorname{nativeDepth}\left(E\right), \operatorname{nativeDepth}\left(D\right)\right) + 1)))))))$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeClassRootSimulation.nativeDepth` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The depth is zero at a stop and one plus the maximum depth of the four children at a read.

**Definition 1.5 (Experiment Path Budget).**

$$\forall C: LiteralRow, (\forall O: Type, ((\forall o: O, (\operatorname{rootDepth}\left(\operatorname{stop}\left(o\right)\right) = 0)) \land (\forall d: \operatorname{Classes}\left(C\right), (\forall A: \operatorname{RootTree}\left(C, O\right), (\forall B: \operatorname{RootTree}\left(C, O\right), (\forall E: \operatorname{RootTree}\left(C, O\right), (\operatorname{rootDepth}\left(\operatorname{ask}\left(d, A, B, E\right)\right) = \operatorname{max}\left(\operatorname{rootDepth}\left(A\right), \operatorname{rootDepth}\left(B\right), \operatorname{rootDepth}\left(E\right)\right) + 1)))))))$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeClassRootSimulation.rootDepth` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The depth is zero at a stop and one plus the maximum depth of the three children at a class experiment.

**Definition 1.6 (Finite Native Word Bound).**

$$\forall O: Type, ((\forall o: O, (\operatorname{wordBound}\left(\operatorname{stop}\left(o\right)\right) = 0)) \land (\forall a: Address, (\forall A: \operatorname{Dialogue}\left(O\right), (\forall B: \operatorname{Dialogue}\left(O\right), (\forall E: \operatorname{Dialogue}\left(O\right), (\forall D: \operatorname{Dialogue}\left(O\right), (\operatorname{wordBound}\left(\operatorname{read}\left(a, A, B, E, D\right)\right) = \operatorname{max}\left(\operatorname{length}\left(a\right), \operatorname{wordBound}\left(A\right), \operatorname{wordBound}\left(B\right), \operatorname{wordBound}\left(E\right), \operatorname{wordBound}\left(D\right)\right))))))))$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeClassRootSimulation.wordBound` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The maximum ranges over all installed query words, including unrealized edges. A stop contributes zero. This is a bound on this one finite comparator, not on source size.

**Definition 1.7 (Exterior Navigation and Experiment Compilation).**

$$\forall C: LiteralRow, (\forall O: Type, ((\forall o: O, (\operatorname{compileRoot}\left(C, \operatorname{stop}\left(o\right)\right) = \operatorname{stop}\left(o\right))) \land (\forall a: Address, (\forall A: \operatorname{Dialogue}\left(O\right), (\forall B: \operatorname{Dialogue}\left(O\right), (\forall E: \operatorname{Dialogue}\left(O\right), (\forall D: \operatorname{Dialogue}\left(O\right), ((\forall y: Reply, ((\operatorname{firstClass}\left(C, a\right) = \operatorname{inl}\left(y\right)) \implies (\operatorname{compileRoot}\left(C, \operatorname{read}\left(a, A, B, E, D\right)\right) = \operatorname{compileRoot}\left(C, \operatorname{choose}\left(y, A, B, E, D\right)\right)))) \land (\forall d: \operatorname{Classes}\left(C\right), (\forall b: Bool, ((\operatorname{firstClass}\left(C, a\right) = \operatorname{inr}\left((d, b)\right)) \implies (\operatorname{compileRoot}\left(C, \operatorname{read}\left(a, A, B, E, D\right)\right) = \operatorname{ask}\left(d, \operatorname{compileRoot}\left(C, \operatorname{choose}\left(\operatorname{classReply}\left(b, \operatorname{some}\left(true\right)\right), A, B, E, D\right)\right), \operatorname{compileRoot}\left(C, \operatorname{choose}\left(\operatorname{classReply}\left(b, \operatorname{some}\left(false\right)\right), A, B, E, D\right)\right), \operatorname{compileRoot}\left(C, \operatorname{choose}\left(\operatorname{classReply}\left(b, none\right), A, B, E, D\right)\right)\right)))))))))))))$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeClassRootSimulation.compileRoot` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The exterior is traversed to its first class hole, if any. A fixed exterior reply selects one compiled continuation without a class experiment. A hole yields one legal appearing class d and a Boolean b recording whether the remaining suffix is nonempty. When b is false, the class constructor selects the matching native continuation. When b is true, either leaf selects absent and a branch selects branch. Repeated questions remain distinct charged vertices. The symbols firstClass, classReply and choose denote these structural operations; choose(y,A,B,E,D) selects the four-reply child.

**Definition 1.8 (Exactly Attained Joint Types).**

$$\forall C: LiteralRow, (\operatorname{Chart}\left(C\right) = \{theta: \operatorname{Classes}\left(C\right) \to \operatorname{Option}\left(Bool\right) \Vert \operatorname{Admissible}\left(C, theta\right)\})$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeClassRootSimulation.Chart` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Admissibility uses the complete exterior image grammar and the separate multiplicity bounds on the two literal leaf classes. The actual class-root image theorem identifies this chart with exactly the attained types.

**Theorem 1.9 (Truthful Joint Simulation on Actual Origins).**

$$\forall P: CutSet, ((\operatorname{CutPrefixFree}\left(P\right)) \implies (\forall T: Source, (\forall S: Type, ([\operatorname{Finite}\left(S\right)] \forall sigma: \operatorname{ImageValues}\left(\operatorname{canonicalRow}\left(P, T\right)\right) \to S, (\forall E: S \to \operatorname{Dialogue}\left(LiteralRow\right), (\forall q: Nat, (((\forall s: S, (\operatorname{nativeDepth}\left(\operatorname{E}\left(s\right)\right) \leq q)) \land (\forall w: \operatorname{ImageValues}\left(\operatorname{canonicalRow}\left(P, T\right)\right), (\forall z: \operatorname{OriginFiber}\left(P, \operatorname{canonicalRow}\left(P, T\right)\right), ((\operatorname{rho}\left(z\right) = \operatorname{evaluateRow}\left(\operatorname{extend}\left(\operatorname{canonicalRow}\left(P, T\right), w\right), \operatorname{canonicalRow}\left(P, T\right)\right)) \implies (\operatorname{fst}\left(\operatorname{nativeRun}\left(\operatorname{replies}\left(\operatorname{rho}\left(z\right)\right), \operatorname{E}\left(\operatorname{sigma}\left(w\right)\right)\right)\right) = \operatorname{canonicalRow}\left(P, z\right)))))) \implies (\exists v: \operatorname{Chart}\left(\operatorname{canonicalRow}\left(P, T\right)\right) \to \operatorname{ImageValues}\left(\operatorname{canonicalRow}\left(P, T\right)\right), (\exists u: \operatorname{Chart}\left(\operatorname{canonicalRow}\left(P, T\right)\right) \to \operatorname{OriginFiber}\left(P, \operatorname{canonicalRow}\left(P, T\right)\right), (\exists c: \operatorname{Chart}\left(\operatorname{canonicalRow}\left(P, T\right)\right) \to S, (\forall theta: \operatorname{Chart}\left(\operatorname{canonicalRow}\left(P, T\right)\right), ((\operatorname{rho}\left(\operatorname{u}\left(theta\right)\right) = \operatorname{evaluateRow}\left(\operatorname{extend}\left(\operatorname{canonicalRow}\left(P, T\right), \operatorname{v}\left(theta\right)\right), \operatorname{canonicalRow}\left(P, T\right)\right)) \land (\operatorname{types}\left(\operatorname{canonicalRow}\left(P, T\right), \operatorname{v}\left(theta\right)\right) = theta) \land (\operatorname{c}\left(theta\right) = \operatorname{sigma}\left(\operatorname{v}\left(theta\right)\right)) \land (\operatorname{fst}\left(\operatorname{rootRun}\left(theta, \operatorname{compileRoot}\left(\operatorname{canonicalRow}\left(P, T\right), \operatorname{E}\left(\operatorname{c}\left(theta\right)\right)\right)\right)\right) = \operatorname{canonicalRow}\left(P, \operatorname{u}\left(theta\right)\right)) \land (\operatorname{snd}\left(\operatorname{rootRun}\left(theta, \operatorname{compileRoot}\left(\operatorname{canonicalRow}\left(P, T\right), \operatorname{E}\left(\operatorname{c}\left(theta\right)\right)\right)\right)\right) \leq \operatorname{snd}\left(\operatorname{nativeRun}\left(\operatorname{replies}\left(\operatorname{rho}\left(\operatorname{u}\left(theta\right)\right)\right), \operatorname{E}\left(\operatorname{sigma}\left(\operatorname{v}\left(theta\right)\right)\right)\right)\right)) \land (\operatorname{rootDepth}\left(\operatorname{compileRoot}\left(\operatorname{canonicalRow}\left(P, T\right), \operatorname{E}\left(\operatorname{c}\left(theta\right)\right)\right)\right) \leq q)))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeClassRootSimulation.truthful_joint_root_simulation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix an arbitrary finite supplement alphabet S, a supplement sigma depending on the complete acquired valuation, and one finite native dialogue E(s) per value. Assume every installed dialogue has depth at most q and gives the complete predecessor row on every matching actual valuation and origin. There is one fixed actual origin u(theta), one injective image valuation v(theta), and its truthful exported value c(theta)=sigma(v(theta)) for every admissible joint type. The compiled tree returns that origin's entire canonical predecessor row, uses no more calls than its native run, and has depth at most q. To obtain a common finite word bound, take the maximum over all installed dialogues. Apply actual image padding at that bound, then induct through each dialogue using structural exterior navigation. Each vertex is constant or depends on exactly one appearing class, so zero or one class experiment reproduces its native reply on that same padded image. The supplement alphabet is retained unchanged. No assertion says that sigma is constant on all sources of one type. The result covers arbitrary addresses, repeated calls, blocking absences, zero queries, root cuts, empty cuts and zero classes. It is the finite-dialogue simulation needed for the necessity direction of the joint feasibility correspondence. The general source-total reader unrolling, full predecessor factorization through types, reverse native implementation and complete feasibility equivalence are separate obligations. No source reconstruction chart, physical resource equivalence, acquisition permission or controller-state bound follows.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeClassRootSimulation.Chart`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeClassRootSimulation.RootTree`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeClassRootSimulation.compileRoot`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeClassRootSimulation.nativeDepth`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeClassRootSimulation.nativeRun`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeClassRootSimulation.rootDepth`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeClassRootSimulation.rootRun`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeClassRootSimulation.truthful_joint_root_simulation`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeClassRootSimulation.wordBound`
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/NativeClassRootImage](NativeClassRootImage.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/NativeClassRootPadding](NativeClassRootPadding.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/NativePassiveServiceRealization](NativePassiveServiceRealization.md)
