# Controlled behavior and ordered pairwise refinement

## Abstract

Complete controlled behavior, exact quotients, and an ordered pairwise algorithm with its primitive trace.

Let X be nonempty, A any alphabet, F : A to X to X a total update, and o : X to O an arbitrary observation. For a finite word w, runWord applies its first letter first. Put B(x)(w)=o(runWord(F,w,x)), and let R be equality of B. The operator Phi sends a relation S to the intersection of equality of current observations with all inverse images of S under paired one-step updates. No finiteness of X, A, or O is needed here.

Equality of B is a fixed point of Phi: the empty word gives current observation equality and prefixing a letter gives closure under that update. If S is contained in Phi(S), induction on word length shows that S is contained in equality of B. Thus R is the greatest fixed point and the greatest equivalence relation within the observation kernel preserved by every update. These are the existing controlledLimitRelation and controlledRefinementOperator results in ControlledFiniteStability.

The quotient Q=X/R carries the unique maps Fbar(a)([x])=[F(a,x)] and obar([x])=o(x) that commute with the projection pi. For any exact representation r : X to S, its maps G(a) and out are defined only on the actual image range(r), and obey r(F(a,x))=G(a)(r(x)) and o(x)=out(r(x)). Iteration shows that equal r-values have equal behaviors. Consequently p(r(x))=[x] is well defined, surjective, unique, and satisfies pi=p composed with r, p composed with G(a)=Fbar(a) composed with p, and obar composed with p=out. ControlledCompletionDescent supplies the descended maps and DynamicClosureMinimality supplies the behavior factor; completionRangeEquiv identifies the behavior image with Q.

The surjection p gives the cardinal inequality |Q| <= |range(r)| even for infinite carriers. If range(r) injects into b-bit strings, it is finite and Nat.card(Q) <= 2^b. The comparison concerns the actual representation states; it places no condition on unused elements of S.

Now X and A are finite, with n=|X|>0 and k=|A|, and c0 is the number of classes of the observation kernel. Let R(h) compare observations after every word of length at most h. Then R(0) is the observation kernel and R(h+1)=Phi(R(h)). Apply controlled_finite_stability to the surjective observation into range(o); equality of subtypes transports the relations back to O without assuming O finite. If A is empty every word is empty, so all R(h) equal R(0) and h=0 suffices. Otherwise finite class growth yields h<=n-c0 with R(h)=R(h+1)=R. Unequal behaviors therefore have a distinguishing word of length at most n-c0.

The execution input supplies states Fin n, actions Fin k, the transition table F and the observation table o, together with an equality decision on O. label(f,x) is the least input index with f(y)=f(x). scanTrace visits finRange n in order, starting best=x and replacing best by min(best,y) exactly when equality succeeds. Its invariant preserves the observed value, bounds best by its initial value and every matching visited index, and counts every emitted operation. Thus its returned index is label(f,x), including singleton and zero-action cases. Definitions also admit n=0; the termination theorem retains the original nonempty-state premise.

Initial scans compare observations. A refinement signature contains the observation and the previous class label of every successor. Each pair comparison visits all action coordinates, records transition lookups, label reads, equality tests and their flags, and then updates the running minimum. After all new labels are stored, a second pair scan compares the old and new equality matrices. No recursively expanded word history is compared in this operation model.

**Theorem 1.1 (Exact quotient, distinguishing words, and a uniform cost bound).**

$$\forall n:\mathbb{N},(\forall k:\mathbb{N},((0<n)\implies(\forall O:Type,(\forall d:\operatorname{DecidableEq}(O),(\forall F:(\operatorname{Fin}(k))\to ((\operatorname{Fin}(n))\to (\operatorname{Fin}(n))),(\forall o:(\operatorname{Fin}(n))\to (O),(\exists h:\mathbb{N},(\exists cost:\mathbb{N},(\exists c:(\operatorname{Fin}(n))\to (\operatorname{Fin}(n)),(((h)\le ((n)-(\operatorname{initialClasses}(o))))\land(\operatorname{Terminates}(n,k,O,d,F,o,h,cost,c))\land(\forall x:\operatorname{Fin}(n),(\forall y:\operatorname{Fin}(n),(((c(x))=(c(y)))\iff((\operatorname{controlledBehavior}(F,o,x))=(\operatorname{controlledBehavior}(F,o,y))))))\land(\forall x:\operatorname{Fin}(n),(\forall y:\operatorname{Fin}(n),(((\operatorname{controlledBehavior}(F,o,x))\neq (\operatorname{controlledBehavior}(F,o,y)))\implies(\exists w:\operatorname{List}(\operatorname{Fin}(k)),(((\operatorname{length}(w))\le ((n)-(\operatorname{initialClasses}(o))))\land((o(\operatorname{runWord}(F,w,x)))\neq (o(\operatorname{runWord}(F,w,y)))))))))\land((cost)=((4)\times ((n)\times (n))+n+(h+1)\times (((n)\times (n))\times ((7)\times (k)+8)+n)))\land((cost)\le ((((14)\times (k+1))\times ((n)\times (n)))\times ((n)-(\operatorname{initialClasses}(o))+1)))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/PairwiseSignatureRefinement.pairwise_signature_termination` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every n>0, k>=0, arbitrary O with an equality decision, and supplied F and o, there exist h, cost and a label table c with h<=n-c0. In the displayed statement, d is the supplied equality decision on O, and Terminates(n,k,O,d,F,o,h,cost,c) writes all arguments of the existing predicate explicitly. Natural-number subtraction is truncated at zero. Terminates asserts c=labelsAt(h), equality of the consecutive actual tables, cost equal to the complete emitted trace length, and correctness of every initial and refinement scan through h. Equality of final labels is exactly equality of complete behaviors, and unequal behaviors have a distinguishing word of length at most n-c0.

The initial trace has 4*n*n+n operations. Each refinement and stability round has n*n*(7*k+8)+n operations. Including h strict rounds and the last stability comparison gives cost=4*n*n+n+(h+1)*(n*n*(7*k+8)+n), bounded by 14*(k+1)*n*n*(n-c0+1). The constant is independent of the carriers, input tables and equality decision. This is a count in the stated abstract input model; evaluating arbitrary observation equality and Lean VM reduction have no claimed runtime bound.

The relation represented by labelsAt follows the existing controlled-word recursion. A stable relation gives exactly equal least-index label tables. The scan invariant supplies those tables and their trace lengths. Substitution of h<=n-c0 yields the uniform bound; it does not replace the scan by an edge count. utilityInput has three states: 0 and 1 initially share a label, while the sole action sends 1 to the differently observed state 2. The first refinement separates them and the following round is stable, with total cost 315.

For supplied equivalences eX : Fin n equiv X and eA : Fin k equiv A, set E(a,x)=eX.inverse(F(eA(a),eX(x))) and r(x)=rangeFactorization(o)(eX(x)). The equality decision need only act on range(o). Induction gives eX(runWord(E,w,x))=runWord(F,map(eA,w),eX(x)); mapping by the inverse alphabet equivalence gives the converse correspondence. Hence every bounded and complete behavior relation agrees through eX, initialClasses(r)=initialClasses(o), and the final label quotient is equivalent to the original behavior quotient. Word lengths, the exact trace count and the uniform bound are preserved. All output and representation maps remain on their actual ranges.

The finite argument reuses ControlledFiniteStability, ControlledRelationRecursion, ControlledBehaviorUniversality and ControlledCompletionDescent. Mathlib supplies quotient-kernel/range equivalence, cardinal transport and finite-set minima. The running-minimum invariant and its connection to the emitted pairwise trace provide the algorithmic part of this construction.

## References

- Truth anchor: `D5/S3/ObserverMemory/Algorithms/PairwiseSignatureRefinement.pairwise_signature_termination`
- Dependency: [D5/S3/ObserverMemory/Algorithms/ControlledFiniteStability](ControlledFiniteStability.md)
