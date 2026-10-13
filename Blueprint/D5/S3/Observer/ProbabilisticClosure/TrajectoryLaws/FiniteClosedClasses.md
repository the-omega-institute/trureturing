# Actual closed classes and transient escape

## Abstract

FiniteClosedClasses

RowStochastic(P) means a finite real matrix with nonnegative entries and every row sum equal to one. Reach(P,x,y) is Nonempty of the actual Mathlib quiver path type from x to y, whose edges are PLift(0<P(x,y)); empty paths are included. Terminal(P,x) means every state reachable from x reaches x back. communicatingClass(P,x) contains precisely the states mutually reachable with x. ClosedClass(P) is the subtype of finite state sets equal to communicatingClass(P,x) for some terminal x, so repeated representatives do not create duplicate classes.

Recurrent(P,x) means membership in one of these actual classes. Transient(P) is exactly the subtype of states outside this union. restriction(P,C) and transientMatrix(P) are the actual submatrices obtained by Subtype.val in both coordinates. The class index type and transient state type are finite; no supplied partition, terminal-class existence, irreducibility, absorption or escape certificate occurs in the theorem's premises.

**Theorem 1.1 (Structural interface derived from the transition matrix).**

$$\forall X:Type, ([\operatorname{Fintype}(X)][\operatorname{DecidableEq}(X)]\forall P:\operatorname{Matrix}(X, X, \mathbb{R}), (\operatorname{RowStochastic}(P)\implies \operatorname{Structure}(P)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FiniteClosedClasses.actual_structure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Structure(P) is the exact conjunction of the following fields. Each actual closed class C is nonempty, is closed under every actual support path (hence every positive transition), and any two states in C communicate. Its actual restricted matrix is row stochastic and Matrix.IsIrreducible, including positive-length return paths. For every n and x,y in C, the restricted power entry equals the ambient P^n entry; its positivity is equivalent to an ambient support path of exactly length n. All ambient power entries from C to a state outside C are zero. Each C is exactly one Mathlib StronglyConnectedComponent, with a representative in C.

Distinct classes are disjoint; each class cardinality is positive and at most card(X). The number of actual closed classes is at most card(X). The sum of the class state cardinalities plus card(Transient(P)) is exactly card(X). A state is recurrent if and only if it is terminal. Every state reaches a member of an actual closed class. Nonempty(X) entails Nonempty(ClosedClass(P)); no independent nonempty-class premise is supplied.

For every n and transient x,y, the killed Q^n entry equals the ambient P^n entry. Its positivity is equivalent to an ambient support path of exactly length n: a path cannot leave the transient set and return from a closed class. Q is substochastic. There exist h:Nat and c:Real with 0<h, c<1 and every Q^h row sum at most c. All Q^n entries tend to zero, and det(I-Q) is nonzero. These last two conclusions directly consume the original SubstochasticEscape supplier, without duplicating its decay or kernel proof.

If X is empty, the actual class type is empty. If the transient type is empty, Q is the empty zero matrix, det(I-Q)=1, and the escape bound holds explicitly with h=1 and c=0. No normalized stationary probability row is asserted on empty X.

The existence construction minimizes the cardinality of a reachable-state set among states reachable from the chosen start. Reachability gives inclusion of successor reachable sets; minimality forces equality and return reachability, producing a terminal class. For each transient start, a positive path into a terminal class gives positive ambient recurrent mass at a positive time. Exact killed-power restriction and the ambient stochastic row sum give a strict transient deficit. The maximum of finitely many positive escape times and then the maximum of their strictly deficient row sums produce the uniform block. No minimum positive transition is an additional hypothesis.

This interface supplies the actual structural obligations of PH38.2. Genuine gcd periods, cyclic labels, full residue limits, first-entry phase analysis and the single arithmetic denominator with its original bound remain separate obligations. The escape witnesses can depend on P; this result supplies no denominator estimate in terms of them. Phase indexing in the later proof is mathematical analysis and establishes no runtime clock or resource waiver.

## References

- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FiniteClosedClasses.actual_structure`
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/SubstochasticEscape](SubstochasticEscape.md)
