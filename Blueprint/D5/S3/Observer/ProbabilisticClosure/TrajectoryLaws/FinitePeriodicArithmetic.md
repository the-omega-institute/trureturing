# One denominator for all original-matrix periodic limits

## Abstract

FinitePeriodicArithmetic

Let X be a finite state type, let P be a real row-stochastic matrix, and let N and L be natural numbers with card(X)<=N and L>0. Assume each original one-step entry L*P(x,y) is an integer. This includes every real embedding of a rational stochastic matrix with the given clearing integer L; L need not be minimal. There exist actual AllStateLimits A and one positive integer D with D<=(2L)^(N^3)*((N+1)L)^(N^2). The same D clears every periodicEntry of every AllStateLimits representation B, for every natural residue i and every start and target state. For every positive common multiple d of B's actual closed-class periods, these original entries P^(d*t+i)(x,y) converge to an integer divided by D, equal to B's retained periodicEntry. No restriction i<d is imposed.

Write E(x,y)=L*P(x,y), an integer matrix. For each actual closed class C choose the base r and genuine period p_C of A.periods(C). Form the integer stationary matrix S_C by replacing row r of L*(I-P_C^transpose) by an all-ones row. Its right-hand side for the actual stationary row pi_C is the coordinate vector at r. To prove nonsingularity, a kernel vector has total zero and satisfies all the stationary equations except possibly row r. The sum of the stationary residuals is zero because P_C is row-stochastic, so the missing equation also holds. For a signed stationary row v of total zero, t=1+sum |v(x)|/pi_C(x)>0 makes pi_C+v/t a nonnegative normalized stationary row. Strict positivity of the retained pi_C and its probability-row uniqueness imply v=0. No signed uniqueness premise is assumed.

For transient phase masses use the finite index set T times ZMod(p_C). Its substochastic matrix Q_C has entry Q(x,v) from (x,j) to (v,j+1), and zero at the other phases, where Q is the original killed restriction. The n-th power has Q^n(x,v) at phase j+n and zero elsewhere; hence its row sums equal the original transient survival row sums. Actual transient escape proves I-Q_C nonsingular. These phases are mathematical indices in a finite linear system and do not install a runtime clock.

The actual EntranceLaw series gives psi_C(x,j)=sum_z [phi_C(z)-1=j]*P(x,z)+sum_v P(x,v)*psi_C(v,j+1). It follows by separating entrance time zero from the summable tail, using the exact entrance recurrence. The physical entrance time remains n+1. Therefore the integer matrix M_C=L*I-L*Q_C sends the vector of all actual psi_C(x,j) to the integer vector sum_z [phi_C(z)-1=j]*E(x,z). One determinant clears every transient state and every phase at once.

Let a_C=abs(det(M_C)) and b_C=abs(det(S_C)), interpreted as positive natural integers. Pinned adjugate multiplication shows that an integer matrix times a real solution equaling an integer vector has det(M) times that solution integral. This applies to both actual systems. The repository Gram Hadamard inequality is applied after finite reindexing over the real numbers: det(M)^2 is bounded by the product of row squared norms, each bounded by the square of its absolute row sum. Thus abs(det(M)) is bounded by the product row bound. The transient phase matrix has absolute row sums at most 2L. The stationary matrix has absolute row sums at most (N+1)L. Consequently a_C<=(2L)^(|T|*p_C)<=(2L)^(N^2), and b_C<=((N+1)L)^N.

Take D=product_C (a_C*b_C). Each local product divides D. At a same-class recurrent start the actual limit is p_C*pi_C(y) on the compatible phase and zero otherwise. At a transient start it is p_C*pi_C(y)*psi_C(x,phi_C(y)-i), with the original first-entry formula and its physical offset. Both factors are cleared by the corresponding determinants. Transient target columns and entries between distinct recurrent classes are zero. This proves simultaneous integrality for all i without choosing a stride d or counting its residues.

There are at most N actual classes, each genuine p_C is at most its class cardinality, and both class and transient cardinalities are at most N. Multiplying the per-class estimates gives D<=(2L)^(N^3)*((N+1)L)^(N^2). In an empty transient block each M_C is a zero-dimensional matrix with determinant one. In an empty ambient type the actual class family is empty and D is the empty product one; this also covers N=0 and absence of classes. All claims quantified over empty state sets remain vacuous.

The construction first uses actual_all_state_limits to obtain A from P itself. To clear every other AllStateLimits representation B with the same D, choose a positive product of the actual periods only for comparing convergent subsequences. Period independence makes it a common multiple for A and B, and uniqueness of limits identifies their periodicEntry values at every natural i. This comparison stride contributes no denominator factor. The arithmetic construction uses only original one-step entries, actual stationary rows and actual first-entry phases; it is independent of d, the number of residues and the smallest positive transition.

**Theorem 1.1 (One positive bounded denominator for all actual limits).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FinitePeriodicArithmetic.actual_common_denominator`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FinitePeriodicArithmetic.actual_common_denominator` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite real row-stochastic P, every N bounding the ambient cardinality, and every positive natural L making L*P(x,y) an integer for all states, there exist A:AllStateLimits(P) and D>0 satisfying the exact PH38.2 bound and D=1 when X is empty. Every AllStateLimits B, every natural i and all x,y have D*periodicEntry_B(i,x,y) integral. For every such B and every d>0 divisible by all its genuine class periods, every i,x,y has an integer z with periodicEntry_B(i,x,y)=z/D and P^(d*t+i)(x,y) tending to z/D. The same existential D precedes every B,d,i,x,y quantifier.

## References

- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FinitePeriodicArithmetic.actual_common_denominator`
- Dependency: [D5/S3/Arith/AbsoluteValues/Heights/Hadamard](../../../Arith/AbsoluteValues/Heights/Hadamard.md)
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FiniteAllStateLimits](FiniteAllStateLimits.md)
