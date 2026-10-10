# Actual Occupied-Diagonal Comparison

## Abstract

The actual critical shape series determines kernel mass and supports strict occupied-diagonal comparison.

**Theorem 1.1 (Global comparison with actual occupied-shape mass).**

$$\operatorname{Summable}\left(t\right)\land\operatorname{sum}\left(t\right)=b\land\operatorname{sum}\left(k\right)=\frac{1}{2}\land(\forall e\in Z, \operatorname{Summable}\left(\operatorname{m}\left(e\right)\right))\land(\forall e\in Z, 0\le\operatorname{C}\left(e\right)\le c)\land(\forall n\in N, (\forall e\in Z, \operatorname{D}\left(0, n, e\right)=\operatorname{sum}\left(i, \operatorname{cuts}\left(n\right), \operatorname{J}\left(0, i, e\right)(\operatorname{U}\left(n-i\right)-\operatorname{A}\left(n-i, e\right))+\operatorname{I}\left(0, i\right)\operatorname{A}\left(n-i, e\right)\right)))\land(\forall n\in N, (\forall e\in Z, \operatorname{D}\left(1, n, e\right)=\operatorname{sum}\left(i, \operatorname{cuts}\left(n\right), \operatorname{J}\left(1, i, e+n-i\right)\operatorname{U}\left(n-i\right)+\operatorname{I}\left(1, i\right)\operatorname{A}\left(n-i, e-i\right)\right)))\land(\forall s\in Signs, (\forall n\in N, (\forall e\in Z, \operatorname{A}\left(n, e\right)=\operatorname{J}\left(s, n, e\right)+\operatorname{D}\left(s, n, e\right))))\land(\forall s\in Signs, (\forall n\in N, (\forall e\in Z, 2\le n\implies\operatorname{D}\left(s, n, e\right)=\operatorname{J}\left(1-s, n, e\right))))\land(\forall s\in Signs, (\forall e\in Z, \operatorname{J}\left(s, 1, e\right)=\operatorname{delta}\left(e\right)))\land(\forall s\in Signs, (\forall n\in N, (\forall e\in Z, \operatorname{J}\left(s, n, e\right)=\operatorname{J}\left(s, n, -e\right))))\land(\forall e\in Z, \operatorname{C}\left(e\right)=\operatorname{F}\left(C, e\right))\land(\forall w:Z\Rightarrow R, ((\forall e\in Z, 0\le\operatorname{w}\left(e\right)\le c)\land(\forall epsilon>0, \operatorname{Finite}\left(\operatorname{L}\left(w, epsilon\right)\right))\land(\forall e\in Z, \operatorname{w}\left(e\right)\le\operatorname{F}\left(w, e\right)))\implies(\forall e\in Z, \operatorname{w}\left(e\right)\le\operatorname{C}\left(e\right)))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Patterns/Separable/OccupiedComparison.actual_occupation_subsolution_comparison` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The carrier U(n) is the actual set of permutations avoiding 2413 and 3142. J(n) is its subtype with no proper direct cut. For an integer e, M(n,e) counts members of J(n) with at least one position j satisfying j-pi(j)=e. A member contributes once regardless of the number of its hits. Both count series start at length one, retaining the singleton and excluding the empty permutation. The zero-based displacement equals the source's one-based displacement.

Put b=sqrt(2)-1, rho=b squared, a=1-b, h=(1+b)/2 and c=a/2. C(e) is the sum over positive n of rho to n times M(n,e); O(e)=(2/a)C(e). C is raw occupation mass. In the operator, the natural index r denotes length r+1, t(r)=rho to (r+1) times card(U(r+1)), k(r)=t(r)+(rho/2) if r=0 and k(r)=t(r) otherwise; q(r)=(3/2)t(r)+(rho/2) if r=0 and q(r)=(3/2)t(r) otherwise. The correction is supported at the singleton length.

Let V(x)=x squared/(h+x). For each integer e, F(u,e) is f(e) plus the sum over r>=0 of k(r) times the sum of u(e+r+1) and u(e-r-1), minus q(r) times the sum of V(u(e+r+1)) and V(u(e-r-1)). Here f(0)=rho and f(e)=(rho/2)t(abs(e)-1) for nonzero e.

The theorem establishes summability of t, sum(t)=b, sum(k)=one half, summability of every occupied series m(e), and the actual mass box together with reflection and the occupation equation. Here m(e) is the sequence rho to (r+1) times M(r+1,e). The actual occupation equation C(e)=F(C,e) is proved for every integer e. Comparison applies to every function w from the integers to the reals satisfying 0<=w(e)<=c and w(e)<=F(w,e) at every integer. For every real epsilon>0, the set L(w,epsilon) of integers with epsilon<=w(e) must be finite. Thus the displayed box, equation and subsolution clauses hold for all integers e, and the finiteness clause holds for all positive epsilon. The conclusion is w(e)<=C(e) for every integer e.

The actual cardinality theorem identifies t(r) with rho to (r+1) times the r-th large Schroder number. Its native recurrence gives t(r+1)=rho*t(r)+sum_(i+j=r)t(i)t(j). For each N the triangular convolution sum through N-1 is bounded by the square of the first N-term sum. Induction therefore bounds every nonnegative partial sum by b, since rho+rho*b+b squared=b. This proves convergence at the critical radius without assuming analytic GF evaluation. The absolutely convergent Cauchy product yields T=rho+rho*T+T squared for T=sum(t). Since rho=1-2*b and b squared+2*b=1, this equation is (T-b) squared=0. Thus T=b and sum(k)=one half.

Native actual cardinalities give twice card(J(n))=card(U(n)) for n>=2 and card(J(1))=card(U(1))=1. Their positive-length weighted total is c=(b+rho)/2. Subtype cardinality bounds give convergence of each occupied-count series and 0<=C(e)<=c unconditionally. All operator sums on the box converge by domination.

Inversion exchanges the two forbidden patterns and preserves each proper-cut class. A direct cut of size i remains a direct cut of size i; a skew cut of size i becomes a skew cut of size n-i. A hit j-pi(j)=e becomes the hit pi(j)-inverse(pi(j))=-e. Thus each indecomposable occupied count, and its convergent weighted mass, is even.

Every weighted recurrence summand is nonnegative and at most twice the product of the corresponding shape weights. Absolute convergence therefore permits transport from the proper-cut sums to the joint sum over two positive factor lengths. Let T(e) be the full occupied mass and P(e) the direct-decomposable occupied mass. The direct recurrence and partition give P=C(b-T)+cT and T=C+P. Since 1-c=h and 1+b=2h, these imply T=2C-2V(C) and P=C-2V(C).

The skew indecomposable mass is the weighted delta(e)+P(e). This weighted delta is rho at zero and zero elsewhere. The skew recurrence sums its shifted product with the full shape weights, together with the oppositely shifted full occupied mass times the indecomposable shape weights. Reflecting and averaging that identity yields kC-qV(C) at each neighbor. The remaining delta terms vanish at e=0 and select exactly the length abs(e) for nonzero e. Their average is f(e)-delta(e), so C=F(C) holds with the literal forcing and singleton correction.

On the box, V is strictly increasing and its secant slopes lie between zero and one half. Consequently each scalar neighbor term is increasing. For a positive maximum M of w-C, every neighbor-term difference is at most k(r)M. The singleton neighbor has a strict inequality: either the displacement difference is nonpositive, or its positive V difference is multiplied by a strictly positive loss weight. The finite positive superlevel condition supplies an attained maximum. Summing the strict neighbor inequalities and using twice the kernel mass equal to one contradicts the actual equation and the subsolution inequality.

The actual singleton gives C(0)>=rho>0. A concrete vanishing subsolution is w(0)=rho/2 and w(e)=0 for nonzero e. Its value lies in the mass box and its positive superlevel sets are contained in the singleton {0}. Each neighbor term is nonnegative on the box; the forcing at zero is rho and elsewhere is nonnegative. Thus w<=F(w), and comparison gives w<=C with no event-equation premise. This finite-support application supplies no uniform lower bound.

The finite recurrence clauses use U(n)=card(U(n)) and I(s,n)=card of actual indecomposables in orientation s, where zero means direct and one means skew. A(n,e) counts all avoiders with a hit on e, J(s,n,e) counts orientation-s indecomposables with a hit, and D(s,n,e) counts permutations with a proper orientation-s cut and a hit. The sum over cuts(n) ranges over integers i with 0<i<n. Every clause includes all natural lengths n and all integer e.

The actual minimum-cut equivalence reconstructs each permutation as a unique pair of an orientation-s indecomposable of length i and an unrestricted avoider of length n-i. Transport of the literal position/value difference through that reconstruction identifies the hit event with the union of the factor events. In a direct sum, the displacements are unchanged. The disjoint partition into left-hit/right-no-hit and right-hit gives J(0,i,e)*(U(n-i)-A(n-i,e)) plus I(0,i)*A(n-i,e). This subtracts the intersection exactly, without counting multiple hits in either factor.

In a skew sum, a left factor hit has diagonal e+n-i and a right factor hit has diagonal e-i. The actual Fin bounds place the largest left displacement below the smallest right displacement, with a gap of two. Both events cannot hold for a single e. Their cardinalities therefore add: J(1,i,e+n-i)*U(n-i)+I(1,i)*A(n-i,e-i). The finite sigma partition over minimum cuts gives the two displayed actual count recurrences. Absolute convergence transports these identities to the literal critical fixed-point equation, preserving the joint factors and both displacement shifts.

Signs is the two-element orientation set {0,1}. Splitting each actual hit fiber according to the presence of a proper orientation-s cut gives A(n,e)=J(s,n,e)+D(s,n,e). For n>=2 the native opposite-sign law preserves the underlying permutation and its hit event, giving D(s,n,e)=J(1-s,n,e). At length one, both signs have J(s,1,e)=delta(e), where delta is one at zero and zero otherwise. The singleton proof uses the actual Fin(1) displacement. These clauses establish the finite event partitions needed before weighted transport.

A positive logarithmic subsolution still requires uniform residual estimates and a finite-region forcing bound. The uniform occupied-diagonal lower bound and the full separable derangement-ratio conjecture remain open.

## References

- Truth anchor: `D5/S1/Words/Patterns/Separable/OccupiedComparison.actual_occupation_subsolution_comparison`
- Dependency: [D5/S1/Words/Patterns/Separable/ActualCardinality](ActualCardinality.md)
