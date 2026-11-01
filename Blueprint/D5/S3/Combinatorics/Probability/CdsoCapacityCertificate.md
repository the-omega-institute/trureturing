# CDSO capacity certificate on the entire subset domain

## Abstract

A capacity certificate for the actual marginals of one finite subset law.

The native carrier is Fin(a+2), with natural a at least 4096; this represents the integer range a>=4096 exactly. The real parameter satisfies 0<delta<=1/a, including its terminal endpoint. Write r=a+1, s=a+2, n=a-1, q=r-delta, mu=q/s, theta=1-delta, c=2a+1, gamma=c*delta and tau=3(2a+3)delta/r^2. Labels are zero based, so label 2 is the source's third label. The theorem uses the ordered presentation of the same law: its actual marginals y(0),...,y(s-1) are nonincreasing, with ties allowed.

**Definition 1.1 (One dense subset law).**

Lean statement: `D5/S3/Combinatorics/Probability/CdsoCapacityCertificate.DenseLaw`

*Formalization.* `D5/S3/Combinatorics/Probability/CdsoCapacityCertificate.DenseLaw` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Atom(a) is the type of all nonempty finite subsets of Fin(a+2). A DenseLaw assigns nonnegative real masses x(T) to this entire type, of total one, with sum_T x(T)|T|=q. Its actual marginal is y(i)=sum_T 1_(i in T)x(T), and every marginal is at least tau. All cardinalities 1 through s, zero atom masses, nonsymmetric laws and disconnected incidence supports remain in scope. The public theorem takes this mass function and its native law conditions explicitly and constructs the DenseLaw internally.

**Definition 1.2 (Native energy and source normalization).**

Lean statement: `D5/S3/Combinatorics/Probability/CdsoCapacityCertificate.energy`

*Formalization.* `D5/S3/Combinatorics/Probability/CdsoCapacityCertificate.energy` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

energy(x)=H(x)=sum_T x(T)|T|^2 sum_(i in T)y(i)^(-2). Definition 1.1 of the source uses B=a^2*r^2/q+c*theta*r^3/q^2=r^2*Z/q^2, Z=delta*a^3+theta*r^3, and d=H-B. Z is a reference adjacent-cardinality third moment, not the third moment of an arbitrary law. The source identifies H=2J_s and B=2F_r(q) by its common-array parent model and cited CDSO normalization. No new finite-graph realization bridge is asserted.

**Theorem 1.3 (Whole capacity certificate and grouped bounds).**

Lean statement: `D5/S3/Combinatorics/Probability/CdsoCapacityCertificate.capacity_lemma`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Probability/CdsoCapacityCertificate.capacity_lemma` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every mass function satisfying exactly the stated nonnegativity, normalization, mean, density and ordering conditions, put alpha(i)=y(i)^(-2), W=sum_i alpha(i), omega=alpha(2), b(i)=c*max(omega-alpha(i),0), and W_T=sum_(i in T)alpha(i). For every nonempty T, including zero-mass atoms, R(T)=(r-|T|)[c(W-2omega)-(r+|T|)W_T] +sum_(i outside T)b(i) is nonnegative.

The full zero set is exactly the union of two cases: |T|=r, the complement is {i}, and y(i)<=y(2); or |T|=a, the complement is {i,j} with i different from j, and both y(i) and y(j) are at least y(2). No strict ordering is imposed.

Let u=(y(0)+y(1))/2, w=y(2) and v=sum_(i>=3)y(i)/n. The theorem proves v=(q-2u-w)/n and tau<=v<=w<=u<=1. Define g0(z)=r^2/z, g1(z)=r^2/z-gamma/z^2 and f(z)=a^2/z+c*theta/z^2. The Lean definitions use inverse notation for these same rational functions. Set F0=2g0(u)+g1(w)+n*g1(v), F1=2f(u)+r^2/w+c*(2u+delta-2)/w^2+n*g1(v). Then H>=max(F0,F1).

Equality H=F1 forces y(0)=y(1)=u, every y(i)=v for i>=3, and R(T)=0 on every atom of positive mass. This is a necessary consequence, not an unqualified characterization of equality by an if and only if.

The theorem also records the exact same-law identity H=r^2*sum_i(1/y(i))-c*delta*(W-2omega)-sum_i(1-y(i))*b(i)+sum_T x(T)R(T). It follows by interchanging finite incidence sums, using P(i outside T)=1-y(i), and using E[r-|T|]=delta. Every expectation and weight comes from the given x.

The mean and ordering give q<=2+a*y(2) and y(2)>=(a-1-delta)/a>=1-2/a. The inverse-square weights are at least one, and omega is bounded by (32/31)^2, which is less than 16/15. At |T|=r the residual is the omitted positive part. At |T|=a it is c times the sum of max(alpha(i)-omega,0) on omitted labels. At |T|=s it is 2W+2c*omega>0. In the remaining range |T|<a the omitted cardinality lies between 3 and s-1 and the bracket is at least (41a-2)/15>0.

For the first grouped bound, monotonicity of the weights shows that any omission set of at least two elements has weight at least alpha(0)+alpha(1). Thus every subset of cardinality at most a has weight at most M=W-alpha(0)-alpha(1). The pointwise expression (r-|T|)[c*M-(r+|T|)W_T] is nonnegative on every atom. Taking its expectation gives the source's first certificate lower bound.

For the second grouped bound only b(0) and b(1) can be nonzero. The non-residual part becomes f(y(0))+f(y(1))+r^2/w+c*(y(0)+y(1)+delta-2)/w^2 +sum_(i>=3)g1(y(i)). The second derivatives of f and g1 are positive on the closed density interval. In particular g1''(z)=2(r^2*z-3*gamma)/z^4 and r^2*tau-3*gamma=6*delta>0. The generic derivative criterion is Mathlib's strictConvexOn_of_deriv2_pos. Finite Jensen and its strict equality case are applied directly via ConvexOn.map_sum_le and StrictConvexOn.map_sum_eq_iff_of_pos. The existing Finset.sum_eq_zero_iff_of_nonneg gives the positive-mass support consequence.

The proof concerns the finite-law model. It does not assert convexity of H as a function of the law, a resource-bounded graph realization, or literature priority. The source citations to Bertsimas-Popescu Theorem 2.1 and Boyd-Vandenberghe section 3.1.8 describe weak duality and finite Jensen; their names do not replace the target-specific certificate and domain proofs above.

## References

- Truth anchor: `D5/S3/Combinatorics/Probability/CdsoCapacityCertificate.DenseLaw`
- Truth anchor: `D5/S3/Combinatorics/Probability/CdsoCapacityCertificate.capacity_lemma`
- Truth anchor: `D5/S3/Combinatorics/Probability/CdsoCapacityCertificate.energy`
