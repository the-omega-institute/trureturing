# The fourth-order integrated remainder

## Abstract

A signed uniform fourth-order Poisson remainder for integrated logarithmic defects.

**Theorem 1.1 (The complete arbitrary-family remainder theorem).**

Lean statement: `D5/S3/Analytic/CanonicalProducts/TransversePoissonRemainder.integrated_defect_poisson_remainder`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/CanonicalProducts/TransversePoissonRemainder.integrated_defect_poisson_remainder` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let I be an arbitrary index type, w,a,gamma real families with w(i)>=0, 0<=a(i)<=1/2, gamma(i)>0, and summable w(i)*a(i)^2/gamma(i)^2. For every real T>=1, put Q=tsum_i w(i)*a(i)^2*T/(T^2+gamma(i)^2) and R=tsum_i w(i)*a(i)^4*T/(T^2+gamma(i)^2)^2. Let J=integratedDefect(w,a,gamma,T), using the imported logarithmic kernel, unordered weighted defect and interval integral. The theorem asserts all four clauses: the family defining R is summable, -R<=J-2Q, J-2Q<=(4/9)*R, and R<=Q/(4*T^2).

For a single positive height g, write A=T^2+g^2 and f(v)=log(((T+v)^2+g^2)/((T-v)^2+g^2)). Its derivative is 4*T*(A-v^2)/D, where D=((T+v)^2+g^2)*((T-v)^2+g^2). The two identities D=(A-v^2)^2+4*g^2*v^2=(A+v^2)^2-4*T^2*v^2 bound this denominator on both sides. For 0<=v<=1/2 and T>=1, r=v^2/A lies in [0,1/4]. The rational inequalities (1-r)/(1+r)^2>=1-3*r and 1/(1-r)<=1+4*r/3 then give -12*T*v^2/A^2<=f'(v)-4*T/A<=16*T*v^2/(3*A^2).

The fundamental theorem of calculus integrates the derivative error from zero to v, giving -4*T*v^3/A^2<=f(v)-4*T*v/A<=16*T*v^3/(9*A^2). A second integration from zero to a gives -T*a^4/A^2<=endpointKernel(a,g,T)-2*a^2*T/A<=(4/9)*T*a^4/A^2. These integrations retain the quadratic height denominator and need no division by a or v, so the zero-displacement boundary is included.

The imported integrated_transverse_moment identity expresses J as the unordered sum of w(i)*endpointKernel(a(i),gamma(i),T). It is used directly. The Poisson terms q(i) satisfy 0<=q(i)<=T*w(i)*a(i)^2/gamma(i)^2, and the fourth-order terms rho(i) satisfy 0<=rho(i)<=q(i)/(4*T^2). Thus both families are summable under exactly the inverse-square budget. Multiplying the scalar error bounds by nonnegative weights makes the error absolutely dominated by rho. Summing those signed inequalities proves the two remainder bounds and the final comparison.

The index type need not be countable. Heights need only be individually positive; no uniform positive height lower bound is assumed. Empty index types, zero weights, a=0, a=1/2 and T=1 are all included. A finite total weighted second moment or fourth moment is not required: for example, on natural indices w=1, a=1/2 and gamma(n)=n+1 have a finite inverse-square budget and infinite total weighted second moment. The conclusion concerns the finite-T sums Q and R even in that case.

This is a general analytic estimate, with no bounded enumeration, checker, numerical reduction or certified finite instance; utility is none. The signed estimate refines the leading Poisson approximation with a height-sensitive fourth-order error. It does not assert a ratio limit, an optimal constant, polynomial growth, an infinite-product identity or a new asymptotic premise.

The functions logKernel, defect, endpointKernel and integratedDefect retain their definitions in IntegratedTransverseMoment. Application to the actual zeta zero divisor still requires the index and multiplicity correspondence, all displacement, height and summability hypotheses, and identification of the additive defect and its integral with the intended analytic quantity including normalization and boundary terms. Those bridges are absent. This theorem gives no actual-zeta or RH conclusion and makes no literature-novelty claim.

## References

- Truth anchor: `D5/S3/Analytic/CanonicalProducts/TransversePoissonRemainder.integrated_defect_poisson_remainder`
- Dependency: [D5/S3/Analytic/CanonicalProducts/IntegratedTransverseMoment](IntegratedTransverseMoment.md)
