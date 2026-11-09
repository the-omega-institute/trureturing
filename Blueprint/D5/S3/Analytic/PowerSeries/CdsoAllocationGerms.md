# Actual allocation germs

## Abstract

The full CDSO allocation functions have removable analytic extensions and the quadratic Taylor cutoff.

**Theorem 1.1 (Full allocation functions and their genuine coefficients).**

$$\forall a \in Nat,\; \forall h \in Nat,\; \forall b \in \operatorname{AllocationData}\left(a, h\right),\; \forall c \in \operatorname{AllocationData}\left(a, h\right),\; 2 \le a \implies \operatorname{AnalyticAtZero}\left(\operatorname{extension}\left(b\right)\right) \land \operatorname{AnalyticAtZero}\left(\operatorname{extension}\left(c\right)\right) \land \operatorname{PositiveGermEq}\left(\operatorname{actual}\left(b\right), \operatorname{extension}\left(b\right)\right) \land \operatorname{PositiveGermEq}\left(\operatorname{actual}\left(c\right), \operatorname{extension}\left(c\right)\right) \land (\operatorname{PositiveGermEq}\left(\operatorname{actual}\left(b\right), \operatorname{actual}\left(c\right)\right) \iff \forall k \in Nat,\; k \le 3(6(a+1+h)+5)^{2} \implies \operatorname{TaylorCoeff}\left(\operatorname{extension}\left(b\right), k\right) = \operatorname{TaylorCoeff}\left(\operatorname{extension}\left(c\right), k\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/PowerSeries/CdsoAllocationGerms.allocation_germ_iff_taylor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix natural a at least two and h. An allocation datum has a branch j with 1<=j<=h, a remainder d<a+j-1, a remainder t<h+1-j, and an arbitrary integer vector z on Fin(a+j). Write m=a+j, r=m-1, n=h+1-j and s=a+1+h. Source-admissible vectors satisfy sum z=n-d, sum z-positive<=n and sum z-negative<=d; the theorem also permits all other integer vectors. Every source residue supplies such d and t, so no residue, branch or allocation is excluded.

The definitions are alpha=(a-1)/r, beta=j/(rn), phi=-(n+(r-1)d)/r, sigma=(d-n)/r, gamma=(n-d)/(rn), v-minus=gamma-t/n and v-plus=v-minus+1. Let delta_i=sigma+z_i, delta_0=sigma+min z, and L=n-sum z-positive. The radical R(b,delta,k,u) is sqrt((b+delta*u)^2+k^2*u^2)/(b+delta*u)-1, with the nonnegative real square root, positive near zero.

A_b is exactly source formula (8.4): two divided by u squared times the sum over i of (alpha+phi*u)R(alpha,delta_i,m,u)+u(d-z_i-negative)R(alpha,delta_i,r,u)+u*z_i-positive*R(alpha,delta_i,2,u), plus uL times the difference of R(alpha,delta_0,2,u) and R(alpha,delta_0,r,u), plus (n-t) times ((beta+(v-minus-1)u)R(beta,v-minus,1,u)+uR(beta,v-minus,2,u)), plus t times the corresponding v-plus expression.

Replace every R/u squared by k squared divided by (b+delta*u)(sqrt((b+delta*u)^2+k squared*u squared)+b+delta*u). This defines E_b, the actual removable analytic extension. TaylorCoeff(E,k) is the k-th iterated real derivative at zero divided by k factorial. PositiveGermEq means equality throughout a sufficiently small positive neighborhood of zero. The cutoff includes its endpoint.

Each allocation is a sum of at most 3m+2+2n<=3s+2 affine-weighted radicals. Repeating each tail entry preserves the case n=1. A pair has at most 6s+4 radicals. Clearing the product of their affine denominators gives polynomial coefficients of degree at most K+1 and quadratic radicands with nonzero constant roots; its rational part is the radicand one. The formal cutoff applies to the genuine Taylor series. Analytic uniqueness, including the one-sided identity theorem, returns the asserted actual germ identity.

There is no frequency-separation condition, new threshold in a, noncancellation assumption or independence hypothesis. Identical radicals and signed, zero or absent weights are retained. The result gives no optimizer reconstruction, least period, uniform arithmetic separation or parameter-growth threshold.

## References

- Truth anchor: `D5/S3/Analytic/PowerSeries/CdsoAllocationGerms.allocation_germ_iff_taylor`
- Dependency: [D5/S3/Analytic/PowerSeries/RadicalMultiplicity](RadicalMultiplicity.md)
