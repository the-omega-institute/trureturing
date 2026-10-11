# Four-coordinate finite common-marginal comparison

## Abstract

A diagonal law maximizes real supermodular expectations with four equal finite marginals.

**Theorem 1.1 (Diagonal maximization).**

Lean statement: `D5/S3/Combinatorics/Probability/FiniteCommonMarginalSupermodular.common_marginal_supermodular_le_diagonal`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Probability/FiniteCommonMarginalSupermodular.common_marginal_supermodular_le_diagonal` (`✓ std3`). ∎

*Citation.* Giovanni Puccetti and Ruodu Wang (2015). *Extremal Dependence Concepts*. DOI: [10.1214/15-STS525](https://doi.org/10.1214/15-STS525). URL: <https://arxiv.org/abs/1512.03232v3>.

*Commentary.*

Let C be any nonempty finite linearly ordered set. A joint law p on the functions from Fin 4 to C has arbitrary nonnegative real weights whose sum is one. Let m be a real function on C. For every coordinate i and every t in C, the sum of p(x) over all x with x(i)=t is exactly m(t). These identities imply both nonnegativity and normalization of m.

Let f be any real function on the four-coordinate product. Suppose that f(x)+f(y) is at most f(x meet y)+f(x join y) for every x and y, where meet and join take the minimum and maximum in each coordinate. Then the sum of p(x)f(x) over the whole product is at most the sum of m(t)f(t,t,t,t) over C.

The test may take negative values and need not be increasing. The law may have zero cells, irrational masses and arbitrary dependence. Repeated coordinates, a singleton support, and atoms with zero marginal mass are included.

Order the scalar support and follow the diagonal through adjacent levels. Within each level raise coordinates in the order 0,1,2,3. The difference in f at each such step defines a coordinate increment. For an arbitrary product point, clip each coordinate at the current level. Supermodularity compares each clipped increment with the corresponding diagonal increment. Summing the increments gives a separable upper bound, with equality at every diagonal point. Taking its expectation uses only the exact one-coordinate marginals.

This is the finite common-support form of the classical comonotonic supermodular comparison in Theorem 2.1(d) of the cited source.

For the compact-interval application, let a and b be arbitrary real numbers with a at most b, put I=[a,b], and put B=I to the fourth power inside the ambient space of functions from Fin 4 to the reals. Write e_i(x)=x(i) and d(t)=(t,t,t,t). Let mu be any Borel probability measure on the ambient space with x in B for mu-almost every x. Assume exactly (e_i)_*mu=rho for every i, where rho=(e_0)_*mu. Let f be a signed real function on the ambient space, continuous only on B, satisfying f(x)+f(y) at most f(x meet y)+f(x join y) for every x,y in B. Then the integral of f against mu is at most the integral of f(d(t)) against rho.

Here rho is a probability measure concentrated on I. No independence or monotonicity of f is required. The law may be nonatomic, singular, atomic or mixed, with arbitrary dependence and coordinate ties; neither finite support nor rational or uniform masses are required. The case a=b is included. Values of f outside B are unrestricted, and global measurability of f is unnecessary.

To relate the ambient and compact formulations, write X for the functions from Fin 4 to the interval subtype I, and j:X to B for coordinatewise inclusion, viewed as an ambient map. Let p send a real t to min(b,max(a,t)) in I, and let r(x)(i)=p(x(i)). The maps p and r are continuous, r composed with j is the identity on X, and j(r(x))=x on B. Thus nu=r_*mu is a probability measure and j_*nu=mu as whole joint laws. With eta=p_*rho and c:I to the reals the inclusion, c_*eta=rho and every subtype coordinate law of nu is eta. Conversely inclusion sends a subtype law back to an ambient law concentrated on B and clipping recovers it. The inclusions are measurable embeddings, so equality of all four coordinate laws is equivalent in the two formulations. Inclusion also commutes with coordinatewise minimum and maximum, transferring exactly the stated supermodularity condition.

Set F=f composed with j and d_I(t)(i)=t in X. Continuity on B makes F continuous on the compact space X, hence Borel measurable and bounded in absolute value by a finite constant M. The same bound holds for F(d_I(t)) on I. These functions are integrable against the probability measures nu and eta. Change of variables through the measurable embeddings j and c gives the signed identities: the integral of f against mu equals the integral of F against nu, and the integral of f(d(t)) against rho equals the integral of F(d_I(t)) against eta. It also gives almost-everywhere strong measurability and the bound M for both ambient integrands. Thus their signed integrals are defined and integrable even when the off-cube values of f are not measurable.

For the compact comparison, take measurable finite-range maps q_n:I to I converging pointwise to the identity, and define Q_n(x)(i)=q_n(x(i)). Such simple-function approximations exist on the compact metric interval, including a singleton interval. The finite ordered support C_n is the range of q_n. In the finite comparison substitute p_n(z)=(Q_n)_*nu({z}), m_n(t)=(q_n)_*eta({t}), and the restriction of F to C_n to the fourth power. All four marginals of (Q_n)_*nu equal (q_n)_*eta exactly. The inclusion of C_n into I preserves minimum and maximum, so this restriction is supermodular. The finite comparison gives the integral of F(Q_n(x)) against nu at most the integral of F(d_I(q_n(t))) against eta, with the actual real cell masses.

Continuity gives F(Q_n(x)) tending to F(x) and F(d_I(q_n(t))) tending to F(d_I(t)) pointwise. Both sequences are bounded in absolute value by the same M, and the constant M is integrable for both probability measures. Dominated convergence therefore passes the finite inequalities to the compact inequality. The two signed change-of-variables identities then give the ambient inequality with its original common scalar law rho.

In the four-rate argument, equations 16.25 and 16.26 use the comparison for H=F minus x(0)x(1). Applying the compact-interval consequence to that H requires its continuity and lattice supermodularity on the chosen cube, together with concentration and exact equality of the four marginals of the actual rate law. Source-law identification, stationarity, the second-moment identity, rigidity, zero exclusion and a positive attained minimum are separate requirements of that argument. This expectation comparison alone does not imply Theorem 16.2 or Corollary 16.3.

## References

- Truth anchor: `D5/S3/Combinatorics/Probability/FiniteCommonMarginalSupermodular.common_marginal_supermodular_le_diagonal`
