# Uniform Actual Least Crossings and the 5040 Core

## Abstract

A single threshold makes actual least Robin-height crossings strict abundancy records divisible by the literal integer 5040.

**Theorem 1.1 (One threshold for every original eta).**

Lean statement: `D5/S3/Arith/Robin/ActualLeastCrossing5040.uniform_actual_least_crossing_record_5040`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ActualLeastCrossing5040.uniform_actual_least_crossing_record_5040` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Write A(n)=sigma(1,n)/n, W(n)=log(A(n)), and let F be the literal originalObjective. The height is the existing actualHeight(eta,n) =(log(n))^eta*(F(n)-gamma). There exists one positive real T0 such that, for every real 0<eta<1/2 and T>=T0, every actual natural m>=3 with H(eta,m)>=T and H(eta,n)<T for all 3<=n<m satisfies A(m)>30, A(n)<A(m) for every 0<n<m, and 5040 divides m.

The coefficient-two actual integer envelope supplies its own threshold U. Choose R=max(U,exp(2),log(30)). Cofinality of the literal iterated logarithms gives a natural M>=4 such that gamma+log(log(log(m)))>=R for every m>=M. On the finite initial segment use the eta-independent bound max(1,(log(j))^(1/2))*max(F(j)-gamma,0). One plus the sum of these nonnegative bounds defines T0. Thus every crossing under consideration has m>=M, F(m)>gamma, and W(m)>R.

If a positive rival n<m had W(n)>=W(m), the elementary actual bound sigma(1,n)<=n^2 would imply log(n)>=W(n)>R. This first places n in the coefficient-two envelope range, with n>=3 and l=log(log(n))>=2; in particular it excludes the predecessors one and two without omitting them from the record statement.

Put X=log(m), Y=log(n), beta=log(X)-log(Y)>0, E=F(n)-gamma, and delta=W(m)-W(n)<=0. For l>=2, beta>0 and 0<eta<=1/2 the strict scalar bound is (2/l)*(1-exp(-eta*beta))<log(1+beta/l). To see strictness, differentiate log(l+u)-log(l)-(2/l)*(1-exp(-u/2)) on u>=0. Its value at zero is zero and its derivative is strictly positive for u>0, because exp(u/2)>1+u/2>=1+u/l.

Since E<=2/l and 1-(Y/X)^eta>=0, the scalar estimate also handles negative E. The exact height difference is X^eta*(delta+E*(1-(Y/X)^eta)-log(1+beta/l))<0, contradicting leastness. The actual one-layer exchange and finite Euler support bound then give the literal 5040 divisibility.

No strict record, smooth support, fixed-price optimality or originalMaximizes hypothesis is imposed on m. This statement does not construct crossings: applying first_crossing_calibration to obtain them still requires its explicit unbounded-height input. Signed upper estimates, that unboundedness input, the full RH goal and any originalMaximizes conclusion remain outside this theorem.

## References

- Truth anchor: `D5/S3/Arith/Robin/ActualLeastCrossing5040.uniform_actual_least_crossing_record_5040`
- Dependency: [D5/S3/Arith/ExponentExchange/AbundancyRecord5040](../ExponentExchange/AbundancyRecord5040.md)
- Dependency: [D5/S3/Arith/Robin/ActualIntegerHeightJump](ActualIntegerHeightJump.md)
