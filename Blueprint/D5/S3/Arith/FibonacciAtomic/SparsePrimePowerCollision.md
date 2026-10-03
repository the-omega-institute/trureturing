# Sparse Prime-Power Fibonacci Collisions

## Abstract

An arbitrary sparse table of positive times leaves two fixed primitive states with equal complete gcd readings and arbitrarily late separation.

N includes zero and Z denotes the integers. The integer Fibonacci sequence extends F(0)=0 and F(1)=1 by the recurrence at every integer index. The natural sequence agrees with it at nonnegative indices. Absolute value is taken after evaluating the entire signed observation. All gcd values are nonnegative natural numbers. Time tables are finite sets, so their cardinalities count distinct labels, not multiplicities.

**Definition 1.1 (Signed observation).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/SparsePrimePowerCollision.signedObservation`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/SparsePrimePowerCollision.signedObservation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For n,z in Z and k in N, Y(n,z;k)=F(k-1)n+F(k)z. Both Fibonacci indices in this expression are interpreted in Z, including k-1.

**Definition 1.2 (Actual natural source).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/SparsePrimePowerCollision.sourceObservation`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/SparsePrimePowerCollision.sourceObservation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a,b,k in N, O(a,b;k)=F(k+3)a+F(k+4)b, evaluated in N.

**Definition 1.3 (Sparse-table threshold).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/SparsePrimePowerCollision.threshold`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/SparsePrimePowerCollision.threshold` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For p,e in N, put P=p^e, q=p^(e-1), R=zeroRank(q), r=zeroRank(P). Here e-1 is natural subtraction and zeroRank(m) is the natural infimum of the positive indices d for which m divides F(d), with empty infimum zero. Define T(p,e)=r if r=R, and T(p,e)=r-R otherwise.

**Theorem 1.4 (Fixed all-time arithmetic collision).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/SparsePrimePowerCollision.sparse_prime_power_gcd_collision`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/SparsePrimePowerCollision.sparse_prime_power_gcd_collision` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every p,e,Q in N with p prime, e>=2 and Q>0, and every finite S subset of N with k>=1 for every k in S and |S|<T(p,e), put P=p^e, q=p^(e-1) and H=QP. There exist fixed n,z,n2,z2 in Z and fixed a,b,a2,b2 in N with all of the following properties. The prime p does not divide both n and z, and does not divide both n2 and z2. Each of a,b,a2,b2 is strictly smaller than H. For every k in N with k>=1, gcd(O(a,b;k),H)=Q gcd(abs(Y(n,z;k)),P) and gcd(O(a2,b2;k),H)=Q gcd(abs(Y(n2,z2;k)),P). For every k in S, gcd(abs(Y(n,z;k)),P)=gcd(abs(Y(n2,z2;k)),P), and gcd(O(a,b;k),H)=gcd(O(a2,b2;k),H). Finally, for every B in N there exists t in N with B<t, t>=1 and t not in S such that gcd(abs(Y(n,z;t)),P)=P, gcd(abs(Y(n2,z2;t)),P)=q, gcd(O(a,b;t),H)=H and gcd(O(a2,b2;t),H)=H/p. All eight witnesses are chosen before the universal quantifier over B. No zero-rank existence, lifting dichotomy or orbit-classification hypothesis is required.

The step M(a,b)=(b,a+b) is an invertible transformation on the finite residue-state space for every positive modulus. A finite return gives a positive Fibonacci zero and hence a least positive zero. Strong divisibility identifies all zero indices with multiples of that least index. At the lower rank R, write c=F(R-1), d=F(R). Adjacent coprimality makes c a unit modulo P. The relations q dividing d and e>=2 imply d^2=0 and pd=0 modulo P. Iterating the shift gives cY(s+iR)=c^i(cY(s)+idY(s+1)) modulo P. Thus pR is a scalar return, not necessarily an identity return. Rank divisibility yields R dividing r and r dividing pR; since p is prime, r=R or r=pR.

Remove from the r residue phases every phase met by S. In growth, |S|<r-R leaves more than R phases. Two distinct omitted phases have the same reduction modulo R. Choose positive representatives u,v of them and the states K(u)=(F(u),-F(u-1)), K(v). Their signed readings satisfy Y(K(u);k)=(-1)^k F(u-k) at every natural k, with no restriction k<=u. Strong divisibility reduces the lower gcd to gcd(F(gcd(u-k,R)),q), which is the same for the two states. Neither omitted phase is queried, so neither state has a top-P hit on S. Every proper divisor of P divides q, hence equality of lower gcds and absence of top hits imply equality of full-P gcds there. On the first omitted phase, the first gcd is P; the second is divisible by q but not P, so its gcd is exactly q.

In stagnation, |S|<r leaves an omitted phase with positive representative u. Choose K(u) and K(u)-qK(u+1). Their readings are (-1)^k F(u-k) and (-1)^k(F(u-k)-qF(u+1-k)). At time u their consecutive reading pairs are common unit multiples of (0,1) and (q,1); this is simultaneous inverse transport of the perturbation. The states agree modulo q. Off their omitted phase there is no q-hit, and consequently no P-hit, so their full gcds agree. On the phase, the first reading is P-divisible and its neighboring Fibonacci value is a p-unit. The second reading is q-divisible but not P-divisible. Adjacent coprimality also proves primitiveness; the transported perturbation is a multiple of p, preserving it. In either case a label in the first omitted phase can be chosen larger than every prescribed B while the states remain fixed.

For each fixed signed state, use C inverse=((5,-3),(-3,2)), where C=((2,3),(3,5)). Take the least nonnegative residues A,B of its two inverse coordinates modulo P and set the actual source to (QA,QB). Its coordinates are below QP. The identity Y(C(A,B);k)=O(A,B;k) and congruence modulo P give equality of every local gcd. Linearity and gcd(Qy,QP)=Q gcd(y,P) give the complete-source laws simultaneously for all positive times. No coprimality of Q and p is needed, and the sources themselves need not be primitive when p divides Q.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/SparsePrimePowerCollision.signedObservation`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/SparsePrimePowerCollision.sourceObservation`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/SparsePrimePowerCollision.sparse_prime_power_gcd_collision`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/SparsePrimePowerCollision.threshold`
- Dependency: [D5/S3/Arith/FibonacciAtomic/TimeSampling](TimeSampling.md)
