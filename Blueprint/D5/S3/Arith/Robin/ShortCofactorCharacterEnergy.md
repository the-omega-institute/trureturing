# Short Cofactor Character Energy

## Abstract

Short cofactor character sums have fourth moment upper and first moment lower bounds.

For a real cutoff H, I(H) consists of the positive natural numbers strictly below H. The multiplicative energy E(I) counts ordered quadruples (a,c,b,d) in I to the fourth power with ab=cd.

**Theorem 1.1 (Logarithmic energy bound).**

$$\forall H \in \mathbb{R}, 1 \le H \Rightarrow E\left(I\left(H\right)\right) \le 2 H^{2} (1+\log\left(H\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ShortCofactorCharacterEnergy.short_interval_energy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The cutoff is any real number at least one. There is no primality or coprimality restriction.

Write a=gu and c=gv with g=gcd(a,c). The equality ab=cd and coprimality of u,v imply b=jv and d=ju. For m=max(u,v), the two orientations and the smaller coordinate give at most 2m choices; both g and j are at most N/m for the integral interval from 1 to N. Summing the resulting bounds gives 2N squared times the N-th harmonic number.

This is the classical gcd parametrization for the multiplicative energy of an interval. The harmonic estimate is the standard bound by 1+log(N).

**Theorem 1.2 (Character moments for any modulus).**

$$\begin{aligned}\forall V \in \mathbb{N}, \forall H \in \mathbb{R},\\0 < V, 1 \le H, H^{2} \le V \Rightarrow\\M_{4} \le 2 H^{2} (1+\log\left(H\right)) \land\\(2 k \le Q \Rightarrow \frac{k^{\frac{3}{2}}}{4 H \sqrt{1+\log\left(H\right)}} \le M_{1})\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ShortCofactorCharacterEnergy.character_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

V is a positive modulus, S is the subset of I(H) coprime to V, k is its size, and Q is phi(V). B is the sum of a character on S. M_p is the sum of the p-th powers of the absolute values of B over all nonprincipal characters, divided by Q.

Character orthogonality identifies the full fourth moment with integer multiplicative energy when H squared is at most V. Removing the principal character decreases this moment. The second moment after removal is k-k squared over Q. Two applications of Cauchy-Schwarz give M_2 cubed <= M_1 squared times M_4, yielding the first moment estimate when 2k <= Q.

For the classical relation between multiplicative collisions and character moments, see Ayyad, Cochrane and Zheng, Journal of Number Theory 59, 398-413, doi:10.1006/jnth.1996.0105.

**Theorem 1.3 (Fibonacci cutoffs).**

$$\begin{aligned}\forall a \in \mathbb{R}, a > 0 \Rightarrow \exists r_{0} \in \mathbb{N},\\\forall r \in \mathbb{N}, (r \ge r_{0} \land Prime\left(r\right)) \Rightarrow\\H^{2} < V \land M_{4} \le 2 H^{2}(1+\log\left(H\right)) \land\\\frac{k^{\frac{3}{2}}}{4 H \sqrt{1+\log\left(H\right)}} \le M_{1}\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ShortCofactorCharacterEnergy.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let V=F_r, g=ceil(V/10), A=1+Vg, y=log(A), ell=log(y), and H=exp(a*y/ell squared). For every positive real a, all sufficiently large prime indices r satisfy the three displayed bounds with these same parameters.

Euler's product formula gives n <= 2*phi(n) squared for every positive integer n: p <= (p-1) squared for primes p other than two, and two contributes the factor 2. An explicit threshold ensures 8*H squared < V. The cardinality of the short unit set is at most H, so 2k <= phi(V) and the general character estimates apply.

The logarithmic cutoff is smaller than V because A <= V squared and ell squared eventually exceeds 8a. The growth bound r <= F_r for r >= 5 transfers the explicit threshold to Fibonacci indices.

## References

- Truth anchor: `D5/S3/Arith/Robin/ShortCofactorCharacterEnergy.character_bounds`
- Truth anchor: `D5/S3/Arith/Robin/ShortCofactorCharacterEnergy.result`
- Truth anchor: `D5/S3/Arith/Robin/ShortCofactorCharacterEnergy.short_interval_energy`
