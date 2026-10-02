# Sharp Prime Gcd Observation Horizon

## Abstract

The least Fibonacci zero rank determines the signed prime gcd prefix horizon, attained on bounded nonnegative sources.

N includes zero and Z denotes the signed integers. F(0)=0 and F(1)=1. For a natural modulus p, r(p) is the infimum of the positive indices t such that p divides F(t), with infimum zero when that set is empty. For every prime p this set is nonempty, 3 <= r(p) <= p+1, and B(p) is at least two. Subtraction in N is truncated.

**Definition 1.1 (Actual nonnegative source observation).**

$$\forall k,a,b \in N, \operatorname{y}\left(k, a, b\right) = \operatorname{F}\left(k + 3\right) \cdot a + \operatorname{F}\left(k + 4\right) \cdot b$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/PrimeGcdHorizon.observation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A source consists of independent natural coordinates a,b. Its initial recurrence state is (n,z)=(2a+3b,3a+5b), with y(0)=n, y(1)=z and y(k+2)=y(k+1)+y(k). Thus the displayed observation is the actual recurrence at time k, not merely a phase label. All source coordinates, including zero, are allowed.

**Definition 1.2 (Signed initial-state observation).**

$$\forall k \in N, \forall n,z \in Z, \operatorname{Y}\left(k, n, z\right) = \operatorname{ite}\left(k = 0, n, \operatorname{F}\left(k - 1\right) \cdot n + \operatorname{F}\left(k\right) \cdot z\right)$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/PrimeGcdHorizon.signedObservation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The initial coordinates n,z are arbitrary signed integers, not nonnegative source coordinates. Y(0;n,z)=n. For positive natural k, Y(k;n,z)=F(k-1)n+F(k)z, so Y(1;n,z)=z and Y(k+2;n,z)=Y(k+1;n,z)+Y(k;n,z). Its prime gcd reading is gcd(|Y(k;n,z)|,p), a natural number. Only positive times occur in the recovery clauses.

**Definition 1.3 (The full-orbit correction).**

$$\forall p \in N, \operatorname{B}\left(p\right) = \operatorname{ite}\left(\operatorname{r}\left(p\right) = p + 1, \operatorname{r}\left(p\right) - 1, \operatorname{r}\left(p\right)\right)$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/PrimeGcdHorizon.horizon` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The function ite takes its second argument when its first argument holds, and its third argument otherwise. Thus B(p)=r(p)-1 when r(p)=p+1, and B(p)=r(p) otherwise. For primes, the latter case is exactly r(p)<p+1.

**Theorem 1.4 (Universal recovery and attained first separation).**

$$\forall p \in N, (\operatorname{Prime}\left(p\right)) \implies ((\forall n,z,n2,z2 \in Z, (\forall k \in N, ((1 \le k) \land (k \le \operatorname{B}\left(p\right))) \implies (\operatorname{gcd}\left(\operatorname{natAbs}\left(\operatorname{Y}\left(k, n, z\right)\right), p\right) = \operatorname{gcd}\left(\operatorname{natAbs}\left(\operatorname{Y}\left(k, n2, z2\right)\right), p\right))) \implies (\forall k \in N, (1 \le k) \implies (\operatorname{gcd}\left(\operatorname{natAbs}\left(\operatorname{Y}\left(k, n, z\right)\right), p\right) = \operatorname{gcd}\left(\operatorname{natAbs}\left(\operatorname{Y}\left(k, n2, z2\right)\right), p\right)))) \land (\forall a,b,c,d \in N, (\forall k \in N, ((1 \le k) \land (k \le \operatorname{B}\left(p\right))) \implies (\operatorname{gcd}\left(\operatorname{y}\left(k, a, b\right), p\right) = \operatorname{gcd}\left(\operatorname{y}\left(k, c, d\right), p\right))) \implies (\forall k \in N, (1 \le k) \implies (\operatorname{gcd}\left(\operatorname{y}\left(k, a, b\right), p\right) = \operatorname{gcd}\left(\operatorname{y}\left(k, c, d\right), p\right)))) \land (\exists a,b,c,d \in N, (a < p) \land (b < p) \land (c < p) \land (d < p) \land (\forall k \in N, ((1 \le k) \land (k < \operatorname{B}\left(p\right))) \implies (\operatorname{gcd}\left(\operatorname{y}\left(k, a, b\right), p\right) = \operatorname{gcd}\left(\operatorname{y}\left(k, c, d\right), p\right))) \land (\operatorname{gcd}\left(\operatorname{y}\left(\operatorname{B}\left(p\right), a, b\right), p\right) \neq \operatorname{gcd}\left(\operatorname{y}\left(\operatorname{B}\left(p\right), c, d\right), p\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/PrimeGcdHorizon.sharp_prime_gcd_horizon` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every prime p and arbitrary signed integer initial pairs (n,z),(n2,z2), agreement of their absolute prime gcd readings at times 1 through B(p) implies agreement at every positive time. For arbitrary natural source coordinates a,b,c,d, agreement of the prime gcd readings at times 1 through B(p) implies agreement at every positive time. Conversely, four coordinates smaller than p can be chosen so that the readings agree at every positive time smaller than B(p) and differ exactly at B(p). No common initial value, known common content, or primitive-source restriction is assumed. All three conjuncts include p=2 and p=5.

Over the field Z/pZ, the Fibonacci step (u,v) -> (v,u+v) is invertible. Its second-coordinate reading at time t is F(t)u+F(t+1)v. The nonzero kernel vector (F(t+1),-F(t)) defines a projective direction. Two zero readings of a nonzero state have time difference divisible by r(p). The r(p) distinct kernel directions therefore occupy an orbit inside the p+1 directions of the projective line. When that orbit is proper, its last phase and an outside direction first differ at positive time r(p). When the orbit is full, the last two phases first differ at r(p)-1. The zero state is identified by the first two readings, so removing the primitive-source restriction does not enlarge the horizon.

For signed initial state (n,z), the residue of Y(k;n,z) is the field reading F(k-1)n+F(k)z at time k-1. A signed integer has zero residue modulo p exactly when p divides its absolute value. Thus the same field-state estimate determines the absolute gcd readings without a sign or nonnegativity assumption.

For any two prescribed residue states (n,z), the inverse matrix [[5,-3],[-3,2]] gives residue source coordinates. Taking their representatives between zero and p-1 yields actual nonnegative sources. Multiplication by [[2,3],[3,5]] returns exactly the prescribed residue state. A prime gcd is p at a zero residue and 1 otherwise, so this transport preserves every gcd reading and the exact first separation time.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/PrimeGcdHorizon.horizon`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/PrimeGcdHorizon.observation`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/PrimeGcdHorizon.sharp_prime_gcd_horizon`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/PrimeGcdHorizon.signedObservation`
- Dependency: [D5/S3/Arith/FibonacciAtomic/TimeSampling](TimeSampling.md)
