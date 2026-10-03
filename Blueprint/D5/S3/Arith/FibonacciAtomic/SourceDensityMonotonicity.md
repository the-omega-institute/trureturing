# Real Extension of Fibonacci Source Density Ratios

## Abstract

Each real finite-product ratio increases strictly and crosses one at a unique bounded point.

F denotes the natural Fibonacci sequence with F(0)=0 and F(1)=1. Fix natural k>=1 and j. Put d=3k. Nonintegral t is an auxiliary real parameter of finite products; it does not represent a nonintegral number of tree leaves.

**Definition 1.1 (First numerator length).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/SourceDensityMonotonicity.E`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/SourceDensityMonotonicity.E` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

E(k)=F(3k-2), with truncated natural subtraction.

**Definition 1.2 (Second numerator length).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/SourceDensityMonotonicity.A`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/SourceDensityMonotonicity.A` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A(k)=F(3k-1).

**Definition 1.3 (Denominator length).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/SourceDensityMonotonicity.D`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/SourceDensityMonotonicity.D` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

D(k)=F(3k)=E(k)+A(k) for k>=1.

**Definition 1.4 (Total composition coefficient).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/SourceDensityMonotonicity.L`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/SourceDensityMonotonicity.L` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

L(k)=F(3k+1)=A(k)+D(k) for k>=1.

**Definition 1.5 (First affine target coordinate).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/SourceDensityMonotonicity.a`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/SourceDensityMonotonicity.a` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

a(k,j,t)=A(k)t+E(k)j.

**Definition 1.6 (Second affine target coordinate).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/SourceDensityMonotonicity.b`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/SourceDensityMonotonicity.b` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

b(k,j,t)=D(k)t+A(k)j.

**Definition 1.7 (Total affine target coordinate).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/SourceDensityMonotonicity.n`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/SourceDensityMonotonicity.n` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

n(k,j,t)=L(k)t+D(k)j.

**Definition 1.8 (Rising finite product).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/SourceDensityMonotonicity.rising`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/SourceDensityMonotonicity.rising` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

rising(x,m) is the product of x+i over natural 0<=i<m. The empty product is one.

**Definition 1.9 (Finite-product factor).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/SourceDensityMonotonicity.H`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/SourceDensityMonotonicity.H` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

H(k,j,t)=rising(a+1,E) rising(b+1,A) / (4^D rising(n-1/2,D)), where all coefficients and coordinates have the same k,j,t.

**Definition 1.10 (Real extension).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/SourceDensityMonotonicity.q`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/SourceDensityMonotonicity.q` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

q(k,j,t)=(t-j)H(k,j,t)/(j+1).

**Definition 1.11 (Leading coefficient).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/SourceDensityMonotonicity.c`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/SourceDensityMonotonicity.c` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

c(k)=A(k)^E(k) D(k)^A(k)/(4^D(k) L(k)^D(k)).

**Definition 1.12 (Logarithmic derivative).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/SourceDensityMonotonicity.g`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/SourceDensityMonotonicity.g` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

g(k,j,t)=1/(t-j)+A sum(1/(a+1+i),i<E) +D sum(1/(b+1+i),i<A)-L sum(1/(n-1/2+i),i<D).

**Definition 1.13 (Three-block lower envelope).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/SourceDensityMonotonicity.lowerEnvelope`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/SourceDensityMonotonicity.lowerEnvelope` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The lower envelope is 1/(t-j)-(j+1/2)/(LADt^2)-AE/(2a(a+E))-DA/(2b(b+A)) -LD/((n-1/2)(n+D-1/2)). Its coordinates share the same k,j,t.

In the displayed statement, logQ(k,j) denotes the function t maps to log(q(k,j,t)), and qOverT(k,j) denotes t maps to q(k,j,t)/t. R and N denote the real numbers and natural numbers.

**Theorem 1.14 (Strict increase and unique crossing).**

$$\forall k,j \in N, (1 \leq k) \implies (0 < \operatorname{c}\left(k\right)) \land (\forall t \in R, (j + 1 \leq t) \implies (0 < \operatorname{q}\left(k, j, t\right)) \land (\operatorname{HasDerivAt}\left(\operatorname{logQ}\left(k, j\right), \operatorname{g}\left(k, j, t\right), t\right)) \land (\operatorname{lowerEnvelope}\left(k, j, t\right) \leq \operatorname{g}\left(k, j, t\right))) \land (\operatorname{StrictMonoOn}\left(\operatorname{q}\left(k, j\right), \operatorname{Ici}\left(j + 1\right)\right)) \land (\operatorname{Tendsto}\left(\operatorname{qOverT}\left(k, j\right), \operatorname{atTop}\left(\right), \operatorname{nhds}\left(\frac{\operatorname{c}\left(k\right)}{j + 1}\right)\right)) \land (\exists \tau \in R, ((j + 1 \leq \tau) \land (\operatorname{q}\left(k, j, \tau\right) = 1)) \land (\forall z \in R, ((j + 1 \leq z) \land (\operatorname{q}\left(k, j, z\right) = 1)) \implies z = \tau)) \land (\exists \tau \in R, ((j + 1 \leq \tau) \land (\operatorname{q}\left(k, j, \tau\right) = 1)) \land (2j + 1 < \tau) \land (\tau < j + \frac{j + 1}{\operatorname{c}\left(k\right)}) \land (\forall t \in N, (j + 1 \leq t) \implies ((\operatorname{q}\left(k, j, t\right) < 1) \iff (t < \tau)) \land ((\operatorname{q}\left(k, j, t\right) = 1) \iff (t = \tau)) \land ((1 < \operatorname{q}\left(k, j, t\right)) \iff (\tau < t))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/SourceDensityMonotonicity.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The derivative is taken on the whole real line at each legal t, including the endpoint j+1. The reciprocal endpoint bounds follow from the logarithmic-mean kernel sandwich. Cassini's squared determinant identity links the three affine coordinates, so their logarithmic errors are estimated together.

The finite-product factor H decreases strictly to c and lies strictly between c and one on the legal half-line. Hence q(2j+1)<1 and q(j+(j+1)/c)>1. Continuity gives the crossing between these two points, and strict increase gives uniqueness and the three integer comparison equivalences for the real finite-product ratio.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/SourceDensityMonotonicity.A`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/SourceDensityMonotonicity.D`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/SourceDensityMonotonicity.E`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/SourceDensityMonotonicity.H`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/SourceDensityMonotonicity.L`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/SourceDensityMonotonicity.a`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/SourceDensityMonotonicity.b`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/SourceDensityMonotonicity.c`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/SourceDensityMonotonicity.g`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/SourceDensityMonotonicity.lowerEnvelope`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/SourceDensityMonotonicity.n`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/SourceDensityMonotonicity.q`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/SourceDensityMonotonicity.result`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/SourceDensityMonotonicity.rising`
- Dependency: [D5/S1/Scale/Fibonacci](../../../S1/Scale/Fibonacci.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/GenealogicalFiberTransport](GenealogicalFiberTransport.md)
- Dependency: [D5/S3/Divergence/MeanKernels/LogarithmicMeanSandwich](../../Divergence/MeanKernels/LogarithmicMeanSandwich.md)
