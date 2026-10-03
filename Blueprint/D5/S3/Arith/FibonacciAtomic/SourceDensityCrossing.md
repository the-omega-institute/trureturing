# Real Extension of Fibonacci Source Density Ratios

## Abstract

Each real finite-product ratio increases strictly and crosses one at a unique bounded point.

F denotes the natural Fibonacci sequence with F(0)=0 and F(1)=1. Fix natural k>=1 and j. Put d=3k. Nonintegral t is an auxiliary real parameter of finite products; it does not represent a nonintegral number of tree leaves. E,A,D,L,a,b,n,H,q,c,g and lowerEnvelope are the real extension defined in SourceDensityMonotonicity.

**Definition 1.1 (Composition count ratio).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/SourceDensityCrossing.sourceDensity`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/SourceDensityCrossing.sourceDensity` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

sourceDensity(k,t,i) is the ratio of fiberCount(t-i,i) to fiberCount(step iterated 3k times on (t-i,i)). The subtraction is natural subtraction.

**Definition 1.2 (Crossing and integer bridge).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/SourceDensityCrossing.Conclusion`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/SourceDensityCrossing.Conclusion` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Conclusion(k,j) asserts positivity of c, strict increase, the asymptotic slope, the unique crossing with its bounds and integer comparisons, and equality with the adjacent sourceDensity ratio at every legal integer. Both the finite-product and actual count ratios satisfy the three comparison equivalences.

In the displayed statement, logQ(k,j) denotes the function t maps to log(q(k,j,t)), and qOverT(k,j) denotes t maps to q(k,j,t)/t. R and N denote the real numbers and natural numbers.

**Theorem 1.3 (Strict increase and unique crossing).**

$$\forall k,j \in N, (1 \leq k) \implies (0 < \operatorname{c}\left(k\right)) \land (\forall t \in R, (j + 1 \leq t) \implies (0 < \operatorname{q}\left(k, j, t\right)) \land (\operatorname{HasDerivAt}\left(\operatorname{logQ}\left(k, j\right), \operatorname{g}\left(k, j, t\right), t\right)) \land (\operatorname{lowerEnvelope}\left(k, j, t\right) \leq \operatorname{g}\left(k, j, t\right))) \land (\operatorname{StrictMonoOn}\left(\operatorname{q}\left(k, j\right), \operatorname{Ici}\left(j + 1\right)\right)) \land (\operatorname{Tendsto}\left(\operatorname{qOverT}\left(k, j\right), \operatorname{atTop}\left(\right), \operatorname{nhds}\left(\frac{\operatorname{c}\left(k\right)}{j + 1}\right)\right)) \land (\exists \tau \in R, ((j + 1 \leq \tau) \land (\operatorname{q}\left(k, j, \tau\right) = 1)) \land (\forall z \in R, ((j + 1 \leq z) \land (\operatorname{q}\left(k, j, z\right) = 1)) \implies z = \tau)) \land (\exists \tau \in R, ((j + 1 \leq \tau) \land (\operatorname{q}\left(k, j, \tau\right) = 1)) \land (2j + 1 < \tau) \land (\tau < j + \frac{j + 1}{\operatorname{c}\left(k\right)}) \land (\forall t \in N, (j + 1 \leq t) \implies ((\operatorname{q}\left(k, j, t\right) < 1) \iff (t < \tau)) \land ((\operatorname{q}\left(k, j, t\right) = 1) \iff (t = \tau)) \land ((1 < \operatorname{q}\left(k, j, t\right)) \iff (\tau < t)) \land ((\frac{\operatorname{sourceDensity}\left(k, t, j + 1\right)}{\operatorname{sourceDensity}\left(k, t, j\right)} < 1) \iff (t < \tau)) \land ((\frac{\operatorname{sourceDensity}\left(k, t, j + 1\right)}{\operatorname{sourceDensity}\left(k, t, j\right)} = 1) \iff (t = \tau)) \land ((1 < \frac{\operatorname{sourceDensity}\left(k, t, j + 1\right)}{\operatorname{sourceDensity}\left(k, t, j\right)}) \iff (\tau < t)))) \land (\forall t \in N, (j + 1 \leq t) \implies \operatorname{q}\left(k, j, t\right) = \frac{\operatorname{sourceDensity}\left(k, t, j + 1\right)}{\operatorname{sourceDensity}\left(k, t, j\right)})$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/SourceDensityCrossing.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The derivative is taken on the whole real line at each legal t, including the endpoint j+1. The reciprocal endpoint bounds follow from the logarithmic-mean kernel sandwich. Cassini's squared determinant identity links the three affine coordinates, so their logarithmic errors are estimated together.

The finite-product factor H decreases strictly to c and lies strictly between c and one on the legal half-line. Hence q(2j+1)<1 and q(j+(j+1)/c)>1. Continuity gives the crossing between these two points, and strict increase gives uniqueness and the three integer comparison equivalences for the real finite-product ratio and actual density ratio. For i=j or j+1 at a legal integer t, the iterated Fibonacci step has coordinates (At+Ei,Dt+Ai). The Catalan and binomial factorial identities give the adjacent fiber-count ratio. Pairing consecutive factors in rising(2n-1,2D)=4^D rising(n-1/2,D) rising(n,D) then gives the integer bridge.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/SourceDensityCrossing.Conclusion`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/SourceDensityCrossing.result`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/SourceDensityCrossing.sourceDensity`
- Dependency: [D5/S3/Arith/FibonacciAtomic/SourceDensityMonotonicity](SourceDensityMonotonicity.md)
