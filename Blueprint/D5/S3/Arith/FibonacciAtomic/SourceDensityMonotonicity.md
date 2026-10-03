# Definitions of Fibonacci Source Density Ratios

## Abstract

Shared definitions for the real finite-product extension of Fibonacci source density ratios.

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

D(k)=F(3k).

**Definition 1.4 (Total composition coefficient).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/SourceDensityMonotonicity.L`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/SourceDensityMonotonicity.L` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

L(k)=F(3k+1).

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
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/SourceDensityMonotonicity.rising`
