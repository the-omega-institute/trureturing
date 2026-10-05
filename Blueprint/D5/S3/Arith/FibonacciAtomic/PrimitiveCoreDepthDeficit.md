# Primitive Composition Cores and Depth Deficits

## Abstract

Unique nonnegative exit cores relate the golden norm to Fibonacci depth.

**Theorem 1.1 (The unique exit core and its logarithmic bounds).**

$$\begin{aligned}\forall x\in\mathbb{N}^{2},x\neq(0,0)\land \operatorname{gcd}\left(x_{1}, x_{2}\right)=1\Rightarrow\\\exists j\in\mathbb{N},r,s\in\mathbb{N},r>s\ge0,x=\operatorname{iterate}\left(M, j, (r,s)\right)\\\forall k\in\mathbb{N},u,v\in\mathbb{N},u>v\ge0\land x=\operatorname{iterate}\left(M, k, (u,v)\right)\Rightarrow k=j\land u=r\land v=s\\\operatorname{gcd}\left(r, s\right)=1,D=\operatorname{abs}\left(\operatorname{Q}\left(x\right)\right)=r^{2}+r\cdot s-s^{2}\\\frac{\operatorname{log}\left(D\right)-\operatorname{log}\left(\frac{5}{4}\right)}{2\cdot \operatorname{log}\left(phi\right)}+1\le\operatorname{L}\left(x\right)\le\frac{\operatorname{log}\left(D\right)}{2\cdot \operatorname{log}\left(phi\right)}+4\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/PrimitiveCoreDepthDeficit.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every nonzero pair x=(a,b) of natural numbers with gcd(a,b)=1, there is a unique natural depth j and natural core c=(r,s) with r>s and x=M^j(c). Here M(a,b)=(b,a+b) and q(a,b)=2a+3b are the Fibonacci step and quantity. The norm Q(x) is the golden integer norm of a+b phi: a^2+ab-b^2. The core is primitive, and D=abs(Q(x))=r^2+rs-s^2.

The depth deficit L(x)=log(q(x))/log(phi)-j uses the natural real logarithm and phi=(1+sqrt(5))/2. Both displayed bounds concern this same pair, core, depth and norm. They hold for every nonzero primitive nonnegative composition, including pairs with a zero coordinate.

When b>=a, the inverse step (b-a,a) is nonnegative and decreases q by a+b. It therefore reaches the exit section r>s. The forward step is injective, and every positive-length forward image has its second coordinate at least its first. Cancelling a common iterate proves uniqueness. Each step preserves the gcd and reverses the sign of the golden norm.

The identities D-r^2=s(r-s) and 5r^2-4D=(r-2s)^2 give r^2<=D<=(5/4)r^2. The quantity along the orbit is r F_(j+3)+s F_(j+4). Since 0<=s<r, it lies between r F_(j+3) and r F_(j+5). The standard Fibonacci and golden-ratio identity gives phi^n<=F_(n+2)<=phi^(n+1), so the quantity lies between r phi^(j+1) and r phi^(j+4). Taking logarithms and dividing by the positive log(phi) yields the deficit bounds.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/PrimitiveCoreDepthDeficit.result`
- Dependency: [D5/S0/Carrier/Norm](../../../S0/Carrier/Norm.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/GlobalGcdSampling](GlobalGcdSampling.md)
- Dependency: [D5/S3/Axis/AxisConvergence](../../Axis/AxisConvergence.md)
