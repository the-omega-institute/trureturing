# Fibonacci Sampling and the Coarse Time Quotient

## Abstract

Finite Fibonacci samples determine exactly the coarse time observations; a nonzero sampling kernel prevents an autonomous one-step update.

**Theorem 1.1 (Coarse time equivalence and the one-step obstruction).**

$$(\forall x, \forall j, \operatorname{u}\left(j + 2, x\right) = L \cdot \operatorname{u}\left(j + 1, x\right) - (-1)^{g} \cdot \operatorname{u}\left(j, x\right)) \land (\forall z, ((\operatorname{O}\left(z\right) = 0) \iff ((\operatorname{r}\left(s, z\right) = 0) \land (\operatorname{r}\left(s + g, z\right) = 0))) \land ((\operatorname{O}\left(z\right) = 0) \iff ((\operatorname{snd}\left(\operatorname{iterate}\left(S, s, z\right)\right) = 0) \land (\operatorname{fib}\left(g\right) \cdot \operatorname{fst}\left(\operatorname{iterate}\left(S, s, z\right)\right) = 0)))) \land (\forall x, \forall y, (\operatorname{O}\left(x\right) = \operatorname{O}\left(y\right)) \iff (\forall j, \operatorname{u}\left(j, x\right) = \operatorname{u}\left(j, y\right))) \land (\forall Phi, (\forall x, \operatorname{O}\left(\operatorname{S}\left(x\right)\right) = \operatorname{Phi}\left(\operatorname{O}\left(x\right)\right)) \implies \forall z, \operatorname{O}\left(z\right) = 0 \implies \operatorname{O}\left(\operatorname{S}\left(z\right)\right) = 0) \land (\operatorname{Injective}\left(x \mapsto (\operatorname{r}\left(s, x\right),\operatorname{r}\left(s + 1, x\right))\right)) \land (\operatorname{det}\left(\operatorname{adjacentRows}\left(s\right)\right) = (-1)^{s + 1}) \land ((\exists z, (z \neq 0) \land (\operatorname{O}\left(z\right) = 0)) \implies \neg(\exists Phi, \forall x, \operatorname{O}\left(\operatorname{S}\left(x\right)\right) = \operatorname{Phi}\left(\operatorname{O}\left(x\right)\right))) \land ((M3^{4} = 2 \cdot I) \land (\forall j, \forall x, \operatorname{r3}\left(4 \cdot j, x\right) = 2^{j} \cdot \operatorname{snd}\left(x\right)) \land (\forall j, \forall x, (\operatorname{r3}\left(8 \cdot j, x\right) = \operatorname{snd}\left(x\right)) \land (\operatorname{r3}\left(8 \cdot j + 4, x\right) = 2 \cdot \operatorname{snd}\left(x\right))) \land (\forall j, \operatorname{r3}\left(4 \cdot j, \operatorname{pair}\left(0, 0\right)\right) = \operatorname{r3}\left(4 \cdot j, \operatorname{pair}\left(1, 0\right)\right)) \land (\operatorname{r3}\left(1, \operatorname{pair}\left(0, 0\right)\right) = 0) \land (\operatorname{r3}\left(1, \operatorname{pair}\left(1, 0\right)\right) = 1) \land (0 \neq 1) \land (\exists Psi, \forall x, \operatorname{O4}\left(\operatorname{iterate}\left(S, 4, x\right)\right) = \operatorname{Psi}\left(\operatorname{O4}\left(x\right)\right)) \land (\neg(\exists Phi, \forall x, \operatorname{O4}\left(\operatorname{iterate}\left(S, 1, x\right)\right) = \operatorname{Phi}\left(\operatorname{O4}\left(x\right)\right))) \land (\neg((\exists Psi, \forall x, \operatorname{O4}\left(\operatorname{iterate}\left(S, 4, x\right)\right) = \operatorname{Psi}\left(\operatorname{O4}\left(x\right)\right)) \implies (\exists Phi, \forall x, \operatorname{O4}\left(\operatorname{iterate}\left(S, 1, x\right)\right) = \operatorname{Phi}\left(\operatorname{O4}\left(x\right)\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/SamplingQuotient.sampling_quotient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let n be a positive natural number, including n=1, and let m be at least two. The time family t : Fin(m) -> N is strictly increasing. Set s=t(0), g=gcd(t(i)-s : i is nonzero), and O(x)(i)=r(t(i),x). All states x=(a,b) belong to (Z/nZ)^2 and r(k,x)=F(k)a+F(k+1)b, where F(0)=0 and F(1)=1. The step S(a,b)=(b,a+b) has matrix M=[[0,1],[1,1]]. Every occurrence of a time observation refers to this same state and keeps its time label. In the displayed formula, adjacentRows(s) has rows (F(s),F(s+1)) and (F(s+1),F(s+2)); M3 and r3 denote M and r over Z/3Z, and I is the identity matrix.

Write u(j,x)=r(s+jg,x) and L=trace(M^g). For every natural j and every x, u(j+2,x)=L*u(j+1,x)-(-1)^g*u(j,x). The kernel of O equals the joint kernel of r(s,-) and r(s+g,-). In the shifted coordinates (a',b')=S^s(z), it is exactly b'=0 and F(g)*a'=0. Consequently O(x)=O(y) if and only if u(j,x)=u(j,y) for all natural j. The first two coarse readings therefore determine the entire coarse sequence.

For every function Phi on the sample space, the identity O(S(x))=Phi(O(x)) for all states implies that O(z)=0 entails O(S(z))=0. The pair x -> (r(s,x),r(s+1,x)) is injective: its matrix has determinant (-1)^(s+1). Thus a state in a stable sampling kernel must be zero. If any nonzero state lies in the sampling kernel, there is no such Phi, even without a linearity assumption on Phi.

Over Z/3Z, M^4=2I and r(4j,x)=2^j*b for every natural j. In particular r(8j,x)=b and r(8j+4,x)=2b. The states (0,0) and (1,0) agree at every time 4j, but their time-one readings are respectively 0 and 1, which are distinct.

For this modulus define O4(x)=(r(0,x),r(4,x)). There exists a function Psi with O4(S^4(x))=Psi(O4(x)) for every x; multiplication of both sample coordinates by 2 gives one. There is no function Phi with O4(S(x))=Phi(O4(x)) for all x. The theorem explicitly negates the implication from the existence of the four-step update to the existence of the one-step update: in this example the coarse sample closes under the four-step clock but not under the one-step clock.

Cayley-Hamilton gives the coarse recurrence. Fibonacci divisibility places the two-reading kernel inside the sampling kernel. Their equal finite cardinalities, both gcd(n,F(g)), give equality. Applying that equality to differences yields the coarse observation equivalence. The invertible Fibonacci step gives adjacent-reading injectivity and the obstruction to a one-step update.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/SamplingQuotient.sampling_quotient`
- Dependency: [D5/S1/Recurrence/FiniteSamplingSmithDefect](../../../S1/Recurrence/FiniteSamplingSmithDefect.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/TimeSampling](TimeSampling.md)
