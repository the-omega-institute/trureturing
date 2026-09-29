# Singleton-or-constant query capacity

## Abstract

Adaptive singleton-or-constant binary questions identify at most d+1 sources at depth d.

**Theorem 1.1 (Linear capacity for exact adaptive identification).**

$$\begin{gathered}\forall X: \operatorname{Type}, [\operatorname{Fintype}(X)], d: \mathbb{N}, p: \operatorname{BinaryProtocol}(X, d),\\{}\operatorname{Injective}(T) \land [\forall t: \operatorname{Fin}(d), \forall h: (\operatorname{Fin}(\operatorname{val}(t)) \to \operatorname{Bool}),\\{}(\exists b: \operatorname{Bool}, \forall x: X, \operatorname{q}(t, h, x)=b) \lor \operatorname{card}(\{x: X \mid \operatorname{q}(t, h, x)=\operatorname{true}\}) \leq 1]\\{}\implies \operatorname{card}(X) \leq d+1.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/SingletonQueryCapacity.singleton_or_constant_query_capacity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let X be any finite source type and let p be a BinaryProtocol of depth d. Write T for its transcript and q(t,h,x) for its question at round t, history h and source x. Transcript consistency means that the t-th bit of T(x) equals q(t,T(x) restricted to earlier rounds,x).

Assume T is injective. Every question, at every history including unrealized histories, is either constant on X or true at at most one source. Both constant false and constant true are permitted.

After t rounds, retain a set of sources sharing one transcript prefix and having size at least the size of X minus t. A constant answer keeps the entire set. For a question with at most one true source, keeping the false answers removes at most one member. Transcript consistency extends the common prefix. At depth d, injectivity leaves at most one member, giving the stated bound.

No nonemptiness or positive-depth assumption is imposed. Repeated constant YES answers are allowed; the last remaining candidate can be inferred without an additional question. The questions may depend on the complete previous history, and no prior source information is supplied.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/SingletonQueryCapacity.singleton_or_constant_query_capacity`
- Dependency: [D5/S3/ConceptDynamics/Coding/FiberBinaryIdentification](FiberBinaryIdentification.md)
