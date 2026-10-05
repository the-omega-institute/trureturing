# Nearest Strict Dyadic Ceilings of Optimal Laws

## Abstract

Every larger atom of an attaining real law is the first strictly higher grid point at its least binary depth.

**Theorem 1.1 (Strict ceiling at the least terminating depth).**

$$(\forall m: \mathbb{N}, (\forall p: \operatorname{Fin}\left(m\right) \to \mathbb{R}, ((2 \le m \land (\forall a: \operatorname{Fin}\left(m\right), 0 < \operatorname{p}\left(a\right)) \land \sum_{a \in \operatorname{Fin}\left(m\right)}\operatorname{p}\left(a\right) = 1 \land \operatorname{cost}\left(p\right) = \operatorname{alpha}\left(m\right) \cdot \operatorname{inf}\left(\operatorname{range}\left(p\right)\right)) \to (\forall i: \operatorname{Fin}\left(m\right), (\operatorname{inf}\left(\operatorname{range}\left(p\right)\right) < \operatorname{p}\left(i\right) \to \operatorname{p}\left(i\right) = \frac{\lfloor2^{D_{i}} \cdot \operatorname{inf}\left(\operatorname{range}\left(p\right)\right)\rfloor + 1}{2^{D_{i}}})))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/OptimalLawNearestStrictCeiling.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The law p is strictly positive and normalized on m labels, with m at least two. Its least mass t is the infimum of its finite range. The dyadic cost divided by t attains the full real infimum alpha(m). For each p(i)>t, D_i is the least natural D for which p(i)=N/2^D for some natural N. Termination supplies this least depth; the Lean statement selects it by Nat.find. The numerator is floor(2^D_i*t)+1, even when 2^D_i*t is an integer.

Suppose a larger atom violates the formula and choose such an atom j whose least depth d is maximal. Put delta=2^(-d), k=floor(2^d*t), and Q=(k+1)*delta. Let S contain exactly the labels with mass below Q and n be its cardinality. It contains a minimum label and excludes j, so 1<=n<m. Every atom outside S lies on the depth-d grid: an atom of greater least depth obeys its own strict-ceiling formula and would lie at or below Q, while equality would contradict its least depth.

Atoms inside S have depth-d integer part k. The sum of their fractional parts is an integer R, because the total scaled mass and all outside masses are integers. With f the fractional part of 2^d*t, one has n*f<=R<=n-1. Consequently Q-t>=delta/n. The donor is at least Q+delta, and its least depth implies an odd terminal numerator, so removing delta changes none of its shallower floor counts.

Choose an attaining n-label law q with minimum u. Normalization gives u<=1/n. Transfer delta from j to S in the proportions q, obtaining a positive normalized law P with every mass at least t+delta*u. The shared dyadic transfer bound gives cost(P)<=alpha(m)*t+delta*alpha(n)*u. Strict growth alpha(n)<alpha(m) makes this less than alpha(m)*(t+delta*u), contradicting the optimal lower bound for P. Thus every larger atom satisfies the displayed strict-ceiling formula.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/OptimalLawNearestStrictCeiling.result`
- Dependency: [D5/S3/Arith/FibonacciAtomic/OptimalLawLargerAtomsTerminate](OptimalLawLargerAtomsTerminate.md)
