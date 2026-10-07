# Mersenne Dyadic Cost Support Lines

## Abstract

Two affine inequalities for the classical dyadic tail cost on every Mersenne real simplex.

**Theorem 1.1 (Dyadic series bounds).**

$$\forall h: \mathbb{N}, \forall p: \operatorname{Fin}\left((2^{h} - 1)\right) \to \mathbb{R}, (\sum_{i \in \operatorname{Fin}\left((2^{h} - 1)\right)}\operatorname{p}\left(i\right) = 1 \Rightarrow (\forall d: \mathbb{N}, (0 \le \operatorname{R}\left(p, d\right) \land \operatorname{R}\left(p, d\right) \le (2^{h} - 1)) \land (\operatorname{Summable}\left(d: \mathbb{N} \mapsto \frac{\operatorname{R}\left(p, d\right)}{2^{d}}\right) \land 0 \le \operatorname{L}\left(p\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/MersenneDyadicSupportLines.simplex_data` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any real vector on Fin(2^h-1) summing to one, each residual lies between zero and 2^h-1. Geometric domination makes the residual series summable and its cost nonnegative.

**Theorem 1.2 (Individual atom bound).**

$$\forall h: \mathbb{N}, \forall p: \operatorname{Fin}\left((2^{h} - 1)\right) \to \mathbb{R}, (\sum_{i \in \operatorname{Fin}\left((2^{h} - 1)\right)}\operatorname{p}\left(i\right) = 1 \Rightarrow \forall t: \mathbb{R}, (\forall i: \operatorname{Fin}\left((2^{h} - 1)\right), t \le \operatorname{p}\left(i\right) \Rightarrow \forall i: \operatorname{Fin}\left((2^{h} - 1)\right), \operatorname{p}\left(i\right) \le 1 - ((2^{h} - 1) - 1) t))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/MersenneDyadicSupportLines.simplex_atom_upper` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If every coordinate is at least t and their sum is one, any single coordinate is at most 1-(m-1)t, where m=2^h-1.

**Theorem 1.3 (Vanishing prefix floors).**

$$\forall h: \mathbb{N}, \forall p: \operatorname{Fin}\left((2^{h} - 1)\right) \to \mathbb{R}, (\forall i: \operatorname{Fin}\left((2^{h} - 1)\right), (0 \le \operatorname{p}\left(i\right) \land 2^{h} \operatorname{p}\left(i\right) < 2) \Rightarrow \forall i: \operatorname{Fin}\left((2^{h} - 1)\right), \forall d: \mathbb{N}, (d < h \Rightarrow \operatorname{floor}\left(2^{d} \operatorname{p}\left(i\right)\right) = 0))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/MersenneDyadicSupportLines.scaling_floors` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When every coordinate is nonnegative and M times each coordinate is below two, all floors before depth h vanish.

**Theorem 1.4 (Exact high interval scaling).**

$$\forall h: \mathbb{N}, (2 \le h \Rightarrow \forall p: \operatorname{Fin}\left((2^{h} - 1)\right) \to \mathbb{R}, \forall t: \mathbb{R}, ((\sum_{i \in \operatorname{Fin}\left((2^{h} - 1)\right)}\operatorname{p}\left(i\right) = 1 \land (\forall i: \operatorname{Fin}\left((2^{h} - 1)\right), t \le \operatorname{p}\left(i\right) \land \frac{1}{2^{h}} < t)) \Rightarrow \forall q: \operatorname{Fin}\left((2^{h} - 1)\right) \to \mathbb{R}, (q = i: \operatorname{Fin}\left((2^{h} - 1)\right) \mapsto 2^{h} \operatorname{p}\left(i\right) - 1 \Rightarrow (\forall i: \operatorname{Fin}\left((2^{h} - 1)\right), 0 \le \operatorname{q}\left(i\right) \land (\sum_{i \in \operatorname{Fin}\left((2^{h} - 1)\right)}\operatorname{q}\left(i\right) = 1 \land \operatorname{L}\left(p\right) = h + \frac{\operatorname{L}\left(q\right)}{2^{h}})))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/MersenneDyadicSupportLines.scaling` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For h>=2, a vector of sum one with all coordinates at least t>1/M transforms to q(i)=Mp(i)-1, a nonnegative vector of sum one. Vanishing prefix floors and integer translation of the remaining floors give L(p)=h+L(q)/M.

**Theorem 1.5 (Both supporting lines).**

$$\forall h: \mathbb{N}, (2 \le h \Rightarrow \forall p: \operatorname{Fin}\left((2^{h} - 1)\right) \to \mathbb{R}, (((\forall i: \operatorname{Fin}\left((2^{h} - 1)\right), 0 \le \operatorname{p}\left(i\right)) \land \sum_{i \in \operatorname{Fin}\left((2^{h} - 1)\right)}\operatorname{p}\left(i\right) = 1) \Rightarrow (\operatorname{Summable}\left(d: \mathbb{N} \mapsto \frac{\operatorname{R}\left(p, d\right)}{2^{d}}\right) \land \forall t: \mathbb{R}, (t = \operatorname{min}\left(p\right) \Rightarrow (0 \le t \land (t \le \frac{1}{(2^{h} - 1)} \land ((h 2^{h} - 2) t \le \operatorname{L}\left(p\right) \land ((h + 2) 2^{h} - 2) t - 2 \le \operatorname{L}\left(p\right))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/MersenneDyadicSupportLines.mersenne_support_lines` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let h be a natural number at least two, M=2^h and m=M-1. For every nonnegative real probability vector p on Fin(m), let t be its smallest coordinate. The dyadic series L(p) is summable, 0<=t<=1/m, and (hM-2)t<=L(p) and ((h+2)M-2)t-2<=L(p). The residual R and cost L are the definitions in Dyadic Cost Support Lines. They accept arbitrary finite real vectors; an unsummable real tsum is zero. Values outside the probability simplex have no sampling-cost interpretation.

In the low interval t<=1/M, put w(i)=(p(i)-t)/(1-mt). These weights sum to one. Each scalar dyadic prefix of length h is at least t times h+(h-2)w(i). To prove this, take the first dyadic depth k with 2^k p(i)>=1, when such a depth occurs by h. The preceding k floors vanish, so their contribution is kp(i). The affine function (k-2)x+2/2^k lies below this contribution, is nonnegative at zero and one, and has values at least h/M and 2(h-1)/M at 1/M and 2/M. The inequalities 2^(h-k)>=h-k+1 verify those endpoint values. The convex decomposition p(i)=(1-Mt)w(i)+Mt(1+w(i))/M then gives the scalar bound. If no such depth occurs, the whole prefix equals hp(i). Summing the scalar bounds gives the first supporting line without logarithms.

Above t=1/M, q(i)=Mp(i)-1 is another probability vector. Every floor before depth h vanishes, and subsequent floors translate by 2^d. Consequently L(p)=h+L(q)/M. Repeatedly applying this identity to a supporting inequality with an error of size (h+3)/M^r, and letting r tend to infinity, gives the second line on the entire real simplex. The first line follows from the second in the high interval. Zero atoms and terminating dyadic expansions remain included. At h=2 the lines are 6t and 14t-2 on the three-outcome simplex.

These statements concern numerical dyadic costs. They do not assert a sampler optimization, a batch phase transition, an equality classification, or a value at every prescribed minimum atom.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/MersenneDyadicSupportLines.mersenne_support_lines`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/MersenneDyadicSupportLines.scaling`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/MersenneDyadicSupportLines.scaling_floors`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/MersenneDyadicSupportLines.simplex_atom_upper`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/MersenneDyadicSupportLines.simplex_data`
- Dependency: [D5/S3/Arith/FibonacciAtomic/DyadicSupportLines](DyadicSupportLines.md)
