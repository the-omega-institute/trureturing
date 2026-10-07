# Mersenne Dyadic Equality Laws

## Abstract

Equality cases of both affine dyadic-cost bounds on Mersenne probability simplices.

**Theorem 1.1 (Both equality classifications).**

$$\forall h: \mathbb{N}, (2 \le h \Rightarrow \forall p: \operatorname{Fin}\left((2^{h} - 1)\right) \to \mathbb{R}, (((\forall i: \operatorname{Fin}\left((2^{h} - 1)\right), 0 \le \operatorname{p}\left(i\right)) \land \sum_{i \in \operatorname{Fin}\left((2^{h} - 1)\right)}\operatorname{p}\left(i\right) = 1) \Rightarrow \forall t: \mathbb{R}, (t = \operatorname{min}\left(p\right) \Rightarrow ((\operatorname{L}\left(p\right) = (h 2^{h} - 2) t \Leftrightarrow \exists j: \operatorname{Fin}\left((2^{h} - 1)\right), (p = \operatorname{delta}\left(j\right) \lor p = \operatorname{v}\left(j\right))) \land (\operatorname{L}\left(p\right) = ((h + 2) 2^{h} - 2) t - 2 \Leftrightarrow (p = u \lor \exists r: \mathbb{N}, \exists j: \operatorname{Fin}\left((2^{h} - 1)\right), p = \operatorname{s}\left(r, j\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/MersenneDyadicEqualityLaws.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix a natural number h>=2, M=2^h and m=M-1. Let p be any nonnegative real probability vector on Fin(m), and let t be its smallest coordinate. L is the dyadic cost defined in Dyadic Cost Support Lines: the sum over d>=0 of (2^d-sum_i floor(2^d p(i)))/2^d. Put a=hM-2 and b=(h+2)M-2. The point law delta(j) has coordinate one at j and zero elsewhere; v(j)(i)=(1+delta(j)(i))/M. The uniform law u has all coordinates 1/m. For a natural number r and an index j, define s(r,j)(j) as 1/m+(M-2)/(m M^(r+1)), and every other coordinate as 1/m-1/(m M^(r+1)).

The first support equality L(p)=a t holds exactly for a point law or a biased law v(j). The second support equality L(p)=b t-2 holds exactly for u or one of the finite staircase laws s(r,j). Both directions hold for every real probability vector, including zero atoms and terminating dyadic expansions. At r=0 the staircase law equals v(j).

The dyadic cost bounds Shannon entropy. For a positive coordinate x, choose the first depth k with 2^k x>=1. Earlier floors vanish, so its dyadic series is at least kx; monotonicity of the logarithm gives -x log(x)/log(2)<=kx. Summation gives the entropy bound, with zero coordinates contributing zero. When 0<t<=1/M, put w(i)=(p(i)-t)/(1-mt) and c=Mt. The law p is the convex combination of delta(j) and v(j) with respective weights (1-c)w(j) and c w(j). Strict concavity of -x log(x), applied in each coordinate, forces c=1 and all active biased vertices to coincide if the first support equality holds. At t=0, zero cost forces a point law. Above 1/M the second support line is strictly stronger than the first.

For a high-interval law set q(i)=Mp(i)-1. Its coordinates are nonnegative and sum to one, and L(p)=h+L(q)/M. The second support defect is divided by M under the inverse transformation. If p is nonuniform, its distance from the uniform law grows by M under each forward transformation, so a finite first exit from the high interval exists. At exit the two support inequalities force the minimum coordinate to equal 1/M; the first equality classification then yields v(j). Inverting the finite sequence gives precisely s(r,j). For the reverse implication, the explicit biased cost and the same scaling identity prove every staircase equality by induction. The uniform law is a fixed point and has cost hM/m.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/MersenneDyadicEqualityLaws.result`
- Dependency: [D5/S3/Arith/FibonacciAtomic/MersenneDyadicSupportLines](MersenneDyadicSupportLines.md)
