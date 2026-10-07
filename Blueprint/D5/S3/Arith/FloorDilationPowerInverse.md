# Quantitative Floor Dilation Inversion

## Abstract

A dominant first coefficient controls inversion of a floor dilation transform.

**Theorem 1.1 (Every nonnegative power scale).**

$$\forall b,f: \mathbb{N}\to \mathbb{R}, \forall a,C,T\in \mathbb{R}, (0\le a\land 0\le C\land (\forall N\in \mathbb{N}, \sum_{1< d\le N}\left|\operatorname{b}\left(d\right)\right|\le T)\land T< \left|\operatorname{b}\left(1\right)\right|\land (\forall N\in \mathbb{N}, 0< N\Rightarrow \left|\sum_{0< d\le N}\operatorname{b}\left(d\right)\cdot\operatorname{f}\left(\left\lfloor\frac{N}{d}\right\rfloor\right)\right|\le C\cdot N^{a}))\Rightarrow \forall N\in \mathbb{N}, 0< N\Rightarrow \left|\operatorname{f}\left(N\right)\right|\le \frac{C}{\left|\operatorname{b}\left(1\right)\right|-T}\cdot N^{a}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FloorDilationPowerInverse.floorSum_power_inverse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let b and f be arbitrary real sequences indexed by natural numbers. Let a, C and T be real numbers with a>=0 and C>=0. For every natural N, assume the sum of |b(d)| over 1<d<=N is at most T, and assume T<|b(1)|. For every positive natural N, assume the absolute transform sum over 0<d<=N is at most C N^a. The conclusion bounds |f(N)| by C N^a/(|b(1)|-T) at every positive natural cutoff. All powers with exponent a are real powers; N/d inside f is natural division, or floor(N/d).

The tail hypothesis at N=1 gives T>=0, so the strict gap makes the denominator and |b(1)| positive. Set K=C/(|b(1)|-T) and induct strongly on N. Splitting off d=1 leaves only 1<=floor(N/d)<N for 1<d<=N. The inductive estimate and a>=0 bound every smaller value by K N^a. The triangle inequality therefore gives |b(1)| |f(N)| <= (C+K T) N^a. The defining equation K(|b(1)|-T)=C absorbs the tail and allows cancellation of the positive head.

The theorem includes a=0 and C=0, and permits a negative first coefficient. No hypothesis on f(0) is needed, because each division argument in a positive-cutoff sum is positive. It assumes a bound on the transform rather than a global bound on its input. This is a general estimate; it does not establish a Fibonacci reconstruction identity, a Mertens growth bound, the Robin inequality, or the Riemann hypothesis.

## References

- Truth anchor: `D5/S3/Arith/FloorDilationPowerInverse.floorSum_power_inverse`
