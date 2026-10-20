# Hanna's ternary-digit residue theorem

## Abstract

Hanna's binomial-square generating function has the asserted residues at every coefficient.

**Definition 1.1 (The rational summand).**

$$\forall n:\mathbb{N}, \operatorname{term}\left(n\right) = ((\operatorname{PowerSeries}.\operatorname{X})^{n} \cdot ((1-2 \cdot \operatorname{PowerSeries}.\operatorname{X})^{2 \cdot n+1})^{-1} \cdot (\sum_{k\in \operatorname{Finset}.\operatorname{range}\left(n+1\right)}\operatorname{PowerSeries}.\operatorname{C}\left(((\operatorname{Nat}.\operatorname{choose}\left(n, k\right):\mathbb{Q}))^{2} \cdot (2)^{k}\right) \cdot (\operatorname{PowerSeries}.\operatorname{X})^{k}) \cdot (\sum_{k\in \operatorname{Finset}.\operatorname{range}\left(n+1\right)}\operatorname{PowerSeries}.\operatorname{C}\left(((\operatorname{Nat}.\operatorname{choose}\left(n, k\right):\mathbb{Q}))^{2} \cdot (3)^{k}\right) \cdot (\operatorname{PowerSeries}.\operatorname{X})^{k}):\operatorname{PowerSeries}\left(\mathbb{Q}\right))$$

*Formalization.* `D5/S1/Recurrence/Invariants/HannaLegendreCentralBinomialModThree.term` (`✓ std3`).

*Citation.* Paul D. Hanna (2014). *OEIS A246056 and A246423, two binomial-square generating functions*. URL: <https://oeis.org/A246056>.

*Commentary.*

OEIS A246056, unpaginated Name: "G.f.: Sum_{n>=0} x^n / (1-2*x)^(2*n+1) * [Sum_{k=0..n} C(n,k)^2 * 2^k * x^k] * [Sum_{k=0..n} C(n,k)^2 * 3^k * x^k]." The variable is the formal power-series variable and both sums include indices zero through n.

**Definition 1.2 (The generating function).**

$$A = \operatorname{PowerSeries}.\operatorname{mk}\left(\operatorname{fun} (m:\mathbb{N}) \mapsto \operatorname{PowerSeries}.\operatorname{coeff}\left(m, \sum_{n\in \operatorname{Finset}.\operatorname{range}\left(m+1\right)}\operatorname{term}\left(n\right)\right)\right)$$

*Formalization.* `D5/S1/Recurrence/Invariants/HannaLegendreCentralBinomialModThree.A` (`✓ std3`).

*Citation.* Paul D. Hanna (2014). *OEIS A246056 and A246423, two binomial-square generating functions*. URL: <https://oeis.org/A246056>.

*Commentary.*

OEIS A246056, unpaginated Name: "G.f.: Sum_{n>=0} x^n / (1-2*x)^(2*n+1) * [Sum_{k=0..n} C(n,k)^2 * 2^k * x^k] * [Sum_{k=0..n} C(n,k)^2 * 3^k * x^k]." Its coefficient at m uses n from zero through m, because term n has order at least n.

**Definition 1.3 (The residue conjecture).**

$$(claim) \Leftrightarrow (\forall n:\mathbb{N}, \exists z:\mathbb{Z}, (\operatorname{PowerSeries}.\operatorname{coeff}\left(n, A\right) = (z:\mathbb{Q})) \land (((\exists m:\mathbb{N}, (n = 2 \cdot m) \land (\neg (2\in \operatorname{Nat}.\operatorname{digits}\left(3, m\right)))) \Rightarrow (z \equiv 1 \pmod{3})) \land ((\neg (\exists m:\mathbb{N}, (n = 2 \cdot m) \land (\neg (2\in \operatorname{Nat}.\operatorname{digits}\left(3, m\right))))) \Rightarrow (z \equiv 0 \pmod{3}))))$$

*Formalization.* `D5/S1/Recurrence/Invariants/HannaLegendreCentralBinomialModThree.claim` (`✓ std3`).

*Citation.* Paul D. Hanna (2014). *OEIS A246056 and A246423, two binomial-square generating functions*. URL: <https://oeis.org/A246056>.

*Commentary.*

OEIS A246056, unpaginated Comments: "Conjecture: a(n) == 1 (mod 3) when n = 2*A005836(k) for k >= 0, and a(n) == 0 (mod 3) otherwise, where A005836 gives numbers whose base-3 representation contains no 2." The letter n ranges over all natural indices and z is the integer equal to the rational coefficient. Zero has an empty digit list and is included.

**Theorem 1.4 (The conjecture holds).**

$$\forall n:\mathbb{N}, \exists z:\mathbb{Z}, (\operatorname{PowerSeries}.\operatorname{coeff}\left(n, A\right) = (z:\mathbb{Q})) \land (((\exists m:\mathbb{N}, (n = 2 \cdot m) \land (\neg (2\in \operatorname{Nat}.\operatorname{digits}\left(3, m\right)))) \Rightarrow (z \equiv 1 \pmod{3})) \land ((\neg (\exists m:\mathbb{N}, (n = 2 \cdot m) \land (\neg (2\in \operatorname{Nat}.\operatorname{digits}\left(3, m\right))))) \Rightarrow (z \equiv 0 \pmod{3})))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/HannaLegendreCentralBinomialModThree.result` (`✓ std3`). ∎

*Resolves.* `Problems/hanna-a246056-a246423-legendre-central-binomial` (proved) by `D5/S1/Recurrence/Invariants/HannaLegendreCentralBinomialModThree.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hanna-a246056-a246423-legendre-central-binomial","declaration_gid":"D5/S1/Recurrence/Invariants/HannaLegendreCentralBinomialModThree.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2014). *OEIS A246056 and A246423, two binomial-square generating functions*. URL: <https://oeis.org/A246056>.

*Commentary.*

The integer lift allows coefficientwise reduction. The alternating binomial-square transform and Lucas recurrence identify the ternary support and its signed residue.

## References

- Truth anchor: `D5/S1/Recurrence/Invariants/HannaLegendreCentralBinomialModThree.A`
- Truth anchor: `D5/S1/Recurrence/Invariants/HannaLegendreCentralBinomialModThree.claim`
- Truth anchor: `D5/S1/Recurrence/Invariants/HannaLegendreCentralBinomialModThree.result`
- Truth anchor: `D5/S1/Recurrence/Invariants/HannaLegendreCentralBinomialModThree.term`
- Dependency: [D5/S1/Recurrence/Invariants/HannaLegendreCentralBinomialTransform](HannaLegendreCentralBinomialTransform.md)
