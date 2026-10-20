# Hanna's power-of-two residue theorem

## Abstract

Hanna's binomial-square generating function has the asserted residues at every coefficient.

**Definition 1.1 (The rational summand).**

$$\forall n:\mathbb{N}, \operatorname{term}\left(n\right) = ((\operatorname{PowerSeries}.\operatorname{X})^{n} \cdot ((1-3 \cdot \operatorname{PowerSeries}.\operatorname{X})^{2 \cdot n+1})^{-1} \cdot (\sum_{k\in \operatorname{Finset}.\operatorname{range}\left(n+1\right)}\operatorname{PowerSeries}.\operatorname{C}\left(((\operatorname{Nat}.\operatorname{choose}\left(n, k\right):\mathbb{Q}))^{2} \cdot (2)^{k}\right) \cdot (\operatorname{PowerSeries}.\operatorname{X})^{k}) \cdot (\sum_{k\in \operatorname{Finset}.\operatorname{range}\left(n+1\right)}\operatorname{PowerSeries}.\operatorname{C}\left(((\operatorname{Nat}.\operatorname{choose}\left(n, k\right):\mathbb{Q}))^{2} \cdot (3)^{k}\right) \cdot (\operatorname{PowerSeries}.\operatorname{X})^{k}):\operatorname{PowerSeries}\left(\mathbb{Q}\right))$$

*Formalization.* `D5/S1/Recurrence/Invariants/HannaLegendreCentralBinomialModFour.term` (`✓ std3`).

*Citation.* Paul D. Hanna (2014). *OEIS A246056 and A246423, two binomial-square generating functions*. URL: <https://oeis.org/A246056>.

*Commentary.*

OEIS A246423, unpaginated Name: "G.f.: Sum_{n>=0} x^n / (1-3*x)^(2*n+1) * [Sum_{k=0..n} C(n,k)^2 * 2^k * x^k] * [Sum_{k=0..n} C(n,k)^2 * 3^k * x^k]." The variable is the formal power-series variable and both sums include indices zero through n.

**Definition 1.2 (The generating function).**

$$A = \operatorname{PowerSeries}.\operatorname{mk}\left(\operatorname{fun} (m:\mathbb{N}) \mapsto \operatorname{PowerSeries}.\operatorname{coeff}\left(m, \sum_{n\in \operatorname{Finset}.\operatorname{range}\left(m+1\right)}\operatorname{term}\left(n\right)\right)\right)$$

*Formalization.* `D5/S1/Recurrence/Invariants/HannaLegendreCentralBinomialModFour.A` (`✓ std3`).

*Citation.* Paul D. Hanna (2014). *OEIS A246056 and A246423, two binomial-square generating functions*. URL: <https://oeis.org/A246056>.

*Commentary.*

OEIS A246423, unpaginated Name: "G.f.: Sum_{n>=0} x^n / (1-3*x)^(2*n+1) * [Sum_{k=0..n} C(n,k)^2 * 2^k * x^k] * [Sum_{k=0..n} C(n,k)^2 * 3^k * x^k]." Its coefficient at m uses n from zero through m, because term n has order at least n.

**Definition 1.3 (The residue conjecture).**

$$(claim) \Leftrightarrow ((\operatorname{PowerSeries}.\operatorname{coeff}\left(0, A\right) = 1) \land (\forall n:\mathbb{N}, (0<n) \Rightarrow (\exists z:\mathbb{Z}, (\operatorname{PowerSeries}.\operatorname{coeff}\left(n, A\right) = (z:\mathbb{Q})) \land (((z \equiv 2 \pmod{4}) \Leftrightarrow (\exists k:\mathbb{N}, (2\leq k) \land (n = (2)^{k}))) \land ((\neg (\exists k:\mathbb{N}, (2\leq k) \land (n = (2)^{k}))) \Rightarrow (z \equiv 0 \pmod{4}))))))$$

*Formalization.* `D5/S1/Recurrence/Invariants/HannaLegendreCentralBinomialModFour.claim` (`✓ std3`).

*Citation.* Paul D. Hanna (2014). *OEIS A246056 and A246423, two binomial-square generating functions*. URL: <https://oeis.org/A246056>.

*Commentary.*

OEIS A246423, unpaginated Comments: "a(n) == 2 (mod 4) iff n = 2^k for k>=2, and a(n) == 0 (mod 4) elsewhere except at a(0)=1 (conjecture)." The letter n ranges over all natural indices and z is the integer equal to the rational coefficient. The constant coefficient is one and the residue assertion begins at n positive.

**Theorem 1.4 (The conjecture holds).**

$$(\operatorname{PowerSeries}.\operatorname{coeff}\left(0, A\right) = 1) \land (\forall n:\mathbb{N}, (0<n) \Rightarrow (\exists z:\mathbb{Z}, (\operatorname{PowerSeries}.\operatorname{coeff}\left(n, A\right) = (z:\mathbb{Q})) \land (((z \equiv 2 \pmod{4}) \Leftrightarrow (\exists k:\mathbb{N}, (2\leq k) \land (n = (2)^{k}))) \land ((\neg (\exists k:\mathbb{N}, (2\leq k) \land (n = (2)^{k}))) \Rightarrow (z \equiv 0 \pmod{4})))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/HannaLegendreCentralBinomialModFour.result` (`✓ std3`). ∎

*Resolves.* `Problems/hanna-a246423-legendre-central-binomial` (proved) by `D5/S1/Recurrence/Invariants/HannaLegendreCentralBinomialModFour.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hanna-a246423-legendre-central-binomial","declaration_gid":"D5/S1/Recurrence/Invariants/HannaLegendreCentralBinomialModFour.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2014). *OEIS A246056 and A246423, two binomial-square generating functions*. URL: <https://oeis.org/A246056>.

*Commentary.*

The integer lift allows coefficientwise reduction. The alternating transform plus twice its first moment reduces to powers of two; the first-moment term cancels the degree-two residue.

## References

- Truth anchor: `D5/S1/Recurrence/Invariants/HannaLegendreCentralBinomialModFour.A`
- Truth anchor: `D5/S1/Recurrence/Invariants/HannaLegendreCentralBinomialModFour.claim`
- Truth anchor: `D5/S1/Recurrence/Invariants/HannaLegendreCentralBinomialModFour.result`
- Truth anchor: `D5/S1/Recurrence/Invariants/HannaLegendreCentralBinomialModFour.term`
- Dependency: [D5/S1/Recurrence/Invariants/HannaLegendreCentralBinomialTransform](HannaLegendreCentralBinomialTransform.md)
