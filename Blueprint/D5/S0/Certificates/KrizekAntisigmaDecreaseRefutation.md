# The OEIS A231548 Antisigma Gap-Three Conjecture

## Abstract

At n = 332640, antisigma decreases across a gap of three.

**Definition 1.1 (The antisigma function).**

$$\forall n \in \mathrm{Nat},\; \operatorname{antisigma}\left(n\right): \mathrm{Nat} = \sum_{d \in Finset.filter\left(Finset.Icc\left(1, n\right), (\lambda d \mapsto \neg d \mid n)\right)} d$$

*Formalization.* `D5/S0/Certificates/KrizekAntisigmaDecreaseRefutation.antisigma` (`✓ std3`).

*Citation.* Jaroslav Krizek (2013). *OEIS A231548, Numbers n such that 2*n - 1 < sigma(n) - sigma(n-2)*. URL: <https://oeis.org/A231548>.

*Commentary.*

For each natural n, the finite interval contains the integers from one through n. The filter retains exactly those d that do not divide n, and the outer sum adds the retained values.

**Definition 1.2 (Krizek's gap-three conjecture).**

$$(claim) \Leftrightarrow (\forall n \in \mathrm{Nat},\; 3 \le n \Rightarrow \operatorname{antisigma}\left(n - 3\right) \le \operatorname{antisigma}\left(n\right))$$

*Formalization.* `D5/S0/Certificates/KrizekAntisigmaDecreaseRefutation.claim` (`✓ std3`).

*Citation.* Jaroslav Krizek (2013). *OEIS A231548, Numbers n such that 2*n - 1 < sigma(n) - sigma(n-2)*. URL: <https://oeis.org/A231548>.

*Commentary.*

For every natural n at least three, the conjecture says that antisigma at n minus three is at most antisigma at n.

**Theorem 1.3 (The conjecture fails at n = 332640).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/KrizekAntisigmaDecreaseRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a231548-antisigma-decrease-refutation` (refuted) by `D5/S0/Certificates/KrizekAntisigmaDecreaseRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a231548-antisigma-decrease-refutation","declaration_gid":"D5/S0/Certificates/KrizekAntisigmaDecreaseRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Jaroslav Krizek (2013). *OEIS A231548, Numbers n such that 2*n - 1 < sigma(n) - sigma(n-2)*. URL: <https://oeis.org/A231548>.

*Commentary.*

At n = 332640, the divisor sums are sigma(332640) = 1451520 and sigma(332637) = 443520. The complement identity gives antisigma(332640) = 55323399600 and antisigma(332637) = 55323409683. The first value is smaller, so the universal gap-three inequality is false.

## References

- Truth anchor: `D5/S0/Certificates/KrizekAntisigmaDecreaseRefutation.antisigma`
- Truth anchor: `D5/S0/Certificates/KrizekAntisigmaDecreaseRefutation.claim`
- Truth anchor: `D5/S0/Certificates/KrizekAntisigmaDecreaseRefutation.result`
