# Two-Odd-Prime Uncovered Density

## Abstract

Congruence classes with distinct nontrivial moduli supported on two odd primes leave a positive density of residue classes uncovered.

**Theorem 1.1 (At least one eighth of the residues remain uncovered).**

$$\begin{aligned}\forall p, q \in \mathbb{N},\\(\left(\left(\left(Prime\left(p\right) \land Prime\left(q\right)\right) \land Odd\left(p\right)\right) \land Odd\left(q\right)\right) \land p \ne q) \Rightarrow\\\forall A, B \in \mathbb{N}, D \in Finset\left(\mathbb{N}\right),\\\forall a: \mathbb{N} \to \mathbb{N},\\(\forall d \in \mathbb{N},\; d \in D \Rightarrow \left(1 < d \land d \mid p^{A} \cdot q^{B}\right)) \Rightarrow\\p^{A} \cdot q^{B} \le 8 \cdot card\left(\{x: Fin\left(p^{A} \cdot q^{B}\right) \mid \forall d \in \mathbb{N},\; d \in D \Rightarrow val\left(x\right) \bmod d \ne a\left(d\right) \bmod d\}\right).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/TwoOddPrimeUncoveredDensity.two_odd_prime_uncovered_density` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let p and q be distinct odd primes and let L = p^A q^B, with A and B arbitrary natural numbers, including zero. A finite set D records distinct moduli. If every d in D is greater than one and divides L, then every assignment a of residue representatives leaves at least one eighth of Fin L uncovered.

Here mod denotes natural-number remainder, val is the coercion from Fin L to its natural representative, and card counts the displayed finite set. The proof counts one residue fibre exactly as L/d, bounds the finite union of covered fibres, identifies the ambient reciprocal sum with the divisor sum with d = 1 removed, and proves 8 sigma(L) <= 15L from two finite geometric estimates.

The reciprocal-sum necessary condition is classical covering-system folklore: the reciprocal sum of covering moduli is at least one. The quantified two-odd-prime form proved here is repository-derived. Hough and Nielsen (2019), Covering systems with restricted divisibility, and Balister, Bollobas, Morris, Sahasrabudhe and Tiba (2022), On the Erdos Covering Problem: the density of the uncovered set, provide background on odd covering systems; neither is cited as attesting the displayed two-prime L/8 bound.

This is a periphery result for Erdos problem 7. It excludes modulus families supported on at most two odd primes; it does not resolve the open problem for arbitrary distinct odd moduli.

**Proposition 1.2 (The residue classes cannot cover the complete period).**

$$\begin{aligned}\forall p, q \in \mathbb{N},\\(\left(\left(\left(Prime\left(p\right) \land Prime\left(q\right)\right) \land Odd\left(p\right)\right) \land Odd\left(q\right)\right) \land p \ne q) \Rightarrow\\\forall A, B \in \mathbb{N}, D \in Finset\left(\mathbb{N}\right),\\\forall a: \mathbb{N} \to \mathbb{N},\\(\forall d \in \mathbb{N},\; d \in D \Rightarrow \left(1 < d \land d \mid p^{A} \cdot q^{B}\right)) \Rightarrow\\\neg (\forall x \in Fin\left(p^{A} \cdot q^{B}\right),\; \exists d \in \mathbb{N},\; d \in D \land val\left(x\right) \bmod d = a\left(d\right) \bmod d).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/TwoOddPrimeUncoveredDensity.two_odd_prime_residue_classes_do_not_cover` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the same prime, exponent, modulus, and residue hypotheses, it is not the case that every element of Fin(p^A q^B) belongs to one of the selected congruence classes. This is the named bind-only companion directed from the no-cover consequence to the preceding density theorem. This consequence is repository-derived from that theorem; the literature above supplies background only.

## References

- Truth anchor: `D5/S3/Arith/Congruence/TwoOddPrimeUncoveredDensity.two_odd_prime_residue_classes_do_not_cover`
- Truth anchor: `D5/S3/Arith/Congruence/TwoOddPrimeUncoveredDensity.two_odd_prime_uncovered_density`
