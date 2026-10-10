# DegreeGeneratingFunction

## Abstract

Degree enumeration for labelled circular run-constrained words.

**Definition 1.1 (degSeries).**

$$\operatorname{degSeries} = (\operatorname{PowerSeries}.\operatorname{mk} (\operatorname{fun} \operatorname{n} \mapsto \sum \operatorname{k} \in \operatorname{Finset}.\operatorname{range} (\operatorname{n} + 1) , \operatorname{Polynomial}.\operatorname{C} (\operatorname{N} \operatorname{n} \operatorname{k} : \mathbb{Z}) \cdot \operatorname{Polynomial}.\operatorname{X}^{\operatorname{k}}))$$

*Formalization.* `D5/S1/Words/AssociatedMersenne/DegreeGeneratingFunction.degSeries` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* J. Wei and Y. Yang (2024). *Associated Mersenne graphs*. DOI: [10.48550/arXiv.2407.08237](https://doi.org/10.48550/arXiv.2407.08237). URL: <https://arxiv.org/abs/2407.08237v1>.

*Commentary.*

Each length coefficient is the polynomial histogram of admissible labelled words by degree.

**Definition 1.2 (numCoeff).**

$$\begin{aligned}\forall (\operatorname{n}: \operatorname{Nat}), (\operatorname{n} = 0) \to (\operatorname{numCoeff} \operatorname{n} = 1)\\\forall (\operatorname{n}: \operatorname{Nat}), (\operatorname{n} = 1) \to (\operatorname{numCoeff} \operatorname{n} = 1 - (\operatorname{Polynomial}.\operatorname{X} : \operatorname{Polynomial} \mathbb{Z}))\\\forall (\operatorname{n}: \operatorname{Nat}), (\operatorname{n} = 2) \to (\operatorname{numCoeff} \operatorname{n} = - (\operatorname{Polynomial}.\operatorname{X} : \operatorname{Polynomial} \mathbb{Z}) - 3)\\\forall (\operatorname{n}: \operatorname{Nat}), (\operatorname{n} = 3) \to (\operatorname{numCoeff} \operatorname{n} = (\operatorname{Polynomial}.\operatorname{X} : \operatorname{Polynomial} \mathbb{Z})^{3} + 5 \cdot (\operatorname{Polynomial}.\operatorname{X} : \operatorname{Polynomial} \mathbb{Z}) - 4)\\\forall (\operatorname{n}: \operatorname{Nat}), (\operatorname{n} = 4) \to (\operatorname{numCoeff} \operatorname{n} = - 3 \cdot (\operatorname{Polynomial}.\operatorname{X} : \operatorname{Polynomial} \mathbb{Z})^{2} + 7 \cdot (\operatorname{Polynomial}.\operatorname{X} : \operatorname{Polynomial} \mathbb{Z}) + 2)\\\forall (\operatorname{n}: \operatorname{Nat}), (\operatorname{n} = 5) \to (\operatorname{numCoeff} \operatorname{n} = (\operatorname{Polynomial}.\operatorname{X} : \operatorname{Polynomial} \mathbb{Z})^{3} - 11 \cdot (\operatorname{Polynomial}.\operatorname{X} : \operatorname{Polynomial} \mathbb{Z}) + 6)\\\forall (\operatorname{n}: \operatorname{Nat}), (\operatorname{n} = 6) \to (\operatorname{numCoeff} \operatorname{n} = - 5 \cdot (\operatorname{Polynomial}.\operatorname{X} : \operatorname{Polynomial} \mathbb{Z})^{3} + 17 \cdot (\operatorname{Polynomial}.\operatorname{X} : \operatorname{Polynomial} \mathbb{Z})^{2} - 18 \cdot (\operatorname{Polynomial}.\operatorname{X} : \operatorname{Polynomial} \mathbb{Z}) + 2)\\\forall (\operatorname{n}: \operatorname{Nat}), (\operatorname{n} = 7) \to (\operatorname{numCoeff} \operatorname{n} = 7 \cdot (\operatorname{Polynomial}.\operatorname{X} : \operatorname{Polynomial} \mathbb{Z})^{4} - 22 \cdot (\operatorname{Polynomial}.\operatorname{X} : \operatorname{Polynomial} \mathbb{Z})^{3} + 7 \cdot (\operatorname{Polynomial}.\operatorname{X} : \operatorname{Polynomial} \mathbb{Z})^{2} + 14 \cdot (\operatorname{Polynomial}.\operatorname{X} : \operatorname{Polynomial} \mathbb{Z}) - 4)\\\forall (\operatorname{n}: \operatorname{Nat}), (\operatorname{n} = 8) \to (\operatorname{numCoeff} \operatorname{n} = - (\operatorname{Polynomial}.\operatorname{X} : \operatorname{Polynomial} \mathbb{Z})^{4} + 15 \cdot (\operatorname{Polynomial}.\operatorname{X} : \operatorname{Polynomial} \mathbb{Z})^{3} - 32 \cdot (\operatorname{Polynomial}.\operatorname{X} : \operatorname{Polynomial} \mathbb{Z})^{2} + 22 \cdot (\operatorname{Polynomial}.\operatorname{X} : \operatorname{Polynomial} \mathbb{Z}) - 3)\\\forall (\operatorname{n}: \operatorname{Nat}), (\operatorname{n} = 9) \to (\operatorname{numCoeff} \operatorname{n} = - (\operatorname{Polynomial}.\operatorname{X} : \operatorname{Polynomial} \mathbb{Z})^{5} - 24 \cdot (\operatorname{Polynomial}.\operatorname{X} : \operatorname{Polynomial} \mathbb{Z})^{4} + 57 \cdot (\operatorname{Polynomial}.\operatorname{X} : \operatorname{Polynomial} \mathbb{Z})^{3} - 22 \cdot (\operatorname{Polynomial}.\operatorname{X} : \operatorname{Polynomial} \mathbb{Z})^{2} - 11 \cdot (\operatorname{Polynomial}.\operatorname{X} : \operatorname{Polynomial} \mathbb{Z}) + 1)\\\forall (\operatorname{n}: \operatorname{Nat}), (\operatorname{n} = 10) \to (\operatorname{numCoeff} \operatorname{n} = - 2 \cdot (\operatorname{Polynomial}.\operatorname{X} : \operatorname{Polynomial} \mathbb{Z})^{5} + 8 \cdot (\operatorname{Polynomial}.\operatorname{X} : \operatorname{Polynomial} \mathbb{Z})^{4} - 21 \cdot (\operatorname{Polynomial}.\operatorname{X} : \operatorname{Polynomial} \mathbb{Z})^{3} + 27 \cdot (\operatorname{Polynomial}.\operatorname{X} : \operatorname{Polynomial} \mathbb{Z})^{2} - 13 \cdot (\operatorname{Polynomial}.\operatorname{X} : \operatorname{Polynomial} \mathbb{Z}) + 1)\\\forall (\operatorname{n}: \operatorname{Nat}), (\operatorname{n} = 11) \to (\operatorname{numCoeff} \operatorname{n} = - 2 \cdot (\operatorname{Polynomial}.\operatorname{X} : \operatorname{Polynomial} \mathbb{Z})^{6} - 2 \cdot (\operatorname{Polynomial}.\operatorname{X} : \operatorname{Polynomial} \mathbb{Z})^{5} + 43 \cdot (\operatorname{Polynomial}.\operatorname{X} : \operatorname{Polynomial} \mathbb{Z})^{4} - 71 \cdot (\operatorname{Polynomial}.\operatorname{X} : \operatorname{Polynomial} \mathbb{Z})^{3} + 27 \cdot (\operatorname{Polynomial}.\operatorname{X} : \operatorname{Polynomial} \mathbb{Z})^{2} + 5 \cdot (\operatorname{Polynomial}.\operatorname{X} : \operatorname{Polynomial} \mathbb{Z}))\\\forall (\operatorname{n}: \operatorname{Nat}), (\operatorname{n} = 12) \to (\operatorname{numCoeff} \operatorname{n} = - (\operatorname{Polynomial}.\operatorname{X} : \operatorname{Polynomial} \mathbb{Z})^{6} + 8 \cdot (\operatorname{Polynomial}.\operatorname{X} : \operatorname{Polynomial} \mathbb{Z})^{5} - 19 \cdot (\operatorname{Polynomial}.\operatorname{X} : \operatorname{Polynomial} \mathbb{Z})^{4} + 21 \cdot (\operatorname{Polynomial}.\operatorname{X} : \operatorname{Polynomial} \mathbb{Z})^{3} - 12 \cdot (\operatorname{Polynomial}.\operatorname{X} : \operatorname{Polynomial} \mathbb{Z})^{2} + 3 \cdot (\operatorname{Polynomial}.\operatorname{X} : \operatorname{Polynomial} \mathbb{Z}))\\\forall (\operatorname{n}: \operatorname{Nat}), (\operatorname{n} = 13) \to (\operatorname{numCoeff} \operatorname{n} = - (\operatorname{Polynomial}.\operatorname{X} : \operatorname{Polynomial} \mathbb{Z})^{7} - 7 \cdot (\operatorname{Polynomial}.\operatorname{X} : \operatorname{Polynomial} \mathbb{Z})^{6} + 39 \cdot (\operatorname{Polynomial}.\operatorname{X} : \operatorname{Polynomial} \mathbb{Z})^{5} - 72 \cdot (\operatorname{Polynomial}.\operatorname{X} : \operatorname{Polynomial} \mathbb{Z})^{4} + 59 \cdot (\operatorname{Polynomial}.\operatorname{X} : \operatorname{Polynomial} \mathbb{Z})^{3} - 17 \cdot (\operatorname{Polynomial}.\operatorname{X} : \operatorname{Polynomial} \mathbb{Z})^{2} - (\operatorname{Polynomial}.\operatorname{X} : \operatorname{Polynomial} \mathbb{Z}))\\\forall (\operatorname{n}: \operatorname{Nat}), (\operatorname{n} = 14) \to (\operatorname{numCoeff} \operatorname{n} = 2 \cdot (\operatorname{Polynomial}.\operatorname{X} : \operatorname{Polynomial} \mathbb{Z})^{6} - 10 \cdot (\operatorname{Polynomial}.\operatorname{X} : \operatorname{Polynomial} \mathbb{Z})^{5} + 18 \cdot (\operatorname{Polynomial}.\operatorname{X} : \operatorname{Polynomial} \mathbb{Z})^{4} - 14 \cdot (\operatorname{Polynomial}.\operatorname{X} : \operatorname{Polynomial} \mathbb{Z})^{3} + 4 \cdot (\operatorname{Polynomial}.\operatorname{X} : \operatorname{Polynomial} \mathbb{Z})^{2})\\\forall (\operatorname{n}: \operatorname{Nat}), (\operatorname{n} = 15) \to (\operatorname{numCoeff} \operatorname{n} = - 14 \cdot (\operatorname{Polynomial}.\operatorname{X} : \operatorname{Polynomial} \mathbb{Z})^{7} + 64 \cdot (\operatorname{Polynomial}.\operatorname{X} : \operatorname{Polynomial} \mathbb{Z})^{6} - 114 \cdot (\operatorname{Polynomial}.\operatorname{X} : \operatorname{Polynomial} \mathbb{Z})^{5} + 98 \cdot (\operatorname{Polynomial}.\operatorname{X} : \operatorname{Polynomial} \mathbb{Z})^{4} - 40 \cdot (\operatorname{Polynomial}.\operatorname{X} : \operatorname{Polynomial} \mathbb{Z})^{3} + 6 \cdot (\operatorname{Polynomial}.\operatorname{X} : \operatorname{Polynomial} \mathbb{Z})^{2})\\\forall (\operatorname{n}: \operatorname{Nat}), (\operatorname{n} = 16) \to (\operatorname{numCoeff} \operatorname{n} = - (\operatorname{Polynomial}.\operatorname{X} : \operatorname{Polynomial} \mathbb{Z})^{6} + 4 \cdot (\operatorname{Polynomial}.\operatorname{X} : \operatorname{Polynomial} \mathbb{Z})^{5} - 6 \cdot (\operatorname{Polynomial}.\operatorname{X} : \operatorname{Polynomial} \mathbb{Z})^{4} + 4 \cdot (\operatorname{Polynomial}.\operatorname{X} : \operatorname{Polynomial} \mathbb{Z})^{3} - (\operatorname{Polynomial}.\operatorname{X} : \operatorname{Polynomial} \mathbb{Z})^{2})\\\forall (\operatorname{n}: \operatorname{Nat}), (\operatorname{n} = 17) \to (\operatorname{numCoeff} \operatorname{n} = - 6 \cdot (\operatorname{Polynomial}.\operatorname{X} : \operatorname{Polynomial} \mathbb{Z})^{8} + 39 \cdot (\operatorname{Polynomial}.\operatorname{X} : \operatorname{Polynomial} \mathbb{Z})^{7} - 97 \cdot (\operatorname{Polynomial}.\operatorname{X} : \operatorname{Polynomial} \mathbb{Z})^{6} + 118 \cdot (\operatorname{Polynomial}.\operatorname{X} : \operatorname{Polynomial} \mathbb{Z})^{5} - 72 \cdot (\operatorname{Polynomial}.\operatorname{X} : \operatorname{Polynomial} \mathbb{Z})^{4} + 19 \cdot (\operatorname{Polynomial}.\operatorname{X} : \operatorname{Polynomial} \mathbb{Z})^{3} - (\operatorname{Polynomial}.\operatorname{X} : \operatorname{Polynomial} \mathbb{Z})^{2})\\\forall (\operatorname{n}: \operatorname{Nat}), (\operatorname{n} = 19) \to (\operatorname{numCoeff} \operatorname{n} = 4 \cdot (\operatorname{Polynomial}.\operatorname{X} : \operatorname{Polynomial} \mathbb{Z})^{8} - 20 \cdot (\operatorname{Polynomial}.\operatorname{X} : \operatorname{Polynomial} \mathbb{Z})^{7} + 40 \cdot (\operatorname{Polynomial}.\operatorname{X} : \operatorname{Polynomial} \mathbb{Z})^{6} - 40 \cdot (\operatorname{Polynomial}.\operatorname{X} : \operatorname{Polynomial} \mathbb{Z})^{5} + 20 \cdot (\operatorname{Polynomial}.\operatorname{X} : \operatorname{Polynomial} \mathbb{Z})^{4} - 4 \cdot (\operatorname{Polynomial}.\operatorname{X} : \operatorname{Polynomial} \mathbb{Z})^{3})\\\forall (\operatorname{n}: \operatorname{Nat}), (\neg (\operatorname{n} \in [ 0 , 1 , 2 , 3 , 4 , 5 , 6 , 7 , 8 , 9 , 10 , 11 , 12 , 13 , 14 , 15 , 16 , 17 , 19 ])) \to (\operatorname{numCoeff} \operatorname{n} = 0)\end{aligned}$$

*Formalization.* `D5/S1/Words/AssociatedMersenne/DegreeGeneratingFunction.numCoeff` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* J. Wei and Y. Yang (2024). *Associated Mersenne graphs*. DOI: [10.48550/arXiv.2407.08237](https://doi.org/10.48550/arXiv.2407.08237). URL: <https://arxiv.org/abs/2407.08237v1>.

*Commentary.*

The explicit finite polynomial coefficients specify the numerator in the length variable.

**Definition 1.3 (denCoeff).**

$$\begin{aligned}\forall (\operatorname{n}: \operatorname{Nat}), (\operatorname{n} = 0) \to (\operatorname{denCoeff} \operatorname{n} = 1)\\\forall (\operatorname{n}: \operatorname{Nat}), (\operatorname{n} = 1) \to (\operatorname{denCoeff} \operatorname{n} = - (\operatorname{Polynomial}.\operatorname{X} : \operatorname{Polynomial} \mathbb{Z}))\\\forall (\operatorname{n}: \operatorname{Nat}), (\operatorname{n} = 2) \to (\operatorname{denCoeff} \operatorname{n} = - 4)\\\forall (\operatorname{n}: \operatorname{Nat}), (\operatorname{n} = 3) \to (\operatorname{denCoeff} \operatorname{n} = 3 \cdot (\operatorname{Polynomial}.\operatorname{X} : \operatorname{Polynomial} \mathbb{Z}))\\\forall (\operatorname{n}: \operatorname{Nat}), (\operatorname{n} = 4) \to (\operatorname{denCoeff} \operatorname{n} = 6)\\\forall (\operatorname{n}: \operatorname{Nat}), (\operatorname{n} = 5) \to (\operatorname{denCoeff} \operatorname{n} = - (\operatorname{Polynomial}.\operatorname{X} : \operatorname{Polynomial} \mathbb{Z})^{2} - 2 \cdot (\operatorname{Polynomial}.\operatorname{X} : \operatorname{Polynomial} \mathbb{Z}))\\\forall (\operatorname{n}: \operatorname{Nat}), (\operatorname{n} = 6) \to (\operatorname{denCoeff} \operatorname{n} = - 4)\\\forall (\operatorname{n}: \operatorname{Nat}), (\operatorname{n} = 7) \to (\operatorname{denCoeff} \operatorname{n} = (\operatorname{Polynomial}.\operatorname{X} : \operatorname{Polynomial} \mathbb{Z})^{3} + 2 \cdot (\operatorname{Polynomial}.\operatorname{X} : \operatorname{Polynomial} \mathbb{Z})^{2} - 2 \cdot (\operatorname{Polynomial}.\operatorname{X} : \operatorname{Polynomial} \mathbb{Z}))\\\forall (\operatorname{n}: \operatorname{Nat}), (\operatorname{n} = 8) \to (\operatorname{denCoeff} \operatorname{n} = 1)\\\forall (\operatorname{n}: \operatorname{Nat}), (\operatorname{n} = 9) \to (\operatorname{denCoeff} \operatorname{n} = 2 \cdot (\operatorname{Polynomial}.\operatorname{X} : \operatorname{Polynomial} \mathbb{Z})^{4} - 6 \cdot (\operatorname{Polynomial}.\operatorname{X} : \operatorname{Polynomial} \mathbb{Z})^{3} + (\operatorname{Polynomial}.\operatorname{X} : \operatorname{Polynomial} \mathbb{Z})^{2} + 3 \cdot (\operatorname{Polynomial}.\operatorname{X} : \operatorname{Polynomial} \mathbb{Z}))\\\forall (\operatorname{n}: \operatorname{Nat}), (\operatorname{n} = 11) \to (\operatorname{denCoeff} \operatorname{n} = (\operatorname{Polynomial}.\operatorname{X} : \operatorname{Polynomial} \mathbb{Z})^{5} - 7 \cdot (\operatorname{Polynomial}.\operatorname{X} : \operatorname{Polynomial} \mathbb{Z})^{4} + 12 \cdot (\operatorname{Polynomial}.\operatorname{X} : \operatorname{Polynomial} \mathbb{Z})^{3} - 5 \cdot (\operatorname{Polynomial}.\operatorname{X} : \operatorname{Polynomial} \mathbb{Z})^{2} - (\operatorname{Polynomial}.\operatorname{X} : \operatorname{Polynomial} \mathbb{Z}))\\\forall (\operatorname{n}: \operatorname{Nat}), (\operatorname{n} = 13) \to (\operatorname{denCoeff} \operatorname{n} = - 2 \cdot (\operatorname{Polynomial}.\operatorname{X} : \operatorname{Polynomial} \mathbb{Z})^{5} + 8 \cdot (\operatorname{Polynomial}.\operatorname{X} : \operatorname{Polynomial} \mathbb{Z})^{4} - 10 \cdot (\operatorname{Polynomial}.\operatorname{X} : \operatorname{Polynomial} \mathbb{Z})^{3} + 4 \cdot (\operatorname{Polynomial}.\operatorname{X} : \operatorname{Polynomial} \mathbb{Z})^{2})\\\forall (\operatorname{n}: \operatorname{Nat}), (\operatorname{n} = 15) \to (\operatorname{denCoeff} \operatorname{n} = (\operatorname{Polynomial}.\operatorname{X} : \operatorname{Polynomial} \mathbb{Z})^{5} - 3 \cdot (\operatorname{Polynomial}.\operatorname{X} : \operatorname{Polynomial} \mathbb{Z})^{4} + 3 \cdot (\operatorname{Polynomial}.\operatorname{X} : \operatorname{Polynomial} \mathbb{Z})^{3} - (\operatorname{Polynomial}.\operatorname{X} : \operatorname{Polynomial} \mathbb{Z})^{2})\\\forall (\operatorname{n}: \operatorname{Nat}), (\neg (\operatorname{n} \in [ 0 , 1 , 2 , 3 , 4 , 5 , 6 , 7 , 8 , 9 , 11 , 13 , 15 ])) \to (\operatorname{denCoeff} \operatorname{n} = 0)\end{aligned}$$

*Formalization.* `D5/S1/Words/AssociatedMersenne/DegreeGeneratingFunction.denCoeff` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* J. Wei and Y. Yang (2024). *Associated Mersenne graphs*. DOI: [10.48550/arXiv.2407.08237](https://doi.org/10.48550/arXiv.2407.08237). URL: <https://arxiv.org/abs/2407.08237v1>.

*Commentary.*

The explicit finite polynomial coefficients specify the denominator with constant coefficient one.

**Definition 1.4 (NUM).**

$$\operatorname{NUM} = (\operatorname{PowerSeries}.\operatorname{mk} \operatorname{numCoeff})$$

*Formalization.* `D5/S1/Words/AssociatedMersenne/DegreeGeneratingFunction.NUM` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* J. Wei and Y. Yang (2024). *Associated Mersenne graphs*. DOI: [10.48550/arXiv.2407.08237](https://doi.org/10.48550/arXiv.2407.08237). URL: <https://arxiv.org/abs/2407.08237v1>.

*Commentary.*

The numerator coefficient list defines a power series with finite support in the length variable.

**Definition 1.5 (DEN).**

$$\operatorname{DEN} = (\operatorname{PowerSeries}.\operatorname{mk} \operatorname{denCoeff})$$

*Formalization.* `D5/S1/Words/AssociatedMersenne/DegreeGeneratingFunction.DEN` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* J. Wei and Y. Yang (2024). *Associated Mersenne graphs*. DOI: [10.48550/arXiv.2407.08237](https://doi.org/10.48550/arXiv.2407.08237). URL: <https://arxiv.org/abs/2407.08237v1>.

*Commentary.*

The denominator coefficient list defines a power series with finite support in the length variable.

**Definition 1.6 (claim).**

$$\operatorname{claim} \iff (\operatorname{degSeries} \cdot \operatorname{DEN} = \operatorname{NUM})$$

*Formalization.* `D5/S1/Words/AssociatedMersenne/DegreeGeneratingFunction.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* J. Wei and Y. Yang (2024). *Associated Mersenne graphs*. DOI: [10.48550/arXiv.2407.08237](https://doi.org/10.48550/arXiv.2407.08237). URL: <https://arxiv.org/abs/2407.08237v1>.

*Commentary.*

Wei and Yang, Question 6.2, arXiv v1, p. 18: “For given n and k, how many vertices of Associated Mersenne graph ℳₙ have degree k?” N n k counts labelled admissible Boolean words, without identifying rotations. The PowerSeries index is length and Polynomial.X records degree. The displayed formula clears the explicit denominator.

**Theorem 1.7 (result).**

$$\operatorname{claim}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/AssociatedMersenne/DegreeGeneratingFunction.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Wei and Y. Yang (2024). *Associated Mersenne graphs*. DOI: [10.48550/arXiv.2407.08237](https://doi.org/10.48550/arXiv.2407.08237). URL: <https://arxiv.org/abs/2407.08237v1>.

*Commentary.*

The marked tuple bijection and pair-local flip classification give the degree statistic. The marked double count and finite transfer resolvent, with the exact singleton correction, yield the displayed denominator-cleared degree generating function for every length.

## References

- Truth anchor: `D5/S1/Words/AssociatedMersenne/DegreeGeneratingFunction.DEN`
- Truth anchor: `D5/S1/Words/AssociatedMersenne/DegreeGeneratingFunction.NUM`
- Truth anchor: `D5/S1/Words/AssociatedMersenne/DegreeGeneratingFunction.claim`
- Truth anchor: `D5/S1/Words/AssociatedMersenne/DegreeGeneratingFunction.degSeries`
- Truth anchor: `D5/S1/Words/AssociatedMersenne/DegreeGeneratingFunction.denCoeff`
- Truth anchor: `D5/S1/Words/AssociatedMersenne/DegreeGeneratingFunction.numCoeff`
- Truth anchor: `D5/S1/Words/AssociatedMersenne/DegreeGeneratingFunction.result`
- Dependency: [D5/S1/Words/AssociatedMersenne/TransferResolvent](TransferResolvent.md)
