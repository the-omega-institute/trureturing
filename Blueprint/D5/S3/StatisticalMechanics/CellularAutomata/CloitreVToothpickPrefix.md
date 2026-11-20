# Vanishing prefix corrections in the V-toothpick kernel

## Abstract

All prefix corrections of the honeycomb V-toothpick kernel vanish.

**Theorem 1.1 (The full prefix equality).**

$$\forall j \in \mathbb{N},\; \forall c \in \mathbb{N},\; 1 \le j \Rightarrow (c + 2 \le j \Rightarrow (\operatorname{e}\left(j, c\right) = \operatorname{e}\left(j, c + \operatorname{p}\left(j\right)\right) \land \left(\operatorname{e}\left(j, c + \operatorname{p}\left(j\right)\right) = \operatorname{e}\left(j, \operatorname{i}\left(j, \operatorname{p}\left(j\right), c \bmod \operatorname{p}\left(j\right)\right)\right) \land \operatorname{e}\left(j, c\right) - \operatorname{e}\left(j, \operatorname{i}\left(j, \operatorname{p}\left(j\right), c \bmod \operatorname{p}\left(j\right)\right)\right) = 0\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/CellularAutomata/CloitreVToothpickPrefix.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Benoît Cloitre (2026). *On the V-toothpick sequence*. URL: <https://arxiv.org/html/2611.23172v1>.

*Commentary.*

Section 9 asks whether all prefix corrections ηⱼ vanish, equivalently whether for every dyadic P the coefficients of E_c of degree less than P are determined by c modulo 2P.

Here e(j,c) is the coefficient of degree j in the integer polynomial E_c of equation (17). The period p(j) is 2 raised to floor(log₂ j)+2, twice the least dyadic integer P strictly above j. The function i(j,p,r) returns j−1 plus the Euclidean remainder of r−j+1 modulo p, computed over the integers before conversion to a natural. The third equality states that the correction of equation (43) is zero. At j=1 the prefix range is empty.

Take any dyadic P>j. For each of the two cuts, height 4P at column c+2P and height 3P at column c have the same strict bound on g=2x+y+p, where p is the vertex color. At read time s=6P−c−1+j, every nonzero signed weight lies strictly below the displaced-wall horizon in both runs. The first-touch comparison matches the birth indicators at both cuts, including vertices missing from a clipped domain.

The strip identity shifts the adjacent-cut difference at height 3P and column c by 2P to give the difference at height 4P and column c. Reading both coefficients at the common dyadic enclosure gives e(j,c)=e(j,c+2P). For the least eligible P, the negative offset in the Euclidean remainder of equation (43) gives i(j,p(j),c mod p(j))=c+p(j).

## References

- Truth anchor: `D5/S3/StatisticalMechanics/CellularAutomata/CloitreVToothpickPrefix.result`
- Dependency: [D5/S3/StatisticalMechanics/CellularAutomata/HoneycombBirthKernel](HoneycombBirthKernel.md)
