# MultiRunDegrees

## Abstract

Degree enumeration for labelled circular run-constrained words.

**Theorem 1.1 (degree raw multi).**

$$\forall (\operatorname{n}: \operatorname{Nat}), \forall (\operatorname{w}: \operatorname{Fin} \operatorname{n} \to \operatorname{Bool}), \forall (\operatorname{i}: \operatorname{Fin} \operatorname{n}), \forall (\operatorname{t}: \operatorname{List} (\operatorname{Nat} \times \operatorname{Nat})), (2 \le \operatorname{t}.\operatorname{length}) \to ((\forall \operatorname{b} \in \operatorname{t} , 0 < \operatorname{b}.1 \land \operatorname{b}.1 < \operatorname{b}.2) \to ((\operatorname{linearize} \operatorname{w} \operatorname{i} = \operatorname{rawWord} \operatorname{t}) \to (\operatorname{degree} \operatorname{w} = \sum \operatorname{p} : \operatorname{Fin} \operatorname{t}.\operatorname{length} , (\operatorname{min} \operatorname{t} [ \operatorname{p}.\operatorname{val} ] . 1 2 + (\operatorname{t} [ \operatorname{p}.\operatorname{val} ] . 2 - (\operatorname{t} [ \operatorname{p}.\operatorname{val} ] . 1 + 1) - 1) + \operatorname{if} \operatorname{t} [ \operatorname{p}.\operatorname{val} ] . 1 + 1 < \operatorname{t} [ \operatorname{p}.\operatorname{val} ] . 2 \land (\operatorname{t} [ (\operatorname{p}.\operatorname{val} + 1) \operatorname{Nat}.\operatorname{mod} \operatorname{t}.\operatorname{length} ]) . 1 + 1 < (\operatorname{t} [ (\operatorname{p}.\operatorname{val} + 1) \operatorname{Nat}.\operatorname{mod} \operatorname{t}.\operatorname{length} ]) . 2 \operatorname{then} 1 \operatorname{else} 0))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/AssociatedMersenne/MultiRunDegrees.degree_raw_multi` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Wei and Y. Yang (2024). *Associated Mersenne graphs*. DOI: [10.48550/arXiv.2407.08237](https://doi.org/10.48550/arXiv.2407.08237). URL: <https://arxiv.org/abs/2407.08237v1>.

*Commentary.*

Pairwise deletion endpoints, gap extensions and interior singleton insertions partition all legal flips.

**Definition 1.2 (tupleDegree).**

$$\forall (\operatorname{t}: \operatorname{List} (\operatorname{Nat} \times \operatorname{Nat})), \operatorname{tupleDegree} \operatorname{t} = (\operatorname{if} \operatorname{t}.\operatorname{length} = 1 \operatorname{then} (\operatorname{t}.\operatorname{map} (\operatorname{fun} \operatorname{b} \mapsto \operatorname{min} \operatorname{b}.1 2 + \operatorname{if} 2 \le \operatorname{b}.2 \operatorname{then} \operatorname{b}.2 \operatorname{else} 0)) . \operatorname{sum} \operatorname{else} \sum \operatorname{p} : \operatorname{Fin} \operatorname{t}.\operatorname{length} , (\operatorname{min} \operatorname{t} [ \operatorname{p}.\operatorname{val} ] . 1 2 + (\operatorname{t} [ \operatorname{p}.\operatorname{val} ] . 2 - 1) + \operatorname{if} 1 \le \operatorname{t} [ \operatorname{p}.\operatorname{val} ] . 2 \land 1 \le (\operatorname{t} [ (\operatorname{p}.\operatorname{val} + 1) \operatorname{Nat}.\operatorname{mod} \operatorname{t}.\operatorname{length} ]) . 2 \operatorname{then} 1 \operatorname{else} 0))$$

*Formalization.* `D5/S1/Words/AssociatedMersenne/MultiRunDegrees.tupleDegree` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* J. Wei and Y. Yang (2024). *Associated Mersenne graphs*. DOI: [10.48550/arXiv.2407.08237](https://doi.org/10.48550/arXiv.2407.08237). URL: <https://arxiv.org/abs/2407.08237v1>.

*Commentary.*

The singleton case includes both circular gap endpoints meeting the same run. Natural subtraction is truncated; it is not integer subtraction.

**Lemma 1.3 (degree wordOfTuple).**

$$\forall (\operatorname{n}: \operatorname{Nat}), \forall (\operatorname{i}: \operatorname{Fin} \operatorname{n}), \forall (\operatorname{t}: \operatorname{GoodTuple} \operatorname{n}), \operatorname{degree} (\operatorname{wordOfTuple} \operatorname{i} \operatorname{t}.\operatorname{val} \operatorname{t}.\operatorname{property}.2.2) = \operatorname{tupleDegree} \operatorname{t}.\operatorname{val}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/AssociatedMersenne/MultiRunDegrees.degree_wordOfTuple` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Wei and Y. Yang (2024). *Associated Mersenne graphs*. DOI: [10.48550/arXiv.2407.08237](https://doi.org/10.48550/arXiv.2407.08237). URL: <https://arxiv.org/abs/2407.08237v1>.

*Commentary.*

The reconstructed word has its tuple encoding, so the pair-local formula gives its degree.

## References

- Truth anchor: `D5/S1/Words/AssociatedMersenne/MultiRunDegrees.degree_raw_multi`
- Truth anchor: `D5/S1/Words/AssociatedMersenne/MultiRunDegrees.degree_wordOfTuple`
- Truth anchor: `D5/S1/Words/AssociatedMersenne/MultiRunDegrees.tupleDegree`
- Dependency: [D5/S1/Words/AssociatedMersenne/SingleRunDegrees](SingleRunDegrees.md)
