# SingleRunDegrees

## Abstract

Degree enumeration for labelled circular run-constrained words.

**Theorem 1.1 (run interior delete illegal).**

$$\forall (\operatorname{n}: \operatorname{Nat}), \forall (\operatorname{w}: \operatorname{Fin} \operatorname{n} \to \operatorname{Bool}), \forall (\operatorname{a}: \operatorname{Fin} \operatorname{n}), \forall (\operatorname{r}: \operatorname{Nat}), \forall (\operatorname{p}: \operatorname{Nat}), (\operatorname{IsOneRunStart} \operatorname{w} \operatorname{a} \operatorname{r}) \to ((0 < \operatorname{p}) \to ((\operatorname{p} + 1 < \operatorname{r}) \to (\neg \operatorname{Admissible} (\operatorname{CircularWords}.\operatorname{flip} \operatorname{w} (\operatorname{cycAdd} \operatorname{a} \operatorname{p})))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/AssociatedMersenne/SingleRunDegrees.run_interior_delete_illegal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Wei and Y. Yang (2024). *Associated Mersenne graphs*. DOI: [10.48550/arXiv.2407.08237](https://doi.org/10.48550/arXiv.2407.08237). URL: <https://arxiv.org/abs/2407.08237v1>.

*Commentary.*

Deleting an interior one splits its run around a zero gap too short for the preceding run.

**Definition 1.2 (singleRun).**

$$\forall (\operatorname{n}: \operatorname{Nat}), \forall (\operatorname{r}: \operatorname{Nat}), \operatorname{singleRun} \operatorname{n} \operatorname{r} = (\operatorname{fun} \operatorname{j} \mapsto \operatorname{decide} (\operatorname{j}.\operatorname{val} < \operatorname{r}))$$

*Formalization.* `D5/S1/Words/AssociatedMersenne/SingleRunDegrees.singleRun` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* J. Wei and Y. Yang (2024). *Associated Mersenne graphs*. DOI: [10.48550/arXiv.2407.08237](https://doi.org/10.48550/arXiv.2407.08237). URL: <https://arxiv.org/abs/2407.08237v1>.

*Commentary.*

The first r labelled positions are ones and the remaining positions are zeros.

**Theorem 1.3 (singleRun degree).**

$$\forall (\operatorname{r}: \operatorname{Nat}), \forall (\operatorname{s}: \operatorname{Nat}), (0 < \operatorname{r}) \to (\operatorname{degree} (\operatorname{singleRun} (2 \cdot \operatorname{r} + 1 + \operatorname{s}) \operatorname{r}) = \operatorname{min} \operatorname{r} 2 + \operatorname{if} 2 \le \operatorname{s} \operatorname{then} \operatorname{s} \operatorname{else} 0)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/AssociatedMersenne/SingleRunDegrees.singleRun_degree` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Wei and Y. Yang (2024). *Associated Mersenne graphs*. DOI: [10.48550/arXiv.2407.08237](https://doi.org/10.48550/arXiv.2407.08237). URL: <https://arxiv.org/abs/2407.08237v1>.

*Commentary.*

Endpoint deletions and the admissible insertions in the shared circular gap give the exact single-run degree.

**Theorem 1.4 (degree raw singleton).**

$$\forall (\operatorname{n}: \operatorname{Nat}), \forall (\operatorname{w}: \operatorname{Fin} \operatorname{n} \to \operatorname{Bool}), \forall (\operatorname{i}: \operatorname{Fin} \operatorname{n}), \forall (\operatorname{r}: \operatorname{Nat}), \forall (\operatorname{z}: \operatorname{Nat}), (0 < \operatorname{r}) \to ((\operatorname{r} < \operatorname{z}) \to ((\operatorname{linearize} \operatorname{w} \operatorname{i} = \operatorname{rawWord} [ (\operatorname{r} , \operatorname{z}) ]) \to (\operatorname{degree} \operatorname{w} = \operatorname{min} \operatorname{r} 2 + \operatorname{if} 2 \le \operatorname{z} - \operatorname{r} - 1 \operatorname{then} \operatorname{z} - \operatorname{r} - 1 \operatorname{else} 0)))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/AssociatedMersenne/SingleRunDegrees.degree_raw_singleton` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Wei and Y. Yang (2024). *Associated Mersenne graphs*. DOI: [10.48550/arXiv.2407.08237](https://doi.org/10.48550/arXiv.2407.08237). URL: <https://arxiv.org/abs/2407.08237v1>.

*Commentary.*

Rotating to the mark identifies a singleton raw-pair encoding with the single-run degree calculation.

## References

- Truth anchor: `D5/S1/Words/AssociatedMersenne/SingleRunDegrees.degree_raw_singleton`
- Truth anchor: `D5/S1/Words/AssociatedMersenne/SingleRunDegrees.run_interior_delete_illegal`
- Truth anchor: `D5/S1/Words/AssociatedMersenne/SingleRunDegrees.singleRun`
- Truth anchor: `D5/S1/Words/AssociatedMersenne/SingleRunDegrees.singleRun_degree`
- Dependency: [D5/S1/Words/AssociatedMersenne/RunTupleBijection](RunTupleBijection.md)
