# Bounded Two-Term Count Discrepancy and Full Phase Alignment

## Abstract

Bounded two-term count discrepancy can coexist with frequent full sine alignment.

The count, sine score and mass use inclusive cutoffs. Eventually means for all sufficiently large real thresholds. Write u(q,m) = πq/2 + 2πqm.

**Theorem 1.1 (Harmonic weights and full alignment at a bounded count discrepancy).**

$$\exists S \in Spectrum,\; \exists w \in \operatorname{index}\left(S\right) \to \mathbb{R},\; \operatorname{Infinite}\left(\operatorname{index}\left(S\right)\right) \land \left(\left(\forall j \in \operatorname{index}\left(S\right),\; \operatorname{mult}\left(S, j\right) = 1 \land \operatorname{w}\left(j\right) = \frac{\gamma(j)}{\frac{1}{4} + (\gamma(j))^{2}}\right) \land \left(\left(\exists D \in \mathbb{R},\; 0 \le D \land \operatorname{Eventually}\left((T \mapsto \left|\operatorname{N}\left(S, T\right)-\frac{T}{2 \cdot \pi} \cdot (\operatorname{log}\left(\frac{T}{2 \cdot \pi}\right)-1)\right| \le D), atTop\right)\right) \land \left(\operatorname{HasLogSquaredMass}\left(S, w\right) \land \left(\operatorname{HasLogarithmicSquareTail}\left(S, w\right) \land \operatorname{Eventually}\left((T \mapsto 0 < \operatorname{mass}\left(S, w, T\right) \land \left(\exists q \in \mathbb{N},\; 0 < q \land \left(q + 1 \le 21 \cdot \frac{\operatorname{log}\left(21 \cdot T\right)}{\operatorname{log}\left(2\right)} \land \left(\left(\forall m \in \mathbb{Z},\; \forall X \in \mathbb{R},\; X \le T \Rightarrow \operatorname{sine}\left(S, w, X, \operatorname{u}\left(q, m\right)\right) = \operatorname{mass}\left(S, w, X\right)\right) \land \left(\forall A \in \mathbb{R},\; \exists m \in \mathbb{Z},\; A < \operatorname{u}\left(q, m\right) \land \operatorname{u}\left(q, m\right) < A + \frac{42 \cdot \pi}{\operatorname{log}\left(2\right)} \cdot \operatorname{log}\left(21 \cdot T\right)\right)\right)\right)\right)), atTop\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Oscillation/SpectrumTwoTermCountAlignment.exists_two_term_count_alignment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Scale the grid of `D5/S3/Analytic/Oscillation/SpectrumCommensurateAlignment.exists_logarithmic_full_alignment` by 1/21. Start at the lower boundary of block six. Write F for the displayed smooth counting function. Its derivative is log(t/(2π))/(2π). The increase of F between successive grid points is in [0,1), including the gaps crossing block boundaries.

Keep a grid point exactly when the floor of F increases there. All retained frequencies have multiplicity one. Summing the floor increments telescopes to the floor of F at the last grid point at or below the cutoff, minus the floor of F at the initial boundary. Before the first grid point the initial boundary serves as predecessor. The floor and the remaining gap contribute less than two to the absolute count error after removing the initial offset.

Use the count in the partial-summation estimate for harmonic phase mass and the inverse-square tail bound. The closed and open counts differ by at most one since the frequencies are distinct and have unit multiplicity. The chosen weights are positive and bounded above by the inverse frequency.

For a cutoff in block n take q equal to 21 times the grid denominator of that block. Every grid frequency at or below the cutoff, multiplied by q, is an integer congruent to one modulo four. This also holds on the retained subset, so all its sines equal one at u(q,m) simultaneously for all smaller cutoffs. The interval length exceeds the progression period by at least 2π.

The comparison spectrum matches the two-term count with a uniformly bounded error and retains full alignment. Applying a finite-resolution cancellation argument to actual zeta ordinates still requires estimates for their additive phase relations.

## References

- Truth anchor: `D5/S3/Analytic/Oscillation/SpectrumCommensurateAlignment.exists_logarithmic_full_alignment`
- Truth anchor: `D5/S3/Analytic/Oscillation/SpectrumTwoTermCountAlignment.exists_two_term_count_alignment`
- Dependency: [D5/S3/Analytic/Oscillation/SpectrumCommensurateAlignment](SpectrumCommensurateAlignment.md)
