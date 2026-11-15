# Exact finite measurable moments

## Abstract

An integrable finite-dimensional barycenter is in the actual convex hull, and admits exact finite point evaluations.

E is any finite-dimensional real normed space; alpha is any measurable space. No compactness, closedness of the range, or continuity of the moment map is assumed. Integral is the Bochner integral. The proof descends in dimension using a supporting functional and its almost-everywhere zero kernel. This is a formalization of the cited finite-moment argument, not a claim of a new cubature theorem.

**Theorem 1.1 (integral_mem_convexHull).**

$$\forall E : \operatorname{Type}\left(\right), \forall alpha : \operatorname{Type}\left(\right), [\operatorname{NormedAddCommGroup}\left(E\right)] [\operatorname{NormedSpace}\left(\mathbb{R}, E\right)] [\operatorname{FiniteDimensional}\left(\mathbb{R}, E\right)] [\operatorname{MeasurableSpace}\left(alpha\right)] \forall mu : \operatorname{Measure}\left(alpha\right), \forall f : (alpha \to E), \operatorname{IsProbabilityMeasure}\left(mu\right) \Rightarrow \left(\operatorname{Integrable}\left(f, mu\right) \Rightarrow \operatorname{Mem}\left(\operatorname{Integral}\left(f, mu\right), \operatorname{convexHull}\left(\mathbb{R}, \operatorname{range}\left(f\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Convexity/MeasurableFiniteMoments.integral_mem_convexHull` (`✓ std3`). ∎

*Citation.* Christian Bayer and Josef Teichmann (2006). *The proof of Tchakaloff's theorem*. DOI: [10.1090/S0002-9939-06-08249-9](https://doi.org/10.1090/S0002-9939-06-08249-9). URL: <https://arxiv.org/abs/math/0502473v2>.

*Commentary.*

Translate the barycenter to zero. A proper span reduces dimension immediately. In full span, the affine span is full and the convex hull has nonempty interior. If zero were absent, a nonzero supporting functional would have one sign and zero integral. It vanishes almost everywhere; repair the null set by an actual point on the kernel and descend to that proper subspace.

**Theorem 1.2 (finite_moments_probability).**

$$\forall E : \operatorname{Type}\left(\right), \forall alpha : \operatorname{Type}\left(\right), [\operatorname{NormedAddCommGroup}\left(E\right)] [\operatorname{NormedSpace}\left(\mathbb{R}, E\right)] [\operatorname{FiniteDimensional}\left(\mathbb{R}, E\right)] [\operatorname{MeasurableSpace}\left(alpha\right)] \forall mu : \operatorname{Measure}\left(alpha\right), \forall f : (alpha \to E), \forall s : \operatorname{Set}\left(alpha\right), \operatorname{IsProbabilityMeasure}\left(mu\right) \Rightarrow \left(\operatorname{Integrable}\left(f, mu\right) \Rightarrow \left(\operatorname{AE}\left(mu, x \mapsto \operatorname{Mem}\left(x, s\right)\right) \Rightarrow \exists k : \operatorname{Nat}\left(\right), \exists w : (\operatorname{Fin}\left(k\right) \to \mathbb{R}), \exists a : (\operatorname{Fin}\left(k\right) \to alpha), \forall i : \operatorname{Fin}\left(k\right), 0 \le w\left(i\right) \land \left(\operatorname{Sum}\left(w\right) = 1 \land \left(\forall i : \operatorname{Fin}\left(k\right), \operatorname{Mem}\left(a\left(i\right), s\right) \land \operatorname{Sum}\left(i \mapsto \operatorname{SMul}\left(w\left(i\right), f\left(a\left(i\right)\right)\right)\right) = \operatorname{Integral}\left(f, mu\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Convexity/MeasurableFiniteMoments.finite_moments_probability` (`✓ std3`). ∎

*Citation.* Christian Bayer and Josef Teichmann (2006). *The proof of Tchakaloff's theorem*. DOI: [10.1090/S0002-9939-06-08249-9](https://doi.org/10.1090/S0002-9939-06-08249-9). URL: <https://arxiv.org/abs/math/0502473v2>.

*Commentary.*

Every label is an actual point in an arbitrarily prescribed conull set. Repair its complement by one point in that set, apply actual-hull membership, and extract a finite convex combination. The weights are nonnegative and sum to one.

**Theorem 1.3 (finite_moments).**

$$\forall E : \operatorname{Type}\left(\right), \forall alpha : \operatorname{Type}\left(\right), [\operatorname{NormedAddCommGroup}\left(E\right)] [\operatorname{NormedSpace}\left(\mathbb{R}, E\right)] [\operatorname{FiniteDimensional}\left(\mathbb{R}, E\right)] [\operatorname{MeasurableSpace}\left(alpha\right)] \forall mu : \operatorname{Measure}\left(alpha\right), \forall f : (alpha \to E), \forall s : \operatorname{Set}\left(alpha\right), \operatorname{IsFiniteMeasure}\left(mu\right) \Rightarrow \left(\operatorname{Integrable}\left(f, mu\right) \Rightarrow \left(\operatorname{AE}\left(mu, x \mapsto \operatorname{Mem}\left(x, s\right)\right) \Rightarrow \exists k : \operatorname{Nat}\left(\right), \exists w : (\operatorname{Fin}\left(k\right) \to \mathbb{R}), \exists a : (\operatorname{Fin}\left(k\right) \to alpha), \forall i : \operatorname{Fin}\left(k\right), 0 \le w\left(i\right) \land \left(\operatorname{Sum}\left(w\right) = \operatorname{MeasureReal}\left(mu, \operatorname{univ}\left(\right)\right) \land \left(\forall i : \operatorname{Fin}\left(k\right), \operatorname{Mem}\left(a\left(i\right), s\right) \land \operatorname{Sum}\left(i \mapsto \operatorname{SMul}\left(w\left(i\right), f\left(a\left(i\right)\right)\right)\right) = \operatorname{Integral}\left(f, mu\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Convexity/MeasurableFiniteMoments.finite_moments` (`✓ std3`). ∎

*Citation.* Christian Bayer and Josef Teichmann (2006). *The proof of Tchakaloff's theorem*. DOI: [10.1090/S0002-9939-06-08249-9](https://doi.org/10.1090/S0002-9939-06-08249-9). URL: <https://arxiv.org/abs/math/0502473v2>.

*Commentary.*

Normalize a nonzero finite measure to probability and rescale the weights by its total mass. For the zero measure the empty alphabet gives the exact zero moment. No numerical cardinality bound is asserted by this interface.

## References

- Truth anchor: `D5/S3/Analytic/Convexity/MeasurableFiniteMoments.finite_moments`
- Truth anchor: `D5/S3/Analytic/Convexity/MeasurableFiniteMoments.finite_moments_probability`
- Truth anchor: `D5/S3/Analytic/Convexity/MeasurableFiniteMoments.integral_mem_convexHull`
