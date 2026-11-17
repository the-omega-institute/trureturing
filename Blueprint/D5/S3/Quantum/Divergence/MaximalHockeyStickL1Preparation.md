# Preparation on the entire complex L1 space

## Abstract

Actual positive trace-preserving complex L1 maps, finite-source density representation and change of density.

The source measure and measurable space are arbitrary, and the output is any finite complex matrix algebra, including empty dimension. Positivity and trace preservation hold on the entire complex L1 domain; continuity is derived. Finite-source density representation uses a supplied trace-one base only to repair a null exceptional set. No optimizer or invertibility hypothesis is introduced.

**Theorem 1.1 (PositiveTracePreservingL1Map.norm_bound).**

$$\forall n : \operatorname{Type}\left(\right), [\operatorname{Fintype}\left(n\right)] [\operatorname{DecidableEq}\left(n\right)] \forall alpha : \operatorname{Type}\left(\right), [\operatorname{MeasurableSpace}\left(alpha\right)] \forall mu : \operatorname{Measure}\left(alpha\right), \forall Gamma : \operatorname{PositiveTracePreservingLoneMap}\left(mu, n\right), \forall v : \operatorname{ComplexLone}\left(alpha, mu\right), \operatorname{Norm}\left(Gamma\left(v\right)\right) \le 4 \cdot \operatorname{Norm}\left(v\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/MaximalHockeyStickL1Preparation.norm_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Entrywise matrix norm is bounded by the real trace on positive matrices. Decompose a complex L1 input into the positive and negative parts of its real and imaginary coordinates. Trace preservation bounds each contribution by the original L1 norm. Thus positivity and TP imply boundedness, rather than continuity being a hidden extra source-class assumption.

**Theorem 1.2 (closedPerspectiveCost_withDensity).**

$$\forall f : (\mathbb{R} \to \mathbb{R}), \forall h : \operatorname{ConvexOn}\left(\mathbb{R}, \operatorname{Ioi}\left(0\right), f\right), \forall alpha : \operatorname{Type}\left(\right), [\operatorname{MeasurableSpace}\left(alpha\right)] \forall mu : \operatorname{Measure}\left(alpha\right), \forall r : (alpha \to \operatorname{NonnegativeReal}\left(\right)), \operatorname{Measurable}\left(r\right) \Rightarrow \forall p : (alpha \to \mathbb{R}), \forall q : (alpha \to \mathbb{R}), \operatorname{closedPerspectiveCost}\left(h, \operatorname{WithDensity}\left(mu, r\right), p, q\right) = \operatorname{closedPerspectiveCost}\left(h, mu, x \mapsto r\left(x\right) \cdot p\left(x\right), x \mapsto r\left(x\right) \cdot q\left(x\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/MaximalHockeyStickL1Preparation.closedPerspectiveCost_withDensity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Changing to a finite-valued nonnegative measurable density preserves the unnormalized perspective cost for arbitrary source measure and arbitrary real input functions. The real affine part uses the Bochner change-of-measure identity and the curvature part uses positive homogeneity under the extended nonnegative integral. Infinite axis values are retained.

**Theorem 1.3 (finite_source_density).**

$$\forall n : \operatorname{Type}\left(\right), \forall alpha : \operatorname{Type}\left(\right), [\operatorname{Fintype}\left(n\right)] [\operatorname{DecidableEq}\left(n\right)] [\operatorname{MeasurableSpace}\left(alpha\right)] \forall mu : \operatorname{Measure}\left(alpha\right), \operatorname{IsFiniteMeasure}\left(mu\right) \Rightarrow \forall G : \operatorname{RealLoneLinearMap}\left(alpha, mu, \operatorname{Matrix}\left(n, n, \operatorname{Complex}\left(\right)\right)\right), \operatorname{Positive}\left(G\right) \Rightarrow \left(\operatorname{TracePreserving}\left(G\right) \Rightarrow \forall base : \operatorname{Matrix}\left(n, n, \operatorname{Complex}\left(\right)\right), \operatorname{PosSemidef}\left(base\right) \Rightarrow \left(\operatorname{Trace}\left(base\right) = 1 \Rightarrow \exists tau : (alpha \to \operatorname{Matrix}\left(n, n, \operatorname{Complex}\left(\right)\right)), \left(\operatorname{Measurable}\left(tau\right) \land \left(\operatorname{Integrable}\left(tau, mu\right) \land \forall x : alpha, \operatorname{PosSemidef}\left(tau\left(x\right)\right) \land \operatorname{Trace}\left(tau\left(x\right)\right) = 1\right)\right) \land \forall E : \operatorname{Set}\left(alpha\right), \operatorname{MeasurableSet}\left(E\right) \Rightarrow \forall i : n, \forall j : n, \operatorname{SetIntegral}\left(E, x \mapsto tau\left(x, i, j\right), mu\right) = G\left(\operatorname{LoneIndicator}\left(E, mu\right), i, j\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/MaximalHockeyStickL1Preparation.finite_source_density` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Construct V(E) directly from the real L1 indicator action of the map. Positivity and the trace identity dominate its matrix norm by the source measure, proving countable additivity. Continuous coordinate projections give genuine complex measures. Apply the frozen positive_history_density theorem to this PositiveHistoryMeasure; Radon–Nikodym theory is reused, not rebuilt.

**Theorem 1.4 (finite_source_representation).**

$$\forall n : \operatorname{Type}\left(\right), \forall alpha : \operatorname{Type}\left(\right), [\operatorname{Fintype}\left(n\right)] [\operatorname{DecidableEq}\left(n\right)] [\operatorname{MeasurableSpace}\left(alpha\right)] \forall mu : \operatorname{Measure}\left(alpha\right), \operatorname{IsFiniteMeasure}\left(mu\right) \Rightarrow \forall G : \operatorname{ContinuousRealLoneLinearMap}\left(alpha, mu, \operatorname{Matrix}\left(n, n, \operatorname{Complex}\left(\right)\right)\right), \operatorname{Positive}\left(G\right) \Rightarrow \left(\operatorname{TracePreserving}\left(G\right) \Rightarrow \forall base : \operatorname{Matrix}\left(n, n, \operatorname{Complex}\left(\right)\right), \operatorname{PosSemidef}\left(base\right) \Rightarrow \left(\operatorname{Trace}\left(base\right) = 1 \Rightarrow \exists tau : (alpha \to \operatorname{Matrix}\left(n, n, \operatorname{Complex}\left(\right)\right)), \left(\operatorname{Measurable}\left(tau\right) \land \left(\operatorname{Integrable}\left(tau, mu\right) \land \forall x : alpha, \operatorname{PosSemidef}\left(tau\left(x\right)\right) \land \operatorname{Trace}\left(tau\left(x\right)\right) = 1\right)\right) \land \forall v : \operatorname{RealLone}\left(alpha, mu\right), G\left(v\right) = \operatorname{Integral}\left(x \mapsto \operatorname{SMul}\left(v\left(x\right), tau\left(x\right)\right), mu\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/MaximalHockeyStickL1Preparation.finite_source_representation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The density tau is measurable, integrable, positive semidefinite and trace one everywhere. The indicator identities extend to every integrable real L1 input by simple-function density and continuity of both the original action and the density-integral map. The chosen trace-one base handles the null exceptional set; zero source mass is allowed.

PositiveTracePreservingL1Map.weightMap and weightMap_coe implement the actual change of density and its almost-everywhere action. psd_norm_le_trace and closedPerspective_homogeneous are used both here and in MaximalHockeyStickL1ReverseTest's finite-moment atomization. That consumer retains the original sigma-finite and s-finite source equivalences. The coordinate density theorem reuses MeasurableInstrumentHistory.positive_history_density; the homogeneity identity retains infinite convex endpoint costs.

## References

- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickL1Preparation.closedPerspectiveCost_withDensity`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickL1Preparation.finite_source_density`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickL1Preparation.finite_source_representation`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickL1Preparation.norm_bound`
- Dependency: [D5/S3/Analytic/Convexity/CurvaturePerspectiveEndpoints](../../Analytic/Convexity/CurvaturePerspectiveEndpoints.md)
- Dependency: [D5/S3/Quantum/Divergence/MaximalHockeyStickOperational](MaximalHockeyStickOperational.md)
- Dependency: [D5/S3/Quantum/Matrix/CartesianVariance](../Matrix/CartesianVariance.md)
- Dependency: [D5/S3/Quantum/Measurement/MeasurableInstrumentHistory](../Measurement/MeasurableInstrumentHistory.md)
