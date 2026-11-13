# The all-source bridge

## Abstract

The actual s-finite complex L1 reverse-test class and the finite-alphabet class have equal extended infima for one specified convex closed-perspective cost.

The output is any finite complex matrix algebra, including the empty index type. The two outputs need not be invertible, normalized or have the same trace. A preparation acts on the entire complex L1 space and is complex-linear, positive on the actual almost-everywhere nonnegative cone, and trace-preserving. Continuity is proved from these properties. The scalar generator is real valued and convex on the positive ray; both closed-perspective endpoints may be infinite.

**Theorem 1.1 (source_atomization).**

$$\forall n : \operatorname{Type}\left(\right), [\operatorname{Fintype}\left(n\right)] [\operatorname{DecidableEq}\left(n\right)] \forall f : (\mathbb{R} \to \mathbb{R}), \forall h : \operatorname{ConvexOn}\left(\mathbb{R}, \operatorname{Ioi}\left(0\right), f\right), \forall alpha : \operatorname{Type}\left(\right), [\operatorname{MeasurableSpace}\left(alpha\right)] \forall mu : \operatorname{Measure}\left(alpha\right), \operatorname{SFinite}\left(mu\right) \Rightarrow \forall Gamma : \operatorname{PositiveTracePreservingLoneMap}\left(mu, n\right), \forall p : (alpha \to \mathbb{R}), \forall q : (alpha \to \mathbb{R}), \operatorname{Measurable}\left(p\right) \Rightarrow \left(\operatorname{Measurable}\left(q\right) \Rightarrow \left(\operatorname{Integrable}\left(p, mu\right) \Rightarrow \left(\operatorname{Integrable}\left(q, mu\right) \Rightarrow \left(\operatorname{AENonnegative}\left(p, mu\right) \Rightarrow \left(\operatorname{AENonnegative}\left(q, mu\right) \Rightarrow \left(\operatorname{Ne}\left(\operatorname{closedPerspectiveCost}\left(h, mu, p, q\right), \operatorname{Top}\left(\right)\right) \Rightarrow \exists k : \operatorname{Nat}\left(\right), \exists R : \operatorname{ReverseTest}\left(Gamma\left(\operatorname{ComplexToLone}\left(p, mu\right)\right), Gamma\left(\operatorname{ComplexToLone}\left(q, mu\right)\right), k\right), \operatorname{Sum}\left(i \mapsto \operatorname{closedPerspective}\left(h, \operatorname{InputLeft}\left(R, i\right), \operatorname{InputRight}\left(R, i\right)\right)\right) = \operatorname{closedPerspectiveCost}\left(h, mu, p, q\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/MaximalHockeyStickL1ReverseTest.source_atomization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every specified finite source cost, an actual finite ReverseTest prepares the same two matrices and has exactly that one cost. Reweight by the nonnegative density p+q, represented using positive parts on a null exceptional set. The weighted source measure is finite even when the original source has infinite mass. The induced weighted map remains a positive complex-linear TP map on the entire new L1 space. No existence of a minimizing test is used. The interface asserts a finite alphabet without a numerical cardinality bound.

**Theorem 1.2 (source_class_infimum_eq).**

$$\forall n : \operatorname{Type}\left(\right), [\operatorname{Fintype}\left(n\right)] [\operatorname{DecidableEq}\left(n\right)] \forall f : (\mathbb{R} \to \mathbb{R}), \forall h : \operatorname{ConvexOn}\left(\mathbb{R}, \operatorname{Ioi}\left(0\right), f\right), \forall A : \operatorname{Matrix}\left(n, n, \operatorname{Complex}\left(\right)\right), \forall B : \operatorname{Matrix}\left(n, n, \operatorname{Complex}\left(\right)\right), \operatorname{sInf}\left(\operatorname{allLoneCosts}\left(h, A, B\right)\right) = \operatorname{sInf}\left(\operatorname{finiteCosts}\left(h, A, B\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/MaximalHockeyStickL1ReverseTest.source_class_infimum_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two sets quantify all s-finite source spaces and all finite alphabets respectively, at the same fixed source universe. Finite tests embed through counting measure. Any all-source cost other than plus infinity is atomized exactly; plus infinity imposes no additional lower-bound obligation. Taking lower bounds proves equality in EReal, including unattained finite infima and empty feasible classes. This endpoint concerns one generator at a time, not simultaneous preservation of all generators or the full profile.

**Theorem 1.3 (finiteCosts_subset_allL1Costs).**

$$\forall n : \operatorname{Type}\left(\right), [\operatorname{Fintype}\left(n\right)] [\operatorname{DecidableEq}\left(n\right)] \forall f : (\mathbb{R} \to \mathbb{R}), \forall h : \operatorname{ConvexOn}\left(\mathbb{R}, \operatorname{Ioi}\left(0\right), f\right), \forall A : \operatorname{Matrix}\left(n, n, \operatorname{Complex}\left(\right)\right), \forall B : \operatorname{Matrix}\left(n, n, \operatorname{Complex}\left(\right)\right), \operatorname{Subset}\left(\operatorname{finiteCosts}\left(h, A, B\right), \operatorname{allLoneCosts}\left(h, A, B\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/MaximalHockeyStickL1ReverseTest.finiteCosts_subset_allL1Costs` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Use counting measure on a universe lift of the finite labels. The map sends an arbitrary complex L1 input h to the finite sum of h(i) times its density state. This realizes the exact same matrices and extended perspective cost.

**Theorem 1.4 (allL1Costs_finite).**

$$\forall n : \operatorname{Type}\left(\right), [\operatorname{Fintype}\left(n\right)] [\operatorname{DecidableEq}\left(n\right)] \forall f : (\mathbb{R} \to \mathbb{R}), \forall h : \operatorname{ConvexOn}\left(\mathbb{R}, \operatorname{Ioi}\left(0\right), f\right), \forall A : \operatorname{Matrix}\left(n, n, \operatorname{Complex}\left(\right)\right), \forall B : \operatorname{Matrix}\left(n, n, \operatorname{Complex}\left(\right)\right), \forall z : \operatorname{EReal}\left(\right), \operatorname{Mem}\left(z, \operatorname{allLoneCosts}\left(h, A, B\right)\right) \Rightarrow \left(\operatorname{Ne}\left(z, \operatorname{Top}\left(\right)\right) \Rightarrow \operatorname{Mem}\left(z, \operatorname{finiteCosts}\left(h, A, B\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/MaximalHockeyStickL1ReverseTest.allL1Costs_finite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This applies the constructed atomization to each individual actual source test. It assumes no density representation or finite-moment supplier: both are proved from the original map.

**Theorem 1.5 (allL1Costs_of_positive_L1).**

$$\forall n : \operatorname{Type}\left(\right), [\operatorname{Fintype}\left(n\right)] [\operatorname{DecidableEq}\left(n\right)] \forall f : (\mathbb{R} \to \mathbb{R}), \forall h : \operatorname{ConvexOn}\left(\mathbb{R}, \operatorname{Ioi}\left(0\right), f\right), \forall alpha : \operatorname{Type}\left(\right), [\operatorname{MeasurableSpace}\left(alpha\right)] \forall mu : \operatorname{Measure}\left(alpha\right), \operatorname{SFinite}\left(mu\right) \Rightarrow \forall Gamma : \operatorname{PositiveTracePreservingLoneMap}\left(mu, n\right), \forall p : \operatorname{ComplexLone}\left(alpha, mu\right), \forall q : \operatorname{ComplexLone}\left(alpha, mu\right), \operatorname{AENonnegative}\left(p, mu\right) \Rightarrow \left(\operatorname{AENonnegative}\left(q, mu\right) \Rightarrow \operatorname{Mem}\left(\operatorname{closedPerspectiveCost}\left(h, mu, \operatorname{RealPart}\left(p\right), \operatorname{RealPart}\left(q\right)\right), \operatorname{allLoneCosts}\left(h, Gamma\left(p\right), Gamma\left(q\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/MaximalHockeyStickL1ReverseTest.allL1Costs_of_positive_L1` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The measurable representatives in L1ReverseTest do not restrict the actual source class. For any nonnegative elements p,q of the original complex L1 space, measurable integrable real representatives have the same complex L1 classes and the same cost. Almost-everywhere equality leaves both the finite affine integral and the nonnegative curvature integral unchanged.

**Theorem 1.6 (PositiveTracePreservingL1Map.norm_bound).**

$$\forall n : \operatorname{Type}\left(\right), [\operatorname{Fintype}\left(n\right)] [\operatorname{DecidableEq}\left(n\right)] \forall alpha : \operatorname{Type}\left(\right), [\operatorname{MeasurableSpace}\left(alpha\right)] \forall mu : \operatorname{Measure}\left(alpha\right), \forall Gamma : \operatorname{PositiveTracePreservingLoneMap}\left(mu, n\right), \forall v : \operatorname{ComplexLone}\left(alpha, mu\right), \operatorname{Norm}\left(Gamma\left(v\right)\right) \le 4 \cdot \operatorname{Norm}\left(v\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/MaximalHockeyStickL1ReverseTest.norm_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Entrywise matrix norm is bounded by the real trace on positive matrices. Decompose a complex L1 input into the positive and negative parts of its real and imaginary coordinates. Trace preservation bounds each contribution by the original L1 norm. Thus positivity and TP imply boundedness, rather than continuity being a hidden extra source-class assumption.

**Theorem 1.7 (closedPerspectiveCost_withDensity).**

$$\forall f : (\mathbb{R} \to \mathbb{R}), \forall h : \operatorname{ConvexOn}\left(\mathbb{R}, \operatorname{Ioi}\left(0\right), f\right), \forall alpha : \operatorname{Type}\left(\right), [\operatorname{MeasurableSpace}\left(alpha\right)] \forall mu : \operatorname{Measure}\left(alpha\right), \forall r : (alpha \to \operatorname{NonnegativeReal}\left(\right)), \operatorname{Measurable}\left(r\right) \Rightarrow \forall p : (alpha \to \mathbb{R}), \forall q : (alpha \to \mathbb{R}), \operatorname{closedPerspectiveCost}\left(h, \operatorname{WithDensity}\left(mu, r\right), p, q\right) = \operatorname{closedPerspectiveCost}\left(h, mu, x \mapsto r\left(x\right) \cdot p\left(x\right), x \mapsto r\left(x\right) \cdot q\left(x\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/MaximalHockeyStickL1ReverseTest.closedPerspectiveCost_withDensity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Changing to a finite-valued nonnegative measurable density preserves the unnormalized perspective cost for arbitrary source measure and arbitrary real input functions. The real affine part uses the Bochner change-of-measure identity and the curvature part uses positive homogeneity under the extended nonnegative integral. Infinite axis values are retained.

**Theorem 1.8 (finite_cost_count).**

$$\forall f : (\mathbb{R} \to \mathbb{R}), \forall h : \operatorname{ConvexOn}\left(\mathbb{R}, \operatorname{Ioi}\left(0\right), f\right), \forall beta : \operatorname{Type}\left(\right), [\operatorname{Fintype}\left(beta\right)] [\operatorname{MeasurableSpace}\left(beta\right)] [\operatorname{MeasurableSingletonClass}\left(beta\right)] \forall p : (beta \to \mathbb{R}), \forall q : (beta \to \mathbb{R}), \operatorname{Nonnegative}\left(p\right) \Rightarrow \left(\operatorname{Nonnegative}\left(q\right) \Rightarrow \operatorname{closedPerspectiveCost}\left(h, \operatorname{Count}\left(beta\right), p, q\right) = \operatorname{Sum}\left(i \mapsto \operatorname{closedPerspective}\left(h, p\left(i\right), q\left(i\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/MaximalHockeyStickL1ReverseTest.finite_cost_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On a finite measurable alphabet, counting-measure integrals are the actual finite sums. The pointwise affine-plus-curvature identity, with its nonnegative extended remainder, proves the equality even when individual axis costs are infinite.

**Theorem 1.9 (finite_density_atomization).**

$$\forall n : \operatorname{Type}\left(\right), [\operatorname{Fintype}\left(n\right)] [\operatorname{DecidableEq}\left(n\right)] \forall f : (\mathbb{R} \to \mathbb{R}), \forall h : \operatorname{ConvexOn}\left(\mathbb{R}, \operatorname{Ioi}\left(0\right), f\right), \forall alpha : \operatorname{Type}\left(\right), [\operatorname{MeasurableSpace}\left(alpha\right)] \forall mu : \operatorname{Measure}\left(alpha\right), \operatorname{IsFiniteMeasure}\left(mu\right) \Rightarrow \forall tau : (alpha \to \operatorname{Matrix}\left(n, n, \operatorname{Complex}\left(\right)\right)), \operatorname{Measurable}\left(tau\right) \Rightarrow \left(\forall x : alpha, \operatorname{PosSemidef}\left(tau\left(x\right)\right) \land \operatorname{Trace}\left(tau\left(x\right)\right) = 1 \Rightarrow \forall p : (alpha \to \mathbb{R}), \forall q : (alpha \to \mathbb{R}), \forall c : (alpha \to \mathbb{R}), \operatorname{Integrable}\left(p, mu\right) \Rightarrow \left(\operatorname{Integrable}\left(q, mu\right) \Rightarrow \left(\operatorname{Integrable}\left(c, mu\right) \Rightarrow \left(\operatorname{AENonnegative}\left(p, mu\right) \Rightarrow \left(\operatorname{AENonnegative}\left(q, mu\right) \Rightarrow \left(\operatorname{AE}\left(mu, x \mapsto \operatorname{closedPerspective}\left(h, p\left(x\right), q\left(x\right)\right) = c\left(x\right)\right) \Rightarrow \exists k : \operatorname{Nat}\left(\right), \exists R : \operatorname{ReverseTest}\left(\operatorname{Integral}\left(x \mapsto \operatorname{SMul}\left(p\left(x\right), tau\left(x\right)\right), mu\right), \operatorname{Integral}\left(x \mapsto \operatorname{SMul}\left(q\left(x\right), tau\left(x\right)\right), mu\right), k\right), \operatorname{Sum}\left(i \mapsto \operatorname{closedPerspective}\left(h, \operatorname{InputLeft}\left(R, i\right), \operatorname{InputRight}\left(R, i\right)\right)\right) = \operatorname{Integral}\left(c, mu\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/MaximalHockeyStickL1ReverseTest.finite_density_atomization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Apply the proved finite-moment theorem to two matrix moments and one real cost, restricting all selected points to the conull set where p,q are nonnegative and the perspective equals the finite real c. Multiply both scalar inputs at each selected point by its nonnegative cubature weight. Homogeneity proves exact preservation of this one cost. The zero measure uses the empty alphabet.

**Theorem 1.10 (finite_source_density).**

$$\forall n : \operatorname{Type}\left(\right), \forall alpha : \operatorname{Type}\left(\right), [\operatorname{Fintype}\left(n\right)] [\operatorname{DecidableEq}\left(n\right)] [\operatorname{MeasurableSpace}\left(alpha\right)] \forall mu : \operatorname{Measure}\left(alpha\right), \operatorname{IsFiniteMeasure}\left(mu\right) \Rightarrow \forall G : \operatorname{RealLoneLinearMap}\left(alpha, mu, \operatorname{Matrix}\left(n, n, \operatorname{Complex}\left(\right)\right)\right), \operatorname{Positive}\left(G\right) \Rightarrow \left(\operatorname{TracePreserving}\left(G\right) \Rightarrow \forall base : \operatorname{Matrix}\left(n, n, \operatorname{Complex}\left(\right)\right), \operatorname{PosSemidef}\left(base\right) \Rightarrow \left(\operatorname{Trace}\left(base\right) = 1 \Rightarrow \exists tau : (alpha \to \operatorname{Matrix}\left(n, n, \operatorname{Complex}\left(\right)\right)), \left(\operatorname{Measurable}\left(tau\right) \land \left(\operatorname{Integrable}\left(tau, mu\right) \land \forall x : alpha, \operatorname{PosSemidef}\left(tau\left(x\right)\right) \land \operatorname{Trace}\left(tau\left(x\right)\right) = 1\right)\right) \land \forall E : \operatorname{Set}\left(alpha\right), \operatorname{MeasurableSet}\left(E\right) \Rightarrow \forall i : n, \forall j : n, \operatorname{SetIntegral}\left(E, x \mapsto tau\left(x, i, j\right), mu\right) = G\left(\operatorname{LoneIndicator}\left(E, mu\right), i, j\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/MaximalHockeyStickL1ReverseTest.finite_source_density` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Construct V(E) directly from the real L1 indicator action of the map. Positivity and the trace identity dominate its matrix norm by the source measure, proving countable additivity. Continuous coordinate projections give genuine complex measures. Apply the frozen positive_history_density theorem to this PositiveHistoryMeasure; Radon–Nikodym theory is reused, not rebuilt.

**Theorem 1.11 (finite_source_representation).**

$$\forall n : \operatorname{Type}\left(\right), \forall alpha : \operatorname{Type}\left(\right), [\operatorname{Fintype}\left(n\right)] [\operatorname{DecidableEq}\left(n\right)] [\operatorname{MeasurableSpace}\left(alpha\right)] \forall mu : \operatorname{Measure}\left(alpha\right), \operatorname{IsFiniteMeasure}\left(mu\right) \Rightarrow \forall G : \operatorname{ContinuousRealLoneLinearMap}\left(alpha, mu, \operatorname{Matrix}\left(n, n, \operatorname{Complex}\left(\right)\right)\right), \operatorname{Positive}\left(G\right) \Rightarrow \left(\operatorname{TracePreserving}\left(G\right) \Rightarrow \forall base : \operatorname{Matrix}\left(n, n, \operatorname{Complex}\left(\right)\right), \operatorname{PosSemidef}\left(base\right) \Rightarrow \left(\operatorname{Trace}\left(base\right) = 1 \Rightarrow \exists tau : (alpha \to \operatorname{Matrix}\left(n, n, \operatorname{Complex}\left(\right)\right)), \left(\operatorname{Measurable}\left(tau\right) \land \left(\operatorname{Integrable}\left(tau, mu\right) \land \forall x : alpha, \operatorname{PosSemidef}\left(tau\left(x\right)\right) \land \operatorname{Trace}\left(tau\left(x\right)\right) = 1\right)\right) \land \forall v : \operatorname{RealLone}\left(alpha, mu\right), G\left(v\right) = \operatorname{Integral}\left(x \mapsto \operatorname{SMul}\left(v\left(x\right), tau\left(x\right)\right), mu\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/MaximalHockeyStickL1ReverseTest.finite_source_representation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The density tau is measurable, integrable, positive semidefinite and trace one everywhere. The indicator identities extend to every integrable real L1 input by simple-function density and continuity of both the original action and the density-integral map. The chosen trace-one base handles the null exceptional set; zero source mass is allowed.

For finite density moments, the norm bound on tau makes p tau and q tau Bochner integrable. A finite-cost affine-plus-curvature decomposition supplies an integrable real cost c and pointwise equality on a conull set. MeasurableFiniteMoments.finite_moments is applied to ((p tau,q tau),c), with all selected points in that conull set. Homogeneity of the closed perspective then gives exact equality of the finite sum. Infinite values on the null complement are never converted to real moments. When the output type is empty, trace preservation forces the nonnegative inputs to vanish almost everywhere; the empty finite test has exactly zero cost.

closedPerspectiveCost_withDensity uses the actual unnormalized affine integral plus nonnegative curvature remainder. It retains infinite axis costs and makes no normalization assumption. finite_cost_count identifies that same integral with the finite perspective sum. finitePreparationL1Map is the actual counting-measure preparation, L1ReverseTest records its two L1 inputs and exact output identities, finiteCosts ranges over Fin k, and allL1Costs ranges over every s-finite measurable source and actual preparation map.

**Definition 1.12 (L1ReverseTest.hockey).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickL1ReverseTest.hockey`

*Formalization.* `D5/S3/Quantum/Divergence/MaximalHockeyStickL1ReverseTest.hockey` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The actual positive profile is the real Bochner integral of max(p-tq,0), for the actual integrable nonnegative inputs of the specified positive complex-linear TP L1 test.

**Definition 1.13 (L1ReverseTest.negativeHockey).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickL1ReverseTest.negativeHockey`

*Formalization.* `D5/S3/Quantum/Divergence/MaximalHockeyStickL1ReverseTest.negativeHockey` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The actual negative profile is the real Bochner integral of max(tq-p,0), over the same test and source measure.

**Theorem 1.14 (L1ReverseTest.hockey_integrable).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickL1ReverseTest.hockey_integrable`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/MaximalHockeyStickL1ReverseTest.hockey_integrable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real threshold, integrability of p and q proves integrability of max(p-tq,0); the actual positive integral is finite.

**Theorem 1.15 (L1ReverseTest.negative_hockey_integrable).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickL1ReverseTest.negative_hockey_integrable`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/MaximalHockeyStickL1ReverseTest.negative_hockey_integrable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real threshold, integrability of p and q proves integrability of max(tq-p,0); the actual negative integral is finite. This integrability is used in the direct construction.

**Theorem 1.16 (L1ReverseTest.input_masses).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickL1ReverseTest.input_masses`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/MaximalHockeyStickL1ReverseTest.input_masses` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

TP on the actual complex L1 inputs gives integral p=Re Tr(A) and integral q=Re Tr(B), without trace normalization or a measure-class assumption.

**Theorem 1.17 (L1ReverseTest.negative_hockey_eq).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickL1ReverseTest.negative_hockey_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/MaximalHockeyStickL1ReverseTest.negative_hockey_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At every real threshold the negative integral equals the positive integral minus Re Tr(A) plus t Re Tr(B), by the scalar positive-part identity and the actual TP masses.

**Theorem 1.18 (L1ReverseTest.finite_hockey_realization).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickL1ReverseTest.finite_hockey_realization`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/MaximalHockeyStickL1ReverseTest.finite_hockey_realization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every actual L1 test on any measure and every specified t>0, there exists a finite ReverseTest preparing exactly A,B and realizing both actual hockey integrals at t. Set r=(p-tq)+, h=p-r=min(p,tq) almost everywhere and s=tq-h=(tq-p)+. Whole-domain complex L1 linearity and positivity make X=Gamma(h), A-X=Gamma(r), tB-X=Gamma(s) PSD, and TP gives Re Tr(X)=integral h. In nonempty output dimension use the existing independently indexed weighted-component supplier on three labels with components X,A-X,tB-X and weights (1,1,0),(1/t,0,1/t). In empty dimension TP forces p=q=0 almost everywhere and the genuinely empty alphabet realizes zero profiles. No coordinate or density state is used in the empty branch. This is HMT Proposition V.1, not new mathematics. The quantifiers are for every t>0 and every test there exists a finite test, not one finite test for all t.

**Definition 1.19 (finiteL1ReverseTest).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickL1ReverseTest.finiteL1ReverseTest`

*Formalization.* `D5/S3/Quantum/Divergence/MaximalHockeyStickL1ReverseTest.finiteL1ReverseTest` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Factor the counting-measure constructor already used by finiteCosts_subset_allL1Costs, on ULift of Fin k in the arbitrary source universe. Reuse finitePreparationL1Map on the entire complex L1 domain; the two inputs and exact preparations are unchanged.

**Theorem 1.20 (finiteL1ReverseTest_cost).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickL1ReverseTest.finiteL1ReverseTest_cost`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/MaximalHockeyStickL1ReverseTest.finiteL1ReverseTest_cost` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The factored counting embedding preserves the same extended closed-perspective cost, by finite_cost_count and the universe-lift sum equivalence. The existing finite-cost subset theorem consumes this helper.

**Theorem 1.21 (finiteL1ReverseTest_profiles).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickL1ReverseTest.finiteL1ReverseTest_profiles`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/MaximalHockeyStickL1ReverseTest.finiteL1ReverseTest_profiles` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The same factored counting embedding preserves both actual hockey integrals at every threshold, by integral_count and the universe-lift sum equivalence.

**Theorem 1.22 (positive_L1_profiles).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickL1ReverseTest.positive_L1_profiles`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/MaximalHockeyStickL1ReverseTest.positive_L1_profiles` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any two original nonnegative complex L1 elements and any actual positive complex-linear TP map, the existing measurable representative construction gives an L1ReverseTest with the exact same prepared matrices and both literal real-part hockey integrals at every threshold. integral_congr_ae proves representative independence. No sigma-finite or s-finite premise is needed, and there is no silent measurable-density restriction.

**Theorem 1.23 (positive_L1_finite_hockey_realization).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickL1ReverseTest.positive_L1_finite_hockey_realization`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/MaximalHockeyStickL1ReverseTest.positive_L1_finite_hockey_realization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The raw positive complex L1 inputs therefore admit the same fixed-positive-threshold finite realization of both literal hockey integrals, consuming positive_L1_profiles and the direct three-component theorem.

**Definition 1.24 (sigmaFiniteHockeyProfiles).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickL1ReverseTest.sigmaFiniteHockeyProfiles`

*Formalization.* `D5/S3/Quantum/Divergence/MaximalHockeyStickL1ReverseTest.sigmaFiniteHockeyProfiles` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Pairs of actual positive and negative hockey values of the same test at the specified threshold, quantified over every X in the arbitrary source universe, every measurable structure and sigma-finite measure, and every actual L1ReverseTest. Projecting the first or second coordinate gives exactly the respective original HMT value set.

**Definition 1.25 (sFiniteHockeyProfiles).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickL1ReverseTest.sFiniteHockeyProfiles`

*Formalization.* `D5/S3/Quantum/Divergence/MaximalHockeyStickL1ReverseTest.sFiniteHockeyProfiles` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The identical paired value set with every s-finite measure in place of sigma-finite; the source universe remains independent of the finite output universe.

**Definition 1.26 (finiteHockeyProfiles).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickL1ReverseTest.finiteHockeyProfiles`

*Formalization.* `D5/S3/Quantum/Divergence/MaximalHockeyStickL1ReverseTest.finiteHockeyProfiles` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Pairs of actual finite positive and negative profiles of the same ReverseTest, over all natural alphabet sizes.

**Theorem 1.27 (sigmaFiniteHockeyProfiles_eq).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickL1ReverseTest.sigmaFiniteHockeyProfiles_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/MaximalHockeyStickL1ReverseTest.sigmaFiniteHockeyProfiles_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At each positive threshold the original sigma-finite paired value set equals the finite paired value set. Forward inclusion uses direct per-test realization on the original measure; reverse inclusion uses actual universe-lifted finite counting preparation.

**Theorem 1.28 (sFiniteHockeyProfiles_eq).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickL1ReverseTest.sFiniteHockeyProfiles_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/MaximalHockeyStickL1ReverseTest.sFiniteHockeyProfiles_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At each positive threshold the full s-finite paired value set equals the same finite paired value set, by the same measure-independent realization and counting embedding.

**Definition 1.29 (operationalL1Hockey).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickL1ReverseTest.operationalL1Hockey`

*Formalization.* `D5/S3/Quantum/Divergence/MaximalHockeyStickL1ReverseTest.operationalL1Hockey` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The real infimum of the first projection of sigmaFiniteHockeyProfiles is precisely the original sigma-finite infimum of integral max(p-tq,0).

**Definition 1.30 (operationalL1NegativeHockey).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickL1ReverseTest.operationalL1NegativeHockey`

*Formalization.* `D5/S3/Quantum/Divergence/MaximalHockeyStickL1ReverseTest.operationalL1NegativeHockey` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The real infimum of the second projection of sigmaFiniteHockeyProfiles is precisely the original sigma-finite infimum of integral max(tq-p,0).

**Definition 1.31 (sFiniteOperationalHockey).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickL1ReverseTest.sFiniteOperationalHockey`

*Formalization.* `D5/S3/Quantum/Divergence/MaximalHockeyStickL1ReverseTest.sFiniteOperationalHockey` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The real infimum of the positive actual integral profile over every s-finite L1 source.

**Definition 1.32 (sFiniteOperationalNegativeHockey).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickL1ReverseTest.sFiniteOperationalNegativeHockey`

*Formalization.* `D5/S3/Quantum/Divergence/MaximalHockeyStickL1ReverseTest.sFiniteOperationalNegativeHockey` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The real infimum of the negative actual integral profile over every s-finite L1 source.

**Theorem 1.33 (operationalL1_eq_finite).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickL1ReverseTest.operationalL1_eq_finite`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/MaximalHockeyStickL1ReverseTest.operationalL1_eq_finite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At every positive threshold both original sigma-finite operational infima and both s-finite infima equal the respective finite operational infima. The paired source-set equalities are proved before taking either infimum.

**Theorem 1.34 (operationalL1_hockey_eq).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickL1ReverseTest.operationalL1_hockey_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/MaximalHockeyStickL1ReverseTest.operationalL1_hockey_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary finite PSD A,B and t>0, the actual positive operational infimum is Re Tr(A)-overlapValue(A,tB), and the actual negative infimum is t Re Tr(B)-overlapValue(A,tB), for both original sigma-finite and s-finite sources. The proof consumes operationalL1_eq_finite and the existing finite operational formulas. Those finite infima have nonempty attaining classes and are bounded below. Empty, singular and zero output pairs and arbitrary traces remain included. No closedPerspectiveCost is assumed to be a literal hinge integral.

**Definition 1.35 (sigmaFiniteL1Costs).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickL1ReverseTest.sigmaFiniteL1Costs`

*Formalization.* `D5/S3/Quantum/Divergence/MaximalHockeyStickL1ReverseTest.sigmaFiniteL1Costs` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The same actual closed-perspective cost class as allL1Costs, with the original sigma-finite measure quantifier and arbitrary independent source universe.

**Theorem 1.36 (sigma_finite_source_infimum_eq).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickL1ReverseTest.sigma_finite_source_infimum_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/MaximalHockeyStickL1ReverseTest.sigma_finite_source_infimum_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Finite counting sources are sigma-finite, and sigma-finite sources are s-finite. The original sigma-finite infimum is sandwiched between the already equal finite and s-finite extended infima. This faithful original-source identification is consumed by originalL1Value_eq_allL1Value.

Matsumoto, A new quantum version of f-divergence, arXiv:1311.4722v4, p. 8, Lemma 4.1, proves one-cost finite-source compression with bound 2d^2+3. This interface asserts existence of a finite alphabet without a cardinality bound and makes no new compression claim. Its finite-moment implementation follows Bayer and Teichmann's proof of Tchakaloff's theorem through MeasurableFiniteMoments.finite_moments; the positive-history Radon-Nikodym theorem supplies the matrix density. MaximalHockeyStickAllL1Convex consumes source_class_infimum_eq to identify the actual all-L1 maximal convex value and transfer the finite equality criterion for the Hiai-Mosonyi-Tomamichel source question. The general-f bridge preserves one specified cost. The separate actual hockey bridge implements HMT Proposition V.1 by the direct min/three-component argument and preserves both orientations at one specified positive threshold; no finite test preserving all thresholds or every generator is asserted. MaximalHockeyStickAllL1Convex consumes the original sigma-finite and s-finite operational equalities in its integrated identity and final classifier.

## References

- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickL1ReverseTest.allL1Costs_finite`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickL1ReverseTest.allL1Costs_of_positive_L1`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickL1ReverseTest.closedPerspectiveCost_withDensity`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickL1ReverseTest.finiteCosts_subset_allL1Costs`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickL1ReverseTest.finiteHockeyProfiles`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickL1ReverseTest.finiteL1ReverseTest`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickL1ReverseTest.finiteL1ReverseTest_cost`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickL1ReverseTest.finiteL1ReverseTest_profiles`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickL1ReverseTest.finite_cost_count`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickL1ReverseTest.finite_density_atomization`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickL1ReverseTest.finite_hockey_realization`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickL1ReverseTest.finite_source_density`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickL1ReverseTest.finite_source_representation`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickL1ReverseTest.hockey`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickL1ReverseTest.hockey_integrable`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickL1ReverseTest.input_masses`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickL1ReverseTest.negativeHockey`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickL1ReverseTest.negative_hockey_eq`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickL1ReverseTest.negative_hockey_integrable`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickL1ReverseTest.norm_bound`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickL1ReverseTest.operationalL1Hockey`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickL1ReverseTest.operationalL1NegativeHockey`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickL1ReverseTest.operationalL1_eq_finite`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickL1ReverseTest.operationalL1_hockey_eq`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickL1ReverseTest.positive_L1_finite_hockey_realization`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickL1ReverseTest.positive_L1_profiles`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickL1ReverseTest.sFiniteHockeyProfiles`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickL1ReverseTest.sFiniteHockeyProfiles_eq`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickL1ReverseTest.sFiniteOperationalHockey`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickL1ReverseTest.sFiniteOperationalNegativeHockey`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickL1ReverseTest.sigmaFiniteHockeyProfiles`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickL1ReverseTest.sigmaFiniteHockeyProfiles_eq`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickL1ReverseTest.sigmaFiniteL1Costs`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickL1ReverseTest.sigma_finite_source_infimum_eq`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickL1ReverseTest.source_atomization`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickL1ReverseTest.source_class_infimum_eq`
- Dependency: [D5/S3/Analytic/Convexity/CurvaturePerspectiveEndpoints](../../Analytic/Convexity/CurvaturePerspectiveEndpoints.md)
- Dependency: [D5/S3/Analytic/Convexity/MeasurableFiniteMoments](../../Analytic/Convexity/MeasurableFiniteMoments.md)
- Dependency: [D5/S3/Quantum/Divergence/MaximalHockeyStickOperational](MaximalHockeyStickOperational.md)
- Dependency: [D5/S3/Quantum/Matrix/CartesianVariance](../Matrix/CartesianVariance.md)
- Dependency: [D5/S3/Quantum/Measurement/MeasurableInstrumentHistory](../Measurement/MeasurableInstrumentHistory.md)
