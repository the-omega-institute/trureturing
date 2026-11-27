# One-loop gauge running and Standard Model normalization

## Abstract

One-loop inverse coupling flow, explicit Weyl charge traces, and the three-coupling meeting condition.

The sign convention gives positive beta coefficients for inverse couplings that increase with energy. All hypercharges use left-handed Weyl fields and the convention Q = T₃ + Y. The trace equality selects three colors within this family of multiplets and normalizations.

**Definition 1.1 (One-loop coefficient).**

Lean statement: `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.betaOneLoop`

*Formalization.* `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.betaOneLoop` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* David J. Gross and Frank Wilczek (1973). *Ultraviolet Behavior of Non-Abelian Gauge Theories*. DOI: [10.1103/PhysRevLett.30.1343](https://doi.org/10.1103/PhysRevLett.30.1343). URL: <https://doi.org/10.1103/PhysRevLett.30.1343>.

*Commentary.*

For N colors, n Dirac fermions and s complex scalars in the fundamental representation the coefficient is 11N/3 − 2n/3 − s/6.

**Theorem 1.2 (Asymptotic freedom criterion).**

Lean statement: `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.asymptotic_freedom_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.asymptotic_freedom_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David J. Gross and Frank Wilczek (1973). *Ultraviolet Behavior of Non-Abelian Gauge Theories*. DOI: [10.1103/PhysRevLett.30.1343](https://doi.org/10.1103/PhysRevLett.30.1343). URL: <https://doi.org/10.1103/PhysRevLett.30.1343>.

*Commentary.*

The coefficient is positive exactly when four times the fermion count plus the scalar count is less than 22 times the color count.

**Theorem 1.3 (QCD flavor bound).**

Lean statement: `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.qcd_asymptotic_freedom_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.qcd_asymptotic_freedom_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David J. Gross and Frank Wilczek (1973). *Ultraviolet Behavior of Non-Abelian Gauge Theories*. DOI: [10.1103/PhysRevLett.30.1343](https://doi.org/10.1103/PhysRevLett.30.1343). URL: <https://doi.org/10.1103/PhysRevLett.30.1343>.

*Commentary.*

With three colors and no scalars, the coefficient is positive exactly when the flavor count is at most sixteen.

**Theorem 1.4 (Six-flavor QCD).**

Lean statement: `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.qcd_six_flavors_beta`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.qcd_six_flavors_beta` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David J. Gross and Frank Wilczek (1973). *Ultraviolet Behavior of Non-Abelian Gauge Theories*. DOI: [10.1103/PhysRevLett.30.1343](https://doi.org/10.1103/PhysRevLett.30.1343). URL: <https://doi.org/10.1103/PhysRevLett.30.1343>.

*Commentary.*

The coefficient for three colors, six flavors and no scalars is seven.

**Definition 1.5 (Running inverse coupling).**

Lean statement: `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.rgInvCoupling`

*Formalization.* `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.rgInvCoupling` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Howard Georgi, Helen R. Quinn, and Steven Weinberg (1974). *Hierarchy of Interactions in Unified Gauge Theories*. DOI: [10.1103/PhysRevLett.33.451](https://doi.org/10.1103/PhysRevLett.33.451). URL: <https://doi.org/10.1103/PhysRevLett.33.451>.

*Commentary.*

Add the log of the scale ratio times the coefficient divided by twice pi to the reference inverse coupling.

**Theorem 1.6 (One-loop differential equation).**

Lean statement: `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.rgInvCoupling_hasDerivAt`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.rgInvCoupling_hasDerivAt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Howard Georgi, Helen R. Quinn, and Steven Weinberg (1974). *Hierarchy of Interactions in Unified Gauge Theories*. DOI: [10.1103/PhysRevLett.33.451](https://doi.org/10.1103/PhysRevLett.33.451). URL: <https://doi.org/10.1103/PhysRevLett.33.451>.

*Commentary.*

At positive scales, the derivative of the inverse coupling in the running scale is the coefficient divided by twice pi times that scale.

**Theorem 1.7 (Ultraviolet limit).**

Lean statement: `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.rg_asymptotic_freedom_limit`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.rg_asymptotic_freedom_limit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive coefficient and reference scale, the reciprocal of the inverse coupling tends to zero as the running scale tends to infinity.

**Theorem 1.8 (Formula for the zero scale).**

Lean statement: `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.rg_zero_scale_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.rg_zero_scale_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive scales and a nonzero coefficient, the inverse coupling vanishes exactly at the reference scale times exp(−2πa₀/b₀), where a₀ is the reference inverse coupling and b₀ is the coefficient.

**Theorem 1.9 (Unique positive zero).**

Lean statement: `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.rg_zero_scale_unique`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.rg_zero_scale_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For nonzero coefficient and positive reference scale, there is exactly one positive scale at which the inverse coupling vanishes.

**Theorem 1.10 (Infrared one-loop scale).**

Lean statement: `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.rg_confinement_scale_lt`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.rg_confinement_scale_lt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive coefficient, reference inverse coupling and reference scale, the exponential scale solving the flow equation lies below the reference scale.

**Theorem 1.11 (Ultraviolet one-loop scale).**

Lean statement: `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.rg_landau_pole_gt`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.rg_landau_pole_gt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For negative coefficient and positive reference data, the exponential scale solving the flow equation lies above the reference scale.

**Definition 1.12 (One-generation Weyl multiplets).**

Lean statement: `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.SMFermion`

*Formalization.* `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.SMFermion` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Use the quark doublet, the conjugate up and down quark singlets, the lepton doublet, and the conjugate charged lepton singlet.

**Definition 1.13 (Weak dimensions).**

Lean statement: `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.weakMultiplicity`

*Formalization.* `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.weakMultiplicity` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The quark and lepton doublets have two weak components. Each conjugate singlet has one.

**Definition 1.14 (Color multiplicities).**

Lean statement: `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.colorMultiplicity`

*Formalization.* `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.colorMultiplicity` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each quark multiplet has one component per color. Each lepton multiplet has one color component.

**Definition 1.15 (Weak generator eigenvalues).**

Lean statement: `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.weylT3`

*Formalization.* `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.weylT3` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The weak doublet weights are one half and minus one half. Each singlet has weight zero.

**Definition 1.16 (Hypercharges on the anomaly-free curve).**

Lean statement: `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.weylY`

*Formalization.* `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.weylY` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For color count N the charges in multiplet order are 1/(2N), −(N + 1)/(2N), (N − 1)/(2N), minus one half, and one.

**Definition 1.17 (Weyl weight sum).**

Lean statement: `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.weylTrace`

*Formalization.* `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.weylTrace` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Sum a function of weak weight and hypercharge over each multiplet's weak components, multiply by the color multiplicity, and sum over the multiplets.

**Definition 1.18 (Quadratic color index).**

Lean statement: `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.colorIndex`

*Formalization.* `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.colorIndex` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each quark multiplet has index one half per weak component. The lepton indices vanish.

**Definition 1.19 (Weak trace).**

Lean statement: `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.weylT3SqTrace`

*Formalization.* `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.weylT3SqTrace` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Sum squared weak weights over the five multiplets with their color multiplicities.

**Definition 1.20 (Color trace).**

Lean statement: `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.weylColorSqTrace`

*Formalization.* `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.weylColorSqTrace` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Sum the quadratic color indices weighted by weak dimensions, with fundamental and antifundamental index one half.

**Definition 1.21 (Mixed trace).**

Lean statement: `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.weylT3YTrace`

*Formalization.* `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.weylT3YTrace` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Sum the product of weak weight and hypercharge over all multiplet components.

**Definition 1.22 (Anomaly-free hypercharge trace).**

Lean statement: `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.weylYSqTraceAnom`

*Formalization.* `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.weylYSqTraceAnom` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Sum squared hypercharges with both weak and color multiplicities.

**Definition 1.23 (Anomaly-free electric charge trace).**

Lean statement: `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.weylQSqTraceAnom`

*Formalization.* `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.weylQSqTraceAnom` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Sum squared electric charges, formed by adding each weak weight to its multiplet hypercharge.

**Theorem 1.24 (Weak trace evaluation).**

Lean statement: `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.weylT3SqTrace_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.weylT3SqTrace_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The squared weak trace is half the color count plus one half. Each doublet contributes two squared weights of one half.

**Theorem 1.25 (Color trace evaluation).**

Lean statement: `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.weylColorSqTrace_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.weylColorSqTrace_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The quadratic color trace is two. The quark doublet contributes one and the two conjugate quark singlets contribute one half each.

**Theorem 1.26 (Color selection by trace equality).**

Lean statement: `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.color_weak_unification_iff_three`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.color_weak_unification_iff_three` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The weak and color traces coincide exactly at three colors.

**Theorem 1.27 (Cancellation of the mixed trace).**

Lean statement: `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.weylT3YTrace_eq_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.weylT3YTrace_eq_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The weak weights cancel within each doublet and vanish on every singlet, so the mixed trace is zero.

**Theorem 1.28 (Hypercharge trace evaluation).**

Lean statement: `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.weylYSqTraceAnom_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.weylYSqTraceAnom_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a nonzero color count N, the hypercharge trace equals (N + 1)(N + 2)/(2N).

**Theorem 1.29 (Electric charge trace evaluation).**

Lean statement: `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.weylQSqTraceAnom_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.weylQSqTraceAnom_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a nonzero color count N, the electric charge trace equals (N + 1)²/N.

**Theorem 1.30 (Electric charge trace splitting).**

Lean statement: `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.weyl_pythagoras`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.weyl_pythagoras` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The electric charge trace is the sum of the weak and hypercharge traces because the mixed trace vanishes.

**Theorem 1.31 (Hypercharge normalization).**

Lean statement: `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.gut_hypercharge_norm_anom`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.gut_hypercharge_norm_anom` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a nonzero color count N, the ratio of hypercharge trace to weak trace is (N + 2)/N.

**Theorem 1.32 (Three-color normalization).**

Lean statement: `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.gut_hypercharge_norm_three`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.gut_hypercharge_norm_three` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The hypercharge to weak trace ratio is five thirds at three colors.

**Theorem 1.33 (Weak mixing ratio).**

Lean statement: `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.gut_weinberg_anom`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.gut_weinberg_anom` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a nonzero color count N, the ratio of weak trace to electric charge trace is N/(2(N + 1)).

**Theorem 1.34 (Three-color weak mixing ratio).**

Lean statement: `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.gut_weinberg_three_eighths`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.gut_weinberg_three_eighths` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The weak to electric charge trace ratio is three eighths at three colors.

**Theorem 1.35 (Difference between charge conventions).**

Lean statement: `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.weinberg_anom_sub_fixed`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.weinberg_anom_sub_fixed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The anomaly-free ratio minus the fixed-charge ratio is (N² − 9)/(4(N + 1)(9 + 5N)) for every natural color count N.

**Theorem 1.36 (Unique crossing of the curves).**

Lean statement: `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.weinberg_curves_cross_iff_three`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.weinberg_curves_cross_iff_three` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two displayed rational curves coincide exactly at three colors among natural color counts.

**Definition 1.37 (Fifteen-state enumeration).**

Lean statement: `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.sm15State`

*Formalization.* `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.sm15State` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

List three pairs of quark doublet components, three components for each conjugate quark singlet, one pair of lepton doublet components and one conjugate charged lepton.

**Definition 1.38 (Fifteen-state weak weights).**

Lean statement: `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.sm15T3`

*Formalization.* `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.sm15T3` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Assign a weak weight to each color and weak component of the three-color Weyl multiplet enumeration.

**Definition 1.39 (Fifteen-state hypercharges).**

Lean statement: `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.sm15Y`

*Formalization.* `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.sm15Y` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Assign the hypercharge of the corresponding multiplet to each of the fifteen states.

**Definition 1.40 (Fifteen-state electric charges).**

Lean statement: `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.sm15Q`

*Formalization.* `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.sm15Q` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Add the weak weight and hypercharge in each of the fifteen states.

**Theorem 1.41 (Fifteen-state weak trace).**

Lean statement: `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.sm15_trace_T3_sq`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.sm15_trace_T3_sq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The evaluated sum of the squared weak weights is two.

**Theorem 1.42 (Fifteen-state hypercharge trace).**

Lean statement: `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.sm15_trace_Y_sq`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.sm15_trace_Y_sq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The evaluated sum of squared hypercharges is ten thirds.

**Theorem 1.43 (Fifteen-state electric charge trace).**

Lean statement: `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.sm15_trace_Q_sq`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.sm15_trace_Q_sq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The evaluated sum of squared electric charges is sixteen thirds.

**Theorem 1.44 (Fifteen-state mixed trace).**

Lean statement: `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.sm15_trace_T3_Y`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.sm15_trace_T3_Y` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The evaluated sum of weak weight times hypercharge is zero.

**Theorem 1.45 (Fifteen-state hypercharge sum).**

Lean statement: `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.sm15_trace_Y`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.sm15_trace_Y` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The evaluated sum of hypercharges is zero.

**Theorem 1.46 (Fifteen-state cubic hypercharge sum).**

Lean statement: `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.sm15_trace_Y_cube`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.sm15_trace_Y_cube` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The evaluated sum of cubed hypercharges is zero.

**Definition 1.47 (Standard Model hypercharge coefficient).**

Lean statement: `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.smBeta1`

*Formalization.* `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.smBeta1` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Use minus four thirds times the number of generations minus one tenth times the number of Higgs doublets.

**Definition 1.48 (Standard Model weak coefficient).**

Lean statement: `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.smBeta2`

*Formalization.* `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.smBeta2` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Use twenty-two thirds minus four thirds times the number of generations minus one sixth times the number of Higgs doublets.

**Definition 1.49 (Standard Model color coefficient).**

Lean statement: `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.smBeta3`

*Formalization.* `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.smBeta3` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Use eleven minus four thirds times the number of generations.

**Definition 1.50 (Supersymmetric hypercharge coefficient).**

Lean statement: `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.mssmBeta1`

*Formalization.* `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.mssmBeta1` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Use minus thirty-three fifths.

**Definition 1.51 (Supersymmetric weak coefficient).**

Lean statement: `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.mssmBeta2`

*Formalization.* `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.mssmBeta2` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Use minus one.

**Definition 1.52 (Supersymmetric color coefficient).**

Lean statement: `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.mssmBeta3`

*Formalization.* `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.mssmBeta3` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Use three.

**Theorem 1.53 (Standard Model coefficients).**

Lean statement: `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.sm_beta_standard_values`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.sm_beta_standard_values` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Three generations and one Higgs doublet give minus forty-one tenths, nineteen sixths and seven in the hypercharge, weak and color sectors respectively.

**Theorem 1.54 (Generation-independent differences).**

Lean statement: `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.sm_beta_diff_independent_of_ng`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.sm_beta_diff_independent_of_ng` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For H Higgs doublets, the weak-minus-hypercharge, color-minus-weak and color-minus-hypercharge differences are 22/3 − H/15, 11/3 + H/6, and 11 + H/10 respectively.

**Theorem 1.55 (Three-coupling meeting criterion).**

Lean statement: `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.three_coupling_unification_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.three_coupling_unification_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Howard Georgi, Helen R. Quinn, and Steven Weinberg (1974). *Hierarchy of Interactions in Unified Gauge Theories*. DOI: [10.1103/PhysRevLett.33.451](https://doi.org/10.1103/PhysRevLett.33.451). URL: <https://doi.org/10.1103/PhysRevLett.33.451>.

*Commentary.*

For strictly increasing slopes and distinct first two intercepts, the three affine inverse couplings meet exactly when the ratio of successive intercept differences equals the ratio of successive slope differences.

**Theorem 1.56 (Standard Model slope ratio).**

Lean statement: `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.sm_B_ratio_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.sm_B_ratio_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The color-minus-weak difference divided by the weak-minus-hypercharge difference equals 115/218 for three generations and one Higgs doublet.

**Theorem 1.57 (Supersymmetric slope ratio).**

Lean statement: `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.mssm_B_ratio_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.mssm_B_ratio_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The color-minus-weak difference divided by the weak-minus-hypercharge difference equals five sevenths for the supersymmetric coefficients.

**Theorem 1.58 (Slope ratio comparison).**

Lean statement: `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.sm_B_ratio_lt_mssm`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.sm_B_ratio_lt_mssm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Standard Model slope ratio 115/218 is strictly less than the supersymmetric ratio five sevenths.

**Definition 1.59 (Weak mixing angle sine squared).**

Lean statement: `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.weakMixingAngleSq`

*Formalization.* `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.weakMixingAngleSq` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Howard Georgi, Helen R. Quinn, and Steven Weinberg (1974). *Hierarchy of Interactions in Unified Gauge Theories*. DOI: [10.1103/PhysRevLett.33.451](https://doi.org/10.1103/PhysRevLett.33.451). URL: <https://doi.org/10.1103/PhysRevLett.33.451>.

*Commentary.*

Take three fifths of the reciprocal normalized hypercharge inverse coupling and divide by its sum with the reciprocal weak inverse coupling.

**Theorem 1.60 (Running weak mixing angle).**

Lean statement: `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.gut_weinberg_running_formula`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.gut_weinberg_running_formula` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Howard Georgi, Helen R. Quinn, and Steven Weinberg (1974). *Hierarchy of Interactions in Unified Gauge Theories*. DOI: [10.1103/PhysRevLett.33.451](https://doi.org/10.1103/PhysRevLett.33.451). URL: <https://doi.org/10.1103/PhysRevLett.33.451>.

*Commentary.*

For nonzero inverse couplings, the angle sine squared is three times the weak inverse coupling divided by the sum of five times the normalized hypercharge inverse coupling and three times the weak inverse coupling.

**Theorem 1.61 (Weak mixing at unification).**

Lean statement: `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.gut_weinberg_at_unification`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.gut_weinberg_at_unification` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Howard Georgi, Helen R. Quinn, and Steven Weinberg (1974). *Hierarchy of Interactions in Unified Gauge Theories*. DOI: [10.1103/PhysRevLett.33.451](https://doi.org/10.1103/PhysRevLett.33.451). URL: <https://doi.org/10.1103/PhysRevLett.33.451>.

*Commentary.*

Equal nonzero inverse couplings give three eighths for the sine squared.

**Definition 1.62 (Electromagnetic coupling).**

Lean statement: `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.electromagneticCoupling`

*Formalization.* `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.electromagneticCoupling` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Invert the sum of five thirds of the normalized hypercharge inverse coupling and the weak inverse coupling.

**Theorem 1.63 (Georgi–Quinn–Weinberg offset).**

Lean statement: `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.gut_weinberg_running_offset`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.gut_weinberg_running_offset` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Howard Georgi, Helen R. Quinn, and Steven Weinberg (1974). *Hierarchy of Interactions in Unified Gauge Theories*. DOI: [10.1103/PhysRevLett.33.451](https://doi.org/10.1103/PhysRevLett.33.451). URL: <https://doi.org/10.1103/PhysRevLett.33.451>.

*Commentary.*

For two inverse flows with a common reference value, the offset from three eighths is five divided by sixteen pi times the electromagnetic coupling, the weak-minus-hypercharge slope difference, and the log of the scale ratio. The two inverse couplings and the denominator of the electromagnetic coupling are nonzero.

## References

- Truth anchor: `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.SMFermion`
- Truth anchor: `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.asymptotic_freedom_iff`
- Truth anchor: `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.betaOneLoop`
- Truth anchor: `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.colorIndex`
- Truth anchor: `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.colorMultiplicity`
- Truth anchor: `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.color_weak_unification_iff_three`
- Truth anchor: `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.electromagneticCoupling`
- Truth anchor: `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.gut_hypercharge_norm_anom`
- Truth anchor: `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.gut_hypercharge_norm_three`
- Truth anchor: `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.gut_weinberg_anom`
- Truth anchor: `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.gut_weinberg_at_unification`
- Truth anchor: `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.gut_weinberg_running_formula`
- Truth anchor: `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.gut_weinberg_running_offset`
- Truth anchor: `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.gut_weinberg_three_eighths`
- Truth anchor: `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.mssmBeta1`
- Truth anchor: `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.mssmBeta2`
- Truth anchor: `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.mssmBeta3`
- Truth anchor: `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.mssm_B_ratio_eq`
- Truth anchor: `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.qcd_asymptotic_freedom_iff`
- Truth anchor: `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.qcd_six_flavors_beta`
- Truth anchor: `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.rgInvCoupling`
- Truth anchor: `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.rgInvCoupling_hasDerivAt`
- Truth anchor: `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.rg_asymptotic_freedom_limit`
- Truth anchor: `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.rg_confinement_scale_lt`
- Truth anchor: `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.rg_landau_pole_gt`
- Truth anchor: `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.rg_zero_scale_iff`
- Truth anchor: `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.rg_zero_scale_unique`
- Truth anchor: `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.sm15Q`
- Truth anchor: `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.sm15State`
- Truth anchor: `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.sm15T3`
- Truth anchor: `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.sm15Y`
- Truth anchor: `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.sm15_trace_Q_sq`
- Truth anchor: `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.sm15_trace_T3_Y`
- Truth anchor: `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.sm15_trace_T3_sq`
- Truth anchor: `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.sm15_trace_Y`
- Truth anchor: `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.sm15_trace_Y_cube`
- Truth anchor: `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.sm15_trace_Y_sq`
- Truth anchor: `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.smBeta1`
- Truth anchor: `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.smBeta2`
- Truth anchor: `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.smBeta3`
- Truth anchor: `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.sm_B_ratio_eq`
- Truth anchor: `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.sm_B_ratio_lt_mssm`
- Truth anchor: `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.sm_beta_diff_independent_of_ng`
- Truth anchor: `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.sm_beta_standard_values`
- Truth anchor: `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.three_coupling_unification_iff`
- Truth anchor: `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.weakMixingAngleSq`
- Truth anchor: `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.weakMultiplicity`
- Truth anchor: `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.weinberg_anom_sub_fixed`
- Truth anchor: `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.weinberg_curves_cross_iff_three`
- Truth anchor: `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.weylColorSqTrace`
- Truth anchor: `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.weylColorSqTrace_eq`
- Truth anchor: `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.weylQSqTraceAnom`
- Truth anchor: `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.weylQSqTraceAnom_eq`
- Truth anchor: `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.weylT3`
- Truth anchor: `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.weylT3SqTrace`
- Truth anchor: `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.weylT3SqTrace_eq`
- Truth anchor: `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.weylT3YTrace`
- Truth anchor: `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.weylT3YTrace_eq_zero`
- Truth anchor: `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.weylTrace`
- Truth anchor: `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.weylY`
- Truth anchor: `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.weylYSqTraceAnom`
- Truth anchor: `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.weylYSqTraceAnom_eq`
- Truth anchor: `D5/S3/Quantum/Gauge/GaugeUnificationRG4D.weyl_pythagoras`
