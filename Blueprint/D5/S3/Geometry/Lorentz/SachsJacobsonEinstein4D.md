# Sachs focusing and the local horizon equation of state

## Abstract

Null optical focusing, the local horizon Clausius limit, and the Einstein equation on a connected chart.

The twist-free optical equations govern the expansion, the complex trace-free shear and the area radius of a two-dimensional screen. At an equilibrium horizon cross-section the expansion and shear vanish, so the leading area change along a past-directed interval is controlled by Ricci curvature. Comparing it with the heat flux gives the null Einstein equation. The full null cone determines a symmetric tensor up to the metric. Contracted Bianchi and stress-energy conservation fix that remaining coefficient up to a constant.

**Definition 1.1 (Optical fields).**

Lean statement: `D5/S3/Geometry/Lorentz/SachsJacobsonEinstein4D.OpticalData`

*Formalization.* `D5/S3/Geometry/Lorentz/SachsJacobsonEinstein4D.OpticalData` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The affine parameter is real. Expansion, radius and Ricci contraction are real-valued, while shear and trace-free tidal driving are complex-valued.

**Definition 1.2 (Focusing coefficient).**

$$\forall o \in \operatorname{OpticalData},\; \forall t \in \mathbb{R},\; \operatorname{focusing}\left(o, t\right) = \frac{\operatorname{normSq}\left(\operatorname{shear}\left(o, t\right)\right) + \operatorname{ricciTerm}\left(o, t\right)}{2}$$

*Formalization.* `D5/S3/Geometry/Lorentz/SachsJacobsonEinstein4D.focusing` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Half the sum of complex shear norm squared and the full Ricci contraction gives the second-order focusing coefficient.

**Definition 1.3 (Sachs optical equations).**

Lean statement: `D5/S3/Geometry/Lorentz/SachsJacobsonEinstein4D.SolvesOn`

*Formalization.* `D5/S3/Geometry/Lorentz/SachsJacobsonEinstein4D.SolvesOn` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At every affine parameter t in the specified set, the expansion derivative is −θ²/2−|σ|²−Rkk, the shear derivative is −θσ−Ψ, and the radius derivative is θρ/2. The derivatives are taken for functions globally typed on the real line, so evaluation at the endpoints of a closed interval is meaningful.

**Definition 1.4 (Area from radius).**

$$\forall o \in \operatorname{OpticalData},\; \forall t \in \mathbb{R},\; \operatorname{area}\left(o, t\right) = \operatorname{radius}\left(o, t\right)^{2}$$

*Formalization.* `D5/S3/Geometry/Lorentz/SachsJacobsonEinstein4D.area` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The cross-sectional area is the square of the area radius.

**Definition 1.5 (Optical radius slope).**

$$\forall o \in \operatorname{OpticalData},\; \forall t \in \mathbb{R},\; \operatorname{radiusSlope}\left(o, t\right) = \frac{\operatorname{expansion}\left(o, t\right) \cdot \operatorname{radius}\left(o, t\right)}{2}$$

*Formalization.* `D5/S3/Geometry/Lorentz/SachsJacobsonEinstein4D.radiusSlope` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The affine radius slope is expansion times radius divided by two.

**Theorem 1.6 (Area derivative).**

Lean statement: `D5/S3/Geometry/Lorentz/SachsJacobsonEinstein4D.hasDerivAt_area`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/SachsJacobsonEinstein4D.hasDerivAt_area` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At each parameter of a solution, the area derivative equals expansion times area by the derivative of a square.

**Theorem 1.7 (Linearized Sachs equation).**

Lean statement: `D5/S3/Geometry/Lorentz/SachsJacobsonEinstein4D.hasDerivAt_radiusSlope`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/SachsJacobsonEinstein4D.hasDerivAt_radiusSlope` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At each parameter of a solution the derivative of the radius slope equals minus the focusing coefficient times radius. The product rule and expansion equation cancel the terms quadratic in expansion.

**Theorem 1.8 (Second-order focusing on an open set).**

$$\forall o \in \operatorname{OpticalData},\; \forall J \in \operatorname{Set}\left(\mathbb{R}\right),\; \forall t \in \mathbb{R},\; ((\operatorname{SolvesOn}\left(o, J\right) \land (\operatorname{IsOpen}\left(J\right) \land (t \in J))) \implies \operatorname{deriv}\left(\operatorname{deriv}\left(\operatorname{radius}\left(o\right)\right), t\right) + \operatorname{focusing}\left(o, t\right) \cdot \operatorname{radius}\left(o, t\right) = 0)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/SachsJacobsonEinstein4D.area_radius_focusing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual derivative of the radius agrees locally with the explicit optical radius slope. Therefore the second derivative plus the focusing coefficient times radius vanishes at each parameter of an open solution set.

**Theorem 1.9 (Null energy condition and concavity).**

Lean statement: `D5/S3/Geometry/Lorentz/SachsJacobsonEinstein4D.optical_nec_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/SachsJacobsonEinstein4D.optical_nec_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On a convex solution set with nonnegative Ricci contraction and radius, the focusing coefficient is nonnegative, the radius slope derivative is nonpositive, and the expansion derivative is at most −θ²/2. Derivative comparison gives antitonicity of the expansion and radius slope, and concavity of the radius.

**Theorem 1.10 (Inverse expansion estimate).**

Lean statement: `D5/S3/Geometry/Lorentz/SachsJacobsonEinstein4D.reciprocal_expansion_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/SachsJacobsonEinstein4D.reciprocal_expansion_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On a closed interval from zero to t with t nonnegative, an initially negative expansion under nonnegative Ricci contraction stays negative. Differentiating its inverse gives a lower derivative bound of one half. Thus its final inverse is at least its initial inverse plus t/2.

**Theorem 1.11 (Finite-affine focusing bound).**

Lean statement: `D5/S3/Geometry/Lorentz/SachsJacobsonEinstein4D.no_positive_optics_through_focal_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/SachsJacobsonEinstein4D.no_positive_optics_through_focal_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A regular optical solution throughout the half-open interval from zero to L with initially negative expansion and nonnegative Ricci contraction satisfies L ≤ 2/|θ(0)|. If that endpoint lay strictly inside the solution interval, the inverse expansion estimate would force a nonnegative inverse of a negative expansion.

**Theorem 1.12 (A continued radius reaches zero).**

Lean statement: `D5/S3/Geometry/Lorentz/SachsJacobsonEinstein4D.radius_zero_le_focal_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/SachsJacobsonEinstein4D.radius_zero_le_focal_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For negative initial expansion and positive initial radius, suppose the radius is continuous through the focal bound, and the optical equations and nonnegative Ricci contraction hold at every positive-radius point. A zero occurs at some strictly positive parameter no greater than the focal bound. In the absence of such a zero, continuity and the intermediate value theorem force the radius to remain positive throughout. The inverse expansion contradiction then occurs at the focal bound itself.

**Definition 1.13 (Tangent radius deficit).**

$$\forall o \in \operatorname{OpticalData},\; \forall t \in \mathbb{R},\; \operatorname{tangentDelay}\left(o, t\right) = \operatorname{radius}\left(o, 0\right) + t \cdot \operatorname{radiusSlope}\left(o, 0\right) - \operatorname{radius}\left(o, t\right)$$

*Formalization.* `D5/S3/Geometry/Lorentz/SachsJacobsonEinstein4D.tangentDelay` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The radius at zero plus t times its initial optical slope minus the radius at t defines the tangent deficit.

**Theorem 1.14 (Nonnegative focusing delay).**

Lean statement: `D5/S3/Geometry/Lorentz/SachsJacobsonEinstein4D.tangent_delay_nonneg`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/SachsJacobsonEinstein4D.tangent_delay_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

With nonnegative radius and Ricci contraction on the closed interval from zero to t, the tangent deficit starts at zero and has nonnegative derivative. Hence the final tangent deficit is nonnegative.

**Theorem 1.15 (Weyl-driven shear).**

Lean statement: `D5/S3/Geometry/Lorentz/SachsJacobsonEinstein4D.weyl_generates_shear`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/SachsJacobsonEinstein4D.weyl_generates_shear` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At a solution point with zero shear and nonzero tidal input, the shear derivative is minus the tide and is nonzero. The difference quotient stays nonzero sufficiently near the point in the deleted neighborhood. The shear there is consequently nonzero, and wherever the solution has positive radius and nonnegative Ricci contraction the radius slope has strictly negative derivative. This applies in vacuum.

**Theorem 1.16 (Optical delay in the clock-area bound).**

Lean statement: `D5/S3/Geometry/Lorentz/SachsJacobsonEinstein4D.clock_deficit_of_optics`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/SachsJacobsonEinstein4D.clock_deficit_of_optics` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a nonempty finite family of generator samples with positive weights, positive radius throughout each closed past-to-sample interval from zero, nonnegative Ricci contraction and cutoff ε below one, use the radius as the corner density and its tangent deficit as the clock delay. The resulting clock is at least (1−ε) times the square root of weighted area divided by total weight. Equality holds exactly when all sampled delays vanish and all sampled radii agree.

**Definition 1.17 (Bilinear tensor evaluation).**

Lean statement: `D5/S3/Geometry/Lorentz/SachsJacobsonEinstein4D.evalMat`

*Formalization.* `D5/S3/Geometry/Lorentz/SachsJacobsonEinstein4D.evalMat` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Contract both vector arguments against the covariant four-by-four matrix entries by a double finite sum.

**Theorem 1.18 (Ricci trace and complex Weyl source).**

Lean statement: `D5/S3/Geometry/Lorentz/SachsJacobsonEinstein4D.screen_trace_and_tide`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/SachsJacobsonEinstein4D.screen_trace_and_tide` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Urbantke (1984). *On integrability properties of SU(2) Yang-Mills fields. I. Infinitesimal part*. DOI: [10.1063/1.526402](https://doi.org/10.1063/1.526402). URL: <https://doi.org/10.1063/1.526402>.

*Commentary.*

Scale the chart generator by a and the chart tidal matrix by a². Its trace equals the Ricci contraction on the scaled generator. Subtraction of half this contraction from each diagonal entry leaves the scaled Weyl tide. The squared scale times the complex Weyl tide is twice the first diagonal component plus twice i times the first off-diagonal component of that scaled Weyl matrix.

**Theorem 1.19 (Twist-free screen Riccati components).**

Lean statement: `D5/S3/Geometry/Lorentz/SachsJacobsonEinstein4D.screen_riccati_components`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/SachsJacobsonEinstein4D.screen_riccati_components` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Write the optical matrix with diagonal entries θ/2+s and θ/2−s and off-diagonal entries u. If the derivative matrix equals minus the matrix square minus a tidal matrix P of trace Rkk, adding the two diagonal equations gives θ′=−θ²/2−2(s²+u²)−Rkk. Subtracting them and using the off-diagonal equation gives the complex shear equation for σ=√2(s+iu), with source √2(P₀₀−Rkk/2+iP₀₁).

**Definition 1.20 (Past horizon area variation).**

$$\forall o \in \operatorname{OpticalData},\; \forall e \in \mathbb{R},\; \operatorname{areaChange}\left(o, e\right) = \operatorname{area}\left(o, 0\right) - \operatorname{area}\left(o, -e\right)$$

*Formalization.* `D5/S3/Geometry/Lorentz/SachsJacobsonEinstein4D.areaChange` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For affine width e, the area at zero minus the area at −e defines the horizon area change.

**Definition 1.21 (Weighted past horizon heat flux).**

Lean statement: `D5/S3/Geometry/Lorentz/SachsJacobsonEinstein4D.heat`

*Formalization.* `D5/S3/Geometry/Lorentz/SachsJacobsonEinstein4D.heat` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For real surface gravity κ and heat flux density T, integrate −t T(t) A(t) from −e to zero and multiply by κ.

**Theorem 1.22 (Normalized area and heat limits).**

Lean statement: `D5/S3/Geometry/Lorentz/SachsJacobsonEinstein4D.horizon_first_variation`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/SachsJacobsonEinstein4D.horizon_first_variation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* T. Jacobson (1995). *Thermodynamics of Spacetime: The Einstein Equation of State*. DOI: [10.1103/PhysRevLett.75.1260](https://doi.org/10.1103/PhysRevLett.75.1260). URL: <https://doi.org/10.1103/PhysRevLett.75.1260>.

*Commentary.*

Take a solution on a past segment of positive width, with zero expansion and shear at zero, positive initial radius and continuous heat flux on the segment. Normalize both variations by A(0)e²/2. As e decreases to zero through positive values, these ratios tend respectively to Rkk(0) and κ T(0). The divided slope of the expansion is continuous at zero and has value −Rkk(0). The fundamental theorem of calculus rewrites the area change as the same weighted integral used for the heat flux. Bounds on the continuous integrand near zero yield the two limits since the integral of −t is e²/2.

**Theorem 1.23 (Clausius implies the null Einstein equation).**

Lean statement: `D5/S3/Geometry/Lorentz/SachsJacobsonEinstein4D.null_identity_of_clausius`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/SachsJacobsonEinstein4D.null_identity_of_clausius` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* T. Jacobson (1995). *Thermodynamics of Spacetime: The Einstein Equation of State*. DOI: [10.1103/PhysRevLett.75.1260](https://doi.org/10.1103/PhysRevLett.75.1260). URL: <https://doi.org/10.1103/PhysRevLett.75.1260>.

*Commentary.*

Under the same horizon assumptions and with positive κ, ℏ and entropy density η, suppose every positive sufficiently short segment satisfies heat = ℏκη/(2π) times area change. Normalize by the positive area-width factor and use the two limits. Cancelling κ gives Rkk(0)−2πT(0)/(ℏη)=0.

**Theorem 1.24 (Metric proportionality from null vanishing).**

Lean statement: `D5/S3/Geometry/Lorentz/SachsJacobsonEinstein4D.symmetric_eq_metric_of_null`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/SachsJacobsonEinstein4D.symmetric_eq_metric_of_null` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For symmetric real four-by-four matrices S and g, suppose an invertible real linear frame pulls the quadratic form of g back to the Lorentzian form with signature (−+++). If the quadratic form of S vanishes on every null vector of g, transport it through the frame and the time-space splitting to apply Minkowski null-cone rigidity. The certificate uses signature (+−−−), so its coefficient changes sign. Polarization on pairs of coordinate vectors then yields S=f g for a real f.

**Definition 1.25 (Covariant tensor fields).**

Lean statement: `D5/S3/Geometry/Lorentz/SachsJacobsonEinstein4D.TensorField`

*Formalization.* `D5/S3/Geometry/Lorentz/SachsJacobsonEinstein4D.TensorField` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A covariant tensor field assigns a real four-by-four matrix to each vector in real four-dimensional coordinate space.

**Definition 1.26 (Coordinate partial derivative).**

Lean statement: `D5/S3/Geometry/Lorentz/SachsJacobsonEinstein4D.coordinateDerivative`

*Formalization.* `D5/S3/Geometry/Lorentz/SachsJacobsonEinstein4D.coordinateDerivative` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Evaluate the real Fréchet derivative of the scalar field on the specified coordinate unit vector.

**Definition 1.27 (Covariant divergence).**

Lean statement: `D5/S3/Geometry/Lorentz/SachsJacobsonEinstein4D.tensorDivergence`

*Formalization.* `D5/S3/Geometry/Lorentz/SachsJacobsonEinstein4D.tensorDivergence` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For inverse metric entries g^{ma} and connection coefficients Γ^d_ma, the b component is the sum over m and a of g^{ma} times the partial derivative of S_ab in direction m minus the connection sums Γ^d_ma S_db and Γ^d_mb S_ad.

**Definition 1.28 (Metric trace).**

Lean statement: `D5/S3/Geometry/Lorentz/SachsJacobsonEinstein4D.metricTrace`

*Formalization.* `D5/S3/Geometry/Lorentz/SachsJacobsonEinstein4D.metricTrace` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The trace is the double sum of g^{ma} S_am over coordinate indices m and a.

**Definition 1.29 (Differentiability on a chart).**

Lean statement: `D5/S3/Geometry/Lorentz/SachsJacobsonEinstein4D.ComponentDiff`

*Formalization.* `D5/S3/Geometry/Lorentz/SachsJacobsonEinstein4D.ComponentDiff` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each of the sixteen real-valued tensor entries is differentiable on the specified set.

**Theorem 1.30 (Einstein equation with constant cosmological term).**

Lean statement: `D5/S3/Geometry/Lorentz/SachsJacobsonEinstein4D.jacobson_einstein_on`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/SachsJacobsonEinstein4D.jacobson_einstein_on` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* T. Jacobson (1995). *Thermodynamics of Spacetime: The Einstein Equation of State*. DOI: [10.1103/PhysRevLett.75.1260](https://doi.org/10.1103/PhysRevLett.75.1260). URL: <https://doi.org/10.1103/PhysRevLett.75.1260>.

*Acknowledgement.* H. Urbantke (1984). *On integrability properties of SU(2) Yang-Mills fields. I. Infinitesimal part*. DOI: [10.1063/1.526402](https://doi.org/10.1063/1.526402). URL: <https://doi.org/10.1063/1.526402>.

*Commentary.*

On an open preconnected chart take differentiable component fields g, its inverse, Ricci R and stress T, with symmetric g, R and T, a pointwise Lorentz frame, and a metric-compatible connection. At each point and nonzero null vector require an equilibrium past optical pencil of positive width and positive surface gravity with continuous heat flux, positive initial radius, initial Ricci and flux values equal to the contractions of R and T, and the Clausius identity on every short segment. Assume the contracted Bianchi identity and vanishing stress divergence. The null Clausius identity and metric proportionality give R−cT=f g for c=2π/(ℏη), with f equal to the metric trace of R−cT divided by four. Metric compatibility and the product rule give div(f g)=df. Bianchi and conservation imply d(f−Rscal/2)=0. The open preconnected chart makes this difference constant, yielding R−(Rscal/2)g+Λg=8πGT for a single real Λ and G=1/(4ℏη).

## References

- Truth anchor: `D5/S3/Geometry/Lorentz/SachsJacobsonEinstein4D.ComponentDiff`
- Truth anchor: `D5/S3/Geometry/Lorentz/SachsJacobsonEinstein4D.OpticalData`
- Truth anchor: `D5/S3/Geometry/Lorentz/SachsJacobsonEinstein4D.SolvesOn`
- Truth anchor: `D5/S3/Geometry/Lorentz/SachsJacobsonEinstein4D.TensorField`
- Truth anchor: `D5/S3/Geometry/Lorentz/SachsJacobsonEinstein4D.area`
- Truth anchor: `D5/S3/Geometry/Lorentz/SachsJacobsonEinstein4D.areaChange`
- Truth anchor: `D5/S3/Geometry/Lorentz/SachsJacobsonEinstein4D.area_radius_focusing`
- Truth anchor: `D5/S3/Geometry/Lorentz/SachsJacobsonEinstein4D.clock_deficit_of_optics`
- Truth anchor: `D5/S3/Geometry/Lorentz/SachsJacobsonEinstein4D.coordinateDerivative`
- Truth anchor: `D5/S3/Geometry/Lorentz/SachsJacobsonEinstein4D.evalMat`
- Truth anchor: `D5/S3/Geometry/Lorentz/SachsJacobsonEinstein4D.focusing`
- Truth anchor: `D5/S3/Geometry/Lorentz/SachsJacobsonEinstein4D.hasDerivAt_area`
- Truth anchor: `D5/S3/Geometry/Lorentz/SachsJacobsonEinstein4D.hasDerivAt_radiusSlope`
- Truth anchor: `D5/S3/Geometry/Lorentz/SachsJacobsonEinstein4D.heat`
- Truth anchor: `D5/S3/Geometry/Lorentz/SachsJacobsonEinstein4D.horizon_first_variation`
- Truth anchor: `D5/S3/Geometry/Lorentz/SachsJacobsonEinstein4D.jacobson_einstein_on`
- Truth anchor: `D5/S3/Geometry/Lorentz/SachsJacobsonEinstein4D.metricTrace`
- Truth anchor: `D5/S3/Geometry/Lorentz/SachsJacobsonEinstein4D.no_positive_optics_through_focal_bound`
- Truth anchor: `D5/S3/Geometry/Lorentz/SachsJacobsonEinstein4D.null_identity_of_clausius`
- Truth anchor: `D5/S3/Geometry/Lorentz/SachsJacobsonEinstein4D.optical_nec_bounds`
- Truth anchor: `D5/S3/Geometry/Lorentz/SachsJacobsonEinstein4D.radiusSlope`
- Truth anchor: `D5/S3/Geometry/Lorentz/SachsJacobsonEinstein4D.radius_zero_le_focal_bound`
- Truth anchor: `D5/S3/Geometry/Lorentz/SachsJacobsonEinstein4D.reciprocal_expansion_bound`
- Truth anchor: `D5/S3/Geometry/Lorentz/SachsJacobsonEinstein4D.screen_riccati_components`
- Truth anchor: `D5/S3/Geometry/Lorentz/SachsJacobsonEinstein4D.screen_trace_and_tide`
- Truth anchor: `D5/S3/Geometry/Lorentz/SachsJacobsonEinstein4D.symmetric_eq_metric_of_null`
- Truth anchor: `D5/S3/Geometry/Lorentz/SachsJacobsonEinstein4D.tangentDelay`
- Truth anchor: `D5/S3/Geometry/Lorentz/SachsJacobsonEinstein4D.tangent_delay_nonneg`
- Truth anchor: `D5/S3/Geometry/Lorentz/SachsJacobsonEinstein4D.tensorDivergence`
- Truth anchor: `D5/S3/Geometry/Lorentz/SachsJacobsonEinstein4D.weyl_generates_shear`
- Dependency: [D5/S0/Certificates/MinkowskiNullConeRigidity](../../../S0/Certificates/MinkowskiNullConeRigidity.md)
- Dependency: [D5/S3/Geometry/Lorentz/WeylNullScreen](WeylNullScreen.md)
- Dependency: [D5/S3/Quantum/Analysis/NullConeGravity/NullConeClockAreaBound](../../Quantum/Analysis/NullConeGravity/NullConeClockAreaBound.md)
