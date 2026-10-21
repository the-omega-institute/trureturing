# Riemannian gradient dissipation and the full length-action application

## Abstract

Actual tangent speed connects smooth gradient dissipation, metric variation, Riemannian length and kinetic action.

Let E be any finite-dimensional real inner-product space, including dimension zero, and M a connected Hausdorff smooth E-charted manifold with a continuous Riemannian metric on its tangent bundle. Write I for the self model on E and IR for the real-line model. Every metric assertion uses Original172.canonicalMetric (E:=E) (M:=M), which retains the original topology. Tangent norms use the given Riemannian bundle.

The definition actualGradient V p is the inverse Riesz map applied to mfderiv I IR V p. Thus inner(actualGradient V p,w)=dV(p)(w). The definitions kineticAction z T=(extended integral over [0,T] of enorm(mfderiv IR I z t 1)^2)/2 and shortestConnector z T use the actual tangent derivative and pathELength. shortestConnector requires length(z on [0,T])<=length(y on [0,1]) for every C1 competitor y with the same endpoints.

**Theorem 1.1 (Smooth curves are absolutely continuous in the canonical metric).**

Lean statement: `D5/S3/Geometry/Riemannian/GradientDissipation.S1_C1_to_actual_metric_AC`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Riemannian/GradientDissipation.S1_C1_to_actual_metric_AC` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every T>0 and every x : real -> M that is ContMDiffOn IR I 1 on [0,T], x is AbsolutelyContinuousOnInterval on 0..T for the canonical metric. Compactness bounds the norm of the within velocity on the closed interval. The Riemannian endpoint-distance estimate and the path integral formula turn this into a Lipschitz bound for every ordered pair of times. No curve Lipschitz constant is assumed.

**Theorem 1.2 (Riesz-gradient dissipation).**

Lean statement: `D5/S3/Geometry/Riemannian/GradientDissipation.S2_dissipation`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Riemannian/GradientDissipation.S2_dissipation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For T>0, a C1 potential V and a C1 curve x on [0,T], assume the within-derivative equation mfderivWithin IR I x [0,T] t 1=-actualGradient V (x t) at every t in [0,T]. Both actual speed and its square are interval integrable, and V(x(0))-V(x(T)) is the integral of the squared actual speed over 0..T. The manifold chain rule and Riesz pairing give derivative(V composed with x)=-speed^2 at every interior time; continuity and the real fundamental theorem give the identity. This is a consumed analytic helper, used by the quadratic nonattainment proof.

**Theorem 1.3 (Actual AC speed equals the variation density).**

Lean statement: `D5/S3/Geometry/Riemannian/GradientDissipation.actual_AC_speed_variation_length`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Riemannian/GradientDissipation.actual_AC_speed_variation_length` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every T>0 and every canonically metric-AC z, z is manifold differentiable almost everywhere and its ENNReal tangent speed is almost everywhere measurable. Its real tangent speed is interval integrable and equals deriv(variationOnFromTo z [0,T] 0) almost everywhere. pathELength I z 0 T=eVariationOn z [0,T]<infinity, and riemannianEDist I (z 0) (z T)<=pathELength I z 0 T. For every 0<=a<=b<=T, the integral of that same actual tangent speed over a..b equals real variation on [a,b] and bounds the canonical distance of its endpoints. The frozen ACTangentSpeed gives the finite chart partition, tangent formula and metric-speed limit; MetricACSpeed supplies the integral identities. This conjunction is consumed in the length-energy calculation and the strict quadratic argument.

**Theorem 1.4 (Finite-energy length and action transport).**

Lean statement: `D5/S3/Geometry/Riemannian/GradientDissipation.actual_length_energy_real`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Riemannian/GradientDissipation.actual_length_energy_real` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For T>0, a canonically metric-AC z and interval-integrable squared actual speed, length and kineticAction are finite. Their real values are respectively the speed integral and one half the squared-speed integral. Moreover length.toReal^2<=T times the squared-speed integral. The proof transports the actual AC variation identity to real integrals and applies the pinned Holder inequality with the constant function one. This is a consumed helper for the quadratic strictness theorem.

Application to the full original dissipation-length statement. Fix T>0, a C1 potential V and a C1 curve x satisfying the actual within gradient ODE on [0,T], with exactly the geometric data above. Smooth-curve absolute continuity allows the actual speed-variation theorem to be applied to x. Dissipation gives the finite squared-speed integral. The length-energy calculation and distance<=length give V(x(0))-V(x(T)) >= length(x)^2/T >= distance(x(0),x(T))^2/T, with equality of the potential drop and the squared-speed integral. No extra derived estimate is an assumption.

The arbitrary-AC branch uses the same actual objects. For every canonical-metric AC z on [0,T], including curves with infinite squared-speed integral, extended Holder gives length(z)^2<=ofReal(T) times that extended energy. If the energy is infinite, division by two remains infinite and the action lower bound is immediate. In the finite branch positivity of T and finiteness of length permit real conversion and give distance(z(0),z(T))^2/(2*ofReal(T))<=kineticAction z T. This introduces no finite-energy premise into the arbitrary-AC statement.

For the attainment branch, take a C1 z on [0,T] with one constant speed on the open interval, and suppose shortestConnector z T. Given any C1 curve gamma on the unit interval from the defining intrinsic-distance infimum, extend it by composition with projIcc 0 1. This is a genuine C1 competitor with the required endpoints and the same path length. Minimality gives length(z)<=intrinsic distance; the general endpoint bound gives equality. The speed and squared-speed integrals are T*c and T*c^2, so kineticAction z T=distance(z(0),z(T))^2/(2*ofReal(T)). Existence of a shortest curve is not asserted.

Together with ChartComparison and ACTangentSpeed, this application retains the original metric construction, local comparison, chart partition and actual tangent formula. Every positive horizon is allowed; no positive-dimension, nonzero-speed, completeness or extra comparison premise is introduced. Arbitrary total extensions of curves need not be differentiable at either endpoint: the ODE uses within derivatives there and the integral identities use actual derivatives almost everywhere.

The strict quadratic example completes the non-shortest-flow branch: `D5/S3/Geometry/Riemannian/QuadraticGradientFlow.S8_actual_strict_length_and_nonattainment`

## References

- Truth anchor: `D5/S3/Geometry/Riemannian/GradientDissipation.S1_C1_to_actual_metric_AC`
- Truth anchor: `D5/S3/Geometry/Riemannian/GradientDissipation.S2_dissipation`
- Truth anchor: `D5/S3/Geometry/Riemannian/GradientDissipation.actual_AC_speed_variation_length`
- Truth anchor: `D5/S3/Geometry/Riemannian/GradientDissipation.actual_length_energy_real`
- Truth anchor: `D5/S3/Geometry/Riemannian/QuadraticGradientFlow.S8_actual_strict_length_and_nonattainment`
- Dependency: [D5/S3/Geometry/Metric/MetricACSpeed](../Metric/MetricACSpeed.md)
- Dependency: [D5/S3/Geometry/Riemannian/ACTangentSpeed](ACTangentSpeed.md)
- Dependency: [D5/S3/Geometry/Riemannian/ChartComparison](ChartComparison.md)
