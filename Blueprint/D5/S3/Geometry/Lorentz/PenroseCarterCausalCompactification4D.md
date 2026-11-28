# Conformal infinity and the Kruskal extension

## Abstract

Minkowski and de Sitter conformal boundaries, extended Schwarzschild coordinates, and sharp proper time.

The Einstein cylinder has unit spatial radius. The Minkowski factor is the sum of the compactified time and radius cosines. The de Sitter conformal clock runs across an interval of length pi, and the Kruskal coordinates use null product below one to parametrize positive radius.

**Theorem 1.1 (Exact image inequalities).**

Lean statement: `D5/S3/Geometry/Lorentz/PenroseCarterCausalCompactification4D.minkowski_image`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/PenroseCarterCausalCompactification4D.minkowski_image` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. Penrose (1963). *Asymptotic Properties of Fields and Space-Times*. DOI: [10.1103/PhysRevLett.10.66](https://doi.org/10.1103/PhysRevLett.10.66).

*Commentary.*

For nonnegative physical radius the compactified radius is nonnegative and its sum with absolute compactified time is less than pi.

**Theorem 1.2 (Positive interior conformal factor).**

Lean statement: `D5/S3/Geometry/Lorentz/PenroseCarterCausalCompactification4D.conformalFactor_pos`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/PenroseCarterCausalCompactification4D.conformalFactor_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The sum of the time and radius cosines is strictly positive where compactified radius is nonnegative and its sum with absolute time is less than pi.

**Theorem 1.3 (Inverse in the physical coordinates).**

Lean statement: `D5/S3/Geometry/Lorentz/PenroseCarterCausalCompactification4D.minkowski_inverse`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/PenroseCarterCausalCompactification4D.minkowski_inverse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The sine over the sum of cosines formulas recover the original time and radius from the forward map.

**Theorem 1.4 (Inverse in the compactified coordinates).**

Lean statement: `D5/S3/Geometry/Lorentz/PenroseCarterCausalCompactification4D.minkowski_onto`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/PenroseCarterCausalCompactification4D.minkowski_onto` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In the diamond the inverse radius is nonnegative and applying the forward map to the two inverse quantities recovers the compactified point.

**Theorem 1.5 (Image characterized by the diamond).**

Lean statement: `D5/S3/Geometry/Lorentz/PenroseCarterCausalCompactification4D.minkowski_image_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/PenroseCarterCausalCompactification4D.minkowski_image_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The stated diamond inequalities characterize all pairs arising from a real time and nonnegative radius.

**Theorem 1.6 (Arctangent coordinate derivatives).**

Lean statement: `D5/S3/Geometry/Lorentz/PenroseCarterCausalCompactification4D.minkowski_coordinate_derivatives`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/PenroseCarterCausalCompactification4D.minkowski_coordinate_derivatives` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Differentiable physical curves have compactified derivatives given by the sum and difference of the two null coordinate derivatives, each with its arctangent denominator.

**Theorem 1.7 (Four-dimensional metric identity).**

Lean statement: `D5/S3/Geometry/Lorentz/PenroseCarterCausalCompactification4D.minkowski_metric_pullback`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/PenroseCarterCausalCompactification4D.minkowski_metric_pullback` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Minkowski quadratic form, multiplied by the square of the sum of the two cosines, agrees with the Einstein-cylinder quadratic form evaluated on the transformed speeds.

**Theorem 1.8 (Conformal curve derivatives).**

Lean statement: `D5/S3/Geometry/Lorentz/PenroseCarterCausalCompactification4D.minkowski_curve_pullback`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/PenroseCarterCausalCompactification4D.minkowski_curve_pullback` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For differentiable time, radius, and two angular coordinates, the metric identity holds on the curve with the calculated compactified derivatives.

**Theorem 1.9 (Inverse Minkowski curve identity).**

Lean statement: `D5/S3/Geometry/Lorentz/PenroseCarterCausalCompactification4D.minkowski_conformal_metric_pullback`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/PenroseCarterCausalCompactification4D.minkowski_conformal_metric_pullback` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any differentiable cylinder time and radius through the diamond, the inverse-coordinate line element with arbitrary angular speed is the cylinder expression divided by the conformal factor squared.

**Theorem 1.10 (Derivative of the Minkowski factor).**

Lean statement: `D5/S3/Geometry/Lorentz/PenroseCarterCausalCompactification4D.conformalFactor_derivative`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/PenroseCarterCausalCompactification4D.conformalFactor_derivative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The derivative along a curve is the sum of minus sine of each coordinate times its coordinate speed.

**Theorem 1.11 (Null regular-boundary normal).**

Lean statement: `D5/S3/Geometry/Lorentz/PenroseCarterCausalCompactification4D.minkowski_null_boundary`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/PenroseCarterCausalCompactification4D.minkowski_null_boundary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. Penrose (1963). *Asymptotic Properties of Fields and Space-Times*. DOI: [10.1103/PhysRevLett.10.66](https://doi.org/10.1103/PhysRevLett.10.66).

*Commentary.*

The conformal factor vanishes on the two null boundary lines and its normal there has squared Lorentzian length zero.

**Theorem 1.12 (Regular null boundary segments).**

Lean statement: `D5/S3/Geometry/Lorentz/PenroseCarterCausalCompactification4D.minkowski_boundary_regular`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/PenroseCarterCausalCompactification4D.minkowski_boundary_regular` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At each positive radius below pi the two boundary normal vectors are nonzero.

**Theorem 1.13 (Vanishing conformal factor at the corners).**

Lean statement: `D5/S3/Geometry/Lorentz/PenroseCarterCausalCompactification4D.minkowski_three_corners`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/PenroseCarterCausalCompactification4D.minkowski_three_corners` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The conformal factor vanishes at spatial infinity and the past and future timelike endpoints.

**Theorem 1.14 (Critical points at the corners).**

Lean statement: `D5/S3/Geometry/Lorentz/PenroseCarterCausalCompactification4D.minkowski_corner_derivatives`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/PenroseCarterCausalCompactification4D.minkowski_corner_derivatives` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every directional derivative of the conformal factor vanishes at each of the three endpoints.

**Theorem 1.15 (Explicit regular-boundary derivatives).**

Lean statement: `D5/S3/Geometry/Lorentz/PenroseCarterCausalCompactification4D.minkowski_boundary_derivatives`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/PenroseCarterCausalCompactification4D.minkowski_boundary_derivatives` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The conformal derivative along a curve through either boundary line follows from the sine rule with the respective future or past sign.

**Theorem 1.16 (Limits to the three corners).**

Lean statement: `D5/S3/Geometry/Lorentz/PenroseCarterCausalCompactification4D.minkowski_corner_limits`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/PenroseCarterCausalCompactification4D.minkowski_corner_limits` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Along radius zero, the compactified image tends to the future or past timelike corner as time diverges. Along time zero, it tends to spatial infinity as radius grows.

**Theorem 1.17 (Conformal time range).**

Lean statement: `D5/S3/Geometry/Lorentz/PenroseCarterCausalCompactification4D.deSitterEta_range`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/PenroseCarterCausalCompactification4D.deSitterEta_range` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The dimensionless de Sitter clock takes values strictly between minus pi over two and pi over two.

**Theorem 1.18 (De Sitter inverse on the real line).**

Lean statement: `D5/S3/Geometry/Lorentz/PenroseCarterCausalCompactification4D.deSitterTime_left_inverse`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/PenroseCarterCausalCompactification4D.deSitterTime_left_inverse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The logarithm of the half-angle tangent recovers the original dimensionless time.

**Theorem 1.19 (De Sitter inverse on the conformal interval).**

Lean statement: `D5/S3/Geometry/Lorentz/PenroseCarterCausalCompactification4D.deSitterTime_right_inverse`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/PenroseCarterCausalCompactification4D.deSitterTime_right_inverse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exponential-arctangent clock recovers each conformal time strictly inside its interval.

**Theorem 1.20 (Compactification factor and scale factor).**

Lean statement: `D5/S3/Geometry/Lorentz/PenroseCarterCausalCompactification4D.deSitter_cos_cosh`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/PenroseCarterCausalCompactification4D.deSitter_cos_cosh` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The cosine of the conformal time equals the reciprocal of the hyperbolic cosine of the dimensionless time.

**Theorem 1.21 (De Sitter conformal scale).**

Lean statement: `D5/S3/Geometry/Lorentz/PenroseCarterCausalCompactification4D.deSitter_cosh_sec`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/PenroseCarterCausalCompactification4D.deSitter_cosh_sec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The hyperbolic cosine of the dimensionless time is the reciprocal cosine of its conformal time.

**Theorem 1.22 (Forward conformal clock derivative).**

Lean statement: `D5/S3/Geometry/Lorentz/PenroseCarterCausalCompactification4D.deSitterEta_derivative`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/PenroseCarterCausalCompactification4D.deSitterEta_derivative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The derivative of the conformal time is the reciprocal of the hyperbolic cosine of dimensionless time.

**Theorem 1.23 (Inverse conformal clock derivative).**

Lean statement: `D5/S3/Geometry/Lorentz/PenroseCarterCausalCompactification4D.deSitterTime_derivative`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/PenroseCarterCausalCompactification4D.deSitterTime_derivative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In the open conformal interval the derivative of the dimensionless proper-time coordinate is the reciprocal cosine.

**Theorem 1.24 (De Sitter metric in conformal time).**

Lean statement: `D5/S3/Geometry/Lorentz/PenroseCarterCausalCompactification4D.deSitter_weighted_metric_pullback`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/PenroseCarterCausalCompactification4D.deSitter_weighted_metric_pullback` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The full spherical de Sitter metric is conformal to the Einstein cylinder with weight cosine squared divided by the radius squared.

**Theorem 1.25 (Physical de Sitter time and metric).**

Lean statement: `D5/S3/Geometry/Lorentz/PenroseCarterCausalCompactification4D.desitter_conformal_metric_pullback`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/PenroseCarterCausalCompactification4D.desitter_conformal_metric_pullback` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The inverse physical time multiplies the dimensionless inverse by the positive radius. Its squared derivative and the scaled spatial speed satisfy the conformal metric identity with factor cosine divided by radius.

**Theorem 1.26 (Spacelike de Sitter conformal boundary).**

Lean statement: `D5/S3/Geometry/Lorentz/PenroseCarterCausalCompactification4D.deSitter_spacelike_boundary`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/PenroseCarterCausalCompactification4D.deSitter_spacelike_boundary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At the two endpoint times the cosine vanishes and its derivative is a unit normal of negative Lorentzian squared length.

**Theorem 1.27 (Radius-scaled boundary normal).**

Lean statement: `D5/S3/Geometry/Lorentz/PenroseCarterCausalCompactification4D.desitter_scri_spacelike_hypersurface`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/PenroseCarterCausalCompactification4D.desitter_scri_spacelike_hypersurface` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At the two conformal times the cosine divided by the positive de Sitter radius vanishes. Its derivatives are the signed reciprocal radius, and the normal square is strictly negative with value minus one divided by radius squared.

**Theorem 1.28 (Positive boundary metric).**

Lean statement: `D5/S3/Geometry/Lorentz/PenroseCarterCausalCompactification4D.deSitter_boundary_induced_positive`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/PenroseCarterCausalCompactification4D.deSitter_boundary_induced_positive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In regular spherical coordinates the induced quadratic form on a nonzero spatial tangent vector is positive.

**Theorem 1.29 (Limits of the de Sitter conformal clock).**

Lean statement: `D5/S3/Geometry/Lorentz/PenroseCarterCausalCompactification4D.deSitter_boundary_limits`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/PenroseCarterCausalCompactification4D.deSitter_boundary_limits` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The clock approaches minus pi over two toward the past and pi over two toward the future.

**Theorem 1.30 (Closed de Sitter scale derivative).**

Lean statement: `D5/S3/Geometry/Lorentz/PenroseCarterCausalCompactification4D.deSitterScale_derivative`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/PenroseCarterCausalCompactification4D.deSitterScale_derivative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The derivative of the radius times the hyperbolic cosine of proper time over radius is the corresponding hyperbolic sine.

**Theorem 1.31 (Closed Friedmann identity).**

Lean statement: `D5/S3/Geometry/Lorentz/PenroseCarterCausalCompactification4D.deSitter_friedmann`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/PenroseCarterCausalCompactification4D.deSitter_friedmann` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive de Sitter radius the Hubble square and reciprocal scale square sum to the reciprocal radius square.

**Theorem 1.32 (Positive de Sitter factor).**

Lean statement: `D5/S3/Geometry/Lorentz/PenroseCarterCausalCompactification4D.deSitter_conformalFactor_pos`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/PenroseCarterCausalCompactification4D.deSitter_conformalFactor_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Cosine is positive in the open conformal time interval.

**Theorem 1.33 (Causal angular travel bound).**

Lean statement: `D5/S3/Geometry/Lorentz/PenroseCarterCausalCompactification4D.causal_angular_displacement`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/PenroseCarterCausalCompactification4D.causal_angular_displacement` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a spherical curve parameterized by conformal time with nonpositive metric square, the absolute polar-angle change is bounded by the conformal time elapsed.

**Theorem 1.34 (Exact radial causal reachability).**

Lean statement: `D5/S3/Geometry/Lorentz/PenroseCarterCausalCompactification4D.radialReachable_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/PenroseCarterCausalCompactification4D.radialReachable_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A radial causal path exists exactly when its polar displacement in absolute value is at most the time elapsed.

**Theorem 1.35 (Exact spherical polar reachability).**

Lean statement: `D5/S3/Geometry/Lorentz/PenroseCarterCausalCompactification4D.sphericalReachable_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/PenroseCarterCausalCompactification4D.sphericalReachable_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Allowing two additional angular coordinates leaves the polar reachability criterion equal to the radial criterion.

**Theorem 1.36 (Observer diamond at finite endpoint times).**

Lean statement: `D5/S3/Geometry/Lorentz/PenroseCarterCausalCompactification4D.deSitter_causal_diamond`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/PenroseCarterCausalCompactification4D.deSitter_causal_diamond` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* G. W. Gibbons and S. W. Hawking (1977). *Cosmological Event Horizons, Thermodynamics, and Particle Creation*. DOI: [10.1103/PhysRevD.15.2738](https://doi.org/10.1103/PhysRevD.15.2738).

*Commentary.*

For nonnegative polar angle the point lies in the causal diamond between two polar-zero observer times exactly when its polar angle is at most the minimum of the two time separations.

**Theorem 1.37 (Observer diamond for the full lifetime).**

Lean statement: `D5/S3/Geometry/Lorentz/PenroseCarterCausalCompactification4D.desitter_causal_horizon_dichotomy`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/PenroseCarterCausalCompactification4D.desitter_causal_horizon_dichotomy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* G. W. Gibbons and S. W. Hawking (1977). *Cosmological Event Horizons, Thermodynamics, and Particle Creation*. DOI: [10.1103/PhysRevD.15.2738](https://doi.org/10.1103/PhysRevD.15.2738).

*Commentary.*

A point of nonnegative polar angle is reachable to and from finite polar-zero observer times inside the conformal interval precisely when its absolute conformal time plus its polar angle is less than pi over two.

**Theorem 1.38 (Kruskal radial profile).**

Lean statement: `D5/S3/Geometry/Lorentz/PenroseCarterCausalCompactification4D.kruskalF_deriv_and_strict_anti`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/PenroseCarterCausalCompactification4D.kruskalF_deriv_and_strict_anti` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* M. D. Kruskal (1960). *Maximal Extension of Schwarzschild Metric*. DOI: [10.1103/PhysRev.119.1743](https://doi.org/10.1103/PhysRev.119.1743).

*Commentary.*

At positive mass the profile has derivative minus radius times the exponential divided by four mass squared. It is strictly decreasing from value one at zero to negative infinity, vanishes at twice the mass, and bijects positive radii with real values below one.

**Theorem 1.39 (Exterior null coordinate inversion data).**

Lean statement: `D5/S3/Geometry/Lorentz/PenroseCarterCausalCompactification4D.kruskal_uv_product_and_ratio`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/PenroseCarterCausalCompactification4D.kruskal_uv_product_and_ratio` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For exterior radius, the first null coordinate is negative and the second positive. Their product is the radial profile, their signed ratio recovers time by a logarithm, and both equal the exponential expressions of tortoise radius and time.

**Theorem 1.40 (Exterior metric in null coordinates).**

Lean statement: `D5/S3/Geometry/Lorentz/PenroseCarterCausalCompactification4D.kruskal_metric_analytic_pullback`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/PenroseCarterCausalCompactification4D.kruskal_metric_analytic_pullback` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* M. D. Kruskal (1960). *Maximal Extension of Schwarzschild Metric*. DOI: [10.1103/PhysRev.119.1743](https://doi.org/10.1103/PhysRev.119.1743).

*Commentary.*

The exterior Schwarzschild radial-time quadratic form equals minus the Kruskal coefficient times the product of null speeds. The common spherical term is the radius squared times angular speed squared.

**Theorem 1.41 (Analytic radial coefficient and regular horizon).**

Lean statement: `D5/S3/Geometry/Lorentz/PenroseCarterCausalCompactification4D.kruskal_horizon_nonsingular`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/PenroseCarterCausalCompactification4D.kruskal_horizon_nonsingular` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The positive-radius coefficient is positive and its horizon value is sixteen mass squared times the exponential of minus one. Every null product below one has a local analytic inverse of positive radius and an analytic metric coefficient.

**Theorem 1.42 (Strict radial decrease in region II).**

Lean statement: `D5/S3/Geometry/Lorentz/PenroseCarterCausalCompactification4D.kruskal_regionII_trapping_no_escape`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/PenroseCarterCausalCompactification4D.kruskal_regionII_trapping_no_escape` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Positive null coordinates and nonnegative speeds of positive sum give a strictly increasing null product and a strictly decreasing radius below twice the mass.

**Theorem 1.43 (Spacelike singularity hyperbola).**

Lean statement: `D5/S3/Geometry/Lorentz/PenroseCarterCausalCompactification4D.kruskal_singularity_spacelike`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/PenroseCarterCausalCompactification4D.kruskal_singularity_spacelike` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A tangent to the unit timelike hyperbola with nonzero spatial speed has positive Lorentzian square equal to that speed squared divided by the time coordinate squared.

**Theorem 1.44 (Minimal throat on the symmetric slice).**

Lean statement: `D5/S3/Geometry/Lorentz/PenroseCarterCausalCompactification4D.einstein_rosen_bridge_minimal_throat`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/PenroseCarterCausalCompactification4D.einstein_rosen_bridge_minimal_throat` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On the zero Kruskal-time slice the radius is at least twice the mass. Equality occurs exactly at the zero spatial coordinate.

**Theorem 1.45 (Sharp interior proper-time bound).**

Lean statement: `D5/S3/Geometry/Lorentz/PenroseCarterCausalCompactification4D.schwarzschild_interior_proper_time_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/PenroseCarterCausalCompactification4D.schwarzschild_interior_proper_time_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The cycloid gives exact radius and proper-time derivatives and the interior rest-geodesic equation. Its duration is pi times the mass, and an endpoint-continuous competing clock obeying the interior speed inequality has duration at most that value.

**Theorem 1.46 (Inverse radial speed bound).**

Lean statement: `D5/S3/Geometry/Lorentz/PenroseCarterCausalCompactification4D.schwarzschild_inverse_proper_time_derivative`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/PenroseCarterCausalCompactification4D.schwarzschild_inverse_proper_time_derivative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If an interior proper-time radial speed has square at least twice the mass over radius minus one, its reciprocal absolute value is at most the reciprocal square root of that expression.

## References

- Truth anchor: `D5/S3/Geometry/Lorentz/PenroseCarterCausalCompactification4D.causal_angular_displacement`
- Truth anchor: `D5/S3/Geometry/Lorentz/PenroseCarterCausalCompactification4D.conformalFactor_derivative`
- Truth anchor: `D5/S3/Geometry/Lorentz/PenroseCarterCausalCompactification4D.conformalFactor_pos`
- Truth anchor: `D5/S3/Geometry/Lorentz/PenroseCarterCausalCompactification4D.deSitterEta_derivative`
- Truth anchor: `D5/S3/Geometry/Lorentz/PenroseCarterCausalCompactification4D.deSitterEta_range`
- Truth anchor: `D5/S3/Geometry/Lorentz/PenroseCarterCausalCompactification4D.deSitterScale_derivative`
- Truth anchor: `D5/S3/Geometry/Lorentz/PenroseCarterCausalCompactification4D.deSitterTime_derivative`
- Truth anchor: `D5/S3/Geometry/Lorentz/PenroseCarterCausalCompactification4D.deSitterTime_left_inverse`
- Truth anchor: `D5/S3/Geometry/Lorentz/PenroseCarterCausalCompactification4D.deSitterTime_right_inverse`
- Truth anchor: `D5/S3/Geometry/Lorentz/PenroseCarterCausalCompactification4D.deSitter_boundary_induced_positive`
- Truth anchor: `D5/S3/Geometry/Lorentz/PenroseCarterCausalCompactification4D.deSitter_boundary_limits`
- Truth anchor: `D5/S3/Geometry/Lorentz/PenroseCarterCausalCompactification4D.deSitter_causal_diamond`
- Truth anchor: `D5/S3/Geometry/Lorentz/PenroseCarterCausalCompactification4D.deSitter_conformalFactor_pos`
- Truth anchor: `D5/S3/Geometry/Lorentz/PenroseCarterCausalCompactification4D.deSitter_cos_cosh`
- Truth anchor: `D5/S3/Geometry/Lorentz/PenroseCarterCausalCompactification4D.deSitter_cosh_sec`
- Truth anchor: `D5/S3/Geometry/Lorentz/PenroseCarterCausalCompactification4D.deSitter_friedmann`
- Truth anchor: `D5/S3/Geometry/Lorentz/PenroseCarterCausalCompactification4D.deSitter_spacelike_boundary`
- Truth anchor: `D5/S3/Geometry/Lorentz/PenroseCarterCausalCompactification4D.deSitter_weighted_metric_pullback`
- Truth anchor: `D5/S3/Geometry/Lorentz/PenroseCarterCausalCompactification4D.desitter_causal_horizon_dichotomy`
- Truth anchor: `D5/S3/Geometry/Lorentz/PenroseCarterCausalCompactification4D.desitter_conformal_metric_pullback`
- Truth anchor: `D5/S3/Geometry/Lorentz/PenroseCarterCausalCompactification4D.desitter_scri_spacelike_hypersurface`
- Truth anchor: `D5/S3/Geometry/Lorentz/PenroseCarterCausalCompactification4D.einstein_rosen_bridge_minimal_throat`
- Truth anchor: `D5/S3/Geometry/Lorentz/PenroseCarterCausalCompactification4D.kruskalF_deriv_and_strict_anti`
- Truth anchor: `D5/S3/Geometry/Lorentz/PenroseCarterCausalCompactification4D.kruskal_horizon_nonsingular`
- Truth anchor: `D5/S3/Geometry/Lorentz/PenroseCarterCausalCompactification4D.kruskal_metric_analytic_pullback`
- Truth anchor: `D5/S3/Geometry/Lorentz/PenroseCarterCausalCompactification4D.kruskal_regionII_trapping_no_escape`
- Truth anchor: `D5/S3/Geometry/Lorentz/PenroseCarterCausalCompactification4D.kruskal_singularity_spacelike`
- Truth anchor: `D5/S3/Geometry/Lorentz/PenroseCarterCausalCompactification4D.kruskal_uv_product_and_ratio`
- Truth anchor: `D5/S3/Geometry/Lorentz/PenroseCarterCausalCompactification4D.minkowski_boundary_derivatives`
- Truth anchor: `D5/S3/Geometry/Lorentz/PenroseCarterCausalCompactification4D.minkowski_boundary_regular`
- Truth anchor: `D5/S3/Geometry/Lorentz/PenroseCarterCausalCompactification4D.minkowski_conformal_metric_pullback`
- Truth anchor: `D5/S3/Geometry/Lorentz/PenroseCarterCausalCompactification4D.minkowski_coordinate_derivatives`
- Truth anchor: `D5/S3/Geometry/Lorentz/PenroseCarterCausalCompactification4D.minkowski_corner_derivatives`
- Truth anchor: `D5/S3/Geometry/Lorentz/PenroseCarterCausalCompactification4D.minkowski_corner_limits`
- Truth anchor: `D5/S3/Geometry/Lorentz/PenroseCarterCausalCompactification4D.minkowski_curve_pullback`
- Truth anchor: `D5/S3/Geometry/Lorentz/PenroseCarterCausalCompactification4D.minkowski_image`
- Truth anchor: `D5/S3/Geometry/Lorentz/PenroseCarterCausalCompactification4D.minkowski_image_iff`
- Truth anchor: `D5/S3/Geometry/Lorentz/PenroseCarterCausalCompactification4D.minkowski_inverse`
- Truth anchor: `D5/S3/Geometry/Lorentz/PenroseCarterCausalCompactification4D.minkowski_metric_pullback`
- Truth anchor: `D5/S3/Geometry/Lorentz/PenroseCarterCausalCompactification4D.minkowski_null_boundary`
- Truth anchor: `D5/S3/Geometry/Lorentz/PenroseCarterCausalCompactification4D.minkowski_onto`
- Truth anchor: `D5/S3/Geometry/Lorentz/PenroseCarterCausalCompactification4D.minkowski_three_corners`
- Truth anchor: `D5/S3/Geometry/Lorentz/PenroseCarterCausalCompactification4D.radialReachable_iff`
- Truth anchor: `D5/S3/Geometry/Lorentz/PenroseCarterCausalCompactification4D.schwarzschild_interior_proper_time_bound`
- Truth anchor: `D5/S3/Geometry/Lorentz/PenroseCarterCausalCompactification4D.schwarzschild_inverse_proper_time_derivative`
- Truth anchor: `D5/S3/Geometry/Lorentz/PenroseCarterCausalCompactification4D.sphericalReachable_iff`
- Dependency: [D5/S3/Geometry/Lorentz/BlackHoleThermodynamics4D](BlackHoleThermodynamics4D.md)
- Dependency: [D5/S3/Geometry/Lorentz/FLRWCosmologyFriedmann4D](FLRWCosmologyFriedmann4D.md)
