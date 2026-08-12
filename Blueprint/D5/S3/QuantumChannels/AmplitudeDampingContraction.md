# Amplitude-Damping Coherence Contraction Endpoints

## Abstract

For amplitude damping on the Bloch axis, the SLD coherence contraction ratio is the constant one minus gamma, while the RLD ratio is bounded by one in the open Bloch interval and tends to one at the pure-state boundary.

**Definition 1.1 (Amplitude damping is affine on the Bloch axis).**

Lean statement: `D5/S3/QuantumChannels/AmplitudeDampingContraction.dampedAxis`

*Formalization.* `D5/S3/QuantumChannels/AmplitudeDampingContraction.dampedAxis` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The amplitude-damping parameter gamma sends an axial Bloch coordinate u to the affine coordinate u prime.

**Definition 1.2 (The SLD radial profile is constant).**

Lean statement: `D5/S3/QuantumChannels/AmplitudeDampingContraction.sldRadialProfile`

*Formalization.* `D5/S3/QuantumChannels/AmplitudeDampingContraction.sldRadialProfile` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The SLD radial profile assigns one to every axial coordinate.

**Definition 1.3 (The KM radial profile is the hyperbolic ratio).**

Lean statement: `D5/S3/QuantumChannels/AmplitudeDampingContraction.kmRadialProfile`

*Formalization.* `D5/S3/QuantumChannels/AmplitudeDampingContraction.kmRadialProfile` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The KM radial profile is artanh of u divided by u away from zero, with its continuous value one assigned at zero.

**Definition 1.4 (The RLD radial profile has a quadratic boundary pole).**

Lean statement: `D5/S3/QuantumChannels/AmplitudeDampingContraction.rldRadialProfile`

*Formalization.* `D5/S3/QuantumChannels/AmplitudeDampingContraction.rldRadialProfile` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The RLD radial profile is the reciprocal of one minus the squared axial coordinate.

**Definition 1.5 (The coherence ratio compares radial profiles before and after damping).**

Lean statement: `D5/S3/QuantumChannels/AmplitudeDampingContraction.coherenceRatio`

*Formalization.* `D5/S3/QuantumChannels/AmplitudeDampingContraction.coherenceRatio` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The axial coherence contraction ratio multiplies the profile quotient at the damped and original coordinates by one minus gamma.

**Definition 1.6 (A pure-state boundary endpoint combines an interior bound and a one-sided limit).**

Lean statement: `D5/S3/QuantumChannels/AmplitudeDampingContraction.HasPureBoundaryEndpoint`

*Formalization.* `D5/S3/QuantumChannels/AmplitudeDampingContraction.HasPureBoundaryEndpoint` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A ratio has boundary endpoint b when it never exceeds b in the open Bloch interval and converges to b from below at the pure-state boundary.

**Theorem 1.7 (SLD is constant and RLD reaches the unit boundary endpoint).**

$$0\le\Gamma<1\Rightarrow(\forall u,eta_{SLD}(\Gamma,u)=1-\Gamma) \land (\forall u\in(-1,1),eta_{RLD}(\Gamma,u)\le1) \land \lim_{u\to1^-}eta_{RLD}(\Gamma,u)=1$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumChannels/AmplitudeDampingContraction.amplitude_damping_sld_rld_endpoints` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For damping parameters from zero inclusive to one exclusive, the constant SLD profile makes its coherence ratio exactly one minus gamma at every axial coordinate. The RLD quotient simplifies inside the open interval to (1+u)/(1+u prime); the damped coordinate is at least u, so this ratio is at most one, and continuity gives the one-sided limit one as u approaches the pure-state boundary.

## References

- Truth anchor: `D5/S3/QuantumChannels/AmplitudeDampingContraction.HasPureBoundaryEndpoint`
- Truth anchor: `D5/S3/QuantumChannels/AmplitudeDampingContraction.amplitude_damping_sld_rld_endpoints`
- Truth anchor: `D5/S3/QuantumChannels/AmplitudeDampingContraction.coherenceRatio`
- Truth anchor: `D5/S3/QuantumChannels/AmplitudeDampingContraction.dampedAxis`
- Truth anchor: `D5/S3/QuantumChannels/AmplitudeDampingContraction.kmRadialProfile`
- Truth anchor: `D5/S3/QuantumChannels/AmplitudeDampingContraction.rldRadialProfile`
- Truth anchor: `D5/S3/QuantumChannels/AmplitudeDampingContraction.sldRadialProfile`
