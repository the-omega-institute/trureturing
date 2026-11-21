# Purity of two phase encodings

## Abstract

The best uniform purity-loss coefficient between the singleton and product phase encodings.

Encode a choice of n phases by the n + 1 amplitudes consisting of one and the phases themselves. A second encoding uses all products indexed by subsets. Its normalized vector is a tensor product of n equatorial qubit vectors. Both squared overlaps depend only on the coordinatewise relative phases.

**Definition 1.1 (Singleton phase overlap).**

$$A(u)=\frac{\left|1+\sum_{k}u_{k}\right|^{2}}{(n+1)^{2}}$$

*Formalization.* `D5/S3/Quantum/PureState/PhaseProductFidelity.simplex` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For unit phases this is the squared inner product with the constant phase vector. For a pair of inputs, take u to be their coordinatewise relative phase.

**Definition 1.2 (Product phase overlap).**

$$B(u)=\prod_{k}\frac{1+\Re u_{k}}{2}$$

*Formalization.* `D5/S3/Quantum/PureState/PhaseProductFidelity.cube` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each unit complex coordinate contributes the squared overlap of the two equatorial qubit states in that tensor factor.

**Definition 1.3 (Ensemble purity loss).**

$$L(F,p,v)=\sum_{i,j}p_{i}p_{j}(1-F(\overline{v_{i}}v_{j}))$$

*Formalization.* `D5/S3/Quantum/PureState/PhaseProductFidelity.mixedDeficit` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The product of the conjugated row and the other row is coordinatewise. Drawing two independent indices from the same distribution gives pairwise weights p_i p_j. For normalized states this average loss is one minus the purity of their mixture.

**Theorem 1.4 (Sharp comparison for all finite phase ensembles).**

$$\forall n\ge1,C\in\mathbb{R},\\(\forall m,p,v,(p_{i}\ge0,\sum_{i}p_{i}=1,\left|v_{ik}\right|=1)\Rightarrow L(B,p,v)\le CL(A,p,v))\Leftrightarrow\frac{(n+1)^{2}}{4}\le C$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/PureState/PhaseProductFidelity.mixed_coefficient_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Here n is a positive integer, m is an arbitrary finite ensemble size, p is a probability vector of length m, and v is an m by n array of unit complex phases. All coordinate conditions range over their full index sets.

The loss of a product of factors in the unit interval is at most the sum of their individual losses. The modulus of the sum of n phases is at most n. Expanding the singleton overlap then gives the displayed coefficient for each pair and multiplication by the nonnegative pair weights preserves it.

For sharpness, give equal weights to the constant row and a row whose coordinates are all the same phase. As this phase approaches one, the ratio of the two losses tends to the claimed coefficient. For two independent phases the coefficient is nine quarters.

## References

- Truth anchor: `D5/S3/Quantum/PureState/PhaseProductFidelity.cube`
- Truth anchor: `D5/S3/Quantum/PureState/PhaseProductFidelity.mixedDeficit`
- Truth anchor: `D5/S3/Quantum/PureState/PhaseProductFidelity.mixed_coefficient_iff`
- Truth anchor: `D5/S3/Quantum/PureState/PhaseProductFidelity.simplex`
