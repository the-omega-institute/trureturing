# Purity of two phase encodings

## Abstract

The best uniform purity-loss coefficient between the singleton and product phase encodings.

Encode a choice of n phases by the n + 1 amplitudes consisting of one and the phases themselves. A second encoding uses all products indexed by subsets. Its normalized vector is a tensor product of n equatorial qubit vectors. Both squared overlaps depend only on the coordinatewise relative phases.

**Definition 1.1 (Singleton phase overlap).**

$$\forall n\in \mathbb{N},u\in \mathbb{C}^{n},\\A(u)=\frac{\left|1+\sum_{1\le k\le n} u_{k}\right|^{2}}{(n+1)^{2}}$$

*Formalization.* `D5/S3/Quantum/PureState/PhaseProductFidelity.simplex` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For unit phases this is the squared inner product with the constant phase vector. For a pair of inputs, take u to be their coordinatewise relative phase.

**Definition 1.2 (Product phase overlap).**

$$\forall n\in \mathbb{N},u\in \mathbb{C}^{n},\\B(u)=\prod_{1\le k\le n}\frac{1+\Re u_{k}}{2}$$

*Formalization.* `D5/S3/Quantum/PureState/PhaseProductFidelity.cube` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each unit complex coordinate contributes the squared overlap of the two equatorial qubit states in that tensor factor.

**Definition 1.3 (Ensemble purity loss).**

$$\forall m\in \mathbb{N},n\in \mathbb{N},F: \mathbb{C}^{n}\to \mathbb{R},p\in \mathbb{R}^{m},v\in \mathbb{C}^{m\times n},\\L(F,p,v)=\sum_{1\le i\le m} \sum_{1\le j\le m} p_{i}p_{j}(1-F(\overline{v_{i}}v_{j}))$$

*Formalization.* `D5/S3/Quantum/PureState/PhaseProductFidelity.mixedDeficit` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The product of the conjugated row and the other row is coordinatewise. Drawing two independent indices from the same distribution gives pairwise weights p_i p_j. For a probability vector p, if F on each relative row equals the squared inner product of the corresponding unit encoded states, this average loss is one minus the purity of their mixture. The singleton and product overlaps meet this condition.

**Theorem 1.4 (Sharp comparison for all finite phase ensembles).**

$$\forall n\in \mathbb{N},n\ge1,C\in \mathbb{R},\\(\forall m\in \mathbb{N},p\in \mathbb{R}^{m},v\in \mathbb{C}^{m\times n},\\((\forall 1\le i\le m,p_{i}\ge0)\land (\forall 1\le i\le m,1\le k\le n,\left|v_{ik}\right|=1))\\\Rightarrow L(B,p,v)\le CL(A,p,v))\Leftrightarrow\frac{(n+1)^{2}}{4}\le C$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/PureState/PhaseProductFidelity.mixed_coefficient_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Here n is a positive integer, m is an arbitrary finite ensemble size, p is a nonnegative weight vector of length m, and v is an m by n array of unit complex phases. The bound permits every total weight. For a probability distribution it compares the two mixture purities. At n = 0 both losses vanish for every coefficient. With rows (1,1) and (-1,-1) and signed weights 2 and -1, the product loss is -4 and nine quarters times the singleton loss is -8. With a single entry 2 of weight one at n = 1, the product loss is -3/2 and the singleton loss is -21/4.

The loss of a product of factors in the unit interval is at most the sum of their individual losses. The modulus of the sum of n phases is at most n. Expanding the singleton overlap then gives the displayed coefficient for each pair and multiplication by the nonnegative pair weights preserves it.

For sharpness, give equal weights to the constant row and a row whose coordinates are all the same phase. As this phase approaches one, the ratio of the two losses tends to the claimed coefficient. When n equals two the coefficient is nine quarters.

## References

- Truth anchor: `D5/S3/Quantum/PureState/PhaseProductFidelity.cube`
- Truth anchor: `D5/S3/Quantum/PureState/PhaseProductFidelity.mixedDeficit`
- Truth anchor: `D5/S3/Quantum/PureState/PhaseProductFidelity.mixed_coefficient_iff`
- Truth anchor: `D5/S3/Quantum/PureState/PhaseProductFidelity.simplex`
- Dependency: [D5/S3/Factorization/JordanCototientRecordLimitInfinity](../../Factorization/JordanCototientRecordLimitInfinity.md)
