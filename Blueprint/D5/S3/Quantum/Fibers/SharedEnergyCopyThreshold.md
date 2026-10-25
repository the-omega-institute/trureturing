# Sparse Shared Energy Relations

## Abstract

Sparse positive density matrices in the fixed three-level energy basis have a primitive phase-sensitive relation of degree twice the upper energy minus one.

**Definition 1.1 (Literal sparse Hermitian matrices).**

Lean statement: `D5/S3/Quantum/Fibers/SharedEnergyCopyThreshold.sparseMatrix`

*Formalization.* `D5/S3/Quantum/Fibers/SharedEnergyCopyThreshold.sparseMatrix` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The diagonal entries are one third. The entries between the first and second basis vectors vanish. The two entries into the third basis vector have modulus one twelfth, with a unit phase on the first edge. The reverse entries are the complex conjugates in this same basis.

**Theorem 1.2 (Positive density spectrum).**

$$\forall u\in\operatorname{Complex}(),u\cdot \operatorname{star}(u)=1 \implies \\\operatorname{PosDef}(\operatorname{sparseMatrix}(u)) \land \operatorname{trace}(\operatorname{sparseMatrix}(u))=1 \land \\\operatorname{spectrum}(\operatorname{Complex}(),\operatorname{sparseMatrix}(u))=\{ \frac{1}{3},\frac{1}{3}-\frac{\sqrt{2}}{12},\frac{1}{3}+\frac{\sqrt{2}}{12}\}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fibers/SharedEnergyCopyThreshold.sparse_density_spectrum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every complex phase of unit modulus, the literal matrix is positive definite and has trace one. Its spectrum is exactly the stated three real numbers. Factoring the determinant of the shifted matrix gives the spectrum; its smallest element is strictly positive.

**Definition 1.3 (Native density states).**

Lean statement: `D5/S3/Quantum/Fibers/SharedEnergyCopyThreshold.sparseState`

*Formalization.* `D5/S3/Quantum/Fibers/SharedEnergyCopyThreshold.sparseState` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The literal matrix enters the native positive trace-one DensityState subtype through its star algebra equivalence. Positivity and trace normalization are proved, rather than assumed as independent coordinates.

**Definition 1.4 (The resonant phase).**

Lean statement: `D5/S3/Quantum/Fibers/SharedEnergyCopyThreshold.phase`

*Formalization.* `D5/S3/Quantum/Fibers/SharedEnergyCopyThreshold.phase` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a natural number m the phase is the circle exponential at pi divided by m minus one. When m is at least two, its power m minus one is minus one. This includes the coincident numerical gaps at m equal to two.

**Definition 1.5 (First sparse density state).**

Lean statement: `D5/S3/Quantum/Fibers/SharedEnergyCopyThreshold.rho`

*Formalization.* `D5/S3/Quantum/Fibers/SharedEnergyCopyThreshold.rho` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The first native state uses phase one and has both nonzero coherences equal to one twelfth.

**Definition 1.6 (Second sparse density state).**

Lean statement: `D5/S3/Quantum/Fibers/SharedEnergyCopyThreshold.sigma`

*Formalization.* `D5/S3/Quantum/Fibers/SharedEnergyCopyThreshold.sigma` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The second native state has the same diagonal and zero entries and uses the resonant phase on the edge between the first and third levels.

**Definition 1.7 (The primitive supported monomial).**

Lean statement: `D5/S3/Quantum/Fibers/SharedEnergyCopyThreshold.starMonomial`

*Formalization.* `D5/S3/Quantum/Fibers/SharedEnergyCopyThreshold.starMonomial` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The monomial is the entry from level two to level one to the power m, times the entry from level zero to level two to the power m minus one. Natural powers retain the value one at exponent zero, even at zero entries.

**Theorem 1.8 (Sparse states and the supported integer kernel).**

$$\forall m\in\operatorname{Nat}(),2\leq m \implies \\\operatorname{PosDef}(\operatorname{stateMatrix}(\operatorname{rho}())) \land \operatorname{PosDef}(\operatorname{stateMatrix}(\operatorname{sigma}(m))) \land\\\operatorname{starMonomial}(m,\operatorname{stateMatrix}(\operatorname{rho}()))=(\frac{1}{12})^{2\cdot m-1} \land\\\operatorname{starMonomial}(m,\operatorname{stateMatrix}(\operatorname{sigma}(m)))=-(\frac{1}{12})^{2\cdot m-1} \land\\(\forall k_{1},k_{2}\in\operatorname{Int}(),((m-1)\cdot k_{1}+m\cdot k_{2}=0 \iff \exists l\in\operatorname{Int}(),k_{1}=l\cdot m \land k_{2}=l\cdot (-(m-1)))) \land\\(\forall l\in\operatorname{Int}(),l\neq 0 \implies 2\cdot m-1\leq \lvert l\cdot m\rvert +\lvert l\cdot (-(m-1))\rvert )$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fibers/SharedEnergyCopyThreshold.sparse_pair_data` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural m at least two, both actual state matrices are positive definite. The distinguished monomial takes opposite values of modulus one twelfth to the power twice m minus one. The entire integer kernel of the two supported gaps consists of multiples of the primitive vector with coordinates m and minus m plus one. Every nonzero multiple has l1 norm at least twice m minus one. The kernel calculation applies the cofactor kernel theorem after checking its determinant, sum and gcd premises for these actual consecutive gaps.

**Definition 1.9 (Integer energy labels).**

Lean statement: `D5/S3/Quantum/Fibers/SharedEnergyCopyThreshold.energy`

*Formalization.* `D5/S3/Quantum/Fibers/SharedEnergyCopyThreshold.energy` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The labelled basis energies are zero, one and m. Integer differences are used before grouping any equal numerical gaps.

**Definition 1.10 (Labelled matrix exponents).**

Lean statement: `D5/S3/Quantum/Fibers/SharedEnergyCopyThreshold.Exponent`

*Formalization.* `D5/S3/Quantum/Fibers/SharedEnergyCopyThreshold.Exponent` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An exponent is a natural number at each of the nine ordered matrix coordinates. Opposite directions and repeated numerical gaps remain different coordinates.

**Definition 1.11 (Total exponent degree).**

Lean statement: `D5/S3/Quantum/Fibers/SharedEnergyCopyThreshold.degree`

*Formalization.* `D5/S3/Quantum/Fibers/SharedEnergyCopyThreshold.degree` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The degree is the sum of all nine natural multiplicities.

**Definition 1.12 (Total energy weight).**

Lean statement: `D5/S3/Quantum/Fibers/SharedEnergyCopyThreshold.weight`

*Formalization.* `D5/S3/Quantum/Fibers/SharedEnergyCopyThreshold.weight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The weight sums each actual ordered energy difference times its natural multiplicity, in the integers.

**Definition 1.13 (Actual coordinate monomials).**

Lean statement: `D5/S3/Quantum/Fibers/SharedEnergyCopyThreshold.monomial`

*Formalization.* `D5/S3/Quantum/Fibers/SharedEnergyCopyThreshold.monomial` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The monomial is the product of all nine matrix entries raised to their natural exponents. In particular zero to the zeroth power is one.

**Theorem 1.14 (Every low zero-weight monomial).**

$$\forall m\in\operatorname{Nat}(),2\leq m \implies \forall a\in\operatorname{Exponent}(),\\\operatorname{degree}(a)<2\cdot m-1 \implies \operatorname{weight}(m,a)=0 \implies \\\forall u\in\operatorname{Complex}(),u\cdot \operatorname{star}(u)=1 \implies \\\operatorname{monomial}(\operatorname{sparseMatrix}(1),a)=\operatorname{monomial}(\operatorname{sparseMatrix}(u),a)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fibers/SharedEnergyCopyThreshold.sparse_low_monomials` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every m at least two, every labelled exponent of degree less than twice m minus one and weight zero gives the same monomial on the first matrix and on every unit phase in the sparse family. A positive exponent on either missing edge makes both values zero. Otherwise the primitive kernel and the degree bound force both net oriented exponents to vanish, so conjugate phases cancel.

These matrix and integer-kernel statements do not by themselves establish the least uniform copy order on all density states. That conclusion also requires the upper bound for all labelled zero-weight exponents, the shared Haar average and full total-energy pinching identity, and the equivalence with every compatible complex effect. A compact orbit is distinct from reachability at one exact time. The sparse monomial alone gives no Helstrom optimum, adaptive protocol bound, postselection advantage, or identification of integer description length with copy cost.

## References

- Truth anchor: `D5/S3/Quantum/Fibers/SharedEnergyCopyThreshold.Exponent`
- Truth anchor: `D5/S3/Quantum/Fibers/SharedEnergyCopyThreshold.degree`
- Truth anchor: `D5/S3/Quantum/Fibers/SharedEnergyCopyThreshold.energy`
- Truth anchor: `D5/S3/Quantum/Fibers/SharedEnergyCopyThreshold.monomial`
- Truth anchor: `D5/S3/Quantum/Fibers/SharedEnergyCopyThreshold.phase`
- Truth anchor: `D5/S3/Quantum/Fibers/SharedEnergyCopyThreshold.rho`
- Truth anchor: `D5/S3/Quantum/Fibers/SharedEnergyCopyThreshold.sigma`
- Truth anchor: `D5/S3/Quantum/Fibers/SharedEnergyCopyThreshold.sparseMatrix`
- Truth anchor: `D5/S3/Quantum/Fibers/SharedEnergyCopyThreshold.sparseState`
- Truth anchor: `D5/S3/Quantum/Fibers/SharedEnergyCopyThreshold.sparse_density_spectrum`
- Truth anchor: `D5/S3/Quantum/Fibers/SharedEnergyCopyThreshold.sparse_low_monomials`
- Truth anchor: `D5/S3/Quantum/Fibers/SharedEnergyCopyThreshold.sparse_pair_data`
- Truth anchor: `D5/S3/Quantum/Fibers/SharedEnergyCopyThreshold.starMonomial`
- Truth anchor: `D5/S3/Quantum/Fibers/SharedEnergyCopyThreshold.weight`
- Dependency: [D5/S3/Arith/Lattices/CofactorKernel](../../Arith/Lattices/CofactorKernel.md)
- Dependency: [D5/S3/Quantum/Fibers/RealCopyConjugation](RealCopyConjugation.md)
