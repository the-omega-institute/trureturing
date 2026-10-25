# Sparse Shared Energy Relations

## Abstract

Sparse positive density matrices in the fixed three-level energy basis have a phase-sensitive relation of degree twice the upper energy minus one.

**Definition 1.1 (Literal sparse Hermitian matrices).**

Lean statement: `D5/S3/Quantum/Fibers/SharedEnergyCopyThreshold.sparseMatrix`

*Formalization.* `D5/S3/Quantum/Fibers/SharedEnergyCopyThreshold.sparseMatrix` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The diagonal entries are one third. The entries between the first and second basis vectors vanish. Entries (2,0) and (0,2) are u divided by twelve and its conjugate; entries (2,1) and (1,2) are one twelfth. Both edge moduli are one twelfth when u has unit modulus.

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

**Definition 1.7 (The phase-sensitive supported monomial).**

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

**Definition 1.15 (One labelled occurrence).**

Lean statement: `D5/S3/Quantum/Fibers/SharedEnergyCopyThreshold.coordinateExponent`

*Formalization.* `D5/S3/Quantum/Fibers/SharedEnergyCopyThreshold.coordinateExponent` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The unit exponent at one ordered coordinate retains the row and column labels.

**Definition 1.16 (Exponents of native tensor entries).**

Lean statement: `D5/S3/Quantum/Fibers/SharedEnergyCopyThreshold.tensorExponent`

*Formalization.* `D5/S3/Quantum/Fibers/SharedEnergyCopyThreshold.tensorExponent` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each pair of product-basis words contributes one labelled occurrence at each tensor position.

**Definition 1.17 (Total product-basis energy).**

Lean statement: `D5/S3/Quantum/Fibers/SharedEnergyCopyThreshold.totalEnergy`

*Formalization.* `D5/S3/Quantum/Fibers/SharedEnergyCopyThreshold.totalEnergy` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The energy of a word is the sum of its single-copy energies, with zero for the empty word.

**Definition 1.18 (Complete total-energy projections).**

Lean statement: `D5/S3/Quantum/Fibers/SharedEnergyCopyThreshold.energyProjector`

*Formalization.* `D5/S3/Quantum/Fibers/SharedEnergyCopyThreshold.energyProjector` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The diagonal projection selects all words with the specified total energy. It preserves the full degenerate energy space.

**Definition 1.19 (Pinched native tensor states).**

Lean statement: `D5/S3/Quantum/Fibers/SharedEnergyCopyThreshold.pinchedCopies`

*Formalization.* `D5/S3/Quantum/Fibers/SharedEnergyCopyThreshold.pinchedCopies` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Sum the native tensor state between the complete projections over its finite set of total energies.

**Definition 1.20 (Total-energy pinching of arbitrary matrices).**

Lean statement: `D5/S3/Quantum/Fibers/SharedEnergyCopyThreshold.energyPinch`

*Formalization.* `D5/S3/Quantum/Fibers/SharedEnergyCopyThreshold.energyPinch` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The same complete projections act on arbitrary complex matrices. Pinching a positive contraction gives a positive contraction commuting with the sum Hamiltonian.

**Theorem 1.21 (Every compatible complex effect).**

$$\forall m,n\in\operatorname{Nat}(),\forall r,s\in\operatorname{DensityState}(\operatorname{Fin}(3)),\\\operatorname{pinchedCopies}(m,n,r)=\operatorname{pinchedCopies}(m,n,s) \iff \forall F\in\operatorname{Matrix}(\operatorname{CopyIndex}(\operatorname{Fin}(3),n),\operatorname{CopyIndex}(\operatorname{Fin}(3),n),\operatorname{Complex}()),\\\operatorname{PosSemidef}(F) \implies \operatorname{PosSemidef}(1-F) \implies F\cdot \operatorname{totalHamiltonian}(m,n)=\operatorname{totalHamiltonian}(m,n)\cdot F \implies \operatorname{trace}(F\cdot \operatorname{stateMatrix}(\operatorname{copies}(r,n)))=\operatorname{trace}(F\cdot \operatorname{stateMatrix}(\operatorname{copies}(s,n)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fibers/SharedEnergyCopyThreshold.compatible_effects_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all native density states, including states of deficient rank, equality of complete total-energy pinchings is equivalent to equality of unconditional trace probabilities for every positive complex effect bounded by the identity and commuting with the sum Hamiltonian. Pinching preserves the trace pairing and maps every complex effect into this commutant. The original effect-trace uniqueness theorem then separates the pinched matrices. No reality restriction is placed on the effect entries, and degenerate blocks retain their complex off-diagonals.

**Theorem 1.22 (Native tensor entries and total-energy pinching).**

$$\forall m,n\in\operatorname{Nat}(),\forall r\in\operatorname{DensityState}(\operatorname{Fin}(3)),\forall I,J\in\operatorname{CopyIndex}(\operatorname{Fin}(3),n),\\\operatorname{degree}(\operatorname{tensorExponent}(n,I,J))=n \land \operatorname{weight}(m,\operatorname{tensorExponent}(n,I,J))=\operatorname{totalEnergy}(m,n,I)-\operatorname{totalEnergy}(m,n,J) \land\\\operatorname{entry}(\operatorname{stateMatrix}(\operatorname{copies}(r,n)),I,J)=\operatorname{monomial}(\operatorname{stateMatrix}(r),\operatorname{tensorExponent}(n,I,J)) \land\\\operatorname{entry}(\operatorname{pinchedCopies}(m,n,r),I,J)=\operatorname{ite}(\operatorname{weight}(m,\operatorname{tensorExponent}(n,I,J))=0,\operatorname{monomial}(\operatorname{stateMatrix}(r),\operatorname{tensorExponent}(n,I,J)),0) \land\\\operatorname{PosSemidef}(\operatorname{pinchedCopies}(m,n,r)) \land \operatorname{trace}(\operatorname{pinchedCopies}(m,n,r))=1$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fibers/SharedEnergyCopyThreshold.tensor_monomial_bridge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every native three-dimensional density state, every copy count and every pair of actual tensor words, the recursively constructed exponent has that copy count as degree and the total-energy difference as weight. The actual tensor entry equals its coordinate monomial. Complete total-energy pinching keeps exactly the zero-weight entries, including off-diagonals inside degenerate blocks. The pinched matrix is positive semidefinite with trace one.

**Theorem 1.23 (Every exponent has native tensor words).**

$$\forall m\in\operatorname{Nat}(),\forall a\in\operatorname{Exponent}(),\exists I,J\in\operatorname{CopyIndex}(\operatorname{Fin}(3),\operatorname{degree}(a)),\\\operatorname{tensorExponent}(\operatorname{degree}(a),I,J)=a \land \operatorname{totalEnergy}(m,\operatorname{degree}(a),I)-\operatorname{totalEnergy}(m,\operatorname{degree}(a),J)=\operatorname{weight}(m,a) \land\\\forall r\in\operatorname{DensityState}(\operatorname{Fin}(3)),\operatorname{entry}(\operatorname{stateMatrix}(\operatorname{copies}(r,\operatorname{degree}(a))),I,J)=\operatorname{monomial}(\operatorname{stateMatrix}(r),a) \land\\\operatorname{entry}(\operatorname{pinchedCopies}(m,\operatorname{degree}(a),r),I,J)=\operatorname{ite}(\operatorname{weight}(m,a)=0,\operatorname{monomial}(\operatorname{stateMatrix}(r),a),0)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fibers/SharedEnergyCopyThreshold.exponent_tensor_bridge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every labelled exponent is realized by two words whose length is its degree. Their energy difference is its weight, and their tensor entry is its monomial on every native state. The construction successively removes one actual coordinate occurrence. It includes the empty exponent, zero matrix entries, deficient rank and repeated numerical gaps.

**Theorem 1.24 (Low-order complete pinchings agree).**

$$\forall m,n\in\operatorname{Nat}(),2\leq m \implies n<2\cdot m-1 \implies \operatorname{pinchedCopies}(m,n,\operatorname{rho}())=\operatorname{pinchedCopies}(m,n,\operatorname{sigma}(m))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fibers/SharedEnergyCopyThreshold.sparse_low_pinching` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every m at least two and every copy count below twice m minus one, the complete total-energy pinchings of the actual sparse tensor states agree. This uses all labelled entries and includes zero exponents.

**Definition 1.25 (Tuples in the native tensor basis).**

Lean statement: `D5/S3/Quantum/Fibers/SharedEnergyCopyThreshold.wordIndex`

*Formalization.* `D5/S3/Quantum/Fibers/SharedEnergyCopyThreshold.wordIndex` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A tuple is mapped to the same recursively parenthesized product basis used by the native density-state copies.

**Definition 1.26 (Two block lengths).**

Lean statement: `D5/S3/Quantum/Fibers/SharedEnergyCopyThreshold.copyOrder`

*Formalization.* `D5/S3/Quantum/Fibers/SharedEnergyCopyThreshold.copyOrder` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The distinguishing copy count is m plus m minus one.

**Definition 1.27 (First distinguishing word).**

Lean statement: `D5/S3/Quantum/Fibers/SharedEnergyCopyThreshold.wordI`

*Formalization.* `D5/S3/Quantum/Fibers/SharedEnergyCopyThreshold.wordI` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The first word has m twos followed by m minus one zeros.

**Definition 1.28 (Second distinguishing word).**

Lean statement: `D5/S3/Quantum/Fibers/SharedEnergyCopyThreshold.wordJ`

*Formalization.* `D5/S3/Quantum/Fibers/SharedEnergyCopyThreshold.wordJ` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The second word has m ones followed by m minus one twos.

**Definition 1.29 (Sum of the one-copy Hamiltonians).**

Lean statement: `D5/S3/Quantum/Fibers/SharedEnergyCopyThreshold.totalHamiltonian`

*Formalization.* `D5/S3/Quantum/Fibers/SharedEnergyCopyThreshold.totalHamiltonian` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

On each native tensor product, add the first Hamiltonian tensored with the identity to the identity tensored with the remaining Hamiltonian.

**Theorem 1.30 (The actual sum Hamiltonian is diagonal).**

$$\forall m,n\in\operatorname{Nat}(),\operatorname{totalHamiltonian}(m,n)=\operatorname{diagonal}((\lambda I:\operatorname{CopyIndex}(\operatorname{Fin}(3),n),\operatorname{totalEnergy}(m,n,I)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fibers/SharedEnergyCopyThreshold.total_hamiltonian_diagonal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every m and every native tensor length, the recursive sum Hamiltonian is diagonal in the native product basis. Its diagonal is the sum of the actual one-copy energy labels.

**Theorem 1.31 (Actual equal-energy words).**

$$\forall m\in\operatorname{Nat}(),2\leq m \implies \\\operatorname{copyOrder}(m)=2\cdot m-1 \land \operatorname{wordI}(m)\neq \operatorname{wordJ}(m) \land\\\operatorname{totalEnergy}(m,\operatorname{copyOrder}(m),\operatorname{wordI}(m))=(m)^{2} \land \operatorname{totalEnergy}(m,\operatorname{copyOrder}(m),\operatorname{wordJ}(m))=(m)^{2} \land\\\forall r\in\operatorname{DensityState}(\operatorname{Fin}(3)),\operatorname{entry}(\operatorname{stateMatrix}(\operatorname{copies}(r,\operatorname{copyOrder}(m))),\operatorname{wordI}(m),\operatorname{wordJ}(m))=\operatorname{starMonomial}(m,\operatorname{stateMatrix}(r))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fibers/SharedEnergyCopyThreshold.sparse_joint_words` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every m at least two the two words are distinct, have common energy m squared, and have length twice m minus one. Their tensor entry on every native state is the distinguished monomial, without a rank or support restriction.

**Definition 1.32 (Equal-superposition projection).**

Lean statement: `D5/S3/Quantum/Fibers/SharedEnergyCopyThreshold.jointEffect`

*Formalization.* `D5/S3/Quantum/Fibers/SharedEnergyCopyThreshold.jointEffect` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The effect is one half the outer product of the sum of the two computational basis vectors with its conjugate. It is a projection on their actual tensor space.

**Theorem 1.33 (A compatible effect with exact unconditional probabilities).**

$$\forall m\in\operatorname{Nat}(),2\leq m \implies \\\operatorname{PosSemidef}(\operatorname{jointEffect}(m)) \land \operatorname{PosSemidef}(1-\operatorname{jointEffect}(m)) \land\\\operatorname{jointEffect}(m)\cdot \operatorname{totalHamiltonian}(m,\operatorname{copyOrder}(m))=\operatorname{totalHamiltonian}(m,\operatorname{copyOrder}(m))\cdot \operatorname{jointEffect}(m) \land\\\operatorname{trace}(\operatorname{jointEffect}(m)\cdot \operatorname{stateMatrix}(\operatorname{copies}(\operatorname{rho}(),\operatorname{copyOrder}(m))))=(\frac{1}{3})^{2\cdot m-1}+(\frac{1}{12})^{2\cdot m-1} \land \operatorname{trace}(\operatorname{jointEffect}(m)\cdot \operatorname{stateMatrix}(\operatorname{copies}(\operatorname{sigma}(m),\operatorname{copyOrder}(m))))=(\frac{1}{3})^{2\cdot m-1}-(\frac{1}{12})^{2\cdot m-1} \land\\0<2\cdot (\frac{1}{12})^{2\cdot m-1} \land\\(\frac{1}{3})^{2\cdot m-1}+(\frac{1}{12})^{2\cdot m-1}\in\operatorname{Icc}(0,1) \land (\frac{1}{3})^{2\cdot m-1}-(\frac{1}{12})^{2\cdot m-1}\in\operatorname{Icc}(0,1) \land\\\operatorname{pinchedCopies}(m,\operatorname{copyOrder}(m),\operatorname{rho}())\neq \operatorname{pinchedCopies}(m,\operatorname{copyOrder}(m),\operatorname{sigma}(m)) \land\\\forall n\in\operatorname{Nat}(),n<2\cdot m-1 \implies \forall F\in\operatorname{Matrix}(\operatorname{CopyIndex}(\operatorname{Fin}(3),n),\operatorname{CopyIndex}(\operatorname{Fin}(3),n),\operatorname{Complex}()),\\\operatorname{PosSemidef}(F) \implies \operatorname{PosSemidef}(1-F) \implies F\cdot \operatorname{totalHamiltonian}(m,n)=\operatorname{totalHamiltonian}(m,n)\cdot F \implies \operatorname{trace}(F\cdot \operatorname{stateMatrix}(\operatorname{copies}(\operatorname{rho}(),n)))=\operatorname{trace}(F\cdot \operatorname{stateMatrix}(\operatorname{copies}(\operatorname{sigma}(m),n)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fibers/SharedEnergyCopyThreshold.sparse_joint_effect` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The effect and its complement are positive semidefinite, and the effect commutes with the sum Hamiltonian. Its unconditional probabilities on the two native sparse tensor states are respectively one third to the copy count plus and minus one twelfth to that count. Both real probabilities lie between zero and one, and their gap is positive. The complete total-energy pinchings differ at this copy count. At every smaller copy count all compatible complex effects have equal probabilities on the two actual tensor states.

**Definition 1.34 (Labelled indecomposable zero-weight exponents).**

Lean statement: `D5/S3/Quantum/Fibers/SharedEnergyCopyThreshold.Indecomposable`

*Formalization.* `D5/S3/Quantum/Fibers/SharedEnergyCopyThreshold.Indecomposable` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An exponent is nonzero, has weight zero, and contains no nonzero proper subexponent of weight zero. This definition retains diagonal coordinates and distinguishes coordinates with equal numerical gaps.

For every natural m at least two, let alpha have multiplicity m at the ordered coordinate (2,1), multiplicity m minus one at (0,2), and zero at all other coordinates. Its weight is m times (m minus one) minus (m minus one) times m, hence zero; its degree is twice m minus one. Its monomial on every complex three by three matrix X is exactly X(2,1) to the power m times X(0,2) to the power m minus one. These statements keep all nine coordinate labels, including the coincident numerical gaps when m equals two.

The indecomposability of alpha follows directly from D5/S3/Arith/Lattices/CofactorKernel.primitive_kernel_span. Take the one-row integer matrix A with entries m minus one and m, and the primitive vector v with entries m and minus (m minus one). The augmented determinant is one, A times v is zero, the coordinate sum of v is one, and its coordinate gcd is one. If beta is a nonnegative subexponent of alpha with weight zero, its only possible nonzero coordinates are (2,1) and (0,2). The vector (beta(2,1), minus beta(0,2)) lies in the integer kernel of A. The cited theorem makes it ell times v. Since zero is at most beta(2,1) and beta(2,1) is at most m, the integer ell is zero or one. Thus beta is zero or alpha. The exponent alpha is nonzero, so it is an indecomposable zero-weight exponent attaining degree twice m minus one. Together with the general labelled degree bound, this gives the exact maximal degree. This application uses the original primitive integer-kernel theorem; it supplies no additional claim about experimental access to matrix coordinates.

The all-state compact-orbit theorem combines these sparse lower bounds with labelled exponent decomposition and phase reconstruction to obtain the least uniform order. The explicit effect gives no Helstrom optimum, adaptive protocol bound or postselection advantage. Integer description length and physical copy cost are distinct quantities.

## References

- Truth anchor: `D5/S3/Quantum/Fibers/SharedEnergyCopyThreshold.Exponent`
- Truth anchor: `D5/S3/Quantum/Fibers/SharedEnergyCopyThreshold.Indecomposable`
- Truth anchor: `D5/S3/Quantum/Fibers/SharedEnergyCopyThreshold.compatible_effects_iff`
- Truth anchor: `D5/S3/Quantum/Fibers/SharedEnergyCopyThreshold.coordinateExponent`
- Truth anchor: `D5/S3/Quantum/Fibers/SharedEnergyCopyThreshold.copyOrder`
- Truth anchor: `D5/S3/Quantum/Fibers/SharedEnergyCopyThreshold.degree`
- Truth anchor: `D5/S3/Quantum/Fibers/SharedEnergyCopyThreshold.energy`
- Truth anchor: `D5/S3/Quantum/Fibers/SharedEnergyCopyThreshold.energyPinch`
- Truth anchor: `D5/S3/Quantum/Fibers/SharedEnergyCopyThreshold.energyProjector`
- Truth anchor: `D5/S3/Quantum/Fibers/SharedEnergyCopyThreshold.exponent_tensor_bridge`
- Truth anchor: `D5/S3/Quantum/Fibers/SharedEnergyCopyThreshold.jointEffect`
- Truth anchor: `D5/S3/Quantum/Fibers/SharedEnergyCopyThreshold.monomial`
- Truth anchor: `D5/S3/Quantum/Fibers/SharedEnergyCopyThreshold.phase`
- Truth anchor: `D5/S3/Quantum/Fibers/SharedEnergyCopyThreshold.pinchedCopies`
- Truth anchor: `D5/S3/Quantum/Fibers/SharedEnergyCopyThreshold.rho`
- Truth anchor: `D5/S3/Quantum/Fibers/SharedEnergyCopyThreshold.sigma`
- Truth anchor: `D5/S3/Quantum/Fibers/SharedEnergyCopyThreshold.sparseMatrix`
- Truth anchor: `D5/S3/Quantum/Fibers/SharedEnergyCopyThreshold.sparseState`
- Truth anchor: `D5/S3/Quantum/Fibers/SharedEnergyCopyThreshold.sparse_density_spectrum`
- Truth anchor: `D5/S3/Quantum/Fibers/SharedEnergyCopyThreshold.sparse_joint_effect`
- Truth anchor: `D5/S3/Quantum/Fibers/SharedEnergyCopyThreshold.sparse_joint_words`
- Truth anchor: `D5/S3/Quantum/Fibers/SharedEnergyCopyThreshold.sparse_low_monomials`
- Truth anchor: `D5/S3/Quantum/Fibers/SharedEnergyCopyThreshold.sparse_low_pinching`
- Truth anchor: `D5/S3/Quantum/Fibers/SharedEnergyCopyThreshold.sparse_pair_data`
- Truth anchor: `D5/S3/Quantum/Fibers/SharedEnergyCopyThreshold.starMonomial`
- Truth anchor: `D5/S3/Quantum/Fibers/SharedEnergyCopyThreshold.tensorExponent`
- Truth anchor: `D5/S3/Quantum/Fibers/SharedEnergyCopyThreshold.tensor_monomial_bridge`
- Truth anchor: `D5/S3/Quantum/Fibers/SharedEnergyCopyThreshold.totalEnergy`
- Truth anchor: `D5/S3/Quantum/Fibers/SharedEnergyCopyThreshold.totalHamiltonian`
- Truth anchor: `D5/S3/Quantum/Fibers/SharedEnergyCopyThreshold.total_hamiltonian_diagonal`
- Truth anchor: `D5/S3/Quantum/Fibers/SharedEnergyCopyThreshold.weight`
- Truth anchor: `D5/S3/Quantum/Fibers/SharedEnergyCopyThreshold.wordI`
- Truth anchor: `D5/S3/Quantum/Fibers/SharedEnergyCopyThreshold.wordIndex`
- Truth anchor: `D5/S3/Quantum/Fibers/SharedEnergyCopyThreshold.wordJ`
- Dependency: [D5/S3/Arith/Lattices/CofactorKernel](../../Arith/Lattices/CofactorKernel.md)
- Dependency: [D5/S3/Quantum/Fibers/RealCopyConjugation](RealCopyConjugation.md)
- Dependency: [D5/S3/Quantum/Foundation/EffectProbabilityExtension](../Foundation/EffectProbabilityExtension.md)
