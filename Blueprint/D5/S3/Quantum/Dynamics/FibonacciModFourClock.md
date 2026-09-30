# The Actual Mod-Four Fibonacci Clock

## Abstract

The standard mod-four digit lift has four energies and an exact exponential polynomial on the entire sixteen-dimensional joint space.

**Definition 1.1 (The standard digit permutation).**

$$\forall z \in \operatorname{Fin}(4)\times\operatorname{Fin}(4),\; \operatorname{digitMap}(z) = \operatorname{pair}(\operatorname{fin}(2 \cdot \operatorname{mod}(\operatorname{value}(\operatorname{fst}(z)), 2) + \operatorname{mod}(\operatorname{floor}(\frac{\operatorname{value}(\operatorname{fst}(z))}{2}) + \operatorname{mod}(\operatorname{value}(\operatorname{fst}(z)), 2), 2)), \operatorname{fin}(2 \cdot \operatorname{mod}(\operatorname{value}(\operatorname{snd}(z)), 2) + \operatorname{mod}(\operatorname{floor}(\frac{\operatorname{value}(\operatorname{snd}(z))}{2}) + \operatorname{mod}(\operatorname{value}(\operatorname{snd}(z)), 2) + \operatorname{floor}(\frac{\operatorname{floor}(\frac{\operatorname{value}(\operatorname{fst}(z))}{2}) + \operatorname{mod}(\operatorname{value}(\operatorname{fst}(z)), 2)}{2}), 2)))$$

*Formalization.* `D5/S3/Quantum/Dynamics/FibonacciModFourClock.digitMap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each four-label factor represents a bit pair by 2b0+b1. The joint pair represents the standard coordinate split a+2h. The high update includes the carry from the sum of the two low bits.

**Definition 1.2 (The invertible digit action).**

$$digitPermutation:\operatorname{Perm}(\operatorname{Fin}(4)\times\operatorname{Fin}(4))=\operatorname{equivalence}(digitMap, \operatorname{iterate}(digitMap, 5))$$

*Formalization.* `D5/S3/Quantum/Dynamics/FibonacciModFourClock.digitPermutation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Five applications of the digit map give its inverse. Its sixth application fixes every joint label.

**Definition 1.3 (The actual lift matrix).**

$$\forall i \in \operatorname{Fin}(4)\times\operatorname{Fin}(4),\; \forall j \in \operatorname{Fin}(4)\times\operatorname{Fin}(4),\; \operatorname{entry}(U, i, j) = \operatorname{if}(i = \operatorname{digitMap}(j), 1, 0)$$

*Formalization.* `D5/S3/Quantum/Dynamics/FibonacciModFourClock.U` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The column indexed by a joint label is the basis vector indexed by its digit-map image.

**Definition 1.4 (The source Hamiltonian).**

$$L = \operatorname{smul}(2, \operatorname{identity}(\operatorname{Fin}(4)\times\operatorname{Fin}(4))) - U - \operatorname{star}(U)$$

*Formalization.* `D5/S3/Quantum/Dynamics/FibonacciModFourClock.L` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The Hamiltonian is twice the identity minus the lift and its adjoint.

**Definition 1.5 (The actual exponential gate).**

$$\forall Delta \in \mathbb{R},\; \operatorname{clock}(Delta) = \operatorname{exp}(\operatorname{smul}(-i \cdot \operatorname{ofReal}(Delta), L))$$

*Formalization.* `D5/S3/Quantum/Dynamics/FibonacciModFourClock.clock` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The gate uses the Hamiltonian exponential at the declared time.

**Definition 1.6 (The four energy labels).**

$$\forall r \in \operatorname{Fin}(4),\; \operatorname{energy}(r) = \operatorname{at}(\operatorname{vector}(0, 1, 3, 4), r)$$

*Formalization.* `D5/S3/Quantum/Dynamics/FibonacciModFourClock.energy` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The energy labels are ordered as zero, one, three and four.

**Definition 1.7 (Polynomial spectral pieces).**

$$\forall r \in \operatorname{Fin}(4),\; \operatorname{spectralPiece}(r) = \operatorname{smul}(\frac{1}{6}, \operatorname{at}(\operatorname{vector}(\operatorname{identity}(\operatorname{Fin}(4)\times\operatorname{Fin}(4)) + U + U^{2} + U^{3} + U^{4} + U^{5}, \operatorname{smul}(2, \operatorname{identity}(\operatorname{Fin}(4)\times\operatorname{Fin}(4))) + U - U^{2} - \operatorname{smul}(2, U^{3}) - U^{4} + U^{5}, \operatorname{smul}(2, \operatorname{identity}(\operatorname{Fin}(4)\times\operatorname{Fin}(4))) - U - U^{2} + \operatorname{smul}(2, U^{3}) - U^{4} - U^{5}, \operatorname{identity}(\operatorname{Fin}(4)\times\operatorname{Fin}(4)) - U + U^{2} - U^{3} + U^{4} - U^{5}), r))$$

*Formalization.* `D5/S3/Quantum/Dynamics/FibonacciModFourClock.spectralPiece` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

These four polynomials sum to identity. The Hamiltonian acts on each piece by its corresponding energy.

**Theorem 1.8 (The exact clock polynomial).**

$$\forall Delta \in \mathbb{R},\; \operatorname{let}(x:\mathbb{C}, \operatorname{exp}(-i \cdot \operatorname{ofReal}(Delta)), \operatorname{let}(Pplus:\operatorname{Matrix}(\operatorname{Fin}(4)\times\operatorname{Fin}(4), \operatorname{Fin}(4)\times\operatorname{Fin}(4), \mathbb{C}), \operatorname{smul}(\frac{1}{2}, \operatorname{identity}(\operatorname{Fin}(4)\times\operatorname{Fin}(4)) + U^{3}), \operatorname{let}(Pminus:\operatorname{Matrix}(\operatorname{Fin}(4)\times\operatorname{Fin}(4), \operatorname{Fin}(4)\times\operatorname{Fin}(4), \mathbb{C}), \operatorname{smul}(\frac{1}{2}, \operatorname{identity}(\operatorname{Fin}(4)\times\operatorname{Fin}(4)) - U^{3}), \operatorname{let}(A:\mathbb{C}, \frac{1 + 2 \cdot x^{3}}{3}, \operatorname{let}(B:\mathbb{C}, \frac{x \cdot \left(2 + x^{3}\right)}{3}, \operatorname{let}(C:\mathbb{C}, \frac{1 - x^{3}}{3}, U^{6} = \operatorname{identity}(\operatorname{Fin}(4)\times\operatorname{Fin}(4)) \land \operatorname{clock}(Delta) = \operatorname{smul}(A, Pplus) + \operatorname{smul}(B, Pminus) + \operatorname{smul}(C, U \cdot \left(Pplus + \operatorname{smul}(x, Pminus)\right)) + \operatorname{smul}(C, U^{2} \cdot \left(Pplus - \operatorname{smul}(x, Pminus)\right))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/FibonacciModFourClock.fixed_clock_formula` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The sixth-power identity and the four eigenpiece equations yield the exponential by applying its eigenvector action to every column. The result uses the full joint space and every real time.

## References

- Truth anchor: `D5/S3/Quantum/Dynamics/FibonacciModFourClock.L`
- Truth anchor: `D5/S3/Quantum/Dynamics/FibonacciModFourClock.U`
- Truth anchor: `D5/S3/Quantum/Dynamics/FibonacciModFourClock.clock`
- Truth anchor: `D5/S3/Quantum/Dynamics/FibonacciModFourClock.digitMap`
- Truth anchor: `D5/S3/Quantum/Dynamics/FibonacciModFourClock.digitPermutation`
- Truth anchor: `D5/S3/Quantum/Dynamics/FibonacciModFourClock.energy`
- Truth anchor: `D5/S3/Quantum/Dynamics/FibonacciModFourClock.fixed_clock_formula`
- Truth anchor: `D5/S3/Quantum/Dynamics/FibonacciModFourClock.spectralPiece`
- Dependency: [D5/S3/Quantum/Dynamics/EnergyEigenstateStationarity](EnergyEigenstateStationarity.md)
- Dependency: [D5/S3/Quantum/Dynamics/ProjectionProbabilityFlow](ProjectionProbabilityFlow.md)
