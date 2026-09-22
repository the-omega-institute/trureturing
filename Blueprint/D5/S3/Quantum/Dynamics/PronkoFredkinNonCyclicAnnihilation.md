# Non-cyclic periodic Fredkin eigenstates are annihilated

## Abstract

The periodic Fredkin Hamiltonian and Pronko's nonlocal operators are represented on the spin-word basis. The cyclic-shift absorption identity then forces both nonlocal operators to vanish on every non-cyclic invariant eigenstate.

**Definition 1.1 (The spin-raising matrix).**

$$sigmaPlus = \begin{bmatrix}0&1\\0&0\end{bmatrix}$$

*Formalization.* `D5/S3/Quantum/Dynamics/PronkoFredkinNonCyclicAnnihilation.sigmaPlus` (`✓ std3`).

*Citation.* Andrei G. Pronko (2025). *Symmetries of the periodic Fredkin chain*. DOI: [10.1088/1751-8121/ae1644](https://doi.org/10.1088/1751-8121/ae1644). URL: <https://doi.org/10.1088/1751-8121/ae1644>.

*Commentary.*

The basis order is 0 = up and 1 = down. This is the sigma-plus matrix printed in section 2.1, p. 3.

**Definition 1.2 (The spin-lowering matrix).**

$$sigmaMinus = \begin{bmatrix}0&0\\1&0\end{bmatrix}$$

*Formalization.* `D5/S3/Quantum/Dynamics/PronkoFredkinNonCyclicAnnihilation.sigmaMinus` (`✓ std3`).

*Citation.* Andrei G. Pronko (2025). *Symmetries of the periodic Fredkin chain*. DOI: [10.1088/1751-8121/ae1644](https://doi.org/10.1088/1751-8121/ae1644). URL: <https://doi.org/10.1088/1751-8121/ae1644>.

*Commentary.*

In the same ordered basis, this is the sigma-minus matrix printed in section 2.1, p. 3.

**Definition 1.3 (Projection onto spin up).**

$$nUp = (\frac{1}{2}) \cdot ((I) + (qubitZ))$$

*Formalization.* `D5/S3/Quantum/Dynamics/PronkoFredkinNonCyclicAnnihilation.nUp` (`✓ std3`).

*Citation.* Andrei G. Pronko (2025). *Symmetries of the periodic Fredkin chain*. DOI: [10.1088/1751-8121/ae1644](https://doi.org/10.1088/1751-8121/ae1644). URL: <https://doi.org/10.1088/1751-8121/ae1644>.

*Commentary.*

The scalar one half is a complex scalar, I is the two-dimensional identity matrix, and qubitZ is the frozen matrix owned by D5/S3/Quantum/FiniteDimensional. The expression is the printed spin-up projector.

**Definition 1.4 (Projection onto spin down).**

$$nDown = (\frac{1}{2}) \cdot ((I) - (qubitZ))$$

*Formalization.* `D5/S3/Quantum/Dynamics/PronkoFredkinNonCyclicAnnihilation.nDown` (`✓ std3`).

*Citation.* Andrei G. Pronko (2025). *Symmetries of the periodic Fredkin chain*. DOI: [10.1088/1751-8121/ae1644](https://doi.org/10.1088/1751-8121/ae1644). URL: <https://doi.org/10.1088/1751-8121/ae1644>.

*Commentary.*

The scalar one half is a complex scalar, I is the two-dimensional identity matrix, and qubitZ is the frozen matrix owned by D5/S3/Quantum/FiniteDimensional. The expression is the printed spin-down projector.

**Definition 1.5 (Sitewise Kronecker product).**

$$\forall N \in \mathbb{N},\; \forall f \in \operatorname{Fin}\left(N\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right),\; \forall y \in \operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(2\right),\; \forall x \in \operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(2\right),\; \operatorname{tensor}\left(N, f\right)\left(y, x\right) = \prod_{i \in \operatorname{Fin}\left(N\right)} (f\left(i\right)\left(y\left(i\right), x\left(i\right)\right))$$

*Formalization.* `D5/S3/Quantum/Dynamics/PronkoFredkinNonCyclicAnnihilation.tensor` (`✓ std3`).

*Citation.* Andrei G. Pronko (2025). *Symmetries of the periodic Fredkin chain*. DOI: [10.1088/1751-8121/ae1644](https://doi.org/10.1088/1751-8121/ae1644). URL: <https://doi.org/10.1088/1751-8121/ae1644>.

*Commentary.*

For configurations x and y, the matrix entry is the product of the corresponding one-site entries over i in Fin N. This fixes the Kronecker-product convention used below.

**Definition 1.6 (A one-site operator).**

$$\forall N \in \mathbb{N},\; \forall j \in \operatorname{Fin}\left(N\right),\; \forall A \in \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right),\; \operatorname{site}\left(N, j, A\right) = \operatorname{tensor}\left(N, (i \mapsto \operatorname{ite}\left(i = j, A, I\right))\right)$$

*Formalization.* `D5/S3/Quantum/Dynamics/PronkoFredkinNonCyclicAnnihilation.site` (`✓ std3`).

*Citation.* Andrei G. Pronko (2025). *Symmetries of the periodic Fredkin chain*. DOI: [10.1088/1751-8121/ae1644](https://doi.org/10.1088/1751-8121/ae1644). URL: <https://doi.org/10.1088/1751-8121/ae1644>.

*Commentary.*

The operator A occupies site j and every other factor is the two-dimensional identity. Site indices have type Fin N.

**Definition 1.7 (Exchange of adjacent sites).**

$$\forall N \in \mathbb{N},\; \forall j \in \operatorname{Fin}\left(N\right),\; \operatorname{P}\left(N, j\right) = \operatorname{permMatrix}\left(\mathbb{C}, \operatorname{arrowCongr}\left(\operatorname{swap}\left(j, \operatorname{finRotate}\left(N, j\right)\right), \operatorname{Equiv.refl}\left(\operatorname{Fin}\left(2\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Dynamics/PronkoFredkinNonCyclicAnnihilation.P` (`✓ std3`).

*Citation.* Andrei G. Pronko (2025). *Symmetries of the periodic Fredkin chain*. DOI: [10.1088/1751-8121/ae1644](https://doi.org/10.1088/1751-8121/ae1644). URL: <https://doi.org/10.1088/1751-8121/ae1644>.

*Commentary.*

Here finRotate N j is j + 1 modulo N. The configuration permutation swaps sites j and finRotate N j, and permMatrix is its complex permutation matrix.

**Definition 1.8 (Antisymmetric two-site projector).**

$$\forall N \in \mathbb{N},\; \forall j \in \operatorname{Fin}\left(N\right),\; \operatorname{Pi}\left(N, j\right) = (\frac{1}{2}) \cdot ((I) - (\operatorname{P}\left(N, j\right)))$$

*Formalization.* `D5/S3/Quantum/Dynamics/PronkoFredkinNonCyclicAnnihilation.Pi` (`✓ std3`).

*Citation.* Andrei G. Pronko (2025). *Symmetries of the periodic Fredkin chain*. DOI: [10.1088/1751-8121/ae1644](https://doi.org/10.1088/1751-8121/ae1644). URL: <https://doi.org/10.1088/1751-8121/ae1644>.

*Commentary.*

This is one half of the identity minus the adjacent-site exchange operator, as in section 2.1.

**Definition 1.9 (Periodic Fredkin Hamiltonian density).**

$$\forall N \in \mathbb{N},\; \forall j \in \operatorname{Fin}\left(N\right),\; \operatorname{F}\left(N, j\right) = ((\operatorname{site}\left(N, j, nUp\right)) \cdot (\operatorname{Pi}\left(N, \operatorname{finRotate}\left(N, j\right)\right))) + ((\operatorname{Pi}\left(N, j\right)) \cdot (\operatorname{site}\left(N, \operatorname{finRotate}\left(N, \operatorname{finRotate}\left(N, j\right)\right), nDown\right)))$$

*Formalization.* `D5/S3/Quantum/Dynamics/PronkoFredkinNonCyclicAnnihilation.F` (`✓ std3`).

*Citation.* Andrei G. Pronko (2025). *Symmetries of the periodic Fredkin chain*. DOI: [10.1088/1751-8121/ae1644](https://doi.org/10.1088/1751-8121/ae1644). URL: <https://doi.org/10.1088/1751-8121/ae1644>.

*Commentary.*

The first term projects site j onto spin up before antisymmetrizing sites j + 1 and j + 2. The second antisymmetrizes sites j and j + 1 before projecting site j + 2 onto spin down. Every addition of site indices is modulo N.

**Definition 1.10 (Periodic Fredkin Hamiltonian).**

$$\forall N \in \mathbb{N},\; \operatorname{H}\left(N\right) = \sum_{j \in \operatorname{Fin}\left(N\right)} (\operatorname{F}\left(N, j\right))$$

*Formalization.* `D5/S3/Quantum/Dynamics/PronkoFredkinNonCyclicAnnihilation.H` (`✓ std3`).

*Citation.* Andrei G. Pronko (2025). *Symmetries of the periodic Fredkin chain*. DOI: [10.1088/1751-8121/ae1644](https://doi.org/10.1088/1751-8121/ae1644). URL: <https://doi.org/10.1088/1751-8121/ae1644>.

*Commentary.*

The Hamiltonian is the sum of the local density over every j in Fin N, matching equation (2.3).

**Definition 1.11 (Ordered cyclic product).**

$$\forall N \in \mathbb{N},\; \operatorname{C}\left(N\right) = \operatorname{List.prod}\left(\operatorname{List.map}\left((j \mapsto \operatorname{P}\left(N, j\right)), \operatorname{List.dropLast}\left(\operatorname{List.finRange}\left(N\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Dynamics/PronkoFredkinNonCyclicAnnihilation.C` (`✓ std3`).

*Citation.* Andrei G. Pronko (2025). *Symmetries of the periodic Fredkin chain*. DOI: [10.1088/1751-8121/ae1644](https://doi.org/10.1088/1751-8121/ae1644). URL: <https://doi.org/10.1088/1751-8121/ae1644>.

*Commentary.*

The list is finRange N with its final element removed, mapped through j to P_N(j), and multiplied from left to right. Thus it is the printed ordered product P_(1,2) through P_(N-1,N), with zero-based formal site indices.

**Definition 1.12 (The three encoded local operators).**

$$\begin{aligned}\operatorname{sigmaPow}\left(0\right) = sigmaMinus\\\operatorname{sigmaPow}\left(1\right) = I\\\operatorname{sigmaPow}\left(2\right) = sigmaPlus\end{aligned}$$

*Formalization.* `D5/S3/Quantum/Dynamics/PronkoFredkinNonCyclicAnnihilation.sigmaPow` (`✓ std3`).

*Citation.* Andrei G. Pronko (2025). *Symmetries of the periodic Fredkin chain*. DOI: [10.1088/1751-8121/ae1644](https://doi.org/10.1088/1751-8121/ae1644). URL: <https://doi.org/10.1088/1751-8121/ae1644>.

*Commentary.*

The Fin 3 values 0, 1, and 2 encode exponents -1, 0, and 1. They select sigma-minus, the identity, and sigma-plus, respectively.

**Definition 1.13 (Pronko's constrained operator sum).**

$$\forall N \in \mathbb{N},\; \forall epsilon \in \mathbb{Z},\; \operatorname{Sigma}\left(N, epsilon\right) = \sum_{r: \operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(3\right), \sum_{i \in \operatorname{Fin}\left(N\right)} ((\operatorname{int}\left(\operatorname{val}\left(r\left(i\right)\right)\right)) - (1)) = epsilon} (\operatorname{tensor}\left(N, (i \mapsto \operatorname{sigmaPow}\left(r\left(i\right)\right))\right))$$

*Formalization.* `D5/S3/Quantum/Dynamics/PronkoFredkinNonCyclicAnnihilation.Sigma` (`✓ std3`).

*Citation.* Andrei G. Pronko (2025). *Symmetries of the periodic Fredkin chain*. DOI: [10.1088/1751-8121/ae1644](https://doi.org/10.1088/1751-8121/ae1644). URL: <https://doi.org/10.1088/1751-8121/ae1644>.

*Commentary.*

The sum ranges over all r from Fin N to Fin 3 whose encoded integer exponents sum to epsilon. Each summand is the sitewise Kronecker product of sigmaPow(r_i). Hence epsilon = 1 and epsilon = -1 are exactly the two operators in equation (3.1).

**Definition 1.14 (Pronko's Conjecture 1).**

$$claim \Leftrightarrow (\forall N \in \mathbb{N},\; (N \ge 3) \Rightarrow (\forall psi \in \left(\operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(2\right)\right) \to \mathbb{C},\; (psi \ne 0) \Rightarrow (\forall E \in \mathbb{C},\; \forall c \in \mathbb{C},\; (\operatorname{mulVec}\left(\operatorname{H}\left(N\right), psi\right) = (E) \cdot (psi)) \Rightarrow ((\operatorname{mulVec}\left(\operatorname{C}\left(N\right), psi\right) = (c) \cdot (psi)) \Rightarrow ((c \ne 1) \Rightarrow ((\operatorname{mulVec}\left(\operatorname{Sigma}\left(N, 1\right), psi\right) = 0) \land (\operatorname{mulVec}\left(\operatorname{Sigma}\left(N, -(1)\right), psi\right) = 0)))))))$$

*Formalization.* `D5/S3/Quantum/Dynamics/PronkoFredkinNonCyclicAnnihilation.claim` (`✓ std3`).

*Citation.* Andrei G. Pronko (2025). *Symmetries of the periodic Fredkin chain*. DOI: [10.1088/1751-8121/ae1644](https://doi.org/10.1088/1751-8121/ae1644). URL: <https://doi.org/10.1088/1751-8121/ae1644>.

*Commentary.*

The quantifiers make the source reading explicit: N is at least three; psi is a nonzero vector in the spin-word basis; E and c are complex eigenvalues; psi is simultaneously an H-eigenvector and a C-eigenvector; and non-cyclic means c is not one.

**Theorem 1.15 (Conjecture 1 holds).**

$$\forall N \in \mathbb{N},\; (N \ge 3) \Rightarrow (\forall psi \in \left(\operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(2\right)\right) \to \mathbb{C},\; (psi \ne 0) \Rightarrow (\forall E \in \mathbb{C},\; \forall c \in \mathbb{C},\; (\operatorname{mulVec}\left(\operatorname{H}\left(N\right), psi\right) = (E) \cdot (psi)) \Rightarrow ((\operatorname{mulVec}\left(\operatorname{C}\left(N\right), psi\right) = (c) \cdot (psi)) \Rightarrow ((c \ne 1) \Rightarrow ((\operatorname{mulVec}\left(\operatorname{Sigma}\left(N, 1\right), psi\right) = 0) \land (\operatorname{mulVec}\left(\operatorname{Sigma}\left(N, -(1)\right), psi\right) = 0))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/PronkoFredkinNonCyclicAnnihilation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Andrei G. Pronko (2025). *Symmetries of the periodic Fredkin chain*. DOI: [10.1088/1751-8121/ae1644](https://doi.org/10.1088/1751-8121/ae1644). URL: <https://doi.org/10.1088/1751-8121/ae1644>.

*Commentary.*

At each matrix entry (y, x), at most one Kronecker monomial has a nonzero value, determined site by site by (y_i, x_i), with total exponent equal to the number of up spins in y minus that in x. This monomial lies in the constrained sum (3.1) exactly when that difference equals epsilon; otherwise no term contributes. Every adjacent exchange preserves this weight. Consequently Sigma_epsilon P_N(j) = Sigma_epsilon, and folding through the printed ordered product gives Sigma_epsilon C_N = Sigma_epsilon. If C_N psi = c psi, then Sigma_epsilon psi = c Sigma_epsilon psi; c different from one forces the vector to vanish. The argument applies to every C-eigenvector with eigenvalue different from one. The proof uses no property of H; the hypothesis H psi = E psi is retained exactly as in Conjecture 1.

## References

- Truth anchor: `D5/S3/Quantum/Dynamics/PronkoFredkinNonCyclicAnnihilation.C`
- Truth anchor: `D5/S3/Quantum/Dynamics/PronkoFredkinNonCyclicAnnihilation.F`
- Truth anchor: `D5/S3/Quantum/Dynamics/PronkoFredkinNonCyclicAnnihilation.H`
- Truth anchor: `D5/S3/Quantum/Dynamics/PronkoFredkinNonCyclicAnnihilation.P`
- Truth anchor: `D5/S3/Quantum/Dynamics/PronkoFredkinNonCyclicAnnihilation.Pi`
- Truth anchor: `D5/S3/Quantum/Dynamics/PronkoFredkinNonCyclicAnnihilation.Sigma`
- Truth anchor: `D5/S3/Quantum/Dynamics/PronkoFredkinNonCyclicAnnihilation.claim`
- Truth anchor: `D5/S3/Quantum/Dynamics/PronkoFredkinNonCyclicAnnihilation.nDown`
- Truth anchor: `D5/S3/Quantum/Dynamics/PronkoFredkinNonCyclicAnnihilation.nUp`
- Truth anchor: `D5/S3/Quantum/Dynamics/PronkoFredkinNonCyclicAnnihilation.result`
- Truth anchor: `D5/S3/Quantum/Dynamics/PronkoFredkinNonCyclicAnnihilation.sigmaMinus`
- Truth anchor: `D5/S3/Quantum/Dynamics/PronkoFredkinNonCyclicAnnihilation.sigmaPlus`
- Truth anchor: `D5/S3/Quantum/Dynamics/PronkoFredkinNonCyclicAnnihilation.sigmaPow`
- Truth anchor: `D5/S3/Quantum/Dynamics/PronkoFredkinNonCyclicAnnihilation.site`
- Truth anchor: `D5/S3/Quantum/Dynamics/PronkoFredkinNonCyclicAnnihilation.tensor`
- Dependency: [D5/S3/Quantum/FiniteDimensional](../FiniteDimensional.md)
