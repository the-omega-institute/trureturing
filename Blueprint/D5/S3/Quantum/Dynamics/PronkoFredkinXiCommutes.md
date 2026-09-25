# Pronko's Dyck-class operator commutes with the periodic Fredkin Hamiltonian

## Abstract

Spin words of the periodic Fredkin chain are read as lattice paths and sorted into Dyck classes. Pronko's diagonal operator Xi weights the balanced classes by alternating signs, and it commutes with the periodic Fredkin Hamiltonian.

**Definition 1.1 (Height of a spin-word path).**

$$\forall N \in \mathbb{N},\; \forall ell \in \operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(2\right),\; \forall i \in \mathbb{N},\; \operatorname{pathHeight}\left(ell, i\right) = \sum_{t \in \operatorname{Fin}\left(N\right), t < i} (\operatorname{ite}\left(ell\left(t\right) = 0, 1, -(1)\right))$$

*Formalization.* `D5/S3/Quantum/Dynamics/PronkoFredkinXiCommutes.pathHeight` (`✓ std3`).

*Citation.* Andrei G. Pronko (2025). *Symmetries of the periodic Fredkin chain*. DOI: [10.1088/1751-8121/ae1644](https://doi.org/10.1088/1751-8121/ae1644). URL: <https://doi.org/10.1088/1751-8121/ae1644>.

*Commentary.*

The letter 0 (spin up) is a step up and the letter 1 (spin down) is a step down; the height after i letters sums these steps over the sites t in Fin N with t below i.

**Definition 1.2 (Membership in the Dyck class C_(a,b)(N)).**

$$\forall N \in \mathbb{N},\; \forall a \in \mathbb{N},\; \forall b \in \mathbb{N},\; \forall ell \in \operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(2\right),\; \operatorname{inClass}\left(N, a, b, ell\right) \Leftrightarrow ((\forall i \in \mathbb{N},\; (i \le N) \Rightarrow (0 \le (a) + (\operatorname{pathHeight}\left(ell, i\right)))) \land ((\exists i \in \mathbb{N},\; (i \le N) \land ((a) + (\operatorname{pathHeight}\left(ell, i\right)) = 0)) \land ((a) + (\operatorname{pathHeight}\left(ell, N\right)) = b)))$$

*Formalization.* `D5/S3/Quantum/Dynamics/PronkoFredkinXiCommutes.inClass` (`✓ std3`).

*Citation.* Andrei G. Pronko (2025). *Symmetries of the periodic Fredkin chain*. DOI: [10.1088/1751-8121/ae1644](https://doi.org/10.1088/1751-8121/ae1644). URL: <https://doi.org/10.1088/1751-8121/ae1644>.

*Commentary.*

Started at height a, the path of the word stays at height at least zero, touches height zero at some index between 0 and N, and ends at height b, as in section 2.2.

**Definition 1.3 (Pronko's operator Xi).**

$$\forall N \in \mathbb{N},\; \operatorname{Xi}\left(N\right) = \sum_{k \in \operatorname{Finset.range}\left((\left\lfloor\frac{N}{2}\right\rfloor) + (1)\right)} (((-(1))^{k}) \cdot (\sum_{ell: \operatorname{inClass}\left(N, k, k, ell\right)} (\operatorname{tensor}\left(N, (i \mapsto \operatorname{ite}\left(ell\left(i\right) = 0, nUp, nDown\right))\right))))$$

*Formalization.* `D5/S3/Quantum/Dynamics/PronkoFredkinXiCommutes.Xi` (`✓ std3`).

*Citation.* Andrei G. Pronko (2025). *Symmetries of the periodic Fredkin chain*. DOI: [10.1088/1751-8121/ae1644](https://doi.org/10.1088/1751-8121/ae1644). URL: <https://doi.org/10.1088/1751-8121/ae1644>.

*Commentary.*

The outer sum runs over k from 0 to the floor of N/2 with sign (-1)^k; the inner sum runs over the words of the class C_(k,k)(N), each contributing the product of the one-site spin-up and spin-down projections selected by its letters, as in equation (4.1).

**Definition 1.4 (The commutation relation of section 4.1).**

$$claim \Leftrightarrow (\forall N \in \mathbb{N},\; (3 \le N) \Rightarrow ((\operatorname{Even}\left(N\right)) \Rightarrow ((\operatorname{Xi}\left(N\right)) \cdot (\operatorname{H}\left(N\right)) = (\operatorname{H}\left(N\right)) \cdot (\operatorname{Xi}\left(N\right)))))$$

*Formalization.* `D5/S3/Quantum/Dynamics/PronkoFredkinXiCommutes.claim` (`✓ std3`).

*Citation.* Andrei G. Pronko (2025). *Symmetries of the periodic Fredkin chain*. DOI: [10.1088/1751-8121/ae1644](https://doi.org/10.1088/1751-8121/ae1644). URL: <https://doi.org/10.1088/1751-8121/ae1644>.

*Commentary.*

For every even number of sites N at least three, Xi commutes with the periodic Fredkin Hamiltonian H of equation (2.3).

**Theorem 1.5 (Xi commutes with the Hamiltonian).**

$$\forall N \in \mathbb{N},\; (3 \le N) \Rightarrow ((\operatorname{Even}\left(N\right)) \Rightarrow ((\operatorname{Xi}\left(N\right)) \cdot (\operatorname{H}\left(N\right)) = (\operatorname{H}\left(N\right)) \cdot (\operatorname{Xi}\left(N\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/PronkoFredkinXiCommutes.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Andrei G. Pronko (2025). *Symmetries of the periodic Fredkin chain*. DOI: [10.1088/1751-8121/ae1644](https://doi.org/10.1088/1751-8121/ae1644). URL: <https://doi.org/10.1088/1751-8121/ae1644>.

*Commentary.*

Xi is diagonal: its value at a word is (-1)^a when the word is balanced and lies in C_(a,a)(N), where a is the negative of the smallest height, and zero otherwise. The off-diagonal part of the density F_(j,j+1,j+2) exchanges the letters at j + 1 and j + 2 when the letter at j is up, or the letters at j and j + 1 when the letter at j + 2 is down, indices modulo N. Such an exchange keeps the number of up letters. When it does not wrap around the end of the word it changes a single height by two, and the control letter forces the smaller of the two values to occur at another index, so the smallest height and a are unchanged. When it exchanges the last and the first letter, every interior height moves by the same amount, and the control letter forces an interior height at most zero in both words, so a changes by zero or two. Hence a has the same parity at the two words, Xi commutes with every density, and so with their sum H. The argument uses only N at least three.

## References

- Truth anchor: `D5/S3/Quantum/Dynamics/PronkoFredkinXiCommutes.Xi`
- Truth anchor: `D5/S3/Quantum/Dynamics/PronkoFredkinXiCommutes.claim`
- Truth anchor: `D5/S3/Quantum/Dynamics/PronkoFredkinXiCommutes.inClass`
- Truth anchor: `D5/S3/Quantum/Dynamics/PronkoFredkinXiCommutes.pathHeight`
- Truth anchor: `D5/S3/Quantum/Dynamics/PronkoFredkinXiCommutes.result`
- Dependency: [D5/S3/Quantum/Dynamics/PronkoFredkinNonCyclicAnnihilation](PronkoFredkinNonCyclicAnnihilation.md)
