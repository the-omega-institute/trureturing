# Majorana matrices on fermionic Fock space

## Abstract

Occupation-space Majoranas satisfy Clifford relations and reverse number parity.

Nat denotes natural numbers, Bool the two occupation values false and true, Fin(N) the mode labels, and Assignment(N) the occupation basis Fin(N) → Bool. FullOperator(N) is the complex matrix algebra on that basis. fullC(N,j) is the Jordan–Wigner annihilator for mode j, with increasing-mode parity prefix. A star denotes matrix conjugate transpose, smul is complex scalar multiplication, ComplexI is the imaginary unit, pi is π, exp is the NormedSpace.exp operator exponential, and asComplex is the natural-to-complex cast. occupationCount(s) is the sum of the Boolean values as natural numbers, using the shared occupationCount definition. IsHermitian means equality to the conjugate transpose. Explicit mode-count arguments in these formulas display the corresponding implicit Lean parameters. PairType is the Cartesian product and fst and snd are its two projections. ite is the conditional expression. univ(T) is the finite set of all elements of T; filter selects those satisfying the displayed predicate, and card counts them.

**Definition 1.1 (The two Majoranas of a mode).**

$$\forall N \in \mathit{Nat},\; \forall j \in \mathrm{Fin}\left(N\right),\; \forall b \in \mathit{Bool},\; \mathrm{majorana}\left(N, j, b\right) = \mathrm{ite}\left(b, \mathrm{smul}\left(\mathrm{ComplexI}\left(\right), (\mathrm{fullC}\left(N, j\right) - \mathrm{fullC}\left(N, j\right)^{*})\right), \mathrm{fullC}\left(N, j\right) + \mathrm{fullC}\left(N, j\right)^{*}\right)$$

*Formalization.* `D5/S3/Quantum/Fermionic/FockMajoranaCarrier.majorana` (`✓ std3`).

*Citation.* Amir-Reza Negari; Farzin Salek; Zoltán Zimborás; Aram Harrow; Patrick Hayden; Jens Eisert (2026). *Approximation theorems for fermionic Gaussian states*. DOI: [10.48550/arXiv.2610.01860](https://doi.org/10.48550/arXiv.2610.01860). URL: <https://arxiv.org/abs/2610.01860v1>.

*Commentary.*

From the creation and annihilation operators we define Hermitian Majorana operators by [page 4, equation (11)]: γ₂ⱼ₋₁ = cⱼ + cⱼ†, γ₂ⱼ = i(cⱼ − cⱼ†), j = 1, …, m. Here b=false denotes the first operator and b=true the second. The carrier uses N modes in the fixed increasing order.

**Definition 1.2 (Number parity as an operator power).**

$$\forall N \in \mathit{Nat},\; \mathrm{numberParity}\left(N\right) = \mathrm{exp}\left(\mathrm{smul}\left(\mathrm{pi}\left(\right) \cdot \mathrm{ComplexI}\left(\right), \mathrm{numberOperator}\left(N\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Fermionic/FockMajoranaCarrier.numberParity` (`✓ std3`).

*Citation.* Amir-Reza Negari; Farzin Salek; Zoltán Zimborás; Aram Harrow; Patrick Hayden; Jens Eisert (2026). *Approximation theorems for fermionic Gaussian states*. DOI: [10.48550/arXiv.2610.01860](https://doi.org/10.48550/arXiv.2610.01860). URL: <https://arxiv.org/abs/2610.01860v1>.

*Commentary.*

The source defines N̂ = ∑ⱼ₌₁ᵐ cⱼ†cⱼ and P = (−1)^N̂ [page 3]. Number parity is defined by this operator power as P = exp(iπN̂). Its diagonal form follows from the occupation-factor calculation of the number operator.

**Definition 1.3 (Number operator).**

$$\forall N \in \mathit{Nat},\; \mathrm{numberOperator}\left(N\right) = \sum_{j:\mathrm{Fin}\left(N\right)}(\mathrm{fullC}\left(N, j\right)^{*} \cdot \mathrm{fullC}\left(N, j\right))$$

*Formalization.* `D5/S3/Quantum/Fermionic/FockMajoranaCarrier.numberOperator` (`✓ std3`).

*Citation.* Amir-Reza Negari; Farzin Salek; Zoltán Zimborás; Aram Harrow; Patrick Hayden; Jens Eisert (2026). *Approximation theorems for fermionic Gaussian states*. DOI: [10.48550/arXiv.2610.01860](https://doi.org/10.48550/arXiv.2610.01860). URL: <https://arxiv.org/abs/2610.01860v1>.

*Commentary.*

The number operator is the sum of the Jordan–Wigner creation-annihilation products over all modes.

**Theorem 1.4 (Number operator in the occupation basis).**

$$\forall N \in \mathit{Nat},\; \mathrm{numberOperator}\left(N\right) = \mathrm{diagonal}\left(s:\mathrm{Assignment}\left(N\right) \mapsto \mathrm{asComplex}\left(\mathrm{occupationCount}\left(s\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/FockMajoranaCarrier.numberOperator_eq_diagonal` (`✓ std3`). ∎

*Citation.* Amir-Reza Negari; Farzin Salek; Zoltán Zimborás; Aram Harrow; Patrick Hayden; Jens Eisert (2026). *Approximation theorems for fermionic Gaussian states*. DOI: [10.48550/arXiv.2610.01860](https://doi.org/10.48550/arXiv.2610.01860). URL: <https://arxiv.org/abs/2610.01860v1>.

*Commentary.*

The explicit occupation-factor calculation identifies the operator sum with the diagonal matrix of the occupied-mode count.

**Theorem 1.5 (Number parity in the occupation basis).**

$$\forall N \in \mathit{Nat},\; \mathrm{numberParity}\left(N\right) = \mathrm{diagonal}\left(s:\mathrm{Assignment}\left(N\right) \mapsto (-\mathrm{asComplex}\left(1\right))^{\mathrm{occupationCount}\left(s\right)}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/FockMajoranaCarrier.numberParity_eq_diagonal` (`✓ std3`). ∎

*Citation.* Amir-Reza Negari; Farzin Salek; Zoltán Zimborás; Aram Harrow; Patrick Hayden; Jens Eisert (2026). *Approximation theorems for fermionic Gaussian states*. DOI: [10.48550/arXiv.2610.01860](https://doi.org/10.48550/arXiv.2610.01860). URL: <https://arxiv.org/abs/2610.01860v1>.

*Commentary.*

The diagonal exponential evaluates to exp(iπ times the integer occupation count), hence to (−1) raised to that count.

**Theorem 1.6 (Clifford relations and odd parity).**

$$\forall N \in \mathit{Nat},\; (\mathrm{IsHermitian}\left(\mathrm{numberParity}\left(N\right)\right)) \land ((\mathrm{numberParity}\left(N\right) \cdot \mathrm{numberParity}\left(N\right) = (1:\mathrm{FullOperator}\left(N\right))) \land ((\forall p \in \mathrm{PairType}\left(\mathrm{Fin}\left(N\right), \mathit{Bool}\right),\; \mathrm{IsHermitian}\left(\mathrm{majorana}\left(N, \mathrm{fst}\left(p\right), \mathrm{snd}\left(p\right)\right)\right)) \land ((\forall p \in \mathrm{PairType}\left(\mathrm{Fin}\left(N\right), \mathit{Bool}\right),\; \forall q \in \mathrm{PairType}\left(\mathrm{Fin}\left(N\right), \mathit{Bool}\right),\; \mathrm{majorana}\left(N, \mathrm{fst}\left(p\right), \mathrm{snd}\left(p\right)\right) \cdot \mathrm{majorana}\left(N, \mathrm{fst}\left(q\right), \mathrm{snd}\left(q\right)\right) + \mathrm{majorana}\left(N, \mathrm{fst}\left(q\right), \mathrm{snd}\left(q\right)\right) \cdot \mathrm{majorana}\left(N, \mathrm{fst}\left(p\right), \mathrm{snd}\left(p\right)\right) = \mathrm{ite}\left(p = q, \mathrm{smul}\left(\mathrm{asComplex}\left(2\right), (1:\mathrm{FullOperator}\left(N\right))\right), \mathrm{zero}\left(\mathrm{FullOperator}\left(N\right)\right)\right)) \land (\forall p \in \mathrm{PairType}\left(\mathrm{Fin}\left(N\right), \mathit{Bool}\right),\; \mathrm{numberParity}\left(N\right) \cdot \mathrm{majorana}\left(N, \mathrm{fst}\left(p\right), \mathrm{snd}\left(p\right)\right) + \mathrm{majorana}\left(N, \mathrm{fst}\left(p\right), \mathrm{snd}\left(p\right)\right) \cdot \mathrm{numberParity}\left(N\right) = \mathrm{zero}\left(\mathrm{FullOperator}\left(N\right)\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/FockMajoranaCarrier.majorana_clifford_and_parity` (`✓ std3`). ∎

*Citation.* Amir-Reza Negari; Farzin Salek; Zoltán Zimborás; Aram Harrow; Patrick Hayden; Jens Eisert (2026). *Approximation theorems for fermionic Gaussian states*. DOI: [10.48550/arXiv.2610.01860](https://doi.org/10.48550/arXiv.2610.01860). URL: <https://arxiv.org/abs/2610.01860v1>.

*Commentary.*

They satisfy the Clifford relations [page 4, equation (12)]: {γₚ,γ_q} = 2δₚ,q 1, γₚ† = γₚ. The displayed statement verifies these relations for the actual Jordan–Wigner matrices and also verifies that number parity is a Hermitian involution which anticommutes with each generator. Products of two generators consequently commute with number parity.

## References

- Truth anchor: `D5/S3/Quantum/Fermionic/FockMajoranaCarrier.majorana`
- Truth anchor: `D5/S3/Quantum/Fermionic/FockMajoranaCarrier.majorana_clifford_and_parity`
- Truth anchor: `D5/S3/Quantum/Fermionic/FockMajoranaCarrier.numberOperator`
- Truth anchor: `D5/S3/Quantum/Fermionic/FockMajoranaCarrier.numberOperator_eq_diagonal`
- Truth anchor: `D5/S3/Quantum/Fermionic/FockMajoranaCarrier.numberParity`
- Truth anchor: `D5/S3/Quantum/Fermionic/FockMajoranaCarrier.numberParity_eq_diagonal`
- Dependency: [D5/S3/Quantum/FockSpace/ForbiddenNeighbourDeterminant](../FockSpace/ForbiddenNeighbourDeterminant.md)
- Dependency: [D5/S3/Quantum/SpinChains/SupersymmetricFermion/JordanWigner](../SpinChains/SupersymmetricFermion/JordanWigner.md)
