# Majorana matrices on fermionic Fock space

## Abstract

Occupation-space Majoranas satisfy Clifford relations and reverse number parity.

Natural subtraction is truncated at zero. All other divisions are in Real or Complex. Scalar casts retain their target type. Matrix products are operator products, and Matrix.conjTranspose is conjugate transpose. Subtype.val is the value of a density; Equiv.symm applied to CStarMatrix.ofMatrix recovers its ordinary matrix. Assignment N is the occupation basis Fin N → Bool. Implicit Lean mode and dimension arguments may be displayed explicitly. Bracketed Fintype, DecidableEq and Nonempty assumptions are anonymous instance arguments.

**Definition 1.1 (The two Majoranas of a mode).**

$$\forall N \in \mathit{Nat},\; \forall j \in \mathrm{Fin}\left(N\right),\; \forall b \in \mathit{Bool},\; \mathrm{majorana}\left(N, j, b\right) = \mathrm{ite}\left(b, \operatorname{SMul}.\operatorname{smul}\left(\operatorname{Complex}.\operatorname{I}, (\mathrm{fullC}\left(N, j\right) - \mathrm{fullC}\left(N, j\right)^{*})\right), \mathrm{fullC}\left(N, j\right) + \mathrm{fullC}\left(N, j\right)^{*}\right)$$

*Formalization.* `D5/S3/Quantum/Fermionic/FockMajoranaCarrier.majorana` (`✓ std3`).

*Citation.* Amir-Reza Negari; Farzin Salek; Zoltán Zimborás; Aram Harrow; Patrick Hayden; Jens Eisert (2026). *Approximation theorems for fermionic Gaussian states*. DOI: [10.48550/arXiv.2610.01860](https://doi.org/10.48550/arXiv.2610.01860). URL: <https://arxiv.org/abs/2610.01860v1>.

*Commentary.*

From the creation and annihilation operators we define Hermitian Majorana operators by [page 4, equation (11)]: γ₂ⱼ₋₁ = cⱼ + cⱼ†, γ₂ⱼ = i(cⱼ − cⱼ†), j = 1, …, m. Here b=false denotes the first operator and b=true the second. The carrier uses N modes in the fixed increasing order.

**Definition 1.2 (Number parity as an operator power).**

$$\forall N \in \mathit{Nat},\; \mathrm{numberParity}\left(N\right) = \operatorname{NormedSpace}.\operatorname{exp}\left(\operatorname{SMul}.\operatorname{smul}\left(\operatorname{Real}.\operatorname{pi} \cdot \operatorname{Complex}.\operatorname{I}, \mathrm{numberOperator}\left(N\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Fermionic/FockMajoranaCarrier.numberParity` (`✓ std3`).

*Citation.* Amir-Reza Negari; Farzin Salek; Zoltán Zimborás; Aram Harrow; Patrick Hayden; Jens Eisert (2026). *Approximation theorems for fermionic Gaussian states*. DOI: [10.48550/arXiv.2610.01860](https://doi.org/10.48550/arXiv.2610.01860). URL: <https://arxiv.org/abs/2610.01860v1>.

*Commentary.*

“The number operator and parity operator are given by” [printed page 3]: N̂ = ∑ⱼ₌₁ᵐ cⱼ†cⱼ, P = (−1)^N̂. The operator-power convention is P = exp(iπN̂). Its diagonal form follows from the occupation-factor calculation of the number operator.

**Definition 1.3 (Number operator).**

$$\forall N \in \mathit{Nat},\; \mathrm{numberOperator}\left(N\right) = \sum_{j:\mathrm{Fin}\left(N\right)}(\mathrm{fullC}\left(N, j\right)^{*} \cdot \mathrm{fullC}\left(N, j\right))$$

*Formalization.* `D5/S3/Quantum/Fermionic/FockMajoranaCarrier.numberOperator` (`✓ std3`).

*Citation.* Amir-Reza Negari; Farzin Salek; Zoltán Zimborás; Aram Harrow; Patrick Hayden; Jens Eisert (2026). *Approximation theorems for fermionic Gaussian states*. DOI: [10.48550/arXiv.2610.01860](https://doi.org/10.48550/arXiv.2610.01860). URL: <https://arxiv.org/abs/2610.01860v1>.

*Commentary.*

“The number operator and parity operator are given by” [printed page 3]: N̂ = ∑ⱼ₌₁ᵐ cⱼ†cⱼ, P = (−1)^N̂. Here fullC is the Jordan–Wigner annihilator and N counts all global modes.

**Theorem 1.4 (Number operator in the occupation basis).**

$$\forall N \in \mathit{Nat},\; \mathrm{numberOperator}\left(N\right) = \operatorname{Matrix}.\operatorname{diagonal}\left(s:\mathrm{Assignment}\left(N\right) \mapsto (\mathrm{occupationCount}\left(s\right):\mathit{Complex})\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/FockMajoranaCarrier.numberOperator_eq_diagonal` (`✓ std3`). ∎

*Citation.* Amir-Reza Negari; Farzin Salek; Zoltán Zimborás; Aram Harrow; Patrick Hayden; Jens Eisert (2026). *Approximation theorems for fermionic Gaussian states*. DOI: [10.48550/arXiv.2610.01860](https://doi.org/10.48550/arXiv.2610.01860). URL: <https://arxiv.org/abs/2610.01860v1>.

*Commentary.*

The explicit occupation-factor calculation identifies the operator sum with the diagonal matrix of the occupied-mode count.

**Theorem 1.5 (Number parity in the occupation basis).**

$$\forall N \in \mathit{Nat},\; \mathrm{numberParity}\left(N\right) = \operatorname{Matrix}.\operatorname{diagonal}\left(s:\mathrm{Assignment}\left(N\right) \mapsto (-(1:\mathit{Complex}))^{\mathrm{occupationCount}\left(s\right)}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/FockMajoranaCarrier.numberParity_eq_diagonal` (`✓ std3`). ∎

*Citation.* Amir-Reza Negari; Farzin Salek; Zoltán Zimborás; Aram Harrow; Patrick Hayden; Jens Eisert (2026). *Approximation theorems for fermionic Gaussian states*. DOI: [10.48550/arXiv.2610.01860](https://doi.org/10.48550/arXiv.2610.01860). URL: <https://arxiv.org/abs/2610.01860v1>.

*Commentary.*

The diagonal exponential evaluates to exp(iπ times the integer occupation count), hence to (−1) raised to that count.

**Theorem 1.6 (Clifford relations and odd parity).**

$$\forall N \in \mathit{Nat},\; (\operatorname{Matrix}.\operatorname{IsHermitian}\left(\mathrm{numberParity}\left(N\right)\right)) \land ((\mathrm{numberParity}\left(N\right) \cdot \mathrm{numberParity}\left(N\right) = (1:\mathrm{FullOperator}\left(N\right))) \land ((\forall p \in \operatorname{Prod}\left(\mathrm{Fin}\left(N\right), \mathit{Bool}\right),\; \operatorname{Matrix}.\operatorname{IsHermitian}\left(\mathrm{majorana}\left(N, \operatorname{Prod}.\operatorname{fst}\left(p\right), \operatorname{Prod}.\operatorname{snd}\left(p\right)\right)\right)) \land ((\forall p \in \operatorname{Prod}\left(\mathrm{Fin}\left(N\right), \mathit{Bool}\right),\; \forall q \in \operatorname{Prod}\left(\mathrm{Fin}\left(N\right), \mathit{Bool}\right),\; \mathrm{majorana}\left(N, \operatorname{Prod}.\operatorname{fst}\left(p\right), \operatorname{Prod}.\operatorname{snd}\left(p\right)\right) \cdot \mathrm{majorana}\left(N, \operatorname{Prod}.\operatorname{fst}\left(q\right), \operatorname{Prod}.\operatorname{snd}\left(q\right)\right) + \mathrm{majorana}\left(N, \operatorname{Prod}.\operatorname{fst}\left(q\right), \operatorname{Prod}.\operatorname{snd}\left(q\right)\right) \cdot \mathrm{majorana}\left(N, \operatorname{Prod}.\operatorname{fst}\left(p\right), \operatorname{Prod}.\operatorname{snd}\left(p\right)\right) = \mathrm{ite}\left(p = q, \operatorname{SMul}.\operatorname{smul}\left((2:\mathit{Complex}), (1:\mathrm{FullOperator}\left(N\right))\right), (0:\mathrm{FullOperator}\left(N\right))\right)) \land (\forall p \in \operatorname{Prod}\left(\mathrm{Fin}\left(N\right), \mathit{Bool}\right),\; \mathrm{numberParity}\left(N\right) \cdot \mathrm{majorana}\left(N, \operatorname{Prod}.\operatorname{fst}\left(p\right), \operatorname{Prod}.\operatorname{snd}\left(p\right)\right) + \mathrm{majorana}\left(N, \operatorname{Prod}.\operatorname{fst}\left(p\right), \operatorname{Prod}.\operatorname{snd}\left(p\right)\right) \cdot \mathrm{numberParity}\left(N\right) = (0:\mathrm{FullOperator}\left(N\right))))))$$

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
