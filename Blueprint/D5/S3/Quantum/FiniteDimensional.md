# Finite-Dimensional Quantum Skeletons

## Abstract

Finite-dimensional Pauli, no-character, and trace-probability skeletons.

<a id="describe-the-standard-qubit-weyl-pair-has-the-pauli-star-skeleton"></a>

**Theorem 1.1 (The standard qubit Weyl pair has the Pauli star skeleton).**

$ZX=-(XZ) \land X^{*}=X \land Z^{*}=Z \land X^{2}=I \land Z^{2}=I$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FiniteDimensional.qubit_weyl_star` (`✓ std3`). ∎

*Citation.* Julian Schwinger (1960). *Unitary Operator Bases*. DOI: [10.1073/pnas.46.4.570](https://doi.org/10.1073/pnas.46.4.570).

*Commentary.*

The standard two-dimensional Pauli X and Z matrices anticommute, are self-adjoint, and square to the identity. This is only the d = 2 Weyl specialization: it does not identify an arbitrary observer window with a full matrix algebra, prove prime-power tensor factorization or a general qudit relation, or derive the structure from a classical ontology. Original numerical-certificate claim not formalized: the source atom's matrix-unit relations with exact zero certificate error.

<a id="describe-the-qubit-matrix-algebra-has-no-complex-algebra-character"></a>

**Theorem 1.2 (The qubit matrix algebra has no complex-algebra character).**

$\operatorname{IsEmpty}(\operatorname{QubitMatrix}\to_{\mathbb{C}\text{-alg}}\mathbb{C})$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FiniteDimensional.qubit_matrix_algebra_has_no_character` (`✓ std3`). ∎

*Citation.* Gerard J. Murphy (1990). *C*-Algebras and Operator Theory*. DOI: [10.1016/C2009-0-22289-6](https://doi.org/10.1016/C2009-0-22289-6).

*Commentary.*

No unital complex-algebra homomorphism from the two-by-two full matrix algebra to the complex numbers exists. The proof uses the stronger global additive and multiplicative laws of an algebra character. `D5/L/kochen1968problem` is contextual background only: this declaration is not the Kochen-Specker valuation theorem, does not exclude qubit noncontextual projection valuations, and proves neither the arbitrary M_n result for n greater than one nor any CHSH, hidden-address, or probability-is-not-ignorance claim.

<a id="describe-positive-trace-one-matrices-give-nonnegative-projection-weights"></a>

**Theorem 1.3 (Positive trace-one matrices give nonnegative projection weights).**

$$\forall n\ [\operatorname{Fintype}(n)]\ [\operatorname{DecidableEq}(n)],\ \forall \rho \in M_{n}(\mathbb{C}),\ \operatorname{PosSemidef}(\rho) \land \operatorname{tr}(\rho)=1 \Rightarrow \operatorname{bornProbability}(\rho,I)=1 \land (\forall P,Q,\ \operatorname{bornProbability}(\rho,P+Q)=\operatorname{bornProbability}(\rho,P)+\operatorname{bornProbability}(\rho,Q)) \land (\forall P,\ P^{*}=P \Rightarrow P^{2}=P \Rightarrow 0\leq\operatorname{bornProbability}(\rho,P))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FiniteDimensional.born_probability_skeleton` (`✓ std3`). ∎

*Citation.* Andrew M. Gleason (1957). *Measures on the Closed Subspaces of a Hilbert Space*. DOI: [10.1512/iumj.1957.6.56050](https://doi.org/10.1512/iumj.1957.6.56050).

*Commentary.*

For a positive semidefinite finite complex matrix rho with trace one, P maps to trace(rho P), is normalized at the identity, is additive, and is nonnegative for every self-adjoint idempotent P. Positivity follows from the compression P rho P* and does not assume that rho commutes with P. `D5/L/born1926zur` records the historical Born context only. The declaration proves no Gleason representation or uniqueness theorem, no rank-one pure-state modulus-square reduction, no ledger-derived noncontextuality, no harmonic or quartic numerical certificate, and no forced classical-to-quantum origin. Original numerical-certificate claim not formalized: the source atom's separate Born control group balance to 10^-16.

## References

- Truth anchor: `D5/S3/Quantum/FiniteDimensional.born_probability_skeleton`
- Truth anchor: `D5/S3/Quantum/FiniteDimensional.qubit_matrix_algebra_has_no_character`
- Truth anchor: `D5/S3/Quantum/FiniteDimensional.qubit_weyl_star`
