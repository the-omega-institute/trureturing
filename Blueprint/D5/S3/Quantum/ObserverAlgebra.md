# Finite Observer Read-Update Skeleton

## Abstract

Finite-register read and reversible-update operators form a covariant noncommutative skeleton.

<a id="describe-specified-permutation-updates-form-a-covariant-group-action"></a>

**Theorem 1.1 (Specified permutation updates form a covariant group action).**

$$\forall I,\ \forall \tau,\sigma \in \operatorname{Perm}(I),\ \forall f:I\to\mathbb{C},\ \forall \psi:I\to\mathbb{C},\ U_{\operatorname{id}}\psi=\psi \land U_{\sigma\circ\tau}\psi=U_{\sigma}(U_{\tau}\psi) \land U_{\tau^{-1}}(U_{\tau}\psi)=\psi \land U_{\tau}(R_{f}\psi)=R_{f\circ\tau^{-1}}(U_{\tau}\psi)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/ObserverAlgebra.observer_update_covariant_group_skeleton` (`✓ std3`). ∎

*Citation.* Julian Schwinger (1960). *Unitary Operator Bases*. DOI: [10.1073/pnas.46.4.570](https://doi.org/10.1073/pnas.46.4.570).

*Commentary.*

The register index type may be arbitrary, including an empty type. Explicitly supplied permutations act by pullback on complex amplitude functions; identity, composition, inverse, and covariance with pointwise multiplication reads are proved together. This is a represented finite-register skeleton. It does not construct or identify the universal C*-crossed product, prove its universal property, exclude continuous hidden flows, derive discreteness or an integer action, or force quantum structure from a classical ontology. Original numerical-certificate disposition: neither observer-algebra CAS atom contains a numerical certificate.

<a id="describe-changed-read-values-witness-noncommutativity"></a>

**Theorem 1.2 (Changed read values witness noncommutativity).**

$$\forall I,\ \forall \tau \in \operatorname{Perm}(I),\ \forall f,\psi:I\to\mathbb{C},\ \forall i\in I,\ f(\tau^{-1}i)\neq f(i) \land \psi(\tau^{-1}i)\neq 0 \Rightarrow U_{\tau}(R_{f}\psi)\neq R_{f}(U_{\tau}\psi)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/ObserverAlgebra.observer_read_update_noncommutative` (`✓ std3`). ∎

*Citation.* Julian Schwinger (1960). *Unitary Operator Bases*. DOI: [10.1073/pnas.46.4.570](https://doi.org/10.1073/pnas.46.4.570).

*Commentary.*

Noncommutativity requires an explicit address i where the pulled-back read value differs from the current read value and a state whose predecessor amplitude is nonzero. That address is also the explicit inhabitability witness; there is no hidden Nonempty premise. The theorem does not say that every read function, reversible update, or state fails to commute, and it does not assert an abstract C*-algebra commutator identity. Original numerical-certificate disposition: neither observer-algebra CAS atom contains a numerical certificate.

## References

- Truth anchor: `D5/S3/Quantum/ObserverAlgebra.observer_read_update_noncommutative`
- Truth anchor: `D5/S3/Quantum/ObserverAlgebra.observer_update_covariant_group_skeleton`
