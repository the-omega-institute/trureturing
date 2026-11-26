# Reset Semigroups from Rank-Two Channels

## Abstract

Explicit finite reset semigroups from the rank-two Schur channels.

**Theorem 1.1 (Finite channel construction and time composition).**

Lean statement: `D5/S3/Quantum/ProcessReconstruction/HiddenProcessSemigroup.flow_add`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/ProcessReconstruction/HiddenProcessSemigroup.flow_add` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let Φ be either static rank-two channel and Rτ(X) = tr(X)τ for a diagonal density τ. Write Φ as the average of conjugations by the two commuting diagonal involutions of the static construction. For t ≥ 0 mix each conjugation with the identity using identity weight p = (1 + exp(−t))/2 and compose the two mixtures. This gives a CPTP channel Tₜ, with matrix-unit multipliers exp(t(cₓᵧ − 1)), where cₓᵧ is the multiplier of Φ.

With a common rate γ, the finite-time channel is Γₜ = exp(−γt) Tₜ + (1 − exp(−γt)) Rτ. The Schur multipliers multiply under time addition. The dephasing channels preserve trace and fix τ, so TₜRτ = RτTₜ = Rτ, and Rτ² = Rτ. These identities give ΓₛΓₜ = Γₛ₊ₜ, with Γ₀ the identity.

**Theorem 1.2 (Continuity in channel operator norm).**

Lean statement: `D5/S3/Quantum/ProcessReconstruction/HiddenProcessSemigroup.flow_norm_continuous`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/ProcessReconstruction/HiddenProcessSemigroup.flow_norm_continuous` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The real exponential coefficients are continuous. Finite dimensionality of the matrix algebra gives continuity in the norm of continuous linear maps.

**Theorem 1.3 (Right derivative at time zero).**

Lean statement: `D5/S3/Quantum/ProcessReconstruction/HiddenProcessSemigroup.flow_generator`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/ProcessReconstruction/HiddenProcessSemigroup.flow_generator` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Differentiating the two exponential coefficients at zero on each matrix entry yields L = Φ − id + γ(Rτ − id).

**Theorem 1.4 (Trace dual of the finite-time channel).**

Lean statement: `D5/S3/Quantum/ProcessReconstruction/HiddenProcessSemigroup.heisenberg_trace_dual`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/ProcessReconstruction/HiddenProcessSemigroup.heisenberg_trace_dual` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The real symmetric Schur multiplier gives the same Schur part in the trace-dual observable map. The dual reset sends A to tr(τA) I, and Γₜ is unital in the Heisenberg picture.

**Theorem 1.5 (GNS detailed balance for the observable semigroup).**

Lean statement: `D5/S3/Quantum/ProcessReconstruction/HiddenProcessSemigroup.heisenberg_gns_symmetric`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/ProcessReconstruction/HiddenProcessSemigroup.heisenberg_gns_symmetric` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Eric A. Carlen and Jan Maas (2017). *Gradient flow and entropy inequalities for quantum Markov semigroups with detailed balance*. DOI: [10.1016/j.jfa.2017.05.003](https://doi.org/10.1016/j.jfa.2017.05.003). URL: <https://arxiv.org/abs/1609.01254v3>.

*Commentary.*

The matrix units are orthogonal in the pairing tr(τ A†B). The Schur multipliers are real, and the dual reset is the orthogonal projection onto the identity line for faithful τ. This proves symmetry at every time and uses the same pairing as Carlen and Maas, arXiv:1609.01254v3, p. 6, Definition 2.2 and Eq. (2.3) at s = 1, and p. 8, Definition 2.10.

**Theorem 1.6 (GNS symmetry of the observable generator).**

Lean statement: `D5/S3/Quantum/ProcessReconstruction/HiddenProcessSemigroup.heisenberg_generator_gns_symmetric`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/ProcessReconstruction/HiddenProcessSemigroup.heisenberg_generator_gns_symmetric` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Eric A. Carlen and Jan Maas (2017). *Gradient flow and entropy inequalities for quantum Markov semigroups with detailed balance*. DOI: [10.1016/j.jfa.2017.05.003](https://doi.org/10.1016/j.jfa.2017.05.003). URL: <https://arxiv.org/abs/1609.01254v3>.

*Commentary.*

The generator uses the real exponential rates as its Schur coefficients and γ as the coefficient of the dual reset. Both terms are symmetric for the same pairing. The observable generator is also the entrywise right derivative at zero.

**Theorem 1.7 (Covariance under the diagonal Hamiltonian).**

Lean statement: `D5/S3/Quantum/ProcessReconstruction/HiddenProcessSemigroup.flow_commutes_hamiltonian_propagator`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/ProcessReconstruction/HiddenProcessSemigroup.flow_commutes_hamiltonian_propagator` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Eric A. Carlen and Jan Maas (2017). *Gradient flow and entropy inequalities for quantum Markov semigroups with detailed balance*. DOI: [10.1016/j.jfa.2017.05.003](https://doi.org/10.1016/j.jfa.2017.05.003). URL: <https://arxiv.org/abs/1609.01254v3>.

*Commentary.*

Conjugation by exp(−isH) for diagonal H multiplies the same matrix units by phases, so it commutes with the Schur component. The reset commutes because conjugation preserves trace and fixes τ. For a Gibbs τ at positive inverse temperature, this is the Hamiltonian covariance associated to its modular group. See Carlen and Maas, arXiv:1609.01254v3, p. 4, Definition 1.1 and Eq. (1.2), and pp. 8–9, Theorem 2.9(1) and Remark 2.11, Eq. (2.8).

## References

- Truth anchor: `D5/S3/Quantum/ProcessReconstruction/HiddenProcessSemigroup.flow_add`
- Truth anchor: `D5/S3/Quantum/ProcessReconstruction/HiddenProcessSemigroup.flow_commutes_hamiltonian_propagator`
- Truth anchor: `D5/S3/Quantum/ProcessReconstruction/HiddenProcessSemigroup.flow_generator`
- Truth anchor: `D5/S3/Quantum/ProcessReconstruction/HiddenProcessSemigroup.flow_norm_continuous`
- Truth anchor: `D5/S3/Quantum/ProcessReconstruction/HiddenProcessSemigroup.heisenberg_generator_gns_symmetric`
- Truth anchor: `D5/S3/Quantum/ProcessReconstruction/HiddenProcessSemigroup.heisenberg_gns_symmetric`
- Truth anchor: `D5/S3/Quantum/ProcessReconstruction/HiddenProcessSemigroup.heisenberg_trace_dual`
- Dependency: [D5/S3/Quantum/Foundation/FinitePreparationChannel](../Foundation/FinitePreparationChannel.md)
- Dependency: [D5/S3/Quantum/ProcessReconstruction/RankTwoHiddenProcess](RankTwoHiddenProcess.md)
