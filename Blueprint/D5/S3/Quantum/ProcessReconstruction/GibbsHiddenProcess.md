# Hidden Process Coherence at Gibbs Equilibrium

## Abstract

Two primitive GNS-symmetric semigroups at the same faithful Gibbs equilibrium have identical proper output channels at every time.

This is an extra-dynamics example alongside static process reconstruction. Fix at least two qubits, a Hamiltonian diagonal in the computational basis, a common inverse temperature β > 0, and a common reset rate γ > 0. Construct the two time-homogeneous semigroups using the rank-two Schur channels and reset to the same Gibbs density. These are explicit choices for the construction. The model specifies finite-system channels. A geometrically local physical bath, finite reservoir, or energy-preserving dilation requires additional hypotheses.

**Theorem 1.1 (Common faithful equilibrium and primitivity).**

Lean statement: `D5/S3/Quantum/ProcessReconstruction/GibbsHiddenProcess.gibbs_register_dynamics`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/ProcessReconstruction/GibbsHiddenProcess.gibbs_register_dynamics` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Eric A. Carlen and Jan Maas (2017). *Gradient flow and entropy inequalities for quantum Markov semigroups with detailed balance*. DOI: [10.1016/j.jfa.2017.05.003](https://doi.org/10.1016/j.jfa.2017.05.003). URL: <https://arxiv.org/abs/1609.01254v3>.

*Commentary.*

For H = diag(E), the equilibrium τ is the normalized diagonal matrix of Boltzmann weights exp(−β Eₓ). All weights are positive, including for degenerate H. The semigroup laws, stationarity of τ and finite-time Heisenberg GNS symmetry hold for both choices of the Schur channel. Each flow also commutes with the conjugations of the same H by the diagonal Hamiltonian covariance result.

For every t > 0 the reset has positive weight. On any nonzero positive input X it contributes a positive multiple of the faithful τ, so Γₜ(X) is positive definite. The reset weight tends to one, and the other component tends to zero on every input because the dephasing multipliers have absolute value at most one. The limit is X ↦ tr(X)τ, which gives uniqueness of the stationary density. The detailed balance convention is Carlen and Maas, arXiv:1609.01254v3, p. 8, Definition 2.10.

**Theorem 1.2 (Identical proper outputs and exact diamond separation).**

Lean statement: `D5/S3/Quantum/ProcessReconstruction/GibbsHiddenProcess.gibbs_hidden_process`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/ProcessReconstruction/GibbsHiddenProcess.gibbs_hidden_process` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Scott N. Walck and David W. Lyons (2008). *Only n-Qubit Greenberger-Horne-Zeilinger States Are Undetermined by Their Reduced Density Matrices*. DOI: [10.1103/PhysRevLett.100.050501](https://doi.org/10.1103/PhysRevLett.100.050501). URL: <https://arxiv.org/abs/0707.4428v2>.

*Acknowledgement.* Erkka Haapasalo, Teiko Heinosaari and Juha-Pekka Pellonpää (2012). *When do pieces determine the whole? Extremal marginals of a completely positive map*. DOI: [10.48550/arXiv.1209.5933](https://doi.org/10.48550/arXiv.1209.5933). URL: <https://arxiv.org/abs/1209.5933v1>.

*Commentary.*

Let u and v be the all-zero and all-one words. The common reset cancels when taking the channel difference. Only the two ordered coherences (u,v) and (v,u) differ, with dephasing multipliers 1 and exp(−2t). The difference is therefore exp(−γt)(1 − exp(−2t))/2 times the static rank-two channel difference. Tracing out any qubit kills both coherences. Equality holds as maps on the entire input algebra at every t ≥ 0, so it also holds after any finite reference extension.

The unhalved global diamond distance is exp(−γt)(1 − exp(−2t)), by the exact static value two and nonnegative scaling on amplified inputs. The balanced GHZ input attains the bound. The value is strictly positive for every t > 0.

Walck and Lyons, arXiv:0707.4428v2, p. 2, Main Result and the first direction of its proof, exhibit the same coherence loss for states. Haapasalo, Heinosaari and Pellonpää, arXiv:1209.5933v1, p. 8, Section 4, Definition 3 and Eqs. (12)–(13), formulate channel marginals directly. The equality and diamond formula above are for the two constructed semigroups.

## References

- Truth anchor: `D5/S3/Quantum/ProcessReconstruction/GibbsHiddenProcess.gibbs_hidden_process`
- Truth anchor: `D5/S3/Quantum/ProcessReconstruction/GibbsHiddenProcess.gibbs_register_dynamics`
- Dependency: [D5/S3/Quantum/Divergence/GibbsVariationalIdentity](../Divergence/GibbsVariationalIdentity.md)
- Dependency: [D5/S3/Quantum/Entanglement/ConicalDesignConcurrenceComparability](../Entanglement/ConicalDesignConcurrenceComparability.md)
- Dependency: [D5/S3/Quantum/ProcessReconstruction/HiddenProcessSemigroup](HiddenProcessSemigroup.md)
