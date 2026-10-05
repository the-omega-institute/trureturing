# Subsystem Lanczos positivity fails

## Abstract

The first squared subsystem Lanczos coefficient can be negative for an entangled two-qubit state.

**Definition 1.1 (The evolved pure density).**

$$\forall a \in \mathbb{N},\; \forall b \in \mathbb{N},\; \forall psi \in \operatorname{EuclideanSpace}\left(\mathbb{C}, \operatorname{Prod}\left(\operatorname{Fin}\left(a\right), \operatorname{Fin}\left(b\right)\right)\right),\; \forall H \in \operatorname{Matrix}\left(\operatorname{Prod}\left(\operatorname{Fin}\left(a\right), \operatorname{Fin}\left(b\right)\right), \operatorname{Prod}\left(\operatorname{Fin}\left(a\right), \operatorname{Fin}\left(b\right)\right), \mathbb{C}\right),\; \forall t \in \mathbb{R},\; \operatorname{hamiltonianPropagator}\left(H, t\right) = \operatorname{exp}\left(((-i) \cdot (t)) \cdot (H)\right) \land \operatorname{rho}\left(psi, H, t\right) = ((\operatorname{hamiltonianPropagator}\left(H, t\right)) \cdot (\operatorname{rankOneDensity}\left(psi\right))) \cdot (\operatorname{conjTranspose}\left(\operatorname{hamiltonianPropagator}\left(H, t\right)\right))$$

*Formalization.* `D5/S3/Quantum/Dynamics/SubsystemLanczosPositivityRefutation.rho` (`✓ std3`).

*Citation.* Pawel Caputa, Giuseppe Di Giulio, Tran Quang Loc (2026). *Complexity Inequalities for Quantum Subsystems*. DOI: [10.48550/arXiv.2606.20790](https://doi.org/10.48550/arXiv.2606.20790). URL: <https://arxiv.org/abs/2606.20790v2>.

*Commentary.*

Section 3.1, printed p. 17, writes: "full density matrix ρ(t)=|ψ(t)⟩⟨ψ(t)| before the partial trace". The initial pure density is rankOneDensity(ψ) = ψψᴴ, using the existing rank-one density definition. The source exponential exp(−i t H) equals hamiltonianPropagator(H,t): real scalar multiplication followed by the generator −iH gives the same exponent. Conjugation by this propagator gives the full evolved density. The symbols a and b are the finite subsystem dimensions; matrix products are ordinary matrix multiplication, and matrix norms use the L² operator norm.

**Definition 1.2 (The reduced density).**

$$\forall a \in \mathbb{N},\; \forall b \in \mathbb{N},\; \forall psi \in \operatorname{EuclideanSpace}\left(\mathbb{C}, \operatorname{Prod}\left(\operatorname{Fin}\left(a\right), \operatorname{Fin}\left(b\right)\right)\right),\; \forall H \in \operatorname{Matrix}\left(\operatorname{Prod}\left(\operatorname{Fin}\left(a\right), \operatorname{Fin}\left(b\right)\right), \operatorname{Prod}\left(\operatorname{Fin}\left(a\right), \operatorname{Fin}\left(b\right)\right), \mathbb{C}\right),\; \forall t \in \mathbb{R},\; \operatorname{rhoA}\left(psi, H, t\right) = \operatorname{partialTraceRight}\left(\operatorname{rho}\left(psi, H, t\right)\right)$$

*Formalization.* `D5/S3/Quantum/Dynamics/SubsystemLanczosPositivityRefutation.rhoA` (`✓ std3`).

*Citation.* Pawel Caputa, Giuseppe Di Giulio, Tran Quang Loc (2026). *Complexity Inequalities for Quantum Subsystems*. DOI: [10.48550/arXiv.2606.20790](https://doi.org/10.48550/arXiv.2606.20790). URL: <https://arxiv.org/abs/2606.20790v2>.

*Commentary.*

Section 3.1, printed p. 14, says: "we have a corresponding non-unitary evolution for the reduced density matrices ρ_A(t) and ρ_B(t)." The operation partialTraceRight sums the B diagonal index of the full density and returns the matrix on Fin a.

**Definition 1.3 (The subsystem return amplitude).**

$$\forall a \in \mathbb{N},\; \forall b \in \mathbb{N},\; \forall psi \in \operatorname{EuclideanSpace}\left(\mathbb{C}, \operatorname{Prod}\left(\operatorname{Fin}\left(a\right), \operatorname{Fin}\left(b\right)\right)\right),\; \forall H \in \operatorname{Matrix}\left(\operatorname{Prod}\left(\operatorname{Fin}\left(a\right), \operatorname{Fin}\left(b\right)\right), \operatorname{Prod}\left(\operatorname{Fin}\left(a\right), \operatorname{Fin}\left(b\right)\right), \mathbb{C}\right),\; \forall t \in \mathbb{R},\; \operatorname{returnAmplitude}\left(psi, H, t\right) = \frac{\operatorname{re}\left(\operatorname{trace}\left((\operatorname{rhoA}\left(psi, H, t\right)) \cdot (\operatorname{rhoA}\left(psi, H, 0\right))\right)\right)}{\operatorname{re}\left(\operatorname{trace}\left((\operatorname{rhoA}\left(psi, H, 0\right)) \cdot (\operatorname{rhoA}\left(psi, H, 0\right))\right)\right)}$$

*Formalization.* `D5/S3/Quantum/Dynamics/SubsystemLanczosPositivityRefutation.returnAmplitude` (`✓ std3`).

*Citation.* Pawel Caputa, Giuseppe Di Giulio, Tran Quang Loc (2026). *Complexity Inequalities for Quantum Subsystems*. DOI: [10.48550/arXiv.2606.20790](https://doi.org/10.48550/arXiv.2606.20790). URL: <https://arxiv.org/abs/2606.20790v2>.

*Commentary.*

Section 3.1, printed pp. 14-15, defines R_A(t) = Tr(ρ_A(t)ρ_A(0))/Tr(ρ_A(0)²). It says: "For this reason, throughout the manuscript we refer to R_A(t) as the subsystem return amplitude." The real part selects the real carrier of these trace overlaps; the source explicitly notes R_A*(t) = R_A(t). The denominator is the initial reduced purity, without a time-dependent normalization. Equation labels generaldef_RL and subsystem moments identify the definitions; the v2 PDF numbers them (3.2) and (3.3).

**Definition 1.4 (Moments at zero).**

$$\forall a \in \mathbb{N},\; \forall b \in \mathbb{N},\; \forall psi \in \operatorname{EuclideanSpace}\left(\mathbb{C}, \operatorname{Prod}\left(\operatorname{Fin}\left(a\right), \operatorname{Fin}\left(b\right)\right)\right),\; \forall H \in \operatorname{Matrix}\left(\operatorname{Prod}\left(\operatorname{Fin}\left(a\right), \operatorname{Fin}\left(b\right)\right), \operatorname{Prod}\left(\operatorname{Fin}\left(a\right), \operatorname{Fin}\left(b\right)\right), \mathbb{C}\right),\; \forall n \in \mathbb{N},\; \operatorname{moment}\left(psi, H, n\right) = \operatorname{iteratedDeriv}\left(n, \operatorname{returnAmplitude}\left(psi, H\right), 0\right)$$

*Formalization.* `D5/S3/Quantum/Dynamics/SubsystemLanczosPositivityRefutation.moment` (`✓ std3`).

*Citation.* Pawel Caputa, Giuseppe Di Giulio, Tran Quang Loc (2026). *Complexity Inequalities for Quantum Subsystems*. DOI: [10.48550/arXiv.2606.20790](https://doi.org/10.48550/arXiv.2606.20790). URL: <https://arxiv.org/abs/2606.20790v2>.

*Commentary.*

Section 3.1, printed p. 15, defines μ_n^(A) = ∂_t^n R_A(t)|_(t=0). The operation iteratedDeriv is Mathlib's n-fold real derivative, evaluated at 0. Equation (3.5) of the v2 PDF, labeled b1_generalprocedure in the TeX, gives (b₁^(A))² = (μ₁^(A))² − μ₂^(A).

**Definition 1.5 (The first clause of the conjecture).**

$$claim \Leftrightarrow (\forall a \in \mathbb{N},\; \forall b \in \mathbb{N},\; \forall psi \in \operatorname{EuclideanSpace}\left(\mathbb{C}, \operatorname{Prod}\left(\operatorname{Fin}\left(a\right), \operatorname{Fin}\left(b\right)\right)\right),\; \forall H \in \operatorname{Matrix}\left(\operatorname{Prod}\left(\operatorname{Fin}\left(a\right), \operatorname{Fin}\left(b\right)\right), \operatorname{Prod}\left(\operatorname{Fin}\left(a\right), \operatorname{Fin}\left(b\right)\right), \mathbb{C}\right),\; (\operatorname{norm}\left(psi\right) = 1) \Rightarrow ((\operatorname{IsHermitian}\left(H\right)) \Rightarrow (0 < (\operatorname{moment}\left(psi, H, 1\right))^{2} - \operatorname{moment}\left(psi, H, 2\right))))$$

*Formalization.* `D5/S3/Quantum/Dynamics/SubsystemLanczosPositivityRefutation.claim` (`✓ std3`).

*Citation.* Pawel Caputa, Giuseppe Di Giulio, Tran Quang Loc (2026). *Complexity Inequalities for Quantum Subsystems*. DOI: [10.48550/arXiv.2606.20790](https://doi.org/10.48550/arXiv.2606.20790). URL: <https://arxiv.org/abs/2606.20790v2>.

*Commentary.*

Section 3.1, printed p. 15 (PDF page 16), states: "At present, however, we are unable to establish the sign of (bₙ⁽ᴬ⁾)² in full generality. Based on all the examples discussed in this manuscript, we conjecture that (bₙ⁽ᴬ⁾)²>0 for every n, and hence that all the coefficients bₙ⁽ᴬ⁾ are real." The predicate claim is its n = 1 clause over every finite pair of subsystem dimensions, every normalized pure initial state, and every Hermitian time-independent Hamiltonian. The norm is the Euclidean norm of ψ. A counterexample to this clause refutes the universal sign conjecture.

**Theorem 1.6 (Refutation by an entangled two-qubit state).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/SubsystemLanczosPositivityRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/caputa-di-giulio-loc-subsystem-lanczos-positivity` (refuted) by `D5/S3/Quantum/Dynamics/SubsystemLanczosPositivityRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"caputa-di-giulio-loc-subsystem-lanczos-positivity","declaration_gid":"D5/S3/Quantum/Dynamics/SubsystemLanczosPositivityRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Pawel Caputa, Giuseppe Di Giulio, Tran Quang Loc (2026). *Complexity Inequalities for Quantum Subsystems*. DOI: [10.48550/arXiv.2606.20790](https://doi.org/10.48550/arXiv.2606.20790). URL: <https://arxiv.org/abs/2606.20790v2>.

*Commentary.*

Section 3.1, printed p. 15, conjectures: "At present, however, we are unable to establish the sign of (bₙ⁽ᴬ⁾)² in full generality. Based on all the examples discussed in this manuscript, we conjecture that (bₙ⁽ᴬ⁾)²>0 for every n, and hence that all the coefficients bₙ⁽ᴬ⁾ are real." Take ψ = (3/5)|00⟩ + (4/5)|11⟩ and H = X_A ⊗ |0⟩⟨0|_B. The state has norm one and H is Hermitian. Differentiating the matrix exponential, conjugation, partial trace and fixed-normalization overlap yields initial purity 337/625, first overlap derivative 0, and second overlap derivative 126/625. Thus moment(ψ,H,1) = 0 and moment(ψ,H,2) = 126/337. The witness has (μ_1)^2 − μ_2 = −126/337, so the first squared coefficient contradicts strict positivity. No higher Lanczos coefficient is needed for the refutation.

## References

- Truth anchor: `D5/S3/Quantum/Dynamics/SubsystemLanczosPositivityRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Dynamics/SubsystemLanczosPositivityRefutation.moment`
- Truth anchor: `D5/S3/Quantum/Dynamics/SubsystemLanczosPositivityRefutation.result`
- Truth anchor: `D5/S3/Quantum/Dynamics/SubsystemLanczosPositivityRefutation.returnAmplitude`
- Truth anchor: `D5/S3/Quantum/Dynamics/SubsystemLanczosPositivityRefutation.rho`
- Truth anchor: `D5/S3/Quantum/Dynamics/SubsystemLanczosPositivityRefutation.rhoA`
- Dependency: [D5/S3/Quantum/Dynamics/ProjectionProbabilityFlow](ProjectionProbabilityFlow.md)
- Dependency: [D5/S3/Quantum/Information/PartialTraceMutualInformation](../Information/PartialTraceMutualInformation.md)
- Dependency: [D5/S3/Quantum/PureState/PureStateHandshake](../PureState/PureStateHandshake.md)
