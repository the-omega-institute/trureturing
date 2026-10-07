# In-between states do not always minimize Bayesian transmissivity error

## Abstract

A vacuum–two-photon superposition has strictly smaller Bayesian transmissivity error than every phased in-between state at mean photon number one half, for an equiprobable two-point prior.

**Definition 1.1 (Mean photon number).**

$$\forall N : \mathbb{N}, \forall psi : \operatorname{Fin}\left(N + 1\right) \to \mathbb{C}, \operatorname{meanPhoton}\left(N, psi\right) = \sum_{n : \operatorname{Fin}\left(N + 1\right)} ((\operatorname{toReal}\left(\operatorname{val}\left(n\right)\right)) \cdot (\operatorname{normSq}\left(psi\left(n\right)\right)))$$

*Formalization.* `D5/S3/Estimation/TransmissivityTwoPointProbeRefutation.meanPhoton` (`✓ std3`).

*Citation.* B. Zhou; B. A. Bash; S. Guha; C. N. Gagatsos (2023). *Bayesian minimum mean square error for transmissivity sensing*. DOI: [10.1103/PhysRevResearch.5.043033](https://doi.org/10.1103/PhysRevResearch.5.043033). URL: <https://arxiv.org/abs/2304.05539v1>.

*Commentary.*

Equations (30)–(32), p. 4: psi gives complex Fock coefficients on Fin(N+1). val is the natural-number value of a finite index, toReal casts it to the reals, and normSq is the squared complex modulus. Hilbert normalization is norm(toLp(2,psi))=1, meaning the Euclidean L2 norm rather than the sup norm of a function space.

**Definition 1.2 (Pure-loss output).**

$$\forall N : \mathbb{N}, \forall tau : \mathbb{R}, \forall psi : \operatorname{Fin}\left(N + 1\right) \to \mathbb{C}, \operatorname{outputState}\left(N, tau, psi\right) = \sum_{l : \operatorname{Fin}\left(N + 1\right)} (((\operatorname{amplitudeKraus}\left(N, l, 1 - tau\right)) \cdot (\operatorname{rankOneDensity}\left(psi\right))) \cdot (\operatorname{adjoint}\left(\operatorname{amplitudeKraus}\left(N, l, 1 - tau\right)\right)))$$

*Formalization.* `D5/S3/Estimation/TransmissivityTwoPointProbeRefutation.outputState` (`✓ std3`).

*Citation.* B. Zhou; B. A. Bash; S. Guha; C. N. Gagatsos (2023). *Bayesian minimum mean square error for transmissivity sensing*. DOI: [10.1103/PhysRevResearch.5.043033](https://doi.org/10.1103/PhysRevResearch.5.043033). URL: <https://arxiv.org/abs/2304.05539v1>.

*Commentary.*

The pure-loss channel sends |n> to sqrt(choose(n,l) tau^(n-l) (1-tau)^l)|n-l> in Kraus branch l. The reused amplitudeKraus(l,f) has entries ofReal(sqrt(choose(n,l)) sqrt(1-f)^(n-l) sqrt(f)^l) at row n-l and column n. Here f=1-tau, so on 0<=tau<=1 its coefficient is exactly the source coefficient. Natural subtraction is truncated subtraction. rankOneDensity(psi)=vecMulVec(psi,star(psi)) is the input outer product; adjoint is conjugate transpose. The finite sum contains all nonzero Kraus branches for a finite Fock support. The formula defines the channel output. For natural n and l and admissible tau, the source coefficient equals the factored coefficient of the frozen owner as displayed below.

$\forall n : \mathbb{N}, \forall l : \mathbb{N}, \forall tau : \mathbb{R}, (\operatorname{mem}\left(tau, \operatorname{Icc}\left(0, 1\right)\right)) \Rightarrow (\sqrt{((\operatorname{toReal}\left(\operatorname{choose}\left(n, l\right)\right)) \cdot ((tau)^{\operatorname{NatSub}\left(n, l\right)})) \cdot ((1 - tau)^{l})} = ((\sqrt{\operatorname{toReal}\left(\operatorname{choose}\left(n, l\right)\right)}) \cdot ((\sqrt{tau})^{\operatorname{NatSub}\left(n, l\right)})) \cdot ((\sqrt{1 - tau})^{l}))$

**Definition 1.3 (Two-point moment operators).**

$$\forall N : \mathbb{N}, \forall q : \mathbb{R}, \forall tau0 : \mathbb{R}, \forall tau1 : \mathbb{R}, \forall psi : \operatorname{Fin}\left(N + 1\right) \to \mathbb{C}, \forall k : \mathbb{N}, \operatorname{momentState}\left(N, q, tau0, tau1, psi, k\right) = \operatorname{smul}\left(\operatorname{ofReal}\left((q) \cdot ((tau0)^{k})\right), \operatorname{outputState}\left(N, tau0, psi\right)\right) + \operatorname{smul}\left(\operatorname{ofReal}\left((1 - q) \cdot ((tau1)^{k})\right), \operatorname{outputState}\left(N, tau1, psi\right)\right)$$

*Formalization.* `D5/S3/Estimation/TransmissivityTwoPointProbeRefutation.momentState` (`✓ std3`).

*Citation.* B. Zhou; B. A. Bash; S. Guha; C. N. Gagatsos (2023). *Bayesian minimum mean square error for transmissivity sensing*. DOI: [10.1103/PhysRevResearch.5.043033](https://doi.org/10.1103/PhysRevResearch.5.043033). URL: <https://arxiv.org/abs/2304.05539v1>.

*Commentary.*

Equations (13) and (15), p. 3: P(tau)=q delta(tau-tau0)+(1-q) delta(tau-tau1), where 0<=q<=1. momentState(k) is Gamma_k with the real prior weights cast to complex scalars. smul denotes scalar multiplication of a matrix.

**Definition 1.4 (Finite positive operator valued measurements).**

$$\forall N : \mathbb{N}, \forall m : \mathbb{N}, \forall E : \operatorname{Fin}\left(m\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(N + 1\right), \operatorname{Fin}\left(N + 1\right), \mathbb{C}\right), \operatorname{finitePOVM}\left(N, m, E\right) \Leftrightarrow ((\forall k : \operatorname{Fin}\left(m\right), \operatorname{PosSemidef}\left(E\left(k\right)\right)) \land (\sum_{k : \operatorname{Fin}\left(m\right)} (E\left(k\right)) = 1))$$

*Formalization.* `D5/S3/Estimation/TransmissivityTwoPointProbeRefutation.finitePOVM` (`✓ std3`).

*Citation.* B. Zhou; B. A. Bash; S. Guha; C. N. Gagatsos (2023). *Bayesian minimum mean square error for transmissivity sensing*. DOI: [10.1103/PhysRevResearch.5.043033](https://doi.org/10.1103/PhysRevResearch.5.043033). URL: <https://arxiv.org/abs/2304.05539v1>.

*Commentary.*

The effects are positive semidefinite matrices on the output Fock span, and their sum is the identity matrix. The outcome count m may be any natural number, and the estimates in the risk below are real numbers.

**Definition 1.5 (Bayesian squared-error risk).**

$$\forall N : \mathbb{N}, \forall m : \mathbb{N}, \forall q : \mathbb{R}, \forall tau0 : \mathbb{R}, \forall tau1 : \mathbb{R}, \forall psi : \operatorname{Fin}\left(N + 1\right) \to \mathbb{C}, \forall E : \operatorname{Fin}\left(m\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(N + 1\right), \operatorname{Fin}\left(N + 1\right), \mathbb{C}\right), \forall x : \operatorname{Fin}\left(m\right) \to \mathbb{R}, \operatorname{bayesianRisk}\left(N, m, q, tau0, tau1, psi, E, x\right) = \sum_{k : \operatorname{Fin}\left(m\right)} (\operatorname{Re}\left(\operatorname{trace}\left((E\left(k\right)) \cdot (\operatorname{smul}\left(\operatorname{ofReal}\left((x\left(k\right))^{2}\right), \operatorname{momentState}\left(N, q, tau0, tau1, psi, 0\right)\right) - \operatorname{smul}\left(\operatorname{ofReal}\left((2) \cdot (x\left(k\right))\right), \operatorname{momentState}\left(N, q, tau0, tau1, psi, 1\right)\right) + \operatorname{momentState}\left(N, q, tau0, tau1, psi, 2\right))\right)\right))$$

*Formalization.* `D5/S3/Estimation/TransmissivityTwoPointProbeRefutation.bayesianRisk` (`✓ std3`).

*Citation.* B. Zhou; B. A. Bash; S. Guha; C. N. Gagatsos (2023). *Bayesian minimum mean square error for transmissivity sensing*. DOI: [10.1103/PhysRevResearch.5.043033](https://doi.org/10.1103/PhysRevResearch.5.043033). URL: <https://arxiv.org/abs/2304.05539v1>.

*Commentary.*

Equations (10)–(13), pp. 2–3: the finite measurement risk is sum_k Re tr(E_k (x_k^2 Gamma_0-2 x_k Gamma_1+Gamma_2)). Re extracts the real part of the complex trace. The real estimate coefficients are cast by ofReal before matrix scalar multiplication.

**Definition 1.6 (Minimum mean square error).**

$$\forall N : \mathbb{N}, \forall q : \mathbb{R}, \forall tau0 : \mathbb{R}, \forall tau1 : \mathbb{R}, \forall psi : \operatorname{Fin}\left(N + 1\right) \to \mathbb{C}, \operatorname{MMSE}\left(N, q, tau0, tau1, psi\right) = \operatorname{sInf}\left(\{r : \mathbb{R} \mid \exists m : \mathbb{N}, \exists E : \operatorname{Fin}\left(m\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(N + 1\right), \operatorname{Fin}\left(N + 1\right), \mathbb{C}\right), \exists x : \operatorname{Fin}\left(m\right) \to \mathbb{R}, (\operatorname{finitePOVM}\left(N, m, E\right)) \land (r = \operatorname{bayesianRisk}\left(N, m, q, tau0, tau1, psi, E, x\right))\}\right)$$

*Formalization.* `D5/S3/Estimation/TransmissivityTwoPointProbeRefutation.MMSE` (`✓ std3`).

*Citation.* B. Zhou; B. A. Bash; S. Guha; C. N. Gagatsos (2023). *Bayesian minimum mean square error for transmissivity sensing*. DOI: [10.1103/PhysRevResearch.5.043033](https://doi.org/10.1103/PhysRevResearch.5.043033). URL: <https://arxiv.org/abs/2304.05539v1>.

*Commentary.*

MMSE is the real infimum of the risks of all finite POVMs and all real estimates on the finite output span. Identifying this finite-outcome quantity with the source's MMSE over arbitrary measurements requires the following compression argument: an output supported on a finite span has identical statistics for a full-space effect E and its compression P E P; compressing a POVM preserves completeness on the span. A finite POVM on the span extends by assigning the orthogonal complement to one outcome. ASSUMED-UNVERIFIED: this compression argument and the equality with the arbitrary-outcome source MMSE are not kernel-checked in this module. The Lean lower bound and spectral attainment concern finite POVMs only. The finite-dimensional definition is extended to raw parameters and unnormalised vectors, but the claim uses only admissible parameters and normalised inputs.

**Definition 1.7 (Phased in-between Fock states).**

$$\forall nbar : \mathbb{R}, \forall phi : \mathbb{R}, \forall n : \operatorname{Fin}\left(\operatorname{ceilNat}\left(nbar\right) + 1\right), \operatorname{inBetween}\left(nbar, phi\right)\left(n\right) = (\operatorname{exp}\left((\operatorname{ComplexI}\left(\right)) \cdot (\operatorname{ofReal}\left((phi) \cdot (\operatorname{toReal}\left(\operatorname{val}\left(n\right)\right))\right))\right)) \cdot (\operatorname{ite}\left(\operatorname{val}\left(n\right) = \operatorname{NatSub}\left(\operatorname{ceilNat}\left(nbar\right), 1\right), \operatorname{ofReal}\left(\operatorname{sqrt}\left(1 - (\operatorname{sqrt}\left(1 - \operatorname{toReal}\left(\operatorname{ceilNat}\left(nbar\right)\right) + nbar\right))^{2}\right)\right), \operatorname{ite}\left(\operatorname{val}\left(n\right) = \operatorname{ceilNat}\left(nbar\right), \operatorname{ofReal}\left(\operatorname{sqrt}\left(1 - \operatorname{toReal}\left(\operatorname{ceilNat}\left(nbar\right)\right) + nbar\right)\right), 0\right)\right))$$

*Formalization.* `D5/S3/Estimation/TransmissivityTwoPointProbeRefutation.inBetween` (`✓ std3`).

*Citation.* B. Zhou; B. A. Bash; S. Guha; C. N. Gagatsos (2023). *Bayesian minimum mean square error for transmissivity sensing*. DOI: [10.1103/PhysRevResearch.5.043033](https://doi.org/10.1103/PhysRevResearch.5.043033). URL: <https://arxiv.org/abs/2304.05539v1>.

*Commentary.*

Section V, p. 4: "For this case, we provide numerical evidence that the optimal state has the form," followed by (27) |Phi_nbar>=|a(nbar)| |ceil(nbar)-1>+|c(nbar)| |ceil(nbar)>, (28) |c(nbar)|=sqrt(1-ceil(nbar)+nbar), and (29) |a(nbar)|=sqrt(1-|c(nbar)|^2). The source says: "We refer to the state of Eq. (27) as in-between state as it is a superposition of the two nearest Fock states for a given n̄ and it reverts to a Fock state when n̄ is an integer." Equation (33) applies exp(i phi n-hat). ceilNat is the natural ceiling; for the positive nbar in the claim it is the source ceiling. NatSub is natural truncated subtraction, and ComplexI is the imaginary unit. The conditional order and extension outside positive nbar match the Lean definition.

**Definition 1.8 (Non-integer-energy optimality conjecture).**

$$claim \Leftrightarrow (\forall q : \mathbb{R}, \forall tau0 : \mathbb{R}, \forall tau1 : \mathbb{R}, \forall nbar : \mathbb{R}, (\operatorname{mem}\left(q, \operatorname{Icc}\left(0, 1\right)\right)) \Rightarrow ((\operatorname{mem}\left(tau0, \operatorname{Icc}\left(0, 1\right)\right)) \Rightarrow ((\operatorname{mem}\left(tau1, \operatorname{Icc}\left(0, 1\right)\right)) \Rightarrow ((0 < nbar) \Rightarrow (\forall N : \mathbb{N}, \forall psi : \operatorname{Fin}\left(N + 1\right) \to \mathbb{C}, (\operatorname{norm}\left(\operatorname{toLp}\left(2, psi\right)\right) = 1) \Rightarrow ((\operatorname{meanPhoton}\left(N, psi\right) = nbar) \Rightarrow (\exists phi : \mathbb{R}, \operatorname{MMSE}\left(\operatorname{ceilNat}\left(nbar\right), q, tau0, tau1, \operatorname{inBetween}\left(nbar, phi\right)\right) \le \operatorname{MMSE}\left(N, q, tau0, tau1, psi\right))))))))$$

*Formalization.* `D5/S3/Estimation/TransmissivityTwoPointProbeRefutation.claim` (`✓ std3`).

*Citation.* B. Zhou; B. A. Bash; S. Guha; C. N. Gagatsos (2023). *Bayesian minimum mean square error for transmissivity sensing*. DOI: [10.1103/PhysRevResearch.5.043033](https://doi.org/10.1103/PhysRevResearch.5.043033). URL: <https://arxiv.org/abs/2304.05539v1>.

*Commentary.*

Section V, arXiv v1 PDF p. 4: "For the two-point prior PDF (15), we verify that for integer n̄ the optimal state is the Fock state with the same photon number. For real n̄, our numerical results support the conjecture that the optimal state has the form of the state (27), up to a phase, i.e., |Φ′ₙ̄⟩ = e^{iφn̂}|Φₙ̄⟩." The prior parameters range over [0,1]; nbar is positive; N is any finite Fock cutoff. The psi input has Euclidean norm one and meanPhoton(psi)=nbar. The encoding says that some phased in-between state has finite-POVM MMSE no greater than each competing input. Each state's MMSE is computed on its own finite output span. Identification with the source's arbitrary-measurement optimum requires the compression argument stated above and a reduction from arbitrary outcomes to finite outcomes; that bridge is ASSUMED-UNVERIFIED and not kernel-checked here.

**Theorem 1.9 (Strict error advantage of a nonadjacent Fock superposition).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/TransmissivityTwoPointProbeRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/zhou-bash-guha-gagatsos-2023-transmissivity-in-between-probe-refutation` (refuted) by `D5/S3/Estimation/TransmissivityTwoPointProbeRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"zhou-bash-guha-gagatsos-2023-transmissivity-in-between-probe-refutation","declaration_gid":"D5/S3/Estimation/TransmissivityTwoPointProbeRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* B. Zhou; B. A. Bash; S. Guha; C. N. Gagatsos (2023). *Bayesian minimum mean square error for transmissivity sensing*. DOI: [10.1103/PhysRevResearch.5.043033](https://doi.org/10.1103/PhysRevResearch.5.043033). URL: <https://arxiv.org/abs/2304.05539v1>.

*Commentary.*

Take q=1/2, tau0=4/9, tau1=1 and nbar=1/2. Every in-between phase has MMSE 1625/23976, whereas psi=(sqrt(3)/2)|0>+(1/2)|2> has MMSE 110575/1674432, with positive gap 107725/61953984. Its Hilbert norm is one and its mean photon number is one half. For any finite POVM, the operator variance M2-M1^2 is a sum of positive semidefinite sandwiches. If Gamma0 B+B Gamma0=2 Gamma1, completing the square gives risk>=Re tr(Gamma2-B Gamma1). The phased two-dimensional certificate is [[787,145 exp(-i phi)],[145 exp(i phi),937]]/1332. The competitor certificate is [[62971,0,4293 sqrt(3)],[0,41344,0],[4293 sqrt(3),0,68965]]/93024. Both solve the Sylvester equation for the channel outputs. Spectral projections of each Hermitian certificate, with its eigenvalues as estimates, attain its lower bound. The rational comparison refutes the conjecture. It does not assert that the competitor is globally optimal, or settle the beta-prior conjecture.

## References

- Truth anchor: `D5/S3/Estimation/TransmissivityTwoPointProbeRefutation.MMSE`
- Truth anchor: `D5/S3/Estimation/TransmissivityTwoPointProbeRefutation.bayesianRisk`
- Truth anchor: `D5/S3/Estimation/TransmissivityTwoPointProbeRefutation.claim`
- Truth anchor: `D5/S3/Estimation/TransmissivityTwoPointProbeRefutation.finitePOVM`
- Truth anchor: `D5/S3/Estimation/TransmissivityTwoPointProbeRefutation.inBetween`
- Truth anchor: `D5/S3/Estimation/TransmissivityTwoPointProbeRefutation.meanPhoton`
- Truth anchor: `D5/S3/Estimation/TransmissivityTwoPointProbeRefutation.momentState`
- Truth anchor: `D5/S3/Estimation/TransmissivityTwoPointProbeRefutation.outputState`
- Truth anchor: `D5/S3/Estimation/TransmissivityTwoPointProbeRefutation.result`
- Dependency: [D5/S3/Quantum/QuantumChannels/TruncatedLossDephasingOptimizerRefutation](../Quantum/QuantumChannels/TruncatedLossDephasingOptimizerRefutation.md)
