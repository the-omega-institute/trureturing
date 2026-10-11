---
slug: higuchi-sudbery-2000-four-qubit-average-entropy-maximum
bibkey: higuchisudbery2000entangledcouples
doi: 10.1016/S0375-9601(00)00506-4
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Entanglement/HiguchiSudbery/HiguchiSudberyEntropyMaximum.result
---

## Problem

For every normalized pure state $\psi\in(\mathbb C^2)^{\otimes4}$, the average two-qubit marginal von Neumann entropy in bits satisfies

$$\frac{S(\rho_{AB})+S(\rho_{AC})+S(\rho_{AD})}{3}\le 1+\frac12\log_2 3.$$

Equality is attained at the explicit Higuchi–Sudbery state

$$|M_4\rangle=\frac1{\sqrt6}\bigl[|0011\rangle+|1100\rangle+\omega(|1010\rangle+|0101\rangle)+\omega^2(|1001\rangle+|0110\rangle)\bigr],\qquad\omega=e^{2\pi i/3}.$$

Higuchi–Sudbery, Section 3: “Given that a four-qubit state cannot have maximal entropy of entanglement for every two-qubit subset, we now ask what is the greatest possible average for such entropies, i.e. we seek to maximise”. Their average over the six pairs equals the displayed average over the three complementary cuts.

## Motivation

The declaration `D5/S3/Quantum/Entanglement/HiguchiSudbery/HiguchiSudberyEntropyMaximum.result` proves the universal bound and exact attainment. The amplitudes have domain `Fin 16 → Complex`, with basis index $8a+4b+2c+d$; the three literal flattenings retain $AB$, $AC$ and $AD$. Repository partial trace, density states and von Neumann entropy are used directly, with division by $\log 2$ converting natural logarithms to bits.

## Gap

Brierley–Higuchi establishes local maximality. Gour–Wallach establishes global maximality in the 1-uniform family and related linear-entropy results. Pauwels–Gühne, arXiv:2608.21185, records unrestricted global maximality of the average von Neumann entropy as conjectural. The theorem here ranges over every normalized four-qubit amplitude vector.

## Route

The cubic Hermite majorant for $-x\log x$ has double contact at $1/6$ and $1/2$. Its gap is nonnegative by `HermiteMajorant.double_contact_nonnegative`; `HermiteEntropy.hermite_majorant` handles the nonnegative half-line, including zero. Newton identities and the common-state purity bound reduce the entropy estimate to the coupled degree-six inequality $E_3\le5/36$. Cauchy–Binet identifies spectral $e_3$ with sums of squared three-by-three flattening minors. The exact mixed sum-of-squares identity is kernel-checked through the private reflection certificate and its soundness chain; positivity supplies the minor bound. The three marginal spectra of $M_4$ are $\{1/2,1/6,1/6,1/6\}$ and give exact attainment.

## Falsifier

An exact normalized four-qubit state with average entropy strictly above $1+\frac12\log_2 3$ would refute the universal clause. A numerical excess is insufficient. Failure of the auxiliary $E_3$ estimate alone would invalidate this route without refuting the original entropy statement.

## Evidence

The nine Lean modules in `D5/S3/Quantum/Entanglement/HiguchiSudbery/` carry the checked development. The settling theorem is `HiguchiSudberyEntropyMaximum.result : claim`; `claim` conjoins the universal upper bound and equality at `M4`. The corresponding Scribe theorem node binds this dossier with `OpenProblemResolutionClaim` of kind `Proved`. The literature locators and quoted clauses are in the four `Library/QuantumStates/` notes for Higuchi–Sudbery, Brierley–Higuchi, Gour–Wallach and Pauwels–Gühne. The preregistration is issue #13454; its tier-3 research admission basis is `escape-witness`.

## Triage

### What the settlement shows

- **Proved:** HS4 holds for every normalized four-qubit pure state and equality is attained at $M_4$, by `HiguchiSudberyEntropyMaximum.result`.
- **Proved:** $E_3\le5/36$ for the three marginals of one normalized state. The homogeneous degree-six inequality, its exact mixed sum-of-squares certificate and its positivity are used on the live proof path through `PrimeHierarchyCertificate.prime_certificate_identity`, `ReflectionEvaluation.ref_eval_rhs_nonneg`, `HS4Assembly.spectrum_e3_eq_minors` and the settling module’s `e3_bound_of_certificate`. These are private proof components rather than additional standalone public conclusions.
- **Open:** uniqueness or classification of all maximizers up to local unitaries. Attainment does not establish uniqueness.
- **Open:** the unrestricted average Rényi-$\alpha$ entropy question for $1<\alpha<2$. This theorem concerns von Neumann entropy; Gour–Wallach’s results for $\alpha\ge2$ are separate.
- **Open:** corresponding maximization questions for five or more qubits. The literal cuts, dimensions and certificate here are four-qubit data.

The decisive mechanism keeps the three marginal spectra coupled through the same amplitude vector, while the scalar majorant removes the logarithm. The majorant is proved on the nonnegative half-line; the entropy conclusion uses normalized four-qubit states. The exact $M_4$ spectrum proves sharpness of the stated bound. The local and 1-uniform maximality statements remain compatible with this global bound; no additional source theorem or uniqueness assertion is claimed.

## ASSUMED-UNVERIFIED

Literature coverage is bounded by the cited sources and the preregistration’s searches. Independent standalone upstream-only route certification for the unchanged private certificate helpers is not asserted. Information-escape registration is paused under CLAUDE.md §3.9.
