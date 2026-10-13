---
slug: higuchi-sudbery-2000-four-qubit-average-entropy-maximum
bibkey: higuchisudbery2000entangledcouples
doi: 10.1016/S0375-9601(00)00480-1
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

Brierley–Higuchi establishes local maximality. Gour–Wallach establishes maximality in the 1-uniform family and related linear-entropy results. Their Theorem 10 concerns Tsallis entropy, including its von Neumann limit; it does not establish the analogous average Rényi statement throughout $1<\alpha<2$. Pauwels–Gühne, arXiv:2608.21185, records unrestricted global maximality of the average von Neumann entropy as conjectural. The theorem here ranges over every normalized four-qubit amplitude vector.

## Route

The cubic Hermite majorant for $-x\log x$ has double contact at $1/6$ and $1/2$. Its gap is nonnegative by `HermiteMajorant.double_contact_nonnegative`; `HermiteEntropy.hermite_majorant` handles the nonnegative half-line, including zero. Newton identities and the common-state purity bound reduce the entropy estimate to the coupled degree-six inequality $E_3\le5/36$. Cauchy–Binet identifies spectral $e_3$ with sums of squared three-by-three flattening minors. The exact mixed sum-of-squares identity is kernel-checked through the private reflection certificate and its soundness chain; positivity supplies the minor bound. The three marginal spectra of $M_4$ are $\{1/2,1/6,1/6,1/6\}$ and give exact attainment.

## Falsifier

An exact normalized four-qubit state with average entropy strictly above $1+\frac12\log_2 3$ would refute the universal clause. A numerical excess is insufficient. Failure of the auxiliary $E_3$ estimate alone would invalidate this route without refuting the original entropy statement.

## Evidence

The nine Lean modules in `D5/S3/Quantum/Entanglement/HiguchiSudbery/` carry the checked development. The settling theorem is `HiguchiSudberyEntropyMaximum.result : claim`; `claim` conjoins the universal upper bound and equality at `M4`. The corresponding Scribe theorem node binds this dossier with `OpenProblemResolutionClaim` of kind `Proved`. The literature locators and quoted clauses are in the four `Library/QuantumStates/` notes for Higuchi–Sudbery, Brierley–Higuchi, Gour–Wallach and Pauwels–Gühne. The preregistration is issue #13454; its tier-3 research admission basis is `escape-witness`.

## Triage

### What the settlement shows

- **Proved in Lean:** HS4 holds for every normalized four-qubit pure state and equality is attained at $M_4$, by `HiguchiSudberyEntropyMaximum.result`.
- **Proved in Lean:** $E_3\le5/36$ for the three marginals of one normalized state. The homogeneous degree-six inequality, its exact mixed sum-of-squares certificate and its positivity are used on the live proof path through `PrimeHierarchyCertificate.prime_certificate_identity`, `ReflectionEvaluation.ref_eval_rhs_nonneg`, `HS4Assembly.spectrum_e3_eq_minors` and the settling module’s `e3_bound_of_certificate`. These are private proof components rather than additional standalone public conclusions.
- **Paper proof; Lean formalization open:** the structural continuation below classifies the maximizers into two local-unitary orbits for labelled parties, represented by $M_4$ and its complex conjugate. Allowing party permutations joins these two orbits. This uses the existing moment bounds and the published one-uniform normal-form theorem; it is not a new kernel-checked classification.
- **Open:** the unrestricted average Rényi-$\alpha$ optimizer problem for $1<\alpha<2$. The HS and cluster candidates already cross inside this interval, as proved in the continuation. Their comparison does not give the complete optimizer diagram.
- **Open:** corresponding maximization questions for five or more qubits. The literal cuts, dimensions and certificate here are four-qubit data.

The decisive mechanism keeps the three marginal spectra coupled through the same amplitude vector, while the scalar majorant removes the logarithm. The majorant is proved on the nonnegative half-line; the entropy conclusion uses normalized four-qubit states. The exact $M_4$ spectrum proves sharpness of the stated bound. The original kernel theorem establishes the maximum and attainment, without a uniqueness assertion.

## Structural continuation

[Higuchi-Sudbery rigidity, marginal fibers and minimal interaction locality](../docs/develop/theory/HIGUCHI_SUDBERY_RIGIDITY.md) derives an exact entropy-deficit identity and quantitative spectral and one-body bounds. Equality forces the target spectra and one-uniformity. Gour–Wallach Theorem 5 then supplies a Bell-product normal form, and explicit phase alignment gives the two labelled-party LU orbits. A determinant invariant with opposite values on the conjugates proves their separation without relying on Theorem 10's one-orbit uniqueness wording.

The same continuation determines the full mixed-state fiber of the six HS two-body marginals: exactly the line segment between the two orthogonal conjugate projectors. A three-body scalar-chirality observable resolves the fiber. This yields a two-local unique-ground-state obstruction, an explicit three-local parent Hamiltonian with gap exactly 2 in its displayed normalization, and an energy-to-fidelity certificate for arbitrary mixed states.

These are ordinary mathematical derivations, not newly formalized declarations. Their supporting [experimental program, reference output and scope notes](https://github.com/the-omega-institute/trureturing-experiments/tree/13ab9d0905217da7cc61a72211e3dfbc202cc014/docs/reports/hs4-rigidity) check finite exact identities and bounded numerical examples. They do not replay the existing global certificate or prove the universal normal-form theorem in Lean.

## ASSUMED-UNVERIFIED

Literature coverage is bounded by the cited sources and the preregistration’s searches. Independent standalone upstream-only route certification for the unchanged private certificate helpers is not asserted. Information-escape registration is paused under CLAUDE.md §3.9. The structural continuation has not undergone independent mathematical review or Lean verification; historical originality of its individual consequences is not asserted.
