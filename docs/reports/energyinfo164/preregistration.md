# Energy–information identity: preregistration

Production: Codex main worker using the lean4 skill, in the runner's implementation stage.
No independent review seats; numerical checks and local gates will be worker measurements.
Base: ea50faf34c (lane/math/energyinfo164). This is a user-selected formalization of a
known identity, not a claim to solve a new open problem.

## v1 — supplied proposal, before implementation

Source: quantum-reality atom
0b75ef93a42867b46dad6346602e61b3e0ddd972090c84dc472bf3e38758283b, equation 164.1.
Proposed admission_basis: escape-witness. Proposed witness: joint unitary entropy
preservation implies the sum of marginal entropy changes equals the change of mutual
information. This proposal is unverified and must be tested against the frozen API.

## v2 — API search correction, before Lean or numerical implementation

The public entropy_production_coherence_deletion_identity can be instantiated at U
and at 1. Both yield the same pinching relative entropy, so subtraction proves unitary
entropy invariance. Expanding quantumMutualInformation then proves step 3 by ring.
The Gibbs variational identity evaluated at the final and initial Gibbs states proves
step 2 by subtraction. These are bind-only under CLAUDE.md 3.2. No escape is claimed.

proof_shape: bind-only
admission_basis: atom-required-bridge
escape_witness: none
computational_content.kind: none (arbitrary finite dimensions and arbitrary states;
no finite enumeration, checker, numerical reduction or certified instance in Lean).

New typed edge: local Gibbs energy/relative-entropy changes and joint unitary
mutual-information changes are connected under exact Gibbs marginal equalities.
Named downstream consumer (registered before proof):
D5/S3/Quantum/Information/CorrelatedGibbsEnergyIdentity.energy_information_identity.
Its prerequisites will be gibbs_relative_entropy_energy_difference and
marginal_entropy_change_eq_mutual_information_change in that module.
The latter consumes von_neumann_entropy_unitary from that module; that lemma consumes
the existing public entropy-production theorem, without re-proving its private CFC lemmas.
All companion edges have the direction consumer -> prerequisite.

Exact hypotheses: finite nonempty A,B, Hermitian HA,HB; real betaA,betaB;
marginalRight rho = gibbsState (-betaA • HA), marginalLeft rho = gibbsState (-betaB • HB);
U in the unitary group of A × B, with final state unitaryConjugateState U hU rho.
No product-state, energy-conservation, positivity-of-beta or final-faithfulness assumption.
Entropy conservation and the energy identities must be conclusions, never hypotheses.

Independent numerical plan: fixed seed 1641; dimensions 2,3; 41 correlated initial
states gammaA tensor gammaB + epsilon X tensor Y with traceless Hermitian X,Y,
and 20 product controls, total 61. Verify positivity, normalization and exact marginals
to floating precision. Use random joint unitaries; compare the main residual against
1e-10 and require every correlated case to reject the sign-flipped Delta I formula
at 1e-8. These thresholds and case counts precede computation; numbers are diagnostic,
not kernel evidence. A sign-reversed residual may vanish for special evolutions;
no universal claim is made about that control.

Search receipt: read the four supplied D5 APIs and EntropyProductionCoherenceDeletionIdentity;
searched pinned Mathlib and D5 for entropy/unitary/Gibbs/energy identities. The exact
Gibbs identity is already public and will be applied. Coherent copying is a specific
isometry, so its entropy lemma does not directly cover arbitrary joint U. GitHub code
search q='"gibbs" "entropy" language:Lean' identified csd-lean4 FreeEnergy/SecondLaw;
read both at 13eda16971c66de4bc9f550e418dd4fdf59a5121. They use other entropy/Gibbs
carriers and do not provide this repository's exact two-marginal identity. No new port
or dependency is needed. Search scope is bounded, not an assertion of exhaustive absence.
Crossref and the Nature full article for 10.1038/s41467-019-10333-7 were fetched;
the article's Methods give the local relative entropy relation and Delta S_A+Delta S_B=Delta I.

Stop: complete target plus serial build/report/emit/deposit gates = 成 under this brief;
counterexample needs a kernel witness for 翻; otherwise deliver proved layers and a
precise blocked report. No sorry, private axiom, native_decide or definition-body theorem.
Gate order: serial-lean.sh -> make lean-report -> make emit -> make deposit-uncovered;
then the specified scribe-content-checks at the exact merge-base before any PR.
An implementation-stage result does not claim independent review or a merged PR.
