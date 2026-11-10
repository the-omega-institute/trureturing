---
slug: kanachova-liu-tu-2026-pure-state-detection
bibkey: kanachova2026qubitqutrit
doi: 10.48550/arXiv.2609.11151
url: https://arxiv.org/abs/2609.11151v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Tomography/KanachovaLiuTuPureStateDetection.result
---

# Kanachova–Liu–Tu pure-state detection conjecture

## Problem

Veronica Kanachova, Feng Liu and Zhoudunming Tu, Qubit–Qutrit Quantum Tomography of hadronic Λφ and ΛK*0 systems, arXiv:2609.11151v1, state in Appendix §.7 immediately after Proposition 1: “We therefore conjecture, without proof, that ρ_meas detects every pure entangled state of this system.” The source reconstruction is $\rho_{\rm meas}=\tfrac12[\rho+\mathcal U_B(\rho^{T_B})]$ with $\mathcal U_B(\rho)=(1_2\otimes U)\rho(1_2\otimes U)^\dagger$ and $U=\begin{pmatrix}0&0&-1\\0&1&0\\-1&0&0\end{pmatrix}$ in the ordered basis $(+1,0,-1)$. The Lean claim quantifies over every normalized complex qubit–qutrit vector with no product factorization and asks for a negative real eigenpair of this fixed reconstruction.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Every complex pure qubit–qutrit amplitude | D5.S3.Quantum.Tomography.KanachovaLiuTuPureStateDetection.claim quantifies over Fin 2 × Fin 3 → ℂ | The full six-coordinate complex domain is retained. |
| Normalization | star ψ ⬝ᵥ ψ = 1 | The source unit-norm condition is literal. |
| Entanglement means no two-by-three product factorization | The negated existential factorization in claim | No Schmidt basis or nonzero-factor restriction is added. |
| Fixed local matrix in the ordered qutrit basis | U | The entries and basis order match Eq. (S18). |
| Measured reconstruction | measured | Eq. (3) is represented using the existing second-factor partialTranspose and rankOneDensity owners. |
| Detection | The existential negative real eigenpair in claim | The conclusion requires eigenvalue < 0, w ≠ 0, and the exact matrix eigen-equation. |
| Conjecture settlement | result : claim | The full source proposition is proved. |

## Motivation

The settling declaration is D5/S3/Quantum/Tomography/KanachovaLiuTuPureStateDetection.result, with admission_basis: open-problem-resolution (#22252; Proved). This external named problem has no digestion atom. The source is recorded in Library/QuadraticForms/kanachova2026qubitqutrit.md. The public owner D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPureBound.pt_rank_hermitian is also part of the delivery's dependency surface.

## Gap

Appendix §.7 supplied numerical evidence and the restricted-basis Proposition 1 but left arbitrary Schmidt bases as a conjecture. The settling proof constructs a fixed witness from the two rows of the amplitude vector, proves its expectation is strictly negative for every non-product input, proves the reconstruction Hermitian, and invokes the finite-dimensional Hermitian eigenbasis. The escape audit for result and the newly publicized owner pt_rank_hermitian is unfinished under #22682; no registration is claimed declared_validated before the required CI current-job reading.

## Route

For $\psi=(u,v)^T$, the private witness eta is $(U\overline v,-U\overline u)^T$. The private expectation_identity reduces its quadratic form to the negative sum of the three squared two-by-two minors. delta_pos proves that this sum is positive under the negated product factorization, using product_of_minors_zero for the zero-minor converse. measured_hermitian combines the rank-one Hermitian fact, the imported partial-transpose owner and the published Hermitian owner for the conjugated term. negative_eigenpair applies the existing Hermitian positive-semidefinite eigenvalue criterion and eigenvector basis. The public result composes these statements into the exact claim.

## Falsifier

A falsifier would be a normalized non-product complex six-coordinate vector for which the fixed measured matrix has no negative real eigenpair, or a failure of one of the compiled identities on the result's proof path. Finite numerical agreement alone would not refute or prove the universal statement. Mixed-state detection, arbitrary symmetric-unitary extensions and quantitative noise bounds are outside this result.

## Evidence

The scoped Lean build proves D5.S3.Quantum.Tomography.KanachovaLiuTuPureStateDetection.result : claim and the owner re-pin preserves its theorem statement. The axiom closure of every public declaration is contained in {propext, Classical.choice, Quot.sound}. The public surface is U, localConjugation, measured, claim and result; the auxiliary definitions and theorems remain private and are consumed by result. The result and owner audit targets remain unfinished under #22682.

### Exact experiment

The experiment is at commit 2e5c42249159964a68ca7ccf7bdf8d625d1afcad, script docs/reports/pure-state-detection/check.py. The command python3 docs/reports/pure-state-detection/check.py exits 0; script SHA-256 is e594cec061c9a50e7f9eb615ecd80e2bbb04ae0d8f60e8da90bd18f636674261; the final line is ALL_CHECKS_OK. The exact scope is symbolic orthogonality, witness normalization, Hermiticity, the Gram/minor identity and the Proposition 1 checks, together with all 5^6=15,625 Gaussian-integer six-tuples over {0,1,-1,i,-i}: one zero tuple, 744 product tuples and 14,880 entangled tuples. These computations corroborate the formal result and do not replace it.

## Triage

### What the settlement shows

| Item | Status and evidence kind | Evidence and boundary |
| --- | --- | --- |
| All normalized non-product complex 2×3 inputs have a negative real eigenpair for the exact fixed source reconstruction. | Proved; kernel-checked | D5.S3.Quantum.Tomography.KanachovaLiuTuPureStateDetection.result proves the complete claim. |
| The witness expectation is minus the sum of the three squared 2×2 minors; entanglement makes that sum strictly positive. | Proved; kernel-checked | expectation_identity and delta_pos are consumed on the live proof path of result; their private statements are included in the compiled result proof. |
| Exact SymPy verifies orthogonality, norm preservation, the Gram/minor identity and Hermiticity for twelve real coordinates; the independent finite checker covers 15,625 Gaussian-integer inputs. | Computed | The pinned experiment command, exit code and script SHA-256 in Evidence cover twelve symbolic real coordinates and the exact 15,625-input scope. |
| Extension to 2×d with an arbitrary symmetric unitary U is not formalized or claimed settled. | Open | No declaration or experiment in this delivery covers arbitrary d or arbitrary symmetric unitary U. |
| Mixed-state detection, optimal negative-eigenvalue bounds and robustness to noise are not settled by this proof. | Open | The result concerns normalized pure vectors and existence of a negative eigenpair only; these neighbouring questions have no delivered declaration. |
| Literature completeness. | ASSUMED-UNVERIFIED | The bounded source and citation screen recorded in preregistration #22252 found no inspected settlement; OpenAlex and Semantic Scholar rate limits, MathOverflow challenges, unindexed journal versions and other listed coverage gaps remain unresolved. |

The decisive mechanism is the explicit witness $(U\overline v,-U\overline u)^T$. Its expectation is the negative sum of the squared minors, so non-productness supplies strict negativity without a Schmidt-basis restriction. Hermiticity then converts the negative quadratic form into a negative real eigenpair. The source's restricted Proposition 1 remains a special case; the mixed-state blind-window discussion is unchanged.

## ASSUMED-UNVERIFIED

Literature completeness is ASSUMED-UNVERIFIED; the source's only arXiv version is v1 and the bounded screen in #22252 does not establish exhaustive absence or priority. The experiment is finite corroboration. The escape audit for result and pt_rank_hermitian remains unfinished under #22682, and no declared_validated registration is asserted without the required CI current reading.

