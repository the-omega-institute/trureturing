---
bibkey: gourwallach2010fourqubits
authors: Gilad Gour; Nolan R. Wallach
year: 2010
title: "All Maximally Entangled Four Qubits States"
doi: 10.1063/1.3511477
url: https://arxiv.org/abs/1006.0036v2
claim: "Four-qubit marginal entropy: one-uniform normal form, purity bounds, entropy scope and labelled-party equality qualifications."
strata_touched:
  - D5/S3/Quantum/Entanglement/HiguchiSudbery/HiguchiSudberyEntropyMaximum
license: citation-only
triage: anchor
---

## Verified locator

DOI: https://doi.org/10.1063/1.3511477

Source: https://arxiv.org/abs/1006.0036v2

# All Maximally Entangled Four Qubits States

## Purity and entropy boundaries

The discussion before Theorem 5:

> Hence, since $\tau_1$ is bounded by $1$, it follows that $\tau_2\leq 4/3<3/2$. That is, there are no 4-qubit states for which all the 3 reduced density matrices, obtained by tracing out two qubits, are proportional to the identity.

With the paper's tangle normalization, $\tau_2\leq4/3$ is the bound $\sum_{c}\operatorname{Tr}\rho_c^2\geq1$ over the three inequivalent two-versus-two cuts.

Theorem 5, p. 5, states that every normalized four-qubit state has $\tau_1=1$ if and only if it is locally unitarily equivalent to a vector in the Bell-product subspace $\mathcal A$. Since the one-qubit tangles are individually at most one, $\tau_1=1$ means all four one-qubit marginals equal $I_2/2$. This is the normal-form input used in the structural continuation; all of its hypotheses are retained.

Theorem 6 gives $\tau_2=(4\tau_1-\tau_4)/3$. In Bloch-vector notation this is $2(P-1)=\sum_X|r_X|^2+\tau_4$, where $P$ is the sum of the three two-body purities.

Theorem 10(a), p. 8, has the hypothesis $\psi\in\mathcal A$:

$$E_2^{(\alpha)}(\psi)\leq E_2^{(\alpha)}(|M\rangle)\quad\text{for }0<\alpha<2.$$

> with equality if and only if up to local unitaries $\psi=|M\rangle$.

The opening paragraph of Section IV.B specifies that Theorem 10 concerns **Tsallis entropy**, with von Neumann entropy recovered in the order-one limit. Its notation must not be read as the analogous average Rényi inequality throughout $1<\alpha<2$. The displayed uniqueness sentence also requires the labelled-party qualification below.

Theorem 12, p. 9:

> Let $\psi\in\mathcal H_4$ and $\alpha\geq2$. Then,

$$E_2^{(\alpha)}(\psi)\leq5/3,$$

> with equality if and only if, up to local unitaries, $\psi$ is one of the cluster states given in Eqs.(3,4,5).

Theorem 12 concerns average Rényi entropy. Theorem 10's restricted-family conclusion does not provide the unrestricted von Neumann bound, and the cluster-state result for $\alpha\geq2$ does not settle the optimizer for $1<\alpha<2$.

## Labelled-party equality qualification

The [HS4 rigidity continuation](../../docs/develop/theory/HIGUCHI_SUDBERY_RIGIDITY.md), Section 3, keeps the four parties labelled and excludes party swaps from local unitaries. For the literal flattening determinants $d_{AB}$ and $d_{AC}$, the quantity

$$\chi(\psi)=\operatorname{Im}\bigl(d_{AB}(\psi)\overline{d_{AC}(\psi)}\bigr)$$

is invariant under product $U(2)^4$ transformations and global phase. Direct evaluation on the original Higuchi-Sudbery state and its conjugate gives $\pm\sqrt3/864$. Their identical marginal spectra therefore cannot imply that they occupy one labelled-party LU orbit. A swap of C and D exchanges them. The original Higuchi-Sudbery paper already discusses both conjugate candidates.

Accordingly, the continuation uses Theorem 5 for existence of the normal form and proves the two-orbit classification separately by phase alignment and explicit local Pauli actions. It does not use Theorem 10's one-orbit sentence as a uniqueness premise. These qualifications and the continuation are ordinary mathematical arguments, not new Lean-verified declarations. The explicit invariant computation and local operations are supported by the companion exact checker linked from the HS4 dossier.
