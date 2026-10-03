---
bibkey: xu2015oblique
authors: Jianwei Xu
year: 2015
title: "Oblique discord"
doi: 10.1142/S0217979216502568
url: https://arxiv.org/abs/1506.00404v1
claim: "The Conjecture of Eq. (22) asserts I(rho^AB) >= I(Phi_A rho^AB) for every normalized oblique operation of Eq. (13) and every bipartite density state."
strata_touched:
  - D5/S3/Quantum/Information/ObliqueDiscordMutualInformationRefutation
license: citation-only
triage: anchor
---

# Oblique discord

Jianwei Xu, *Oblique discord*, arXiv:1506.00404v1; Int. J. Mod. Phys. B
31, 1650256 (2017). The arXiv text defines a state-dependent normalized
operation using a normalized basis and its biorthogonal dual.

The definition on p. 2 preceding Eq. (13) reads:

> Suppose $\{|i\rangle \}_{i=1}^{n_{A}}$ is a normalized basis of $H^{A}$
> which not necessarily orthogonal to each other. There exists an unique basis
> $\{|\widetilde{i}\rangle \}_{i=1}^{n}$ of $H^{A}$ such that $\langle i|\widetilde{j}\rangle =\delta _{ij}$,
> note that $\{|\widetilde{i}\rangle \}_{i=1}^{n}$ not necessarily orthogonal and not necessarily normalized.
> $\{|\widetilde{i}\rangle \}_{i=1}^{n_{A}}$ is called the dual basis of
> $\{|i\rangle \}_{i=1}^{n_{A}}$. We define the quantum operation
> $\Phi _{A}=\{|i\rangle \langle \widetilde{i}|\}_{i=1}^{n_{A}}$ which operates the
> bipartite state $\rho ^{AB}$ as

$$
\Phi _{A}\rho ^{AB}=\frac{\sum_{i=1}^{n_{A}}|i\rangle \langle \widetilde{i}|\rho ^{AB}|\widetilde{i}\rangle \langle i|}{tr[\sum_{i=1}^{n_{A}}\langle \widetilde{i}|\rho ^{AB}|\widetilde{i}\rangle ]}.
$$

The Conjecture on p. 3, Eq. (22), reads:

> **Conjecture:** $I(\rho ^{AB})\geq I(\Phi _{A}\rho ^{AB})$ for any $\Phi _{A}$ and any $\rho ^{AB}$,
> where $I(\rho ^{AB})$ is the mutual information, $\Phi _{A}$ is defined in Eq.(13).

The sentence following Eq. (21) on p. 3 reads:

> where $I(\rho )=S(\rho ^{A})+S(\rho ^{B})-S(\rho )$ is the mutual information.

The paper defines
$D_O^A(\rho)=\inf_{\Phi_A}[I(\rho)-I(\Phi_A\rho)]$. The Lean encoding
uses finite complex Hilbert spaces, actual bases and their normalization
and duality equations, and the frozen density-state subtype. Tensoring each
Kraus operator with the identity makes its action on the untouched factor
explicit. The denominator is defined literally as tr_B(∑_i ⟨w_i|ρ|w_i⟩),
using the existing partialTraceRight on the one-dimensional factor times B.
The unit norm of each basis vector proves its equality with the trace of
the unnormalized output inside phi; result checks the equality at the witness. Entropy uses natural logarithms; changing to any logarithm base
greater than one multiplies mutual information by a positive constant.

## Verified locator

- URL: https://arxiv.org/abs/1506.00404v1, Eq. (13) and the Conjecture of Eq. (22).
- DOI: https://doi.org/10.1142/S0217979216502568. The journal full text is
  unverified; the formal claim concerns the arXiv v1 text.
