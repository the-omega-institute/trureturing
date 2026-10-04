---
bibkey: kumari2017sufficient
authors: Meenu Kumari, Shohini Ghose, Robert B. Mann
year: 2017
title: "Sufficient condition for nonexistence of symmetric extension of qudits using Bell inequalities"
doi: 10.1103/PhysRevA.96.012128
url: https://arxiv.org/abs/1704.06516v2
claim: "For a two-qutrit state, the CGLMP expression I_3 = P(A_1=B_1) + P(B_1=A_2+1) + P(A_2=B_2) + P(B_2=A_1) - P(A_1=B_1-1) - P(B_1=A_2) - P(A_2=B_2-1) - P(B_2=A_1-1) is evaluated with A_k = U_FT U(phi_k) and B_l = U_FT^* U(phi'_l), U(phi) = diag(exp(-i phi(j))), followed by a computational-basis measurement, and B_CGLMP(rho) is its maximum over the twelve angles (Eqs. (CGLMP1), (CGLMP2)). Based on numerical studies the paper conjectures (Eq. (35)) that the CGLMP inequality is monogamous: for every three-qutrit state at most one of rho_AB, rho_BC, rho_AC has B_CGLMP > 2."
strata_touched:
  - D5/S3/Quantum/Entanglement/CglmpMonogamyRefutation
license: citation-only
triage: anchor
---

# Sufficient condition for nonexistence of symmetric extension of qudits using Bell inequalities

Meenu Kumari, Shohini Ghose and Robert B. Mann, Phys. Rev. A 96, 012128
(2017); arXiv:1704.06516v2. Quotations are from the arXiv v2 source.

The CGLMP expression (Eq. (CGLMP1)):

> $\mathcal{I}_3(\rho) = P(A_1=B_1) +P(B_1=A_2+1)+P(A_2=B_2) +P(B_2=A_1)-P(A_1=B_1-1)-P(B_1=A_2) -P(A_2=B_2-1)-P(B_2=A_1-1)$

The measurement family:

> Let $U(\vec{\phi_k})$ and $U(\vec{\varphi_l})$ be $3\times 3$ unitary operators whose diagonal elements are $\exp{(-\mathrm{i}\phi_k(j))}$ and $\exp{(-\mathrm{i}\varphi_l(j))}$, and off-diagonal elements are zero. Let $U_{\text{FT}}$ and $U^{*}_{\text{FT}}$ be the respective 3-dimensional discrete Fourier transform and inverse.

with $A_k=U_{\text{FT}}U(\vec\phi_k)$ and $B_l=U^*_{\text{FT}}U(\vec\varphi_l)$
"followed by a measurement in the $\{|0 \rangle, |1 \rangle, |2 \rangle \}$
basis", the probabilities
$P(A_m=j,B_n=k)=\mathrm{tr}(\Pi_j\otimes\Pi_k A_m\otimes B_n\rho A_m^{\dagger}\otimes B_n^{\dagger})$,
and $\mathcal B_{CGLMP}(\rho)=\max_{\vec\phi_k,\vec\varphi_l}\mathcal I_3$
(Eq. (CGLMP2)).

The conjecture (Eq. (35)):

> Based on our numerical studies, we make the following conjecture. The CGLMP inequality for 2-qutrit states is monogamous, that is, if $\rho_{ABC}$ is any 3-qutrit state such that $\rho_{AB}$, $\rho_{BC}$ and $\rho_{AC}$ are its three 2-qutrit RDMs, at most one of these violates the CGLMP inequality.

followed by the display
$\mathcal{B}_{\text{CGLMP}}(\rho_{AB}) > 2 \Rightarrow \mathcal{B}_{\text{CGLMP}}(\rho_{BC}) \leq 2$
and $\mathcal{B}_{\text{CGLMP}}(\rho_{AC}) \leq 2$, "with the same result
holding for any permutation of $(A,B,C)$". With Theorem 3 (a monogamous
two-qudit Bell inequality certifies that a violating state has no symmetric
extension) the paper concludes that a CGLMP violation would exclude a
three-qutrit symmetric extension.

The encoding takes outcomes in `Fin 3` with modular addition;
$U_{\text{FT}}$ has entries $\omega^{jk}/\sqrt3$ with the existing `omega`
$=e^{2\pi i/3}$, and $U^*_{\text{FT}}$ is its conjugate transpose;
$\mathcal B_{CGLMP}$ is the supremum over all angle vectors; the reduced
states are the existing partial traces, with the first-named party of each
pair measured by $A_k$.

## Verified locator

- DOI: https://doi.org/10.1103/PhysRevA.96.012128 (Phys. Rev. A 96, 012128
  (2017)).
- URL: https://arxiv.org/abs/1704.06516v2 (v2, 2017-08-07, the latest
  version; source
  `Symmetric_extension_and_Bell_inequality_paper_revision_for_arxiv.tex`, md5
  `1fd49d0919d1b80fc742512d732f3b53`): Eq. (CGLMP1) (l. 128–132), the
  measurement family and Eq. (Probabilities) (l. 133–146), Eq. (CGLMP2)
  (l. 148–152), Theorem 3 (l. 338) and the conjecture (l. 400–406).
