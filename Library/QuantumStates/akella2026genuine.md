---
bibkey: akella2026genuine
authors: S. Akella, N. Iizuka, A. Miyata
year: 2026
title: "Genuine Multi-Entropy in the Toric Code"
doi: 10.48550/arXiv.2607.06050
url: https://arxiv.org/abs/2607.06050v1
claim: "For stabilizer states and q ≥ 4 the q-partite genuine multi-entropy at replica index n < q collapses to multi-entropies of at most q − 2 parties; at q = 4 the n = 3 case reads GM^{(4)}_{n=3} = −(a − 1/9) I_3, and whether a counting argument exists for n = 3 is stated as open."
strata_touched:
  - D5/S3/Quantum/Entanglement/StabilizerMultiEntropyCollapse
license: citation-only
triage: anchor
---

# Akella, Iizuka and Miyata, genuine multi-entropy in the toric code

S. Akella, N. Iizuka and A. Miyata, *Genuine Multi-Entropy in the Toric Code*,
arXiv:2607.06050v1 (7 July 2026; hep-th, cross-listed cond-mat.str-el and quant-ph).

## Verified locator

DOI: 10.48550/arXiv.2607.06050.
Primary version: https://arxiv.org/abs/2607.06050v1 (the only arXiv version).
The TeX source of v1 supplies §1 (Eq. (1), the tripartite information; Eqs. (2) and (3), the $n=2$ and $n=3$ collapses), §2 (the definition of $\mathrm{GM}^{(4)}_n$),
§6 (the open question) and Appendix A (the replica definition of the multi-entropy).

## Source statements

Rényi tripartite information (§1): "$I_{3,n} = S^{(2)}_n(BCD:A) +S^{(2)}_n(CDA:B) +S^{(2)}_n(DAB:C)
+S^{(2)}_n(ABC:D) -S^{(2)}_n(AB:CD) -S^{(2)}_n(AC:BD) -S^{(2)}_n(AD:BC)$".

Genuine four-partite multi-entropy (§2): "$\GM[4]_n(A:B:C:D) = S^{(4)}_n(A:B:C:D) -\frac{1}{3}\Big[
S^{(3)}_n(AB:C:D) +S^{(3)}_n(AC:B:D) +S^{(3)}_n(AD:B:C) +S^{(3)}_n(BC:A:D) +S^{(3)}_n(BD:A:C)
+S^{(3)}_n(CD:A:B)\Big] +\frac{1}{3}\Big[ S^{(2)}_n(ABC:D) +S^{(2)}_n(ABD:C) +S^{(2)}_n(ACD:B)
+S^{(2)}_n(BCD:A)\Big] -a\, I_{3,n}$", with "$a$ is a real parameter".

Eq. (3): "$\GM[\mathtt{q}=4]_{n=3}(A:B:C:D) = -\left(a-\tfrac{1}{9}\right) I_3$", where "$I_3$
denotes the common value of the R\'enyi tripartite information $I_{3,n}$ for stabilizer states,
which is independent of $n$", and "Unlike the $n=2$ relation, this reduction is not a consequence
of the Coxeter structure of the corresponding multi-entropy."

Appendix A: "$S_n^{(\mathtt{q})}(A_1:\cdots:A_{\mathtt{q}}) = \frac{1}{1-n}\frac{1}{n^{\mathtt{q}-2}}
\log\left[ \frac{Z_n^{(\mathtt{q})}}{\left(Z_1^{(\mathtt{q})}\right)^{n^{\mathtt{q}-1}}}\right]$",
"$Z_n^{(\mathtt{q})} = \bra{\psi}^{\otimes n^{\mathtt{q}-1}} \Sigma_1(g_1)\Sigma_2(g_2)\cdots
\Sigma_{\mathtt{q}}(g_{\mathtt{q}}) \ket{\psi}^{\otimes n^{\mathtt{q}-1}}$", with the replicas labeled by
the points of $(\mathbb Z/n)^{\mathtt q-1}$, $g_i$ shifting coordinate $i$ and $g_{\mathtt q}$ the identity.

§6: "Whether there is a similar counting argument for $n = 3$ case is an open question."

## Scope

The paper establishes Eq. (3) by explicit computation for toric-code stabilizer states and states
the general $\mathtt q=4$, $n=3$ collapse for stabilizer states; the follow-up arXiv:2608.29627 reports
it as established numerically for general qubit stabilizer states. The $n=2$ counting argument is
in arXiv:2601.16258.
