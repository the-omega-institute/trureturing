---
bibkey: klobus2016communication
authors: Waldemar Kłobus; Michał Oszmaniec; Remigiusz Augusiak; Andrzej Grudka
year: 2016
title: "Communication strength of correlations violating monogamy relations"
doi: 10.1007/s10701-015-9983-5
url: https://arxiv.org/abs/1408.1223v2
claim: "For boxes p(a,b,e|A_i,B_j) with M settings for A and B, one setting E for the third party, all one- and three-party expectation values zero and a common value of <B_0E>_{A_i}, the chained Bell expression I^M_AB = sum_k (<A_kB_k> + <A_(k+1)B_k>) with A_M = -A_0 obeys the monogamy relation |I^M_AB| + 2|<B_0E>| <= 2M for nonsignaling boxes. Section 5 introduces the coordinates x_A^i, y_A^i, x_B^i, y_B^i, derives the necessary inequalities (ElPrat) for boxes with R_M = I^M_AB + 2<B_0E> = 2M + Delta, Delta in [0,2], and conjectures that every correlator vector satisfying (ElPrat) is realized by some signaling box with R_M = 2M + Delta."
strata_touched:
  - D5/S3/QuantumBounds/ChainedMonogamySignalingRealizability
license: citation-only
triage: anchor
---

# Communication strength of correlations violating monogamy relations

Waldemar Kłobus, Michał Oszmaniec, Remigiusz Augusiak, Andrzej Grudka,
Found. Phys. 46 (2016) 620–634, arXiv:1408.1223v2 (quant-ph). Quotations
are from the arXiv v2 source, with its macros kept as printed.

Correlators of a box (Section 1):

> by $\langle XY\rangle_Z$ we denote the standard bipartite expectation value of the product of observables $X$ and $Y$, which in general might be conditioned on the third party's measurement choice $Z$. An example of such conditional expectation value is $\langle A_iE\rangle_{B_j}=\sum_{a,b,e=\pm1} a\cdot	e\cdot p(a,b,e|A_i,B_j).$

The class of boxes (Section 3):

> in what follows we restrict our attention to a subclass of boxes whose all one-partite expectation values $\langle X\rangle_{YZ}$ with $X,Y,Z=A_i,B_j,E$ are zero. … Below we then restrict our attention to boxes having only bipartite correlators non-vanishing. They form a convex set denoted by $\mathcal{P}$.

The preceding sentence states that the symmetrized box has "all one- and
three-partite expectation values vanish".

The chained Bell expression and its monogamy relation (Section 5):

> $I^{M}_{AB}:=\sum_{k=0}^{M-1}(\langle A_kB_k\rangle+\langle A_{k+1}B_{k}\rangle)\leq 2M-2,$ where we use the convention that $A_{M}=-A_0$.

> $|I_{AB}^{M}|+ 2 |\<B_0 E  \>|\leq 2M,$

> Let us now assume as before that all correlators appearing in the monogamy relation (\ref{chainedEve}) do not depend on the the third party's measurements, in particular, $\langle B_0E\rangle_{A_i}=\langle B_0E\rangle_{A_j}$ for any $i\neq j$. Let then $\mathcal{P}_{\Delta}^M$ be the convex set of boxes for which $R_M(\vec{p})=2M+\Delta$ with $\Delta\in[0,2]$.

As for $M=2$ (Section 3, $R(\vec{p})\equiv I_{AB}+2\langle B_0E\rangle$),
$R_M=I^M_{AB}+2\langle B_0E\rangle$ is the left side of the monogamy
relation with the absolute values omitted.

The coordinates:

> $x_A^i=\langle B_iE\rangle_{A_i},\ y_A^i=\langle B_iE\rangle_{A_{i+1}},\ x_B^i=\langle A_iE\rangle_{B_{i-1}},\ y_B^i=\langle A_iE\rangle_{B_i},$ and finally $x_B^0=\langle A_0E \rangle_{B_0},\ \ \text{and}\ \ y_B^0=\langle A_0E\rangle_{B_{M-1}}.$

The inequalities and the conjecture:

> $\sum_{i=1}^{M-1}(-1)^{a_i}(x_A^i-y_B^i)+ \sum_{i=1}^{M-2}(-1)^{b_i}(x_B^{i+1}-y_A^i) +(-1)^c(y_A^{M-1} +y_B^0)+x_B^1+x_B^0\geq \Delta,$ with $a_i,b_i,c\in\{0,1\}$ for $i=1,\ldots,M-1$. Although we cannot prove it as in the case $M=2$, we conjecture that all possible values of the correlators in $S_{A\to BE}^i$ and $S_{B\to AE}^i$ that satisfy inequalities (\ref{ElPrat}) can always be realized with some signaling probability distribution $\vec{p}$ for which $R_M(\vec{p})=2M+\Delta$.

Here $S^i_{A\to BE}=\{x_A^i,y_A^i\}$ ($i=1,\dots,M-1$) and
$S^i_{B\to AE}=\{x_B^i,y_B^i\}$ ($i=0,\dots,M-1$). For $M=2$ the paper
prints four inequalities (Section 4, labels niert1–niert4) and states in
Appendix A that they characterize the realizable correlators.

The encoding indexes settings and coordinates by natural numbers, takes
outcomes in `Bool` with the sign $\pm1$, reads the setting $A_M=-A_0$ of
$y_A^{M-1}=\langle B_{M-1}E\rangle_{A_M}$ as the setting pair
$(A_0,B_{M-1})$ (the relabelling $a\mapsto-a$ does not change a correlator
of $B$ and $E$), and requires the realizing box to lie in $\mathcal P$.

## Verified locator

- DOI: https://doi.org/10.1007/s10701-015-9983-5 (Found. Phys. 46 (2016)
  620–634).
- URL: https://arxiv.org/abs/1408.1223v2 (v2, 2015-12-13, the latest
  version; source `monsyg_arxiv_rev.tex`, md5
  `5de9e3dfdbf983d1702258847136f444`): the correlators (l. 225–230), the
  class $\mathcal P$ (l. 425–443), $R$ for $M=2$ (l. 319), the printed
  $M=2$ list (l. 468–471), the chained Bell expression and its monogamy
  relation (l. 594–602), the set $\mathcal P^M_\Delta$ (l. 646–651), the
  coordinates (l. 665–669) and (ElPrat) with the conjecture (l. 712–723).
