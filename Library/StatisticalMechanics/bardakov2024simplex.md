---
bibkey: bardakov2024simplex
authors: V. G. Bardakov; B. B. Chuzhinov; I. A. Emelyanenkov; M. E. Ivanov; T. A. Kozlovskaya; V. E. Leshkov
year: 2024
title: "Set-Theoretical Solutions of the n-Simplex Equation"
doi: 10.1134/S1055134424010012
url: https://arxiv.org/abs/2206.08906v1
claim: "The n-simplex equation R_1 R_2 ... R_(n+1) = R_(n+1) ... R_2 R_1 for a map R of X^n acts on X^N, N = n(n+1)/2, with the multi-indices given by the rows of the matrix MI_n; a solution is simple when it has the form (x_1, ..., x_n) -> (x_s(1), ..., x_s(n)). Question 2 (Question 4.22 of the journal version) asks for which n > 2 there are non-identity permutations without fixed points that give solutions of the n-simplex equation. Section 9.2 defines the first tetrahedral 4-groupoid (T1-groupoid) and the reduced T1-groupoid and states that it is not clear whether some T1-groupoid yields, after forgetting the operations ◁ and ▷, a system that is not a reduced T1-groupoid."
strata_touched:
  - D5/S3/StatisticalMechanics/VertexModels/SimplexFixedPointFreePermutations
  - D5/S3/StatisticalMechanics/VertexModels/TetrahedralGroupoidReductRefutation
license: citation-only
triage: anchor
---

# Set-Theoretical Solutions of the n-Simplex Equation

V. Bardakov, B. Chuzinov, I. Emel'yanenkov, M. Ivanov, T. Kozlovskaya and
V. Leshkov (arXiv spelling), arXiv:2206.08906v1 [nlin.SI, cross-listed to math-ph and math.GR]
(2022); Мат. труды 27(1) (2024) 5–72; Siberian Adv. Math. 34(1) (2024) 1–40.
Quotations are from the arXiv source.

The equation (Section 3.1):

> In general case, the left side and the right side of the {\SE} are words of length $n+1$. … $R_{\overline{1}}R_{\overline{2}} \cdots R_{\overline{n+1}} = R_{\overline{n+1}} \cdots R_{\overline{2}} R_{\overline{1}}$, where $\overline{k} = (k_1, k_2, \ldots, k_{n+1}) \in \mathbb{N}^{n+1}$ is a multi-index.

> The multi-indices in the {\SE} can be regarded as rows of the multi-indices matrix $MI_n$ that is a $(n+1) \times n$ matrix satisfying the recurrence relation

For $n = 3$ the equation is
$R_{123} R_{145} R_{246} R_{356} = R_{356} R_{246} R_{145} R_{123}$.
Simple solutions (Section 4.2 in both versions):

> A solution $T : X^n \to X^n$ of the {\SE} is said to be simple if $T(x_1, \dots , x_n) = (x_{s(1)}, \dots , x_{s(n)})$, where $s: \{1, \dots , n\} \to \{1, \dots , n\}$ is a map (not necessary injective).

The question:

> 1) Is there a indecomposable simple solution of the {\SE} for some $n$ different from five solutions $\{ \id_X, P, Pr^2_1, Pr^2_2, Pr^3_2 \} $? 2) We know that the permutation $P_{12}$ is a solution of the YBE. For which $n > 2$ there are non-identity permutations without fixed points that gives solutions of the \SE? Of course, using Proposition \ref{invsymm} it is not difficult to find some transpositions which are solutions of \SE.

The journal version (Мат. труды 27(1), p. 29) states the same question as
Вопрос 4.22: "Для каких $n > 2$ есть перестановки без неподвижных точек,
являющиеся решениями n-SE?"

Elementary 1-solutions of the tetrahedron equation (Section 9.2 of the arXiv source; Section 9.2,
pp. 51–53 of Мат. труды 27(1) (2024), with the same axioms):

> For studying elementary 1-solutions of the TE let us introduce an algebraic system $(X, \os, \oc, \oL, \oR)$ with four binary operations which satisfy axioms: $x \oc y = (x \oL z) \oc (y \oL z)$; $(x \oc y) \os (z \oc w) = (x \os z) \oc (y \os w)$; $(x \oR y) \oR z = (x \oR z) \oR (y \os z)$; $(x \os y) \oL z = x \oR (y \oc z)$. We call it first tetrahedral 4-groupoid and denote it by $T_1$-groupoid.

> There are 2-groupoids, that give elementary 1-solutions. Consider for example a system $(X, \os, \oc)$ with the following axioms: $x \oc y = (x \oc z) \oc (y \oc z)$; $(x \os y) \os z = (x \os z) \os (y \os z)$; $(x \oc y) \os (z \oc w) = (x \os z) \oc (y \os w)$. We will call it a reduced first tetrahedral 4-groupoid or simply reduced $T_1$-groupoid.

> It is generally true that if in $T_1$-groupoid $x \os y = x \oR y$ then forgetting about operations $x \oL y$ and $x \oR y$ yields a reduced $T_1$-groupoid. It is not clear if there is a $T_1$-groupoid such that forgetting about $x \oL y$ and $x \oR y$ will not yield a reduced $T_1$-groupoid.

The journal version (p. 53) keeps both sentences: «В общем случае верно, что если в $T_1$-группоиде
$x \overline{*} y = x \overline{\triangleright} y$, то при отбрасывании операций $x \overline{\triangleleft} y$ и
$x \overline{\triangleright} y$ получается редуцированный $T_1$-группоид. Не ясно существуют ли такие
$T_1$-группоиды, что отбрасывание $x \overline{\triangleleft} y$ и $x \overline{\triangleright} y$ не даст
редуцированный $T_1$-группоид.»

## Verified locator

- DOI: https://doi.org/10.1134/S1055134424010012 (the English journal
  version; the Crossref record gives the six authors, volume 34, issue 1,
  pages 1–40; the question was read in the Russian original, Мат. труды
  27(1) (2024), p. 29, Вопрос 4.22).
- URL: https://arxiv.org/abs/2206.08906v1 (source
  `ArXiv--Tetrahedral_equation.tex` retrieved 2026-10-01): the construction
  of the equation and the matrix $MI_n$ (Section 3.1), the definition of
  simple solutions and the question (Section 4.2), and the $T_1$-groupoids with the question about
  their reducts (Section 9.2, lines 2135–2255); the Russian original was read for Section 9.2
  (pp. 51–53).
