---
slug: zhang-2024-three-operator-clarkson-mccarthy
bibkey: zhang2024clarksonmccarthy
doi: null
url: https://arxiv.org/abs/2410.21961v4
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Matrix/ZhangThreeOperatorClarksonRefutation.result
---

# Zhang's three-operator Clarkson–McCarthy conjecture is false

## Problem

Teng Zhang, *Clarkson–McCarthy type inequalities, part I: $\ell_p$–$\ell_p$ and $\ell_q$–$\ell_p$ Schatten $p$-estimates* (2024 preprint, arXiv:2410.21961v4), Section 2, subsection “Euler's identity”, states Conjecture `conj:sharp-inequality`:

> Let $A,B,C\in S_p$. Then for $2\le p<\infty$,
>
> $\|A+B+C\|_p^p+\|A\|_p^p+\|B\|_p^p+\|C\|_p^p\le\frac{3^{p-1}+1}{2^p}\left(\|A+B\|_p^p+\|B+C\|_p^p+\|C+A\|_p^p\right).$
>
> For $0<p\le2$, the inequality is reversed. Moreover, the constant $\frac{3^{p-1}+1}{2^p}$ is optimal: equality holds for all $p>0$ by taking $A=B=C\neq0$.

This quotation is from lines 574–580 of the downloaded TeX member `v1_Clarkson_McCarthy_type_inequalities_part_I.tex`, MD5 `3ba34aa0913b51484593b3594a9f69d6`; only mathematical display layout and whitespace are normalized. The conjecture is introduced by “numerical evidence suggests the following sharp inequality” (line 571). Zhang restates it in *On five questions of Bourin and Lee* (2026), arXiv:2602.01463v2, TeX member `On_five_questions_of_Bourin_and_Lee.tex`, lines 411–419, MD5 `b3e91436b76494a53687b26bf5b2d06e`.

For a finite complex matrix and $p>0$, write $\|X\|_p^p=\sum_j s_j(X)^p$. Abbreviate the four-term expression on the left by $L_p(A,B,C)$, the sum of the three pairwise terms by $P_p(A,B,C)$, and the proposed coefficient by $c(p)=(3^{p-1}+1)/2^p$.

Issue [#22304](https://github.com/the-omega-institute/trureturing/issues/22304) fixes the reading settled by `claim`: for every real $p\ge2$, every natural dimension $n$, and every $A,B,C\in M_n(\mathbb C)$, $L_p(A,B,C)\le c(p)P_p(A,B,C)$. This universal statement is refuted. The reverse clause for $0<p\le2$ is outside `claim`.

The source and norm definition are documented in [the literature note](../Library/QuadraticForms/zhang2024clarksonmccarthy.md).

## Motivation

The conjecture proposes a sharp converse companion to the paper's Euler-type Clarkson–McCarthy estimate. It compares the Schatten powers of three operators and their total sum with those of their pairwise sums. Its validity would determine whether the equality case $A=B=C$ supplies a universal optimal coefficient, rather than just an attained ratio for one configuration. Euler's square-sum identity gives equality at $p=2$; controlling the redistribution of singular values at other exponents is the additional requirement.

## Gap

Issue #22304 records the bounded literature check before any Lean:

- Both identified TeX versions retain the conjecture; their relevant passages are reproduced by the source readings above.
- The preregistering author reports zero citing works in OpenAlex for each arXiv record, and no settlement in web searches for the three-operator inequality, its coefficient and Hlawka-type sums.
- The author distinguishes Zeng, Liu and Ratnavelu (2026), arXiv:2608.15558, as addressing a different conjecture of Tang and Zhang.
- The author reports no existing repository settlement; the issue also records candidate-search reports of no MathDB or formal-conjectures match.

The preregistered literature status is `not-found-in-searched-scope`. The external search results and the historical repository-absence reading are attributed reports, with the reproduction limits listed below.

## Route

Use the fixed complex matrices $A=\operatorname{diag}(1,0)$, $B=\operatorname{diag}(0,1)$ and $C=-\frac12\begin{pmatrix}1&1\\1&1\end{pmatrix}$. In Lean these are `coordinateProjectorTwo 0`, `coordinateProjectorTwo 1` and `-equalSuperpositionDensity`.

1. **Gram characteristic polynomials.** The private lemma `power_of_gram_charpoly` takes a complex $2\times2$ matrix $X$, a vector $d:\mathrm{Fin}\,2\to\mathbb R$ with $d_i\ge0$ for every $i$, equality of the characteristic polynomials of $X^*X$ and $\operatorname{diag}(d)$ viewed as a complex matrix, and a real exponent $p>0$. It concludes $\|X\|_p^p=\sum_i d_i^{p/2}$. The proof matches the Hermitian eigenvalues, reindexes by a permutation, and applies `schattenNorm_rpow_eq_sum_singularValues`, whose exponent hypothesis is also $p>0$.
2. **The two sides for this triple.** For every real $p>0$, `left_side` proves $L_p(A,B,C)=4$, using $d=(1,0)$ for each of $A$, $B$, $C$ and $A+B+C$. For the same fixed matrices and every real $p>0$, `right_side` proves $P_p(A,B,C)=2+2^{2-p/2}$, using $d=(1,1)$ for $A+B$ and $d=(1/2,1/2)$ for each of $B+C$ and $C+A$.
3. **The certified scalar bound.** The hypothesis-free lemma `certified_bound` proves $F(9/4)<4$, where $F(p)=c(p)(2+2^{2-p/2})$. It uses exact real-power comparisons $3^{1/4}<13161/10000$, $11892/10000<2^{1/4}$ and $2^{7/8}<18341/10000$. Raising nonnegative quantities to the fourth or eighth power certifies these bounds. Clearing the positive denominator reduces the conclusion to the rational comparison $(3\cdot13161/10000+1)(2+18341/10000)<16\cdot11892/10000$ and the strict lower bound on $2^{1/4}$.
4. **Refutation.** `result` applies a hypothetical `claim` at $p=9/4\ge2$, $n=2$, and precisely these three matrices. The two side lemmas apply because $9/4>0$. They turn that instance into $4\le F(9/4)$, contradicting `certified_bound`.

## Falsifier

The refutation would miss the source problem if the norm, quantifiers or matrices differed from its assertion. The module uses the trace-functional-calculus `schattenNorm`; for every finite complex matrix and real $p>0$, `schattenNorm_rpow_eq_sum_singularValues` identifies its $p$th power with the sum of singular-value powers. The unordered indexing of singular values does not change this sum. There is no dimension normalization.

The source permits arbitrary Schatten operators, so the real symmetric witness matrices are admissible complex matrices. Extending a finite matrix by zero on $\ell_2$ preserves its nonzero singular values and supplies an operator instance of the source statement; this interpretation bridge is not formalized in the module. The exponent $9/4$ belongs to the asserted upper-bound range. No positivity or commutativity assumption occurs in `claim` or the quoted conjecture.

## Evidence

The canonical source is `D5/S3/Quantum/Matrix/ZhangThreeOperatorClarksonRefutation.lean`.

- **Proof.** It proves `result : ¬ claim`.
- **Reuse.** It uses the Schatten norm and singular-value power identity from `Schatten/Holder`, the coordinate projectors from `Tomography/MutuallyUnbiasedDiagonalPlanes`, and the equal-superposition matrix from `QubitWitnesses`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.
- **Escape registrations.** `result` is the designated refutation result of the `utility` header and is exempt. The module has no other public theorem.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Matrix/ZhangThreeOperatorClarksonRefutation.lean.json`.

Declaration statements:

- `result`: `sha256:15ac3a163975eef411be70225c656339b2da90c6dd4af5af74067e43435bfff5`;
- `claim`: `sha256:9a2a9c811cf698342e7953509b8477ca58057c4cee76727d554c8a203dc33049`.

## Triage

Tier 1 conjecture of a 2024 preprint, retained in its v4 revision and restated in a 2026 preprint, preregistered in issue #22304 before any Lean.
`theorem`; resolution `refuted`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2. The refutation is a certified instance with basis `refutes`. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** it is false that $L_p(A,B,C)\le c(p)P_p(A,B,C)$ for every real $p\ge2$, every natural dimension $n$, and every $A,B,C\in M_n(\mathbb C)$.

**Computed, not formalized** (independent numerical evaluation of the fixed witness):

- At $p=9/4$, evaluation from the Gram eigenvalues gives $L_p=4$ and $c(p)P_p\approx3.98827149$.
- For the same witness, numerical evaluation at the tested exponents $p=2.01$ and $p=2.3$ also gives $c(p)P_p<4$, and at $p=2.5$ it gives $c(p)P_p>4$.
- At each of the 150 tested exponents $p=0.50,0.51,\ldots,1.99$, numerical evaluation gives $c(p)P_p>4=L_p$, so the reversed clause of the source fails for this witness at those tested points.

**Argued, not formalized.**

- *Mechanism and possible restrictions.* The witness concentrates each of the four individual or total-sum spectra at $(1,0)$, while each of two mixed sums spreads its squared singular values equally at $(1/2,1/2)$, as encoded by `left_side` and `right_side` for this fixed triple and every real $p>0$. Thus equality of the aggregate square-sums does not enforce the proposed comparison at higher powers. All three matrices are real and Hermitian, so either restriction alone cannot repair the conjecture. They do not all commute: $AC-CA=\frac12\begin{pmatrix}0&-1\\1&0\end{pmatrix}$. Also $C$ has eigenvalue $-1$. Requiring mutual commutativity or requiring all three matrices to be positive semidefinite excludes this witness; whether either restriction restores the proposed coefficient remains open here.
- *A neighbourhood of the transition.* For this fixed triple and every real $p>0$, the side lemmas give $L_p=4$ and $c(p)P_p=F(p)$. The positive function $F$ is differentiable near $2$, $F(2)=4$, and $(\log F)'(2)=(3\log3-5\log2)/4=\log(27/32)/4<0$. Hence $F'(2)<0$; the definition of derivative gives some $\varepsilon>0$, chosen below $2$, with $F(p)<4$ on $(2,2+\varepsilon)$ and $F(p)>4$ on $(2-\varepsilon,2)$. This supplies an analytic local refutation of each direction on its respective side of $2$, without determining the full failure range. Neither this neighbourhood conclusion nor a negation of the reverse clause is the type of `result`.
- *Surviving equality cases.* For arbitrary finite complex matrices at $p=2$, expanding the Hilbert–Schmidt squares on both sides gives $L_2=P_2$, and $c(2)=1$. For $A=B=C=X\ne0$ and every real $p>0$, homogeneity gives $L_p=(3^p+3)\|X\|_p^p$ and $P_p=3\cdot2^p\|X\|_p^p$, so this configuration still has ratio $c(p)$. An attained ratio alone cannot establish a universal bound. Any coefficient valid for all triples at $p=9/4$ must instead be at least $4/(2+2^{7/8})>c(9/4)$.
- *A weaker comparison.* Zhang (2024), arXiv:2410.21961v4, line 572, explicitly mentions “a weaker bound with coefficient $3^{\frac{p}{2}-1}$”. For $A,B,C\in S_p$ and $2\le p<\infty$, applying the paper's square-sum theorem `thm:schatten_p_norms` with the four operators $A+B+C,A,B,C$ on one side and the three pairwise sums on the other gives $L_p\le3^{p/2-1}P_p$: expansion identifies the two Gram sums, and the theorem's upper estimate uses three input operators. Its reversed estimate gives $L_p\ge3^{p/2-1}P_p$ for $0<p\le2$. These are applications of a source theorem, not additional Lean conclusions of this settlement.
- *Effect on the sources.* The conjecture and its proposed universal sharp coefficient are refuted, including the identical upper-bound conjecture in Zhang (2026), arXiv:2602.01463v2. The independent Euler-type and mixed-exponent estimates in the sources do not use this conjecture. The weaker-bound theorem `thm:conj-weaker-inequality` in arXiv:2602.01463v2 likewise has an independent proof; its following remark's numerical suggestion that the conjectured coefficient is sharp is contradicted. No theorem is presented as a consequence of the conjecture in these inspected passages. The optimal replacement coefficient for general triples remains open here.

## ASSUMED-UNVERIFIED

The bounded literature check in #22304 does not establish exhaustive worldwide novelty or priority. Its OpenAlex counts, general web searches, comparison with arXiv:2608.15558, MathDB and formal-conjectures queries, and historical repository-absence claim were not independently reproduced. The unique crossing near $p=2.35174$ reported in #22304 was not independently checked. The two conjecture passages, the primary source's adjacent estimates and square-sum theorem, and the restatement source's weaker-bound proof and remark were read directly.

The finite-matrix to $\ell_2$ operator interpretation, numerical evaluations, derivative argument, local failure intervals, equality-case analysis, proposed positivity or commutativity restrictions, applications of the source's weaker bound, and conclusions about the sources' dependence on the conjecture are not formalized here. Numerical tests settle no untested exponent. No global transition point, full failure range, corrected optimal coefficient, or validity theorem under either proposed restriction is established here; these remain open beyond the stated evidence.
