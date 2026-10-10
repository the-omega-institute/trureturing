---
slug: krishna-2022-cstar-kushel-tyaglov
bibkey: krishna2022cstarschoenberg
doi: 10.48550/arXiv.2206.06653
url: https://arxiv.org/abs/2206.06653v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Algebra/CStarKushelTyaglov.result
---

# The C*-algebraic Kushel–Tyaglov Conjecture is false

## Problem

K. Mahesh Krishna, "C*-algebraic Schoenberg Conjecture", arXiv:2206.06653v1 (14 June 2022; single version), Section 2. The source text is quoted verbatim:

> **Conjecture 2.4 (C*-algebraic Kushel-Tyaglov Conjecture).** Let $\mathcal{A}$ be a C*-algebra, $n\in \mathbb{N}\setminus\{1\}$ and let $P(z) \coloneqq (z-a_1)(z-a_2)\cdots (z-a_d)$ be a polynomial over $\mathcal{A}$ with $a_1, a_2, \dots, a_d\in \mathcal{A}$. Assume that $P'$ can be written as $P'(z)\coloneqq d (z-b_1)\cdots (z-b_{d-1})$ on $\mathcal{A}$ with $b_1, b_2, \dots, b_{d-1} \in \mathcal{A}$. Then
> $$\sum_{k=1}^{d-1}(b_kb_k^*)^2\leq \frac{d-6}{d}\sum_{j=1}^{n}(a_ja_j^*)^2+\frac{1}{d^2}\left(\sum_{j=1}^{d}a_ja_j^*\right)^2+ \frac{1}{d^2}\left[\sum_{j=1}^{d}a_j^2-\frac{1}{d^2}\left(\sum_{k=1}^{d}a_k\right)^2\right] \left[\sum_{j=1}^{d}a_j^2-\frac{1}{d^2}\left(\sum_{k=1}^{d}a_k\right)^2\right]^* +\frac{2}{d}\sum_{j=1}^{d}a_j\left[a_j+\frac{1}{d}\sum_{k=1}^{d}a_k\right]\left[a_j+\frac{1}{d}\sum_{k=1}^{d}a_k\right]^*a_j^*-\frac{4}{d^3}\sum_{j=1}^{d}a_j \left[\sum_{k=1}^{d}a_k \right] \left[\sum_{k=1}^{d}a_k \right]^*a_j^*$$
> and
> $$\sum_{k=1}^{d-1}(b_k^*b_k)^2\leq \frac{d-6}{d}\sum_{j=1}^{d}(a_j^*a_j)^2+\frac{1}{d^2}\left(\sum_{j=1}^{d}a_j^*a_j\right)^2+ \frac{1}{d^2}\left[\sum_{j=1}^{d}a_j^2-\frac{1}{d^2}\left(\sum_{k=1}^{d}a_k\right)^2\right]^* \left[\sum_{j=1}^{d}a_j^2-\frac{1}{d^2}\left(\sum_{k=1}^{d}a_k\right)^2\right] +\frac{2}{d}\sum_{j=1}^{n}a_j^*\left[a_j+\frac{1}{d}\sum_{k=1}^{d}a_k\right]^*\left[a_j+\frac{1}{d}\sum_{k=1}^{d}a_k\right]a_j-\frac{4}{d^3}\sum_{j=1}^{d}a_j^* \left[\sum_{k=1}^{d}a_k \right]^* \left[\sum_{k=1}^{d}a_k \right]a_j.$$

The ordered derivative is defined in the source immediately before the conjecture. In Conjecture 2.4, the encoding reads the printed n as d. Indices become zero-based Fin types and the product order is retained. The encoding uses complex scalar coefficients, star, and the C*-order, and restricts the source to unital C*-algebras in Type with PartialOrder and StarOrderedRing and d >= 2; this subclass is enough for a counterexample to the source's universal assertion.

## Motivation

The same cubic matrix polynomial settles this conjecture and the two linked conjectures in the Schoenberg dossier (krishna-2022-cstar-schoenberg.md) and the de Bruin-Sharma dossier (krishna-2022-cstar-de-bruin-sharma.md). Each dossier records one named OpenProblemResolutionClaim on its own result node.

## Gap

The published source states the conjecture and the bounded literature check recorded in #14845 did not identify a prior settlement in that searched scope. Exhaustive literature coverage and publication priority remain ASSUMED-UNVERIFIED.

## Route

In M_2(C) let x=E_12, y=E_11+E_12, and
$$
a_1=(2x+y)/3,\quad a_2=(-x+y)/3,\quad a_3=(-x-2y)/3,\qquad
u=(x+y)/3,\quad (b_1,b_2)=(u,-u).
$$
Then xy=0 != yx, sum_j a_j=0, and the ordered derivative equals 3(z-u)(z+u) for every matrix z. The first inequality has right side minus left side D_2.4^(1)=-t^4(43c^2+158) E_11/81. Its first diagonal entry is negative, so the C*-order inequality fails. The fixed Lean result is D5/S3/Quantum/Algebra/CStarKushelTyaglov.result.

## Falsifier

The encoded statement retains the full-algebra factorization hypothesis, both inequalities, the source coefficients and the noncommutative product order. A failure of factorization, a sign error in the displayed defect, or a changed source clause would invalidate this route. The Lean result verifies the fixed witness and the negation of the stated claim.

## Evidence

The settling module is D5/S3/Quantum/Algebra/CStarKushelTyaglov.lean. The imported witness lemmas sum_a, factorization and negative_e11_not_posSemidef supply the zero-sum, whole-algebra factorization and positivity obstruction. The public result is the designated refutation result (basis=refutes) and is exempt from four-slot escape registration (CLAUDE.md §3.9). The axiom closure of every public declaration is contained in {propext, Classical.choice, Quot.sound}.

Experiment: exact symbolic matrix check at https://github.com/the-omega-institute/trureturing-experiments/tree/51f6d69f317a872443b4d3360ae4b28808dee017/docs/reports/krishna-2022-cstar-schoenberg-critical-points, entry check.py, SHA-256 702b68b36e2ae270381994118ce00660b5310f00ad5c514705b95334a7b0f4dd. Command: python3 docs/reports/krishna-2022-cstar-schoenberg-critical-points/check.py in the experiments repository; exit 0. The tested scope is symbolic real t,c>0 and an arbitrary symbolic 2x2 matrix z, with x=tE_12, y=t(cE_11+E_12) and the displayed definitions of a,u,b. The factorization residual and sum_j a_j are zero matrices.

The first defects are
$$
D_2.1^(1)=-2t^2 E_11/9,\qquad
D_2.3^(1)=2t^4(c^2-7)E_11/81,\qquad
D_2.4^(1)=-t^4(43c^2+158)E_11/81.
$$
The second defects are
$$
D_2.1^(2)=t^2\begin{pmatrix}0&-c\\-c&-2\end{pmatrix}/9,
\quad D_2.3^(2)=t^4\begin{pmatrix}-5c^2&-c(c^2+7)\\-c(c^2+7)&-5c^2-14\end{pmatrix}/81,
$$
$$
D_2.4^(2)=t^4\begin{pmatrix}-44c^2&-c(c^2+79)\\-c(c^2+79)&-5c^2-158\end{pmatrix}/81.
$$
Their least eigenvalues are respectively negative for t,c>0, with exact formulas in the experiment entry. Conjecture 2.4 fails throughout t,c>0. The fixed Lean result uses t=c=1 and the first inequality.

## Triage

### What the settlement shows

**Mechanism — proved.** In a noncommutative ring with $\sum_j a_j=0$,
$$
P'(z)-3(z-u)(z+u)=z(2a_1+a_2-3u)-(2a_1+a_2-3u)z+a_1a_2-(a_1+a_2)^2+3u^2.
$$
With $2a_1+a_2=x+y=3u$, the remainder is $xy/3$. Hence a one-sided zero divisor $xy=0\ne yx$ satisfies the factorization while $xy^*+yx^*\ne0$ changes the energies. The fixed instance is kernel-checked by CStarSchoenberg.factorization, imported by the latter two modules where applicable.

**Witness family — computed.** The experiment entry above verifies the symbolic family for $t,c>0$, all six defect matrices and the least-eigenvalue formulas. The first inequality of 2.3 fails for $0<c<\sqrt7$, and its second inequality fails for every $c>0$. The other two conjectures' first and second inequalities fail for every $t,c>0$. Uniform extension beyond this tested symbolic scope is not claimed by computation. The fixed first-inequality refutation for this dossier is kernel-checked.

**Corner embedding — proved in prose, not formalized.** For every $n\ge2$, embed $x,y$ in the upper-left corner of $M_n(\mathbb{C})$. The identities $xy=0$, $2a_1+a_2=3u$ and $\sum_j a_j=0$ persist, and the displayed algebraic identity applies to every $z\in M_n(\mathbb{C})$. The negative corner defect therefore persists. This embeds the present refutation in every matrix size $n\ge2$.

**Commutative case — proved (literature) for 2.1 and 2.3, not formalized.** In a commutative unital C*-algebra, Gelfand evaluation sends the factorization and C*-order to pointwise scalar statements. The classical results apply: Malamud–Pereira for 2.1 and Cheung–Ng for 2.3. For these two conjectures, commutativity removes the one-sided-zero-divisor mechanism. This literature consequence is not formalized here.

**Conjecture 2.4 already fails in $\mathbb{C}$ — computed.** The scalar inequality that the source quotes as the Kushel–Tyaglov theorem (Section 1), which Conjecture 2.4 lifts term by term, is false as printed. Take $d=3$ and $a=(1+i,\,1-i,\,1)$. Then $P(z)=(z-1)^3+(z-1)$, so $P'(z)=3(z-b_1)(z-b_2)$ with $b_{1,2}=1\pm i/\sqrt3$. The left side is $32/9$ and the right side is $28/9$, so the inequality fails by $4/9$. The same data refute Conjecture 2.4 in the commutative C*-algebra $\mathbb{C}$, so commutativity does not restore 2.4 as transcribed. The exact check is pinned at [scalar-kushel-tyaglov.py](https://github.com/the-omega-institute/trureturing-experiments/blob/f7cf7ad682cb87c7c44587f34a0a364b5be84665/docs/reports/krishna-2022-cstar-schoenberg-critical-points/scalar-kushel-tyaglov.py); command `python3 scalar-kushel-tyaglov.py`, exit 0, script SHA-256 `19281dba6dfa200069d585239213a1151175da8fd53d207b8756d842701412f4`. Whether Kushel and Tyaglov's published theorem differs from the source's quotation was not checked against their paper: `ASSUMED-UNVERIFIED`.

**Degree two — proved (source).** Krishna's Theorem 2.2 proves Conjecture 2.1 for $d=2$ with equality, and the source states the degree-two case of Conjecture 2.3. The present counterexample has $d=3$ and leaves those degree-two statements intact.

**Trace versions — proved in prose, not formalized.** $M_2(\mathbb{C})$ is a factor: a matrix commuting with every matrix unit is scalar. Its normalized trace $\tau=\operatorname{Tr}/2$ is faithful, since $\tau(v^*v)=\frac12\sum_{i,j}|v_{ij}|^2$ vanishes only for $v=0$. At $t=c=1$, applying $\tau$ to the first-inequality defects $-\frac29 E_{11}$, $-\frac4{27} E_{11}$ and $-\frac{67}{27} E_{11}$ gives $-\frac19$, $-\frac2{27}$ and $-\frac{67}{54}$, respectively. Each is negative, so the same witness refutes all three inequalities taken in trace.

**Open.** Whether Conjectures 2.1 and 2.3 hold for $d\ge3$ under extra hypotheses excluding one-sided zero divisors among the relevant products, short of full commutativity, remains open here. Conjecture 2.4 as transcribed has no such repair, because it fails in $\mathbb{C}$. Krishna's companion C*-algebraic Gauss–Lucas/Sendov, Casas–Alvero and Smale mean-value conjectures are outside this delivery. Any source result relying on one of the three conjectures as an assumption loses that unconditional implication; the source's independent definitions, scalar results and degree-two theorem are unaffected.

## ASSUMED-UNVERIFIED

The literature check is bounded by #14845 and the cited source; exhaustive absence of another settlement is ASSUMED-UNVERIFIED. The symbolic experiment is evidence only for its stated scope. The unfinished escape audit for the non-result public witness declarations is tracked in #14861; no declared_validated claim is made.
