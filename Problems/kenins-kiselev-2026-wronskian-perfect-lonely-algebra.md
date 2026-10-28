---
slug: kenins-kiselev-2026-wronskian-perfect-lonely-algebra
bibkey: keninskiselev2026wronskianalgebras
doi: 10.48550/arXiv.2605.27305
url: https://arxiv.org/abs/2605.27305v2
triage: theorem
motivation_gids:
  - D5/S3/HomologicalAlgebra/WronskianPerfectLonelyAlgebra.result
---

# Perfect homogeneous Wronskian extensions exist exactly at order one

## Problem

Markuss G. Ķēniņš and Arthemy V. Kiselev, *Explicit class of finite-dimensional polynomial algebras with Wronskians over $\mathbb R^d$ as $N$-ary Lie brackets: beyond $\mathfrak{sl}(2)$*, arXiv:2605.27305v2 (2026), subsection `(Im)perfect N-ary SH-Lie polynomial algebras`, Open problem `open:perfect-algebras`. The following is the verbatim TeX paragraph at line 1259 of `FinDim220526v2.tex` (md5 `777135f176c9db701f21e5554216fb33`):

> Let the base dimension $d\geqslant 2$ and differential order $k\geqslant 1$ be arbitrary. Put the complete generalised Wronskian $W_d^k=\Bone\wedge \partial_\bx\wedges \partial^k_{\bx...\bx}$ as the $N$\nobreakdash-ary bracket, $N={d+k\choose d}$, on the $N$\nobreakdash-ary SH-Lie polynomial algebra $\Bbbk[x^1,...,x^d]$. Does there exist an homogeneous polynomial $p(\bx)\in \Bbbk[\bx]$ of degree $k+1$ such that the $N$\nobreakdash-ary SH-Lie polynomial subalgebra $\EuA=\Bbbk_k[\bx]\oplus\langle p(\bx)\rangle$ is \emph{perfect} w.r.t\ the Wronskian, i.e.\ $\Span_\Bbbk W_d^k(\EuA,...,\EuA)=\EuA$?

The source macros are retained in the quotation: `\Bone` is the identity operator, `\bx` denotes $\boldsymbol x$, `\wedges` denotes $\wedge\cdots\wedge$, `\EuA` denotes $\mathcal A$, and `\Span` denotes linear span. The source takes $\Bbbk=\mathbb R$ or $\mathbb C$ and writes $\Bbbk_k[\boldsymbol x]$ for polynomials of degree at most $k$ (TeX lines 538–542 and 613–623).

Issue [#22115](https://github.com/the-omega-institute/trureturing/issues/22115) fixes the statement over a characteristic-zero field $K$. Put

$I=\{\alpha\in\mathbb N^d:|\alpha|\le k\},\qquad W(f)=\det(\partial^\alpha f_\beta)_{\alpha,\beta\in I},$

$A_p=K_{\le k}[\boldsymbol x]+Kp,\qquad D_p=\operatorname{span}_K\{W(f):f:I\to A_p\}.$

Here $\partial^\alpha$ is ordinary iterated partial differentiation, without divided-power normalization. The settled statement is: for every characteristic-zero field $K$, every $d\ge2$ and every $k\ge1$,

$\bigl(\exists p\in K[\boldsymbol x],\ p\ne0,\ p\text{ homogeneous of degree }k+1,\ D_p=A_p\bigr)\ \Longleftrightarrow\ k=1.$

This classification is proved.

## Motivation

The source's research problem concerns perfect finite-dimensional polynomial algebras with the complete Wronskian as bracket (TeX lines 525–527). Perfectness requires regeneration of the entire vector space by bracket values, in addition to closure. Over the source fields $K=\mathbb R$ or $\mathbb C$, the source's main theorem 1 establishes closure of $K_{\le k}[\boldsymbol x]\oplus Kp$ for every $d\ge1$, $k\ge1$ and homogeneous $p$ of degree $k+1$ (lines 1187–1192). The open problem asks which parameter pairs also permit perfectness. The settlement gives the exact order restriction throughout the requested range $d\ge2$.

## Gap

Issue #22115 records the bounded literature check:

- The orchestrator (Claude Code, Opus) checked the v2 TeX question and searched for complete Wronskian brackets, perfectness and homogeneous top-degree polynomials; the reported hits were the source and arXiv:2510.02145.
- The same report checks the abstract of the authors' follow-up arXiv:2607.26039v2, which concerns degree growth under iterated brackets and does not mention perfect lonely algebras.
- The codex-cli search report identified in the issue attributes zero citing works to OpenAlex, no settlement to arXiv:2510.02145v1 or arXiv:2610.08636v1, and no match to formal-conjectures. MathDB returned HTTP 403.
- The preregistration reports no earlier repository issue title, module, Library note or dossier for arXiv:2605.27305.

`not-found-in-searched-scope`. These search reports do not establish exhaustive novelty or priority.

## Route

All lemma names below belong to `D5.S3.HomologicalAlgebra.WronskianPerfectLonelyAlgebra`; the proof helpers are private.

1. **Reduce to omission brackets.** Over any field $K$, for arbitrary natural $d,k$ and arbitrary polynomial $p$, `lonely_eq_span` identifies $A_p$ with the span of $p$ and the monomials $x^\alpha$ for $\alpha\in I$. For any $f:I\to K[\boldsymbol x]$ with every $f_\beta\in A_p$, `bracket_mem_span_basis` expands $W(f)$ into brackets of this generating family. For every selection $b:I\to\operatorname{Option}(I)$, `bracket_mem_span_omissions` places its generator bracket in the span of the $N+1$ brackets omitting one generator. Repetitions give equal columns and zero determinant; injective selections differ from one omission bracket by a column-permutation sign. Neither lemma requires $p$ to be nonzero or homogeneous.
2. **Separate homogeneous degrees.** Over any field $K$, for arbitrary natural $d,k$, functions $f:I\to K[\boldsymbol x]$ and $n:I\to\mathbb N$ satisfying that each $f_\beta$ is homogeneous of degree $n_\beta$, `wronskian_homogeneous` makes $W(f)$ homogeneous of degree $\sum_\beta n_\beta-\sum_{\alpha\in I}|\alpha|$, with truncated natural subtraction. This allows a zero bracket and does not assert nonvanishing or exact total degree. Over any field and arbitrary natural $d,k$, if $p$ is homogeneous of degree $k+1$, `omittedBracket_homogeneous` makes the bracket omitting $p$ homogeneous of degree zero, and the bracket omitting $x^\alpha$ homogeneous of degree $k+1-|\alpha|$.
3. **Obstruct higher orders.** Over any field, for arbitrary natural $d$ and $k\ge2$, homogeneous $p$ of degree $k+1$, and $f:I\to K[\boldsymbol x]$ with all arguments in $A_p$, `projected_bracket_bound` puts the degree-$k$ component of $W(f)$ in the span of the $d$ brackets omitting $x_i$. Over a characteristic-zero field, for $d\ge2$, $k\ge2$ and every homogeneous $p$ of degree $k+1$, `upper_order_obstruction` concludes $\neg\operatorname{perfect}(p)$. Its dimension contradiction uses the $d$ pure powers $x_i^k$ and $x_0^{k-1}x_1$: these are $d+1$ distinct, linearly independent degree-$k$ monomials in $A_p$, whereas the projected bracket span has at most $d$ generators. The proof establishes finite-dimensionality of that span before using its dimension. Nonzeroness of $p$ is not a hypothesis of the obstruction.
4. **Construct at order one.** Over any field $K$, for arbitrary natural $d$ and homogeneous quadratic $p$, `first_order_evaluations` gives $W(1,x_0,\ldots,x_{d-1})=1$. Replacing the constant column by $p$ gives $-p$; replacing the $x_i$ column by $p$ gives $\partial_i p$. These replacements retain their original column positions. Euler's quadratic identity supplies the determinant calculation. Over a characteristic-zero field with $d\ge2$, `quadratic_construction` takes $q=\sum_i x_i^2$, uses $\partial_iq=2x_i$ and invertibility of $2$ to obtain every generator from brackets, and also puts every bracket in $A_q$. It supplies a nonzero homogeneous quadratic with $D_q=A_q$. Finally, over a characteristic-zero field $K$ with $d\ge2$ and $k\ge1$, `result` combines this construction with `upper_order_obstruction` to prove `claim`.

## Falsifier

A statement about a different differential operator or a weaker notion of perfectness would not settle the source's question. The module uses:

- `I d k`, all differential multi-indices of total order at most $k$, each once;
- `pderivMulti`, ordinary repeated partial derivatives in coordinate order, and `wronskian`, their determinant on all $N$ arguments;
- `lonely`, the submodule sum $K_{\le k}[\boldsymbol x]+Kp$;
- `perfect`, the equality $D_p=A_p$, which includes both closure under brackets and generation by their values.

For nonzero homogeneous $p$ of degree $k+1$, the sum defining `lonely` is direct because its other summand has degree at most $k$. Indexing arguments by $I$ rather than $1,\ldots,N$ only changes their order, hence at most the sign of a bracket and not its span. Factorial-normalized monomials appearing elsewhere in the source change the generating basis by nonzero scalars over a characteristic-zero field; the differential operators themselves are not divided by factorials.

The claim excludes $p=0$, even though Lean's homogeneous predicate includes the zero polynomial. Its quantifiers require $d\ge2$, $k\ge1$ and characteristic zero. It asserts existence at order one, not perfectness for every quadratic. The module does not separately formalize the SH-Lie identities of the ambient Wronskian algebra.

## Evidence

The canonical source is `D5/S3/HomologicalAlgebra/WronskianPerfectLonelyAlgebra.lean` (622 lines).

- **Proof.** It proves `result : claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

Frozen state: `Golden/Frozen/state/D5/S3/HomologicalAlgebra/WronskianPerfectLonelyAlgebra.lean.json`, statement `sha256:f5460286f014eb9743ef7e91a871cf267d8f0a47c5d6d08d4227d1879082fddd`.

Declaration statements:

- `result`: `sha256:c8924cc4055629e4033f1a9cf9945703d77b8a6e1b45645a6099dfd613d8d7aa`;
- `claim`: `sha256:b5a7734b29a11de2eed3edb8590a1df2bdd97236409f6c222c6ba8a45b9a33d5`.

## Triage

Tier 1: an explicit open problem in a 2026 preprint, preregistered in issue #22115 before any Lean.
`theorem`; resolution `proved`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; the per-declaration proof shapes are listed in the delivery PR. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** for every characteristic-zero field $K$, every $d\ge2$ and every $k\ge1$, a nonzero homogeneous polynomial $p$ of degree $k+1$ whose complete-Wronskian bracket values on $K_{\le k}[\boldsymbol x]+Kp$ span exactly that subspace exists if and only if $k=1$.

**Argued, not formalized.**

- *Size of the higher-order deficit.* For a characteristic-zero field, $d\ge2$, $k\ge2$ and homogeneous $p$ of degree $k+1$, `projected_bracket_bound`, applied to arguments in $A_p$, bounds each projected bracket by the span of $d$ omission brackets. Linearity of the homogeneous projection extends this bound to the entire projected bracket span. The degree-$k$ homogeneous space has the monomial basis of size $\binom{d+k-1}{k}$. Subtracting dimensions therefore gives a deficit of at least $\binom{d+k-1}{k}-d$ in that component. This quantitative codimension statement is not an additional conclusion of `result`.
- *Which quadratics work.* For a characteristic-zero field, $d\ge2$ and a nonzero homogeneous quadratic $p$, `first_order_evaluations`, together with `bracket_mem_span_basis` for arguments in $A_p$ and `bracket_mem_span_omissions` for their generator selections, gives $D_p=\operatorname{span}_K\{1,p,\partial_0p,\ldots,\partial_{d-1}p\}$. Every listed generator is an actual bracket value, and every bracket is in their span. The constant, linear and quadratic homogeneous components are independent, so $D_p=A_p$ exactly when the partial derivatives span all linear forms. Writing $p=\tfrac12\boldsymbol x^{\mathsf T}H\boldsymbol x$ with its symmetric Hessian $H$, the gradient is $H\boldsymbol x$; the condition is $\det H\ne0$. Thus the remaining coefficient question at order one is a nondegeneracy condition. For example, $p=x_0^2$ has no derivative generating $x_1$ when $d\ge2$. This criterion is an ordinary linear-algebra argument, not a separate compiled declaration.
- *A relaxed field hypothesis for the construction.* For any field $K$ with $(2:K)\ne0$ and $d\ge2$, $q=\sum_i x_i^2$ is homogeneous of degree two and nonzero because the coefficient of $x_0^2$ is one. Its derivatives are $2x_i$, so `first_order_evaluations` applied to this homogeneous quadratic gives $1,-q,2x_i$ as bracket values. They generate $A_q$ because $2$ is invertible. For arguments in $A_q$, `bracket_mem_span_basis` and `bracket_mem_span_omissions` applied to the generator selections put every bracket in their span. This extends the order-one construction as an argument; `result` retains characteristic zero. No classification in positive characteristic is asserted here.
- *Sharpness and remaining scope.* Within the formal range $d\ge2$, $k\ge1$, the transition at $k=1$ is exact. For a characteristic-zero field, $d\ge2$, $k\ge2$ and homogeneous $p$ of degree $k+1$, `upper_order_obstruction` uses two distinct coordinates to obtain its extra mixed monomial. It does not supply a conclusion for $d=1$, missing lower-degree generators, or extensions with several independent top-degree generators.
- *Effect on the source.* The explicit cross-references to `open:perfect-algebras` occur in the problem and its following Comment (TeX lines 1258–1277). For the source fields $K=\mathbb R$ or $\mathbb C$, $d\ge2$ and $k\ge2$, `result` makes that Comment's generation requirement unattainable for every nonzero homogeneous $p$ of degree $k+1$. For those fields, $d\ge2$ and $k=1$, the quadratic criterion above answers the corresponding coefficient question. The source's main theorem 1, over those same fields and for every $d\ge1$, $k\ge1$ and homogeneous $p$ of degree $k+1$, concerns closure, so the negative perfectness conclusion at higher orders does not contradict it. The later question `open:existence-if-dropped-consistency` and conjecture `conj:non-existence-of-inconsistent` (lines 1669–1677) concern algebras with gaps in the lower-degree generators and remain outside this settlement.

## ASSUMED-UNVERIFIED

The bounded literature check in #22115 does not establish exhaustive worldwide novelty or priority. Its web-search results, follow-up abstract reading, OpenAlex citation count, negative readings of arXiv:2510.02145v1 and arXiv:2610.08636v1, formal-conjectures search and earlier-repository-record search were not independently reproduced. MathDB's HTTP 403 supplies no negative literature result. The v2 source question, its notation, the adjacent Comment, the closure theorem statement and the later inconsistent-algebra question were checked directly in the TeX identified above.

The random-polynomial rank readings attributed to the orchestrator (Claude Code, Opus) in #22115 remain unreproduced because the issue supplies neither the sampled coefficients nor a random seed. The codimension estimate, Hessian criterion, relaxed field hypothesis for the construction and discussion of consequences for the paper are argued rather than additional formalized statements. A complete dependency audit of the source's proofs was not performed. The SH-Lie identities, the source's general classification of finite-dimensional subalgebras, the dimension-one cases, order zero and positive-characteristic classification are not established by `result`.
