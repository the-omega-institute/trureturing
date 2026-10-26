---
slug: ma-weigert-2025-log-function-monotone-chain
bibkey: maweigert2025logfunctions
doi: 10.1007/s13324-025-01136-9
url: https://arxiv.org/abs/2505.04225v2
triage: theorem
motivation_gids:
  - D5/S3/Analytic/LogFunctionMonotoneChain.result
---

# The Ma–Weigert derivative-sign regions form a descending chain

## Problem

Rourou Ma and Julian Weigert, *Complete monotonicity of log-functions*, arXiv:2505.04225v2 (Analysis and Mathematical Physics 15, 141, 2025), §4, Conjecture `conj:shrinking`, `infiniteOrderDeriv.tex`, lines 154–160 (TeX macros expanded and display mathematics set inline):

> For any $n\in \mathbb N$ the semialgebraic sets $D_k=\left\{f\in \mathcal{F}_{1,n}\middle|\forall x\in \mathbb R:\left(\frac{-\mathrm d}{\mathrm d x}\right)^kf(x)\geq 0\right\}$ form a descending chain under inclusion, i.e. $D_k\supseteq D_{k+1}$, which converges to the region $\mathrm{CM}_{1,n}=\bigcap_{k=1}^\infty D_k$.

The source defines $\mathcal F_{1,n}$ as the smooth functions $f(x)=p(\log x)/x$ on $x>0$, where $p$ is a real polynomial of degree at most $n$ (`Intro.tex`, lines 20–23). Although the conjecture's display writes $x\in\mathbb R$, the functions' domain and the preceding example's sign condition are $x>0$ (`infiniteOrderDeriv.tex`, line 150). Issue [#21992](https://github.com/the-omega-institute/trureturing/issues/21992) fixes this positive-domain reading.

Write $f_p(x)=p(\log x)/x$ and $D_{n,k}=\{p\in\mathbb R[y]:\operatorname{natDegree}(p)\le n,\ \forall x>0,\ (-1)^k f_p^{(k)}(x)\ge0\}$. The module represents regions by their polynomial parameters. Its `claim` states, for every $n\in\mathbb N_0$:

- $D_{n,k+1}\subseteq D_{n,k}$ for every natural $k\ge1$;
- for each real polynomial $p$ with $\operatorname{natDegree}(p)\le n$, membership in every $D_{n,k}$ with $k\ge1$ is equivalent to $(-1)^j f_p^{(j)}(x)\ge0$ for every natural $j\ge0$ and every $x>0$.

Here $f_p^{(j)}$ denotes Lean's `iteratedDeriv j (logFunction p)`. The zero polynomial has natural degree zero. The claim is proved.

## Motivation

The source studies complete monotonicity in polynomial log-function spaces and gives a finite coefficient-based description using inverse Laplace transforms and nonnegative polynomials. Its derivative-sign regions offer another description: each derivative order gives an outer approximation. Nesting determines whether increasing that order can ever reintroduce a polynomial parameter already excluded by a lower order. The intersection assertion also asks whether positive derivative orders alone recover the order-zero nonnegativity condition.

## Gap

The bounded literature check in #21992 reports:

- the preregistering orchestrator read the v2 TeX conjecture and found only the source in web searches using the paper with “descending chain” and nesting;
- the codex-cli search author identified in that issue, `a13231ff2f7579617f7ad225`, reported that the journal version retains Conjecture 4.6, that the citing work by Ditsch–Henn–Raman, arXiv:2512.18499, does not resolve it, and that MathDB and formal-conjectures had no match;
- the orchestrator reported no repository issue, module, Library note or dossier for arXiv:2505.04225 within that preregistration search.

`not-found-in-searched-scope`. The source itself establishes the quadratic contraction and the intersection description for its displayed quartic family; neither statement supplies the general nesting argument.

## Route

All helper names below refer to the private declarations in the canonical module.

1. **Derivative polynomials.** For a real polynomial $p$ and natural $j$, `derivativePolynomial` defines $q_0=p$ and $q_{j+1}=(j+1)q_j-q_j'$. For every such $p,j$ and every real $x>0$, `signed_derivative_formula` gives $(-1)^j f_p^{(j)}(x)=(x^{-1})^{j+1}q_j(\log x)$. For any natural $n,j$ and any real polynomial $p$, `sign_transfer` states $p\in D_{n,j}$ if and only if $\operatorname{natDegree}(p)\le n$ and $q_j(y)\ge0$ for every real $y$. It uses the positive factor and $x=\exp y$; it imposes no nonzero or positive-degree hypothesis on $p$.
2. **Recovering polynomial nonnegativity.** For a real polynomial $q$, a real scalar $a>0$, and the hypothesis $(aq-q')(y)\ge0$ for every real $y$, `nonneg_of_sub_derivative` concludes $q(y)\ge0$ for every real $y$. If $\operatorname{natDegree}(q)=0$, this is division of a constant inequality by $a$, including the zero polynomial. Otherwise the derivative has smaller degree, so $aq-q'$ has the degree of $q$ and leading coefficient $a$ times that of $q$. The helper `leadingCoeff_nonneg_of_nonneg`, whose hypothesis is nonnegativity of a real polynomial at every real argument, supplies nonnegative leading coefficients from $aq-q'$ and its reflection. These imply that $q$ tends to $+\infty$ at both ends. Continuity gives a global minimum $m$, polynomial differentiability gives $q'(m)=0$, and $0\le aq(m)$ gives the conclusion. No infimum without an attained minimum is used.
3. **Nesting.** For any natural $n,k$, `descending` proves $D_{n,k+1}\subseteq D_{n,k}$. It applies the preceding implication to the real polynomial $q_k$ with $a=k+1>0$, and retains the degree bound on $p$. This helper also covers $k=0$; `result` exposes the inclusions required by `claim`, namely $k\ge1$.
4. **Intersection.** For any natural $n$ and any real polynomial $p$ satisfying $\operatorname{natDegree}(p)\le n$, `intersection` proves the equivalence between membership in all positive-order regions and `completelyMonotone (logFunction p)`. Membership in $D_{n,1}$ and `descending n 0` supply order zero; the remaining orders are already among the hypotheses. Conversely, all signed derivative inequalities together with the given degree bound give each region membership. `result : claim` combines this equivalence and the required inclusions.

## Falsifier

A counterexample to `claim` would be either a natural $n$, a natural $k\ge1$, and a polynomial in $D_{n,k+1}$ outside $D_{n,k}$, or a polynomial of natural degree at most $n$ satisfying every positive-order sign condition but violating one of the conditions of `completelyMonotone`.

Source fidelity requires the positive half-line, the fixed degree bound, and all derivative orders in the intersection. The Lean function `logFunction` is total on the reals, but every sign condition explicitly requires $x>0$. The predicate `completelyMonotone` records all signed derivative inequalities, including order zero; it does not separately assert smoothness. For polynomial log-functions, smoothness on the positive half-line follows analytically from smoothness of polynomials, logarithm and division by a nonzero argument. That smoothness bridge is not a separate conclusion of `result`. Semialgebraicity and a rate of convergence are also absent from its type.

## Evidence

The canonical source is `D5/S3/Analytic/LogFunctionMonotoneChain.lean` (166 lines).

- **Proof.** It proves `result : claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

Frozen state: `Golden/Frozen/state/D5/S3/Analytic/LogFunctionMonotoneChain.lean.json`, statement `sha256:c1731638f8309b11d902fde2676cb6ca61e1d6727334d3a7fa2ca235e321c06f`.

Declaration statements:

- `result`: `sha256:5d5fcb685dd8148f07cbf4d19d36ba607e4cb5aadfe22fc861d7751c864729b5`;
- `claim`: `sha256:c788876a7f1fa7d77c2cf8fde293e9334ca667f46d23868ef03246d0447b7628`.

## Triage

Tier 1 conjecture of a 2025 journal article, preregistered in issue #21992 before any Lean.
`theorem`; resolution `proved`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; the per-declaration proof shapes are listed in the delivery PR. There is no digestion atom.

Ma and Weigert (2025), arXiv:2505.04225v2, establish the following source results. The example in `infiniteOrderDeriv.tex`, lines 145–152, concerns $\mathcal F'_{1,4}$, whose numerators are $y^4+c_2y^2+c_1y+c_0$ with real $c_0,c_1,c_2$. It identifies that family's completely monotone region with the intersection of the signed-derivative regions over all $m\in\mathbb N_0$; its plots suggest their nesting. The quadratic contraction is Remark `rem:shrinking`, `example.tex`, lines 137–145: for $c_2>0$ and $k\ge1$, $\operatorname{disc}(g_{k-1})-\operatorname{disc}(g_k)=-4c_2^2/k^2<0$, under the coefficient assumptions introduced at line 96. The settlement adds nesting and the positive-order intersection description for every natural degree bound, including zero, without restricting the leading or cubic coefficients.

### What the settlement shows

**Proved by `result`:** for every natural degree bound $n$, the set of real polynomials $p$ with $\operatorname{natDegree}(p)\le n$ and $(-1)^{k+1}f_p^{(k+1)}(x)\ge0$ for every $x>0$ is contained in the corresponding order-$k$ set whenever the natural number $k$ satisfies $k\ge1$. For each real polynomial $p$ with that degree bound, satisfying these inequalities for all natural $k\ge1$ is equivalent to satisfying them for all natural $k\ge0$, at every $x>0$.

**Computed, not formalized** (exact rational arithmetic): for each tested $k=0,\ldots,8$, put $H_k=\sum_{r=1}^k1/r$, $H_k^{(2)}=\sum_{r=1}^k1/r^2$, and $p_k(y)=y^2+H_k^{(2)}$. Iterating the polynomial recurrence gave $q_k=k!(y-H_k)^2$ and $q_{k+1}=(k+1)!((y-H_{k+1})^2-1/(k+1)^2)$, with all coefficients compared exactly. Their quadratic minima were respectively zero and $-k!/(k+1)$; for $k=1$, these are zero and $-1/2$. No mismatch with these identities was observed for the tested family. These finite computations do not establish an assertion for all $k$.

**Argued, not formalized.**

- *Decisive mechanism and its hypotheses.* The inverse implication in `nonneg_of_sub_derivative` concerns a real polynomial $q$, a positive real $a$, and $(aq-q')(y)\ge0$ at every real $y$. A negative global minimum would make that last expression negative at the minimizer. The polynomial and global-domain hypotheses supply the minimum in the nonconstant case, as detailed in Route. Positivity of $a$ cannot simply be dropped: for $a\le0$ and the constant polynomial $q=-1$, $aq-q'=-a\ge0$ but $q<0$. Nor does the implication extend to arbitrary smooth $q$: for $a>0$, $q(y)=-\exp(ay)$ has $aq-q'=0$ and is negative everywhere.
- *Strictness and finite derivative tests.* For any real $C$, the recurrence defining `derivativePolynomial`, applied to $p(y)=y^2+C$, gives $q_j=j!((y-H_j)^2+C-H_j^{(2)})$ for every natural $j$. The initial case has $H_0=H_0^{(2)}=0$; substitution into $q_{j+1}=(j+1)q_j-q_j'$ and completion of the square replace $H_j$ by $H_j+1/(j+1)$ and $H_j^{(2)}$ by $H_j^{(2)}+1/(j+1)^2$, giving the inductive step. Taking $C=H_k^{(2)}$ gives a globally nonnegative $q_k$ and a $q_{k+1}$ negative at $y=H_{k+1}$. For any $n\ge2$ and $k\ge1$, these degree-two parameters meet the hypotheses of `sign_transfer` and lie in $D_{n,k}$ outside $D_{n,k+1}$. For every natural $j\le k$, $H_j^{(2)}\le H_k^{(2)}$, so the same identity gives nonnegativity at every order through $k$. Thus the argument gives strict nesting and excludes a uniform finite derivative-order cutoff for $n\ge2$. This argument is not a conclusion formalized by `result`.
- *Degenerate degree bounds.* For $n=0$ or $n=1$, write $p(y)=by+c$. The recurrence gives the coefficient of $y$ in $q_j$ as $j!b$, so global nonnegativity forces $b=0$. With $b=0$ it gives $q_j=j!c$, whose nonnegativity is equivalent to $c\ge0$. Hence all the regions in these degree bounds equal the set of nonnegative constant polynomials. This classification is not formalized in the module.
- *A neighbouring extension.* For a real $a>0$ and a real polynomial $p$, the same differentiation argument for $f_a(x)=x^{-a}p(\log x)$ on $x>0$ gives $(-1)^j f_a^{(j)}(x)=x^{-a-j}q_j(\log x)$ with $q_0=p$ and $q_{j+1}=(a+j)q_j-q_j'$. Indeed differentiating the order-$j$ expression multiplies its polynomial by $-(a+j)$ and adds its derivative; changing the sign gives the stated recurrence. The multiplier $x^{-a-j}$ is positive and every $a+j$ is positive, so the polynomial implication yields nesting and recovers order zero from order one. This extension is not formalized; its endpoint $a=0$ cannot recover order zero, as the function $f_0=-1$ has all positive derivatives zero.
- *Effect on the source.* The nesting suggested by Figure `fig:ShrinkCone4` and stated in Conjecture `conj:shrinking` becomes an inclusion statement for every degree. The source's inverse-Laplace and semialgebraicity results use their own arguments (`mainTh.tex`, lines 54–75 and 185–190), rather than assuming this conjecture. The settlement supplies the missing nesting step in the derivative viewpoint of §4; it neither replaces those coefficient criteria nor formalizes their proofs. Quantitative convergence, multivariate derivative-region analogues and the connection to the source's limiting transformed polynomials are not settled by this module.

## ASSUMED-UNVERIFIED

The bounded literature check in #21992 does not establish exhaustive worldwide novelty or priority. Its web-search completeness and repository-search readings were reported by the preregistering orchestrator and are not independently reproduced here. Retention in the journal version, the assessment of Ditsch–Henn–Raman (arXiv:2512.18499), and the MathDB and formal-conjectures searches are the named search author's reports; those readings are not independently reproduced. The source reading supporting this dossier is the v2 arXiv TeX, not an independent comparison with the journal text.

The statements labelled “Computed, not formalized” and “Argued, not formalized” are outside the compiled conclusion. This includes general strictness, the absence of a finite derivative-order cutoff, the classification for degree bounds zero and one, and the extension to $x^{-a}p(\log x)$. The analytic smoothness bridge, identification with the source's smooth function spaces, and discussion of effects on the source are not separate Lean theorems in this module. Semialgebraicity, inverse Laplace formulas, convergence rates and multivariate extensions are not formalized by this settlement; the latter quantitative and multivariate questions remain open here. The positive-domain interpretation is the explicit reading of #21992; the literal all-real-domain display is not asserted.
