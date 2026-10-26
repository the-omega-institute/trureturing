---
slug: li-morgan-siegrist-2026-inflection-points-conjecture-6-1
bibkey: li2026concavity
doi: 10.1007/s41478-026-01192-9
url: https://link.springer.com/article/10.1007/s41478-026-01192-9
triage: theorem
motivation_gids:
  - D5/S0/Certificates/LiMorganSiegristInflectionRefutation.result
---

## Problem

Li, Morgan and Siegrist, *Concavity structure of fractional differential equations and zeros of Mittag–Leffler functions*, Conjecture 6.1, asks whether every solution under Theorem 5.2 has exactly one sign-changing zero of its second derivative in $(0,1)$. The source explicitly states that uniqueness remains open. The verbatim source and literature screen are in [#18772](https://github.com/the-omega-institute/trureturing/issues/18772), and the source locators are in [the Library note](../Library/Certificates/li2026concavity.md).

### Statement echo

| Source clause | Formal counterpart | Interpretation |
| --- | --- | --- |
| Definition 1.1, the left-sided Riemann–Liouville fractional integral | `rlIntegral` | Lower endpoint zero, `Real.Gamma`, real powers and the interval integral; positive order and positive argument give the source interpretation. |
| Equation (7), the solution and its boundary constant | `solution` | The source expression with the boundary constant substituted. Equivalence with the fractional Sobolev weak solution is supplied by the paper. |
| $1<\alpha<2$ | Two order hypotheses of `claim` | All real orders in this interval. |
| $f\in C([0,1])\cap C^1((0,1])$ | First two conjuncts of `Hypotheses` | `ContinuousOn` on the closed interval and `ContDiffOn` on the half-open interval. |
| $f(1)=0$, $f\geq0$, $f\not\equiv0$ | Next three conjuncts of `Hypotheses` | Endpoint equality, pointwise nonnegativity and one nonzero point. |
| Weighted right derivative limit zero | Last conjunct of `Hypotheses` | `deriv f`, right-sided neighborhood filter and exponent $(3-\alpha)/(2-\alpha)$. |
| Exactly one zero in $(0,1)$ | Existence and uniqueness conjuncts of `claim` | The derivative is `iteratedDeriv 2`; every interior zero equals the selected zero. |
| Changes sign at that zero | Last conjunct of `claim` | Negative product at every sufficiently close pair on opposite sides. |

There are no additional hypotheses on the public conclusion. Lean's integral and real powers are totalized; the displayed source interpretation uses their stated domain conditions.

## Motivation

The frozen settling declaration is `D5/S0/Certificates/LiMorganSiegristInflectionRefutation.result`, with admission basis `open-problem-resolution (#18772; Refuted)`. Its precise conclusion is the negation of the supplied conjecture. The witness uses $\alpha=3/2$ and $f(x)=(1-x)(1+5x^{12})$.

## Gap

The conjecture asserts uniqueness for every admissible forcing. Two distinct interior zeros suffice to refute it. The exact zero count and simplicity are stronger properties of the computed instance, rather than separate Lean conclusions. No equivalence with a fractional Sobolev formulation is formalized here.

## Route

The proof verifies all six forcing assumptions, evaluates the four monomial integrals at degrees $0,1,12,13$, differentiates their real-power closed form twice, and obtains

$$
x^{3/2}\Gamma(3/2)F''(x)=P(x),\qquad
P(x)=\frac{180640483}{1764461790}+\frac{x}{2}-x^2+
\frac{10485760}{676039}x^{13}-\frac{4194304}{260015}x^{14}.
$$

The positive multiplier preserves zeros for $x>0$. The signs at $7/10$, $3/4$ and $4/5$ give two zeros on disjoint intervals by the intermediate value theorem. These are the private steps `curvature_identity`, `polynomial_signs` and `two_distinct_zeros`, consumed by the public `result`.

## Falsifier

A failure of any forcing hypothesis, the curvature identity or the three strict signs would invalidate this refutation route. The public result checks their combination in Lean. The independent numerical quadrature in the experiment checks the curvature at four specified points without evaluating the polynomial formula.

## Evidence

The mathematical source is [DOI 10.1007/s41478-026-01192-9](https://doi.org/10.1007/s41478-026-01192-9), Definition 1.1, equation (7), Theorem 5.2 and Conjecture 6.1. All delivered theorem proofs are classified `bind-only`; the external named problem supplies the admission basis. The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).

### Experiment

[Published checker and results](https://github.com/the-omega-institute/trureturing-experiments/tree/b479024210b3fc827f415110e6419096c387e7e9/docs/reports/li-morgan-siegrist-2026-conjecture-6-1-inflection-uniqueness), commit `b479024210b3fc827f415110e6419096c387e7e9`, script `check.py`, SHA-256 `b862fce6a3a376f76896aa06bde0e1e1c7dca8908788b3c901f7422f243662ee`. Run `python3 check.py` in that pinned directory: exit 0, `RESULT PASS`.

For the fixed degree-12 instance at $\alpha=3/2$, the checker finds exactly three simple interior zeros, approximately $0.712340266337$, $0.780776464563$ and $0.896775163481$. Its exact rational evaluations give signs $+,-,+,-$ at $7/10,3/4,4/5,9/10$. Independent quadrature at these four points agrees with the curvature polynomial to absolute error below $10^{-41}$.

For $f_A=(1-x)(1+Ax^{20})$ at $\alpha=3/2$, the checker verifies that $P_A$ is affine in $A$, and verifies the signs $+,-,+,-$ at $1/2,3/4,19/20,1$ for the two endpoints $A=19,21$. For $(\alpha,k,A)=(1.1,8,10),(1.3,8,5),(1.7,30,10)$, it finds three sign changes on the grid $i/4000$, $1\leq i<4000$. Those grid readings do not certify an exact zero count or a uniform range of orders.

## Triage

### What the settlement shows

| Item | Status and evidence |
| --- | --- |
| Precise negation of Conjecture 6.1 | Proved in Lean by `result`, using at least two distinct zeros. The theorem does not separately assert exactly three zeros or sign-changing multiplicity. |
| Exact count three, simple zeros and four signs | Computed by the pinned checker for the degree-12 instance only, with the readings above. |
| Failure mechanism | Proved in Lean for the instance by the private `curvature_identity` and `polynomial_signs` on the path to `result`: the fractional averaging and boundary correction produce a curvature polynomial with repeated sign changes. This instance does not require a rising forcing, as the following prose argument shows. |
| Nonincreasing-forcing extension | Proved in prose below by exact differentiation and critical-point analysis. It is not a separate Lean theorem or an additional admission claim. |
| Surviving scope | The instance remains compatible with Theorem 5.2's at-least-one conclusion. The principal-eigenfunction Mittag–Leffler zero question is open and is not refuted here. The concave-and-nonincreasing subcase is outside the instance. |
| Degree-20 family $A\in[19,21]$ | Endpoint signs and affine dependence are computed by the pinned checker; the uniform extension in $A$ is proved in prose below. No Lean declaration asserts this family. |
| Other orders | Computed grid signs only for the three triples above. Uniform extensions, exact counts and simplicity at those orders are open. The reported absence of a degree-pattern example at $\alpha=1.9$ is unverified and gives no nonexistence result. |
| Unbounded inflection numbers | Open: the separated-pulse sketch for every order and every desired number of zeros has no checked proof here. |
| Concave, nonincreasing forcing | Conditional prose argument below; it uses the source's curvature formula and Theorem 5.2. It is not checked in Lean. |
| General nonincreasing forcing | The degree-12 witness is strictly decreasing by the prose argument below, and its nonuniqueness is proved by `result`. Thus nonincreasing forcing alone does not restore uniqueness. The issue's reported random sample is not a universal assertion and is not reproduced here. |
| Source's other conclusions | The at-least-one theorem survives this counterexample; a use of universal uniqueness cannot follow from the refuted conjecture. The principal-eigenfunction question remains distinct and open. |
| Literature status | The issue's screen found no settlement of the named conjecture in its searched sources. Completeness is `ASSUMED-UNVERIFIED`. |

### Strictly decreasing forcing

Exact differentiation gives

$$
f'(x)=-1+60x^{11}-65x^{12},\qquad
f''(x)=60x^{10}(11-13x).
$$

On $[0,1]$, $f'$ is nondecreasing up to $11/13$ and nonincreasing thereafter. Its maximum is

$$
f'(11/13)=-\frac{365602040982}{1792160394037}<0
\quad(\text{approximately }-0.204000736875146).
$$

Consequently $f$ is strictly decreasing throughout $[0,1]$. This is a proof in prose by critical-point analysis and rational arithmetic. It is not an added Lean declaration. The polynomial endpoints are exactly $P(0)=180640483/1764461790>0$ and $P(1)=-69088606/67863915<0$. Since $f''$ changes sign at $11/13$, this forcing is not concave on the whole interval.

### Degree-20 family

At every listed test point the checker verifies the same strict sign for both $P_{19}$ and $P_{21}$. Affine dependence gives

$$
P_A(x)=\frac{21-A}{2}P_{19}(x)+\frac{A-19}{2}P_{21}(x)
\qquad(19\leq A\leq21).
$$

The nonnegative coefficients sum to one, so the strict signs persist for all such $A$. The intermediate value theorem gives three distinct sign transitions. This is a proof in prose using the computed exact endpoints; no uniform-family theorem is claimed as kernel-checked.

### Concave and nonincreasing subcase

Conditional on the source's curvature representation and its regularity and nontriviality assumptions, put $K=I^\alpha f(1)(\alpha-1)(2-\alpha)>0$. Substituting $t=xs$ gives

$$
x^{2-\alpha}F''(x)=\frac{f(0)}{\Gamma(\alpha-1)}+
\frac Kx+\frac{x}{\Gamma(\alpha-1)}
\int_0^1(1-s)^{\alpha-2}f'(xs)\,ds.
$$

When $f'$ is nonpositive and nonincreasing, for $0<x<y$ one has $y f'(ys)\leq x f'(xs)$ for every $s\in[0,1]$. The last term is nonincreasing, and $K/x$ strictly decreases. Thus the scaled curvature is strictly decreasing and has at most one zero. Theorem 5.2 supplies a zero, so this conditional argument gives uniqueness and sign change, including the source examples $f=1-x$ and $f=1-x^2$. This prose argument is not independently formalized; it does not apply to the degree-12 witness.

## ASSUMED-UNVERIFIED

Completeness of the literature screen is `ASSUMED-UNVERIFIED`. The source supplies the equivalence between equation (7) and its fractional Sobolev weak solution; that bridge is not checked in Lean. Numerical zero counts, quadrature and grid signs have exactly the computed scopes stated above. The general pulse construction, principal-eigenfunction zero question, uniform other-order extensions and the reported random sample remain unverified here. The prose extensions have no additional Lean declarations.
