---
slug: herrera-2023-function-approximation-conjecture
bibkey: herrera2023functionapproximation
doi: null
url: https://arxiv.org/abs/2311.17448v1
triage: theorem
motivation_gids:
  - D5/S3/Fourier/PositiveFourierApproximationRefutation.result
---

# Herrera's function-approximation conjecture

## Problem

D. Herrera, *On the commutator modulus of continuity for operator monotone functions*, arXiv:2311.17448v1, Conjecture 2 (numbered 1.10 in print), states:

> Let $f$ be a non-negative function that is operator monotone on $[0, \infty)$. Then $E_{f}(c) \leq Cf(c)$ holds for all $c > 0$ when $C = 1$.

The source defines

$$
E_f(c)=\inf_{g'\in\widehat{\mathcal M}_+}
\left(\sup_{x\ge0}(f-g)(x)-\inf_{x\ge0}(f-g)(x)+cg'(0)\right),
$$

where $\widehat{\mathcal M}_+$ consists of Fourier transforms of finite positive Borel measures on $\mathbb R$. Section 5, equation (28), requires $g\in C^1(\mathbb R)$. The conjecture is refuted by $f(x)=x/(1+x)$ and $c=1$. Preregistration: [#15279](https://github.com/the-omega-institute/trureturing/issues/15279).

### Statement echo

| Source clause | Lean counterpart | Scope |
| --- | --- | --- |
| “$g$ is $C^1(\mathbb R)$ and $g'$ is the Fourier transform of a finite positive Borel measure” | `IsAdmissible` | `ContDiff` and a finite positive measure, with the complex exponential sign convention. |
| The displayed oscillation plus $cg'(0)$ | `approxCost` | Supremum and infimum on the subtype of nonnegative reals. |
| Infimum over admissible $g$ | `approxError` | Real infimum over finite oscillation costs. |
| “a non-negative function” | The nonnegativity premise of `claim` | Every nonnegative real argument. |
| “operator monotone on $[0,\infty)$” | `OperatorMonotoneOn` | Loewner order for positive semidefinite complex matrices at every finite dimension. |
| “for all $c>0$ when $C=1$” | The positive-$c$ conclusion of `claim` | The constant is exactly one. |
| Failure of the conjecture | `result : ¬ claim` | The witness satisfies all premises; the lower bound exceeds $f(1)$. |

`approxError` is a real infimum; Lean's real empty-set infimum convention is zero. The refutation instance has a nonempty finite cost set, witnessed by $g=0$, and a uniform finite lower bound. Discarding infinite-cost candidates preserves the source infimum in this domain. No extended-real equivalence is claimed for targets without a finite-cost approximant. Matrix monotonicity at all finite dimensions is the classical Löwner formulation used here; no separate infinite-dimensional transport theorem is claimed.

## Motivation

The positive-Fourier approximation problem supplies upper estimates for commutator moduli. Its sharp constant need not equal the sharp constant of the commutator problem. A positive lower barrier for the approximation cost distinguishes these questions.

## Gap

The source proves an upper constant $C<1.01975$ for $x/(x+1)$ using Gaussian approximants, while Conjecture 2 asks for $C=1$. The published upper estimates do not give the lower obstruction proved here. The preregistration's literature search found no settlement in its searched scope.

### Literature reading

The source is arXiv:2311.17448v1. The preregistration records inspections of Herrera's arXiv:2409.14636, 2412.20795 and 2609.15057, and Boyadzhiev, *Publ. RIMS* 26 (1990), 521–527; these are search-seat reports, not independent Lean evidence.

R. Farrell, *Lipschitz conditions on operators and matrices*, [UNF thesis 1343](https://digitalcommons.unf.edu/etd/1343/) (2025), was read in full by the orchestrator through the NyxID Firecrawl proxy (180,280 characters). It cites Herrera for the inequality of Corollary 1.3, as its Theorem 20, and does not treat Conjecture 2 or $E_f$. This is an orchestrator-reported literature reading; it is not a claim of exhaustive literature coverage.

## Route

For an admissible $g$, write $m=g'(0)$ and $d(x)=xm-(g(x)-g(0))$. The Fourier representation gives

$$
m-g'(s)=\int(1-\cos(ts))\,d\mu(t)\ge0.
$$

Mathlib's Chebyshev derivative bound yields $|\sin(Nu)|\le N|\sin u|$ for natural $N$. The half-angle identity then gives $1-\cos(Nu)\le N^2(1-\cos u)$. Integration and a change of scale give $d(Nc)\le N^3d(c)$. No moment assumption or interchange of two integrals is required.

Let $W$ be the oscillation of $f-g$ and $e=W+cm-f(c)$. Since $f(0)=0$, the normalized residual lies between $-W$ and $W$. Comparing $c$, $2c$ and $Nc$ yields

$$
(N^3+N+2)e\ge D_N(f,c),\qquad
D_N(f,c)=(N+1)f(2c)-(N+2)f(c)-f(Nc).
$$

For $f(x)=x/(1+x)$, $c=1$ and $N=11$, this forces $e\ge1/2304$. The resolvent formula $f(A)=I-(I+A)^{-1}$ proves operator monotonicity by order reversal of positive inverses. The module applies `CStarAlgebra.ringInverse_le_ringInverse` for this step.

## Falsifier

The formal refutation would fail if the witness were not nonnegative and operator monotone, if the finite cost set were empty, or if an admissible finite-cost approximant had cost below $1153/2304$. The private nonnegativity, monotonicity, nonemptiness and uniform-bound lemmas on `result`'s proof path exclude these alternatives.

## Evidence

Settling node: `D5/S3/Fourier/PositiveFourierApproximationRefutation.result`. Its type is literally `Not claim`, and the claim definition has compiled type `Prop`. The axiom closure of every public declaration is contained in $\{\mathrm{propext},\mathrm{Classical.choice},\mathrm{Quot.sound}\}$.

The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9). It is the module's only public theorem; all supporting lemmas are private.

### Experiment entry

[Pinned experiment directory](https://github.com/the-omega-institute/trureturing-experiments/tree/ca9b6ca70c86a0acde744fe7ade72d7416c475cf/docs/reports/herrera-2023-function-approximation-conjecture), script `check.py`, command `python3 check.py`, exit 0. Script SHA-256: `99ec286668a3c45880cb4005e00e420b49a2c1da15e173b646b467abbe022a39`. The final reading is `bad= 0`.

The exact symbolic checks verify the closed form of $D_N(f_a,c)$ and $D_{11}(f_a,a)=7/12$, the gap $1/2304$ and the bound $1153/2304$. The positivity grid uses $r=k/8$ for $k=1,\ldots,159$ and $N=\lceil4r+4\rceil$. The cosine check uses $N=1,\ldots,12$ and 200,001 equally spaced $u\in[-20,20]$, with numerical tolerance $10^{-12}$. The Gaussian consistency check uses $f_1$, $c=1$, 96 equally spaced amplitudes in $[0.05,1]$, 120 logarithmically spaced parameters in $[0.01,10]$ and 400,001 points of $x\in[0,400]$. Its least sampled cost is $0.505782$. This finite-grid reading does not certify a continuous-domain optimum or a Gaussian upper bound.

## Triage

### What the settlement shows

1. **Proved, kernel-checked — mechanism and instance.** Private `abs_sin_nat_mul_le` and `one_sub_cos_nat_mul_le` establish the trigonometric dilation. Private `admissible_deriv_defect` and `admissible_defect_properties` transfer it to admissible derivatives and defects. Private `three_point_bound_of_defect`, `uniform_cost_lower` and `approx_error_lower` give $E_{f_1}(1)\ge1153/2304>1/2$. Private `div_one_add_opmono` establishes the witness's matrix operator monotonicity. These are statements on the proof path of `result`, which refutes Conjecture 2. Positive Fourier structure constrains the defect more than the conjectured cost budget allows.

2. **Proved in prose — family and constant barrier.** For $a,c>0$, put $f_a(x)=x/(a+x)$ and $r=c/a$. The resolvent $I-a(aI+A)^{-1}$ and inverse order reversal give matrix operator monotonicity; nonnegativity is immediate on the half-line. The same defect and three-point argument applies. Algebra gives

   $$D_N(f_a,c)=\frac{r^2\bigl(N^2-(4r+3)N-2\bigr)}{(1+r)(1+2r)(1+Nr)}.$$

   Choose a natural $N\ge4r+4$. Then $N^2-(4r+3)N-2=N(N-4r-3)-2\ge N-2>0$. Thus every finite admissible cost exceeds $f_a(c)$ by the uniform positive amount $D_N/(N^3+N+2)$, and so does its infimum. The zero approximant has finite cost because $0\le f_a\le1$, ensuring nonemptiness. At $c=a$, $N=11$, the lower bound is $1153/2304$; division by $f_a(a)=1/2$ forces any valid constant to be at least $1153/1152$. Only $a=c=1$ is kernel-checked in this module; the all-parameter family is this prose proof.

3. **Computed — family formula and consistency readings.** The experiment entry verifies the symbolic formula and anchor values, and the stated finite grids, with `bad= 0`. The positivity claim for all $r>0$ is proved in item 2, not by the grid. The exact anchor values are computed there; the inequalities for admissible costs are kernel-checked only in the instance of item 1.

4. **Open, literature reading — consequences.** Conjectures 1 and 3 concern commutator inequalities and remain open here. The source's implication from Conjecture 2 no longer supplies a proof of them; its converse is not asserted. The source's Gaussian upper estimate $C<1.01975$ survives this refutation.

5. **Open — completeness of the literature screen.** The Farrell full-text reading described under Gap treats Herrera's Corollary 1.3, not Conjecture 2 or $E_f$; it supplies no settlement of this approximation question.

6. **Open — sharp constant and neighbouring targets.** The optimal constant for $x/(1+x)$ lies between $1153/1152$ and the source's upper bound $1.01975$. Its exact value and whether broader classes of approximants attain the commutator constant are not settled. A necessary condition for cost $E_f(c)\le f(c)$ under this finite-cost argument is $D_N(f,c)\le0$ for every natural $N$; this is a prose consequence of the three-point inequality, not a sufficiency theorem. The source's weaker upper constant and the finite-cost formulation survive.

## ASSUMED-UNVERIFIED

The independent implementation readings do not include a new full-text inspection of Farrell's thesis or a new global literature search; those literature results are attributed to the orchestrator and search seat. Later unindexed settlements are outside the recorded searched scope. No infinite-dimensional operator transport, extended-real empty-cost-set bridge, optimal-constant theorem or continuous Gaussian optimization is formalized here.
