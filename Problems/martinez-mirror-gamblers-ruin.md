---
slug: martinez-mirror-gamblers-ruin
bibkey: martinez2024mirrorgamblersruin
doi: 10.48550/arXiv.2412.07667
url: https://arxiv.org/abs/2412.07667v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Probability/MartinezMirrorGamblersRuin.result
---

# Martinez's mirror-step gambler's ruin limit

## Problem

L. Martinez, *A symbolic computational approach to the generalized gambler's ruin
problem in one and two dimensions*, arXiv:2412.07667v1, Conjecture 5.1, page 16:

> Consider the generalization of the gambler’s ruin problem when we add a mirror step. If the particle starts at $x=1$, then
> $$\lim_{N\to\infty} f_N^{(p)}(1)=\frac{\sqrt{(p+1)(1-3p+4p^2)}-(1-2p)(p+1)}{2p(p+1)}$$
> whenever we restrict the particle moves by either moving from $x$ to $x-1$ with probability $q_1$, or from $x$ to $x+1$ with probability $p$, or from $x$ to $N-x$ with probability $q_2$ where $q_1=q_2=\frac{1-p}{2}$.

Here $0<p<1$, and $f_N^{(p)}(x)$ is the probability of absorption at $N$.
The [source note](../Library/StatisticalMechanics/martinez2024mirrorgamblersruin.md)
records the versioned locator. The statement and conventions are preregistered
in [#19080](https://github.com/the-omega-institute/trureturing/issues/19080).

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Every real $0<p<1$ | `p : ℝ`, `0 < p`, `p < 1` in `claim` | Full open interval |
| States $0,\ldots,N$ with absorbing endpoints | `f 0 = 0`, `f N = 1` in `IsWinProbability` | Values outside the interval are unrestricted |
| Left step of weight $(1-p)/2$ | First term in `IsWinProbability` | Argument $x-1$ |
| Right step of weight $p$ | Second term in `IsWinProbability` | Argument $x+1$ |
| Mirror step of weight $(1-p)/2$ | Third term in `IsWinProbability` | Argument $N-x$ |
| First-step equation at every interior state | `∀ x, 0 < x → x < N → …` | Coincident destinations add their weights |
| Starts at $x=1$, $N\to\infty$ | `Filter.Tendsto (fun N => f N 1) Filter.atTop …` | Natural-number limit |
| The displayed radical | `limitValue p` | Literal numerator, denominator and positive square root |
| Winning-probability family | `∀ f`, satisfying the recurrence for every $N≥2$ | Uniqueness identifies every such family |

The universal family quantifier introduces no extra restriction on the source's
solution: existence follows from the finite formula, and `harmonic_unique`
proves uniqueness on the interval. The lower bound $N≥2$ ensures the starting
point is interior and removes only finitely many indices from the limit.
Natural subtraction is truncated, and at interior points agrees with integer
subtraction. Conjecture 5.1 assigns $p$ to the right step; the symmetric example
in Section 4 assigns $p$ to the mirror step. The claim uses Conjecture 5.1's
assignment.

## Motivation

The tier-1 external named conjecture is settled by
`D5/S3/Combinatorics/Probability/MartinezMirrorGamblersRuin.result`.
The admission basis is `open-problem-resolution (#19080; Proved)`.
The proof concerns the literal boundary recurrence and its limit.

## Gap

The literature screen recorded in #19080 reads Sections 4 and 5 of the source,
the author-hosted preprint and talk slides, later papers by the author, and
identifier/title/mirror-step searches with OpenAlex and Crossref. It reports no
settlement in that searched scope. Literature completeness is
`ASSUMED-UNVERIFIED`; Semantic Scholar was rate-limited.

## Route

For arbitrary positive left, right and mirror weights $a,b,c$ with $a+b+c=1$,
put

$$
T=\frac{a+b}{ab}-2,\qquad r=\frac{T-\sqrt{T^2-4}}2,\qquad
K_1=1-\frac ar-br,\qquad K_2=1-ar-\frac br,\qquad R=\frac{K_1}c.
$$

The private helper `constants` constructs $r,R$ with $0<r<1$, $R<0$ and

$$
ab r^2-(a+b-2ab)r+ab=0,\qquad
1=\frac ar+br+cR,\qquad R=aRr+\frac{bR}r+c.
$$

Its algebra uses $K_1K_2=c^2$ and $K_1+K_2<0$. The private definition
`solution` is

$$
F_N(x)=\frac{(1-r^x)(1-Rr^{N-x})}{(1-R)(1-r^N)}.
$$

`finite_solution` verifies the two endpoints and the three-destination
recurrence. `harmonic_nonpos` chooses an attained maximum on the finite
interval. The averaging equation at an interior maximizer, together with
$a>0$ and $b,c≥0$, forces its left neighbour to attain the same maximum.
Strong induction reaches a zero boundary. `harmonic_unique` applies this
argument to both differences of two solutions.

`solution_limit` gives $F_N(1)\to(1-r)/(1-R)$. Finally, at
$a=c=(1-p)/2$, $b=p$, `limit_identity` identifies that limit with the radical
in `limitValue`. `result` transfers the limit to every recurrence family.
All these declaration names belong to
`D5.S3.Combinatorics.Probability.MartinezMirrorGamblersRuin`; the helpers
remain private.

## Falsifier

An admissible $p\in(0,1)$ and recurrence family with a different limit would
refute the conjecture. A mismatch in a transition weight, endpoint, radical
branch or quantified family would invalidate the correspondence. Finite
numerical agreement alone cannot establish the universal limit.

## Evidence

`D5.S3.Combinatorics.Probability.MartinezMirrorGamblersRuin.result` proves
`claim`. The axiom closure of every public declaration is contained in
{`propext`, `Classical.choice`, `Quot.sound`}. Only pinned Mathlib modules are
imported; there is no D5 frozen prerequisite or anchor atom. The module is
general (`G`) with `utility: none`.

The public theorem's escape audit is unfinished:
[#19149](https://github.com/the-omega-institute/trureturing/issues/19149).
No Reg mirror or validated registration is claimed. Equality, order, guarded
equality, iff and existential-witness templates do not directly read this
quantified convergence claim. A dependent-family registration still needs
source reconstruction and occurrence ties, an equivalence bridge, an actual
positive-law proof, whole-family variation/sensitivity and observational
dependence evidence.

### Experiment

The independent numerical check is in the
[pinned experiment directory](https://github.com/the-omega-institute/trureturing-experiments/tree/29616f484f91cf715c06c0b73367686d5013270c/docs/reports/martinez-2024-mirror-gamblers-ruin-limit).
Command: `python3 /Users/auric/trureturing-experiments/docs/reports/martinez-2024-mirror-gamblers-ruin-limit/check.py`.
Exit code: 0; result `RESULT PASS`. The script SHA-256 is
`258eacb03afaded6b7ba029c4e3946fae07ebd4c0886ca7d1d38ab790dbaaecb`.
The pinned object exists and its bytes match the executed script.

Computed scope: $p\in\{1/10,1/3,1/2,7/10,9/10\}$, $N\in\{3,7,12,25\}$,
and every interior $x$. The rational linear-system solutions and $F_N(x)$
compare at 40-digit evaluation with maximum reported discrepancy
$2.1\times10^{-171}$. The same five parameters give $0<r<1$, $R<0$,
$|K_1K_2-c^2|<10^{-30}$ and agreement of $(1-r)/(1-R)$ with the conjectured
radical within $10^{-30}$. The script prints $f_{80}(1)$ and the radical to
15 decimal places; for $p=1/3$ both print $0.366025403784439$.
These finite readings supply no proof premise and test only $a=c=(1-p)/2$.

## Triage

### What the settlement shows

| Target item | Status and evidence | Scope |
| --- | --- | --- |
| Finite solution general in $a,b,c$ | Proved, kernel-checked `constants` and `finite_solution` | Positive $a,b,c$ with sum one; every $N>0$ and every interior state |
| Uniqueness general in $a,b,c$ | Proved, kernel-checked `harmonic_unique` | $a>0$, $b,c≥0$, sum one; equality throughout $0,\ldots,N$ |
| Specialization only at the final radical identification | Proved, kernel-checked helper signatures and `limit_identity` | Constants, finite recurrence, uniqueness and geometric limit precede $a=c=(1-p)/2$, $b=p$ |
| Strengthened hypotheses | Proved, kernel-checked `constants`, `finite_solution`, `harmonic_unique` | Positive weights suffice for the finite construction; uniqueness allows zero right or mirror weight |
| Expected-duration half of general-probability future work | Open | No duration recurrence or expectation theorem is supplied |
| Numerical checks | Computed, the pinned experiment entry above | The five $p$ values and listed finite $N$ only |

The decisive mechanism is the reflected geometric ansatz, whose two coefficient
equations close the recurrence, combined with descent from an attained maximum
along the positive left transition. The source's general-probability
winning-probability question has the following consequence, proved in prose
from the checked helpers: `constants` supplies the coefficients,
`finite_solution` supplies a recurrence solution, and `harmonic_unique`
identifies every other solution with it. `solution_limit` then supplies its
limit at $x=1$. This composition holds for every positive $a,b,c$ summing to
one; no extra public theorem or separate named-problem settlement is asserted.
The expected-duration question is unchanged. The source's finite-interval
calculations retain their hypotheses; the conjectured infinite-interval value
is established for every $0<p<1$.

## ASSUMED-UNVERIFIED

Completeness of the literature census beyond the bounded source, author-paper,
OpenAlex, Crossref and identifier searches recorded in #19080 is
`ASSUMED-UNVERIFIED`. The screen does not establish that no inaccessible or
independently published settlement exists. Source correspondence and semantic
proof-shape classifications require review; kernel checking establishes the
formal statements and their axiom closure.
