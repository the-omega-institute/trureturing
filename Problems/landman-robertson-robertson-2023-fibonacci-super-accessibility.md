---
slug: landman-robertson-robertson-2023-fibonacci-super-accessibility
bibkey: landman2023fibonaccisuperaccessibility
doi: 10.2140/moscow.2023.12.181
url: https://math.colgate.edu/~aaron/pap/moreDoAFinal.pdf
triage: theorem
motivation_gids:
  - D5/S3/Arith/Additive/FibonacciSuperAccessibility.result
---

# The Fibonacci numbers are not 2-super-accessible

## Problem

Landman, Robertson and Robertson, *Ramsey properties for integer sequences with restricted gaps*, Moscow Journal of Combinatorics and Number Theory 12(3), 181–195, Section 5, question 3, ask:

> Is the set of Fibonacci numbers 2-super-accessible? We know it is 2-accessible but that it is not 2-large.

The [source note](../Library/Certificates/landman2023fibonaccisuperaccessibility.md) gives the definitions and locators. The external named question and literal Lean conventions are in [#16039](https://github.com/the-omega-institute/trureturing/issues/16039).

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| The Fibonacci set $F=\{f_n\}_{n\ge1}$ | `fibSet` | Membership is a positive-index Fibonacci value; repeated values do not change a set. |
| A $k$-term $S$-ap has positive start and gap in $S$ | `HasAP S A k` | Every index below $k$ belongs to the color class $A$. |
| A positive increasing $S$-diffsequence has successive differences in $S$ | `HasDiffSeq S A k` | The positivity, strict inequalities, difference memberships and all $k$ color memberships are retained. |
| Every $r$-coloring of the positive integers, with literal colors $1,\ldots,r$ | `SuperAccessible r S` | The total natural-valued function is constrained only on positive inputs. Its value at zero is irrelevant. |
| Arbitrarily long color-1 $S$-aps, or arbitrarily long color-$j$ $S$-diffsequences for one $2\le j\le r$ | The disjunction and existential in `SuperAccessible` | The color $j$ is chosen before the length, exactly as in Definition 14. |
| The question for $r=2$ and $S=F$ | `claim` | The literal definitions above are used. |
| A negative answer | `result : ¬ claim` | One coloring violates both alternatives. |

## Motivation

The settling declaration is `D5/S3/Arith/Additive/FibonacciSuperAccessibility.result`. Put

$$\alpha=\frac{47+\sqrt5}{58},\qquad
c(n)=\begin{cases}2&\{\alpha n\}<1/16,\\1&\text{otherwise}.\end{cases}$$

The public theorems `no_color_one_ap` and `no_color_two_diffseq` exclude a 42-term color-1 $F$-ap and a three-term color-2 $F$-diffsequence. Their common coloring refutes 2-super-accessibility. [Wesley's note](../Library/Certificates/wesley2026fibonaccimodulus29.md) supplies the published modulus-29 parameter.

## Gap

Bounded monochromatic diffsequences in color 2 do not force arbitrarily long restricted-gap arithmetic progressions in color 1. The same obstruction holds when color 2 meets every block of 33 consecutive positive integers, as proved below in prose. The claim about all colorings attaining the pair $(41,2)$ is not settled.

## Route

Let $\psi=(1-\sqrt5)/2$ and $r_n=(23f_n+f_{n+1})\bmod29$. The block

$$ (1,24,25,20,16,7,23) $$

is indexed by $n\bmod7$, starting at $n=0$. The consumed private theorem `residue_block` proves this identity for every natural index. The Fibonacci identity in `alpha_fib` and fractional-part calculation in `phase_fib` give

$$\{\alpha f_n\}=\frac{r_n-\psi^n}{29}\quad(n\ge1).$$

The theorem `phase_fib_bounds` proves $1/32<\{\alpha f_n\}<26/29$. The no-wrap addition theorem of `GoldenArcFirstReturnCore`, used through `fract_no_wrap`, makes two successive Fibonacci steps from color 2 increase phase by more than $1/16$. This is incompatible with the color-2 window.

For color 1, `uniform_hitting` constructs a coprime-grid representative and controls its perturbation: if $\delta=p/q+\varepsilon$ with coprime numerator and denominator and

$$\frac1q+(q-1)|\varepsilon|<w<1,$$

then every starting phase has a hit in $[0,w)$ among its first $q$ steps. The theorem `large_gap_hit` applies this with $q=29$ for Fibonacci indices at least 8. The six small-gap certificates in `small_gap_hit` cover $d\in\{1,2,3,5,8,13\}$ with denominators at most 42. The theorem `fib_gap_hit` combines both ranges.

## Falsifier

A color-1 42-term $F$-ap or a color-2 three-term $F$-diffsequence for this exact coloring would contradict its corresponding public theorem. A finite search with no such pattern is only a consistency check; it does not prove the universal avoidance statements. A different coloring with smaller avoidance bounds would inform optimality without contradicting this settlement.

## Evidence

The Lean module is [FibonacciSuperAccessibility](../D5/S3/Arith/Additive/FibonacciSuperAccessibility.lean), with its [Scribe projection](../Blueprint/D5/S3/Arith/Additive/FibonacciSuperAccessibility.md). The module's admission basis is `open-problem-resolution (#16039; Refuted)` and its utility is a certified instance refuting `claim`. Its designated `result` is exempt from four-slot escape registration. The two avoidance theorems and the published owner `D5/S1/Words/ReturnWords/GoldenArcFirstReturnCore.fract_add_displacement_of_no_wrap` have unfinished escape audits in [#16300](https://github.com/the-omega-institute/trureturing/issues/16300); this issue is not registration evidence.

The numerical check is the [experiment directory at commit ffbb05865f67b12df54a9c275251218090d024b2](https://github.com/the-omega-institute/trureturing-experiments/tree/ffbb05865f67b12df54a9c275251218090d024b2/docs/reports/landman-robertson-robertson-2023-fibonacci-super-accessibility/). Executing that commit's `check.py` with argument `2000000` (`python3 check.py 2000000`) exits 0. The implementation seat executed the pinned Git blob with the equivalent command `git show ffbb05865f67b12df54a9c275251218090d024b2:docs/reports/landman-robertson-robertson-2023-fibonacci-super-accessibility/check.py | python3 - 2000000` in the experiments clone. Its SHA-256 is `b0b1b6346c608b56fcf50f720145154e7f36609fc143acab287c7dd2f6a66cad`. The tested scope is $1\le n\le2\cdot10^6$ and all 30 positive Fibonacci gaps in that range. It computes 125001 color-2 points, maximum color-2 $F$-diffsequence length 2, maximum color-1 $F$-ap length 41 (gap 3), maximum consecutive color-1 run 19, and residues $(1,24,25,20,16,7,23,1,24)$ for indices 0 through 8, with zero failed checks. These finite maxima make no assertion about all colorings.

## Triage

### What the settlement shows

| Target item | Status and evidence kind | Result and boundary |
| --- | --- | --- |
| Phase mechanism | Proved; kernel-checked `phase_fib`, `residue_block`, `phase_fib_bounds` | Every positive-index Fibonacci increment has phase strictly between $1/32$ and $26/29$; the residue index starts at zero. |
| Three-term color-2 obstruction | Proved; kernel-checked `color_two_step`, `no_color_two_diffseq` | The window has width $1/16$, less than the sum of two strict minimal increments, and Fibonacci steps from the window do not wrap. |
| Long color-1 obstruction | Proved; kernel-checked `uniform_hitting`, `large_gap_hit`, `small_gap_hit`, `fib_gap_hit`, `no_color_one_ap` | Modulus 29 covers indices $n\ge8$; the six exact certificates cover the remaining gaps; every 42-term $F$-ap hits color 2. |
| Optimality over all colorings | Open | Whether $(41,2)$ is optimal is not determined. |
| Source question 4, degree of accessibility | Proved; literature reading of Wesley and the source | Wesley proves that $F$ is not 3-accessible; together with the source's known 2-accessibility this gives $\operatorname{doa}(F)=2$. This is not a theorem of this Lean module. |
| Other $(r,t)$-accessibility questions | Open | No general classification for other $r,t$ is asserted. |
| Failure of extraction from bounded color-2 diffsequences to long color-1 $F$-aps | Proved; kernel-checked `no_color_two_diffseq`, `no_color_one_ap` | This one coloring has neither unbounded family. |
| Bounded gaps of color 2 | Proved in prose below | Every 33 consecutive positive integers meet color 2. The public Lean theorem only exports the weaker 42-term obstruction. |
| Longest observed consecutive color-1 run | Computed; pinned experiment in Evidence | The maximum is 19 on $1\le n\le2\cdot10^6$. No infinite-search claim is inferred. |
| Finite experiment readings | Computed; pinned experiment in Evidence | The diffsequence maximum 2, $F$-ap maximum 41, run maximum 19 and index-0 residue block have exactly the scope stated there. |

For the bounded-gap claim, the rational bracket proved by `alpha_bracket` implies

$$\left|\alpha-\frac{28}{33}\right|\le\frac{6817}{16500000}=:E.$$

Since $\gcd(28,33)=1$ and

$$\frac1{33}+32E=\frac{22442}{515625}<\frac1{16},$$

the coprime-grid hitting argument above, with $q=33$ and $t=\alpha x$, supplies $0\le j<33$ with $\{\alpha(x+j)\}<1/16$ for every positive integer $x$. Thus every such block contains color 2. This is a mathematical derivation from the $d=1$ certificate, not a separately exported kernel-checked 33-term theorem.

The nearest surviving source statements are that $F$ is 2-accessible and is not 2-large. They are literature results, consistent with this refutation of super-accessibility. No theorem elsewhere in the source that does not assume the open question is invalidated by its negative answer; no source theorem depending on a positive answer is asserted here.

## ASSUMED-UNVERIFIED

Optimality over all colorings and the stated other $(r,t)$ questions remain open. The three escape registrations named in Evidence are unfinished. The literature attribution $\operatorname{doa}(F)=2$ is separate from the Lean axiom closure and is not claimed as a Lean result.
