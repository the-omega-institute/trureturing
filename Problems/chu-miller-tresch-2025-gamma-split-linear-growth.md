---
slug: chu-miller-tresch-2025-gamma-split-linear-growth
bibkey: chumillertresch2025diophantine
doi: 10.48550/arXiv.2512.12681
url: https://arxiv.org/abs/2512.12681v1
triage: theorem
motivation_gids:
  - D5/S3/Arith/Density/ChuMillerTreschGammaSplitGrowth.result
---

# Linear growth for every Gamma-label split

## Problem

Hùng Việt Chu, Steven J. Miller and Garrett Tresch, *Problems Regarding a Pair of Diophantine Equations*, arXiv:2512.12681v1, Section 3.4, p. 11, ask:

> As noted in Remark 2.7, the sequence grows exponentially fast (faster than the Fibonacci sequence). Is there a construction involving a strictly increasing sequence that grows slower than the Fibonacci sequence, or perhaps even like n^k for some k?

The question extends Corollary 2.6 to every prescribed split $p\in[0,1]$. The answer is affirmative. The construction has $-9\le a_n-8n\le15$, so $a_n=8n+O(1)$, and its zero-label count $C_N$ satisfies $0\le pN-C_N<5$.

Preregistration: [#20691](https://github.com/the-omega-institute/trureturing/issues/20691). Source note: `Library/ArithUnits/chumillertresch2025diophantine.md`.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Section 1: the gcd-reduced first equation has a nonnegative integral solution exactly when the label is zero | `Gamma` | Literal natural-number equation, integer division, truncated natural subtraction; complementary branch returns one. The source's exactly-one theorem supplies the interpretation for positive inputs. |
| Corollary 2.6: count the first $N$ pairs of a sequence indexed from zero | `zeroCount` | Inclusive indices $1\le n\le N$ and pair $(a_{n-1},a_n)$. |
| Every split $p\in[0,1]$ | `claim`, binders `p : ℝ`, `0 ≤ p`, `p ≤ 1` | Both endpoints included. |
| A strictly increasing positive integer sequence | `claim`, existential `a : ℕ → ℕ`, strict monotonicity and positivity | Index zero and natural-valued entries. |
| Growth like $n^k$ for some $k$ | Polynomial-bound conjunct of `claim`; `result` chooses exponent one and coefficient 23 | Upper bound for every $n\ge1$. The sharper two-sided linear estimate is private. |
| Limiting zero proportion $p$ | Final conjunct of `claim` and `result` | Real division, natural index tending to infinity. |

The definitions `Gamma`, `zeroCount` and `claim` retain the literal preregistered bodies. The proof uses the existing `D5.S1.Words.Mechanical.lowerMechanicalLetter p 0` schedule; no second definition of that schedule is introduced. The exponent, coefficient and positivity clauses specify the polynomial-growth question without adding a hypothesis on $p$.

## Motivation

The settling node is `D5/S3/Arith/Density/ChuMillerTreschGammaSplitGrowth.result`. Its public conclusion is the full prescribed-split claim. The proof also establishes quantitative growth and discrepancy estimates through consumed private helpers. Linear order suffices for every split.

## Gap

The source construction grows exponentially. The missing ingredient is a concatenable pair of bounded-length chains with opposite constant labels and a common transition edge structure. The literature screen recorded in #20691 found no bounded-growth construction for arbitrary splits in its searched scope; completeness is `ASSUMED-UNVERIFIED`.

## Route

Use $Z=(3,7,17,19,23,43)$ and $O=(3,23,27,29,33,43)$, each translated by $40k$. Their ten edges have polynomial nonnegative-solution certificates and relatively prime endpoints. The exclusivity argument in `exclusive` applies `Nat.Coprime.mul_add_mul_ne_mul` to exclude simultaneous solutions of the two equations. The translated blocks share endpoints, so no uncertified transition edge is added.

The existing floor-increment schedule selects $Z$ when $\lfloor(k+1)p\rfloor-\lfloor kp\rfloor=1$ and $O$ otherwise. For $N=5K+r$, $0\le r<5$, `count_formula` proves

$$C_N=5\lfloor Kp\rfloor+r\bigl(\lfloor(K+1)p\rfloor-\lfloor Kp\rfloor\bigr).$$

`discrepancy` expresses the error as $(5-r)\{Kp\}+r\{(K+1)p\}$, bounded between zero and five. `density` squeezes the ratios between $p-5/N$ and $p$. `result` combines density, positivity, strict increase and the bound $a_n\le23n$ for $n\ge1$.

## Falsifier

A false row certificate, an uncertified transition edge, a prefix count differing from the formula above, or failure of the growth bounds would invalidate this construction. The kernel-checked helpers cover every natural block index and every real split in $[0,1]$; the experiment below supplies separate finite checks of the conventions. It supplies no proof of an unbounded numerical assertion.

## Evidence

Kernel-checked declarations are in `D5/S3/Arith/Density/ChuMillerTreschGammaSplitGrowth.lean`. Only `result` is a public theorem; the three public definitions specify its statement. The axiom closure of every public declaration is contained in `{propext, Classical.choice, Quot.sound}`.

### Experiment

Program and data: [immutable experiment directory](https://github.com/the-omega-institute/trureturing-experiments/tree/9d52d7d7ebb6eed0c13bf1b8bc7d1f641749fe8c/docs/reports/chu-miller-tresch-2025-gamma-split-linear-growth). The script is `check.py`, SHA-256 `24b339e97002aa8c949f24d89790783e7064abf00c18d54925a1c6112b577ddd`. The checked immutable bytes were obtained with `git -C /Users/auric/trureturing-experiments show 9d52d7d7ebb6eed0c13bf1b8bc7d1f641749fe8c:docs/reports/chu-miller-tresch-2025-gamma-split-linear-growth/check.py`. Execution: `uv run --with sympy python /Users/auric/.sshx/720e4aef212a0b5a08770e36/attempt-1/check.py`, exit 0.

Computed results: exactly one equation is solvable for coprime $1\le a,b\le80$; Proposition 2.5 holds for $1\le a\le300$ in its first family and $2\le a\le300$ in its second; the inverse criterion agrees for $1\le a,b\le60$; consecutive labels alternate for $1\le n\le40$. All ten polynomial row identities hold symbolically, and their labels agree for $0\le k\le300$. For each of $p\in\{0,1,1/2,1/3,5/7,\sqrt2-1,\pi-3,0.123456\}$ and $N\le4000$, the script verifies strict increase, the two-sided growth bound, and the discrepancy check (lower tolerance $-10^{-9}$ for floating point). Irrational inputs use floating-point approximations. These are the exact numerical scopes; uniform exact results are supplied by the Lean declarations instead.

### Escape audit

The sole audit target is `D5.S3.Arith.Density.ChuMillerTreschGammaSplitGrowth.result`. The audit is unfinished: [#21309](https://github.com/the-omega-institute/trureturing/issues/21309). The dependent-family model and variation/sensitivity evidence have compiled as described there, but a faithful final typed four-slot registration, complete source reconstruction and binding evidence are missing. No Reg mirror or `declared_validated` registration is claimed.

## Triage

| Item | Status and evidence kind |
| --- | --- |
| Affirmative settlement for every real split, including endpoints | **Proved, kernel-checked:** `result`. |
| Ten arithmetic certificates and exclusivity | **Proved, kernel-checked:** private `z_rows`, `o_rows`, `row_coprime`, `gamma_zero`, `gamma_one`, `exclusive`. |
| Schedule, positivity, strict increase, gaps from 2 to 20 and two-sided linear growth | **Proved, kernel-checked:** private `w_binary`, `sequence_bounds`, `sequence_step`, `sequence_strictMono`. |
| Exact finite-prefix count | **Proved, kernel-checked:** private `count_formula`. |
| Bounded discrepancy and prescribed density | **Proved, kernel-checked:** private `discrepancy`, `density`; public `result`. |
| Source convention and source-example checks | **Computed:** the experiment above, with its stated finite ranges and SHA-256; literal definition fidelity is given in the statement echo. |
| Generalization of finite experiment checks to all indices | **Proved** only for the construction by the named Lean helpers; global source theorem checks beyond the numerical ranges are **open** here. |
| Reuse and mathematical obstruction boundary | The existing floor schedule is reused. No additional frozen owner of the settlement is identified in the repository search. No mathematical obstruction is asserted; exhaustive owner and literature completeness remain **open**. |

### What the settlement shows

**Decisive mechanism — proved, kernel-checked:** `block_edge` and `sequence_edge` certify both within-block and transition edges; `count_formula` turns the selected blocks into an exact floor count. The interval includes $p=0$ and $p=1$ through `w_binary`, `density` and `result`.

**Smallest growth order — proved in prose:** if $a$ is strictly increasing and natural-valued, induction gives $a_n\ge a_0+n$: the successor step uses $a_{n+1}\ge a_n+1$. Thus linear order is the smallest possible order. No optimality assertion is made for the coefficient eight.

**Rational splits — proved in prose:** for $p=r/s$ with $r,s\in\mathbb N$, $0\le r\le s$ and $s>0$, the floor identity $\lfloor(k+s)p\rfloor=\lfloor kp\rfloor+r$ gives a schedule of period $s$. Writing $n=5k+j$, $0\le j<5$, the same block is selected at $k+s$, so $a_{n+5s}=a_n+40s$. This consequence is not a separate Lean declaration.

**Coprimality — proved in prose:** every gap $d=e-c$ in the two blocks divides 40 and has $\gcd(c,d)=1$. Hence $\gcd(40k+c,40k+e)=\gcd(40k+c,d)=1$, including the last edge ending at $40(k+1)+3$.

**Remaining source questions — open:** which interesting splits produce natural sequences, the best possible leading coefficient, and the paper's separate periodicity questions. The argument supplies a new construction for Section 3.4; no modification of the paper's other results or dependency on an unsettled conjecture is asserted.

## ASSUMED-UNVERIFIED

Literature completeness is `ASSUMED-UNVERIFIED`. The screen in #20691 covers arXiv:2512.12681v1, the author-hosted version and publication page, and related arXiv:2309.04488v2, 2509.01781v2 and 2609.08728v1. Beiter's midterm-coefficient paper, Chu (2020), Davala (2023) and Chen et al. (2025) were not read in full. No global originality conclusion follows from this bounded screen. Escape registration remains unfinished under #21309.
