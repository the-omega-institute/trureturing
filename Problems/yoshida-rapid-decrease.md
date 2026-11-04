---
slug: yoshida-rapid-decrease
bibkey: yoshida2010fiskbranden
doi: 10.48550/arXiv.1005.4218
url: https://arxiv.org/abs/1005.4218v1
triage: theorem
motivation_gids:
  - D5/S0/Certificates/YoshidaRapidDecreaseRefutation
---

# Yoshida's rapid-decrease closure question

## Problem

Rintaro Yoshida, *On some questions of Fisk and Brändén*,
[arXiv:1005.4218v1](https://arxiv.org/abs/1005.4218v1), Open Problem 5,
printed page 11, asks:

> Let $f(x)=\sum_{k=0}^{\infty}a_kx^k$ where $\{a_k\}_{k=0}^{\infty}$ is a rapidly decreasing sequence. If $S_r[f(x)]=\sum_{k=0}^{\infty}(a_k^2-a_{k-r}a_{k+r})x^k:=\sum_{k=0}^{\infty}b_kx^k$, is it true that $\{b_k\}_{k=0}^{\infty}$ is a rapidly decreasing sequence?

Definition 29, printed page 10, requires positive terms and one real $\alpha$ with
$\alpha\ge\max\{2,\frac{\sqrt2}{2}(1+\sqrt{1+a_1})\}$ such that
$a_k^2\ge\alpha^2a_{k-1}a_{k+1}$ for every $k\ge1$.
Negative indices are zero-extended, following Definition 8, printed page 3.
The [Library note](../Library/Certificates/yoshida2010fiskbranden.md) carries these locators.
The tier-1 preregistration is [#23414](https://github.com/the-omega-institute/trureturing/issues/23414).

### Statement echo

All declaration names below belong to `D5.S0.Certificates.YoshidaRapidDecreaseRefutation`.

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Positive real sequence indexed by all nonnegative integers | `RapidlyDecreasing` positivity conjunct | Every natural index, including zero; no finite truncation. |
| A single threshold parameter and all positive-index inequalities | `RapidlyDecreasing` existential and universal clauses | The source threshold is literal, with real square roots and real division. |
| $a_j=0$ outside the index domain | Integer conditionals in `RapidlyDecreasing` and `sCoeff` | Zero for negative indices; otherwise `Int.toNat` selects the coefficient. No separate forwarding definition. |
| $b_k=a_k^2-a_{k-r}a_{k+r}$ | `sCoeff` | Subtraction occurs after casting indices to integers. |
| The source's coefficient object and closure question | `claim` | An explicit existence conjunct plus closure for every real coefficient sequence and every natural $r\ge1$, as preregistered. The coefficient representation imposes no convergence condition. |
| Negative answer | `result` | The literal negation of the complete claim; $r=1$ supplies the failure. |

## Motivation

The threshold depends on the first coefficient. Squaring and subtracting adjacent
products can enlarge that threshold beyond the adjacent ratios of the output,
even when every input inequality holds with equality.

## Gap

The bounded source and literature screen in #23414 found no earlier settlement
in the inspected material. It records arXiv, Semantic Scholar, OpenAlex,
MathOverflow/Mathematics Stack Exchange, Zenodo, catalogue, repository and issue
searches. Some endpoints were rate-limited. The journal full text, Yoshida's
dissertation, and the identified Karp and Zhu citing papers were not read.
Search completeness and absence of an earlier settlement are `ASSUMED-UNVERIFIED`.

## Route

Set $a_k=48^k/32^{\binom{k}{2}}$ and $r=1$.
The private lemmas `witness_pos`, `witness_succ` and `witness_adjacent` establish
positivity and $a_{k+1}^2=32a_ka_{k+2}$.
The lemma `witness_rapid` supplies $\alpha=4\sqrt2$ for all positive indices.
The first output coefficients are $b_0=1$, $b_1=2232$, $b_2=5022$.
In `output_not_rapid`, the index-one inequality forces $\alpha^2\le992$,
whereas the output threshold forces $\alpha^2\ge1117+\sqrt{2233}>992$.
The theorem `result` applies that contradiction to the closure conjunct.

## Falsifier

A counterargument to this settlement would have to invalidate the literal
coefficient conventions or one of the all-index input inequalities, or supply
an output parameter satisfying both incompatible bounds above. A finite sample
alone cannot certify the all-index input predicate; `witness_rapid` does so.
The explicit input also satisfies the existence conjunct of `claim`.

## Evidence

The settling declaration is `D5/S0/Certificates/YoshidaRapidDecreaseRefutation.result`.
Its proof and all private supporting lemmas are `bind-only`; the module's
admission basis is `open-problem-resolution (#23414; Refuted)`.
Its only direct import is pinned `Mathlib.Analysis.Real.Sqrt`; there are no D5 imports.

The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).

The exact experiment is
[the experiments directory at `2c0f69d2d9582abff5070716a5f77a84b1601391`](https://github.com/the-omega-institute/trureturing-experiments/tree/2c0f69d2d9582abff5070716a5f77a84b1601391/docs/reports/yoshida-open-problem-5).
Command: `git -C /Users/auric/trureturing-experiments show 2c0f69d2d9582abff5070716a5f77a84b1601391:docs/reports/yoshida-open-problem-5/check.py | python3`
(with shell `pipefail`); exit code 0; final marker `ALL_CHECKS_OK`.
The script's SHA-256 is `a6a02f44eef5a06de6aa6ef0105c08bda4c435c2a294f434f9e97b4ac6ef309e`.

## Triage

1. **Proved, kernel-checked:** the displayed positive all-index sequence satisfies the binding rapid-decrease predicate, while its $S_1$ output does not. Evidence: `witness_pos`, `witness_rapid`, `output_not_rapid`, and `result`. **Proved in prose:** substituting $k=0,1$ in $a_k=48^k/32^{\binom{k}{2}}$ gives $a_0=1$ and $a_1=48$, since $\binom{0}{2}=\binom{1}{2}=0$.
2. **Proved, kernel-checked within `output_not_rapid`:** the failure is the output threshold's dependence on $b_1$. The index-one ratio forces $\alpha^2\le992$, and the threshold forces $\alpha^2\ge1117+\sqrt{2233}$. These are local steps of that private proof, not additional public theorems.
3. **Computed:** the pinned checker verifies the member $q=7,L=49,r=1$ using exact fractions: input positivity for indices $0\ldots15$, $a_1<a_0$, adjacent identities for $k=1\ldots11$, quotient identities for $k=0\ldots9$, output positivity for $k=0\ldots11$, and the index-one ratio $992<b_1/2=1116$. Its symbolic ratio limit is zero. For Example 30 it checks input adjacent identities for $k=1\ldots23$, output positivity for $k=0\ldots23$ and $r=1\ldots7$, and the factor-four inequality for $k=1\ldots19$ and $r=1\ldots7$. Exact SymPy algebra checks the polynomial identity with certificate $u^4+24u^3+196u^2+592u+368$ and its positive constant term. Evidence: the immutable experiment, command, exit code and SHA-256 above. These sampled checks do not establish an infinite-index assertion.
4. **Open in this formalization:** the full $q\ge7,L>0,r\ge1$ family, its entire-series convergence, and its sharp family criterion. The single fixed member already refutes the unchanged coefficient claim. No uniform family or analytic convergence theorem is delivered.
5. **Open:** closure for restricted coefficient classes, the infinite-index assertion for Yoshida's Example 30, and the separate Laguerre–Pólya preservation questions. The finite computation in item 3 does not settle them.

### What the settlement shows

**Proved in this module:** the threshold tied to $b_1$ obstructs closure; the
input's uniform adjacent identity is insufficient to preserve that threshold.

**Proved in prose for this fixed sequence:** output positivity and a uniform
factor lower bound survive. For $k\ge1$, the input identity gives
$b_k=(31/32)a_k^2>0$, while $b_0=1$. At $k=1$ the output adjacent ratio is
$32^2(31/32)=992$; at $k\ge2$ cancellation of the three factors $31/32$
gives ratio $32^2=1024$. Thus all output adjacent ratios are at least $992$.
These formulas explain the surviving fixed-factor inequality; they are not
additional Lean statements. They cannot supply the larger coefficient-dependent
threshold required by Definition 29.

**Open boundary for the source's other questions:** the refutation concerns
Open Problem 5's coefficient closure assertion. It does not negate Example 30
or a Laguerre–Pólya preservation theorem. The latter require their own hypotheses
and proofs; none is inferred from the false closure assertion here.

## ASSUMED-UNVERIFIED

Literature-search completeness and absence of an earlier settlement remain
`ASSUMED-UNVERIFIED`. The journal version and unread citing works listed above
can change the prior-art assessment. Mathematical truth of the compiled
refutation is separate from that assessment. The coefficient representation,
positive natural $r$ and explicit existence conjunct are the conventions of
#23414; no entire-function or Laguerre–Pólya assertion is included in `claim`.
