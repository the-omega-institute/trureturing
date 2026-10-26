---
slug: bors-panario-wang-2023-arithmetic-complexity-question-6-3-1
bibkey: borspanariowang2023cyclotomic
doi: 10.4171/MEMS/23
url: https://arxiv.org/abs/2304.00181v1
triage: theorem
motivation_gids:
  - D5/S3/Arith/Congruence/BorsPanarioWangArithmeticComplexity
---

# Arithmetic complexity of singleton partitions

## Problem

Alexander Bors, Daniel Panario and Qiang Wang, *Functional graphs of generalized
cyclotomic mappings of finite fields*, arXiv:2304.00181v1, Question 6.3.1
(arXiv page 189; published memoir page 224):

> Is it true that lim inf_{m→∞} AC(T_m)/(log² m/log log m) > 0?

Here $T_m$ is the partition of $\mathbb Z/m\mathbb Z$ into singletons and
$\mathrm{AC}(T_m)$ is the least number of congruences with positive moduli
dividing $m$ whose truth values separate all residues. The source is documented
in [the Library note](../Library/Factorization/borspanariowang2023cyclotomic.md).
The mathematical preregistration is [#19381](https://github.com/the-omega-institute/trureturing/issues/19381).

### Statement echo

| Source clause | Formal counterpart | Correspondence |
| --- | --- | --- |
| $x\equiv b\pmod a$, $a\ge1$, $a\mid m$ | `MCongruence` and `MCongruence.Holds` | Positive natural modulus, integer residue, and `Int.ModEq`; positive natural and integer moduli describe the same tests. |
| Standard representatives $0,\ldots,m-1$ | Natural representatives with bounds in `SpansTrivial` | Equality of all test truth values forces equality of representatives. |
| $K$ congruences span the singleton partition | `Fin K` family in `SpansTrivial` | Each possible sign system is a truth vector; each nonempty block has one representative. |
| Smallest admissible $K\in\mathbb N_0$ | `acTrivial` | The natural infimum of separating-family sizes; the set is nonempty for $m>0$. |
| $\liminf_{m\to\infty}\mathrm{AC}(T_m)/(\log^2m/\log\log m)>0$ | `claim`, proved by `result` | Natural index at infinity, real natural logarithms and real division, with the ratio embedded in `EReal`. |

The result has no hypotheses. Values at $m=0,1$ use the total Lean operations;
changing a finite initial segment does not change the lower limit at infinity.

## Motivation

The source's Remark 3.3.6 gives the upper bound
$\mathrm{AC}(T_m)\le\sum_{p\mid m}(p^{v_p(m)}-1)$.
For primorial moduli this has order $\log^2m/\log\log m$.
Question 6.3.1 asks for a matching positive uniform lower order.

## Gap

The missing relation is a charge bound for a family that separates the residues,
rather than an estimate for prime powers alone. A test can separate a prime-order
fibre only when its modulus contains the full corresponding prime power.

## Route

Write $q_p=p^{v_p(m)}$. For each prime $p\mid m$, remove all residues satisfying
at least one test whose modulus contains $q_p$. On the remaining set, reduction
modulo $m/p$ is injective: every other test is constant on a fibre, and separation
then forces equality. The private theorem `per_prime_count` proves the resulting
cardinality inequality. The private theorems `per_prime_charge` and `charge_le`
convert it to prime-power totient charges and bound each test's total charge by
one. The private theorem `counting_lemma` concludes
$\sum_{p\mid m}\varphi(q_p)\le K$ for every separating family of size $K$.

The private theorem `small_log_bound` uses the imported Mathlib declarations
`Chebyshev.psi_le_const_mul_self` and `Chebyshev.psi_eq_log_lcmUpto` in its proof.
Splitting the prime powers at $y=\log m/16$ yields the private theorem
`logarithm_bound`. Together with the counting bound, `ratio_bound_of_log` proves
$\mathrm{AC}(T_m)/(\log^2m/\log\log m)\ge1/64$ whenever $\log m\ge64$.
The private theorem `eventual_ratio_bound` supplies the threshold
$\lceil\exp(64)\rceil$. The public theorem `result` uses the imported Mathlib
`Filter.le_liminf_of_le` to prove the exact affirmative proposition `claim`.
All private names here belong to
`D5.S3.Arith.Congruence.BorsPanarioWangArithmeticComplexity`.

## Falsifier

A refutation of the formal settlement would require a failure of `result` under
Lean kernel checking or a mismatch between the literal source definitions and
the displayed statement echo. A finite numerical test does not establish the
uniform asymptotic assertion.

## Evidence

The settling declaration is
`D5.S3.Arith.Congruence.BorsPanarioWangArithmeticComplexity.result`, in
[D5](../D5/S3/Arith/Congruence/BorsPanarioWangArithmeticComplexity.lean), with its
[Blueprint](../Blueprint/D5/S3/Arith/Congruence/BorsPanarioWangArithmeticComplexity.md).
Its admission basis is `open-problem-resolution (#19381; Proved)`.
Its axiom closure is contained in
$\{\mathtt{propext},\mathtt{Classical.choice},\mathtt{Quot.sound}\}$.
The escape audit of the public `result` is unfinished under
[#19486](https://github.com/the-omega-institute/trureturing/issues/19486);
no faithful compiled four-slot registration is claimed.

### Experiment

[The experiment directory at commit `01acb007894137fb26064d768b19cf90def70263`](https://github.com/the-omega-institute/trureturing-experiments/tree/01acb007894137fb26064d768b19cf90def70263/docs/reports/bors-panario-wang-2023-arithmetic-complexity-question-6-3-1)
contains `check.py`, SHA-256
`81f847ad8c3eb386886fb4299fa073cbf66a6b3e62affc918a1917d4460747ed`.
The implementation-seat command
`python3 /Users/auric/.sshx/a2c2a6600404788afc9177b0/attempt-1/experiment-check.py`
runs the exact Git blob from that commit; exit code 0, `RESULT PASS`.
It enumerates congruence truth vectors for $2\le m\le30$, with a cap of
$3{,}000{,}000$ families per search.

Computed: there is no separating family of size $\sum\varphi(q_p)-1$ for
$m\in\{2,\ldots,21,23,29\}$. The checks for $m=22,24,25,26,27,28,30$ exceed
the cap and are excluded. Exact minima are computed only for
$m\in\{2,\ldots,15,17,19,23,29\}$; all equal $\sum(q_p-1)$.
The exact minima for $m=16,18,20,21$ are not computed by this bounded search.
For primorials with $5\le K\le200$, the script computes the ratios
$\sum\varphi(q_p)/(\log^2m/\log\log m)$ and checks that their minimum exceeds
$0.3$. At $K=5,50,100,200$ the rounded ratios are respectively
$0.7849,0.6134,0.5848,0.5654$. These are finite computations.

## Triage

### What the settlement shows

- **Proved in Lean:** Question 6.3.1 has an affirmative answer (`result`). The
  decisive uniform estimate is the private `ratio_bound_of_log`, with constant
  $1/64$ for $\log m\ge64$, and `eventual_ratio_bound`.
- **Proved in Lean:** the fibre-complement injection and weighted charge mechanism
  are `per_prime_count`, `per_prime_charge`, `charge_le` and `counting_lemma`.
  The last theorem states $\sum\varphi(q_p)\le K$ for every separating family
  for $m\ne0$, without a large-$m$ restriction.
- **Proved in prose:** $\mathrm{AC}(T_m)\ge\sum\varphi(q_p)$ for every $m>0$.
  The private `spanning_nonempty` establishes a nonempty set of family sizes.
  Its least element is therefore attained; applying `counting_lemma` to a
  minimizing family gives this inequality. This exact AC inequality is not
  a separately published Lean theorem.
- **Proved in prose:** if $m>0$ is squarefree, then
  $\mathrm{AC}(T_m)=\sum_{p\mid m}(p-1)$. Indeed $q_p=p$, so the preceding
  lower bound equals the source's Remark 3.3.6 upper bound. This is a consequence
  of the paper's upper bound and the proved separation argument, not a new Lean
  declaration. For $m=1$ both sums are empty and the zero-test family separates
  its single residue.
- **Computed:** the exact values and finite primorial ratios have exactly the
  scope, command, exit code and checksum stated in the experiment entry.
  In particular $\mathrm{AC}(T_4)=3$, $\mathrm{AC}(T_8)=7$ and
  $\mathrm{AC}(T_9)=8$ are computed exact values, not claims of exact-value
  Lean theorems.
- **Open:** the stronger formula
  $\mathrm{AC}(T_m)=\sum_{p\mid m}(p^{v_p(m)}-1)$ for every $m>0$.
  The computed examples support it, but this settlement proves neither it
  nor sharpness of the constant $1/64$. No additional public theorem is asserted.
- **Literature reading:** the cited source upper bound remains applicable, and
  combined with the affirmative answer fixes the lower order asked for in
  Question 6.3.1. No new conclusion about unrelated source results is asserted.
- **Search boundary:** unsuccessful or heartbeat-limited `exact?` searches do
  not certify absence of an owner. Named applicable Mathlib owners are used in
  the proofs. Completeness of the literature and third-party-library screen
  remains `ASSUMED-UNVERIFIED`.

## ASSUMED-UNVERIFIED

The literature screen recorded in #19381 covers arXiv v1, the published question,
excerpts of arXiv:2609.30191 and Qiang Wang's publication list. Wang's 2025 survey
and normal-bases paper, and the Bors–Glasby paper, were not read in full.
Chebyshev and Landau were screened for the separation lemma; the search does not
establish a complete prior-art inventory. No global Lean-ecosystem absence
certificate is claimed. A mathematical proof within the declared source model
does not certify completeness of that literature search.
