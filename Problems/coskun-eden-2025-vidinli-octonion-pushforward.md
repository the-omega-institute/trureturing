---
slug: coskun-eden-2025-vidinli-octonion-pushforward
bibkey: coskuneden2025vidinli
doi: 10.48550/arXiv.2511.09395
url: https://arxiv.org/abs/2511.09395v1
triage: theorem
motivation_gids:
  - D5/S3/HomologicalAlgebra/CoskunEdenVidinliOctonion.result
---

# Coşkun–Eden Remark 5.9: the octonion clause

## Problem

Remark 5.9 of Coşkun–Eden, arXiv:2511.09395v1, asks whether the exceptional
Vidinli algebra $V_7$ has a push-forward description using octonion multiplication.
The affirmative assertion is the existence of real-linear maps
$\nu:V_7\to\mathbb O$ and $\pi:\mathbb O\to V_7$ such that
$a\mathbin{\veebar_7}b=\pi(\nu(a)\nu(b))$ for every $a,b$.
The preregistration is [#20661](https://github.com/the-omega-institute/trureturing/issues/20661).

### Statement echo

`vidinliMul` is the coordinate expression of Definition 5.1, with zero-based
indices in `Fin 7 → ℝ`; index $i$ denotes the paper's coordinate $i+1$.
`claim` quantifies over both arbitrary real-linear maps and every pair of vectors.
Neither map is assumed multiplicative or unital, and no retraction identity is
assumed. `result` proves `¬ claim`.
The octonion carrier, multiplication and multiplicative square norm are reused
from the closed source module `D5/S3/VertexAlgebra/MonsterTwistedOctonionNorm`.
That owner has no frozen state record on the searched dev revision.
The source's higher Cayley–Dickson clause is a separate question.

## Motivation

`D5/S3/HomologicalAlgebra/CoskunEdenVidinliOctonion.result` gives a negative
answer to the octonion clause. Its admission basis is
`open-problem-resolution (#20661; Refuted)`.

## Gap

The literature screen recorded in #20661 examined both source versions,
Elduque–Rández-Ibáñez, arXiv:2601.22839v1, and author, citation, octonion,
compression and rank searches. No settlement was located in that searched
scope. The source's v2 omits the question. The journal version with DOI
10.1142/S0219498827502537 was inaccessible. Literature completeness is
`ASSUMED-UNVERIFIED`.

## Route

The right unit forces $\nu$ injective and $\pi$ surjective, hence
$7+\dim\ker\pi=8$. Let
$K(x)=(0,x_0,x_0,x_1,x_2,x_3,x_4)$. This map is injective and
$e_2\mathbin{\veebar_7}K(x)=0$. The nonzero octonion $\nu(e_2)$ has injective
left multiplication, by the positive-definite multiplicative square norm.
Consequently $T=L_{\nu(e_2)}\circ\nu$ is injective and $T\circ K$ restricts
to an injection $\mathbb R^5\to\ker\pi$. This gives
$5\leq\dim\ker\pi=1$, a contradiction.

## Falsifier

The argument requires the literal product of Definition 5.1, the right unit,
positive-definite multiplicative octonion norm, and real-linearity of both maps.
A model with zero divisors in the ambient algebra does not supply the left
multiplication injection used here.

## Evidence

The settling theorem is `result : ¬ claim`. Its consumed private helpers are
`vidinli_unit`, `oct_zero_mul`, `oct_norm_zero_iff`, `octLeft`,
`octLeft_injective`, `kernelVectors`, `kernelVectors_injective`, and
`vidinli_kills_kernelVectors`. It applies
`MonsterTwistedOctonionNorm.norm_mul`, Mathlib's rank-nullity theorem and
injective-map finrank bound. The axiom closure of every public declaration is
contained in $\{\mathrm{propext},\mathrm{Classical.choice},\mathrm{Quot.sound}\}$.

The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).

The experiment is
[trureturing-experiments@695be153aa31d78a0b5254f2adc967f47a292c3f](https://github.com/the-omega-institute/trureturing-experiments/tree/695be153aa31d78a0b5254f2adc967f47a292c3f/docs/reports/coskun-eden-2025-vidinli-octonion-pushforward),
file `check.py`, SHA-256
`c8888bf942eda9e21e1eb1d3fccb1ddff6ee8002ffed0d3957e7a6aea6992029`.
Running the verified script as
`python3 /Users/auric/.sshx/2660088a9c2c19d17002766b/attempt-1/check.py D5/S3/VertexAlgebra/MonsterTwistedOctonionNorm.lean`
exits 0 with `ALL_CHECKS_OK`. It checks the symbolic V₃ identities of Section
3.1 (3)–(4), the Baez and D5 octonion norm identities in 16 variables, the
D5 two-sided unit, the exact rank and kernel basis of $L_{e_2}$ on $V_7$,
and 20 seeded rational nonzero imaginary vectors in each of $V_3,V_5,V_7,V_9$.
The seed is 20261023. It does not establish a uniform theorem from those samples.

## Triage

| item | status | evidence |
| --- | --- | --- |
| Lemma 1: $\nu$ injective and $\pi$ surjective | proved | Kernel-checked local steps `hν` and `hπ` inside `result`, using `vidinli_unit` and `oct_zero_mul`. |
| Lemma 2: five independent vectors killed by $L_{e_2}$ | proved | Kernel-checked `kernelVectors_injective` and `vidinli_kills_kernelVectors`; no full-kernel classification is asserted as a Lean theorem. |
| Exact rank two and full kernel basis of $L_{e_2}$ | computed | The experiment entry above computes rank 2, kernel dimension 5 and the basis $e_2+e_3,e_4,e_5,e_6,e_7$. |
| Lemma 3 and the negative answer | proved | Kernel-checked `octLeft_injective` and the injection `F`, finrank and contradiction steps inside `result`. |
| V₃ source fidelity and the octonion coordinate conventions | computed | The experiment entry above verifies Section 3.1 (3)–(4), both norm identities and the D5 unit symbolically. |
| Rank-two samples in $V_3,V_5,V_7,V_9$ | computed | The experiment entry above checks exactly 20 seeded nonzero imaginary rational vectors in each dimension. |
| Uniform necessary bound $N\geq 2d-2$ | proved | The dimension argument below assumes an $N$-dimensional real division algebra and the displayed Vidinli product. No general Lean theorem is claimed. |
| Quaternion case $(N,d)=(4,3)$ | computed | The source's Section 3.1 (4) identity is checked symbolically by the experiment entry; $4=2\cdot3-2$. |
| Higher Cayley–Dickson clause | open | Zero divisors remove the nonzero-left-multiplication injection; `result` states only the octonion clause. |
| Literature completeness and inaccessible journal version | open | Literature reading recorded in #20661; `ASSUMED-UNVERIFIED`. |

### What the settlement shows

**Mechanism (proved in this module).** The right unit makes the maps injective
and surjective without multiplicativity assumptions. The ambient octonion
space allows only one kernel dimension for $\pi$, whereas the five displayed
Vidinli directions must inject into it. This is the contradiction in `result`.

**Uniform necessary condition (proved in prose).** For the source's odd-dimensional
Vidinli product with $d\geq3$ and nonzero imaginary $a$, the formula is
$L_a(b)=b_1a+(\omega(a,b)-\langle a,b\rangle)e_1$.
Its image lies in $\operatorname{span}(a,e_1)$. Since $L_a(e_1)=a$ and
$L_a(a)=-\|a\|^2e_1$, its rank is exactly two and its kernel has dimension
$d-2$. A linear push-forward through an $N$-dimensional real division algebra
has injective $\nu$ and surjective $\pi$ by the unit argument. Nonzero left
multiplication makes $L_{\nu(a)}\circ\nu$ injective, so it embeds
$\ker L_a$ into $\ker\pi$. Thus $d-2\leq N-d$, or $N\geq2d-2$.
This is a prose argument, separate from the fixed-dimensional kernel proof.
The quaternion example $N=4,d=3$ attains equality, as verified by the source's
explicit maps and the experiment.

**Neighbouring statements (open).** The higher Cayley–Dickson algebras have zero
divisors, so the division-algebra condition fails and this method supplies no
answer to that clause. The source's established quaternion construction remains
valid. Remark 5.9 presents a question, not a hypothesis used to prove the source's
preceding results; the refutation does not retract those results.

## ASSUMED-UNVERIFIED

Literature-search completeness, the inaccessible journal version, and external
priority remain unverified. The formal result uses the preregistered coordinate
octonion owner. Identification with Baez's octonions is via the real unital
positive-definite composition-algebra classification stated in #20661; that
isomorphism is not separately formalized by this delivery. The experiments
verify the two norm identities, not an explicit algebra isomorphism.
