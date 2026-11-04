---
slug: iosue-mooney-ehrenberg-gorshkov-2024-projective-toric-design-subgroup-conjecture
bibkey: iosuemooneyehrenberggorshkov2024toric
doi: 10.22331/q-2024-12-03-1546
url: https://arxiv.org/abs/2311.13479v3
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Measurements/ProjectiveToricDesignNonGroup.result
---

# A projective toric two-design satisfying the MUB overlap condition need not be a subgroup

## Problem

J. T. Iosue, T. C. Mooney, A. Ehrenberg and A. V. Gorshkov, *Projective toric designs, quantum state designs, and mutually unbiased bases*, Quantum 8, 1546 (2024), arXiv:2311.13479v3, Section 4.3, Conjecture 4.9, `main.tex` lines 786–788, state the following (mathematical delimiters and the absolute-value macro rendered; the equation reference retained literally):

> Let $d$ be any dimension and let $X$ be a $P(T^d)$ $2$-design of size $|X| = d^2$. If $X$ is not a subgroup of $P(T^d)$, then $X$ does not satisfy `\cref{eq:toric-angle}`.

Here $T=\mathbb R/(2\pi\mathbb Z)$ and $P(T^d)=T^d/T$, with the quotient taken by the diagonal circle. The referenced overlap condition is, in `main.tex` lines 654–658,

$\displaystyle \forall\phi\ne\theta\in X:\quad \left|\sum_{j=1}^d e^{i(\phi_j-\theta_j)}\right|^2\in\{0,d\}.$

Use the source's representatives with first coordinate zero. For a finite uniformly weighted set, the second-design condition in `main.tex` lines 198–206 is

$\displaystyle \sum_{\phi\in X}e^{i(\phi_{a_1}+\phi_{a_2}-\phi_{b_1}-\phi_{b_2})}=\begin{cases}|X|&\text{if }\{\!\{a_1,a_2\}\!\}=\{\!\{b_1,b_2\}\!\},\\0&\text{otherwise},\end{cases}$

for every four coordinate indices. This is the normalized moment equation multiplied by $|X|$.

Issue [#26419](https://github.com/the-omega-institute/trureturing/issues/26419) fixes the reading `claim`: for every positive natural number $d$ and finite $X\subset T^d$ with zero first coordinates, cardinality $d^2$, the second-design condition, the overlap condition, and $0\in X$, there exists an additive subgroup of $T^d$ whose carrier is exactly $X$. The added identity hypothesis weakens the source's universal assertion. Even this weaker assertion is refuted.

The source and its encoding are described in [the literature note](../Library/FiniteGeometry/iosuemooneyehrenberggorshkov2024toric.md).

## Motivation

Iosue, Mooney, Ehrenberg and Gorshkov (2024), arXiv:2311.13479v3, `main.tex` lines 652–678, relate complete sets of mutually unbiased bases (MUBs) in dimension $d$ to uniformly weighted projective toric $2$-designs of size $d^2$ satisfying the overlap condition. The conjecture would reduce the admissible designs to subgroups. Their proposed consequence at line 791 combines this restriction with their dimension-six group-design exclusion to obtain nonexistence of complete MUBs in dimension six. Whether overlap and moment constraints force additive closure is therefore the substantive issue.

## Gap

The literature check before any Lean is recorded in #26419:

- The v3 source states Conjecture 4.9 explicitly.
- The reported survey of 13 citing works found no proof or refutation, including D. McNulty and S. Weigert's review, arXiv:2410.23997v2.
- The recorded antecedents include K. Abdukhalikov's symplectic-spread and planar-function constructions, arXiv:1306.3478v3, and W. M. Kantor's spread constructions; the recorded searches found no explicit settlement of this projective-toric subgroup conjecture.
- The preregistration records no existing repository treatment of the source problem.

`not-found-in-searched-scope`. These are bounded, attributed literature readings, not an exhaustive priority claim.

## Route

All lemma names below refer to the settlement module. Put $V=\mathbb F_3^3$ and $\chi=\operatorname{ZMod.stdAddChar}$. The coordinate equivalence `coord` identifies $\mathrm{Fin}\,27$ with $V$, and `coord_zero` sends its zero coordinate to the zero vector. The additive angle map `phase_map` is injective (`phase_injective`) and has complex exponential $\chi$ (`phase_character`).

1. **The fixed matrix family.** `matrices_symmetric` gives symmetry of each of the 27 listed matrices $M_i$. For $i,j\in\mathrm{Fin}\,27$ with $i\ne j$, `spread` gives $\det(M_i-M_j)\ne0$. `matrices_not_add` states that $M_i\ne M_1+M_3$ for every listed index $i$. These finite statements use kernel reduction.
2. **The phases and overlaps.** Define $q_{M,b}(x)=x^{\mathsf T}Mx+b\cdot x$ for $M\in\operatorname{Mat}_{3\times3}(\mathbb F_3)$ and $b,x\in V$, and let $X$ consist of the angle functions $\phi_{i,b}(x)=\operatorname{phase\_map}(q_{M_i,b}(x))$. For every $w\in V$, `character_orthogonality` gives $\sum_x\chi(w\cdot x)=27$ when $w=0$ and zero otherwise. For a symmetric $M$ with $\det M\ne0$ and any $b\in V$, `quadratic_energy` gives $|\sum_x\chi(q_{M,b}(x))|^2=27$. Its shift identity `polynomial_shift` requires symmetry of $M$ and applies to every $b,h,y\in V$. Consequently `exponent_overlap`, for distinct parameter pairs $(i,b)\ne(k,c)$, gives squared overlap zero or 27: equal matrix indices leave a nonzero linear character, while distinct indices give a symmetric invertible difference matrix.
3. **The second moment.** For every nonzero $g\in V$, `spread_evaluation` makes $i\mapsto M_i g$ bijective. For symmetric $M$ and $a_1+a_2=b_1+b_2$, `quadratic_rectangle` identifies the quadratic difference with $2(a_1-b_1)^{\mathsf T}M(a_1-b_2)$. `exponent_moment` applies to every $a_1,a_2,b_1,b_2\in V$: equal index multisets give the double sum 729; otherwise summing over the linear parameter gives zero unless $a_1+a_2=b_1+b_2$. Under that equality and unequal multisets, both $a_1-b_1$ and $a_1-b_2$ are nonzero, so `spread_evaluation` and `character_orthogonality` give zero also in the remaining case.
4. **The finite design.** `point_injective` establishes that the parameter pairs give distinct angle functions. `counterexample_anchored`, `counterexample_card`, `counterexample_design`, `counterexample_overlap` and `counterexample_zero` establish, for this fixed $X$ in dimension 27, zero first coordinates, cardinality $729=27^2$, the second-design condition, the overlap condition and membership of zero, respectively.
5. **Failure of closure.** For symmetric matrices $A,B$, vectors $b,c\in V$, and equality $q_{A,b}(x)=q_{B,c}(x)$ for every $x\in V$, `polynomial_unique` gives $A=B$ and $b=c$. If an additive subgroup had carrier $X$, it would contain $\phi_{1,0}+\phi_{3,0}$. Injectivity of `phase_map` and `polynomial_unique`, applied to the symmetric matrices $M_i$ and $M_1+M_3$, would force $M_i=M_1+M_3$ for some $i$, contradicting `matrices_not_add`. This is `counterexample_not_group`. Applying `claim` at $d=27$ to this fixed $X$ gives the contradiction in `result`.

## Falsifier

A mismatch between the representative slice, the design equation, the overlap normalization or the subgroup conclusion would invalidate the connection to the source. The module uses `Real.Angle` for $T$, `Real.Angle.toCircle` for the unit complex exponential, and four unrestricted coordinate indices for `design2`. Equality of the two index multisets is encoded by the two possible pairings, including repeated indices.

The predicates `design2` and `mubOverlap` alone impose neither positivity nor anchoring. Those hypotheses occur explicitly in `claim`, together with $|X|=d^2$ and $0\in X$. Positive $d$ makes $X$ nonempty, so multiplication of the normalized moment equation by its cardinality is reversible. The first-zero representative slice is an additive copy of $P(T^d)$, so an additive subgroup with carrier $X$ in $T^d$ expresses the source's subgroup condition. The counterexample contains zero; translating a subgroup away from zero cannot account for it.

## Evidence

The canonical source is `D5/S3/Quantum/Measurements/ProjectiveToricDesignNonGroup.lean`.

- **Proof.** It proves `result : ¬ claim`; the scratch import checks the compiled types of `claim`, `design2`, `mubOverlap` and `result`.
- **Axioms.** `#print axioms` on `result` reports only `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom. The source scan for these three constructs has no matches.
- **Escape registrations.** `result` is the designated refutation result of the `utility` header and is exempt. The module has no other public theorem.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Measurements/ProjectiveToricDesignNonGroup.lean.json`.

Declaration statements:

- `result`: `sha256:a54823e3561f36a30a527704021df129db51e871a1263efbd92cb573f6ea170c`;
- `claim`: `sha256:0c6a470ce3334320b4be4abb7dbf9421383dcc4b114f3797dc161edad5811e48`.

## Triage

Tier 1 conjecture of a 2024 Quantum paper, preregistered in issue #26419 before any Lean.
`theorem`; resolution `refuted`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2. The refutation is a certified instance with basis `refutes`. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** it is false that, for every positive natural number $d$ and every finite $X\subset T^d$, zero first coordinates, $|X|=d^2$, the second-design condition, the overlap condition and $0\in X$ together imply the existence of an additive subgroup of $T^d$ whose carrier is $X$.

**Computed, not formalized:** None.

**Argued, not formalized.**

- *Mechanism.* Pairwise nonsingular differences and closure under addition are different constraints. For the fixed family, `spread` supplies nonsingularity when $i\ne j$, while `matrices_not_add` excludes $M_1+M_3$ from the entire family. The character calculations in the route use the former without requiring the latter. Thus overlap and second moments can coexist with a failure of additive closure, even with the identity present.
- *A sufficient repair within the quadratic construction.* Let $\mathcal S$ be any additively closed set of symmetric $3\times3$ matrices over $\mathbb F_3$ containing zero, and include every linear parameter $b\in V$. The sum of the phase functions for $(M,b)$ and $(N,c)$ is the phase function for $(M+N,b+c)$, by additivity of `phase_map`. Zero is present, and the additive inverse is the phase function for $(2M,2b)$ because the characteristic is three. Hence this additional parameter-closure hypothesis suffices for a subgroup in this construction; no design or spread assumption is needed for this argument.
- *Cosets and translations.* A coset $a+H$ containing zero equals $H$, since $0=a+h$ implies $a\in H$. The non-group identity-containing design therefore cannot be a coset either. A fixed translation preserves overlaps by cancellation and multiplies each moment by a unit complex factor; the factor is one for equal index multisets, and the other moments remain zero. Removing translation-only examples is consequently useful but does not repair the conjecture.
- *Anchoring remains a separate question.* Refuting the assertion for an individual phase design does not refute the weaker assertion that each complete MUB set admits some choice of anchoring giving a group design. That existential choice is not a conclusion of `result` and remains open here.
- *Effect on the source.* The proposed deduction at `main.tex` line 791 cannot use Conjecture 4.9 as a true premise. The dimension-27 counterexample does not determine the existence of complete MUBs in dimension six, nor settle the conjectures restricted to non-prime-power dimensions at lines 765–781. The MUB/design correspondence at lines 652–678 and the dimension-six group-design exclusion at lines 743–759 do not rely on Conjecture 4.9; their statements are not refuted by this counterexample, and their proofs or computations are not certified by `result`.

## ASSUMED-UNVERIFIED

The literature check is bounded by #26419 and the source material identified above; it does not establish exhaustive worldwide novelty or priority. The reported 13-paper citation survey, the review quotation, the antecedent-literature searches, the latest-version claims and the web-search coverage in that issue were not independently reproduced. The source's dimension-six exhaustive search was read as a reported result, not rerun.

The identification of the explicit matrices with an inverse Albert spread is not a Lean theorem; the module states the matrices directly. All statements in "Argued, not formalized" are outside the type of `result`. The correspondence between the source's projective quotient and the chosen representative slice is a mathematical interpretation, not a separately formalized quotient equivalence in this module. No extension to other dimensions, claim about an alternative anchoring of the resulting MUBs, or resolution of the non-prime-power and dimension-six questions is asserted.
