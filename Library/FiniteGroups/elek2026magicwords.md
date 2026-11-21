---
bibkey: elek2026magicwords
authors: Balázs Elek
year: 2026
title: Hypercube Richardson varieties from magic words
doi: 10.48550/arXiv.2610.22730
url: https://arxiv.org/abs/2610.22730v1
claim: "Conjecture 3.3 asks whether the Boolean Bruhat intervals are exactly the intervals with a magic word."
strata_touched:
  - D5/S3/FiniteGroups/CoxeterMagic/ElekMagicWordConverseRefutation
license: arXiv perpetual non-exclusive license
triage: anchor
---

# Magic words and Boolean Bruhat intervals

Conjecture 3.3 reads:

> A Bruhat interval $[v,w]$ is a hypercube if and only if there exists a magic word $Q$ for $[v,w]$.

The setting in §2.1 starts with a Kac–Moody group and its Weyl group. The
specialization to symmetric groups in the introduction and the type-A
construction in §4 give particular cases. Conjecture 3.3 is stated in §3 with
the general Weyl setting. Remark 3.4 separately asks about extending the forward
result to Coxeter groups through a Coxeter-theoretic proof. The conjecture and
remark are in the published v1 text. [Section 3.1](https://arxiv.org/html/2610.22730v1#S3.SS1)

Definitions 2.2 and 2.3 distinguish positions in a fixed reduced expression
for the upper element. Each position contributes its simple reflection or
the identity. A magic word has exactly one such choice sequence giving the
lower element. The source's almost magic condition counts reduced subwords
only. For example, keeping the first and last positions of $sts$ yields the
nonreduced word $ss$ with identity product, in addition to the empty choice.
This distinction affects counts even though the Bruhat existence criterion
is equivalent with either convention by deletion. [Definitions 2.2–2.3](https://arxiv.org/html/2610.22730v1#S2.Thmtheorem2) · [Definition 2.9](https://arxiv.org/html/2610.22730v1#S2.Thmtheorem9)

Corollary 3.2 proves magic implies hypercube in the Weyl setting. Lemma 2.17
already obstructs almost magic when the last letter $s$ satisfies
$vs<v\leq ws$. In the type $B_2$ interval $[s,sts]$, the sole possible last
letter is $s$, and the obstruction is $e<s\leq st$. Umutabazi had used the same
interval for a left-descent condition. The direct Lean refutation of
Conjecture 3.3 uses the distinct positions of the two copies of $s$.
[Lemma 2.17](https://arxiv.org/html/2610.22730v1#S2.Thmtheorem17) · [Umutabazi, §4](https://arxiv.org/pdf/2206.06538v1#page=5)

Section 3.2 states the separate right-descent Conjecture 3.9. Its unrestricted
wording meets the same obstruction: the unique reduced expression gives
$D(sts)=D(s)=\{s\}$ and $s\leq st=(sts)s$. This is a consequence of the
counterexample and the right-descent characterization, with Conjecture 3.3
as the sole Lean endpoint. The restriction of the converse to simply laced
Weyl groups and the general Coxeter version of the forward result remain
outside the counterexample. The source reports its type-A₅ check for the
converse. [Conjecture 3.9](https://arxiv.org/html/2610.22730v1#S3.Thmtheorem9)

## Bounded literature evidence

The inspected arXiv v1 originals include Elek, Umutabazi (2206.06538),
Ellenberg–Libedinsky–Plaza–Simental–Williamson (2601.01235) and
Gorsky–Kim–Sherman-Bennett (2603.29260). They give the source conjecture,
prior ingredients, or related type-A results. Bounded arXiv, Crossref,
OpenAlex, MathOverflow and code-index searches located no earlier statement
of this exact all-Weyl positional-magic refutation. Rate-limited citation
queries, incomplete index coverage and inaccessible full-monograph text
limit that finding. [Literature record](https://github.com/the-omega-institute/trureturing/issues/27568)
