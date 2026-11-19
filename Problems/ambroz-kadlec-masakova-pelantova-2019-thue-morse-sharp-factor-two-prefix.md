---
slug: ambroz-kadlec-masakova-pelantova-2019-thue-morse-sharp-factor-two-prefix
bibkey: ambrozetal2019palindromiclength
doi: 10.1016/j.tcs.2019.02.024
url: https://arxiv.org/abs/1812.00711v2
triage: theorem
motivation_gids:
  - D5/S1/Words/Palindromes/ThueMorseSharpPrefix.sharp_factor_two_prefix
---

# Sharp factor two for actual Thue–Morse prefix minima

## Problem

Ambrož, Kadlec, Masáková and Pelantová, *Palindromic length of words and
morphisms in class P*, arXiv:1812.00711v2, Section 6, page 13, with Table 1
on page 14, write the following complete final paragraph:

> Our computations suggest that including both palindromes and antipalindromes into the factorization of Thue-Morse word, one can reduce the number of factors by half (and not more), see Table 1. On the other hand, we suppose that there exist prefixes of arbitrary palindromic length whose combined pal-antipal length as big as the palindromic one, see Table 2. Other research could be done in this direction.

The preceding context explicitly says, “We have computed the palindromic and
combined pal-antipal length for the prefixes of the Thue-Morse word”.
The first sentence is an unnumbered computational suggestion. The single
preregistered settlement is its following quantified reading in that prefix
context, with the finite sharpness already illustrated by Table 1:

$$
(\forall n\in\mathbb N,\ n\ge1\Rightarrow P(n)\le2C(n))
\quad\land\quad
(\exists n\in\mathbb N,\ n\ge1\ \land\ P(n)=2C(n)>0).
$$

Here t is the literal a-start fixed point of a↦ab, b↦ba, with t(0)=a,
t(2r)=t(r), t(2r+1)=E(t(r)), E(a)=b, E(b)=a. The prefix u_n=t[0:n) has
length n and starts at zero. P(n) is the minimum number of consecutive
nonempty palindrome pieces concatenating to u_n. C(n) is the minimum number
of consecutive nonempty pieces concatenating to the same u_n, each either
a palindrome or an antipalindrome w=E(reverse(w)). It is a mixed minimum,
not an antipalindrome-only minimum. Empty pieces are removable; the empty
word has cost zero and the event quantifies over n≥1.

The Lean word is `Complexity.factor n 0`, whose arguments are length and
start, with `false=a`, `true=b` and exchange `Bool.not`. P is
`FridPrefix.PL`, defined by `Nat.find` over `PalFactors`; C is
`ThueMorse.combinedLength`, defined by `Nat.find` over `MixedFactors`.
These are actual minima on this same word. The paper's all-factor maximum
notation from Section 1 is not the prefix cost P used here.

## Motivation

The assertion asks how much allowing exchange-reversal antipalindromes can
save on a prefix. A universal factor-two comparison and one positive
attaining prefix together determine the optimal uniform multiplicative
constant. Table 1's first row is the prefix ab of length two, with ordinary
cost two and mixed cost one; it is source data, not a newly discovered
external event.

## Gap

The frozen signed-cut lower bound gives W(n)≤C(n), where W is the existing
period-doubling signed weight. It does not give the needed ordinary upper
bound for every prefix. The substantive missing step was P(n)≤2W(n) for all
natural n. Binding this estimate to the original lower bound and proving
the two actual minima at n=2 supplies the complete A+B of
[preregistration #28141](https://github.com/the-omega-institute/trureturing/issues/28141).
This dossier concerns that one event; the helper and finite attainer are
not separate problem resolutions.

## Route

`ThueMorseSharpPrefix.prefix_signed_upper` proves P(n)≤2W(n) by strong
induction. The existing substitution tau(b)=[b,not b,not b,b] preserves
palindromes and transports the literal prefix to the prefix of four times
the length, giving P(4m)≤P(m). One-letter Lipschitz bounds and the signed
weight recurrences handle the four residues. For residue two, bounds from
both neighboring multiples of four give 2W(m)+2 and 2W(m+1)+2, matching
W(4m+2)=1+min(W(m),W(m+1)).

Combining with `ThueMorseSignedCut.combined_prefix_signed_lower` gives
P(n)≤2W(n)≤2C(n). Within the existential branch of the complete theorem,
the proof establishes P(2)=2 and C(2)=1 on the literal word `[false,true]`:
that word is one antipalindrome and is not a palindrome. The signed lower
bound and explicit mixed factorization establish C; impossibility of zero
or one ordinary pieces and the ordinary upper bound establish P. These
native-minimum facts are local proof steps, with no separate finite-instance
declaration.

Both retained theorems have `proof_shape: content`. For
`ThueMorseSharpPrefix.sharp_factor_two_prefix`, inlining the same-delivery
`prefix_signed_upper` reaches its substantive all-prefix strong induction;
classification stops at the existing frozen or pinned upstream premises,
not at that new helper. The thin outer composition does not change this
classification. The proposed host `admission_basis: open-problem-resolution`
is for the one complete preregistered A+B assertion. `prefix_signed_upper`
is its consumed all-prefix auxiliary, used on both the universal bound and
the native attainer proof paths, with no separate resolution claim.

The module's `utility: none` applies to each retained declaration: the
all-length upper estimate and the complete sharp uniform comparison are
unbounded mathematical results. Neither is a checker, numeric reduction,
bounded enumeration or separately retained certified instance. The finite
witness is essential evidence inside the complete event, not an independent
computational deliverable. Computational utility basis, instance, premises,
result and claim fields are `not-applicable(kind=none)`.

## Falsifier

A positive prefix with certified actual P(n)>2C(n) would refute the
universal clause. Substituting proxy costs, changing the literal word or
start index, permitting empty positive pieces, or proving only finitely
many prefixes would fail source fidelity. A mixed factorization alone does
not certify an ordinary lower bound. The sharpness clause requires the
same actual minima and positivity; equality at the empty word would not
suffice. The source's finite examples do not prove the universal clause.

## Evidence

The full result is
`D5/S1/Words/Palindromes/ThueMorseSharpPrefix.sharp_factor_two_prefix` in
[the Lean source](../D5/S1/Words/Palindromes/ThueMorseSharpPrefix.lean).
The [Scribe source](../Blueprint/D5/S1/Words/Palindromes/ThueMorseSharpPrefix.scribe.cs)
attaches exactly one `OpenProblemResolutionClaim` of kind `Proved` to that
full theorem and this dossier's slug. The all-prefix auxiliary has no separate resolution claim, and the finite
attainer remains internal to the full theorem. The bibliography is the existing
[AKMP Library owner](../Library/Words/ambrozetal2019palindromiclength.md),
with the same DOI, URL and bibkey as the front matter.

Verification is scoped to the selected Lean module and its imports, with
exact statement identities, current source hashes and axiom closures checked
in the affected scoped report. The accepted axiom boundary is
`Classical.choice`, `Quot.sound`, `propext`, with no `sorryAx`. These checks
do not establish independent source/admission approval. Renewed source
review, canonical emission and freeze remain pending.

The bounded source screen examined the complete arXiv v2 Section 6 and
relevant definitions, and compared related primary sources including
[Frid, JIS 22 (2019), 19.7.8](https://cs.uwaterloo.ca/journals/JIS/VOL22/Frid/frid4.pdf),
[arXiv:1907.12543v1](https://arxiv.org/abs/1907.12543v1),
[arXiv:2009.02934v2](https://arxiv.org/abs/2009.02934v2) and
[arXiv:1906.06174v1](https://arxiv.org/abs/1906.06174v1).
No inspected passage supplied the exact mixed-cost cap. Several later
sources were checked only through selected passages, result headings or
keyword scans; their full proof bodies were not exhaustively read.

## Triage

The compiled result supplies every positive zero-start prefix comparison
and a finite positive attainer for the actual minima. The mechanism is
P≤2W≤2C. The best constant for this domain is two because P(2)=2C(2)>0.
It does not require identifying both minima at every n.

The following Table 2 sentence is the distinct unbounded equal-cost C=P
event of [#26513](https://github.com/the-omega-institute/trureturing/issues/26513)
and the [equal-cost dossier](ambroz-kadlec-masakova-pelantova-2019-thue-morse-equal-cost.md).
That family is not used to prove this event. An unbounded sharpness family
P=2C, a universal Table 1 first-occurrence formula, and an extension to all
shifted factors are outside this settlement. No additional theorem or
external resolution is claimed for them.

Source-owner audits remain unfinished. The two newly authored public
theorems `prefix_signed_upper` and `sharp_factor_two_prefix` require their
source-owner four-slot audit attempts in StageB. The five visibility-only
exposures `tau`, `tau_pl`, `factor_concat`, `tau_prefix` and
`prefix_four_sub_one` remain owned by `ThueMorseAttainment`; their canonical
publicization identities, repins and applicable actual-owner audits are
also StageB obligations. There is no claim of completed publicization,
fresh freeze or `declared_validated`. The existing unfinished audits under
[#26539](https://github.com/the-omega-institute/trureturing/issues/26539)
remain unfinished; this dossier does not repair or discharge them.

## ASSUMED-UNVERIFIED

The full journal body was not accessible in the source intake; publisher
metadata confirms the journal identity, not wording equivalence to arXiv
v2. The literature screen is bounded: unseen proof bodies, unindexed or
later solutions, worldwide present openness and global priority remain
unverified. The quantified A+B is the preregistered reading of the source
prose in its explicit prefix context, not a printed numbered conjecture.
Independent approval of the revised source/admission unit remains pending. Successful
compilation establishes the formal statement, not global novelty, canonical
publicization or a completed source-binding certificate. Independent review,
StageB, triplet review, required CI and normal integration remain necessary
before any completed-event KPI claim.
