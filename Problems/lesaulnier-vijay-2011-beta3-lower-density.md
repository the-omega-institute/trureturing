---
slug: lesaulnier-vijay-2011-beta3-lower-density
bibkey: lesaulnier2011permutations
doi: 10.48550/arXiv.1004.1740
url: https://arxiv.org/abs/1004.1740
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Permutation/LeSaulnierVijayLowerDensityRefutation.result
---

## Problem

LeSaulnier and Vijay, arXiv:1004.1740, *Discrete Mathematics* 311 (2011), p. 207,
define a subset of the positive integers to be 3-free when it admits a permutation containing
no three-term arithmetic progression as a subsequence. Its lower density is

\[
\underline d(S)=\liminf_{n\to\infty}\frac{|S\cap[1,n]|}{n},
\qquad
\beta(3)=\sup\{\underline d(S):S\text{ is 3-free}\}.
\]

Their Theorem 3 establishes \(\beta(3)\ge1/4\), and they conjecture \(\beta(3)=1/4\).
The formal claim is the universal upper bound: for every \(S\subseteq\mathbb N\) with
\(0\notin S\), if there is an injective \(\pi:\mathbb N\to\mathbb N\) whose range is
exactly \(S\) and such that

\[
\forall i<j<k,\quad \pi(i)+\pi(k)\ne2\pi(j),
\]

then \(\underline d(S)\le1/4\). The enumeration condition forces infinitude and covers
arithmetic progressions in both numerical directions. The target is preregistered in issue #14866.

## Motivation

An explicit 3-free set of lower density greater than one quarter refutes the named conjecture.
The rank and progression conventions are compatible with the repository's
`D5/S3/Combinatorics/ErdosGrahamOrderGadget` module: the middle numerical term must not lie
between the endpoint ranks in either direction. A literal enumeration is required in addition
to a progression-free rank, so the counterexample concerns the source's infinite permutation
problem.

## Gap

The preregistration's literature readings and web-search findings were supplied by the
orchestrator; this offline implementation does not constitute a new literature search.

- Geneson, arXiv:2608.12604, refutes only the \(\alpha\) conjunct by establishing
  \(\alpha_{\mathbb N}(3)\ge2/3\).
- Kasel, arXiv:2609.02939, with the supplied August 2026 reading, still lists
  \(\beta_{\mathbb N}(3)\ge1/4\). The bound \(\alpha+\beta\ge11/12\) leaves the density
  obstruction undecided.
- Adenwalla, arXiv:2211.04451, Question 3, is a related open-question source.
- The supplied web searches found no refutation of the \(\beta\) conjunct within their
  searched scope.
- The supplied reading of `formal-conjectures/ErdosProblems/197.lean` states only the parent
  Erdős problem, which remains open; it does not state this lower-density conjunct.

## Route

For \(k\ge0\), put \(M_k=(11^k+1)/2\) and define

\[
S=\{1\}\cup\bigcup_{k\ge0}
\left([11^k+1,(3\cdot11^k+1)/2]
\cup[3\cdot11^k+1,(11^{k+1}+1)/2]\right).
\]

The formal intervals are equivalently
\([2M_k,3M_k-1]\) and \([6M_k-2,11M_k-5]\), with inclusive natural endpoints.
The recurrence \(M_{k+1}=11M_k-5\) gives stage 0 as \([2,2]\cup[4,6]\) and stage 1 as
\([12,17]\cup[34,61]\).

Every numerical three-term progression in \(S\) lies within one stage. If two lower terms
come from previous stages, their third term is below the current stage's first endpoint.
If the first term is at most \(M_k\) and the second lies in one current interval, doubling
the second and subtracting the first lands in the following gap. These inequalities rule
out a progression crossing stages.

Within each stage use binary-reversal order. At the lowest binary digit where the common
progression difference is nonzero, the middle term has the opposite digit from both endpoints;
the middle term therefore precedes both or follows both. Give stages disjoint increasing
natural rank ranges, with 1 ranked first. The rank is injective on \(S\), and Mathlib's
`Nat.nth` enumeration of its infinite image supplies an injective \(\pi\) with range \(S\)
and increasing rank.

The counting target is

\[
\forall n\ge1,\quad15\,|S\cap[1,n]|\ge4n.
\]

An induction counts completed stages and the two partial current intervals. The uniform
bound transfers to the real-valued limit inferior, giving \(\underline d(S)\ge4/15>1/4\).
No equality of finite-prefix density with \(4/15\) is required.

## Falsifier

The counterexample route fails if a progression can cross stages, if the within-stage order
places a progression's middle term between its endpoints, if its natural rank has collisions,
if the purported enumeration omits elements, or if any positive prefix violates the counting
bound. The formal statement would not match the source if it allowed repeated enumeration
values, omitted the range equality, checked only increasing progressions, or used upper
density in place of lower density.

## Evidence

The kernel-checked Lean sources specify the literal power-endpoint set, prove stage separation
and rank properties, convert the rank to the required enumeration, and prove the real-valued
`Filter.liminf` lower-density inequality. The designated public statement is
`D5.S3.Combinatorics.Permutation.LeSaulnierVijayLowerDensityRefutation.result : ¬ claim`.
The scoped Lean build passes. The exact declaration types are `claim : Prop` and
`result : Not claim`; the result's axiom closure contains only `propext`, `Classical.choice`
and `Quot.sound`. All four source modules have matching Scribe definitions.

The larger-family arithmetic below was recomputed with Python's exact rational arithmetic.
For \(J=1,2,3,4,5\), its reported density expression gives
\(4/15,23/84,47/170,1135/4092,379/1365\), respectively. These computations do not certify
the family's progression-free permutations or formalize its limiting density.

## Triage

`theorem`; named external conjecture, preregistration #14866. The explicit instance is used
only to refute the universal quarter-density claim. Admission is `open-problem-resolution`,
and the main module's utility is `certified-instance` with `refutes` directed to its `claim`.

[derived/computed, not formalized] The supplied J-family has density expression

\[
d_J=\frac{40\cdot4^J-3J-13}{144\cdot4^J-36}\longrightarrow\frac5{18}.
\]

Dividing numerator and denominator by \(4^J\) gives the limit \(40/144=5/18\), since
\(J/4^J\to0\). The family would consequently establish \(\beta_{\mathbb N}(3)\ge5/18\)
once its stated construction and limiting lower density are justified; that stronger result
is outside this formalization.

[derived/computed, not formalized] Combining that stronger lower bound with the supplied
Geneson bound would give

\[
\alpha_{\mathbb N}(3)+\beta_{\mathbb N}(3)
\ge\frac23+\frac5{18}=\frac{17}{18}<1.
\]

Thus this improvement still leaves the density obstruction to Erdős #197 undecided.
The stage-separation mechanism explains the quarter-density conjecture's failure: multiple
intervals within one finite stage can share a progression-free order while sufficiently
large interstage gaps forbid mixed progressions.

[open] The exact value of \(\beta_{\mathbb N}(3)\).

## ASSUMED-UNVERIFIED

The literature readings, publication metadata and search conclusions are supplied evidence,
not independently checked by this offline implementation. The journal DOI
`10.1016/j.disc.2010.10.006` was not verified against the paper, so the frontmatter uses the
arXiv DOI. The absence of a refutation in the supplied search does not establish exhaustive
worldwide priority. The J-family construction, its progression-free permutations and its
limiting lower-density assertion are not formalized here. The formal target settles the
quarter-density conjunct; it does not settle the parent
Erdős #197 problem or the exact value of \(\beta_{\mathbb N}(3)\).
