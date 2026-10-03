---
slug: aceska-kaczanowski-2022-cross-frame-welch-bound-refutation
bibkey: aceska2022crossframe
doi: 10.1080/01630563.2022.2128818
url: https://arxiv.org/abs/2205.05613v3
triage: theorem
motivation_gids:
  - D5/S3/QuantumBounds/Designs/CrossFrameWelchBoundRefutation.result
---

# Refutation of the dual-frame cross-Gramian Welch bound

## Problem

R. Aceska and M. Kaczanowski, *Cross-Frame Potential*, arXiv:2205.05613v3,
Section 4.2, Conjecture 41, Eq. (21), page 17, states:

> Let F be a frame for Fⁿ, and let G be one of its dual frames. Then
> $\mu(\mathrm{Gr}(F,G))\ge\sqrt{\frac{nk-n^2}{k^2(k-1)}}$.

The source permits real or complex Hilbert spaces and assumes $k\ge n$.
It imposes no equal-diagonal, tightness or equal-norm condition. A real
counterexample therefore refutes its universal statement. The encoded
`claim` quantifies all natural dimensions and family sizes, both real vector
families, `n ≤ k`, `2 ≤ k`, and the frame and dual-frame predicates.
The condition `2 ≤ k` ensures a nonempty off-diagonal maximum; the witness
has `n = 2` and `k = 3`, so this restriction does not remove the refutation.

## Motivation

This is the Tier-1 published conjecture preregistered in issue
[#12318](https://github.com/the-omega-institute/trureturing/issues/12318).
The frozen `result : ¬ claim` supplies a certified counterexample with no
zero frame vectors and with the canonical dual.

## Gap

The preregistration reports that arXiv v3 retains the conjecture. Its scoped
literature check records Crossref and OpenAlex metadata, MathDB problem
354603 with zero solutions, and later papers arXiv:2502.17760, 2601.08028
and 2609.14861 with no settlement of the unrestricted statement found.
Those later-paper searches are search-seat reports; they are not an
independent Stage-B literature review. The journal text has not been read.
The result is `not-found-in-searched-scope`, without a priority or exhaustive
novelty claim. The source's equal-diagonal Lemma 33 is a restricted statement.

## Route

Use the real frame
$F=((-3,-3),(-3,3),(-1,0))$ and its dual
$G=((-3/19,-1/6),(-3/19,1/6),(-1/19,0))$.
The proof verifies both reconstruction equations for every vector and
uses them to prove both spanning conditions. In finite dimension, spanning
is the source's characterization immediately after Definition 1.
`IsDualFrame` includes that G spans and both equations of Definition 3.

The proof computes the nine inner products exactly. The off-diagonal
supremum is $3/19$, whereas the conjectured bound is
$\sqrt{1/9}=1/3$. Exact rational comparison yields the contradiction.
All computations and span arguments are local to `result`.

## Falsifier

A failure of either reconstruction equation, either spanning condition,
the exact off-diagonal maximum, or the strict comparison would invalidate
this witness. These obligations are discharged inside `result`.
A proof of the encoded universal claim would contradict its kernel-checked
negation under the same standard axiom closure.

## Evidence

Lean source: `D5/S3/QuantumBounds/Designs/CrossFrameWelchBoundRefutation.lean`.
The only public theorem is `result : ¬ claim`; its dependencies use the
standard axioms `propext`, `Classical.choice` and `Quot.sound`.
The companion Library note quotes Definitions 1 and 3, the definition of
coherence, and Conjecture 41 from arXiv v3. No atom or cover is used for this
external named problem. Admission is `open-problem-resolution`; proof shape
is `bind-only` and the escape witness is `none`.

## Triage

`theorem`; settlement `Refuted`.

### What the settlement shows

- **Proved in this module:** both families span, both dual reconstruction
  equations hold, all nine cross-Gramian entries have their displayed
  rational values, coherence is $3/19$, and Conjecture 41 fails.
- **Computed:** the frame operator is $\mathrm{diag}(19,18)$, so G is the
  canonical dual. The cross-Gramian diagonal is $(37/38,37/38,1/19)$,
  which fails Lemma 33's equal-diagonal condition $n/k=2/3$. Its squared
  off-diagonal sum is $73/722$ and squared diagonal sum is $1371/722$.
  Hence this witness lies in case (a) of the source's partial proof:
  $2>4/3+73/722$, with gap $1225/2166$.
  These values can be recomputed with `python3 -c 'from fractions import
  Fraction as Q; F=[[-3,-3],[-3,3],[-1,0]];
  S=[[sum(Q(f[i])*f[j] for f in F) for j in range(2)] for i in range(2)];
  G=[[Q(f[0],19),Q(f[1],18)] for f in F];
  C=[[sum(Q(f[i])*g[i] for i in range(2)) for g in G] for f in F];
  off=sum(C[i][j]**2 for i in range(3) for j in range(3) if i!=j);
  print(S, G, C, off, sum(C[i][i]**2 for i in range(3)), Q(2)-Q(4,3)-off)'`.
- **Computed:** for $t>0$, the one-dimensional family $F=(1,t)$ has
  canonical dual $G=(1,t)/(1+t^2)$ and coherence $t/(1+t^2)$, tending to
  zero as $t\to\infty$. Command: `python3 -c 'import sympy as s;
  t=s.symbols("t", positive=True); F=s.Matrix([[1,t]]); G=F/(1+t*t);
  print(s.simplify((F*G.T)[0]), s.simplify((F.T*G)[0,1]),
  s.limit(t/(1+t*t),t,s.oo))'`; output `1, t/(t**2 + 1), 0`.
  This establishes a computed obstruction to any strictly positive bound
  depending only on n and k. It is not an additional theorem in this module.
- **Open here:** formalizing the one-dimensional limiting family and
  re-proving the source's restricted bound are outside this settlement.
  The equal-diagonal lower-bound statement of Lemma 33 survives this witness;
  no assertion about its equality characterization is made here.
- **Separate existing settlement:** Conjecture 42 is refuted by
  `D5/S3/QuantumBounds/Designs/CrossFrameExclusiveDualRefutation.result`.
  It concerns a unique coherence-minimizing dual being canonical, not the
  uniform lower bound of Conjecture 41. Conjecture 43 is outside this module.
  Any use of
  unrestricted Conjecture 41 as a universal premise is invalidated by the
  witness; source results with independent proofs or the equal-diagonal
  hypothesis are not refuted by this module. No dependency audit of all
  results in the paper is claimed.

## ASSUMED-UNVERIFIED

The journal version's preservation of the conjecture is unverified because
its text has not been read. Later-paper conclusions above are seat-reported.
The literature search is bounded. Neither minimality of the witness nor
publication priority is claimed. The computed Triage statements are not
additional kernel-checked theorems in this module.
