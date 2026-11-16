---
bibkey: allouche2025reflectioncomplexity
authors: Jean-Paul Allouche; John M. Campbell; Shuo Li; Jeffrey Shallit; Manon Stipulanti
year: 2025
title: The reflection complexity of sequences over finite alphabets
doi: 10.1007/s00224-025-10234-x
url: https://arxiv.org/abs/2406.09302v4
claim: "Definitions 1 and 3 define reflection equivalence and reflection complexity; Conjecture 28 asks for bounded consecutive differences under linear factor complexity."
strata_touched:
  - D5/S1/Words/Complexity/AlloucheReflectionComplexitySupport
  - D5/S1/Words/Complexity/AlloucheReflectionComplexityConjecture28
license: citation-only
triage: anchor
---

# Reflection complexity and Conjecture 28

## Verified locator

DOI: https://doi.org/10.1007/s00224-025-10234-x

Source: https://arxiv.org/abs/2406.09302v4

The quotations below are from arXiv v4, revised 6 May 2025.
The journal locator is *Theory of Computing Systems* 69, article 31.
The arXiv PDF and TeX supply the statement; the subscription journal text
is not used as a full-text source.

## Source definitions

Definition 1, pp. 2–3: “Given a finite word $u=u(1)u(2)\cdots u(m)$, its
*reversal* is the word $u^R=u(m)u(m-1)\cdots u(1)$, i.e.,
$u^R(i)=u(m+1-i)$ for all $i\in\{1,\ldots,m\}$.”

Definition 1, p. 3: “Two finite words $u$ and $v$ are *reflectively equivalent*
if $v=u$ or $v=u^R$.”

Definition 3, p. 3: “Let $\mathbf{x}$ be a sequence. The *reflection complexity
function* $r_{\mathbf{x}}:\mathbb{N}_0\to\mathbb{N}$ of $\mathbf{x}$ maps every
$n\ge 0$ to the number of distinct length-$n$ factors of $\mathbf{x}$, up to
equivalence by $\sim_r$.”

The source indexes letters at one. `Fin n` indexes them at zero, and `Fin.rev`
implements the same reversal. The quotient is restricted to actual occurring
factors, including the unique empty factor. Reversal closure is not assumed.
Example 4 gives $r_{\mathbf{t}}(2)=3$: the classes represented by $00$, $11$
and either member of $\{01,10\}$ are counted once each.

## Source assertion

Conjecture 28, p. 15: “Let $\mathbf{x}$ be a sequence of at most linear factor
complexity. Then $r_{\mathbf{x}}(n+1)-r_{\mathbf{x}}(n)$ is bounded for all
$n\ge 0$. Hence, in particular, if $\mathbf{x}$ is (generalized) automatic,
so is $(r_{\mathbf{x}}(n+1)-r_{\mathbf{x}}(n))_{n\ge 0}$.”

The Lean claim is the entire bounded-difference assertion: every finite alphabet
and every one-sided word with $p(n)\le C(n+1)$ for some natural $C$ has an integer
absolute-difference bound at every natural length. The automaticity sentence is
outside this assertion. Its generalized-numeration interpretation requires the
source's addable positional-numeration scope; no claim for arbitrary numeration
systems is made.

## Mathematical mechanism and boundaries

A new marker at the center of the bi-infinite mirror gives exactly $u_n+n$
factors of length $n$, where $u_n$ counts the union of the source factors and
their reversals. A weighted finite graph estimate proves bounded increments for
the mirror's bi-infinite language. Reflection-orbit counting and deletion of
palindromic loops then bound the original reflection increments. Transient
prefixes and periodic words remain included.

The bi-infinite bounded-increment ingredient is a case of Cassaigne's theorem
(Proposition 2 in *Special factors of sequences with linear subword complexity*,
DLT II, 1996, pp. 25–34). A later precise language statement appears in
Leemann–Nagnibeda–Skripchenko–Veprev, arXiv:2402.15877v2, Lemma 2.14.
The formal argument establishes the needed bi-infinite case directly; it does
not assume the language theorem or establish its full factorial-language scope.

The source's Theorem 30 already gives the universal lower bound on consecutive
reflection differences. Its proofs for particular sequences and its
reversal-closed cases retain their stated hypotheses. Optimal dependence on
$C$, a formal automaticity deduction, and the full factorial-language theorem
remain open here. Global literature completeness is ASSUMED-UNVERIFIED.

## Exact finite checks

The independent checker is in `the-omega-institute/trureturing-experiments`,
commit `c9f5c96ca6c988190a2b67aaf38b4f3c42869877`,
`docs/reports/allouche-reflection-complexity-c28/check.py`, SHA256
`a523f22f535caa2b4b4930fb354fe540013eb15e535f971cc301c44f0ac31b0d`.
The recorded command `python3 docs/reports/allouche-reflection-complexity-c28/check.py`
exited 0 with `ALL_CHECKS_OK`: 1,457 ultimately periodic presentations and
24,769 comparisons for lengths 0 through 16, including 1,090 presentations
without reversal closure and 2,160 negative reflection steps. These finite
checks are separate from the universal Lean proof.
