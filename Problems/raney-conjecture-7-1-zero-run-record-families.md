---
slug: raney-conjecture-7-1-zero-run-record-families
bibkey: euhuangkao2026zerorun
doi: null
url: https://arxiv.org/html/2609.25742v1
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Raney/ZeroRunFamilies.raney_zero_run_coefficient_families
---

# Raney Conjecture 7.1: zero-run record families

## Problem

Eu, Huang, and Kao, arXiv:2609.25742v1, Conjecture 7.1, state:

> Fix k, r and a prime p not dividing kr. The left-to-right record values of
> the zero-run sequence of R_(k,r)(n) mod p belong to a finite union of
> families of the form (a p^m + b)/c, where a,b,c depend only on k,r,p.

The source quantifies over positive `k,r` and prime `p` with `p` not dividing
`k*r`. Its Raney numbers are

`R_(k,r)(n) = r * binomial(k*n+r,n) / (k*n+r)`.

The source's left-to-right records allow ties and come from maximal zero runs
in the full infinite sequence. The formal target was preregistered in issue
`#9544` with these parameters, the literal natural quotient, tied records, and
the source-to-formal implication. It does not ask for a converse saying that
every term of every family occurs.

## Motivation

The problem asks for a uniform description of record zero-run lengths for the
entire Raney family, extending beyond the paper's `(3,2)` focus and the known
Catalan `(2,1)` case. The delivered theorem proves the stronger containment of
all actual maximal finite zero-run lengths in one finite family selected before
the endpoints, and separately rules out an infinite terminal zero run.

## Gap

Before this delivery the repository contained neither the general maximal-block
coefficient theorem nor a formal bridge from the literal integral Raney
quotient to a uniform finite-state fixed word. The source paper records
Conjecture 7.1 rather than a proof of its full `k,r,p` statement.

A bounded prior search inspected this repository, the current arXiv source and
its known cases, Crossref results, and a fresh global issue search for the exact
conjecture. It found no full settlement in that scope. A broad Crossref query
returned unrelated items. OpenAlex returned HTTP 429; that is not absence
evidence. No worldwide priority or exhaustive literature certification is
claimed.

## Route

`MaximalBlockEvolution` formalizes literal morphism powers, support
stabilization, actual maximal intervals including `first=0`, and boundary-safe
uniform versions of BKS Lemmas 11 and 12. `MaximalBlockDescent` uses one
stabilizing power throughout, builds actual predecessor/image steps with
literal context words, descends strictly in the right endpoint, and reaches
finite families of early roots, bounded late root words, and bounded contexts.

`BoundaryPivotTransport` follows the complementary boundary letters through
two consecutive descent edges. Rightmost left pivots and leftmost right pivots
make both signed endpoint corrections functions of a finite paired pivot state.
Finite-state repetition yields eventual periodicity. `FinitePathDisplacements`
normalizes periods by the factorial of the paired-state cardinality, combines
finite roots with finite correction paths, and solves the resulting affine
recurrence. It chooses one finite set of integer `(a,b,c)`, with `c>0`, before
an arbitrary actual maximal interval and proves `c*length=a*P^m+b`.

`ZeroRunFamilies` then works with the literal natural quotient. A guarded
adjacent-binomial identity proves integrality and the exact difference formula
before reduction modulo `p`. With `A=max(k-1,r-1)`, the state space
`Fin(A+1) x Bool` stores ordinary values `choose(k*n+a,n)` and guarded
predecessor values `choose(k*n+a,n-1)`, taking the latter as zero at `n=0`.
For each base-`p` digit, the transition records the bounded carry
`(k*d+a)/p`; the Boolean branch records the predecessor borrow through a zero
digit. Lucas' theorem proves the transition weights, including leading-zero
compatibility, so the complete evaluation vector is a pointwise fixed
`p`-uniform word.

The source residue is read exactly as the ordinary component at `r-1` minus
`(k-1)` times its predecessor component. For all sufficiently large `j`, the
same construction proves `R_(k,r)(p^j)=k` modulo `p`; since `p` does not divide
`k*r`, this gives unbounded nonzero support. Applying the generic actual-block
theorem to the zero letter set proves the displayed coefficient equation for
every maximal finite zero interval. Hence every tied left-to-right record value
belongs to the finite union required by Conjecture 7.1.

This route uses neither a finite-prefix approximation nor an assumed
automaticity theorem. It makes no converse-attainment claim. The `(3,2)` and
Catalan cases are not counted as separate results.

## Falsifier

A positive `k,r`, a prime `p` not dividing `k*r`, and an actual maximal finite
zero interval whose length satisfies no equation `c*L=a*p^m+b` from the one
finite coefficient set would refute the formal endpoint. An index cutoff beyond
which every Raney residue is zero would refute its unbounded-support conjunct.
Either finding would also invalidate the route from the stronger theorem to the
source's tied record claim.

## Evidence

- Preregistration: issue `#9544`.
- Source: Eu, Huang, and Kao, arXiv:2609.25742v1, Conjecture 7.1.
- Literature mechanism: Bugeaud, Krieger, and Shallit,
  arXiv:0808.2544v2, Lemmas 10-12 and Corollary 13.
- Formal owner chain:
  `MaximalBlockEvolution -> MaximalBlockDescent -> BoundaryPivotTransport ->
  FinitePathDisplacements -> ZeroRunFamilies`.
- Final theorem:
  `D5/S1/Recurrence/Raney/ZeroRunFamilies.raney_zero_run_coefficient_families`.
- Its first conjunct is unbounded nonzero support. Its second chooses the
  finite coefficient set before all interval endpoints and covers every
  `IsMaximalDeltaInterval {0}` in the literal Raney residue sequence.
- The accepted implementation retains only the standard axiom profile
  `propext`, `Classical.choice`, and `Quot.sound`; canonical report and Freeze
  identities are generated by repository tooling rather than asserted here.

## Triage

`theorem`. The formal result proves a stronger all-actual-runs statement and
unbounded support, from which the literal tied-record assertion follows. Its
`proof_shape` is content and its `admission_basis` is `escape-witness`: the
finite-state Raney construction, exact integral readout, nonzero-support proof,
and actual-block coefficient assembly are live new proof content. The delivery
does not rely on the bind-only open-problem admission exemption.

## ASSUMED-UNVERIFIED

The arXiv title, authors, version, submission time, and literal Conjecture 7.1
were read from the primary v1 pages on 2026-09-24. The BKS title, authors,
version history, and relevant primary-body lemmas were also read directly.
These bibliographic facts, the source-to-formal interpretation, and issue
`#9544` are not kernel-checked.

The negative prior-art result is bounded to the repository, arXiv, Crossref,
and the fresh global issue query described above. OpenAlex was unavailable with
HTTP 429. Worldwide priority, exhaustive absence of another proof, and novelty
beyond the stated repository strengthening remain unverified.
