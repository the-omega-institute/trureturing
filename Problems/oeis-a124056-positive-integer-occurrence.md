---
slug: oeis-a124056-positive-integer-occurrence
bibkey: quet2006a124056
doi: null
triage: theorem
motivation_gids:
  - D5/S3/Arith/Recurrence/A124056Occurrence.missing_residue_of_finite_three
url: https://mathoverflow.net/questions/515669
---

# Positive-integer occurrence in A124056

## Problem

Let $a_1=1$ and, for every $n\ge1$, let

$$a_{n+1}=\#\{i:1\le i\le n,\ a_i\mid a_n\}.$$

The target is that for every positive integer $k$ there exists a positive index
$n$ with $a_n=k$. Indices, multiplicities and the self index are all retained.
The source is Quet's A124056, Della Corte's question 376929 and Sommacal's
question 515669; see `Library/RecurrenceComposition/quet2006a124056.md`.

## Exact representation

`values N` contains exactly the first $N+1$ terms. Internal `term N` is
$a_{N+1}$, while `sourceTerm n = term (n-1)` is used at positive source
indices. `source_specification` proves the original initialization and the
closed-interval, one-based recurrence; zero never occurs among its indices.

`count N d` counts internal indices strictly below $N$. `prefixMax N` takes
the maximum through internal index $N$, inclusive. Thus the multiplicity bound
available at $N$ is applied only to predecessors of this prefix maximum.

## Established implications and open gap

The formal source proves that infinitely many threes imply the full target,
and that finitely many threes force a fixed missing residue class modulo some
$q\ge2$. It also proves that there can be no globally uniform positive $C,\delta$
with $c_N(d)\le C M_N^{1-\delta}$ for all positive $d$ and all $N$.
This last result directly reuses
`D5/S3/Arith/Divisors/DivisorSubpower.card_divisors_subpower` at
$\epsilon=\delta/2$.

For `AvoidsResidue q N`, every internal index through $N$ whose value exceeds
one has remainder different from one modulo $q$. With $q\ge2$, $t\le N$ and
$v\ge2$, `contributor_rank_bound` proves
$D_t(v)\le q\sum_{d\mid v,\ d<v}c_t(d)$. This time range keeps the successor
of every counted contributor inside the avoided prefix. Empty prefixes and the
first rank are included; $v=1$ is handled by its two initial occurrences.

The finite set `primeWords v` contains the distinct permutations of the prime
factor list of positive $v$. Its cardinality is $b(v)$ and its common length is
$\Omega(v)$. The empty word gives $b(1)=1$. `prime_word_split` proves the exact
split convolution at every rank from zero through $\Omega(v)$. With
$W_A(v)=A^{\Omega(v)}b(v)$ and $A=q+1$, `prime_word_weight_bound` absorbs the
proper-divisor weight sum. Strong induction in
`divisor_card_le_prime_word_weight` gives $D_t(v)\le2W_A(v)$ for positive $v$.

For $d\ge2$, `count_le_prime_word_bounds` gives both $c_t(d)\le2W_A(d)$ and
an injection of its occurrences into the positive predecessor values
$v\le M_N$ with $d\le2W_A(v)$. Consecutive-pair injectivity makes these
predecessor values distinct. These are the finite inputs to the remaining
frequency estimate.

The missing formal implication remains: for each fixed $q\ge2$, prefixes
satisfying this avoidance admit a uniform sublinear multiplicity bound, with
constants independent of $N$ and $d$. One must choose $r>1$ from $q$ alone with
$2A\sum_p p^{-r}\le1$, prove $W_{2A}(v)\le v^r$, and for the same
$s=1/(2r)$ prove
$\sum_{v\ge1}W_A(v)^s/v^\sigma<\infty$ for every $\sigma>1$.
The smooth/rough factorization and its nonnegative sums must be justified;
$W_A$ is not assumed multiplicative. The finite predecessor bound then needs
its Markov estimate and the split at $d\le M_N^s$, using
$\delta=s^2/2$ and $\sigma=1+\delta$. The case $d=1$ and the final inference
from finite threes to a globally uniform bound remain required. No theorem or
axiom for that missing analytic implication is present. The full original
target remains open in Lean.

## Admission boundary

This is partial mathematical content, not an open-problem settlement. The exact
source representation and the infinite-three implication use new finite-tuple,
cardinality and threshold arguments. The missing-residue result uses the
earliest seed divisor and one finite LCM. The sublinear-count contradiction
uses the actual recurrence, the injectivity of consecutive pairs, and the
existing uniform divisor supplier. No novelty or priority assertion is made.

The matching Reg source provides dependent-family realization, equivalence,
variation, sensitivity and observational-dependence evidence for the four
original public theorems. Its four `Contract.Registration` attempts have no
`sourceSelection`. The missing evidence is the complete original-source
reconstruction and its readout path and coordinate bindings. The five
prime-word and contributor bridges have no completed registration; their
complete source-family realization, selected readouts, coordinate bindings
and family-wide evidence remain required. The concrete linked exception is
[issue 31349](https://github.com/the-omega-institute/trureturing/issues/31349#issuecomment-6957024804).
No public theorem is claimed to have a completed `declared_validated`
registration. Independent source-fidelity and per-declaration proof-shape
approval of the complete intended unit remains required before freezing.
