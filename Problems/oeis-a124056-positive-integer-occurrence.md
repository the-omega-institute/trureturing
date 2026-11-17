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

The missing formal implication is: for each fixed $q\ge2$, prefixes avoiding
all values greater than one congruent to one modulo $q$ admit such a uniform
sublinear multiplicity bound. The intended majorant is
$W_A(v)=A^{\Omega(v)}b(v)$, $A=q+1$, where $b(v)$ counts ordered prime words.
Its proof requires the divisor-list rank inequality, the prime-word split
convolution, one fixed $s>0$ with
$\sum_{v\ge1}W_A(v)^s/v^\sigma<\infty$ for every $\sigma>1$, and the
distinct-predecessor estimate. No theorem or axiom for this missing implication
is present. The full original target remains open in Lean.

## Admission boundary

This is partial mathematical content, not an open-problem settlement. The exact
source representation and the infinite-three implication use new finite-tuple,
cardinality and threshold arguments. The missing-residue result uses the
earliest seed divisor and one finite LCM. The sublinear-count contradiction
uses the actual recurrence, the injectivity of consecutive pairs, and the
existing uniform divisor supplier. No novelty or priority assertion is made.

The matching Reg source provides dependent-family realization, equivalence,
variation, sensitivity and observational-dependence evidence for each public
theorem. The `Contract.Registration` source-selection bindings and current
binding evidence are absent. No public theorem is claimed to have a completed
`declared_validated` registration.
