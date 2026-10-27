---
slug: liang-sagan-2026-pinnacle-middle-order
bibkey: liang2026distributivelattices
doi: 10.1007/s11083-026-09735-2
triage: theorem
motivation_gids:
  - D5/S0/Certificates/Combinatorics/LiangSaganPinnacle/Result.result
url: https://arxiv.org/abs/2408.02782v2
---

# A general obstruction to the pinnacle middle-order lattice

## Problem

J. Liang and B. E. Sagan, *Log-concavity and log-convexity via distributive
lattices*, Order 43 (2026), Article 21, DOI 10.1007/s11083-026-09735-2,
arXiv:2408.02782v2, Section 8, printed pages 34–35, Question 8.6
and its preceding definition:

> Let σ be a permutation of distinct positive integers. Let Pin_n(σ) = {π ∈ S_n | the pinnacles of π are the elements of σ in that order}. … Computation of examples raise the following questions.
> Question 8.6. For all n and σ:
> (a) Is the restriction of the middle order to Pin_n(σ) a distributive lattice?
> (b) Is the sequence (pin_n(σ)) log-concave?

Section 6, “Permutations”, printed pages 17–18, defines inversions and inversion tops:

> Given π = π1 π2 . . . πn ∈ Sn in one-line notation, its set of inversion (values) is Inv π = {(πi, πj) | i < j and πi > πj}.

> We also say that πi is an inversion top if (πi, πj) ∈ Inv π for some πj.

On printed page 18 the inversion coordinate and middle order are specified separately:

> where ιi = # of inversions in which i is an inversion top.

> We can now use the bijection just given to define the middle order (Sn, ⪯) by π ⪯ σ if and only if ι(π) ≤ ι(σ) where the order on inversion tables is component-wise.

Pinnacles are the values π_j with π_{j−1}<π_j>π_{j+1}.

### Formal reading

Lean names have prefix `D5.S0.Certificates.Combinatorics.LiangSaganPinnacle.Result`.

| Source object | Lean name | Correspondence |
| --- | --- | --- |
| Permutation word | `Equiv.Perm (Fin n)` | Increasing positions; Fin value k represents k+1. |
| Ordered pinnacle sequence | `pinnacleWord` | Values at internal strict local maxima, from left to right. |
| Inversion-top table | `iota` | Number of smaller values to the right of a value. |
| Middle order | `middleLe` | Componentwise comparison of `iota`. |
| Ordered pinnacle class | `Pin` | Fibre of `pinnacleWord`. |
| Universal distributive-lattice assertion | `claim` | A distributive-lattice structure with exactly this order on every fibre. |
| Refutation | `result` | Exactly ¬ claim. |

The source uses distinct positive integers. Repeated values cannot occur
in a pinnacle word. A source sequence containing a value outside [n]
has empty fibre; the counterexample uses only distinct in-range values.

## Motivation

The settling declaration is `D5/S0/Certificates/Combinatorics/LiangSaganPinnacle/Result.result`.
The source note is `D5/L/PermutationPatterns/liang2026distributivelattices`.
The ordered pinnacle condition constrains positions, while the middle
order constrains inversion counts. Their interaction can prevent joins.

## Gap

Even existence of a common upper bound fails in the fibre with
σ=(n−2,n) for every n≥6. Thus this fibre is not a lattice, and the
universal distributive-lattice assertion is false.

## Route

In paper values let

$$A_n=(1,n-2,2,n,3,4,\ldots,n-3,n-1),$$
$$B_n=(n-1,1,n-2,2,n,3,4,\ldots,n-3).$$

Both have ordered pinnacle word (n−2,n). Their relevant inversion counts
are ι_n(A_n)=n−4 and ι_{n−1}(B_n)=n−2.
An upper bound U of B_n must place n−1 before every smaller value.
The left neighbour of the first pinnacle n−2 is smaller than n−2,
so n−1 precedes that neighbour. The first pinnacle therefore has
zero-based position at least 2. The second pinnacle n comes later and
cannot be adjacent, so its position is at least 4. For a maximal value,
ι_n(U)=n−1−pos(n)≤n−5<n−4. This contradicts U being above A_n.
A lattice join would be a common upper bound.

## Falsifier

Two permutations in the same ordered pinnacle fibre with no common upper
bound contradict the universal claim. A mismatch in the word order,
value shift or inversion-top convention would invalidate the argument.

## Evidence

**PROVED in Lean.** `no_common_upper_bound` establishes the obstruction
for every n≥6. `result : ¬ claim` refutes the universal assertion. Both
statements are checked by the Lean kernel.

**COMPUTED.** The immutable
[experiment directory](https://github.com/the-omega-institute/trureturing-experiments/tree/c6b13bb3bbd40e157987f64ddb02e18d280b296f/experiments/liang-sagan-pinnacle-middle-order)
contains `ls-pinnacle.py`, SHA-256
`4343fcc9ffc8cfd37742ca99fe76bc80567cf060d26fd934568621c3473fbb25`.
`python3 ls-pinnacle.py`, exit 0, checks the family for n=6,…,9 and
all nonempty fibres for n=1,…,6. The command
`python3 ls-pinnacle.py 7`, exit 0, additionally gives
`n=7 classes=50 nonlattice=14`.
Both commands use the same pinned script and SHA-256 above.

The supplied literature scope covers arXiv v2 and the Order publication,
Vatter arXiv:2602.16355, and *Middle orders: all distributive lattices
between weak and Bruhat*, arXiv:2606.12129. No settlement was found in
that scope. This does not establish exhaustive coverage or priority.

## Triage

### What the settlement shows

- **PROVED in Lean.** `no_common_upper_bound`: for every n≥6, the class
  with σ=(n−2,n) contains two elements with no common upper bound.
- **PROVED in prose.** A large non-pinnacle value forced before every
  smaller value must lie at the front: it precedes the first pinnacle,
  which precedes the maximum, so it precedes every other value.
  This pushes the first pinnacle past a smaller left neighbour, then
  pushes the maximum two positions farther. The resulting cap on its
  inversion count excludes a common upper bound.
- **COMPUTED.** Every nonempty class is a lattice for n≤5. At n=6 the
  non-lattice classes are σ∈{(3,6),(4,6),(6,3),(6,4)}. The enumeration
  tests lattice existence, not distributivity of the remaining classes.
- **COMPUTED.** At n=7, 14 of 50 nonempty classes are non-lattices.
  The pinned script command `python3 ls-pinnacle.py 7`, exit 0, gives
  `n=7 classes=50 nonlattice=14`; its immutable directory and SHA-256
  are stated in Evidence. These are finite readings, not a general
  classification theorem.
- **OPEN.** Question 8.6(b), log-concavity of the class-size sequence,
  is untouched. A classification of all lattice fibres is also open here.

## ASSUMED-UNVERIFIED

Google Scholar's full cited-by list was unavailable in the supplied
literature check. Quotations and printed page locators use the supplied
pdftotext of arXiv:2408.02782v2; the PDF typography was not independently
checked. External literature checks are the supplied bounded scope; no exhaustive novelty
claim is made.
