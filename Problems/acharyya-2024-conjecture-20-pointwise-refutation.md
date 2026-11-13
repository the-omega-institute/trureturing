---
slug: acharyya-2024-conjecture-20-pointwise-refutation
bibkey: acharyya2024typeb
doi: 10.61091/ars162-14
url: https://arxiv.org/abs/2404.14439v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/QStirling/AcharyyaConjectureTwentyRefutation.result
---

# Acharyya's universal pointwise Conjecture 20 is false

## Problem

Amrita Acharyya, *Type B Set partitions, an analogue of restricted growth
functions*, [arXiv:2404.14439v1](https://arxiv.org/abs/2404.14439v1),
Conjecture 20, states:

> We have that $rcb_B(f(\pi)) = ros_B(\pi) + k(k-1)$ for all
> $\pi \in S_B(\langle n\rangle,k)$.

The journal version, *Ars Combinatoria* 162 (2025), 191–204,
[DOI 10.61091/ars162-14](https://doi.org/10.61091/ars162-14), labels the
same pointwise assertion Conjecture 3.16. The fixed arXiv version is the
statement source. Attribution is to Amrita Acharyya under
[CC BY 4.0](https://creativecommons.org/licenses/by/4.0/); the exact Library
locator is `D5/L/Certificates/acharyya2024typeb`. The signed partition
conventions in Definition 7 are credited there to Sagan and Swanson.

The assertion quantifies over every natural $n,k$ and every standard type B
partition of $\langle n\rangle=\{-n,\ldots,-1,0,1,\ldots,n\}$ into
$2k+1$ blocks. Definition 7 specifies a list
$\pi=[S_0,S_1,\ldots,S_{2k}]$ of nonempty, pairwise disjoint signed
sets whose union is that whole interval. The zero block contains zero and
satisfies $S_0=-S_0$. For every $1\le r\le k$,
$S_{2r}=-S_{2r-1}$ and the positive absolute minimum of this pair belongs
to $S_{2r}$. With
$m_i=\min\{|s|:s\in S_i\}$ and
$M_i=\max\{|s|:s\in S_i\}$, standard order is
$0=m_0<m_2<\cdots<m_{2k}$. These conditions retain the whole source
domain, including all possible zero blocks and block sizes.

Definition 12(1) defines $ros_B(\pi)$ as the number of pairs $(s,S_j)$
such that $s\in S_i$ for some $i<j$ and $s\ge m_j$.
Definition 12(4) defines $rcb_B(\pi)$ as the number of pairs $(s,S_j)$
such that $s\in S_i$ for some $i<j$ and $0<s\le M_j$.
Both bounds are inclusive comparisons on signed integers. The first
statistic does not replace $s$ by its absolute value, and the second
statistic explicitly requires positivity. On disjoint partitions, the
implementation's pair $(s,j)$ identifies precisely the source pair
$(s,S_j)$.

Definition 13 fixes zero and sends each positive $i$ to $n+1-i$ and each
negative $-i$ to $-(n+1-i)$. Lemma 19 defines $f$ by complementing every
letter and then standardizing the entire partition: retain the zero block,
orient each nonzero pair so that its positive absolute minimum is in the
even block, and sort all pairs by their absolute minima. The implemented
map uses this full complement, orientation and sorting algorithm for
general inputs; it has no witness-specific branch.

## Motivation

The proposed map would relate the two statistics separately at each
partition with the shift $k(k-1)$. An admissible partition with unequal
sides decides this universal pointwise assertion. This target is distinct
from the generating-function equality printed after it in the source.

## Gap

The affirmative universal statement is false. The remaining questions are
whether additional hypotheses or a different statistic or map give a
useful replacement, and whether the separately stated generating-function
equality holds. Neither a repair nor that equality follows from this
refutation. General preservation of standard partitions and the involution
assertion about $f$ are not separately proved here.

## Route

The Lean definition `claim` retains every natural $n,k$ and every list of
finite signed blocks, with the full source-domain predicate `Standard`
as its hypothesis. Out-of-range block access and the minimum of an empty
block have total defaults, but every block used at a valid index on an
admissible input is nonempty. The statistics count finite sets of all
eligible signed-letter/target-index pairs, rather than restricting a search
to the displayed witness. Natural truncated subtraction in $k(k-1)$
agrees with the integer expression for every natural $k$, including zero.

Set $n=3$, $k=1$ and

$$
\pi=[\{0\},\{-1,2,3\},\{1,-2,-3\}].
$$

These three blocks partition $\{-3,-2,-1,0,1,2,3\}$, the nonzero
blocks are negatives, and the positive minimum $1$ lies in the even
block. Complementation gives the nonzero pair
$\{-3,2,1\},\{3,-2,-1\}$. Orientation swaps it, and sorting its
single pair leaves

$$
f(\pi)=[\{0\},\{3,-2,-1\},\{-3,2,1\}].
$$

The image also has nonempty, disjoint blocks covering the same interval,
opposite nonzero blocks, positive minimum $1$ in its even block and
even-block minima $0<1$; thus both displayed partitions belong to the
source domain. The exact counted sets, using target indices, are

$$
rosPairs(\pi)=\{(2,2),(3,2)\},\qquad
rcbPairs(f(\pi))=\{(3,2)\}.
$$

Hence $ros_B(\pi)=2$, $rcb_B(f(\pi))=1$ and $k(k-1)=0$.
Instantiating the universal claim would yield $1=2$.

## Falsifier

The refutation requires membership of the input in the complete source
domain, the exact full-map image and the exact signed, inclusive pair
counts. A different source comparison, a different standardization or
failure of any of these witness calculations would invalidate the claimed
source correspondence. The Lean proof checks `Standard 3 1 witness`,
the complete output list and both complete pair sets with `decide +kernel`,
then derives the contradictory cardinality equation with `norm_num`.
Its source correspondence uses Definitions 7, 12(1), 12(4), 13 and
Lemma 19 of the fixed version.

## Evidence

The canonical frozen declaration
`D5/S3/Combinatorics/QStirling/AcharyyaConjectureTwentyRefutation.result`
has the literal type `Not claim`; `claim` has the literal type `Prop`.
The matching Blueprint Scribe binds this result to this dossier with one
`OpenProblemResolutionClaim` of kind `Refuted`. The only public mathematical
declarations are `claim` and `result`; the private definitions support their
live derivation. The accepted axiom closure is the standard three axioms
`propext`, `Classical.choice` and `Quot.sound`.

The admission basis is `open-problem-resolution` under
[issue #30070](https://github.com/the-omega-institute/trureturing/issues/30070#issuecomment-6859977744).
The result's `proof_shape` is `bind-only`: it specializes the full claim
to an original-domain counterexample and uses existing finite-set and
cardinality infrastructure. No escape witness is asserted. The designated
refutation result is exempt from four-slot Reg registration; there is no
additional public theorem to which that exemption could be extended.

## Triage

The universal pointwise Conjecture 20, equivalently the journal's
Conjecture 3.16, is refuted. The proved mechanism is a change in the
cardinality of signed, inclusive comparison pairs under complementation
followed by standardization: the two input ros pairs become only one
image rcb pair, giving the explicit $1\ne2$ witness. The shift is already
zero at $k=1$, so it cannot restore the equation.

This conclusion refutes the asserted statistic identity. It does not
refute the involution assertion about the original map or invalidate the
entire paper. The following generating-function equality remains unsettled;
a pointwise mismatch does not decide equality of the aggregate generating
functions. Restrictions on signed block patterns, an adjusted statistic
or an alternative map are unproved repair directions. None is supplied as
a replacement theorem or formalized as a new conjecture in this dossier.

## ASSUMED-UNVERIFIED

The literature qualification is limited to the fixed arXiv version, the
cited journal version and the registered Library source scope. Exhaustive
worldwide priority and the absence of an unindexed later settlement are
unverified; no global priority claim is made. The Lean kernel verifies
the implemented statement and proof. Correspondence to the published
definitions is a content-review obligation, and this publication unit
remains subject to independent final review. The generating-function
equality, replacement hypotheses and general preservation or involution
theorems for $f$ remain outside the established result.
