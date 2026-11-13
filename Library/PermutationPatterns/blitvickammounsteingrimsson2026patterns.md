---
bibkey: blitvickammounsteingrimsson2026patterns
authors: Natasha Blitvić, Mohammed Slim Kammoun, and Einar Steingrímsson
year: 2026
title: "Permutations, Pattern Covers, Posets and Positivity: Part I: Patterns and Posets"
doi: 10.48550/arXiv.2610.29846
url: https://arxiv.org/abs/2610.29846v1
claim: "Conjecture 7.1 concerns the maximum packing count; Section 7 items 10 and 11 concern 135289467 with overlap 3 and modular regularities of 14325 with overlap 2."
strata_touched:
  - D5/S3/Combinatorics/Permutation/PackingMaximumRefutation
  - D5/S3/Combinatorics/Permutation/BlitvicKammounSteingrimsson135289467Core
  - D5/S3/Combinatorics/Permutation/BlitvicKammounSteingrimsson135289467Product
  - D5/S3/Combinatorics/Permutation/BlitvicKammounSteingrimsson14325Core
  - D5/S3/Combinatorics/Permutation/BlitvicKammounSteingrimsson14325Transfer
license: citation-only
triage: anchor
---

# Prescribed permutation packing

The primary source is arXiv:2610.29846v1, submitted 21 October 2026.
Definition 2.2 defines order isomorphism by agreement of every strict
comparison. Definition 2.6 and equation (2.1) define a permutation of length
$n=K+(j-1)(K-m)$ that has a copy of the $K$-pattern at each start
$1+t(K-m)$, for $0\le t<j$. Remark 2.7 explicitly permits additional
occurrences. This is a prescribed packing count, rather than avoidance
or a count with exactly $j$ total occurrences.

Definition 3.3 and its following paragraph require order-compatible
$m$-prefix and $m$-suffix. The important convention in Section 3 uses
increasing prefix and suffix, with the first prefix value smaller, after
count-preserving symmetries. The Lean comparison domain includes every
compatible pattern directly. No normalization theorem is needed to admit
the counterexample, which already satisfies the convention.

Section 7 item 4 introduces the maximum count as a function of $(K,m,j)$.
Conjecture 7.1 states:

> For overlap $m\le K/2$, the maximum is obtained when prefix and suffix
> are interleaved and minimal, that is, for patterns with prefix
> $135\ldots(2m-1)$ and suffix $246\ldots(2m)$.

This asserts attainment by a member of the prescribed family. It does not
assert uniqueness or fix the order of the remaining middle values.
The equality case $K=2m$ has an empty middle.

The repository calculation gives
$C(13472568,4,2)=9>8=C(13572468,4,2)$. At this equality boundary,
the prefix and suffix determine every prescribed pattern, so the comparison
refutes the entire maximum-attainment assertion. The exact counts and
source-permutation correspondence are the repository result; the general
packing definitions and the packing/linear-extension interpretation
(Lemma 5.1 and Theorem 5.3) are the source authors' results.

The finite mechanism is two independent three-way choices for the
competitor, compared with three independent binary choices for the
prescribed pattern. The actual maximum, the strict-overlap range
$2m<K$, and Section 7 item 8's separate cutoff question are not settled.

The bounded prior check covered the primary version, selected symmetry
and enumeration results, the FPSAC precursor, Elizalde
arXiv:1203.1636v1 (overlap-one results), and Iriarte
arXiv:1405.4880v2 (orientations of a fixed graph). None supplied a located
whole answer in that checked scope. The graph-orientation theorem does
not directly compare these changing pattern posets. Ineffective general
web queries establish no absence. Worldwide priority, exhaustive
literature absence, and provider memory are unverified; no such claim
is made. Ordinary counting ingredients receive no separate novelty claim.

## Verified locator

- DOI: `10.48550/arXiv.2610.29846`.
- https://arxiv.org/abs/2610.29846v1
- https://arxiv.org/html/2610.29846v1#S7.Thmtheorem1
- Definitions 2.1–2.2, 2.5–2.6; equation (2.1); Remark 2.7.
- Definition 3.3 and the important convention in Section 3.
- Lemma 5.1 and Theorem 5.3 for the original chain interpretation.

The retained primary HTML has SHA-256
`ccfe47a85e19f9deb414583e52f1e627c4291eb4aaef1d8af3da683132202b97`.

## Pattern 135289467 with overlap three

Section 7, item 10, page 49:

> The enumeration for 135289467 with overlap 3, for example, has a
> product formula according to our data, but the successive factors are
> not single binomial coefficients. However, the factors are polynomial
> starting from $j=3$, namely
> $121\binom{j-3}{0}+168\binom{j-3}{1}+72\binom{j-3}{2}$, in the
> binomial basis.

Definitions 2.1–2.3 and 2.5–2.6 use actual permutations on the one-based
alphabet, pairwise strict comparisons, and prescribed consecutive windows.
The window starts are $1+6t$, with $0\le t<j$, and the permutation length
is $9+6(j-1)$. Remark 2.7 permits additional occurrences. Lemma 5.1
uses the inverse pattern to express each window as an increasing chain;
Theorem 5.3 identifies the resulting linear extensions with packings.

The zero-based pattern is `![0,2,4,1,7,8,3,5,6]`. The claimed recurrence
uses the literal binomial expression for every natural $j\ge3$; the
separate initial values are $A_1=1$ and $A_2=30$. The last sentence of
item 10 concerning all product formulas is a separate question.

The symbolic derivation removes six labels and shifts the surviving
relations by six. Its two disjoint shuffle cases contribute
$\binom{s+3}{2}+\binom{s+4}{2}=(s+3)^2$. Together with the initial
count, this gives $A_j=30\prod_{t=3}^j(6t-7)^2$ for $j\ge2$.
The repository theorem retains the binomial form of the source.

The bounded literature screen on issue #21331 located no settlement of
this fixed-pattern assertion. Completeness of that screen is
ASSUMED-UNVERIFIED; unpublished work and the authors' cited manuscript
in preparation were not read. The packing correspondence and the
binomial shuffle count are prior results, without a novelty claim.

## Pattern 14325 with overlap two

Section 7, item 11 states:

> A curiosity in the enumeration for 14325 with overlap 2 is that all the
> numbers are congruent to 6 mod 10, except when $j=2^k-1$, those are
> congruent to 1.

Its continuation states:

> Another apparent regularity in this is that 4 seems to divide all but
> those for which $j=2^i+2^p-1$ where $0\le p\le i$, such as 8,9,11,15.

For every natural $j\ge1$, let $A_j$ count actual permutations of
$[3j+2]$ with the prescribed length-five windows starting at $1+3t$,
$0\le t<j$, matching every comparison of 14325. Additional occurrences
are allowed. There is no symmetry quotient or avoidance condition.
The full candidate registered in issue
[28504](https://github.com/the-omega-institute/trureturing/issues/28504)
requires $A_j\bmod10=1$ when $j+1=2^k$ for some $k\ge1$ and $6$
otherwise. It also requires

$$
4\nmid A_j\quad\Longleftrightarrow\quad
\exists i,p\in\mathbb N,\ p\le i\ \land\ j+1=2^i+2^p.
$$

Both $p=0$ and $p=i$ belong to this candidate. There is no assertion at
$j=0$. The printed continuation does not explicitly state the converse
as an iff; exact exceptions are the stronger registered interpretation,
which must be proved in both directions. The earlier issue
[21304](https://github.com/the-omega-institute/trureturing/issues/21304)
concerns only the modulo-ten proposal. Its original criteria, unresolved
status and historical resource boundaries are preserved; it is not a
settlement of the full item.

The source-structure module uses the existing literal `Packs` predicate.
Writing $a_t,b_t,c_t$ for positions $3t,3t+1,3t+2$, respectively, each
window is equivalent to
$a_t<a_{t+1}<c_t<b_t<b_{t+1}$. These chains force every rank between
$a_0$ and $b_j$. In an actual permutation those two positions therefore
have ranks zero and $3j+1$. Deleting these positions and subtracting one
from every remaining rank gives an exact bijection with the grid $Q_j$.
Its columns are $x_t=a_{t+1}<y_t=c_t<z_t=b_t$, and its two horizontal
chains are the increasing $x_t$ and the increasing $z_t$. In the Lean
indexing, $q(3t+2),q(3t+1),q(3t)$ are $x_t,y_t,z_t$. The inverse adds
one to every grid rank and restores the two forced endpoints. Thus
`count_eq_grid` identifies $A_j$ with `Nat.card (GridPacking j)` for every
$j\ge1$, with no symmetry or labeling factor.

The transfer module defines $b_1(k)=1$ and
$b_{n+1}(k)=\sum_{r=1}^k r b_n(r+2)$ on all natural arguments.
Its universal algebraic results are $b_n(3)=1$ in $\mathbb Z/5\mathbb Z$
for all $n\ge1$, and

$$
b_{n+1}(2k+1)=-\sum_{r=1}^k b_n(2r+1)
 +(2k+1)b_n(2k+3)\quad\text{in }\mathbb Z/4\mathbb Z
$$

for $n\ge1$ and $k\ge0$. The simultaneous odd-argument formal series
are $UV^m$ at argument $4m+1$ and $V^{m+1}$ at argument $4m+3$, where
$C$ is the ordinary Catalan series over $\mathbb Z/4\mathbb Z$,
$V=3C^2-2$ and $U=1+XV$. These series satisfy the complete reduced
recurrence and have constant coefficient one. Coefficient induction
therefore gives

$$
b_j(3)\equiv 3C_j\pmod4\qquad(j\ge2),
$$

with the separate initial value $b_1(3)=1$. The natural-to-residue
row correspondence is proved by induction on the transfer.
The existing binary Catalan theorem supplies the dyadic parity rule.
Together with the modulo-five invariant, it proves the exact modulo-ten
rule for every natural transfer row:

$$
b_j(3)\bmod10=
\begin{cases}1,&j+1=2^k\text{ for some }k\ge1,\\
6,&\text{otherwise.}\end{cases}
$$

Writing $s(m)$ for the sum of the binary digits of $m$, binary induction
proves $s(m+1)+v_2(m+1)=s(m)+1$. Pinned Kummer's theorem and
$(m+1)C_m=\binom{2m}{m}$ then imply $v_2(C_m)+1=s(m+1)$.
The exact characterization of $s(m)\le2$ for $m\ge2$ as
$m=2^i+2^p$, $p\le i$, includes the equal-exponent and exponent-zero
cases. It proves both directions of the modulo-four exception rule for
all transfer rows, with $j\ge1$:

$$
4\nmid b_j(3)\quad\Longleftrightarrow\quad
\exists i,p\in\mathbb N,\ p\le i\ \land\ j+1=2^i+2^p.
$$

The Core module proves `grid_card_eq_row`, identifying $A_j$ with
$b_j(3)$ universally. For an actual grid of $N=3j$ ranks, let $d$ be the
rank of its last $x$ and put $k=N-d$. A new column is specified uniquely
by $0\le r<k$ and $0\le s\le r$. Insert its $z$ as the greatest rank,
then $y$ at rank $b=N-r+s$, then $x$ at rank $a=N-r$. Ordered rank
insertion preserves the old grid. Its new comparisons hold exactly
when $d<a\le b\le N$, and its new state is $r+3$. Conversely, the last
$z$ of every grid has the greatest rank; deleting the three new entries
recovers the unique parent and the parameters $r=N-a$, $s=b-a$.
Thus there are exactly $r+1$ children with state $r+3$ for each
$0\le r<k$. This is a bijection of actual rank assignments.

For any natural $n$, sum `row Nat n` over the states of the actual
$j$-column grids. The bijection turns this sum into the corresponding
sum of `row Nat (n+1)` over the parent grids. The unique one-column grid
has state three. Induction therefore gives
`Nat.card (GridPacking j) = row Nat (j-1) 3` for every $j\ge1$.
No recurrence is assumed for the actual count.

The theorems `count_mod_ten` and `count_mod_four_iff` apply the two
transfer laws through this common equality and `count_eq_grid`.
They prove the two displayed modular conclusions for the actual
permutations at every $j\ge1$, including both exact-exception directions
for modulo four. The printed wording's interpretive limit and the old
narrower proposal remain as stated above. These results carry no claim
of worldwide priority or an exhaustive literature screen.
