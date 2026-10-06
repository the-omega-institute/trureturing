[Index](../../../marked_head_profile.md) · [Matched source capture](874-matched-prime-families-and-whole-source-capture.md) · [Actual cut capacity](864-complete-color-covers-and-phase-product-obstruction.md#a-prime-bipartition-repairs-the-entire-deleted-union)

# Semiprime obstructions and repairs without the pure label

Keep the conditional actual-cover branch of Reports871--874:
global cardinality and then modulus-sum minimality, maximal ternary
height two, q=113 of height one, and period 9qW with W coprime to 3q.
The q-free originals leave the exact residual E0 on 9W. All 113
literal q-colors cover this same E0 after stripping q. Let P be the
prime support of W, with r=|P| at most 27. None of these conditions
is asserted for every hypothetical odd distinct cover.

There is a single set of at most 54 actual top originals whose
omission from repair demand removes every rooted semiprime K4.
At least 59 entire original colors remain available. On the resulting
two-matching-prime sectors, a different local repair avoids the pure
numerical label 27. Its count still requires additional captured
originals; it is not a global paid repair of E0.

The graph-coloring input is an application of a published theorem.
The pair-selection exchange and its actual prime-cut application have
scoped Lean checks. The coloring input and complete arithmetic repair
chain below are ordinary mathematical derivations; their full Lean
verification is not claimed here.

## A hereditary indexed density bound and its coloring consequence

Fix one old word z and one auxiliary root phi_p modulo each p in P.
For each selected actual top original 9qm_i, choose two distinct
matching primes p_i,t_i dividing m_i. Thus its literal phase rho_i
agrees with phi at both chosen primes. Different owners remain
different indexed edges, even when they choose the same prime pair.

Report864 PC57--PC64 applies to every induced vertex set of this
one indexed graph, and gives

$$
2|E(S)|\le3|S|\qquad(S\subseteq P).
\tag{KR1}
$$

This applies to every allowed pair selection. Only auxiliary roots
are fixed: they need not describe a point of E0 or a common point of
all the original cofactor classes.

Kostochka--Yancey, *Ore's conjecture on color-critical graphs is almost
true*, JCTB 109 (2014), 73--101,
[DOI 10.1016/j.jctb.2014.05.002](https://doi.org/10.1016/j.jctb.2014.05.002),
Theorem 4 on printed page 76, proves that a finite simple 4-critical
graph H satisfies

$$
3|E(H)|\ge5|V(H)|-2.
$$

Together with KR1 this forces |V(H)| at most four. A 4-critical
graph on four vertices is K4. Therefore the underlying simple graph
of a K4-free indexed graph satisfying KR1 is three-colorable.
Passing to the underlying simple graph only decreases edge counts;
parallel indexed owners are not discarded from any arithmetic count.
This is reuse of the published critical-graph bound, not a new
coloring theorem or a claimed Lean implementation of that theorem.

## One global omission removes the semiprime obstructions

A rooted semiprime K4 consists of a four-prime set S contained in P
such that all six actual originals with labels 9qpt, for unordered
pairs {p,t} in S, have one common old word and compatible literal
roots at each prime in S. Their q-colors may differ. The actual
originals determine the old word and these roots, so a given S
specifies at most one such configuration.

Two different configurations cannot share two or more primes.
A shared pair {p,t} identifies the same actual original 9qpt,
by uniqueness of the original numerical labels. It therefore fixes
the same old word and the roots at p and t in both configurations.
If three primes are shared, their shared pair originals identify
all three roots. The two root assignments can consequently be
combined on their union. Unique factorization identifies distinct
prime pairs with distinct semiprime labels.

Sharing two vertices would give eleven indexed edges on six
vertices; sharing three gives nine edges on five vertices. Both
contradict KR1. Sharing four primes specifies the same configuration.
Thus the four-prime supports form a linear set family. For any
fixed prime, the other three primes in configurations containing it
are disjoint between configurations. If b0 is the total number of
configurations, incidence counting gives

$$
4b_0\le r\left\lfloor\frac{r-1}{3}\right\rfloor,
\qquad b_0\le54\quad(r\le27).
\tag{KR2}
$$

Choose one actual original from each configuration and let O be
the resulting set. This choice is made once, independently of z,
phi and any later source point. Then

$$
|O|\le54,
\qquad
\#\{\text{whole literal colors avoiding }O\}\ge59.
\tag{KR3}
$$

Every untouched color still covers the same E0. Here O is excluded
from a family used to generate repair demand. This does not retain
O as a background guard or change E0: a proposed final deletion
of all q-bearing originals must still repair the original E0.

### A complete-color sector with no low-support top anchors

With the additional earlier exponent cap Omega(W) at most 77 from
Report864 PC34, at most 78 actual top originals have cofactor one
or a prime power. Hence at least 35 whole q-colors contain no such
top original. Choose a fixed set of 35 of these colors.

No rooted semiprime K4 is monochromatic. If all its six owners had
one q-color, the q-versus-prime cut of Report874 MF5 would bound
their number by at most five. For every configuration wholly in
the chosen 35 colors, choose two distinct represented colors and
put an edge between them. The resulting simple graph has at most
54 edges. The standard random-order independent-set bound and
Cauchy--Schwarz give an independent set of size at least

$$
\frac{35^2}{2\cdot54+35}=\frac{1225}{143}>8.
$$

Thus at least nine whole colors can be selected whose top cofactors
all have at least two distinct prime factors and whose union has
no rooted semiprime K4. They still cover E0 after stripping q,
using all their original rows. This does not remove lower-row
obligations. The premise concerns Omega(W), not the smaller
individual bound Omega(m_i) at most 25.

## Changing selected prime pairs removes avoidable K4s

Let A be a nonempty set of actual top owners at z, across arbitrary
q-colors. For each owner let R_i be its matching primes under phi,
and assume |R_i| at least two. Choose one pair in each R_i so that
the number of K4s in the underlying simple graph is minimum.
The choice space is finite and nonempty.

KR1 implies that the K4s of any such graph are vertex-disjoint.
It also implies that each K4 has exactly six indexed edges on its
vertices, so none of its edges has a parallel owner.

Suppose a K4 edge uv belongs to owner i and some w in R_i differs
from u and v. Change only that owner's selected pair to uw.
If w belongs to the same four-vertex set, the old K4 disappears
and no new simple edge is added. Otherwise a newly created K4
would have to contain uw. Let t be its intersection size with the
old four-vertex set. Then t is one, two or three. The old K4 minus
uv still has five edges, so their union has at least

$$
11-\binom t2\text{ edges on }8-t\text{ vertices}.
$$

For t=1,2,3 this gives respectively at least 11/7, 10/6 and 8/5
edges/vertices, each contradicting KR1. Hence no new K4 appears.
The number of K4s strictly decreases, contradicting minimality.
Every owner on a remaining K4 therefore has exactly two matching
primes. In particular,

$$
\forall i\in A,\ |R_i|\ge3
\quad\Longrightarrow\quad
\text{some allowed pair selection is K4-free}.
\tag{KR4}
$$

The density premise is available for the changed pair selection
as well as the original one. A density condition for only one
initial graph would not justify this exchange.

## A fixed local repair with no pure output

Assume A contains no rooted semiprime K4, as holds when A avoids
O. Put k=|A| and M=sum_i m_i. In each remaining K4 of the minimum
selection, some edge owner i has

$$
d_i=p_it_i<m_i.
\tag{KR5}
$$

Otherwise all six anchors would be exactly its six semiprime
products, giving the forbidden configuration. Select one such
exceptional owner per K4 and remove its edge. The resulting graph
is K4-free and satisfies KR1, so choose a proper three-coloring
gamma of its prime vertices. Each removed edge's endpoints have
the same color: they are the nonadjacent vertices of the remaining
K4 minus one edge. They are both adjacent to its other two adjacent
vertices.

Use these fixed outputs, interpreting gamma as the next ternary digit:

* For each used prime p, the label 27p has ternary residue
  z+9 gamma(p) modulo 27 and cofactor phase phi_p modulo p.
* For an ordinary owner i, its selected primes have different
  colors. Give 27m_i the third digit and literal phase rho_i.
* For an exceptional owner i, its two primes have a common digit.
  Give 27m_i and 27d_i the other two digits, retaining rho_i
  modulo m_i and d_i respectively.

CRT supplies the complete residues. For each owner, its full
cofactor class is covered at all three new ternary digits. Hence
the outputs cover every integer lift of {z} times U_A, with one
fixed assignment of all phases and digits.

The labels are distinct. Prime labels differ from all composite
anchors and exceptional products. The actual anchors are distinct.
Exceptional products are distinct because their K4s have disjoint
vertex sets. Finally d_i cannot equal another selected anchor m_j:
that anchor would have exactly the two primes p_i,t_i, forcing its
selected pair to repeat an edge of the original K4. The resulting
seventh indexed edge contradicts KR1. Also d_i is proper in its
own anchor. All labels are odd nonunits and have ternary valuation
three, so they are fresh against all original labels.

Let v be the number of used primes and b the number of exceptional
owners. The output count is

$$
B=k+v+b\le40+27+6=73,
\tag{KR6}
$$

since 2k at most 3v and 4b at most v. Each prime is used by at
least one selected pair, and p_i+t_i at most m_i. Thus the prime
image sum is at most M. Also sum_exceptional d_i at most M. The
modulus sum is consequently

$$
27\left(\sum_{\rm used\ p}p+M+\sum_{\rm exceptional\ i}d_i\right)
\le81M<9\cdot113M.
\tag{KR7}
$$

If every |R_i| is at least three, KR4 gives b=0 and the sum bound
improves to 54M. Report864 PC77 additionally gives 6k at most 7r
in this case, so k at most 31. Hence B at most 58, using the
existing three-matching-prime bound rather than only k at most 40.

## Capture and simultaneous composition have explicit boundaries

Use the complete all-row capture set D_A^{all} from Report874
MF4a, with the same target {z} times U_A. It contains A, and the
simultaneous deletion hole lies in the fixed repair target. KR7
pays the modulus sum. The two-stage minimum therefore implies

$$
|D_A^{\rm all}|\le B-1\le72.
\tag{KR8}
$$

In the three-matching-prime case the bound is 57. Since there are
at least 105 top originals at z, U_A still cannot contain all of
X_z. The bounds concern mixed colors; they are not numerical
improvements of the one-color 55/30 bounds under their different
hypotheses. Deleting only the k selected owners does not pay B.

Several such blocks can be combined when their numerical prime-tag
sets are pairwise disjoint and their selected original sets are
disjoint. Their old words and roots may differ. Prime labels are
separated by the tag condition, and anchor labels by original
uniqueness. An exceptional product from one block cannot equal an
anchor of another: that anchor's selected pair would then use the
first block's primes. Exceptional products from different blocks
are also different by unique factorization. Thus the fixed output
families are jointly legal and their counts and sums add.

This composition rule does not establish that a source-covering
family of blocks with these disjoint resources exists. Overlapping
prime resources still compete for the single numerical label 27p
and its one allowed old word and phase. Lower-row and one-matching-prime
source packets still require treatment. The pure label 27 has been
removed from this local construction; full compatible coverage and
count payment for E0 remain unproved, as does unrestricted Erdős #7.

## Exact verification boundary

`PairSelectionRerouting` proves the finite minimum-selection rigidity
statement and the existence of a rigid selection. Its hereditary
density hypothesis ranges over every legal pair selection. An exact
transient application starts with the actual count-then-modulus-sum
minimal odd distinct cover, no original modulus divisible by 27,
selected original labels 9*113*m_i at one old word, and their literal
matching-prime sets, each containing at least two primes. It derives
the required cut capacities from
`PrimeCutOwnerCapacity`, derives hereditary indexed density through
`BipartiteSubgraphDensity`, and applies the new selection theorem.
Thus density is not an unproved extra premise in that application.
The three-matching-prime K4-free conclusion is included. These
scoped checks use only the standard three axioms.

The same exact selection application also compiles at arbitrary ternary
height h and multiplier q at least seven. Its selected labels are
3^h*q*m_i, their actual residues share one word modulo 3^h, no
original label is divisible by 3^(h+1), and every selected original
has at least two primes matching the fixed auxiliary roots. The
prime pool can be any finite set of primes. No q-primality,
q-height-one, common-q-color, common-source-point or 27-prime bound
is used for this density-to-rigid-selection conclusion. The numerical
54/59 and 73/58 estimates elsewhere retain their stated special-branch
conditions; this wider interface does not extend those estimates or
provide a global repair.

Separate transient applications verify the finite linear-four-set
incidence bound 54 and the 113-color complement bound 59. They retain
linearity and the four-element supports as premises. An additional
exact actual-source application supplies these premises: it forms the
four-prime configurations directly from actual semiprime originals,
uses the unique original numerical labels to identify their shared
old words and roots, and applies the actual density bound to prove
that distinct supports intersect in at most one prime. Equal supports
force equal old words modulo nine and equal roots modulo every
support prime, so arbitrary extensions of the root functions are
not counted as different configurations.

The application then constructs one fixed set O of at most 54 actual
originals, with actual pair-label witnesses for each chosen original
and for the hit in every configuration. At least 59 colors avoid O.
It explicitly retains as a premise that each original literal color
has a q-stripped cover of the same exact q-free residual E0; under
that premise each remaining color has its complete surviving cover.
The prime pool and its bound of 27 are also explicit inputs. This
complete counting application compiles with the standard three axioms.
It does not prove those branch inputs for every hypothetical cover
or assert a whole-cover realization of an arbitrary linear set family.

The scalar implication from 6k at most 7*27, v at most 27,
B=k+v and capture less than B to k at most 31, B at most 58 and
capture at most 57 also compiles. This does not verify
the complete supplier chain for KR5--KR8. In particular the published
three-colorability input, the nine-color refinement, the full fixed
CRT repair and simultaneous composition are not presented as one
end-to-end Lean proof. Neither the checked density-to-selection
bridge nor the finite counts supply a source-covering global phase
assignment.
