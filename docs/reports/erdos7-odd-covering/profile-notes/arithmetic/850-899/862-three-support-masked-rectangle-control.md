[Index](../../../marked_head_profile.md) · [Exact-hole component codes](850-cofactor-dependent-protected-codes.md#components-inside-the-exact-retained-family-hole) · [Phase caps](861-complementary-phase-repair-and-pair-anchor-rigidity.md) · [Experiment](../../../frontier/cover-geometry/three-support-masked-control/verify_masked_control.py)

# A three-support masked rectangle with full collision control

An explicit family of 3518 distinct odd arithmetic progressions has
numerical divisor closure, a private point for every original, all
415 cells of the full available digit/word rectangle in one exact-hole
component, and no literal collision edge in any of Report385's GLC1
graphs. Its complete joint phase counts also obey the bounds in
Report861. The family is an actual **NONCOVER**, and its whole-cover
all-U fibre premise fails. Thus these inventory, connectivity and
phase constraints alone do not supply the missing whole-cover relation.

The results here are ordinary mathematical deductions and exact
finite computations; no Lean verification is asserted. The top
cap four and star cap three are already consequences of
[Report385, Section 172](../350-399/385-private-congruence-hulls-and-crossed-modulus-closure.md#172-literal-prime-root-collisions-have-one-fixed-exceptional-pair-across-all-sources).
The contribution here is the explicit arithmetic control satisfying
the stronger collision condition and the full available rectangle.

## Complete arithmetic encoding

Put $q=113$, $G=10$, and let the safe old ternary words be
$\mathcal A=(2,4,5,7,8)$. Use primary and auxiliary primes

$$
\begin{aligned}
P&=(19,23,29,31,37,41,43,47,53,59,61,67,71,73,79),\\
B&=(5,7,11,13,17,83,89,97,101,103,107,109).
\end{aligned}
$$

The full prime support is exactly the odd primes through 113, all
cofactor exponents are one, and

$$
W=\prod_{p\in P\cup B}p,\qquad Q=9q^{10}W.
\tag{MR1}
$$

Include the pure guards $[0]_3$ and $[1]_9$. Include all thirty
unit-cofactor moduli $3^a q^j$, where $a=0,1,2$ and $1\le j\le10$.
Their q-residue is $3(j-1)+a\pmod{q^j}$, with all higher digits zero;
their present ternary coordinates equal the old word four. Their
first q-digits are exactly $0,\ldots,29$. Hence the entire available
complement is

$$
U=\{30,\ldots,112\},\qquad |U|=83.
\tag{MR2}
$$

For each nonempty $S\subseteq P$ with $|S|\le3$, include all six
moduli $3^a q^j\prod_{p\in S}p$, where $a=0,1,2$ and $j=0,1$.
Assign the 455 triples in lexicographic order cyclically to the 415
cells $U\times\mathcal A$, ordered first by digit and then by word.
Assign the 120 singleton and pair supports, ordered first by size
and then lexicographically, injectively to the first 120 cells of
$\{3,\ldots,29\}\times\mathcal A$. Denote the assigned cell by
$(c_S,z_S)$. Present q-coordinates equal $c_S\pmod q$; present
ternary coordinates equal $z_S\pmod{3^a}$.

For $|S|\le2$, every $p\in S$ has literal residue

$$
\rho_p=1+a+3j+6(|S|-1).
\tag{MR3}
$$

For triples, let $t_{j,S,p}\in\{0,1,2\}$ be the saved color in
[phase_colors.json](../../../frontier/cover-geometry/three-support-masked-control/phase_colors.json).
Set $(\delta_0,\delta_1,\delta_2)=(1,2,0)$ and use

$$
\rho_p=13+3j+\bigl(t_{j,S,p}+\delta_a\bmod3\bigr).
\tag{MR4}
$$

Finally, for every $p\in B$, include $3^a p$, $a=0,1,2$, with
p-residue $a$ and present ternary coordinates equal to four. CRT
determines each original residue uniquely modulo its numerical label.

The raw prime-p classes have phase one for $p\in P$ and zero for
$p\in B\cup\{3,q\}$. Subtracting one global CRT translation,
equal to one at every primary prime and zero modulo $9q^{10}$ and
at every auxiliary prime, normalizes all prime classes to zero.
This preserves privacy, intersections, phase counts and noncoverage.
The saved numerical witness below uses the raw encoding.

## Privacy, divisor closure and the exact masked graph

Every numerical label is a distinct odd nonunit. Its nonunit divisors
are in the displayed palette. The checker also generates the divisors
from each numerical modulus and verifies this closure directly.

A primary-supported original has a private point with its own phases
on $S$, zero at the other primary primes, three at every auxiliary
prime, and old word $z_S$. For $j=1$, choose q-coordinate $c_S+q$
modulo $q^{10}$; this misses any deeper unit original with the same
first digit because its second digit is zero. For $j=0$, choose
$30+q$. Unit originals use their own full q-phase, primary zero and
auxiliary three, with old word four; the pure guards instead use
their own ternary residues and q-coordinate $30+q$. Auxiliary originals
use their own auxiliary phase, three at all other auxiliary primes, primary zero,
old word four and q-coordinate $30+q$.

The phase bands separate different support sizes and q-strata.
Outside the chosen support, primary zero misses every primary test;
on the chosen support, the three ternary rows have different phases
at every prime. These facts give privacy. The checker verifies each
private integer against every original and separately verifies all
67,123 comparable numerical pairs.

Let $E_0\subseteq\mathcal A\times\mathbb Z/W\mathbb Z$ be the exact
hole left by retaining every q-free original. For each moving owner,
let $R_i$ be its support on these preserved coordinates and
$F_i=R_i\cap E_0$, as in Report850 CD17. The moving owners are exactly
the 1365 q-bearing triple-supported originals; 455 are top originals.

Any two moving supports $S,T$ admit a triple $V\subseteq P$ disjoint
from both: their union uses at most six of the fifteen primary primes.
The moving bottom owner on $V$ meets each endpoint inside $E_0$.
For either intersection, choose an old word allowed by the endpoint,
the two disjoint supports' moving phases, zero at every other primary
prime, and three at the auxiliaries. Moving phases lie in $\{16,17,18\}$,
whereas q-free primary phases lie below 16; the pure guards and
auxiliary originals also miss this point. Thus the actual $F_i$
intersection graph is connected and has diameter at most two.

The same construction with one moving support shows that masking
preserves all of its literal old-word availability: all safe words
for a bottom owner, the matching residue modulo three for a middle
owner, and $\{z_S\}$ for a top owner. All three rows on a triple
have the same q-digit and compatible old-word tests. Every cell of
$U\times\mathcal A$ is occupied in this one component, so all 83
digits are saturated in the rectangular inventory of Report850 CD21.

## Full collision and joint phase checks

For every old word and every pair of distinct nonternary primes,
including q, at most one top original has any prescribed pair of
literal first phases. The generator enforces capacity one for the
triple layers; the remaining supports have separate phase bands.
The checker reconstructs all keys directly from numerical moduli
and residues, across every cofactor source and q-height. There are
4530 distinct keys, each with multiplicity one. Consequently all
full GLC1 collision graphs are edgeless, for every distinguished
nonternary prime and first root.

The phase queries are counted jointly across q-free and q-bearing
originals. For three primary primes, top rows capable of matching
two coordinates use the exact residue classes
$0,9,12,13,14,15,16,17,18$, where zero represents all other residues.
For triples containing q, all 113 q-residues and the corresponding
primary phase classes are enumerated. A triple containing auxiliary
primes reduces to a checked two-prime key or has no qualifying top
original. These reductions exhaust the nonternary three-prime tests.

Every original has at most three cofactor primes, so no original
qualifies for four matches among five cofactor primes. A five-set
including q can qualify only a q-bearing triple original. If all
four remaining primes are primary, the checker enumerates the four
possible triple supports and their phases. If an auxiliary prime
is included, at most one triple support can qualify, with at most
one ternary row at fixed phases.

| Exact check | Result |
| --- | ---: |
| Originals, each with a checked private point | 3518 |
| Moving owners / moving top owners | 1365 / 455 |
| Occupied top digit/word cells | 415 |
| Maximum top labels per digit/word cell | 2 |
| Maximum top two-prime phase multiplicity | 1 |
| Full GLC1 collision edges | 0 |
| Joint top two-of-three maximum, three primary primes | 3 |
| Joint top two-of-three maximum, including q | 3 |
| All-row four-of-five maximum, five cofactor primes | 0 |
| All-row four-of-five maximum, including q | 2 |

The three-primary calculation has 315,028 nonzero finite query
classes. The complete result data are in
[result.json](../../../frontier/cover-geometry/three-support-masked-control/result.json).
The self-contained
[generator](../../../frontier/cover-geometry/three-support-masked-control/generate_phase_colors.py)
uses fixed seeds and at most 27 color candidates per triple;
the checker consumes the adjacent saved color file.

From the experiment directory, check the saved fixture with
`python3 verify_masked_control.py`; it prints the result JSON.
Regenerate the color file separately with
`python3 generate_phase_colors.py`. The checker requires ordinary
Python execution and rejects optimized mode, which disables assertions.

## Exact noncoverage and the missing all-U premise

CRT with old word four, primary coordinates zero, auxiliary
coordinates three, and q-coordinate $30+q\pmod{q^{10}}$ gives

```text
x = 15390356347217026029419002673646663556111502730863140910604472468
Q = 142436894702683084318748228942613663999266333047287974862394302405
```

The checker verifies $x\notin A_i$ for every original. Its preserved
base lies in $E_0$. At that same base, every moving cofactor test
fails because all primary coordinates are zero. This failure holds
for **every first digit in U and every higher q-suffix**. Unit
originals and the other q-bearing originals have protected first
digits outside U. Thus no member of the family covers any of these
sources, and the whole-cover all-U fibre implication used in
Report850 fails at this base.

That base is outside $V_C=\bigcup_{i\in C}F_i$. The all-U service
premise behind [Report861 CP13](861-complementary-phase-repair-and-pair-anchor-rigidity.md#exact-deletion-hole-of-a-masked-component)
also fails **inside $V_C$**. Choose the first moving original in the
displayed ordering: the bottom owner on $S=\{19,23,29\}$, namely
$[868887]_{1432049}$, with first q-digit 30. Its checked private
integer and the result of changing only that digit to 31 are

```text
x_private = 99810725828278043765703319081413689572492821843207557305020026468
x_switch  = 8551316190380655425330380521964433050544856165624416690919171143
```

The checker verifies that their common preserved base lies in $E_0$
and in exactly one moving preserved support, that of the chosen
original. Hence it belongs to $V_C$. The two integers agree modulo
$9W$ and have the same higher q-suffix; both first digits belong
to U. The first integer belongs only to the chosen original, while
the second belongs to no original. Component membership and a
complete component rectangle therefore do not supply service at
every moving digit even on the component's own union of supports.

## An expanded first-digit control

The same numerical palette also admits a control with a height-one
owner in **every ternary row at every first q-digit except zero**.
It retains all 415 moving digit/word cells and satisfies SC468, yet
still fails whole coverage and the common-base all-U service relation.
Thus the 112-color inventory bounds and their combined 111-color
three-row bounds do not by themselves supply that relation.

Among the cyclically assigned triple supports, eight cells
$(c,2)$ with $30\le c\le37$ have a second owner group. Change the
assigned first q-digit of the following five complete cofactor groups;
keep their old word equal to two and keep every primary-prime phase:

| Cofactor support | Old first q-digit | New first q-digit |
| --- | ---: | ---: |
| $\{47,67,73\}$ | 30 | 1 |
| $\{53,59,61\}$ | 31 | 2 |
| $\{53,61,67\}$ | 32 | 27 |
| $\{53,67,73\}$ | 33 | 28 |
| $\{59,61,67\}$ | 34 | 29 |

Only the fifteen q-bearing APs change their numerical residues: the
three q-free rows in each group retain exactly their old APs. Every
numerical modulus, every old ternary coordinate and every cofactor
coordinate is unchanged. The new word two avoids the original 3q
root one at first digit one, and the original 9q word four at first
digit two. At first digits 27, 28 and 29, the private-point formula
uses q-coordinate $c+q$, which misses the deeper unit original with
second digit zero. Each old cell retains its first assigned group.

Put $C=\{1,\ldots,112\}$ and $V=C\setminus\{1\}$. Directly from
the numerical moduli and residues, all 112 colors of C have actual
height-one owners in rows zero, one and two. In particular their
minimum-row counts are $(112,0,0)$, and all 111 colors of V have all
three rows. These owners need not have a common cofactor phase.

The 107 colors $\{3,\ldots,26\}\cup U$ still have every safe word
realized by a same-cofactor triple $qm,3qm,9qm$, with all three first
q-digits equal and with compatible middle-root and top-word tests.
Only $\{2,27,28,29\}\subset V$ lack a complete five-word inventory.
Every six-subset of V therefore contains a complete color. Any safe
word assignment on that six-set selects an actual SC468 triple at
that color; the extra 9q word restriction only reduces the permitted
assignments. This verifies the full q=113 SC468 condition for this
control, not merely its row-count consequences.

The delta checker reconstructs all 4530 literal top two-prime keys;
their maximum multiplicity remains one. It also enumerates the
17,150 nonzero top two-of-three phase queries at the five new colors,
whose maximum is two. At other q-colors no matching q-incidence is
added, so the saved global upper bound three remains valid. At a new
color, an all-row four-of-five query can use only the one moved
triple support. Its three row phase vectors are distinct, giving
upper bound one there and preserving the saved global upper bound
two. All non-q phase queries are unchanged, including the 315,028
saved nonzero three-primary query classes.

The checker verifies all 105,315 affected private-point/owner relations
and all 450 affected comparable-modulus pairs. The other relations
are identical to the original fixture. The numerical divisor palette
is unchanged. There are now 1350 moving owners on 450 triple supports,
including 450 moving top owners. For any two moving supports, at least
$\binom{9}{3}-5=79$ available triple supports remain disjoint from
both, so the same phase-band argument keeps the masked graph connected
with diameter at most two. All 415 moving cells remain occupied.

Both displayed uncovered integers are checked against the expanded
family. The saved private integer still has its unique original owner,
and changing its first digit from 30 to 31 still yields the displayed
uncovered integer with exactly the same preserved base and higher
q-suffix. Its base remains inside the actual component union. Hence
the common-base service failure persists even after the expanded row
inventories and SC468 hold together.

The shared arithmetic constructor is
[control_model.py](../../../frontier/cover-geometry/three-support-masked-control/control_model.py).
The original checker retains its original default family and result.
Run `python3 verify_expanded_colors.py` from the experiment directory
to check the expanded variant; its exact data are in
[expanded_result.json](../../../frontier/cover-geometry/three-support-masked-control/expanded_result.json).
The checker pins the saved phase and result inputs and the full
ordered sequences of original numerical APs and private witnesses. It
reuses unchanged relations and verifies all affected relations and
new q-phase query classes. These are finite arithmetic checks and the stated counting
deductions; no complete Lean verification of either 3518-class
fixture is asserted.

This is an actual NONCOVER and is not EB1. It is not a counterexample
to any result assuming whole coverage. It separates the listed
inventory and phase constraints from that missing joint premise;
no claim is made that it satisfies every other necessary consequence
of EB1. The unrestricted covering problem remains unresolved.
