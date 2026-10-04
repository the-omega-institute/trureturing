[Index](../../../marked_head_profile.md) · [Complementary repairs and exact component holes](861-complementary-phase-repair-and-pair-anchor-rigidity.md) · [Component control](862-three-support-masked-rectangle-control.md)

# Retained pair guards share a four-phase repair

In one globally count-then-modulus-sum minimal distinct odd whole
cover with ternary height two, an actual bottom two-prime class
improves the five-prime four-match capacity from 29 to 21 at its
literal phase. The replacement uses 22 distinct fresh classes and
covers the entire deleted union. Several such retained guards give
the capacities 29, 21, 14 or zero according to their actual phase graph.

These bounds supply deductions in whole-phase-grid incidence sums.
When the guards use cofactor primes, a guarded phase center has no
lift into the exact retained q-free hole. Consequently this result does not improve the pointwise
supplier bound at an actual hole point, and does not supply the
missing upper bound on the component rectangle.

The construction reuses the retained-pure forest and fixed-four-phase
capacity from
[Report385, Section15](../350-399/385-private-congruence-hulls-and-crossed-modulus-closure.md#15-retained-pure-powers-reduce-the-fresh-repair-forest).
Applying that capacity separately to two phases gives 28; the common
three-prime part has only eight divisors and does not satisfy that
forest's divisor-count threshold of greater than ten. The shared
22-class replacement below is the additional arithmetic step. The
guard-graph and packing formulas are its counting consequences.

## One actual cover and one bottom pair guard

Let the original family be a finite cover of the integers by
pairwise distinct odd moduli greater than one. It minimizes the
number of classes, then the sum of moduli, among all such covers.
Assume no original modulus is divisible by 27, and retain the
actual disjoint pure 3 and pure 9 originals.

Choose five distinct primes at least five:

$$
P=\{p,s\}\cup T,\qquad |T|=3,\qquad
t=\prod_{\ell\in T}\ell,\qquad h=pst.
\tag{PG1}
$$

Fix one literal phase vector w on these five primes. For an
original $A_i=[a_i]_{d_i}$, let

$$
M_i(P,w)=\{\ell\in P:\ell\mid d_i,\ a_i\equiv w_\ell\pmod\ell\}.
$$

Write $L_P(w)$ for the number of originals with $|M_i(P,w)|\ge4$,
including all ternary rows, all q-heights when a distinguished q
is present, and q-free originals.

Suppose the original family contains the bottom class of numerical
modulus ps with phase $(w_p,w_s)$. Its modulus must be exactly ps;
higher prime powers or additional factors would not give the same
guard condition.

No qualifying original can match both p and s. Otherwise ps
divides its modulus and its whole AP lies in the retained ps class,
contradicting original irredundancy. The guard itself matches only
two selected coordinates and is not qualifying. Thus every qualifying
original has exactly one of the two matching sets

$$
T\cup\{p\},\qquad T\cup\{s\}.
\tag{PG2}
$$

Each complete original AP therefore lies in

$$
\mathcal R=
\{x:x\equiv w_\ell\pmod\ell\ (\ell\in T),\
       x\equiv w_p\pmod p\ \text{or}\ x\equiv w_s\pmod s\}.
\tag{PG3}
$$

This is a containment of every point of each selected original,
not only its private region or its trace on a chosen mask.

## Twenty-two fresh classes cover the entire liability

The actual pure 3 and pure 9 guards leave fifteen safe roots modulo
27. On eight of them, use one tag e for each divisor $e\mid t$.
On the other seven, use the pair of tags

$$
\{pe,se\}\qquad(e\mid t,\ e<t).
\tag{PG4}
$$

A tag v at root r means the CRT class with modulus 27v, residue r
modulo 27, and the prescribed w-phases at every prime dividing v.
There are eight singleton tags and fourteen paired tags. They are
distinct: the first group contains neither p nor s, and the two
paired groups contain exactly one of these primes. All 22 moduli
are odd nonunits and globally fresh because their ternary height
is three.

At a singleton root, every point of $\mathcal R$ matches the tag.
At a paired root, it matches pe or se according to which of p,s
it matches. The retained pure guards cover every unsafe ternary
root. Consequently the new classes and retained guards cover the
entire union of every deleted qualifying original, at every integer
lift. The bottom ps guard remains retained as well.

The exact new modulus sum is

$$
\Sigma_{\mathrm{new}}
=27\left[\sigma(t)+(p+s)(\sigma(t)-t)\right].
\tag{PG5}
$$

Here $\sigma$ is the sum-of-divisors function. Each of the three
primes in t is at least five, so

$$
\sigma(t)\le(6/5)^3t<2t,\qquad
\Sigma_{\mathrm{new}}<27t(p+s+2)<64t(p+s).
\tag{PG6}
$$

The last strict inequality holds already for $p+s\ge10$.

For completeness, the reused fixed-four-phase cap is 14: if fifteen
originals match four prescribed prime phases, place the fifteen
proper divisors of their squarefree product v on the fifteen safe
roots modulo 27. The resulting fresh classes cover the entire
selected union together with the retained pure guards. Their sum
is $27(\sigma(v)-v)<225v$, while fifteen distinct positive odd
multiples of v have sum at least $225v$. The equal-count replacement
contradicts minimality. This is the fixed-four instance of the
existing retained-pure repair.

If 22 originals qualified in PG2, split them into groups of sizes
k and l according to the two four-phase branches. The reused
capacity gives

$$
k+l=22,\qquad k,l\le14,\qquad k,l\ge8.
\tag{PG7}
$$

Distinct positive odd multiples of pt in the first group cost at
least $ptk^2$; the second group similarly costs at least $stl^2$.
Therefore

$$
\Sigma_{\mathrm{old}}
\ge t(pk^2+sl^2)\ge64t(p+s)>\Sigma_{\mathrm{new}}.
\tag{PG8}
$$

Delete these 22 originals, keep every other original, and add the
22 fresh classes. Whole coverage is preserved, class count is
unchanged, and the modulus sum strictly falls. Hence

$$
\boxed{L_P(w)\le21\quad\text{at a matching actual bottom pair guard}.}
\tag{PG9}
$$

There is no q-bearing restriction or upper bound on the selected
primes in PG9.

## Several bottom guards give one phase graph

Let $B_P(w)$ be the graph on P with an edge $\{r,s\}$ exactly when
the actual original of numerical modulus rs exists and matches w
at both primes. This graph uses retained bottom pair classes; it is
different from Report861's moving pair-anchor graph.

The matching set $M_i(P,w)$ of a qualifying original must be
independent in $B_P(w)$. Its complement, of size at most one, must
therefore meet every edge. Together with PG9, the reused fixed-four
cap 14, and the unguarded cap 29, this gives

$$
L_P(w)\le
\begin{cases}
29,&B_P(w)\text{ has no edges},\\
21,&B_P(w)\text{ has exactly one edge},\\
14,&B_P(w)\text{ has at least two edges, all at one vertex},\\
0,&B_P(w)\text{ has no vertex cover of size at most one}.
\end{cases}
\tag{PG10}
$$

In the third case the omitted coordinate must be that common
vertex, so all qualifying originals share the four other phases.
The fourth case includes two disjoint edges and a triangle. The
cases exhaust all graphs on P.

For a distinguished prime q, write the period as
$Q=9q^G W$ with $(W,3q)=1$. For q-bearing counts with
$P\subseteq\{r:r\mid W\}$ and
$\max P\le q$, Report861 CP7 replaces only the unguarded baseline
by 28. The other capacities remain 21, 14 and zero. Keeping q
outside P is necessary for that separate price comparison.

## Exact deductions on the whole phase grid

On $\prod_{r\in P}\mathbb F_r$, let $V_1,V_\star,V_{\mathrm{bad}}$
count centers with, respectively, exactly one guard edge, at least
two edges with every edge incident to one common vertex, or no
vertex cover of size at most one.
All counts use the same actual original pair phases.

Let $N_{4,r}$ count originals whose numerical support meets P in
exactly $P\setminus\{r\}$, and let $N_5$ count originals whose
support contains all of P. Summing PG10 over the phase grid gives

$$
\sum_{r\in P}rN_{4,r}
+\left(\sum_{r\in P}r-4\right)N_5
\le29h-8V_1-15V_\star-29V_{\mathrm{bad}}.
\tag{PG11}
$$

An original of the first type contributes at r centers. One of
the second type contributes at $\sum_{r\in P}r-4$ centers, counting
the union of its five four-match neighborhoods exactly.

Under the stated cofactor-prime and upper-bound premises, the
q-bearing version is

$$
\sum_{r\in P}rN^+_{4,r}
+\left(\sum_{r\in P}r-4\right)N^+_5
\le28h-7V_1-14V_\star-28V_{\mathrm{bad}}.
\tag{PG12}
$$

On the pure-prime-guard-safe grid, replace h by
$\prod_{r\in P}(r-1)$, each coefficient r by $r-1$, and the
five-support coefficient by $\sum_{r\in P}r-9$. Count the three V
terms on that same restricted grid. This uses actual pure-prime
guards and comparable-original disjointness, as in Report861 CP8.
The inequalities also hold for any fixed subfamily of the counted
originals, with the same whole-grid upper bound.

## Relation to the actual retained hole

When P consists of cofactor primes, every center counted by
$V_1,V_\star$ or $V_{\mathrm{bad}}$ has no completion in $E_0$:
one actual retained bottom pair class covers every such completion.
The guarded capacities consequently do not reduce the pointwise
all-U clique bound at a base actually in $E_0$.

The grid sums instead count partial-match neighborhoods of original
APs. Such neighborhoods can meet the guard locus even though the
actual masked supports $F_i$ do not. Using PG11 or PG12 to control
the rectangle still requires an estimate linking its actual label
inventory to enough of those excluded phase centers. No probability
law supported on $E_0$ is assigned to the guard locus.

Report862's arithmetic control already shows why one component and
many top cells do not supply complete service even at a base inside
that component. Report861 CP13 and its every-color consequence keep
the stronger whole-cover premise explicit. No step here derives a
common replacement assignment for every component, bounds the
rectangle below 390, or settles unrestricted Erdős #7.

## Verification scope

A scoped transient Lean check proves PG9 from an actual integer
whole cover with distinct odd nonunit moduli, no modulus divisible
by 27, global count minimality and equal-count modulus-sum minimality,
the actual disjoint pure 3 and pure 9 guards, and the matching bottom
ps guard. It constructs the 22 CRT classes, checks their distinct
fresh numerical labels, covers the complete selected union, and
reassembles a whole integer cover with every other original retained.
The fixed-four cap 14 and the exclusion of an original contained in
the guard are derived within the check. The exact packet price,
the old-cost lower bound and the final strict descent are checked.
No q-bearing condition or upper prime bound is assumed.

The successful check reports 39 axiom closures, including the reused
29-class baseline; each uses only `propext`, `Classical.choice` and
`Quot.sound`. It applies the pinned finite-set, CRT, product and
ordered-sum results and adds no retained mathematical declaration.
The several-guard graph and phase-packing consequences PG10--PG12,
including their safe-grid versions, remain ordinary deductions in
this verification scope. This is not a full-repository check or a
solution of the simultaneous replacement problem.
