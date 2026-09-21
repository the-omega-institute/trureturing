[Index](../../../../Problems/erdos-7-odd-covering-systems.md)

# Incidence pseudoforests with arbitrary original heights and support sizes

This extends the
[incidence-forest construction](48-incidence-forests-with-arbitrary-original-heights.md)
to one cycle per connected component. The support size of an individual
original modulus remains unbounded, so its ordinary prime co-occurrence
graph may contain arbitrarily large cliques. These are ordinary
mathematical deductions with exact finite regression calculations, not
new Lean theorems or a solution of unrestricted Erdős #7.

## Statement

Take a finite family of congruence classes of pairwise distinct odd
numerical moduli greater than one. Its grouped incidence graph has a
vertex for each occurring prime, a vertex for each distinct original
prime support of cardinality at least two, and an edge for membership.
Assume each connected component of this bipartite graph has at most
one cycle. Then the family does not cover the integers.

Furthermore there is a probability nu supported on the actual full
survivor set, with nu<=K H for original full CRT Haar H, where K depends
only on this finite incidence graph and its primes, not on any original
exponent or residue. Consequently full Haar survivor mass is at least
1/K. The existing arbitrary-tail consumer for such a joint density
gives a computable prime cutoff, uniform in all head exponents and
residues, beyond which completely unrestricted original classes cannot
complete this head. The cutoff is not claimed small.

Forest components use Chapter 48, Sections 1--4. It remains
to prove the statement for one connected component with one cycle.

## 1. Retain the actual cyclic separator

The unique cycle alternates between prime vertices and support vertices.
It has at least two prime vertices. Retain the whole cycle. If prime 3
belongs to the component but lies off the cycle, also retain its unique
path to the cycle, including whichever prime or support vertex this path
first meets. Let K be the set of retained prime vertices and let E_core
be the retained support vertices.

Every remaining incidence component is a tree attached at one retained
vertex. All unretained primes are at least 5. Every core support has
two retained prime neighbours, except possibly the support first met
by the path from 3: if that path meets a SUPPORT vertex, this one
support has three retained prime neighbours. This case must not be
silently replaced by a two-prime relation.

A core support E consists exactly of its retained primes C_E and its
private child primes T_E. Distinct such child sets and all hanging tree
interiors are disjoint; any additional intersection or connection would
create a second incidence cycle. Noncore support vertices each have
one parent prime and one or more child primes when rooted away from
the retained subgraph.

Every original pure-power class stays at its prime vertex. Every mixed
original class stays in its exact support group with its original full
exponent vector and residue. No projected moduli are merged.

## 2. Prune hanging trees and quantify the core domains

Use the incidence-forest recursion of Chapter 48, Sections 1--3, on all
noncore support vertices. At every prime q remove its actual pure-power classes and
the exceptional sets of its noncore child supports, calling the
remaining domain S_q. Core support constraints are not deleted here.

The original exponent-layer argument supplies, for a noncore support
with parent q and child set T,

    c_T=product_{r in T}1/(r-1),  D_T=product_{r in T}(r-3),
    B_E={x_q:sum_i w_i 1_{A_i}(x_q)>=(D_T-1/4)c_T},
    H_q(B_E)<=4 q^{-(D_T-1)}/[3(q-1)].

Its success provides an ACTUAL simultaneously allowed child tuple set
of Haar mass greater than c_T/4, once each child's descendant domain
has mass at least (r-3)/(r-1). Summability over distinct representative
child primes closes that induction as in the forest proof.

For every q>=5, including retained primes, it gives

    delta_q:=H_q(S_q)>=d_q
      :=1-1/(q-1)-4q/[3(q-1)(q^2-1)].                (U1)

These d_q exceed 1/2 and in particular exceed (q-3)/(q-1).
If 3 is retained then delta_3>=1/4. If ALSO 5 is a retained prime,
the representative-prime sum at root 3 cannot use 5. Removing that
term gives the stronger bound

    delta_3>=1/4+(2/3)3^{-1}=17/36.                 (U2)

Other excluded representatives would improve the bound further, but
are not needed. All these domains are actual subsets of the original
prime-power coordinates. No assumed distribution on a projected
survivor set is substituted for them.

For q>=5 put b_q=1/[(q-1)d_q]. For a retained 3 use b_3=2 unless 5
is retained, in which case use b_3=18/17. These are upper bounds on
the total positive-exponent cylinder-cap weight under H_q(.|S_q).
The first values are

    b_5=18/49, b_7=36/173, b_11=90/799, b_13=126/1373. (U3)

The function d_q increases and b_q decreases for real q>=5. For the
latter, its reciprocal is q-2-4q/[3(q^2-1)], whose derivative is
1+4(q^2+1)/[3(q^2-1)^2]>0. The two subtracted terms in d_q decrease.
Since d_15=723/784, all remaining primes can be bounded by the larger
set of odd integers at least 15, giving

    sum_{q>=5 prime} b_q^2
     <= b_5^2+b_7^2+b_11^2+b_13^2
         +(784/723)^2*(1/196+1/28)
     =11181700024618215281126396/45205949340120622379111289
     <1/4.                                         (U4)

The final two terms bound sum_{n>=0}(14+2n)^{-2} by its first term
plus its decreasing-function integral. This bound is independent of
the number of original primes or exponent heights.

## 3. One common core source and actual joint extension sets

Use the single product probability

    rho=product_{q in K}H_q(.|S_q).

It is not asserted to be the marginal of Haar conditioned on full
global survival. It is an explicitly selected source on actual domains.

For a core support E with no private child prime, simply let B_E be
the union of its actual original classes on its retained coordinates.
Distinct full exponent vectors and the actual product cylinder caps
give

    rho(B_E)<=product_{q in C_E} b_q.               (U5)

For a core support with nonempty private set T=T_E, retain every
original class i and write w_i for the Haar mass of its child part.
At retained tuple x let L_E(x) be the sum of w_i over precisely those
original classes whose retained-coordinate conditions match x. Set

    B_E={x:L_E(x)>=(D_T-1/4)c_T}.

The complete original exponent inventory gives

    E_rho L_E <= c_T product_{q in C_E} b_q.

This sums every positive exponent at every retained and private prime,
using at most one original class per complete numerical modulus. It
does not assume uniqueness of projected child moduli. Markov yields

    rho(B_E)<=[product_{q in C_E} b_q]/(D_T-1/4)
              <=product_{q in C_E} b_q,             (U6)

since every private prime is at least 5 and D_T>=2. More significantly,
at every x outside B_E the ACTUAL allowed private tuple set in
product_{r in T}S_r, avoiding all active originals, has Haar mass
greater than c_T/4. This follows by subtracting L_E from its available
volume at least D_T c_T.

All (U5)--(U6) use the SAME rho. We will condition only once, on avoiding
all these actual core bad sets. The success assertion is a simultaneous
extension of the entire private tuple, not separate coordinate promises.

## 4. The joint core bad probability is less than 9/10

Two-prime core supports contribute at most b_q b_r each. Keep parallel
edges if the incidence cycle has two prime vertices: they are two
different original support groups. For any such multigraph, the sum
of b_q b_r over its edges is at most one half the degree-weighted sum
of b_q^2, by 2b_qb_r<=b_q^2+b_r^2.

If 3 is absent from the component, the retained graph is the cycle on
its prime vertices, possibly with two parallel edges. Its degrees are
two and (U4) bounds the total by 1/4.

Suppose 3 lies ON a cycle with at least three prime vertices. Its two
neighbours are distinct. If one is 5, (U2) and monotonicity give the
two incident terms at most (18/17)(18/49+36/173). After removing 3,
the remaining edges have degree at most two, so (U4) adds at most 1/4.
If neither neighbour is 5, use 2(36/173+90/799)+1/4 instead. The
respective rational upper bounds are

    495325/576436 <9/10,
    492899/552908 <9/10.                             (U7)

If 3 lies on the cycle with exactly two prime vertices, both support
groups have the same other retained prime q, and there are no further
core edges. Their sum is at most

    2(18/17)(18/49)=648/833<9/10 if q=5,
    4(36/173)=144/173<9/10 if q>=7.                  (U8)

This pays both original support groups. Any private-rank saving in
(U6) is optional and has not been needed to obtain the strict gap.

Finally suppose 3 is OFF the cycle. If its path first meets a prime
vertex, the retained prime-edge graph is a cycle with a path attached.
Prime 3 is a path endpoint. Remove its one incident edge; every other
prime has degree at most three. Hence their total is at most 3/8 by
(U4). The incident edge costs at most (18/17)(18/49) if its neighbour
is 5, and at most 2(36/173) otherwise. Thus the total is at most

    5091/6664<9/10, or 1095/1384<9/10, respectively. (U9)

If the path first meets a SUPPORT vertex E, this support has retained
primes t,q,r: t is the path-side neighbour, and q,r are its two cycle
neighbours. Both q,r are at least 5. Equations (U5)--(U6) charge at
most b_t b_q b_r<=b_t b_q because b_r<=1. For the SCALAR ESTIMATE
only, replace E by the edge t--q and drop the factor b_r. The other
cycle supports form the path q...r, so the estimated graph is a path
from 3 to r. Every retained prime is still sampled under rho, and every
original E-label remains in the actual B_E and extension set. This is
only a valid bound on its rho-mass, not a modification of the original
constraint system. Degrees after removing 3 are at most two, hence
certainly at most three, and (U9) remains valid.

The cases exhaust the connected incidence-unicyclic component. Thus

    rho(union_{E in E_core}B_E)<9/10.               (U10)

## 5. Full extension, uniform density and arbitrary tails

Condition rho once on avoiding this whole union. Its positive normalizer
is greater than 1/10. For each core support with private primes, sample
uniformly from its actual allowed child tuple set. Then extend all
noncore descendant support groups with the forest kernels. No two
generated branches share an unretained prime; hence every original
class is avoided by the resulting full joint probability nu.

Put m=|K| and h=the total number of distinct nonsingleton support groups
in this connected component. Every retained coordinate domain has
Haar mass at least 1/4. The once-conditioned initial density is therefore
at most 10*4^m. Every group introducing new coordinates has a conditional
density at most 4 product_{r introduced}(r-1). There are at most h such
groups, and every unretained prime is introduced exactly once. Thus

    nu<=K_U H,
    K_U=10*4^{m+h} product_{r not in K}(r-1).        (U11)

The true constant can be smaller; (U11) is a simple sufficient bound.
It contains no original height or residue. It is derived from full-history
conditional kernel bounds and cannot be obtained merely by multiplying
unconditional marginals.

The full actual survivor mass is at least 1/K_U. For a disconnected
incidence pseudoforest, take the product of these independent component
laws and the existing forest-component laws. Their primes and original
classes are disjoint, so this yields the claimed global probability,
density bound and noncoverage.

The arbitrary-tail consumer is Chapter 48, Section 6, applied to the
source nu<=K H: uniformly lift to all extra old-coordinate heights
and to unused primes at most a chosen p_k. Use

    kappa=K product_{odd p<=p_k}(1+(3p-1)/(p-1)^2).

Once kappa<=k(log k+loglog k-3)^2, BBMST's original-label second-moment
hypothesis and continuation apply to any additional original classes
with largest prime greater than p_k. A suitable k is computable and
exists because the product grows only as O((log k)^4). This retains
the actual common source and permits arbitrary later support, exponents
and residues. The cutoff depends on the finite head graph and primes,
not their heights or residues.

## Limits and comparison

This is a genuine cyclic-separator result: two support groups can share
two prime coordinates and are paid under one joint law before a single
conditioning. Each may have arbitrarily many private primes with
arbitrary hanging incidence trees. No claim is made for two cycles
in one connected incidence component. There the retained scalar graph
can have higher degrees, or several shared-coordinate hyperedges, and
the uniform 9/10 bound above no longer follows from (U4).

Existing ordinary prime-graph unicyclic and cactus results are reused
as motivation and scalar techniques, not as a theorem covering this
larger-rank class. The current proof explicitly establishes both the
new simultaneous private extension and the height-independent complete
Haar density needed by its unrestricted-tail consumer. Public-literature
novelty has not been verified.


## Exact regressions and source boundary

The companion
[incidence_unicyclic.py](../frontier/cover-geometry/incidence_unicyclic.py)
checks (U4) and every rational bound (U7)--(U9) exactly. It also rebuilds
two literal original families, their grouped incidence graphs, the unique
cycle, any path from 3, every pruned domain, every actual allowed tuple
set, and the full generated joint probability. It uses only the Python
standard library and explicit checks that remain active under `-O`.

| Original family fixture | Period | Original classes | Core source points | Good core points | Full original survivors | Maximum generated density | Proved density cap |
| --- | ---: | ---: | ---: | ---: | ---: | --- | ---: |
| Two shared primes, rank-four support and hanging edge | 45045 | 10 | 24 | 21 | 14958 | 195/59 | 7372800 |
| Path from 3 first meets a support vertex | 15015 | 7 | 48 | 47 | 5638 | 2145/799 | 1228800 |

Both generated joint probabilities have exact total mass one. The first
fixture keeps both original support groups sharing primes 3 and 5,
and original height two at prime 3. The second has cycle primes 5 and 7
and a support with all three retained primes 3, 5 and 7. Their actual
core losses are 1/8 and 1/48, respectively; the original-inventory
same-source union bounds are 1965/8128 and 34055/734976.

These finite checks exercise parallel cyclic support groups,
simultaneous private extension and the three-retained-prime meeting
case. They do not establish arbitrary support size, arbitrary heights or
the infinite analytic continuation; those assertions rest on the proof
above, Chapter 48's induction and its stated BBMST analytic supplier.

The retained exact output is
[incidence_unicyclic.json](../certificates/source_norms/cover-geometry/incidence_unicyclic.json).
From the repository root, replay it with

```sh
python3 -B -I -S -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/incidence_unicyclic.py --check
```
