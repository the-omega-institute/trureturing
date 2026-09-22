[Index](../../marked_head_profile.md) · [One-coordinate trees](375-deep-prime-prefix-projections-and-tree-contraction.md) · [Extremal original model](../321-384/350-extremal-paired-branch-and-source-support.md)

# Complete prime-coordinate chains and one common survivor law

Whole-coordinate transport avoids the separator collision that arises
when only a lowest digit moves. In a globally minimum-class-count
distinct odd cover, let q<p<s be support primes. The actual q-free
residual must meet every product of a complete q-ary tree through the
entire p coordinate and a complete p-ary tree through the entire s
coordinate. Otherwise the complete p coordinate can move to q, and
the complete s coordinate can move to the vacated p coordinate,
producing a smaller whole distinct odd cover.

The product-tree obstruction also gives one probability on the actual
residual controlling every selected prime prefix simultaneously. Its
capacities use consecutive prime gaps along the chain. A weighted
tree argument verifies all fractional covering inequalities needed
by finite linear-programming duality; separate marginal laws alone
would not do this.

This works when the prime support is an initial segment. No additional
fresh prime is required. Full original heights, literal residue
prefixes, and the same old witness for every original event are kept.
It is an ordinary mathematical deduction, not a new Lean theorem or
a resolution of unrestricted Erdős #7.

## 1. A full-height chain has injective numerical labels

Let C be a whole cover with n distinct odd nonunit moduli, globally
minimum in class count. Choose support primes

    q<p_1<...<p_t, t>=1,
    Q=q^h B, B=M product_i p_i^H_i,
    gcd(M,q product_i p_i)=1.

Let C0 be all q-free originals, m=|C0|<n, and let R_q be their actual
uncovered region in Z/B. Put lambda_1=q and lambda_i=p_(i-1) for i>1.
For each i choose a complete lambda_i-ary subtree of depth H_i in
the lowest-digit-first p_i tree. Write its prefix-compatible injections
as theta_(i,a): Z/(lambda_i^a) -> Z/(p_i^a), 0<=a<=H_i.

Suppose the product of these selected leaf sets misses the actual
joint projection of R_q. On the new carrier

    N=M product_i lambda_i^H_i,

use one old witness y for each new point z, defined by

    y mod p_i^H_i = theta_(i,H_i)(z mod lambda_i^H_i),
    y mod M = z mod M.                               (PC1)

All new prime coordinates are distinct and coprime to M. This map
is a bijection onto the chosen product of old full-coordinate leaf
sets, together with every M coordinate. Every image point is covered
by C0 because it lies outside R_q.

An original q-free modulus has the unique form

    d=r product_i p_i^alpha_i,
    gcd(r,q product_i p_i)=1.

If any original residue prefix a_d mod p_i^alpha_i is absent from
theta_(i,alpha_i), discard that original. Otherwise let b_i be its
unique inverse and output the single CRT class with

    z=b_i mod lambda_i^alpha_i for every i,
    z=a_d mod r,
    d'=r product_i lambda_i^alpha_i.                  (PC2)

Conditions at exponent zero are vacuous. Prefix compatibility makes
PC2 exactly the preimage of that original event under PC1.

The map d -> d' is injective: each output valuation at lambda_i
recovers alpha_i, and removing those factors recovers r. In
particular, for t=2,

    p^alpha s^beta r -> q^alpha p^beta r.             (PC3)

The new p exponent belongs entirely to the old s coordinate. There
is no remaining old p tail competing for that exponent, since all
of the old p coordinate moved to q. This is why p can act as the
second separator even though it was originally present.

All output moduli are odd and nonunit. One original produces at
most one output, no closing classes are added, and every z is
covered by the output of an original covering the common point y.
Therefore

    n_out <= m < n,                                  (PC4)

contradicting minimum cardinality. Hence R_q meets every stated
product of complete trees. Divisor closure, original pure-prime
classes, and comparable disjointness are not needed.

This does not justify substituting partial tails into PC2: if an
old p tail is retained while p also encodes s, their exponents can
merge. Here alpha_i ranges through every original height and is
preserved as a complete prefix depth at its new prime.

## 2. A genuine joint exclusion, including the cross obstruction

For two support primes p<s above q, let

    S=projection_(p^H,s^K)(R_q).

Then S meets every product T_p x T_s, where T_p is complete q-ary
of depth H and T_s is complete p-ary of depth K. This is a condition
on the actual joint source, not a product of marginal cardinalities.

As a first consequence, R_q cannot lie inside the union of one
first-p-digit cylinder and one first-s-digit cylinder. Choose the
first q branches in the p tree avoiding the first cylinder, and
the first p branches in the s tree avoiding the second; the strict
prime inequalities give enough branches. Continue each tree at all
remaining levels. Their product would miss R_q.

More generally, for subsets A of p roots and D of s roots,

    R_q subset {x_p in A} union {x_s in D}
       implies |A|>=p-q+1 or |D|>=s-p+1.             (PC5)

Indeed, otherwise the complements have at least q and p roots,
respectively, and support a forbidden tree product.

Thus the actual even cross example in 375 cannot occur in a minimum
odd cover: there R_3 lies in {x_5=0} union {x_7=0}. Its legitimate
even class-count descent is compatible with this conclusion.

## 3. Weighted prefix potentials

For a p-ary tree of depth H, put r=p-q+1. Give a prefix of length
a the capacity r^(-a). Assign arbitrary nonnegative prices w_u to
all prefixes u, including the root, and define

    f(x)=sum_(u prefix of x) w_u,
    C=sum_u w_u r^(-length(u)).                      (PC6)

There is a complete q-ary depth-H subtree on which every leaf has
f(x)<=C. Indeed, if every such tree met the bad set {f>C}, that bad
set would contain a complete r-ary subtree by the duality in 375.
The uniform law on its leaves has prefix masses at most r^(-a),
and hence expectation E f<=C. But every leaf of that subtree has
f>C, giving E f>C, a contradiction.

This works for overlapping prefixes, all original depths, zero
prices, and the root. In particular, a prefix union with total
capacity below one misses a complete q-ary tree: give its prefixes
unit prices, and observe that f>=1 on their union.

## 4. One probability controls the entire selected prime chain

Keep the chain of section 1 and put

    r_i=p_i-lambda_i+1,
    lambda_1=q, lambda_i=p_(i-1) for i>1.

There exists one probability nu supported on the actual R_q such that

    nu(x=c mod p_i^a) <= r_i^(-a)
      for every i, every c, and 0<=a<=H_i.           (PC7)

This is a common law for every prime in the selected chain, rather
than a separate law for each coordinate. For i>1 its cap uses the
consecutive difference p_i-p_(i-1)+1, not p_i-q+1. The stronger
individual caps in 375 cannot simply replace these gaps.

To prove the claim, use nonnegative variables mu_x for x in actual
R_q. Maximize sum_x mu_x subject to the prefix constraints

    sum_(x in R_q with prefix u at p_i) mu_x <= r_i^(-length(u)).

The root constraint bounds total mass by one. The zero vector is
feasible, so this finite rational linear program is feasible and
bounded. Its dual assigns nonnegative prices w_(i,u) to prefixes,
minimizes

    sum_i C_i, C_i=sum_u w_(i,u) r_i^(-length(u)),

and requires the leaf scores to satisfy

    sum_i f_i(x mod p_i^H_i) >= 1 for every x in R_q,
    f_i(v)=sum_(u prefix of v) w_(i,u).               (PC8)

If a dual feasible solution had cost sum_i C_i<1, section 3 would
give, in every coordinate i, a complete lambda_i-ary tree on all of
whose leaves f_i<=C_i. Section 1 says their product meets the joint
projection of actual R_q. At a witness x of this intersection,
PC8 would give

    1 <= sum_i f_i(x mod p_i^H_i) <= sum_i C_i < 1,

a contradiction. Therefore every dual feasible solution has cost
at least one. Pricing one root by one and everything else by zero
is dual feasible with cost exactly one. Finite linear-programming
strong duality now gives primal optimum one, attained by a probability
nu satisfying PC7. All coefficients are rational; a rational optimum
can also be chosen. No integrality of a multi-coordinate matching or
probabilistic independence is assumed.

All C0 events have nu-mass zero because the variables are actual
survivor points. The other M coordinates may be correlated. The law
is not asserted to be Haar or uniform on R_q. For an AP involving
several selected primes, PC7 supplies the minimum of the applicable
marginal caps; multiplying them remains unjustified.

For the pair q=3,p_1=5,p_2=s this gives simultaneous caps 3^(-a)
and (s-4)^(-b). For the initial segment 3,5,7,11,13, the common law
on R_3 has respective prefix bases 3,3,5,3 at 5,7,11,13. These gap
caps are weaker than the separately available bases 3,5,9,11.
Other original primes and all heights remain unrestricted. Different
chosen chains can produce different laws; their strongest coordinate
bounds cannot be pooled as though the laws were identical.

## 5. Scope

The source in this proof is the original q-free residual. Transport
preserves its selected-branch C0 event vector through one common
witness and changes the carrier; it does not preserve the complete
original Haar law or the removed q-bearing events. The probability
from PC7 is newly constructed on actual R_q and cannot be substituted
for Haar in an existing Haar-budget identity without a new argument.

The full-height chain closes the particular missing-separator issue
for joint product trees and supplies the specific common law PC7.
It does not show that every family of stronger prime-prefix caps
admits a common law or establish an all-prime budget
contradiction. Unrestricted Erdős #7 remains unresolved.

## 6. Exact finite controls and existing theorem boundary

[The constructor](../../frontier/cover-geometry/fresh_root_constructor.py) accepts the
complete original family and explicit prefix maps at every original height.
It rejects incomplete, noninjective, out-of-range or noncommuting maps and
products meeting the actual residual. An independent simultaneous CRT
formula checks the common source against every original q-free event; the
output constructor uses pairwise CRT. Coverage alone is not the transport
criterion. Complete input and output periods, numerical-modulus
distinctness, nonunit moduli, source bijection and full cofactor fibres
are checked explicitly. The program does not certify minimality or search
for the supplied trees.

The four whole-cover controls are even and therefore do not instantiate
the unknown minimum odd-cover premise:

| Control | Original to output classes | Output period | Original-event coordinates |
|---|---:|---:|---:|
| The actual 375 cross, chain 3<5<7 | 24 to 17 | 1920 | 36480 |
| The cross with heights H_5=3, H_7=2 | 27 to 20 | 86400 | 1900800 |
| One link 3<5 at complete height four | 24 to 17 | 9072 | 163296 |
| Three links 3<5<7<11 | 26 to 19 | 13440 | 282240 |

Together these check 110832 source points and 2382816 original-event
coordinates. The height-four one-link output agrees with 375. The
unequal-height example retains exponents 1,2,3 at 5 and 1,2 at 7;
its three added originals map to (21 mod 27), (20 mod 25), and
(439 mod 900). Seven rejection controls include a full-layer permutation
which preserves domain, range and injectivity but violates truncation.
The declared finite-check cap is 3000000; exceeding it is a program
limitation, not a rejection of the unrestricted mathematical map.

[The weighted-tree program](../../frontier/cover-geometry/weighted_prefix_tree_potentials.py)
independently enumerates all 27 complete binary subtrees of a ternary
depth-two tree. It verifies PC6 for all 4096 binary prefix-price assignments
(76 attain equality) and 27 nonuniform rational assignments. A four-leaf
blocker has correct budget one and meets every selected tree, while the
incorrect p^(-depth) pricing gives only 4/9. This is a combinatorial
control of the weighted lemma; its branching number two is not an odd
prime separator. These finite calculations complement the proofs above
and do not prove the general statements by enumeration.

The one-coordinate duality is reused directly from 375. Standard finite
linear-programming strong duality supplies the last step of PC7.
[The existing Hough--Nielsen source bridge](../321-384/341-conditional-future-avoidance-controls-the-current-prefix.md)
provides a different route to common supported laws: Theorem 3, equation
(4), of arXiv:1703.02133v2 bounds cylinder probabilities under the uniform
law on the actual residual when its Shearer polynomial conditions hold.
Those positivity conditions are not established here for unrestricted
prime support. PC7 instead uses the minimum-cover transport obstruction,
has consecutive-gap capacities, and does not claim uniformity. The
source bridge, 350, 374 and 375 contain no theorem giving PC1--PC7 in
this full-height chain form; this is a statement of searched scope, not
a literature-priority claim. No Lean declaration is added.

## 7. Joint tree intersections and common marginal laws do not tensorize

The following obstruction retains the new product-tree condition as well
as the stronger one-prime conditions from 375. Put

    S={(i,i),(i,i+1): 1<=i<=4} subset Z/5 x Z/7.      (PC9)

Every three-row by five-column rectangle meets S: three rows include at
least two of the four active rows, and any two active rows have at least
three neighbors. The complement of five columns has only two elements.
The projections have four and five elements, so they also meet every
three-element set in the respective coordinate.

Give the two endpoints (1,1),(4,5) mass 1/5 each and the six remaining
points mass 1/10 each. This is one probability with row masses
(3/10,1/5,1/5,3/10) and five column masses equal to 1/5. In particular,
it satisfies the stronger simultaneous one-coordinate caps 1/3 and 1/5.
Nevertheless no probability on S can give every pair mass at most 1/9:
the eight pair boxes partition S and their total allowed mass is 8/9.
This is a finite dual obstruction to multiplying even the weaker PC7
caps 1/3 and 1/3.

The failure persists at arbitrary depths in the relation domain. For
H,K>=1 take the inverse image of S modulo 5^H and 7^K, keeping all tail
digits. It meets every product of a complete ternary 5-tree and complete
five-ary 7-tree. The displayed root law, extended by uniform independent
tails conditional on the root pair, has prefix masses at most

    (1/3) 5^(-(a-1)) <= 3^(-a),
    (1/5) 7^(-(b-1)) <= 5^(-b).

The same eight root boxes still forbid the joint cap 1/9. Additional
prefix depths therefore do not by themselves remove this obstruction.
This lifted relation is not asserted to come from a minimum odd cover.

### A whole distinct even cover realizes the eight-point source

This is also an actual-residue obstruction, not only an abstract
relation. Let D=2^15. Take the following original classes:

* the 15 classes 2^(j-1)-1 mod 2^j, 1<=j<=15;
* the three pure classes 0 mod 3, 0 mod 5, 0 mod 7;
* enumerate the 16 pairs in ({1,...,4} x {1,...,6}) minus S in
  lexicographic order by e=0,...,15; for pair (i,j), use its CRT class
  x=i mod 5, x=j mod 7, x=-1 mod 2^e;
* enumerate the 16 triples (i,j,k), (i,j) in S and k in {1,2},
  lexicographically by e=0,...,15; use their CRT classes with the
  additional condition x=-1 mod 2^e.

Their odd modulus parts are respectively 1, the pure primes, 35 and
105, so all 50 numerical moduli are distinct. The dyadic classes cover
everything outside x=-1 mod D. On that last fibre the pure 5 and 7
classes remove the zero roots, the 35 classes remove the complement
of S, and pure 3 plus the 105 classes cover what remains. The full
period is 105D=3440640. Removing all 3-bearing originals leaves exactly

    R_3={x mod 35D: x=-1 mod D, (x mod 5,x mod 7) in S}. (PC10)

Each non-dyadic class has a private witness on x=-1 mod D: use its
own distinct grid cell, choosing the other coordinates to avoid the
pure classes. For a dyadic class indexed j, use the last listed inside
triple (4,5,2) and the dyadic residue 2^(j-1)-1 mod D. Only the last
inside class could cover that triple, and it requires all 15 low bits
to be one. Thus this cover is irredundant.

[The exact checker](../../frontier/cover-geometry/joint_prefix_path_obstruction.py)
checks the entire period, all 50 private witnesses, PC10, all 210
three-by-five rectangles, and the common law. Its actual 5-free
residual also has all six nonzero roots modulo 7, so the other
nontrivial odd-prime chain test is satisfied. The eight joint boxes
can even be written as queries with distinct numerical moduli
35*2^e, e=0,...,7, already present among the original moduli: enumerate
S and give each pair its CRT residue with x=-1 mod 2^e. Each query
cuts out one point of R_3. These are alternate-residue queries, not
original forbidden events; every original 3-free event has zero
mass on R_3.

The example is even, not divisor-closed (for instance modulus 6 is
absent), and not globally minimum. It refutes only the implication
from the stated tree intersections, common marginal caps, and even
irredundant AP provenance to multiplicative joint caps. It neither
contradicts PC7 nor refutes a stronger result using the full odd
minimum-cover hypotheses. Such additional arithmetic is still needed
for the unrestricted joint-load argument.

## 8. Pair mixing gives a stronger joint-prefix bound

There is a refinement of the common marginal bounds when six laws are
supported on the six pairs of four rows. It controls a row and a prefix
under one probability. The refinement alone does not give a root
second moment at most four.

Let `nu_ij`, `1<=i<j<=4`, be any six probabilities, each supported on
rows `{i,j}`. There exist nonnegative weights `lambda_ij` summing to one
such that, for their mixture `nu`,

\[
 a_r=\nu(\text{row }r),\qquad
 \theta_r=\sum_{\{i,j\}\ni r}\lambda_{ij},\qquad
 \theta_r+2a_r=1\quad(1\le r\le4).
 \tag{PC11}
\]

To prove existence, make one column for each pair `{i,j}`. Its two
nonzero entries are `1+2p` at row `i` and `3-2p` at row `j`, where
`p=nu_ij(row i)`; both lie in `[1,3]` and their sum is four. By finite
Farkas duality, it suffices to show that a vector `y` with negative
coordinate sum has negative scalar product with some column. Reorder
its coordinates so that `y_1<=y_2<=y_3<=y_4` and use the column for
the two smallest coordinates. For some `1<=c<=3`, its scalar product is

\[
 cy_1+(4-c)y_2\le y_1+3y_2
                 \le y_1+y_2+y_3+y_4<0.
\]

Thus the vector of four ones belongs to the cone of the six columns.
Summing its coordinates forces the cone coefficients to sum to one,
and its coordinate equations are exactly PC11. Rational input row
masses permit rational weights. No positivity or uniqueness of the
individual weights is required.

Since `a_r<=theta_r`, PC11 gives `a_r<=1/3`. Suppose in addition that
all six laws bound every specified depth-`j` prefix by `c_j`. Only
pair laws containing row `r` can contribute to a joint row-prefix
event. The same mixture therefore satisfies, simultaneously,

\[
 \nu(\text{prefix})\le c_j,\qquad
 \nu(\text{row }r,\text{ prefix})
 \le\min\{a_r,(1-2a_r)c_j\}.
 \tag{PC12}
\]

For `R` in `{1,2,3,4} x Z/7^K`, assume each pair of row fibres
contains a complete ternary tree of depth `K`. Choose one such tree
per pair, label each leaf by an available row in that pair, and use
uniform leaf mass. Then `c_j=3^(-j)` at every depth `0<=j<=K`, giving

\[
 \nu(\text{row }r,\text{ depth-}j\text{ prefix})
 \le\min\{a_r,(1-2a_r)3^{-j}\}
 \le\frac1{3^j+2}.
 \tag{PC13}
\]

The last inequality follows by intersecting the increasing bound `a_r`
with the decreasing bound `(1-2a_r)3^(-j)`. At a fixed positive row
mass it improves the marginal estimate `min(a_r,3^(-j))` precisely
when `a_r>1/(3^j+2)`. All caps here belong to the constructed mixture;
they are not attached to the possibly different law supplied by PC7.
For a source meeting every ternary-5 by five-ary-7 product tree with
row zero absent and 5-height one, the pair-tree premise follows by
using 5-roots `{0,i,j}` and the tree duality of report 375. There is no
standalone five-ary 7-tree hypothesis in PC11--PC13.

### A fixed family of pair laws can still force a root cost of 22/5

At `K=1`, use uniform mass on each of these three-point sets:

| Pair | Points supporting its law |
| --- | --- |
| `12` | `(1,0),(2,1),(2,2)` |
| `13` | `(1,0),(3,1),(3,2)` |
| `14` | `(1,0),(4,1),(4,2)` |
| `23` | `(2,0),(3,1),(3,2)` |
| `34` | `(3,0),(4,1),(4,2)` |
| `24` | `(4,0),(2,1),(2,2)` |

Each is a labelled ternary tree. The weights `lambda_1i=1/5` and
`lambda_23=lambda_34=lambda_24=2/15` satisfy PC11 and give

\[
 (a_1,a_2,a_3,a_4)=(1/5,4/15,4/15,4/15),\qquad
 (\theta_1,\theta_2,\theta_3,\theta_4)=(3/5,7/15,7/15,7/15).
 \tag{PC14}
\]

All three occupied columns have mass `1/3`, and row 1 lies entirely
at `(1,0)`. Taking the divisor-5 event to be row 1, the divisor-7
event to be column 0 and the divisor-35 event to be `(1,0)` gives

\[
 \mathbb E_\nu(1+1_{\text{row }1}+1_{\text{column }0}
                    +1_{(1,0)})^2
 =1+3/5+1+9/5=22/5>4.
 \tag{PC15}
\]

This obstruction holds for every mixture of these fixed six laws
that satisfies PC11: their incident laws always put one third of
their mass in row 1, so `a_1=theta_1/3`; PC11 forces `theta_1=3/5`
and `a_1=1/5`. Every pair law gives column 0 mass `1/3`.

For the displayed weights, `22/5` is also the full maximum over all
1,225 independent root layouts. This is not a source-level obstruction
to a better probability: uniform mass on the nine points in rows
2, 3, 4 and columns 0, 1, 2 has root maximum four. The source has only
three 7-roots, so it contains no complete five-ary tree even at depth
one. The example therefore leaves open what can be gained by combining
the pair refinement with a supported five-ary-tree law.

The affine identity and prefix consequence above are ordinary
mathematical arguments. The finite values in PC14--PC15 and both full
root maxima were independently checked with exact rational arithmetic;
no Lean certification or unrestricted covering conclusion is claimed.
