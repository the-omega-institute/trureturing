[Index](../../marked_head_profile.md) · [One-coordinate trees](375-deep-prime-prefix-projections-and-tree-contraction.md) · [Extremal original model](../350-extremal-paired-branch-and-source-support.md)

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

[The constructor](../../frontier/fresh_root_constructor.py) accepts the
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

[The weighted-tree program](../../frontier/weighted_prefix_tree_potentials.py)
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
[The existing Hough--Nielsen source bridge](../341-conditional-future-avoidance-controls-the-current-prefix.md)
provides a different route to common supported laws: Theorem 3, equation
(4), of arXiv:1703.02133v2 bounds cylinder probabilities under the uniform
law on the actual residual when its Shearer polynomial conditions hold.
Those positivity conditions are not established here for unrestricted
prime support. PC7 instead uses the minimum-cover transport obstruction,
has consecutive-gap capacities, and does not claim uniformity. The
source bridge, 350, 374 and 375 contain no theorem giving PC1--PC7 in
this full-height chain form; this is a statement of searched scope, not
a literature-priority claim. No Lean declaration is added.
