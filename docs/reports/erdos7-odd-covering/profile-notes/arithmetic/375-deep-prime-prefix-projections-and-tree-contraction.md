[Index](../../marked_head_profile.md) · [First-root descent](374-extremal-prime-projections-and-cardinality-descent.md) · [Extremal original family](../321-384/350-extremal-paired-branch-and-source-support.md)

# Deep prime-prefix projections of a minimum odd cover

Suppose a finite distinct odd covering system exists, and choose one
with globally minimum class count. For support primes q<p, let R_q
be the actual region avoiding all q-free originals on the complete
q-free cofactor carrier. For every 1<=k<=v_p(Q),

    |projection_(p^k)(R_q)| >= (p-q+1)^k.             (DP1)

There is a stronger structural statement: the complement of this
projection cannot contain an embedded complete q-ary tree of depth k
in the lowest-digit-first p-ary prefix tree. The q selected children
may differ from node to node. A forbidden subtree would give a whole
distinct odd cover with strictly fewer classes, using one common
source map and preserving every remaining higher digit.

Equivalently, the projection itself contains a complete
(p-q+1)-ary depth-k subtree. At full depth this supplies a probability
on the actual R_q with controlled mass on every p-power cylinder.
The probability may depend on p; simultaneous control at all primes
requires a separate common-measure argument.

This extends 374's first-root bound. It needs no original prime
class, divisor closure, universal cofactor, or bound on prime-power
heights. It is an ordinary mathematical proof, not a new Lean theorem
or a solution of unrestricted Erdős #7.

## 1. Complete fibres and the blocked-tree count

Let the original cover have n classes and full period

    Q=q^h B, B=p^H M, gcd(M,pq)=1, h,H>=1.

Let C0 contain all original classes whose moduli are q-free, and put

    m=|C0|<n,
    R_q=(Z/B Z) minus the union of C0,
    D_k=projection_(p^k)(R_q).

The inequality m<n holds because q belongs to the original support.
Minimum cardinality also makes R_q nonempty: otherwise C0 itself
would be a smaller distinct odd cover.

Use a p-ary tree of depth k, reading base-p digits from lowest to
highest. Call a leaf bad exactly when its residue belongs to D_k.
A good leaf therefore represents an entire old p^k fibre covered
by C0, including all higher p digits and every M coordinate.
Call a nonleaf good when at least q of its children are good;
otherwise call it blocked. A leaf is blocked exactly when it is bad.

Induction on remaining depth shows that a node is good exactly when
it contains a complete q-ary subtree whose leaves are all good.
If a depth-j node is blocked, at least p-q+1 children are blocked.
Starting with one bad leaf at depth zero, induction gives

    number of bad descendant leaves >= (p-q+1)^j.    (DP2)

This combinatorial bound is sharp: at every blocked node choose
exactly p-q+1 blocked children, apply the same construction inside
them, and leave the other q-1 child subtrees completely good. The
number of minimum blockers at depth k is

    binom(p,p-q+1)^(1+(p-q+1)+...+(p-q+1)^(k-1)).    (DP3)

Sharpness here concerns arbitrary tree blockers. No realization of
every such blocker as R_q in a minimum odd cover is asserted.

Arbitrarily selecting q^k covered leaves is insufficient. For
p=3,q=2,k=2, distributing five good leaves as (3,1,1) among the
three first-level branches leaves only one good child of the root.
There is no binary depth-two subtree. Prefix compatibility is what
keeps lower-height original classes from splitting into several
output classes with the same modulus.

## 2. One common source map for the selected subtree

Suppose a complete good q-ary depth-k subtree exists. Its child
choices give injections

    theta_j: Z/(q^j) -> Z/(p^j), 0<=j<=k,

which commute with truncation: theta_(j+1)(b) reduced modulo p^j
equals theta_j(b mod q^j). Each theta_j encodes a selected path in
the old tree. The choices may depend on the preceding path; they
need not be the same digit injection at every node.

On the complete new carrier of size

    N=q^k p^(H-k) M,

define one old cofactor point y from each new point z by CRT:

    y=theta_k(z mod q^k)+p^k(z mod p^(H-k)) mod p^H,
    y=z                                           mod M.       (DP4)

This is a bijection onto the union of the selected complete old
p^k fibres. Those fibres miss R_q, so C0 covers every image y.
Every old event is evaluated at this same y.

## 3. Each original contributes at most one output class

Write an original class of C0 as a mod p^alpha r, with gcd(r,pq)=1.
There are three cases.

* alpha=0: keep the original a mod r unchanged.
* 1<=alpha<=k: discard the class if a mod p^alpha is outside the
  image of theta_alpha. Otherwise let b be its unique inverse and
  output the class specified by z=b mod q^alpha and z=a mod r.
  Its modulus is q^alpha r.
* alpha>k: put a0=a mod p^k. Discard the class if a0 is outside the
  image of theta_k. Otherwise let b be its unique inverse and output
  the class specified by

      z=b              mod q^k,
      z=(a-a0)/p^k     mod p^(alpha-k),
      z=a              mod r.

  Its modulus is q^k p^(alpha-k) r.

For alpha<=k, prefix compatibility makes this a single congruence
class, even when selections differ across nodes. For alpha>k, the
literal tail (a-a0)/p^k is essential. Reusing a as the tail would
change original-event membership.

Every unchanged output is q-free; every transported output contains
q. Within the alpha<=k case, the q exponent and q-free factor recover
alpha and r. Within the alpha>k case, the positive p exponent and
remaining factor recover alpha and r. The two transported cases are
disjoint because only the latter contains p. Thus the modulus map
is injective. Original pure p powers may become pure q powers;
there are no added closing classes to collide with them.

All output moduli are distinct, odd, and greater than one. At every
z the output event of each retained original equals its membership
at y in DP4; a discarded original is false throughout this image.
Since C0 covers every y, the output covers its entire carrier. Each
original in C0 contributes at most one class, and hence

    n_out <= m < n.                                  (DP5)

This contradicts global minimum cardinality. No good subtree exists;
DP2 at the root proves DP1. For k=1 this is exactly the first-root
construction of 374. For k=H no old p tail remains, and each surviving
modulus p^alpha r becomes q^alpha r.

## 4. A dual subtree and a supported probability for one prime

Put r0=p-q+1. The blocked-root conclusion has more content than
DP1: select r0 blocked children at every blocked nonleaf. At depth k,
all selected leaves are bad. Thus

    D_k contains a complete r0-ary depth-k subtree.   (DP6)

Conversely, such a bad subtree meets every complete good q-ary tree:
at each level q+r0=p+1 forces the two child sets to intersect.
Following intersections reaches a leaf which cannot be both good
and bad. This proves the equivalence with the obstruction used above.

Take k=H. For every selected leaf xi choose one actual point
x_xi in R_q whose p^H coordinate is xi. These witnesses are distinct.
Put mass r0^(-H) on each of them and call this probability nu_p.
For every residue c and every 0<=a<=H,

    nu_p({x : x=c mod p^a}) <= r0^(-a).              (DP7)

Indeed a p^a cylinder either misses the selected tree or contains
exactly r0^(H-a) of its leaves. All witnesses lie in the same actual
R_q, so every q-free original has nu_p-mass zero. More generally,
an AP with a p^a factor, 0<=a<=H, has mass at most r0^(-a), since its other
congruence conditions can only restrict that cylinder.

This is an existence construction of a probability supported on
actual survivors. It is not the original Haar probability and need
not be uniform on R_q. The witnesses may have strongly correlated
other coordinates. The quantifiers are

    for each p>q, there exists nu_p satisfying DP7,

not one nu simultaneously satisfying all these prime-cylinder bounds.

## 5. What the transport preserves and the remaining joint question

The original q-bearing classes are explicitly removed before the
construction. Every remaining original is constant on the full old
q fibre, so passing to B loses none of the events of C0. Uniform
measure on the new carrier corresponds to uniform measure on the
selected union of old complete fibres, including its joint C0 event
vector. It is not uniform measure on the whole original period, and
the q-bearing event vector is not transported.

In the extremal odd model whose support starts at 3, DP1 gives

    |projection_(p^k)(R_3)| >= (p-2)^k, p>3.          (DP8)

For example, the required counts at depth two are at least 9 modulo
25 and at least 25 modulo 49. These are necessary conditions on the
same hypothetical actual residual, not independent distributions or
a construction of that residual.

Projection counts cannot be multiplied to obtain a joint CRT volume.
Nor does DP8 alone give an all-height positive lower density: its
normalized bound is ((p-2)/p)^k, which tends to zero with k. The
remaining unrestricted question concerns simultaneous prime
coordinates and the actual original-label constraints. The proof
does not settle that joint obstruction.

### An actual residual can forbid a common balanced probability

Consider these 24 distinct classes, given as (residue, modulus):

    (0,2), (1,4), (3,8), (7,16), (15,32), (31,64), (63,128),
    (3,5), (9,10), (5,7), (13,14),
    (1,35), (51,70), (31,140), (151,280), (127,560),
    (1087,1120), (2047,2240), (767,4480),
    (0,3), (895,1920), (511,2688), (575,960), (959,1344).

They form an irredundant whole cover of period 13440. Removing all
3-bearing originals gives the exact residual modulo 4480

    R_3={255,511,1407,1535,2815,3455,4095}.

Its joint (mod 5, mod 7) projection is the cross

    {(0,j):0<=j<5} union {(1,0),(2,0)}.               (DP9)

The individual projection sizes are 3 and 5, meeting DP1 with
q=3. Every odd support prime has height one here; the other odd pair
q=5,p=7 has four residual roots, also meeting its required bound 3.
Each coordinate separately permits its own probability from DP7.

But any single probability nu on this R_3 satisfying both prime
bounds would obey

    1=nu(R_3)
      <=nu(x=0 mod 5)+nu(x=0 mod 7)
      <=1/3+1/5=8/15<1,                              (DP10)

a contradiction. Thus even actual AP provenance, whole coverage,
distinctness, irredundancy, and the individual projection conditions
do not justify interchanging the two quantifiers in DP7.

This control contains even moduli. It is neither a minimum odd cover
nor a refutation of a possible common-probability theorem using the
additional odd extremal hypotheses. It identifies the exact joint
support condition missing from an inference based only on DP1/DP7;
it is not an odd-cover counterexample or an arbitrary-set relaxation.

## 6. Verification scope

The [fresh-root constructor](../../frontier/cover-geometry/fresh_root_constructor.py)
provides `contract_prefix_tree`. It computes the actual residual and
recursively selects a complete good subtree, accepting different child
permutations at different nodes. It checks the complete q-free original
event vector at every transported point; its source-coordinate oracle
uses direct enumeration independently of its output CRT calculation.
It also checks full input/output coverage, distinctness, nonunit moduli,
conditional-fibre bijections, and strict class-count descent. The
default requires odd inputs; all positive controls explicitly allow
even moduli. It never infers global minimality from a finite run.

Starting with the 19-class period-5040 control from 374, add

    (11,25), (36,125), (186,625), (2,200), (92,1000).

This gives a 24-class whole cover of period 630000, with 18 q-free
originals at q=3 and full p=5 height four. The added classes are not
claimed irredundant. All four depths produce 17 output classes:

| Depth k | Output period | Selected source points | Checked event coordinates |
|---|---:|---:|---:|
| 1 | 42000 | 42000 | 756000 |
| 2 | 25200 | 25200 | 453600 |
| 3 | 15120 | 15120 | 272160 |
| 4 | 9072 | 9072 | 163296 |

Depth one agrees class by class with 374's constructor. Depths two
and three exercise alpha<k, alpha=k, and alpha>k, and have respectively
two and eight different nonroot child sets. Their outputs agree with
an independent recursive implementation. At full depth four no output
modulus contains 5. Five invalid inputs are rejected. A mutation
replacing the correct high tail by a still covers, but corrupts 364
joint original-event vectors and is rejected by the event check.

The depth-four residual has 125 bad prefixes, exceeding the numerical
threshold 81, yet admits a good subtree. This verifies the structural
constructor beyond the sufficient small-cardinality test; DP1 is not
an equivalence between cardinality and a blocked root.

The [independent tree counter](../../frontier/cover-geometry/prefix_tree_blocker_counts.py)
checks the recursion at (p,q,k)=(3,2,2)
and (5,3,2). The first enumerates all 512 leaf masks. The second
enumerates 7776 child-count tuples with exact binomial weights,
accounting for all 33554432 masks. The minimum bad-leaf counts are
4 and 9, attained by 27 and 10000 masks respectively, as in DP3.
The q=2 example is a tree control, not an odd-cover instance.

The constructor also checks every point of the 13440-period cross
control, including private witnesses for all 24 originals, the exact
seven-point R_3, separate supported laws, and the common-law cut 8/15.

No dominating deep extremal projection statement was found in the
searched project reports 348, 350, 354, and 374. The digit transport
reuses their prime-prefix construction; the blocked-tree argument
supplies the stated depth bound. No literature-priority claim is
made, and no new Lean verification is claimed.
