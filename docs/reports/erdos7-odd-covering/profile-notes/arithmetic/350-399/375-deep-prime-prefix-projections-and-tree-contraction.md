[Index](../../../marked_head_profile.md) · [First-root descent](374-extremal-prime-projections-and-cardinality-descent.md) · [Extremal original family](../../321-384/350-extremal-paired-branch-and-source-support.md)

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

Section7 gives another transport: retain the old smaller-prime coordinate,
absorb a larger-prime tree into its new higher digits, and filter deleted
labels through actual live cofactors. Its obstruction implies
`q-r <= H*tau(M)-1` for a lexicographically minimum hypothetical cover
of period `r^H q^G M`, with `r<q` and `gcd(M,rq)=1`.

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

The [fresh-root constructor](../../../frontier/cover-geometry/p-flat-constructor/fresh_root_constructor.py)
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

The [independent tree counter](../../../frontier/cover-geometry/prefix-tree-blocker-counts/prefix_tree_blocker_counts.py)
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

## 7. Live cofactors obstruct absorbing a larger prime into new higher digits

A different transport retains the entire old smaller-prime coordinate and places a larger-prime prefix tree in new higher digits of that same prime. It removes all larger-prime originals below the old maximum smaller-prime height. Full-height originals each remain a single AP, with distinct numerical moduli. Filtering the removed originals through the actual live cofactor region makes the resulting extremal blocker occur at a genuinely live source.

This is a conditional whole-cover transformation and an ordinary mathematical consequence for a lexicographically minimum distinct odd cover. It neither asserts that the required avoiding trees always exist nor resolves unrestricted Erdős#7.

### 7.1. The original family and actual live cofactors

Let a finite distinct-modulus odd whole cover have full period

    Q=r^H q^G M,
    r<q distinct support primes, H,G>=1, gcd(M,rq)=1.

Write every original label uniquely as d=r^a q^e s, with a<=H, e<=G and s|M, and write A_d for its literal original congruence class. No prime phase normalization, irredundancy or divisor closure is needed for the conditional transformation.

Fix a FULL old r-coordinate u modulo r^H. Its actual q-free cofactor residual is

    R_u={v mod M : no original with e=0 contains (u,v)}.

A q-free class d=r^a s contains(u,v) exactly when u=a_d mod r^a and v=a_d mod s. Thus R_u is defined using the entire actual q-free original union, including every r-height and every other prime-power coordinate.

A low-r-height q-bearing original d=r^a q^e s contributes at u precisely when

    e>=1, a<H,
    u=a_d mod r^a,
    R_u intersect {v:v=a_d mod s} is nonempty.       (LA1)

Let F_u be the union of its literal q-prefixes a_d mod q^e over all originals satisfying LA1. Different originals may contribute the same prefix, and one contributed prefix may contain another. If R_u is empty, F_u is empty.

The witnesses v in LA1 need not be the same for different originals. F_u is a union over actual live cofactors; it must not be interpreted as their common intersection or as a set simultaneously realized at one v.

### 7.2. One source map for all retained labels

Suppose for every u there is an embedded complete r-ary tree of depth G in the q-ary lowest-digit-first tree whose leaves avoid F_u. Equivalently choose injections

    theta_(u,j): Z/r^j -> Z/q^j, 0<=j<=G,

commuting with truncation, with final image avoiding F_u. The choices may depend on u and the preceding tree path. They are independent of v. Arbitrary leaf injections or maps depending on the M cofactor do not supply the single-AP conclusion below.

For the new carrier Z/N, N=r^(H+G)M, use the one source map

    u=z mod r^H,
    b=(z-u)/r^H mod r^G,
    v=z mod M,
    y=(u,theta_(u,G)(b),v) in the old CRT carrier.     (LA2)

All original events are evaluated at this same y.

### 7.3. Exact retained events and numerical labels

Drop every low-r-height q-bearing original, namely every e>=1,a<H.

Every q-free original is retained unchanged: its inverse image under LA2 is exactly A_d on the new carrier.

For an original with e>=1,a=H, put u_d=a_d mod r^H. If its q-prefix a_d mod q^e is not in the image of theta_(u_d,e), drop it as having empty inverse image. Otherwise let c mod r^e be its unique inverse. Retain the single new AP defined by

    z=u_d+r^H c mod r^(H+e),
    z=a_d mod s.                                    (LA3)

Its numerical modulus is r^(H+e)s. Prefix compatibility ensures that all deeper domain digits are free, so LA3 is one AP. The fixed old full r-coordinate u_d is why u-dependent tree choices do not split this original.

Every retained original has EXACT equality between its output event and its old event at LA2. The deliberately dropped low-r-height originals need not have empty inverse images on dead cofactors; the coverage proof below does not assert this.

### 7.4. Coverage and strict descent

Take any new z and its(u,b,v) coordinates.

If v is outside R_u, some q-free original contains(u,v). That unchanged original covers z, independently of the chosen old q-coordinate.

If v is in R_u, no q-free original contains y. A low-r-height q-bearing original also cannot contain y: if its r- and s-conditions hold at(u,v), that same v witnesses LA1, so its q-prefix belongs to F_u; theta_u avoids it. Since the original family covers every old point y, a full-r-height q-bearing original must contain y. Its inverse image is nonempty, and LA3 covers z.

Thus the output is a whole cover. Dropped labels can remain active at some points with v outside R_u without harming this proof, because q-free originals already cover those points. No independently selected source or cofactor is substituted for y.



Every unchanged output modulus has r-height at most H. Every transported modulus has r-height H+e>H, so these groups do not collide. Within transported moduli, the r-height recovers e and the r-free part recovers s, hence recovers the original r^H q^e s. The map is injective because original numerical moduli are distinct. All new moduli are odd and greater than one.

Each original contributes at most one output class. If any is dropped, the class count strictly decreases. If none is dropped, all q-bearing originals are full-r-height and survive, with each numerical modulus decreased by factor(r/q)^e<1. At least one exists since q is a support prime. Thus the modulus sum strictly decreases while the class count remains fixed.

Consequently a cover lexicographically minimum in(class count, modulus sum) cannot admit the avoiding trees for every u. If the original prime-q class is present, it has a=0<H and is dropped. In that case the transformation already contradicts minimum class count, so the modulus-sum fallback is not needed. This includes the divisor-closed extremal model.

### 7.5. A live blocked tree and a prefix-weight bound

There is therefore a full old r-coordinate u for which no complete r-ary depth-G tree avoids F_u. Necessarily R_u is nonempty: otherwise F_u is empty and any r-ary subtree of the q-ary tree works.

Put t=q-r+1. Apply the finite-tree duality proved in sections1 and4, with ambient branching q and avoiding-tree branching r. It gives a complete t-ary depth-G subtree all of whose leaves lie in F_u. The larger-prime leaf set here is the union of the actual low-r-height prefixes in LA1, not the smaller-prime-free residual projection D_k used earlier.

Deduplicate the contributed prefixes and remove descendants of any retained ancestor, giving the prefix antichain B_u with the same union F_u. Give the t-ary blocked subtree uniform leaf measure. A q-prefix of depth e has mass0 or t^(-e). Since B_u covers its entire support,

    1 <= sum_(b in B_u) t^(-depth(b)).               (LA4)

Before merging, summing t^(-e) over contributing originals gives a valid weaker bound, but repeated or nested prefixes are not independent capacities. LA4 is necessary, not sufficient for blocking. In particular at least t different first-q roots occur among the contributions at this same live u.

The numerical distinctness restriction also gives a direct inventory consequence. At a fixed u and q-height e, there are at most H*tau(M) contributing low-r-height labels: a has H possibilities0,...,H-1 and s is a divisor of M. Merging identical or nested q-prefixes can only decrease their total positive weight. Therefore

    1 <= sum_(b in B_u)t^(-depth(b))
      <= H*tau(M) sum_(e=1..G)t^(-e)
       = H*tau(M)(1-t^(-G))/(t-1),
    t=q-r+1.

Since G is finite, every such lexicographically minimum distinct odd cover satisfies

    q-r < H*tau(M),
    q-r <= H*tau(M)-1.                              (LA5)

This is a direct corollary of the original-label transport, not a separate general theorem. In the divisor-closed extremal model, [Report354](../../321-384/354-synchronized-prime-private-cofactor-matching.md) already forces q-1 distinct nonpure q-free cofactor labels; their total inventory gives q<=(H+1)*tau(M). The new bound q<=H*tau(M)+r-1 is stronger than that coarse existing consequence when tau(M)>r-1, equal at tau(M)=r-1, and otherwise weaker. In particular its two-prime specializations are not presented as new noncoverage results.

### 7.6. A probability on actual original points

For each leaf xi of the blocked tree, choose one contributing original whose q-prefix contains xi, and choose v_xi in R_u satisfying that original's s-condition. Such a v_xi exists by LA1. The actual points(u,xi,v_xi) lie in the union of low-r-height q-bearing originals above the SAME live u and have no q-free owner. Giving the t^G points equal mass produces one probability nu with

    nu(q-coordinate=c mod q^e) <= t^(-e).

The cofactor choices may be correlated with xi. This is one legitimate law supported on the actual low-r-height covered region; it is not a claim that all contributed originals share a cofactor or that one law controls several absorbed primes simultaneously. The union bound on this one law also gives the unmerged version of LA4.

### 7.7. Reuse and the remaining joint obligation

Report374 and sections1--4 above remove all smaller-prime-bearing originals and transport larger-prime branches covered by the smaller-prime-free family. Their arithmetic modulus map does not retain the old smaller-prime coordinate as done here. The present map keeps that coordinate, moves the larger prime to new higher smaller-prime digits, retains full-height originals, and deletes the low-height stratum using an actual live-cofactor filter. The finite-tree duality is reused; the earlier stated arithmetic transport does not directly imply LA2--LA3.

The filter removes the earlier dead-u obstruction, but F_u still combines prefixes witnessed at different live cofactors. Its blockage need not be realized by one fixed v. Nothing here forces LA4 to fail in every odd distinct extremal family. A joint quantitative or structural argument ruling out this genuinely live original-labelled blocker remains the unrestricted #7 obligation.

The construction, event identities and descent proof are ordinary mathematics. No new Lean verification or literature-priority claim is made.

### 7.8. Complete-cover controls for absorption and live filtering

The [full-height absorption program](../../../frontier/cover-geometry/p-flat-constructor/full_height_prime_absorption.py)
constructs the prefix embeddings and checks literal congruences over the
complete input and output periods. Its [exact data](../../../frontier/cover-geometry/p-flat-constructor/full_height_prime_absorption.json)
include the following actual distinct-modulus whole cover, in
`(residue, modulus)` notation:

    (0,2), (1,4), (3,8), (23,40), (7,24),
    (119,200), (119,120), (399,600),
    (0,5), (1,10), (7,20), (4,25), (9,50), (39,100).

Every original has a private point. Take `r=2,q=5,H=3,G=2,M=3`.
The embeddings vary with the complete old coordinate `u`. Absorption
gives the irredundant whole cover

    (0,2), (1,4), (3,8), (7,16), (7,24),
    (15,32), (47,48), (63,96).

| Quantity | Original | Absorbed |
|---|---:|---:|
| Number of classes | 14 | 8 |
| Complete period | 600 | 96 |
| Sum of numerical moduli | 1208 | 230 |

For this control even the stronger unfiltered avoidance condition holds.
All `96*14=1344` original event coordinates equal their transported
coordinates, including zero for every discarded label. This verifies
both larger-prime depths and the full original event vector.

Add the class `13 mod15` to distinguish live filtering from the stronger
condition. This additional class is redundant: every point of it is
already covered by a q-free original. Unfiltered avoidance now fails
at `u=3,7`. Filtered avoidance still holds and produces exactly the
same eight-class output. The only live old r-coordinate is `u=7`, with
`R_7={0,2}` modulo3; the added label has cofactor residue1 and therefore
does not contribute to its forbidden prefixes.

All `96*8=768` retained event coordinates still agree exactly. At all
eight transported points with live cofactors, every discarded original
is false. Outside the live region there are29 discarded-event hits, so
the full original event vector is deliberately not claimed to agree.
This is why the two-domain coverage proof in section7.4 is needed.

Both controls contain even moduli. They verify the transport, not an
all-odd covering example. The second control's extra class is expressly
not irredundant; it separates sufficient conditions without claiming
that their separation occurs in an extremal family. Six negative
controls reject unauthorized even input, a lost necessary input class,
duplicate labels, reversed primes, an absent source prime, and use of
the unfiltered criterion on the filtered-only control. Normal and
optimized runs give identical result bytes:

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/p-flat-constructor/full_height_prime_absorption.py --output /tmp/e7_full_height_prime_absorption.json
```

The program's complete-period cap limits the finite checks only.
The proof in sections7.1--7.7 allows arbitrary original heights and
periods. Neither these controls nor the necessary inequality LA5 force
a descent in every hypothetical distinct odd cover.

## 8. Joint liability gives the exact absorption criterion

The live filter in section7 still forbids some harmless low-r events:
a removed class may hit a selected source point that a retained class
also covers. The exact criterion uses the joint region left uncovered
by the retained originals. It gives an if-and-only-if for the specified
prefix transports, and a stronger support condition on the blocking
probability in a hypothetical extremal odd cover. These are ordinary
mathematical deductions, not new Lean verification or a claim of
literature priority.

### 8.1. One actual joint region

Keep section7's distinct original whole cover, with its actual least
common multiple Q=lcm(D) and two actual support primes r,q:

    Q=r^H q^G M, r<q primes, H,G>=1, gcd(M,rq)=1.

For each original numerical modulus d=r^a q^e s, put

    J={d : e>=1 and a<H},
    K=D minus J,
    E_J=(Z/Q) minus union_(d in K) A_d,
    E_u={xi mod q^G : exists v mod M, (u,xi,v) in E_J}.  (JL1)

Thus K contains exactly the q-free originals and the full-r-height
q-bearing originals. Because the full original family covers, E_J is
the set of points whose nonempty original-owner set is contained in J.
It includes points covered jointly by several removed classes and
private to none of them. This is one actual region; the witness v in
JL1 may depend on xi.

For every u, E_u is contained in the old live-filtered F_u. Indeed a
witness has no q-free owner, so its cofactor is live; an original owner
must be low-r and contributes its literal q-prefix to F_u. The converse
need not hold because a full-r owner can also cover such a point.

### 8.2. Necessary and sufficient for the specified source maps

Choose complete r-ary prefix injections theta_(u,e) into the q-ary
depth-G tree, compatible with truncation and independent of v. Use
exactly the LA2 source map and the LA3 inverse APs of K. Then

    the output covers its full transport carrier
    iff image(theta_(u,G)) intersects E_u trivially for every u. (JL2)

For proof, every retained event at a new point is exactly its original
event at the single source point (u,theta_u(b),v), with zero for an empty
inverse AP. The output misses the new point exactly when that source
point lies in E_J. If a selected xi belongs to E_u, choose its actual
witness v. CRT supplies a new point with that u, b and v, giving an
output hole. Conversely each output hole supplies the selected xi and
witness v. Both directions preserve all retained original events.

Consequently the finite tree recurrence applied to the complement of
E_u decides whether a covering transport of this specified form exists.
It does not decide every possible covering transformation. Its success
at every u gives strict lexicographic descent in (class count, modulus
sum): each original produces at most one output, all J originals are
dropped, and a retained full-r original maps from r^H q^e s to
r^(H+e)s. These output moduli are distinct, have r-height greater than
H, and cannot collide with the q-free outputs. If no class is dropped,
at least one q-bearing original survives and strictly decreases its
modulus because q>r. Oddness and nonunit moduli are preserved on odd
input.

### 8.3. A probability supported on genuine joint liability

In a lexicographically minimum distinct odd whole cover, some u must
therefore have no complete r-ary tree avoiding E_u. The finite-tree
duality from sections1--4 supplies a complete t-ary depth-G tree T,
where t=q-r+1, all of whose leaves belong to E_u. For each leaf xi,
choose one actual witness v_xi in JL1 and give the t^G points
(u,xi,v_xi) equal mass. This is one probability nu with

    support(nu) subset E_J,
    nu(A_d)=0 for every d in K,
    nu(q-coordinate=c mod q^e)<=t^(-e), 0<=e<=G.       (JL3)

A q-prefix either misses the tree or has exactly t^(G-e) descendant
leaves, proving the last bound. The source law now excludes every
retained full-r event as well as the q-free events. Its cofactor choices
can be correlated with the q-coordinate; no common constant cofactor
or simultaneous law for different absorbed primes is asserted.

Let I_u consist of low-r original labels whose events meet E_J in the
u-fibre. Since these actual events cover JL3's support,

    1<=sum_(d in I_u)nu(A_d)
      <=sum_(d in I_u)t^(-v_q(d)).                    (JL4)

One can retain the prefix-cover structure more precisely. For every
subset C of the low-r originals whose literal q-prefixes cover E_u,

    1<=sum_(d in C)t^(-v_q(d)).                       (JL5)

Evaluate those covering prefixes on the same uniform law on T to
obtain JL5. The minimum weight over such prefix covers is thus at least
one. This is necessary for blockage, not sufficient. JL4 still implies
the inventory bound LA5; no stronger unconditional scalar inventory
bound is claimed. Its additional restriction is that the law is
supported on the actual joint loss and labels irrelevant to that loss
need not be charged.

### 8.4. A strict whole-cover control and a false private-set shortcut

Add the deliberately redundant class 3 mod15 to section7.8's fourteen
original classes. This differs from the earlier 13 mod15 control.
For r=2,q=5,H=3,G=2,M=3, the only q-free live u is7, with R_7={0,2}.
The new class meets that live region. The old F_7 now forbids roots
0,1,2,3 entirely and three children of root4, so no binary depth-two
avoiding tree exists.

K has not changed, hence neither has E_u. At u=7 one permitted map is

    theta_7([0,1,2,3])=[3,19,8,24] mod25.

It gives the same eight-class period96 cover listed in section7.8.
The class count falls15 to8 and the modulus sum1223 to230. All768
retained original event coordinates on the96-point transport carrier
agree. Two discarded-class hits occur on live cofactors; both are
harmless because retained full-r originals cover those same source
points. Thus requiring every discarded event to vanish even on the
live region is strictly stronger than JL2.

This strict control contains even moduli and a redundant added class.
It establishes a strict difference between the criteria for whole
covers, without asserting that the difference has been realized on an
irredundant or all-odd whole cover.

For a separate negative control, instead add 0 mod15 and 5 mod30 to
the fourteen-class base. K and E_J again stay unchanged. Above u=7,
every q-leaf0 mod5 has a live witness owned by the modulus5 class AND
one added low-r class. None of these leaves has a point private to a
single low-r class, yet all remain in E_u.

Replacing E_u by the projection of the union of individual private
regions incorrectly permits first roots0,3. The resulting literal
transport has holes23,39,71,87 in the96-point carrier, corresponding
to source points455,375,575,255. Its output period is48, with two
distinct holes. Every listed source point has only removed low-r
owners. Using the actual E_u instead still gives the valid eight-class
cover. Report385's special descendant-phase reduction to ONE complete
private region therefore cannot be applied to an arbitrary deleted
stratum without its hypotheses.

The [joint-liability checker](../../../frontier/cover-geometry/p-flat-constructor/joint_liability_prime_absorption.py)
and [exact data](../../../frontier/cover-geometry/p-flat-constructor/joint_liability_prime_absorption.json)
retain the original numerical classes, complete-period owner sets,
the actual liability and private projections, all prefix maps and
literal transported classes. The base, strict, corrected negative and
deliberately incorrect negative transports check3072 retained event
coordinates in total. Independent enumeration of the CRT source point
confirms all projections, transported APs and holes. Normal and
optimized runs produce identical result bytes:

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/p-flat-constructor/joint_liability_prime_absorption.py --output /tmp/e7_joint_liability_prime_absorption.json
```

The remaining unrestricted obligation is to contradict JL3 for every
hypothetical odd extremal family, or to repair its E_J with a smaller
allowed AP inventory. Different blocked leaves can still require
different cofactor witnesses. Neither the tree nor the private-hull
repair rules make those witnesses one common cofactor.

## 9. Liability multiplicity and the missing distribution of blocked fibres

The actual joint region in section8 gives a multiplicity alternative.
It also identifies the extra premise needed to average over smaller-prime
heights. The following deductions retain the same original labels and
whole-cover hypotheses. The finite controls below are noncovers and test
only the explicitly listed local premises. This section contains ordinary
proofs and exact finite checks, not new Lean verification.

### 9.1. A blocked tree forces private leaves or multiple coverage

Keep a blocked u and its complete t-ary tree T from section8, where
t=q-r+1. For every leaf xi choose v_xi in the actual fibre of E_J
minimizing the number mu_xi of original owners of (u,xi,v_xi).
Whole coverage and the definition of E_J give mu_xi>=1 and put every
owner in J. Let

    n=t^G,
    C_T=sum_(d in J, u=a_d mod r^(v_r(d)))
            #{xi in leaves(T): xi=a_d mod q^(v_q(d))}.

Each summand is either zero or t^(G-v_q(d)). Counting actual
point-owner incidences, and then forgetting only the cofactor test,
gives

    sum_(xi in leaves(T))mu_xi <= C_T
      <= H*tau(M)*(t^G-1)/(t-1).                    (LM1)

The last inequality uses at most H*tau(M) original labels at each
q-height e. It does not assume their cofactor events are independent.
If P is the number of leaves admitting a point IN E_J private to one original,
the minimizing choices have mu_xi=1 at precisely those P leaves, and
mu_xi>=2 elsewhere. Consequently

    P >= max(0, 2*t^G-C_T)
      >= max(0, 2*t^G-H*tau(M)*(t^G-1)/(t-1)).        (LM2)

In particular, if no leaf of T admits a private point in E_J, then

    2*t^G <= H*tau(M)*(t^G-1)/(t-1),
    2*(q-r) <= H*tau(M)-1.                          (LM3)

More generally, if every such liability point has at least m>=1 original
owners, replace 2 by m. If P>0, at least ceil(P/t^(G-1)) distinct low-r
labels privately own the chosen points: any one original in J has
q-height at least one and can meet at most t^(G-1) leaves.

These are alternatives, not a universal doubling of LA5. In the private
arm, each point permits the existing same-source shell inequalities in
[Lettl--Sun accounting](../../../../../../Library/Arith/lettlsun2008cosets.md#the-covering-premise-and-pointwise-demand).
The points need not have the same private owner or cofactor. They do not
identify the complete private region required for a repair in Report385.

### 9.2. A single distribution on blocked smaller-prime fibres

Let U be the set of u modulo r^H for which no complete r-ary depth-G
tree avoids E_u. Extremality gives U nonempty. Suppose ONE probability
sigma supported on U obeys

    sigma(u=c mod r^a)<=beta_a, 0<=a<H, for every c.  (LM4)

Choose the JL3 law nu_u separately for each u and mix these actual laws
with sigma. For an original d=r^a q^e s in J, its event requires the
specified r-prefix, and its conditional probability at any such u is
at most t^(-e). Thus the mixed law nu satisfies

    nu(A_d)<=beta_a*t^(-e),
    1<=sum_(d in J)nu(A_d)
      <=tau(M)*(sum_(a=0..H-1)beta_a)*(1-t^(-G))/(t-1).

All retained events still have mass zero. In particular,

    q-r < tau(M)*sum_(a=0..H-1)beta_a.               (LM5)

This conditional inequality replaces H only after LM4 has been proved
for one actual sigma. A different law for each height or each label
does not suffice.

For example, beta_a=r^(-a) forces sigma uniform modulo r^(H-1): at
that depth its r^(H-1) cell masses sum to one and each is bounded by
1/r^(H-1). Such a sigma exists on U exactly when U meets every one of
those cells. If H>=2 and the original r-class is normalized to0, no
u=0 mod r belongs to U, so this proposed uniform law is impossible.
Normalization is available for the prime classes by one common CRT
translation, and does not change any covering or tree property.

A sufficient different condition is that U contain all leaves of a
complete (r-1)-ary depth-H prefix subtree. Its uniform leaf law has
beta_a=(r-1)^(-a), yielding

    q-r < tau(M)*sum_(a=0..H-1)(r-1)^(-a)
         < tau(M)*(r-1)/(r-2).

No such subtree in U has been established for every hypothetical cover.

### 9.3. The actual source of possible distribution

Let L be the projection onto r^H of the region not covered by the
q-free originals, and let

    V={a_d mod r^H: d in D, v_r(d)=H, v_q(d)>=1}.

Then, directly from the original events,

    L minus V subset U subset L,
    |V|<=G*tau(M).                                  (LM6)

Indeed, outside L the q-free originals cover every cofactor, so E_u
is empty. For u in L minus V choose an actual q-free-live cofactor v.
No full-r q-bearing original has that u, so every q-leaf at (u,v)
belongs to E_J. Hence E_u is the full q-tree and u belongs to U.
There is at most one full-r numerical label for each (e,s), proving
the count on V.

If B=L minus V is nonempty, its uniform distribution gives an explicit
instance of LM4 with

    beta_a=min(1, r^(H-a)/|B|).

Writing delta=|B|/r^H therefore gives the conditional height-independent
consequence

    q-r < tau(M)*(1+1/(delta*(r-1))).                (LM7)

Here beta_0=1 and the positive-depth geometric series is bounded by
1/(delta*(r-1)). The unknown is an adequate positive lower bound on
this actual delta, or a sharper prefix distribution on U. The bound
on |V| alone provides neither. Report374 controls projections of a
prime-free residual onto LARGER primes; it cannot be reversed to
supply the distribution at r<q used here.

Whole coverage gives a further check on L itself. For each u in L
choose one actual q-free-live v_u and then vary xi over ALL q^G leaves,
keeping that v_u fixed. These |L|*q^G points must all have q-bearing
owners. A label r^a q^e s covers at most r^(H-a)*q^(G-e) of them.
There is at most one label for each (a,e,s), so

    |L| <= tau(M)*(r^(H+1)-1)/(r-1)
                  *(1-q^(-G))/(q-1).               (LM8)

Restricting to B=L minus V removes every full-r owner and gives the
same bound with the first geometric factor replaced by
r*(r^H-1)/(r-1). These are direct common-source counting consequences
of the complete q-coordinate marginal test, not a new general marginal
theorem. Unlike a single selected liability law, they use coverage of
every q-leaf above every chosen u. They give upper bounds on the live
projection; they cannot serve as the missing lower bound for delta.

### 9.4. Actual odd controls exclude a local geometric replacement

Consider first the six original classes

    0 mod3, 4 mod9, 10 mod27, 0 mod5, 1 mod15, 37 mod45.

Their period is135. They are odd, numerically distinct, divisor-closed
and irredundant, with normalized prime classes and disjoint comparable
originals. Every complete private congruence hull is exactly its original
modulus. The finite DR3--DR6 conditions of Report385, the EP4 projection
conditions of Report374 and LA5 all hold. The family has49 holes.

For r=3,q=5,H=3,G=1,M=1, the points55,1,82 all have u=1 mod27
and have q-roots0,1,2. They are private to5,15,45 respectively.
Their uniform law is supported on actually covered points of E_J,
has zero mass on every retained original and gives each of the three
r-heights mass1/3. The proposed replacement would require

    q-r=2 < sum_(a=0..2)3^(-a)=13/9,

which fails. For these selected leaves C_T=3, so LM1--LM2 attain
equality and all three private leaves are retained by the accounting.

The second family strengthens the source control:

    (residue,modulus)=
    (0,3),(4,9),(10,27),(28,81),(82,243),
    (0,7),(1,21),(37,63),(136,189),(487,567),
    (0,5),(7,15),(26,35),(76,105).

It has period8505 and2333 holes and satisfies the same listed local
conditions, for every relevant support-prime pair. Take
r=3,q=7,H=5,G=1,M=5. At the SAME u=1 mod243 and v=1 mod5,
the full seven-root q-line consists of

    6076,1,2431,4861,7291,1216,3646.

Every one is covered by the original family. The first five are
private to7,21,63,189,567. Their uniform law gives five distinct
r-heights mass1/5 while every retained event has mass zero. Nevertheless

    q-r=4 > tau(5)*sum_(a=0..4)3^(-a)=242/81.

Thus even one completely covered same-source q-line, together with all
the listed local conditions, does not justify that geometric inventory
bound. These examples do not have the whole-cover premise and are not
counterexamples to LM5 or Erdős#7. In a noncover E_J can also contain
original holes; the verified laws use only its actually covered points.
In fact their live projections have |L|=14 and122, respectively, while
LM8 would require |L|<=8 and104. This whole-cover test rejects both
controls, even though the second covers the displayed complete q-line.
They also fail some same-source private shell demands. The examples
therefore refute the stated local shortcut, not one that additionally
assumes all original shell inequalities or LM8.

The [control program](../../../frontier/cover-geometry/p-flat-constructor/joint_liability_global_bridge.py)
and [exact data](../../../frontier/cover-geometry/p-flat-constructor/joint_liability_global_bridge.json)
check complete-period ownership, all private hulls, divisor closure,
comparable disjointness, the named local inequalities and the literal
source laws. Independent enumeration from the displayed classes agrees
on both private-count vectors, hulls, source points, masses and holes.
Normal and optimized runs produce identical result bytes:

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/p-flat-constructor/joint_liability_global_bridge.py --output /tmp/e7_joint_liability_global_bridge.json
```

The remaining whole-cover obligation is to force enough distribution
on U, exploit both arms of LM3 through complete private-region repairs,
or supply another strict descent. A local geometric substitution does
not discharge it.
