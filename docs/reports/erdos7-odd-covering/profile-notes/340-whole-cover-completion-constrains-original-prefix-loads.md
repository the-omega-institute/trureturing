[Index](../marked_head_profile.md) · [Actual prefix transfer](../problem-details/08-arbitrary-head-transfer-by-the-joint-load-invariant.md#transfer-retaining-the-actual-forbidden-fibre-geometry) · [Same physical and killed chain](334-same-chain-overlap-and-future-risk-certificates.md)

# Whole-cover completion constrains original prefix loads

Assuming that one finite family of pairwise distinct odd moduli greater
than one covers its whole period, every current prefix missed by the
current forbidden union must
be completed by that SAME family's future labels. This gives a lower
bound on current prefix occupancy in terms of an explicit future-label
load. The bound can enter the existing prefix transfer inequality on a
killed submeasure of the same physical chain. At the largest prime,
complete fibre coverage also forces a same-depth p-way old intersection
of distinct original cofactors.

These are ordinary conditional relations with finite original inputs.
They do not supply a uniform positive numerical gain or a contradiction
to the existence of an odd distinct covering family. Two legal
noncovering constructions below show precise limitations of local
completion and of discounting a deepest sibling witness.

## Current prefix occupancy and future original load

Fix one such finite family and a current prime p with
`H=max_i v_p(d_i)>=1`, including p-heights in future-ending labels.
Resolve every original old height, including heights appearing only in
later-ending moduli. Write its full carrier as

    X times Y times Z,
    X=Z/Q_<p Z, Y=Z/p^H Z,

where Z contains all prime coordinates greater than p at their actual
heights. Each coordinate carries Haar probability for the set calculation.
Let R be the complete old survivor set: no earlier-ending original class
covers x in R. Let B_p(x) be the actual p-ending forbidden union in Y,
including pure p powers.

Every future original label i has a unique factorization

    d_i=g_i*p^(e_i)*s_i,

with primes of g_i below p and primes of s_i above p, s_i>1. Its own old
residue condition defines C_i in X. For a depth-t prefix J in Y, put

    a_J(x)=Haar_Y(B_p(x) intersect J),
    F_J(x)=sum_(future original i)
       1_(x in C_i) 1_(i's p-prefix compatible with J)
                           /[p^max(e_i,t)*s_i].       (CP1)

Here0<=t<=H, e_i=0 is allowed, and a p-prefix of depth zero is all Y.
Pure future classes, arbitrary actual exponent heights and repeated
RESIDUAL moduli remain included. Distinct original labels remain
separate summands even when removing their old factors gives the same
residual modulus.

If the whole original family covers, then for every x in R and every J,

    a_J(x)+F_J(x)>=p^-t.                             (CP2)

Indeed every point of `(J minus B_p(x)) times Z` misses all earlier and
current classes. It must belong to a future original class. A compatible
future label has exactly the Haar mass in CP1 inside J times Z, by CRT.
The union bound therefore pays the entire missing mass p^-t-a_J(x).
No distributional independence of future physical kernels is asserted;
this is a pointwise set-cover calculation under product Haar.

Define

    alpha(x)=Haar_Y(B_p(x)),
    m_t(x)=min_(depth-t J) a_J(x),
    F_t^*(x)=max_(depth-t J) F_J(x),
    h_t(x)=[p^-t-F_t^*(x)]_+.

Then, on the genuine old survivor set R,

    m_t(x)>=h_t(x).                                 (CP3)

The right side uses only original-label compatibility, exact exponents,
residues and future cofactors. It is not an unknown final-survival
function. A strictly positive lower bound for it remains an additional
input obligation.

## Transfer on the same physical and killed measures

Use the full-Haar clipped kernel at p with0<delta<1 and
`theta(x)=min(alpha(x),delta)`. Let M_t(x) be its largest depth-t prefix
mass and c_t=p^-t/(1-delta). The exact same-union identity from
problem-details08(W2--W3) is

    c_t-M_t
      =p^-t*(delta-theta)/[(1-delta)(1-theta)]
         +theta*m_t/[alpha*(1-theta)]>=0.            (CP4)

At alpha=0 the second term is zero. Under CP2 this case also has h_t=0.
These numerical Haar factors cannot be copied unchanged to a base law
already conditioned away from pure-power classes.

Let mu be the incoming normalized PHYSICAL law on old histories and let
eta be the unnormalized KILLED submeasure from the same starting law and
the same preceding kernels. The starting law is supported on complete
head survivors. Then eta<=mu and eta is supported on R. Combining the
nonnegative gap in CP4 with CP3 gives

    E_mu(c_t-M_t)
       >= integral theta*h_t/[alpha*(1-theta)] d eta. (CP5)

This does not assert CP3 on previously killed physical histories and
does not renormalize eta. The measure domination follows by restricting
the same nonnegative kernel at every preceding step.

Write A_p(H)=sum_(t=1..H)(2t+1)p^-t, and extend the complete old-layout
square maximum Gamma homogeneously to finite positive measures as in
problem-details08. Its existing(W4) consequently yields

    Gamma_(Q_<p*p^H)(mu K_p)
      <=Gamma_(Q_<p)(mu)*(1+A_p(H)/(1-delta))
        -sum_(t=1..H)(2t+1)
            integral theta*h_t/[alpha*(1-theta)] d eta. (CP6)

All current heights, every original old test label and the same physical
law remain in this inequality. For alpha>0 the coefficient is at least

    k(delta)=min(1,delta/(1-delta)).

For alpha<=delta it equals1/(1-alpha)>=1; for alpha>delta it is at least
delta/(1-delta). Thus a proved bound
`eta{x:h_t(x)>=epsilon}>=w` supplies the correction
`(2t+1)*k(delta)*epsilon*w` to CP6. Without that same-family input CP6
asserts no positive numerical gain. A Gamma correction is not itself a
subtraction from a separate hinge or bad-charge account; any such use
requires a proved consumer connecting those quantities.

## Exact label incidence and its measure boundary

Fix x in R and let N_F(y,z) count the compatible ORIGINAL future labels
covering(y,z). Then F_J is its integral on J times Z, and

    F_J+a_J-p^-t
      =integral_((B_p(x) intersect J) times Z) N_F
        +integral_((J minus B_p(x)) times Z)(N_F-1).  (CP7)

For an arbitrary original family, without the cover premise, instead put

    I_J=integral_((B_p(x) intersect J) times Z) N_F,
    E_J=integral_((J minus B_p(x)) times Z)(N_F-1)_+,
    u_J=Haar{(y,z) in (J minus B_p(x)) times Z:N_F(y,z)=0}.

The pointwise identity `N_F-1=(N_F-1)_+-1_(N_F=0)` gives

    F_J+a_J-p^-t=I_J+E_J-u_J,
    u_J>=max(0,p^-t-a_J-F_J).                       (CP7a)

Thus the prefix deficit is also a noncoverage certificate: if a genuine
old survivor x and one prefix have `a_J+F_J<p^-t`, an uncovered integer
exists by finite CRT. Under whole coverage u_J=0 for every such x,J,
recovering CP2 and CP7. The deficit bound alone need not be positive.
For a fixed depth t the prefixes partition Y, so the full uniform
uncovered density also satisfies

    Haar_full(uncovered)=integral_R sum_J u_J(x) dHaar_X(x)
      >=integral_R sum_J[p^-t-a_J(x)-F_J(x)]_+ dHaar_X(x). (CP7b)

A positive noncoverage conclusion requires a positive combined deficit
somewhere; it does not require every old state or every prefix to have
positive deficit. Using a
different old measure gives its mixed product measure instead, not the
same numerical lower bound under full Haar or the physical kernel law.

All integrals in CP7 and CP7a use current/future product HAAR at this fixed x.
The second integrand is nonnegative under the whole-cover premise;
the first is a current/future original-label incidence. Thus completion
slack has an exact multiplicity interpretation.

CP7 is not a Hunter physical-stage intersection. Converting label
incidence to an actual union incidence needs a valid multiplicity bound
under the same law. Converting Haar incidence to the joint physical
kernel law ALSO needs an explicit measure comparison or a direct
physical-law calculation. Neither follows from CP7: clipping can assign
zero physical mass to a Haar-positive bad region when alpha<=delta.
In particular a multiplicity cap alone supplies no positive Hunter edge.

## Exact local completion with1243 incomparable original moduli

Take p=47, future prime53 and current threshold delta=12/23. At height1,
assign24 current labels to the distinct roots1,...,24. Assign one future
label to each residual atom

    (r mod47,s mod53), r in{0,25,...,46}, s mod53.

There are1219 future labels and1243 labels altogether. Let M=1242 and
give label j its own old cofactor

    c_j=3^j*5^(M-j), j=0,...,M,

with old residue0. The current original modulus is c_j*47 and the future
original modulus is c_j*47*53. These are distinct odd moduli. Increasing j
strictly increases the3 valuation and decreases the5 valuation, so the
full moduli are pairwise incomparable in divisibility. This stronger
property is specific to the construction; an arbitrary irredundant
family need not have all its moduli incomparable.

The current47 roots are distinct. Future roots avoid the current ones,
and distinct future atoms disagree at47 or53. Hence the actual original
classes are pairwise disjoint. Each has a private point with old
coordinates0 and its assigned current/future coordinates. The family is
irredundant, yet misses every point with old coordinates1, so is not a
cover of the full period.

On the old fibre x=0, the residual family covers every(47,53) point
exactly once. Its exact data are

    alpha47=24/47<12/23, beta47=0,
    a_J=1/47, F_J=0          on current roots,
    a_J=0, F_J=1/47          on the remaining roots,
    m1=0, F_1^*=1/47.                              (CP8)

Every CP2 root constraint and CP3 hold with equality. Thus original
modulus incomparability, irredundancy and local exact completion do not
force a strict future-prefix deficit. As a direct counting identity,
the complete middle rank of these old exponent pairs also satisfies

    sum_(j=0..M) binom(M,j)^2/binom(2M,M)=1.

No general antichain theorem is needed for the construction or CP8.
The [finite check](../frontier/original_prefix_completion.py), using
Python3.9+ standard-library exact arithmetic, reconstructs all1243
original factor vectors, checks
771903 original pairs for incomparability and literal CRT disjointness,
and checks all2491 residual atoms for exact single coverage. It also
verifies CP8 and the displayed integer identity using exact arithmetic.

The obstruction persists at arbitrary finite current height: use the
24 disjoint current prefixes `j*47^(e-1) mod47^e`, j=1,...,24, at every
e=1,...,H, and complete their complement using actual depth-H47/53
atoms. Give all labels distinct old cofactors from a new middle rank.
On old x=0,

    alpha_H=(12/23)(1-47^-H)<delta, beta47=0,

while a first root above24 stays empty of current labels. Again this is
local completion inside an actual noncover, not a counterexample to a
claim requiring a global cover of every old survivor.

## The largest prime retains an original sibling certificate

Now let p be the largest prime, so no future labels remain. Write each
p-containing original class as C_i times v_i, where C_i is its old CRT
cylinder, v_i its literal depth-e_i current prefix, and its modulus is
`d_i*p^e_i`. At a literal current node v put

    U_v=union_(i:v_i=v) C_i,
    F_v=U_v                                  at depth H,
    F_v=U_v union intersection_(children w)F_w at smaller depths.

Take U_root empty; p-free original classes are already excluded in R.
Finite induction proves that F_root is EXACTLY the set of old points
whose whole current fibre is covered. A full original cover requires

    R subset F_root.                                (CP9)

The following deepest-sibling argument reuses the original-label
maximal-height principle in [problem-details04](../problem-details/04-a-complete-star-family-refutes-the-unrestricted-gamma-73-bound.md).
At x in F_root, take the active original prefixes and remove those with
a shorter active ancestor. Their distinct nodes form a complete prefix
antichain. A node of greatest depth e has all p siblings selected:
otherwise covering a missing sibling would require either a selected
ancestor or a deeper selected node. Choose one actual active original
label at each sibling.

Let T range over the literal original p-tuples with the same depth,
the same parent and one label per child. Each x in F_root belongs to
some intersection I_T of their old cylinders. Therefore, for every
finite positive old measure sigma supported on R, a full cover requires

    sigma(R)<=sum_T sigma(I_T).                      (CP10)

The p old cofactors within a tuple are distinct: equal old cofactors at
equal p-height would repeat an original modulus. Each consistent I_T is
one old CRT cylinder of modulus m_T=lcm_(i in T)d_i; otherwise it is
empty. In particular m_T has at least p divisors. Under old Haar its
mass is1/m_T. Under a supported source it needs that same source's mass
or a proved simultaneous cylinder cap.

Different tuples may yield the SAME derived modulus, or the same old
cylinder. Original-modulus uniqueness does not make these derived events
a distinct-modulus cover. Equal geometric events may be merged in a
union, but their original witness identities cannot become fresh
original labels.

The entire AND/OR recursion retains more than CP10. Its exact union-of-
intersections expansion uses one original label at each leaf of a
complete prefix cut, combining child certificates by set union. It
preserves every original pair(d_i,e_i). A root certificate has
`1+(p-1)k` labels for some k>=1. CRT-inconsistent certificates may be
removed; repeated old cofactors across DIFFERENT depths remain legal.
Actual old masses of these full certificate intersections are concrete
inputs for the exact union calculation. Their number and overlaps are
not controlled merely by the uniqueness of original moduli.

## A complete comb prevents a geometric discount of the forced tuple

Fix an odd prime p>=5 and H>=1. The complete p-ary comb cut has
`L=(p-1)H+1` leaves: take p-1 nonspine children at each depth e<H, then
all p children of the final depth-H parent. These current cylinders are
pairwise disjoint and partition all current leaves. Order them by depth
and assign leaf k the original old cofactor3^k with old residue0.
The original moduli3^k*p^e_k are distinct and odd. Each class has a
private point with old coordinate0, so the family is irredundant.

Under the uniform old Haar law on Z/3^L Z, the full current fibre is
covered precisely on old0 mod3^L. Every current leaf has one assigned
label, so all old conditions are necessary. There is exactly one direct
complete sibling tuple, at depth H. Its old intersection is also
0 mod3^L, because its final p labels include the cofactor3^L. Hence

    sigma(F_root)=3^-L=sum_T sigma(I_T).             (CP11)

The bottom-witness union bound is sharp. Multiplying its depth-e term by
p^(-(e-1)) instead yields3^-L*p^(-(H-1)), whose ratio to the true mass
tends to zero. No uniform positive height-independent factor for that
weighted sum follows from fibre coverage and original-label uniqueness
alone.

Every old point1 mod3 escapes the entire family, so this is an actual
noncovering obstruction to the DISCOUNTED LOCAL argument. It does not
rule out a stronger relation using coverage across all old survivors.
Such a relation would need control of the same-source future-prefix
loads or complete old tree-certificate intersections identified above;
no uniform bound closing those inputs is established here.

The checker also tests comb cuts at p=5,H=1,...,5, and the signed
identity on57 prefixes of a finite7/11 example with all three slack terms
positive. These exact checks support the constructions; the arbitrary-
height statement is the ordinary proof above. The standalone entrypoint
also accepts explicit primes, root count and comb heights:

```sh
python3 -I -S -O docs/reports/erdos7-odd-covering/frontier/original_prefix_completion.py
```

No new Lean declaration, build or frozen result is asserted.

## Established branching and antichain results

[Simpson, Theorem1](https://doi.org/10.4064/aa-45-2-145-152)
(*Acta Arith.*45(1985), pp.147--148), gives p-1 original sibling
classes at every p-adic level of a class in a finite minimal WHOLE
cover; the selected sibling classes are pairwise disjoint and miss the
original class. Its bare statement does not specify one shared old
point. This does not rule out stronger localization: the private-witness
compatibility and weighted capacities already recorded from Lettl--Sun
in problem-details04 retain one common non-p witness. The remaining
obligation for the present transfer is positive mass under the specified
source/killed law and a shared budget for simultaneous events.

[Chudak--Griggs, Theorem1.1](https://people.math.sc.edu/griggs/lubell.pdf)
(author manuscript dated1996-11-01, pp.2--3) proves, for an exponent
antichain E in the fixed product of chains0<=e_q<=H_q,

    sum_(e in E) prod_q binom(H_q,e_q)/binom(sum_q H_q,sum_q e_q)<=1.

This is the binomial-weight Lubell inequality, not a reciprocal-modulus
load bound. Minimality rules out containment of actual congruence
classes, not divisibility of their moduli with incompatible residues.
The antichain hypothesis must therefore be checked separately, as it
is in CP8. Removing old factors can also merge distinct full labels
into repeated residual moduli, and the binomial weights do not become
CP1's weights. CP8 saturates the OLD middle-rank identity; no saturation
of the full-modulus weighted inequality is asserted. These mature
results provide constraints under their stated hypotheses, with no new
whole-cover conclusion for either noncovering construction above.
