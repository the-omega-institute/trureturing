# Secondary pair endpoints admit a same-source release budget

The eight secondary labels at the edge {17,19} may have independently
chosen first roots, while retaining the complete free-star interface of
[Report626](626-free-square-roots-admit-one-complete-boundary-gate.md).
Their actual higher lifts and central phases remain arbitrary. The resulting
ten-prime Haar survivor mass is at least

    4431452026623492378483431
      /924397893305270357144371200000 >1/210000.          (SR1)

The only-large-owner network of Report626 also survives this release.
Its extendible head Haar mass is strictly greater than

    35599326215723254740897196090524662687
      /9292674124624301561266911535067194982400000
      >1/262000.                                       (SR2)

These are ordinary mathematical deductions and exact rational arithmetic,
not new Lean verification. The general criterion below prices any fixed
subset of the eighty secondary labels. Releasing all eighty does not pass
this additive bound. All remaining Report626 inventory, prime and network
restrictions are retained; unrestricted Erdős #7 is not settled.

## 1. Exact released-subset interface

Use the literal core P0={3,5,7,11,13,17,19}, Q={7,11,13,17,19}, and
continuation P1={23,29,31}. Keep Report626's arbitrary pure phases and
finite heights, independently chosen seven-star roots, central15 mask,
and mixed-original inventory. Every numerical original is distinct and
has one residue fixed globally.

At each edge {q,r}, q<r in Q, the primary four labels are

    3^a 5^b qr,             a,b in{0,1}.

Choose a fixed allowed release subset S of the eighty secondary labels

    3^a 5^b q^2 r,
    3^a 5^b q r^2,          a,b in{0,1}, {q,r} subset Q. (SR3)

Each original may be absent. At every edge, the primary labels and all
secondary labels outside S must share one first-root endpoint pair.
Labels in S can have arbitrary independently chosen first roots, with
any collisions. Their central phases and higher lifts are arbitrary too.
If no unreleased source-live original fixes the edge rectangle, choose
one live auxiliary rectangle as in Report626. An already source-null
rectangle and its originals need no avoidance; an additional live
rectangle may be used for the construction.

For SR1 and SR2, S is exactly the eight labels on {17,19}:

    5491,6137,16473,18411,27455,30685,82365,92055.

The four primary labels on this edge remain aligned. On every other
edge all twelve retained labels still share an endpoint pair. Thus this
releases all eight secondary labels on one edge; the primary labels
and the other nine edges keep their stated endpoint restrictions.

## 2. Keep the auxiliary rectangles and impose every actual constraint

Delete the members of S temporarily from the original inventory and
apply Report626's source construction to the remaining actual family.
Keep its common first-root rectangle E_qr at every edge as an auxiliary
deletion. This rectangle avoids every retained primary and unreleased
secondary original on that edge. Its use is legitimate even when the
released originals are not contained in it: an auxiliary deletion only
shrinks the source, and is not a replacement of an actual constraint.

This produces one actual core survivor eta, avoiding every core original
outside S, with the same normalized product-source domination and the
all-height gate

    eta(1)-c Gamma_h(eta)>=gamma,
    c=1084133/201247200,
    gamma=190452499219361/189995609279692800.             (SR4)

Here h denotes a finite resolving height. All full-height query labels
remain present. Report604's complete L/W arrays already exclude the
retained twelve labels once from the remaining-original loss inventory;
the query inventory is independent of whether one of those originals is
present. Omitting S when constructing eta therefore changes neither the
complete query family nor the uniform lower gate.

Let A be the union of the actual, globally fixed original cylinders in
S, and now set eta_new=eta restricted outside A. This enforces every
core original of the actual requested family. No phase is optimized per query,
no mutually incompatible source laws are combined, and no actual released
constraint is discarded.

## 3. The unit-inclusive moment gives the restriction cost

As in [Report598](598-high-support-central-squares-preserve-the-common-survivor-law.md),
Gamma_h is the maximum over the complete squared query loads INCLUDING
THE UNIT QUERY, one globally selected layout per maximum. If L_b is one
such load, then L_b>=1 pointwise. With delta=eta(A),

    integral L_b^2 d eta_new
      <= integral L_b^2 d eta-delta.

Taking the maximum over the same layouts gives

    Gamma_h(eta_new)<=Gamma_h(eta)-delta.

Writing g=1-c=200163067/201247200, SR4 implies

    eta_new(1)-c Gamma_h(eta_new)>=gamma-g delta.         (SR5)

This holds at every height resolving all old and released originals,
and at arbitrary further query heights. Mere monotonicity of Gamma_h
would give only a cost delta; the stronger cost g delta specifically
uses the unit term. No query term is removed to obtain it.

## 4. Uniform caps on the same actual source

Put r_q=1/(q-1) and a_q=1/[q(q-2)]. At a fixed central leaf c0,
[Report623](623-a-common-matching-source-admits-arbitrary-edge-endpoints.md)'s
same-source conditional matching bound, retained in Report626, is

    zeta_c0(A_T)<=product_(q in T) cap_q(A_q) H_T(Z).

The measure eta is a restriction of the central mixture of these same
zeta_c0. For T={q,r}, H_T is the matching polynomial on the remaining
three vertices. Its derivative in a remaining Z_u is the two-vertex
polynomial Z_v Z_w-r_v r_w, strictly positive throughout Report626's
box 1-5r_q-2a_q<=Z_q<=1. Hence

    H_{q,r}(Z)<=h_qr,
    h_qr=1-sum_(u<v in Q\{q,r}) r_u r_v.               (SR6)

This is an upper bound on a response of the same source, not a new
conditional law chosen for this query.

The normalized central product source has two live ternary roots of
mass at most2/3 each and four live quinary roots of mass at most4/15
each. The distinguished live row of the central15 mask therefore has
mass at least1/3, and its live column has mass at least1/5. Their product
rectangle has mass at least1/15. For central exponent roles(a,b), the
remaining central mass caps can thus be chosen as

    kappa00=14/15,  kappa10=2/3,
    kappa01=4/15,   kappa11=8/45,
    sum_(a,b) kappa_ab=92/45.                           (SR7)

The last three caps follow by marginal/product domination; masking can
only reduce them. The first cap retains the central15 deletion instead
of paying an unnecessary unit mass.

Combining SR6, SR7 and the actual first-/second-prefix caps gives

    B(3^a5^b q^2r)=kappa_ab a_q r_r h_qr,
    B(3^a5^b qr^2)=kappa_ab r_q a_r h_qr.               (SR8)

A union bound on the one actual eta now gives

    delta<=sum_(present m in S) B(m)<=B(S),
    B(S)=sum_(m in S) B(m).                             (SR9)

Each actual numerical constraint is charged once, including overlaps.
The sum over all permitted members is uniform in their presence, phases
and higher lifts. It makes no independence claim for the correlated
post-matching source.

Consequently the general released-subset criterion is

    gamma-g B(S)>0.                                    (SR10)

Under SR10, reconstruct the normalized23/29/31 continuation kernels
from eta_new, as in Report598. Do not inherit kernels normalized for a
different core. Product domination, the joint coordinate caps and the
Haar factor alpha=2673/110656 remain valid, giving head Haar mass at least

    alpha [gamma-g B(S)].                              (SR11)

## 5. One complete eight-label edge passes the criterion

For all eight secondary labels at {q,r}, SR8 sums to

    B_qr=(92/45)(a_q r_r+r_q a_r)h_qr.

At {17,19}, exact arithmetic gives

    h_17,19=173/180,
    B_17,19=1141973/1412802000,
    g B_17,19=32654402587313/40617492379200000,
    gamma-g B_17,19
      =4431452026623492378483431
         /22329702581016733522329600000 >0.             (SR12)

Multiplication by alpha gives SR1. This is uniform over all independent
endpoint choices of the actual eight originals, not a finite phase scan.

## 6. The only-large-owner extension pays a separate complete tail

Use exactly Report626 section6's network: every owner is a prime at
least2^115, with any fixed finite union of smaller head primes or earlier
declared owners as parents. Include its pure powers and assigned mixed
inventory, with each original assigned once. There are no added small
owners, private blocks or Type I blocks. All network sizes, parent counts,
depths and resolving heights are arbitrary finite quantities.

After the new core restriction and reconstructed continuation, reverse
integration gives the same joint head prefix caps as
[Report625](625-arbitrary-pure-heads-support-sharper-common-networks.md).
Normalized N=0 half-threshold owner rows, including dead fibres, retain
conditional density below4. The complete cofactor moment and its Euler
tail therefore remain valid on this one actual joint law. The tail fee is

    E115=19740202146111572828188083
           /495176015714152109959649689600.

Pay this once in addition to the release fee. The general network
criterion is gamma-g B(S)-E115>0. For the eight{17,19} labels,

    gamma-g B_17,19-E115
      =249195283510062783186280372633672638809
         /1571313128486890060302786850533566054400000>0. (SR13)

The strict complete-tail estimate and alpha conversion give SR2.
Counting one actual extension for each extendible head class and applying
CRT yields full finite survivor density>1/(262000 Q_off), where Q_off
is the product of the actual outside resolving prime powers. The tail
padding adds no actual small-owner row or unpaid small-owner network.

## 7. Reproduction and the remaining endpoint gap

The [standard-library producer](../../frontier/cover-geometry/square_pair_endpoint_release.py)
and [exact data](../../frontier/cover-geometry/square_pair_endpoint_release.json)
pin the canonical626 and625 certificates and producers, both626 integer
kernels, the inherited source dependencies and the complete604 query
coefficients. They enumerate all eighty distinct secondary labels,
all ten eight-label edges and both four-label orientations of each edge.
They check the central cap sum, all three-vertex response corners and
derivative signs, the two strict projected bounds and the complete tail.
All184 named checks pass under

    python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/square_pair_endpoint_release.py

The previous large source scans are reused, not repeated. The restriction
argument and its common-source construction are ordinary proofs; the
program certifies their rational arithmetic inputs and consequences.

For all eighty labels, this particular additive bound charges

    g B_all=111509457942163301/3127546913198400000
           approximately0.035653968121657255,

which exceeds gamma, approximately0.0010024047394642452. Thus this bound
does not prove the all-edge release. A negative sufficient lower bound
is not an upper bound on survival and is not a covering counterexample.
Among the ten complete eight-label edges, only{17,19} fits this uniform
budget. Partial subsets are governed by SR10, not by an all-or-nothing
edge rule.

The remaining target is to retain the joint incidence of the independently
located secondary events and their interaction with the primary rectangles
inside a stronger common-source estimate. The current positive subclass
does not remove those joint endpoint obligations, the mixed-inventory
restriction, the literal head primes, or the small-owner/private-interface
restrictions.
