[Index](../../marked_head_profile.md) · [Actual retained pair](225-two-original-tests-share-the-complete-retained-bridge.md) · [Joint deletion rows](228-the-complete-pure-three-projection-shares-the-deletion-row-budget.md) · [Whole source domains](208-the-expanded-seven-survival-bound-covers-both-wide-source-domains.md)

# The retained pair shares one off-face deletion budget

The883 old deletion and survivor-link rows of228 can be transported
together with the1610 moving retained135/125 rows of225. Their
combined prices use one actual raw source, one overlap measure W,
and one seven-coordinate residual budget. The original135 and125
profiles stay independent, including their joint membership state.

The helper evaluates all6292 published225 rational duals on each
of208's two complete source domains. It retains each dual's joint
source, primitive and raw-node prices for later consumers. These
are constraint-residual bounds. They are not added to a face
objective and reported as a complete off-face K comparison.
Inherited raw/selected constraints, signed mass, complete tail
prices and every pruning alternative still require transport.
No Lean verification or unrestricted Erdos7 resolution is asserted.

| Source domain | Maximum combined2493-row error |
| --- | ---: |
| sigma<=1/20, rho<=1/1000 |1.1612304610874862...|
| sigma<=1/12, rho<=1/3000 |0.6748502201921622...|

The exact maxima are2835585438320310678433/2441880000000000000000
and18101280706540383579553/26822664000000000000000. Each maximum
ranges over all6292 duals after the full joint field and budget
calculation; it is not the sum of separately maximized old and
retained-label errors.

## 1. Four actual states retain the same overlap measure

Use the canonical K orientation, either of208's established
domains sigma<=d,rho<=R, and its packing gap G. Keep

    W=V-delta>=0, omega=W(1), mu=Lambda-V+W.

For an old rectangle/mask atom C_i, let J and K be the original
135 and125 test cylinders with independently chosen residues.
The four disjoint states are

    S0=J minus K, S1=K minus J,
    S2=J intersect K, S3=(J union K)^c.

Write x_i^a,y_i^a,Omega_i^a for the restrictions of Lambda,mu,W
to C_i intersect Sa. The explicit first three states are225's
u/v variables; state3 is its implicit complement. Then

    sum_a x_i^a=x_i, sum_a y_i^a=y_i,
    sum_(i,a)Omega_i^a=omega.                         (RP1)

From208's shallow upper density and the actual deletion identity,

    mu<=wbar*Lambda+W,
    wbar=wface+Dw,
    Dw_(c,s)=(d/5)*I_(c!=0)+q5*I_H+q15*I_(root1,H).

Therefore all four states satisfy

    y_i^a-wface_i*x_i^a<=Dw_i*x_i^a+Omega_i^a.        (RP2)

The local W term is necessary: away from saturation, virtual
deletions can overlap and V need not equal delta. Neither the
marked events nor their complement can omit this term. The two
partition inequalities on each old atom remain exact.

## 2. The raw profile and pure-five cap perturbations

Keep225's independent25-point lambda135 and five-point lambda125.
The latter selects one common first-five slot across all ternary
cells. Let pre and descendant be the original normalized tables.
208's valid enlarged coefficients are

    prebar_(c,s)=pre_(c,s)+I_(s=Q)*(v0 if c<2 else v1),
    dbar_(c,s)=descendant_(c,s)
                    +(d/18)*I_(c=0,descendant_(c,s)>0).

The P, root1/A and first-beta/B exclusions stay zero. In particular
prebar is not multiplied by eta a second time. The actual raw
marked masses obey

    X135_(c,s)<=lambda135_(c,s)*prebar_(c,s)/27,
    X125_(c,s)<=lambda125_s*dbar_(c,s)/125.           (RP3)

Positive original events use their own point profiles. Absent or
source-null events have zero raw/survivor/W masses and may use
dummy profiles. Convexifying each profile enlarges the containing
model without identifying any original residues.

For fixed nonnegative profile row prices alpha_(c,s),beta_(c,s),
the total additional price over the face matrix is at most

    Cprof=max(0,v0*max_(c<2)alpha_(c,Q),
                  v1*max_(c>=2)alpha_(c,Q))/27
             +(d/2250)*max_(s!=P)beta_(0,s).        (RP4)

Only five135 Q rows and four125 cell0 rows move. Their different
profile maxima remain separate because the residues are independent.

The global135 survivor cap1/135 remains exact by product Haar
domination. The125 cap2/625 needs125(OT5). Put

    c5=sum_c eta_c*a_c-1/90,
    chi=(z5-D)/90, 0<=chi<=d/240,

where z5 is the pure-five source survivor mass. The pure3
projection deficit Xi satisfies Xi>=0 and Xi(1)=E3+chi. Thus

    mu(K)<=h/125,
    mu(K)<=c5/125+Xi(K)+W(K)
           <=c5/125+E27+Ege4+chi+W(K).              (RP5)

The implementation uses the second row. For its face-dual price
theta>=0, source bound c5<=2/5+13d/90 gives the new source price

    theta*[(c5-2/5)/125+chi]<=theta*479d/90000.      (RP6)

It adds theta to the E27 and Ege4 coordinates, and theta*I_K
to the common W price field. It does not add a separate omega
allowance. The first raw row in(RP5) remains a valid possible
refinement but is not used in the reported prices.

Any node survivor caps derived from(RP3) must similarly read

    Y135_node<=wbar*lambda135*prebar/27+W(J intersect node),
    Y125_node<=wbar*lambda125*dbar/125+W(K intersect node).

Dropping these W terms would invalidate that alternative model.
On J intersect K their prices add on the same measure. Full products
of enlarged coefficients must retain their cross terms.

## 3. Merge the fields before either maximum

The seven actual shifted coordinates are exactly

    Y=(E5-Gq5,E15-Gq15,E27,Ege4,E5d,E15d,omega),
    Y>=0, sum Y<=R-G*(q5+q15),
    q5,q15>=0, q5+q15<=R/G.                         (RP7)

For each old atom i, let l_i be the sum of its old survivor-link,
E5-mask-link and coarse E3+E5-link prices. Let a_i^s be its four
new state-density prices. The joint fields are

    raw: l_i+a_i^s,
    W:   l_i+a_i^s+theta*I_(s in{1,2}).             (RP8)

Their maxima are taken only after this addition:

    u_(c,s)=max_(old mask,state)(l_i+a_i^state),
    Q=max_(i,state)(l_i+a_i^state
                             +theta*I_(state in{1,2})). (RP9)

Thus maximizing the old and new prices separately is unnecessary.
Both the raw partition and the W partition share the original
atoms and the retained states.

Let p228 denote228's full seven primitive prices before its final
simplex maximum. Keep its first six coordinates, add theta to
E27 and Ege4, and replace its old union price by Q. Call the result
p229. The helper likewise keeps228's signed E5 source price C5
and its complete E3 source upper C3, but replaces228's old raw LP
and W price entirely. Set

    C=d*C5+C3+Cprof+theta*479d/90000,
    H(q)=max_(X in Pbar)sum_(c,s)u_(c,s)*Dw_(c,s;q)*X_(c,s).

Pbar is208's fixed25-node raw capacity polytope with its three
group budgets. It contains the same actual coarse raw source.
The combined2493-row residual is bounded by

    C+max_(q in vertices)
          [H(q)+(R-G*(q5+q15))*max_j p229_j],       (RP10)

where the vertices are(0,0),(R/G,0),(0,R/G). H is a maximum of
affine functions over a fixed feasible set, hence convex in q.
The residual-budget term is affine. This proves the vertex rule
for(RP10); it makes no convexity assertion about an LP with a
parameter-dependent constraint matrix.

The exact source gaps, pre-cap increments and raw group budgets
are independently reconstructed from195/208's guarded providers.
Each raw LP checks feasible primal and dual witnesses and their
exact rational equality. Future constraint and tail prices must
be added to these same coordinates before spending(RP7).

## 4. Original row identities and fixed-dual meaning

The checker constructs both225 nested/disjoint branches and
compares all old inequality rows0..996 and equalities0..53 with
223. They are identical, so228's physical row interpretation
applies to the inherited prices. Its existing API expects55
equality entries and reads only the first54; the adapter passes
the first55 entries of225's56-entry vector without changing228.

The new constraints divide as follows:

| Class | Count | Error treatment |
| --- | ---: | --- |
| Raw/survivor partitions |800|Exact|
| Moving raw-profile rows |9|(RP4)|
| Unchanged raw-profile rows |41|Exact|
| Four-state density rows |1600|(RP2),(RP8)|
|135 global survivor cap |1|Exact|
|125 global survivor cap |1|(RP5),(RP6)|
| Independent CRT rows |9|Exact|
| Unit caps |3705|Exact|

There are4556 exact new inequalities,1610 moving new inequalities,
and two exact new profile equalities. The old25 aggregation
equalities remain exact. Adding228's883 priced rows gives2493.
Every row is checked against the actual source constructor,
including complement signs, the two-indicator state, original
CRT denominators and the single shared125 slot profile.

For any checked face dual p>=0,z with
c<=Aface^T*p+Eface^T*z, and any actual off-face vector xi>=0,

    c.xi<=Uface+p.(Aface*xi-bface)
                       +z.(Eface*xi-eface).          (RP11)

This algebraic residual formula does not require xi to be face
feasible.225's objective already separates the raw seven increment
from the actual survivor hinge, so those coefficients do not
change when wface changes. Signed equality prices retain their
signs. Formula(RP10) prices only the stated2493 residuals in(RP11).
The remaining nonzero residuals cannot be silently discarded.

The certificate contains each of6292 duals' combined source,
seven primitive and25 raw-node prices, every triangle value,
field digest and the two heavy controllers. It also retains raw
primal/dual witnesses for the controllers and largest priced
records. Every other raw witness is recomputed and checked by
the helper. No new original-head scan or numerical optimizer
is used in this calculation.

The wire format shares the complete record structure and interns
its53 rational fields. Each record keeps its original dual key
and full W-field hash in separate columns. The helper exports
`decode_price_bank(domain['encoded_price_bank'])`, returning the
original complete key-to-record dictionary. All12584 records
were compared field by field with the original representation;
their JSON field order is preserved as well. No numerical field,
sign, denominator, node price or triangle value is discarded.

With the existing certificate IO, this representation has45
physical JSON parts and7,538,323 logical bytes, compared with
13,151 parts and45,160,742 bytes for the per-record object tree.
The measurements count every JSON under the certificate's parts
directory and every byte reconstructed by `read_artifact_bytes`.
The mathematical price data and the two maxima above are identical.

## 5. Complete-tail interfaces keep both retained labels

For a later complete consumer, let T3(O),T5(O),T15(O),T45(O)
be125's complete OT4--OT8 assigned cap series, starting at depths
(3,2,2,2), with exactly the specified original depths omitted.
Their finite crossings are followed by the full geometric tails.
The225 policy has the exact assigned remainders

    R0off=T3(empty)+T5(empty)+T15(empty)+T45(empty)+1/72,
    R6off=T3({3,4})+T5({2,3})+T15({2})+T45(empty)+7/1080.
                                                               (RP12)

The last constant is1/72-1/135: original135 removes a fixed
product-Haar summand. Original125 removes the b=3 summand of
the actual OT5 series. It does not justify subtracting face
constant2/625 from an independently optimized off-face tail.
At saturation these formulas give163/1800 and7579/405000.

All six retained seven projections also have a complete positive
assigned remainder. With N3 the largest raw root mass, N9 the
largest raw cell mass, em=max eta_c and D=max d_c, put

    Ccofactor=N3+N9+D/18+(h+h1+em)/4+1/72.

Remove the four depth-one labels21,35,63,105 and the two depth-two
labels147,245 from that same cap series. The remaining sum is

    Z6off=Ccofactor/5-(6/35)*(N3+h/5+N9+h1/5)
                              -(6/245)*(N3+h/5)
          =N3/245+N9/35+D/90+53h/4900
                              +11h1/700+em/20+1/360. (RP13)

Its coefficients are positive. At the face
(N3,N9,D,h,h1,em)=(5/36,1/12,3/4,1/2,1/3,1/9), it gives
2669/88200 exactly. Every unit7^e remains in the retained bridge;
the125/135 zero-seven labels change no positive-seven term.

Substituting158's scalar source envelopes, with their195 extension,
gives the six-loss price vector in order(ua,uz,ub,ud,ul,up)

    (1/2940,23/5880,1/8820,29/44100,0,0).

The largest coefficient is23/5880, and its second-largest is at
most(1-d)*23/5880 throughout d<=1/12. Thus156's exposed-price
inequality yields the complete source-only interface

    Z6off<=2669/88200+23d/5880.

This is a bound for the same assigned positive-seven series.
It is available to a subsequent full-tail consumer and is not
added to the2493-row prices reported here.

The complete tail for a nonnegative hinge combination is

    a1*(R0off+Z6off)+sum_(t>=2)a_t*(R6off+Z6off).    (RP14)

The checker verifies the face specializations and the positive
coefficient identity. These tails are **not** included in(RP10).
Their defect prices need compatible supporting expressions and
must join(RP7); arbitrary min/crossing functions do not supply
a general defect-vertex theorem. Nonnegative finite prefixes
pass to all original independent labels by monotone convergence
and the complete geometric sums.

The [helper](../../frontier/retained-transport/retained_pair_row_transport.py) and its
[certificate](../../certificates/source_norms/retained-transport/retained_pair_row_transport.json)
provide the joint2493-row data:

```sh
python3 -I -O docs/reports/erdos7-odd-covering/frontier/retained-transport/retained_pair_row_transport.py --check
```

Complete off-face transportation still needs the inherited raw
caps and selected profiles, remaining scalar survivor caps,
signed actual mass, complete tail prices, every earlier pruning
candidate and the full52-cost/survival consumer with its outside
regions. This result supplies their combined retained-label and
deletion-row input without claiming those further conclusions.
