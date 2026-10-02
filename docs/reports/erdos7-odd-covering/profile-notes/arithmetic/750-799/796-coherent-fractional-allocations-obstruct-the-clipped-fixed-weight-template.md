# Two coherent fractional allocations obstruct the clipped fixed-weight template

Clipping each leaf's signed response at zero does not make the complete
five-leaf source template uniformly sufficient for the pure-conditioned29
step, when the leaf weights are fixed globally and queries still use the
product-cap hinge of Reports790 and792. Two complete rational allocations,
together with their within-root relabelings, prove this statement over the
full relaxed star and mixed-allocation domain.

Each of the two witnesses has NONNEGATIVE responses on every leaf, with
three responses exactly zero. Thus this obstruction survives the clipping
that the negative-leaf witnesses of
[Report793](793-common-colours-bound-the-unclipped-fixed-weight-source-template.md)
explicitly left open. Its comparison uses the actual weight-dependent hinge;
the universal lower floor .02252652 alone is insufficient here.

The witnesses are complete COMMON allocations of the relaxed budgets, not
realized original covering families. The result is a limitation of the
specified mass certificate paired with the specified query estimate. It does
not bound actual survivor mass above, exclude additional arithmetic or phase
constraints, exclude weights selected after the star profile is known, or
resolve unrestricted Erdős #7. Everything below is ordinary mathematics and
exact rational arithmetic; no Lean verification is claimed.

## 1. The clipped certificate and the query threshold

Retain the seven nonternary coordinates

    Q=(5,7,11,13,17,19,23),    D0=product_(q in Q)(q-2)=7952175,

and the two ternary root groups A={0,1}, B={2,3,4} from
[Report791](791-uniform-shared-deficits-lower-depth-two-tail-cutoff-to1300.md).
Every star coordinate has one joint root/leaf allocation; every mixed
support D subset Q, |D|>=2, has one joint root/leaf allocation. The same
mixed allocation is used in every first, pair and triple term containing D.
There are120 mixed supports,546 disjoint pairs and210 disjoint triples.

For a complete allocation x let R_l(x) be the full signed source response
on leaf l, BEFORE applying a leaf weight. The clipped response is

    Phi(w,x)=sum_l w_l max(R_l(x),0),
    Fclip(w)=inf_x Phi(w,x),                                     (CL1)

where w is one probability vector on the five leaves and x ranges over the
complete relaxed domain above. Actual surviving leaf masses are nonnegative
and dominate their signed responses, so CL1 is a legitimate clipped lower
certificate. The obstruction concerns its best uniform value over that
relaxed domain; extra restrictions might exclude the witnesses.

For symmetric weights write

    w=(a,a,b,b,b),    b=(1-2a)/3,    0<=a<=1/2.

The complete product comparator in Report790 uses

    r(a)=max(2a,1-2a),    v(a)=max(a,(1-2a)/3),

as its depth-one ternary root cap and depth-two leaf cap. The ternary run
has tails r at depth1 and v/3^(e-2) at depth e>=2. Every q in Q has tails
[(q-1)/(q-2)]q^-e. Let M_(r,v) be the product of the independent auxiliary
run lengths plus one, and write H_(r,v)(h)=E(M_(r,v)-h)_+.

The declared query certificate is

    B(mu)<=h+H_(r,v)(h)/alpha,    h>=1.                          (CL2)

For this expression to be strictly below28, necessarily h<28 and

    alpha>T(a):=inf_(1<=h<28) H_(r(a),v(a))(h)/(28-h).             (CL3)

The original product comparator is retained. Replacing it by a sharper
star-conditioned query estimate is outside the present limitation.

## 2. Two complete rational common allocations

Use role(r,t), with r=0 for root A, r=1 for root B, and t in{0,...,4}.
Its mixed multiplier on leaf l is

    c_l(r,t)=1+1_(group(l)=r)+1_(l=t).

Convex combinations give a shared root probability and shared leaf
probability. The [certificate](../../../frontier/cover-geometry/refined-capped-source/clipped_common_source_obstruction_certificate.json)
contains every star allocation and all120 mixed roles in increasing binary
support-mask order. Bit0 represents5, bit1 represents7, and so on. Every
unmentioned role in the descriptions below is the certificate's fixed
vertex, not an independently chosen role for a different term or leaf.

Witness A keeps the six stars at7,11,13,17,19,23 equal to

    ((0,0),(0,1),(0,1),(0,1),(0,1),(0,1)).

Its5-star root is B, with leaf probabilities

    (y2,y3,y4)=(2226446,2771867,1818236)/6816549.

Only mixed mask7={5,7,11} is fractional. It mixes roles(0,0) and(1,0), with
probability104825/171999 on(0,0). All other mixed supports have one fixed
vertex role. Its exact full leaf responses are

    R_A=(2888347783/455922049275,
         6022874378/65131721325,
         0,0,0).                                               (CL4)

Witness B keeps the six later stars equal to

    ((1,2),(1,3),(1,4),(1,3),(1,4),(1,4)).

Its5-star root is A, with leaf0 probability394292/2272183 and the remaining
probability on leaf1. Mixed mask5={5,11} mixes(0,0) and(1,0), with probability
60083/67435 on(0,0). Mixed mask6={7,11} mixes(1,2) and(1,3), with probability
561431623/625594495 on(1,2). Every other mixed support is a fixed vertex.
Its exact responses are

    R_B=(0,0,0,
         397674116620058/4974836903276625,
         17363616113/178751640375).                              (CL5)

All stated probabilities are in[0,1] and each star and mixed distribution
sums to one. EquationsCL4--CL5 are nonnegative leaf by leaf, so clipping
leaves them unchanged.

These fractions arise from exact linear systems. In A, the fractional
mixed support contains5, so no signed matching term contains both its
multiplier and the5-star retained factor. The five responses are jointly
affine in y2,y3 and the mixed root probability. Setting R2=R3=R4=0 is a
three-variable linear system. In B, the two fractional mixed supports
overlap, the first contains5, and the second's changing leaf allocation
only affects leaves2 and3 while the5-star split changes only leaves0 and1.
Thus products of the three changing parameters again vanish leafwise.
Setting R0=R1=R2=0 gives the second exact linear system. The retained
certificate is checked by the complete polynomial, independently of this
simplification argument.

## 3. The clipped upper envelope for symmetric fixed weights

Set

    U=sum_(l in A)R_A,l=5005385381/50658005475,
    V=(1/3)sum_(l in B)R_B,l=80083719696451/1356773700893625.

Both witnesses are in the relaxed domain, so

    Fclip(a)<=E(a):=min(Ua,V(1-2a)).                             (CL6)

The lines cross at

    a0=16835279638307625671/61852633133978949697
       =.272183717...,

and their upper-envelope peak is

    E(a0)=400849879824717592982831/14904938269460577403234575
          =.026893763166133844... .                             (CL7)

This exceeds the universal floor .02252652. That floor does not prove the
obstruction for all weights. The needed statement is the comparison with
T(a), which includes how the same leaf weights change the query caps.

For the particular optimal weights of Report792,

    a*=525243426/2350861343,
    Phi(w*,x_A)=876348588655585102/39696648928219950975
              =.022076135198218147...<.02252652.                 (CL8)

Thus even that single fixed law is obstructed after clipping. The full
all-weight statement below needs both witnesses and the actual hinge.

## 4. Exact comparison with every threshold and every weight

For the nonternary product define C=product_(q in Q)(q-1)/(q-2).
The full mean of M_(r,v) is(1+r+3v/2)C. Its probability at every integer
below28 is affine in r,v: the ternary factor has probabilities

    Pr(1+J3=1)=1-r,
    Pr(1+J3=2)=r-v,
    Pr(1+J3=j)=2v/3^(j-2),    j>=3.

Convolving with the fixed nonternary geometric laws therefore computes

    Q_h(r,v):=H_(r,v)(h)/(28-h)
             =c_h+d_h r+e_h v,    h=1,...,27.                    (CL9)

The exact arithmetic uses

    H_(r,v)(h)=EM_(r,v)-h
               +sum_(j<h)(h-j)Pr(M_(r,v)=j).

Only the subthreshold atoms are enumerated. The complete mean includes
ALL higher exponents, so this is not an upper-tail truncation.

Between consecutive integer h, H(h)/(28-h) is linear-fractional with
constant derivative sign. At28 it diverges because the geometric product
has a positive unbounded tail. Hence

    T(a)=min_(h=1,...,27) Q_h(r(a),v(a)).                         (CL10)

The cap functions are affine on[0,1/5],[1/5,1/4],[1/4,1/2]. The envelope E
has one additional breakpoint a0. Thus Q_h(r(a),v(a))-E(a) is affine on
each interval determined by

    0,    1/5,    1/4,    a0,    1/2.

All5*27=135 endpoint inequalities are evaluated as exact rational numbers.
Every one is strictly greater than1/1000. For orientation, the minimum
threshold and gap at the five endpoints are:

| a | E(a) | T(a) | T(a)-E(a) |
|---|---:|---:|---:|
|0|0|.03861948210196479|.03861948210196479|
|1/5|.019761478305616215|.023926113859596573|.004164635553980358|
|1/4|.024701847882020272|.025937149379954536|.001235301497934265|
|a0|.026893763166133844|.028071319559614394|.001177556393480551|
|1/2|0|.04998823726386481|.04998823726386481|

The minimizing integer threshold is16 at these endpoints. The exact
endpoint inequalities, rather than rounded decimals, imply throughout
[0,1/2] that

    Fclip(a)<=E(a)<T(a)-1/1000.                                  (CL11)

This contradicts the necessary certificate requirementCL3 for every
symmetric fixed leaf law.

## 5. Why nonsymmetric fixed weights cannot escape

Let w be any fixed five-leaf probability vector. Average it within the two
root groups to obtain

    wbar=(a,a,b,b,b),
    a=(w0+w1)/2,    b=(w2+w3+w4)/3.

For EACH of the two common allocations, consider its12 relabelings by
S2 x S3. Relabel all star leaves and all mixed colors simultaneously. These
are12 complete common allocations; no per-term choices are made. The
average of their clipped responses under w equals the original allocation's
clipped response under wbar. At least one relabeling has value no larger
than that average. Applying this to both witnesses proves

    Fclip(w)<=E(a).                                              (CL12)

There are24 witness tables in this finite orbit argument. The same statement
also follows from concavity and within-root invariance of Fclip, but the
explicit average makes the common-source quantifiers visible.

The root cap is unchanged by the weight average:

    r(w)=max(w0+w1,w2+w3+w4)=r(wbar).

The largest leaf weight can only decrease:

    v(w)=max_l w_l >=max(a,b)=v(wbar).

Couple the auxiliary runs with common independent uniforms. Increasing
these tails stochastically increases M and every hinge. Consequently

    T(w)>=T(wbar)=T(a).                                          (CL13)

CombiningCL11--CL13 gives, for every globally fixed w,

    Fclip(w)<T(w)-1/1000.                                       (CL14)

The direction matters: symmetrizing the source weights makes the query
threshold easier, while the relabeled common witnesses already obstruct
that easier threshold.

The quantifiers remain “for every fixed law, some complete relaxed allocation
obstructs this certificate.” No single allocation is claimed to obstruct
every possible weight simultaneously. Weights adapted to a known profile,
extra joint restrictions on actual numerical originals, a stronger source
bound or a sharper query comparator remain possible routes.

## 6. Exact reproduction

The standard-library [consumer](../../../frontier/cover-geometry/refined-capped-source/clipped_common_source_obstruction.py)
checks every common probability, every mixed root/leaf marginal, the full
support inventory, all ten exact leaf responses and all135 endpoint
inequalities. It imports no optimizer. Its
[result](../../../frontier/cover-geometry/refined-capped-source/clipped_common_source_obstruction.json)
is compared with a complete fresh computation.

An independent computation of the leaf responses uses the matching
recurrence. For a least coordinate q in S, put

    Z_l(empty)=1,
    Z_l(S)=mraw_ql Z_l(S minus{q})
       -sum_(D subset S,q in D,|D|>=2)c_Dl Z_l(S minus D),
    R_l=Z_l(Q)/D0,

where mraw_ql=(q-2)-x_q,group(l)-y_ql. Each disjoint support collection is
counted once by its least remaining coordinate; at seven coordinates this
is exactly the120 first,546 pair and210 triple expression. The recurrence
uses the same c_D in every occurrence, and agrees exactly with the original
full-sum evaluation of the rational candidates.

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/refined-capped-source/clipped_common_source_obstruction.py
```

The separate profile successes of
[Report795](795-retained-leaf-bounds-admit-twenty-nine-at-both-opposing-profiles.md)
are consistent with this limit:
they retain their specified star profiles. The present obstruction uses
additional fractional star allocations in the full relaxed domain and
addresses a uniform fixed-weight guarantee over that larger domain.
