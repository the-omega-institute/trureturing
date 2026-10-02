# Optimal fixed leaf weights admit the complete1200 tail

Let C be a finite family of pairwise-distinct odd numerical moduli greater
than one, each with one globally fixed residue. Let R contain every actual
support prime at most1200, and assume |R|<=8. If every original whose
complete support lies in R satisfies v3(m)<=2, then C is noncovering. A
constructed distorted survivor measure has mass greater than1/10000.

Originals touching a prime above1200 retain arbitrary finite heights and
mixed support. The number of tail primes is unrestricted but finite.
The distorted mass is not the final Haar density. These are ordinary
mathematical arguments and exact finite comparisons, not Lean verification.

This improves the1300 cutoff of
[Report791](791-uniform-shared-deficits-lower-depth-two-tail-cutoff-to1300.md).
It also identifies exactly how far globally fixed leaf weights can improve
Report791's equal-degree shared-deficit source response. The resulting
limit concerns this particular source certificate and query comparator;
it neither bounds the actual survivor mass above nor settles unrestricted
Erdos7.

## 1. One fixed source law and its concave response

Retain Report791's actual five nine-leaves, grouped A={0,1}, B={2,3,4},
the seven nonternary benchmark coordinates

    Q=(5,7,11,13,17,19,23),

and the source domination, completed star budgets, original shared mixed
allocations and equal-degree deficit shares proved there. Replace only the
fixed leaf law by

    w=(a,a,b,b,b),    b=(1-2a)/3,    0<=a<=1/2.             (FW1)

The complete signed response and shared deficit credits are unchanged.
In Report791's notation the strengthened response at a star profile L is

    F_L(w)=S0-sum_(D:degD=0) max A_D
             +sum_edges min[P_DE-A_D/degD-A_E/degE]
             -sum_triples max T_DEF.                      (FW2)

Every coefficient before a maximum or minimum is linear in w. Thus F_L is
concave in w. Its separate concavity in the star coordinates also remains
valid for every fixed nonnegative w, so the continuous star domain reduces
to the10^7 vertex profiles. Define the uniform certified mass

    M(w)=min_L F_L(w).                                    (FW3)

This minimum is concave in w: apply concavity to every L and then take the
minimum. It is invariant under S2 x S3 permutations within the two root
groups. Averaging any fixed weight vector over this group therefore cannot
decrease M. Hence an optimum over ALL globally fixed five-leaf laws has a
representative of form(FW1). This reduction does not optimize weights afresh
at different star profiles.

## 2. Two profiles give an exact upper certificate for every weight

Write a role(r,t) with r=0 for root A and r=1 for root B. In increasing
coordinate order consider

    Lplus =((1,2),(0,0),(0,1),(0,1),(0,1),(0,1),(0,1)),
    Lminus=((0,0),(1,2),(1,3),(1,4),(1,3),(1,4),(1,4)).

From(FW2), select one affine candidate in each minimum and one candidate in
each subtracted maximum. Their sum is a global affine upper bound on the
profile response, whether or not those choices remain extremal at another
weight. Exact choices at the crossing point below give

    F_Lplus(a) <= Lplus(a)
      =[-301906006+1473412322 a]/3411483075,

    F_Lminus(a) <= Lminus(a)
      =44178103/310134825-(9023647/14995530)a.             (FW4)

These are supporting lines, not linear extrapolations of sampled values.
The checker derives them directly from all10 first roles, all100 pair
roles, and all1000 triple roles; it evaluates the resulting bound and the
baseline-plus-credit expression independently at their intersection.

The first line is strictly increasing and the second strictly decreasing.
They meet inside[0,1/2] at

    a*=525243426/2350861343,
    b*=1300374491/7052584029.                              (FW5)

Consequently, for every a in[0,1/2],

    M(a)<=min(Lplus(a),Lminus(a))<=m*,
    m*=64160977192969114/8019923683316269725
       =.008000197972761544... .                          (FW6)

By the symmetrization argument this is also an upper bound on M(w) for
arbitrary fixed nonnegative five-leaf weights summing to one.

## 3. Complete comparison attains the upper bound

Use integer leaf weights

    (wa,wa,wb,wb,wb),
    wa=1575730278,    wb=1300374491,
    2wa+3wb=7052584029.

Their normalized values are(FW5). The same S2 x S3 reduction as Report791
has7261 canonical leaf words and128 root assignments each, or929408
canonical profiles. Their orbit weights cover exactly10^7 raw vertices.

Pair credits are nonnegative. Therefore any profile whose baseline is at
least1/100 already exceeds the proposed minimum. All929408 baselines are
scanned; only722 profiles require explicit pair refinement, with all546
edges and100 color pairs on each edge. The exact smallest refined value is

    256643908771876456/32079694733265078900=m*.             (FW7)

It is below1/100, hence is the global minimum. Lplus and Lminus both attain
it. The separate rational evaluations give

    G(Lplus)=222646444984111/56083382400813075,
    credit(Lplus)=4617505080034463/1145703383330895675,

    G(Lminus)=282878959358833/56083382400813075,
    credit(Lminus)=4741857200931199/1603984736663253945.     (FW8)

This proves equality in(FW6), not merely an upper envelope from two test
profiles. The baseline uses the existing Report789 producer, whose sum of
absolute terms here is bounded by132087275019834651<2^63. Pair terms and
the common denominator use signed128-bit integers; the full producer was
run with undefined-behavior sanitization. No floating value decides a
comparison.

## 4. The same unnormalized source pays the entire1200 tail

The source has ternary root cap r and leaf cap v given by

    r=max(2a*,3b*)=1300374491/2350861343,
    v=max(a*,b*)=525243426/2350861343.

The all-height fourth-query factor is1+15r+216v. As in Reports790--791,
this follows from arbitrary-phase conditional hinge rearrangement and
ordered-lcm moment expansion, not from identifying arbitrary query phases
with one physical matching-prefix run. The very same unnormalized source
has the complete mixed fourth bound

    K=(1+15r+216v) product_(q in Q)[1+((q-1)/(q-2)) A4(q)]
     =1995816314082394584902043010164181
        /6513156637804234575590400000,

    A4(q)=15t+50t^2+60t^3+24t^4,    t=1/(q-1).            (FW9)

Use [Report734](../700-749/734-seven-and-eight-full-height-heads-admit-quartic-prime-tails.md)
with delta=2/7, growth exponent21, cutoff1200 and ell=6. The complete
prime-tail coefficient is

    tau=(21609/10240)(73/71)^21 [1200/1199^4]
          sum_(j=0..21)21!/[(21-j)!18^j].

Exact arithmetic gives

    m*-K tau=.00013953907533249908...>1/10000.             (FW10)

The missing3 branch uses Report789's squarefree head bound on
(5,7,11,13,17,19,23,29), and independently exceeds1/10000 at the same
cutoff. The existing prefix transport covers fewer than eight small support
primes and arbitrary larger small-prime choices. Only originals wholly
supported in the actual small-prime set require ternary depth at most two;
tail-bearing cofactors retain every finite exponent.

For this weight, the first positive integer cutoff in the checked valid
window729..1300 is1193. A bound greater than1/3000 first occurs at1211.
There is also an exact optimization statement for the positive threshold.
The mass/fourth ratio M(w)/K(w), as well as the mass itself, is maximized
by(FW5) among all globally fixed five-leaf laws in this equal-share template.

To see this, symmetrization increases M, leaves the two root masses fixed,
and decreases the maximum leaf weight, so it decreases K. For M>0 this
cannot decrease M/K; a nonpositive M cannot beat the positive candidate.
For symmetric weights the ternary factor of K is

    k3(a)=88-174a,   0<=a<=1/5;
           16+186a, 1/5<=a<=1/4;
           1+246a,  1/4<=a<=1/2.                         (FW10a)

The remaining factor in K is independent of a. Divide the increasing
supporting line in(FW4) by k3 to the left of a*, and the decreasing line
by k3 to the right. For an affine numerator c+da and denominator u+va,
the derivative sign is that of du-cv. The four exact signs are positive,
positive, negative, negative on the successive intervals cut at1/5,a*,1/4.
Thus both upper ratio envelopes reach their joint maximum at a*, where
the response attains its upper certificate. This proves the ratio optimum.

It follows that NO fixed leaf law using this equal-share mass certificate
and this particular Report734 tail estimate has positive remaining mass
at an integer cutoff729<=B<1193. Here delta=2/7, growth exponent21 and
ell=6 are fixed; these cutoffs obey B>=286,3^ell<=B and4ell>=21. Below729
there is no allowed integer ell for this chosen growth exponent: ell<=5
violates4ell>=21 and ell>=6 requires B>=729. At B=1193 the same fixed law
does give positive remaining mass. This is an optimal cutoff for these
specified certificate parameters and fixed-leaf equal-share laws, not
an optimum over other sources, deficit shares, growth exponents or clipping
parameters. The convenient theorem above retains cutoff1200 and its
simple lower bound1/10000.

## 5. Fixed weights alone cannot reach the pure29 hinge threshold

The continuation mechanism of Report790 requires a complete first-query
bound B(mu)<28 before adjoining the pure-conditioned29 law. Its source-mass
and product-cap certificate is

    B(mu)<=h+H_(r,v)(h)/alpha,    h>=1,
    H_(r,v)(h)=E(M_(r,v)-h)_+.                            (FW11)

Here alpha is the certified retained source mass and M is the auxiliary
product comparator. At3 its run tails are r at depth one and
v/3^(e-2) at depths e>=2; at q in Q they are
[(q-1)/(q-2)]q^-e. Every fixed five-leaf probability law satisfies

    r>=1/2,    v>=1/5.

Thus the common-uniform coupling gives a stochastic lower comparator M0
with exactly these two cap values. It need not itself arise from a physical
five-leaf law; that is unnecessary for a universal lower bound on H.
For every h, H_(r,v)(h)>=H0(h).

For B(mu)<28, necessarily h<28 and

    alpha>H0(h)/(28-h).                                  (FW12)

M0 is integer-valued and has mean

    EM0=(9/5) product_(q in Q)(q-1)/(q-2).

All its atoms below28 are computed exactly from the independent geometric
run tails. The identity

    H0(h)=EM0-h+sum_(j<h)(h-j) Pr(M0=j)

retains the COMPLETE upper tail. Between consecutive integers the quotient
in(FW12) is a linear-fractional function with constant derivative sign,
so its minimum occurs at an integer endpoint. As h approaches28 it
strictly diverges. Exact comparison at h=1,...,27 gives the unique minimum
at h=16, with

    min_(1<=h<28) H0(h)/(28-h)
       =.022526522831384527...>9/400=.0225>m*.                    (FW13)

The full rational value and all27 comparisons are retained in the checker
output. Thus no fixed five-leaf law, using Report791's equal-degree
shared-deficit mass certificate and this cap-based complete hinge bound,
can uniformly certify B(mu)<28. For every fixed law at least one star
profile has certified mass at most m*, below the necessary threshold.

This identifies a method boundary: additional source structure, stronger
joint constraints, a different mass estimate or a sharper query bound is
needed. It does not show that the actual survivor measure fails B<28, and
it does not exclude weight choices that depend on a proved profile-specific
construction. Arbitrary ternary heights of the old-only originals remain
outside the new noncovering theorem.

## Reproduction and scope

The [producer](../../../frontier/cover-geometry/refined-capped-source/depth2_fixed_weight_optimum.cpp)
includes the adjacent Report789 baseline source;
it does not copy that algorithm. Compile the paired C++ producer with
Clang C++17 and undefined-behavior sanitization, then feed its JSON to the
Python consumer under isolated Python. The consumer recomputes both
supporting lines, both exact profile responses, the full comparator hinge
and the complete prime tail. It rejects incomplete coverage or altered
minimum/cutoff data. All these checks concern ordinary exact arithmetic;
no Lean compilation is asserted. The [complete enumeration](../../../frontier/cover-geometry/refined-capped-source/depth2_fixed_weight_optimum_enumeration.json),
[exact consumer](../../../frontier/cover-geometry/refined-capped-source/depth2_fixed_weight_optimum.py)
and [rational result](../../../frontier/cover-geometry/refined-capped-source/depth2_fixed_weight_optimum.json)
retain the inputs and comparisons needed to reproduce these conclusions.

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/refined-capped-source/depth2_fixed_weight_optimum.py
```
