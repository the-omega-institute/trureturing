[Index](../../marked_head_profile.md) · [Sixteen original tests](218-the-retained-deletions-control-sixteen-complete-tests.md) · [Complete pruning candidates](233-explicit-pruning-errors-preserve-all-four-face-ceilings-near-the-source.md) · [Generated source domain](234-every-retained-dual-transports-on-a-generated-small-source-domain.md)

# The sixteen legacy heads transport with their survivor-cap prices

All sixteen complete head bounds of218 extend to the positive source
rectangle

    0 <= delta <= 10^-8, 0 <= rho <= 10^-11,
    common wrong-slot gap G = 1/60.                         (LH1)

Here delta is the source-radius endpoint, not the deleted measure.
The exact certificate prices every one of218's16,391 fixed duals,
including8,483 with nonzero prices on the four original selected
survivor caps. Each test retains its original positive hinge vector,
all62,500,000 containing choices, all pruning alternatives, and all
original infinite-tail labels. A uniform residual bound is attached
to each original face candidate; raw objective values from unrelated
tests are never pooled.

These are ordinary source inequalities with exact rational arithmetic.
The result is sixteen complete heads. It does not transport218's
other cost entries, previous face-only majorants or integer-identity
feedback, and does not assemble a52-cost signed numerator, count-law
denominator or K comparison. Actual-family attainment, Lean
verification and an unrestricted Erdos7 conclusion are not asserted.

## 1. The legacy matrix and its source-bound coefficients

The original containing system has875 variables,581 inequalities
and16 equalities. It is the unchanged prefix of225's larger system.
Its moving rows consist of the28 raw cap/group rows,18 selected
profile rows,400 density links, four survivor-cap rows,25 coarse
deletion links,15 E3 root1-zero rows and five E3 lower rows. The
other86 inequalities remain exact. Equalities0--3 are exact profile
normalizations; equality4 is the survivor-mass equality and has
price zero throughout the bank; equality5 has a nonnegative raw-mass
price throughout the bank. Equalities6--10 are the signed E3
marginals and11--15 the signed E5 totals.

All these counts and the original matrix specification are checked.
The original coefficient vectors are read directly from218's scans:
four AP11 blocks, AP13, and the eleven affine-tail indices

    1,2,7,10,17,18,23,26,32,33,36.

The affine constants f(1) are zero for these eleven tests. Thus their
transported hinge bounds are direct bounds for the original costs;
no new signed-mass term is hidden in this statement.

For each fixed dual write y_i>=0 for its inequality prices and z_i
for its equality prices. With y_i=0 for absent entries, the shared
raw-node field is

    u_(c,s) = max_M [y_(132+16(5c+s)+M)+y_(coarse(c,s))].

There are no additional marked-state or fixed-H prices in218.
The signed E3 and E5 formulas of227--230 therefore specialize
without those extra terms. In particular, their seven primitive
prices use the common order

    (E5-Gq5, E15-Gq15, E27, Ege4, E5d, E15d, omega).  (LH2)

The original raw cap, group and nonnegative raw-mass prices enter
one25-node support calculation together with this same density
field. At q=(q5,q15), its coefficients are

    y_i + y_(25+group(i)) + z5
      + u_i*[delta/5*1_(c!=0)
             +q5*1_(s=4)+q15*1_(c>=2,s=4)].          (LH3)

Subtract the old raw cap/group RHS and z5/4 once. The resulting
signed support increment can be negative. It is not clipped before
adding the other terms. The raw caps, group budgets and all forcing
parameters are234's generated enclosing values for(LH1).

## 2. The four old survivor-cap prices must be added

The larger-bank transport230 assumes zero prices on rows532--535.
That condition fails for8,483 legacy records, so it cannot be
reused on218 without the following additions.

Let b25,b27,b75,b81 be the four prices and put b3=b27+b81.
The complete cylinder envelopes of125 and the source bounds of234
give

    c3 <= 7/10+delta/4,
    c5 <= 2/5+13delta/90,
    c1 <= 4/15+delta/15,
    eps3 = E5+E5d+kappa*(E15+E15d)+omega,
    eps5 <= E27+Ege4+delta/240+omega,
    kappa <= kbar = (6-delta)/(3-2delta).

The root0 branch of the75 cap remains dominated: its available
margin is at least1/30-4delta/45>=7/270 through delta=1/12.
At the original depths,125's min(e,H/p^n)<=e therefore yields

| Original label | Old face cap | Additive cap motion |
| --- | ---: | --- |
|25|2/125|13delta/2250+delta/240+E27+Ege4+omega|
|27|7/270|delta/108+eps3|
|75|4/375|delta/375+omega|
|81|7/810|delta/324+eps3|

The defect appears once in each selected cylinder bound, without
an exponent-count multiplier. The weighted source increment is

    delta*[13b25/2250+b27/108+b75/375+b81/324+b25/240]. (LH4)

The addition to the seven primitive prices(LH2) is

    (b3,kbar*b3,b25,b25,b3,kbar*b3,b25+b3+b75).        (LH5)

Because the first two coordinates in(LH2) are shifted defects,
there is also the explicit term

    G*b3*(q5+kbar*q15).                              (LH6)

Omitting(LH6) would spend the wrong-slot budget twice in different
coordinates. All cap and old-row prices are combined before the
single remaining defect budget is optimized.

The helper separately compares eight zero-cap, zero-padded legacy
records with the general229/230 APIs. The source values, all seven
primitive prices, raw base/subtraction, density fields and all three
raw support values agree exactly. These comparisons include both
all-bank residual controllers and records maximizing the four cap
prices and raw-mass price. The four additions(LH4)--(LH6) are then
checked against the full original records.

## 3. The punctured tails remove only the four retained labels

For an original hinge vector a, let

    w0=a1, w4=sum_(t>=2) a_t.

The unpunctured family starts are(3,2,2,2), with bases(3,5,5,5).
The four-label punctured starts are(5,3,3,2). In particular125 is
still present in the pure-five tail and135 is still present in the
deep mixed tail. The mixed contribution is1/72 for both weights.
Using231's six-label tail unchanged would remove labels that this
legacy head does not retain.

For fixed cut N=17 and any family(p,s), use the elementary support

    L(p,s)=1/[(p-1)*p^(s-1)],
    A(p,s,N)=max(N-s,0),
    B(p,s,N)=1/[(p-1)*p^(max(s,N)-1)].

For every e,H>=0,

    sum_(n>=s) min(e,H*p^-n) <= A*e+H*B.             (LH7)

This counts all n<N and sums every n>=N geometrically. It is an
infinite-tail bound, not a truncation. Form the weighted L,A,B
vectors with w0,w4 and the two start vectors. Call them ell,m,b.
With231's uniform envelopes cbar,Hbar, the full tail source is

    Ctail=sum_j(cbar_j*ell_j+Hbar_j*b_j)+delta*m5/240
       +(w0+w4)*(1/72+2669/88200+23delta/5880).       (LH8)

Its primitive vector is

    tau=(m3,kbar*m3,m5,m5,m3,kbar*m3,sum_j m_j),

and its explicit wrong-slot term is G*m3*(q5+kbar*q15).
The exact face tail subtracted from the original candidate is

    Tface=w0*(163/1800+2669/88200)
          +w4*(19/648+2669/88200).                   (LH9)

The certificate checks(LH9) against each original scan's own tail.
The finite cut is fixed across the source rectangle; its geometric
continuation remains present even at a zero actual defect, so the
certified support need not itself tend to zero at the face for a
fixed N. The exact underlying face tails do recover(LH9).

## 4. One shared residual maximum for each original test

For one legacy row, let S be its complete source increment,
ell its primitive vector after(LH5), and Raw(q) the signed support
increment from(LH3). Its complete row-plus-tail allowance is

    max_q [S+Ctail+Raw(q)+G*(b3+m3)*(q5+kbar*q15)
            +(rho-G*(q5+q15))*max_i(ell_i+tau_i)-Tface], (LH10)

where

    q in {(0,0),(rho/G,0),(0,rho/G)}.

The primitive sum has a single budget rho-G(q5+q15). For fixed q,
nonnegative prices bound it by the largest summed price. Raw(q) is
a support function of coefficients affine in q, hence convex in q;
the remaining terms are affine. A convex function on the q triangle
is bounded by its vertex maximum. This establishes(LH10) for the
whole triangle, rather than checking only three arbitrary samples.

Take the maximum of(LH10) over all16,391 legacy rows separately for
each of the sixteen original tail coefficient vectors. The original
certificate does not supply a full per-key objective partition;
the full-bank residual supremum safely covers each test's actual
rows. No original raw dual RHS is compared with another test's RHS.
The lossless price-table codec retains every repriced row for further
consumers. There are49,173 raw support optimizations and262,256
row-tail joins.

## 5. Transport the accepted minimum, then the complete head

For a fixed leaf,218 uses the minimum of its complete two-, four-,
six-projection and joint candidates. Denote their face values F_i
and uniform errors e_i. Then

    min_i(F_i+e_i) <= min_i F_i + max_i e_i.           (LH11)

The general233 API applies to the original positive hinge vectors,
full D_H deletion and the original pruning selected-prefix policy.
Its two/four/six errors are e2,e4,e6. A two-pruned class needs e2;
a four-pruned class stores min(F2,F4) and needs max(e2,e4);
a six-pruned class stores min(F2,F4,F6) and needs max(e2,e4,e6).
An expanded joint leaf needs max(e2,e4,e6,ejoint), even when its
joint raw face candidate lies above the final face ceiling M.
Thus its uniform upper is

    M+max(e2,e4,e6,ejoint).                          (LH12)

All sixteen scans have prefix_available=prefix_bounded=0. Their
original counts satisfy

    two=125000,
    four=50*(two-two_bounded),
    six=10*(four-four_bounded),
    joint-1=six-six_bounded,

    500*two_bounded+10*four_bounded+six_bounded
      +(joint-1)=62500000.                           (LH13)

The extra joint count is the seed, not an additional original leaf.
The certificate transports every class in(LH13). All48 pruning
classes stay below their own original face ceilings on(LH1).
The smallest remaining margin is the linear-1 class margin,
8.598965361905375...e-8. The complete head is the maximum of these
transported classes and(LH12).

In218 all sixteen newly scanned face bounds are below their previous
bounds. That face-only fact does not justify transporting a previous
minimum without its own proof. Here the scanned bound is transported
directly. AP13's previous-minus-scan difference is only
1.492063492063492...e-14, smaller than its transport allowance; no
claim that this tiny improvement persists off the face is made.
The separate integer-identity feedback and whole-load minima in218
are outside this sixteen-head result.

## Exact certificate

The [helper](../../frontier/retained-transport/legacy_retained_complete_head_transport.py)
and [certificate](../../certificates/source_norms/retained-transport/legacy_retained_complete_head_transport.json)
retain the original source hashes, coefficients, class counts,
branch-decision digests, all repriced rows, complete tail supports,
maximizing dual keys, candidate-specific errors and exact complete
head bounds. The complete-head allowance can exceed the joint-row
allowance: linear-1,7,17,23 are controlled by an old candidate error
in(LH12), not by the new joint residual alone.

```sh
python3 -I -O docs/reports/erdos7-odd-covering/frontier/retained-transport/legacy_retained_complete_head_transport.py --check
```
