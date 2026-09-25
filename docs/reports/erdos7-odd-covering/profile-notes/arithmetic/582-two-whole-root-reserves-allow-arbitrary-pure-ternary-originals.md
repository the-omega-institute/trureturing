# Two whole-root reserves allow arbitrary pure ternary originals

The two-root construction extends to arbitrary finite pure3 originals
by counting their actual deletions inside two WHOLE ternary roots.
Numerical uniqueness gives a shared pure-deletion budget across those
roots. It is unnecessary to assume the particular pure classes
1 mod3 and3 mod9 from Reports579–581.

Let P={3,5,7,11,13,17,19}, Q=P without3. Keep arbitrary finite
distinct nonunit P-smooth numerical moduli and globally fixed residues.
Choose one selected set of at most two Q phases at each nonunit
cofactor, containing its original projections through ternary exponent3.
Retain ONE actual Report569 PA law nu on this selected Q-survivor.

Choose two distinct first ternary roots that are not forbidden by an
actual pure modulus3 original. Suppose the residual mixed loads defined
below obey Y_1,Y_2<=u under this SAME nu, with0<=u<9. There is then
one actual supported probability with exactly Q marginal nu and

    R_P <= N(u) := B+[(27-u)/(27-2u)](1+B),
    B=432040125182653876501/86355045355449035400.        (WR1)

In particular, at u=2,

    N(2)=954033422610567164877/82756918465638658925
        =11.528140973575395... <566/49.               (WR2)

This is an ordinary quantitative corollary of the conditional-query
transport and root-capacity mechanism in
[Report572](572-compatible-fibres-lift-one-six-prime-query-law.md),
[Report579](579-two-root-convex-clipping-has-an-exact-certificate-boundary.md)
and [Report581](581-common-fibre-capacity-allocates-the-two-ternary-roots.md).
The additional arithmetic interface is the shared budget for arbitrary
pure3 phases and heights. Fixed post-restriction root weights suffice
for WR1; adaptive weights are not claimed necessary. There is no new
Lean verification, generic LP theorem, or unrestricted Erdős #7 result.

## 1. Keep all pure and mixed deletions in the same actual reserves

There is at most one original of modulus3, so two roots always remain
available. If no such original occurs, choose any fixed two roots;
the constructed law simply does not use the third. No original residue
or modulus is changed by this choice.

Let u_j be Haar conditioned on whole root j, j=1,2. Its density relative
to ternary Haar is3. Write P_j for the union inside that root of all
actual pure3 originals at depths e>=2, and let

    p_j=u_j(P_j).

These are exact union masses, not sums over overlapping classes.
Each pure modulus3^e occurs at most once, and its cylinder belongs to
at most one chosen root. Therefore

    p_1+p_2 <= sum_(e>=2)3^(1-e)=1/2.                (WR3)

The upper bound includes every possible later depth. Pure classes may
be nested or disjoint, at arbitrary finite heights and in either root.

For the COMPLETE actual original survivor mask chi set

    c_j(x)=integral chi(t,x) du_j(t).

At each e>=4, let L_(j,e)(x) count actual originals3^e d, d>1,
whose fixed Q phase matches x and whose ternary phase belongs to root j.
Define

    Y_j(x)=sum_(e>=4)54*3^(-e)L_(j,e)(x).             (WR4)

An original with selected Q phase vanishes on the source; all Q-bearing
originals through e=3 vanish there by construction. Originals in the
unused root have no effect on either chosen root. A depth-e cylinder
inside a whole root has u_j mass3^(1-e), so the actual union bound is

    1-c_j(x) <= p_j+Y_j(x)/18.                       (WR5)

There is no independence assumption between the loads, the two
survival functions, or the actual Q coordinates. The whole finite
original inventory, at every depth, remains in chi and WR4.

## 2. Fixed weights from the shared pure budget

Suppose Y_j<=u almost everywhere under nu, with0<=u<9. Put

    l_j=1-p_j-u/18,
    M=(18-u)/(27-2u), t=18/(27-2u).

By WR3,

    l_j >= (9-u)/18 >0,
    l_1+l_2 >= (27-2u)/18,
    t*l_j >= 1-M,  t*(l_1+l_2)>=1.                 (WR6)

Also1/2<=M<1. Thus the two-capacity criterion from Report581 gives

    min(M,t*l_1)+min(M,t*l_2)>=1.

Choose ONCE, using the actual pure unions,

    w_2=min(M,t*l_2), w_1=1-w_2.

These weights are positive, sum to one and satisfy w_j<=M and
w_j<=t*l_j. In particular they are fixed before sampling x or choosing
a query. Since c_j(x)>=l_j by WR5, define

    mu(dt,dx)=chi(t,x)
        [w_1u_1(dt)/c_1(x)+w_2u_2(dt)/c_2(x)]nu(dx). (WR7)

Each conditional root distribution integrates to its specified w_j.
Hence mu is supported on the actual survivor, has total mass one,
and preserves the prescribed Q marginal EXACTLY. No final mass-loss
normalization or query-dependent change of source is used.

The weights are fixed AFTER restricting and normalizing within each
root. This need not be the same as choosing a fixed whole-pure Haar
mixture before restricting a complete fibre, as in Report572 FS2.

## 3. Every query height and the outside-prime continuation

For any finite measure sigma, q_d(sigma) denotes its largest residue
cylinder at numerical modulus d, with q_1(sigma)=sigma(1). R_Q and R_P
sum these quantities over ALL nonunit smooth numerical labels, with
every height included.

For a Q-smooth d>=1, a depth1 ternary cylinder meets at most one of
the two supported roots. Therefore

    q_(3d)(mu) <= M q_d(nu).

For h>=2 the whole-root Haar cap is3^(1-h). Since w_j/c_j<=t,

    q_(3^h d)(mu) <= t*3^(1-h)q_d(nu).              (WR8)

The complete sum over h>=2 is t/2. Pure-Q queries have the unchanged
marginal nu. Thus

    R_P(mu) <= R_Q(nu)+(M+t/2)(1+R_Q(nu)),
    M+t/2=(27-u)/(27-2u),                           (WR9)

which proves WR1. The unit Q-cofactor occurs once at each positive
ternary depth and is excluded from the pure-Q sum. Finite query boxes
and monotone convergence justify every sum.

Use the same supplier density bound

    nu <= (9/alpha_min)H_Q,
    alpha_min=7575003978548161/73724315753088000.

On either disjoint root, the density of WR7 is at most3t times that
of nu. Hence

    mu <= 486 H_P/[(27-2u)alpha_min].               (WR10)

Independently condition23 and29 Haar on their complete actual pure-power
survivors and apply Report569 SD15–SD16 to THIS law. All additional
originals touching23 or29 retain arbitrary phases, distinct numerical
labels and arbitrary finite heights. Whenever N(u)<566/49,

    H(full survivor) >=
      alpha_min(27-2u)[566-49N(u)]/299376 >0.        (WR11)

At u=2 this is

    92778143633689872577/10483863107625824716800000
    =0.000008849614181456096... >1/113000.

This continuation has prime support P union{23,29}; primes outside
that set are not included. The strict threshold of the displayed
uniform estimate is

    u < 20750635627803642642318/10004205239367061830851
      =2.0741913156828113... .                      (WR12)

At equality WR1 equals566/49, so no positive continuation is claimed.
WR12 is a sufficient-certificate threshold, not a necessary limit for
actual survivor laws.

## 4. A less symmetric reserve interface

The pointwise capacities can also use the actual c_j directly, as in
Report581. For M=16/23 and t=18/23, sufficient conditions are

    18p_j+Y_j(x)<=11, j=1,2,
    18(p_1+p_2)+Y_1(x)+Y_2(x)<=13.                (WR13)

They imply c_j>=7/18 and c_1+c_2>=23/18. Then choose
a_2(x)=min(M,t*c_2(x)), a_1(x)=1-a_2(x) and replace the w_j in WR7
by these actual-Q-dependent masses. The same WR2 and WR10–11 follow.
The simpler condition Y_1,Y_2<=2 implies WR13 through the shared WR3
budget; it already admits the fixed construction in section2.

Thus the arbitrary-pure extension need not discard the allocation of
pure deletion between roots. Overlaps and unequal actual p_j can make
WR13 stronger than the symmetric sufficient condition.

## 5. Six simultaneous cofactors and unbounded finite pure depth

For any H>=3 use the pure originals

    1 mod3,
    2*3^(e-1) mod3^e, e=2,...,H.

For every q in Q include0 modq, and one original modulo3q with Q
phase1 and ternary phase2. Select{0,1} at each q. Add one original
modulo81q with Q phase2 and the following ternary phase:

| q | 5 | 7 | 11 | 13 | 17 | 19 |
|---|---:|---:|---:|---:|---:|---:|
|phase modulo81|3|12|21|2|5|8|
|chosen root|0|0|0|2|2|2|

CRT specifies each full original residue uniquely. There are H+18
distinct odd nonunit numerical moduli. The six mixed ternary cylinders
are pairwise disjoint and avoid EVERY pure original: the first three
are3 mod9, whereas the depth2 pure class is6 mod9 and all deeper pure
classes are0 mod9; the other three belong to root2. The pure-tail
cylinders are also pairwise disjoint.

The selected PA source is the product of uniform first Q roots
2,...,q-1 with Haar higher digits. Its normalized row densities lie
below the existing PA caps. At every x each chosen root has at most
three active residual classes at e=4 and none later, so Y_0,Y_2<=2.
On the positive cylinder with all six Q roots2, of source probability
1/378675, all six residual numerical cofactors are simultaneously active.

Consequently this source does not meet Report572's two-active-cofactor
premise. Each cofactor has three different projected phases through
e=4, so the earlier through-e4/e5 two-phase interfaces also fail.
No maximum H is imposed in the ordinary construction.

Write epsilon=1/(2*3^(H-1)). The exact pure losses and worst reserves are

    p_0=1/2-epsilon, p_2=0,
    min c_0=7/18+epsilon, min c_2=8/9.

Their minima occur at the same all2 cylinder. The best fixed-post-root
uniform-cap coefficient, including all query heights, is

    C_root(H)=25/[23+3^(3-H)] <=25/23.              (WR14)

For comparison, normalized Haar on the whole pure survivor has mass
w3=(1+3^(-H))/2 and pure query sum1/(2w3), because root2 contains a
full query cylinder at every depth. The six disjoint mixed originals
delete total ternary Haar mass2/27 on the all2 fibre. Its exact
whole-pure-Haar uniform-fibre coefficient from Report572 FS3 is

    C_whole(H)=1/[2(w3-2/27)]
              =27/[23+3^(3-H)].                   (WR15)

Using the SAME retained supplier bound B in both cases, WR14 passes
the gate and WR15 fails it for every H>=3. This compares those
sufficient interfaces, not all earlier actual-query profiles or laws.

The qualification about B matters: this explicit source has

    R_Q=product_(q in Q)[1+q/((q-1)(q-2))]-1
       =214267985/147806208=1.4496548412905634... .

Even using the limiting older coefficient27/23, its actual source cost
gives the successful bound

    R_Q+(27/23)(1+R_Q)
       =7352083433/1699771392=4.325336611501225... .

The examples also belong to older star-support noncoverage classes.
They certify realizable root-load patterns and the stated interface
comparison; their bare noncoverage is not new.

## 6. Reuse, remaining hypotheses and verification

Chapter03 HC1–HC7 and Report578 already supply the pure-only comb,
prefix-capacity and density/query extremal results. They are not
reproved here. Reports579 and581 literally fix two pure3 classes;
their capacity calculation is reused with two whole-root Haar sources
and the actual pure deletions WR3–WR5. Report572's conditional-profile
argument supplies query transport once WR7 is constructed. No new
generic max-flow, minimax or finite-LP result is claimed.

The new interface permits arbitrary finite pure3 phases and heights,
but still requires one two-phase selector through e=3 and the stated
same-source root-load bounds. Those bounds have not been deduced for
arbitrary actual original families. This leaves both shallow phase
multiplicity and unrestricted root loads open.

The [exact producer](../../frontier/cover-geometry/arbitrary_pure_root_reserve.py)
and [data](../../frontier/cover-geometry/arbitrary_pure_root_reserve.json)
contain227 named checks. They include all1120 choices of zero or one
pure original at each of depths1,2,3,4480 fixed-weight controls,
complete geometric tails, the exact continuation and threshold,
and H=3,4,8,40 original families with a private CRT witness checked
against every original for each class. The same data retain the
successful older bound using the control source's actual R_Q.

    python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/arbitrary_pure_root_reserve.py

The general proof, not the finite checks, supplies arbitrary phases,
real parameters and unbounded finite original heights. No new Lean
verification is included.
