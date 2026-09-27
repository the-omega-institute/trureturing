# Clipped joint reserves retain the loss and weighted query cost together

Fix `P={3,5,7,11,13,17,19}` and `Q=P without3`. The initial actual
family is finite and P-supported, with distinct odd nonunit numerical
moduli and one globally fixed original residue per modulus. Its pure3
originals are exactly `1 mod3` and `3 mod9`. At each nonunit Q cofactor,
choose at most two fixed phases containing every original projection
at ternary exponents0 through3. Let nu be ONE resulting actual PA law.
All alternate query layouts below use this same nu. Put G=566/49.

Let `u_A` be ternary Haar conditioned on `[0]_9 union[6]_9`, and `u_B`
ternary Haar conditioned on `[2]_3`. For the COMPLETE original survivor
mask chi, put

    c_j(x)=integral chi(t,x)du_j(t),
    X=12(1-c_A), V=18(1-c_B), W=X+V.

The common source supplies

    R_Q(nu)<=B=432040125182653876501/86355045355449035400,
    nu<=9H_Q/alpha_min,
    alpha_min=7575003978548161/73724315753088000.

For every finite partial nonunit one-phase query layout L it also gives

    E(L-2)_+<=K2=B-2,
    E(L-3)_+<=K3=12019840537595758779003/5715264751774801992890.

The second hinge is the consequence of [Report569](569-complete-suffix-debits-close-the-six-prime-query-target.md) SD10 verified in
[Report585](585-joint-damaged-reserves-retain-every-original-height.md): the complete count N contains its unit once, N>=1+L, and
the same-source bound on `E(N-3)_+` applies before the final addition
of two. It does not follow from `R_Q(nu)<=B` alone. The third hinge
uses [Report574](574-four-level-query-hinge-removes-pointwise-overlap.md)'s existing all-layout envelope, not merely actual layers.

The new conditional conclusion is that

    tau=E(W-16/3)_+
      <21218460281840396929028797/380636632468201812726474000
       =0.05574466163241126...                             (CJ1)

suffices for a supported probability with `R_P<566/49`. Individual
reserves may vanish on positive-source-mass events. Every additional
original supported on `P union{23,29}` and touching23 or29 may have
arbitrary fixed residue and arbitrary finite height. The resulting
Haar survivor mass is at least

    (185 alpha_min/149688)(tau_star-tau)>0.                 (CJ2)

This tail condition and Report585's pointwise capacity domain are
different sufficient domains. Neither is asserted to contain the
other. In particular the present pointwise corollary includes the old
`c_B=1,c_A>=5/9` subclass, but not all of Report585's conditions.
No assertion about unrestricted Erdős #7 is made.

## 1. Numerical uniqueness gives one joint layout at each height

Let `L_(A,e)` and `L_(B,e)` count the actual residual original
projections at ternary height e whose ternary cylinders lie in A and B.
All nonzero residual heights satisfy e>=4 on the selected source.
Numerical distinctness permits at most one original `3^e d` for every
pair (e,d). Consequently

    L_e=L_(A,e)+L_(B,e)

is ONE legal partial one-phase Q query layout. It is not charged as
two separate layouts. Define

    Y=sum_(e>=4)54*3^(-e)L_e.

The actual branch union bounds give W<=Y, and the coefficients sum
exactly to one. Missing original layers are zero layouts. Thus

    E W<=B,   E(W-2)_+<=K2.                                (CJ3)

The second inequality follows from convexity applied to this one
geometric mixture and the uniform second-hinge contract. All original
phases and all actual layers belong to the same source. There is no
upper cutoff on original heights.

More precisely, for every measurable source event E,

    integral_E W dnu<=integral_E Y dnu<=R_Q(nu restricted E).

The last inequality holds for each fixed-height original layout before
averaging. It links damage to actual restricted query cost.

## 2. A clipped kernel with well-defined zero-reserve fibres

Choose `2<=z<=6`, and put `D=30-z`, `r=12/D`. Define actual conditional
branch masses, fixed before any query is chosen, by

    a_A=r c_A,
    a_B=min(1-r c_A,(3r/2)c_B).

Also set

    T=(W-z)_+,   U=min(X,(z-V)_+),   tau_z=E T.

Since `0<=X<=12,0<=V<=18`, elementary rearrangement gives

    a_A+a_B=b=1-T/D,
    (a_B-(1-r))_+=U/D.                                    (CJ4)

Indeed the two entries in the minimum for `D a_B` are
`18-z+X` and `18-V`. Adding `D a_A=12-X` proves the first identity;
subtracting `D(1-r)=18-z` and taking the positive part proves the
second. In particular `0<=b<=1`.

Define one supported subprobability

    eta_z=chi[r u_A+(a_B/c_B)u_B]nu,                        (CJ5)

using zero for the B coefficient wherever c_B=0. On such fibres a_B
is zero. If c_A=0, chi u_A has zero mass, so the displayed A term
also vanishes without division. Thus eta_z has Q marginal `b nu`
and total mass

    s=1-tau_z/D.

When s>0, normalize once at the end: `mu_z=eta_z/s`. If both reserves
vanish, W=30, T=D and b=0: that entire fibre is discarded.

## 3. Keep the actual weighted numerator until after clipping

For any finite measure sigma write q_d(sigma) for its largest residue
mass modulo d, taking `q_1(sigma)=sigma(1)`. The complete nonunit norm
R_Q excludes d=1.

Since r<=1/2, `a_A<=r<=1-r`; CJ4 also gives
`a_B<=1-r+U/D`. At depth1 this bounds the maximum of the two root
queries by

    (1-r)q_d(nu)+(1/D)q_d(U nu).

At every ternary depth e>=2, the A coefficient in CJ5 is r and
the B coefficient is at most3r/2. On zero-reserve fibres the supported
terms vanish; no identity for a ratio0/0 is used. The two conditional Haar cylinder
upper bounds therefore agree at9r/2. One cylinder lies in at most
one root, so these coefficients are not added. Summing the complete
tail `sum_(e>=2)3^(-e)=1/6` gives coefficient `3r/4=9/D`.

Including the Q-unit once at each positive ternary depth and retaining
the actual Q marginal gives

    R_P(eta_z)<=R_Q(b nu)+(1-3/D)(1+R_Q(nu))
                         +(E U+R_Q(U nu))/D.               (CJ6)

Every quantity in CJ6 uses one actual law. All sums can first be taken
over finite numerical query inventories and then exhausted. No query
height cutoff is used.

## 4. The discarded loss also lowers the retained query numerator

Pointwise `U<=min(W,z)`. For z>=2 this implies both

    U+T<=W,
    (U-2)_++T<=(W-2)_+.

Together with CJ3 these give coupled bounds

    E U<=B-tau_z,
    E(U-2)_+<=K2-tau_z.                                   (CJ7)

First apply [Report584](584-weighted-query-costs-retain-the-actual-damaged-branch.md)'s
second-hinge weighted estimate with weight U<=z:

    R_Q(U nu)<=z K2+2E U,
    E U+R_Q(U nu)<=z K2+3B-3tau_z.                         (CJ8)

Alternatively split `U=min(U,2)+(U-2)_+`. The first part costs at
most2B in complete query norm. The second is bounded by z-2, so the
third-hinge weighted estimate and CJ7 give

    R_Q(U nu)<=2B+(z-2)K3+3E(U-2)_+,
    E U+R_Q(U nu)<=3B+3K2+(z-2)K3-4tau_z.                 (CJ9)

Define

    N2(z)=1+2B+[z(B-2)-3]/(30-z),
    Nsplit(z)=1+2B+[3B-9+(z-2)K3]/(30-z).

Using `R_Q(b nu)<=B` in CJ6 now yields

    R_P(mu_z)<=min(N2(z)-3tau_z/D,Nsplit(z)-4tau_z/D)
                       /(1-tau_z/D),   if tau_z<D.         (CJ10)

The subtractions in the numerator are essential: clipped loss and
remaining weight have been bounded jointly on the same source.

## 5. Exact margins, density and the nine-prime continuation

At z=16/3, `D=74/3,r=18/37`, and

    N2=(164B+33)/74
      =18426074256671263478591/1597568339075807154900
      =11.533825380722519...,
    Nsplit=(157B+47+10K3)/74
      =11.533955715826814... .

Under the pointwise condition `W<=16/3`, there is no clipping. The
first bound gives `R_P(mu)<=N2<566/49`, with Q marginal exactly nu.
It includes `c_B=1,c_A>=5/9` and also simultaneous damage with the
same total weighted reserve. It gives Haar survivor mass at least

    1346041340014939222441/188709535937264844902400000
      =0.000007132873987154635... .                        (CJ11)

The split bound in CJ10 gives the positive tail allowance

    tau_z < tau_star
      =D(G-Nsplit)/(G-4)
      =(39581-7693B-490K3)/1110,

which is the exact fraction in CJ1. It is a sufficient condition;
larger tails are not claimed to imply coverage or rule out a sharper
estimate of the actual weighted terms in CJ6.

The common raw ternary density cap is9r/2=54/D. Thus

    eta_z<=486H_P/(D alpha_min).

Condition23 and29 Haar on their complete actual pure-power survivors.
For all additional originals supported on `P union{23,29}`, the
established same-law count leaves raw mass at least
`(566s-49R_P(eta_z))/567`. Its density factors are22/21 and28/27.
Consequently

    H(full survivor)>=D alpha_min[566s-49R_P(eta_z)]/299376.

At z=16/3, use `R_P(eta_z)<=Nsplit-4tau_z/D` to obtain CJ2.
No new prime outside the stated nine-prime set is included.

## 6. An actual family with zero surviving fibres

The tail criterion permits genuine arithmetic fibres excluded by
Report585, not only abstract damage distributions. Enumerate in
increasing order the45 residues t_j modulo81 satisfying

    t_j mod3 !=1,  t_j mod9 !=3,    j=1,...,45.

They comprise all18 A cylinders and all27 B cylinders at depth4.
Keep the two pure3 originals. For each j add one original with
modulus `81*5^j`, ternary phase t_j and Q phase0 modulo5^j, fixing its
single integer residue by CRT. This is a47-original family of
distinct odd nonunit numerical moduli. There are no Q-only or mixed
originals at ternary exponents0 through3, so the selected Q family can
be empty and its actual PA source nu is Q-Haar.

Let `E_j=[0]_(5^j)` and `N=sum_(j=1)^45 1_(E_j)`. The E_j are nested.
Distinct t_j give disjoint ternary cylinders, and each incident
original contributes exactly2/3 to W, in either branch. Therefore

    W=(2/3)N,   nu(N>=j)=5^(-j).

On E_45, of positive source mass `5^(-45)`, all45 surviving pure3
cylinders are removed: `c_A=c_B=0`. The pointwise joint-reserve
hypothesis of Report585 fails on this actual event.

Nevertheless its exact clipping loss is

    E(W-16/3)_+=(2/3)sum_(j=9)^45 5^(-j)
      =(1-5^(-37))/(6*5^8)
      =36379788070917129516601562/85265128291212022304534912109375
      <0.000000427<tau_star.                              (CJ12)

Thus CJ1 applies while genuinely discarding zero-survivor fibres.
This construction witnesses a broader allowed fibre behavior; its
bare noncoverage is already elementary and is not claimed as a newly
resolved instance. The arbitrary-family and all-height theorem is
supplied by the proof, not by this finite control.

## 7. Remaining arithmetic obligation and evidence scope

The argument has not shown that every actual family in the fixed-pure3,
shallow two-phase slice satisfies CJ1, or that its actual weighted
bound in CJ6 falls below `s*(566/49)`. Let K7 be the existing all-layout seventh-hinge bound
from the same source envelope. From W<=Y and the third/seventh hinges,
generic convex interpolation
at16/3 supplies only

    E(W-16/3)_+ <=(5K3+7K7)/12
                  =1.3439186282202944...,

which exceeds tau_star. This is an insufficient available upper bound,
not an actual-family obstruction or a realizability assertion.
Actual restricted query values, the reduced Q cost `R_Q(b nu)` and
verified same-source overlap credits can improve CJ6.

Removing the shallow two-phase condition, replacing the fixed pure3
geometry, and treating arbitrary prime supports remain outside the
conclusion. The [exact producer](../../frontier/cover-geometry/joint_clipped_query_reserve.py)
and [data](../../frontier/cover-geometry/joint_clipped_query_reserve.json)
control the displayed constants, clipped identities and actual47-original example.
All41 named checks pass, including397 rational clipping controls and
all46 actual valuation atoms of that example. Its complete query norm
is computed from the finite constant cells modulo81 and5^45 and the
exact geometric tails in both coordinates, including their common tail.
The proofs above
carry the continuous parameters and complete height/layout quantifiers.
These are ordinary mathematical deductions, not new Lean verification.

Run with Python3 standard library only:

    python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/joint_clipped_query_reserve.py
