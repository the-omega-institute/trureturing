# Query-prefix incidence strengthens the actual-source debits

The actual PA comparison can retain where its mass loss and cap slack
occur relative to a fixed query's earlier-only numerical labels. For
every fixed one-phase nonunit query layout L, the resulting nonnegative
quantity D(L) satisfies

    E_nu(L-2)_+ + D(L) <= K2=B-2.                         (PI1)

Here nu is ONE actual [Report569](569-complete-suffix-debits-close-the-six-prime-query-target.md)
source for an arbitrary finite family with at most two fixed phases
at each nonunit numerical modulus supported on Q={5,7,11,13,17,19},
and

    B=432040125182653876501/86355045355449035400.

There is no bound on original or query heights. Finite partial and
fixed countable layouts are allowed. The new term refines the
conditional comparison in [Report559](559-pure-union-savings-control-all-four-later-rows.md)
CS4; it is additional to the constant cap and suffix credits already
used in B. The old J terms are used once, with their old coefficients.
No uniform positive lower bound for D(L) is asserted.

PI1 also strengthens the actual clipped ternary construction of
[Report586](586-joint-clipping-retains-loss-query-correlation.md).
A 59-original arithmetic control below has positive clipping loss,
zero raw complete-query debit, and positive D(L). The latter is paid
by supplier slack, not by a supposed universal relation between
removed mass and removed query norm. This does not close the
high-query region left by [Report587](587-actual-tail-obstruction-and-source-query-repair.md).
No unrestricted Erdős #7 conclusion or new Lean verification is claimed.

## 1. The same actual prefixes and the additional statistic

Use the source, raw prefixes and caps from Report569. Write

    S=lambda_final(1),   nu=lambda_final/S,
    C11=5/3, C13=3/2, C17=2, C19=9/5,
    kappa_q=min(C_q,1/g_q),
    ell_q=1-min(1,C_q g_q),

where g_q is the actual allowed Haar fraction of row q. At g_q=0
use kappa_q=C_q and the zero row. Let sigma be the unnormalized
product of the actual pure5/7 restrictions, and lambda0 its
restriction after deleting the actual mixed5/7 union.

For a query layout L with globally fixed phases, n_q(h) counts its
nonunit numerical labels supported strictly before q, evaluated at
the actual earlier history h. Let n_* count its labels supported
on {5,7}. These counts refer to this fixed query, not to a new choice
of phases at each history.

Let N_r be the independent auxiliary comparison variables of
Report569, with

    Pr(N_r=1)=1-C_r/r,
    Pr(N_r=k)=C_r(r-1)/r^k,   k>=2.

Put Z_q=product_(r>q)N_r and Z_*=N11 N13 N17 N19. The empty
product Z19 is one. This independence belongs to the comparison;
the actual source coordinates need not be independent.

Define, for nonnegative integers n,

    zeta_q(n)=E(Z_q+n-3)_+,
    eta_q(n)=E sum_(e>=1) q^(-e)
               [(n+(e+1)Z_q-3)_+-(n+e Z_q-3)_+].

Use the same zeta definition with Z_* at the initial boundary. Write
delta_zeta_q(n)=zeta_q(n)-zeta_q(0), and similarly delta_eta_q.
The complete additional debit is

    S D(L) = integral delta_zeta_*(n_*) d(sigma-lambda0)
      + sum_q integral [ell_q delta_zeta_q(n_q)
                   +(C_q-kappa_q)delta_eta_q(n_q)]
                        d lambda_<q.                    (PI2)

Every integral uses its own actual unnormalized prefix in this one
source construction. S is the source normalization mass; it is not
the later clipped mass s.

If p1=Pr(Z_q=1) and p2=Pr(Z_q=2), splitting Z_q into 1, 2 and at
least 3 gives the exact formulas

| n | delta_zeta_q(n) | delta_eta_q(n) |
|---|---|---|
|0|0|0|
|1|1-p1-p2|p1/q^2+p2/q|
|at least2|n-2p1-p2|(q+1)p1/q^2+p2/q|

The zeta column also applies at the initial boundary with Z_*.
Both increments are nonnegative and nondecreasing in n. In particular,

    D19(L)=(1/S) integral [ell19(n19-2)_+
      +(9/5-kappa19)(1_(n19=1)+20*1_(n19>=2))/361]
                                    d lambda_<19         (PI3)

is one nonnegative summand of D(L).

## 2. The two sets of query labels are simultaneously present

First fix a finite partial layout and all its phases, then complete
it to finite exponent boxes. Include the unit once in the box count
N_H and put phi(u)=(u-3)_+. At the current backward-comparison row q,
condition on the actual earlier history and the already-replaced
later auxiliary uniforms. Let S_e count the active labels in current
exponent layer e before its q test, and A_e=S_0+...+S_e.

The later-only numerical labels, including the unit, contribute the
truncated suffix count Z_H in every current layer. The fixed partial
layout's earlier-only nonunit labels contribute n_q in layer zero.
These numerical subfamilies are disjoint. Consequently, on the SAME
history and auxiliary configuration,

    S_0>=Z_H+n_q,   S_e>=Z_H for e>=1.

The conditional cap envelope from Report559 CS4 is

    phi(A_0)+c sum_(e=1)^H q^(-e)
                              [phi(A_e)-phi(A_(e-1))].

Since A_(e-1)>=n_q+e Z_H and S_e>=Z_H, increasing convex increments
give

    phi(A_e)-phi(A_(e-1))
       >=phi(n_q+(e+1)Z_H)-phi(n_q+e Z_H).

Thus an actual normalized row below the full cap supplies the cap
credit (C_q-kappa_q)eta_(q,H)(n_q). A row needing mass completion
has the current-coordinate-independent payoff floor
phi(n_q+Z_H), so its added mass supplies ell_q zeta_(q,H)(n_q).
Positive cap slack and positive completion loss occur in the
separate cases used in Report569, so these are one valid conditional
inequality rather than two incompatible row constructions.

At the initial mixed5/7 deletion, the labels counted by n_* and the
later-only labels counted by Z_* are again disjoint: the latter
contains the unit, the former excludes it. Their sum supplies the
same payoff floor on sigma-lambda0.

Extract each additional integral against its ACTUAL prefix before
the next backward comparison. Only the remaining main term is
compared again; the extracted integrals are kept outside it. This
preserves their common-source meaning.

## 3. Complete heights and the old credits

During box exhaustion keep n_q from the prescribed finite partial
layout. It does not depend on completion phases. The finite-box
coefficient increments converge separately to their full values.
They obey

    0<=delta_zeta_(q,H)(n_q)<=n_q,
    0<=delta_eta_(q,H)(n_q)<=E Z_q/(q-1).

The corresponding pointwise dominator before auxiliary expectation
is Z_q/(q-1), whose mean is finite. The actual prefix measures are
finite, and fixed partial n_q is bounded. Dominated convergence and
the old limits of Phi_H and the constant coefficients therefore give

    integral(L-2)_+ d lambda_final + S D(L)
      <=Phi-zeta_*(0)m
          -sum_q [zeta_q(0)Delta_q+eta_q(0)K_q^cap].      (PI4)

Here m=(sigma-lambda0)(1), Delta_q=integral ell_q d lambda_<q,
and K_q^cap=integral(C_q-kappa_q)d lambda_<q. The unit shift is
exact: N_H>=1+L, so (L-2)_+<=(N_H-3)_+.

A difference eta_(q,H)(n)-eta_(q,H)(0) need not be monotone with box
height. No such assertion is used. After obtaining PI4 for every
finite partial layout, exhaust a fixed countable layout by finite
sublayouts. Now the FULL coefficient functions are fixed and
nondecreasing in n_q. Monotone convergence applies to these counts
and the hinge. Actual prefixes are bounded by finite multiples of
Haar; the full reciprocal-modulus sum on Q is finite, giving the
required integrability without a query-height cutoff.

Apply Report569 SD9 ONLY to its unchanged expression

    (K2-zeta_q(0))Delta_q-eta_q(0)K_q^cap.

It supplies the old J_q once. The same four-corner SD10 estimate
then bounds PI4's right side by K2 S. This proves PI1. Replacing the
old coefficient within SD9 by its history-dependent refinement
would require a different argument; PI4 does not do that.

## 4. High actual query norm forces conditional row criticality

Take a complete layout L1 maximizing every phasewise query under nu.
Such a fixed countable layout is integrable, since the complete
norm R_Q(nu) is finite. The identity

    L1=2+(L1-2)_+-(2-L1)_+

and PI1 give

    B-R_Q(nu)>=D(L1)+E(2-L1)_+.                          (PI5)

On {n19>=3}, PI3's integrand is at least
(36/361)|g19-5/9|. Below 5/9 its loss part is at least
(9/5)(5/9-g19). Above 5/9 its cap part is at least
(20/361)(9/5)(g19-5/9), because g19<=1. Hence

    B-R_Q(nu)>=(36/(361 S))
       integral_(n19(L1)>=3)|g19-5/9|d lambda_<19.       (PI6)

This confines a near-B source on the specified maximizing-query
prefix event; it does not show that event has uniformly positive
mass or rule out rows close to 5/9 there.

If the actual selected19 heights are at most H, g19 lies on the
grid 19^(-H)Z. The minimum loss-plus-cap penalty at n19=3 over that
grid is

    144/[361(5*19^H+4)].

Indeed the penalty decreases up to 5/9 and increases afterwards.
Since 19^H=1 mod9, comparing the two neighboring grid points gives
the displayed minimum at the upper one. It tends to zero with H;
finite original heights do not supply a uniform positive gap.

## 5. Actual damage and weighted queries retain different debits

For this section use exactly Report586's additional hypotheses:
distinct P-supported original numerical labels for
P=Q union{3}, pure3 originals exactly 1 mod3 and 3 mod9, and a fixed
two-phase selection at each nonunit Q cofactor containing every
original projection through ternary exponent3. Use its X,V,W,T,U,
beta=1-T/D, D=30-z, 2<=z<=6 and its SAME supported submeasure eta.

Let L_e combine the actual A and B original layouts at height e.
Numerical uniqueness makes this one legal partial layout. Put

    gamma_e=54*3^(-e),
    Dbar=sum_(e>=4)gamma_e D(L_e).

The weights sum to one and W<=sum gamma_e L_e. PI1 and
L_e<=2+(L_e-2)_+ imply

    E W<=B-Dbar,
    E(W-2)_+<=K2-Dbar.                                  (PI7)

These preserve every actual original layer, with missing layers
zero. They change neither phases nor source.

For 0<=f<=h, choose a complete phasewise maximizing layout L_f
under f nu. The exact identity

    f L_f=h(L_f-2)_++2f
                -(h-f)(L_f-2)_+-f(2-L_f)_+

and PI1 give

    R_Q(f nu)<=h[K2-D(L_f)]+2E f.                       (PI8)

Write D_beta=D(L_beta), D1=D(L1), DU=D(L_U), and tau=E T.
The choices f=beta,1,U, together with U+T<=W and PI7, yield

    R_Q(beta nu)<=B-2tau/D-D_beta,
    R_Q(nu)<=B-D1,
    R_Q(U nu)<=zK2-zDU+2E U,
    E U<=B-tau-Dbar.

Substitution in the unchanged Report586 CJ6, on the SAME eta,
therefore proves

    R_P(eta)<=N2(z)-5tau/D-A_z,
    N2(z)=1+2B+(zK2-3)/D,
    A_z=D_beta+(1-3/D)D1+(z/D)DU+(3/D)Dbar.             (PI9)

All four coefficients are nonnegative. The extra scalar 2tau/D
already follows from the old weighted hinge applied to beta; the
additional retained arithmetic information is A_z.

At z=16/3,

    A_z=D_beta+(65/74)D1+(8/37)DU+(9/74)Dbar.

Writing G=566/49 and s=eta(1)=1-tau/D, a sufficient condition for
R_P(eta/s)<G is

    A_z>((G-5)/D)tau-(G-N2)
       =(963/3626)tau-(G-N2),
    G-N2=0.0171950274407465... .                         (PI10)

This ensures s>0: eta is nonnegative, so s=0 would force eta=0
and contradict the strictly positive lower bound on Gs-R_P(eta).
Report586's continuation through23 and29 then gives

    H(full survivor)
      >=(49 D alpha_min/299376)
          [G-N2-((G-5)/D)tau+A_z]>0.                    (PI11)

Only originals supported on P union{23,29} are included. PI10 has
not been proved for every actual family in even this restricted
slice. The maximizing layouts and actual damage layouts in A_z
are distinct fixed layouts, all measured on the same actual source.

## 6. An actual family separates the new term from raw query loss

Keep pure originals 1 mod3 and 3 mod9. For every q in Q take the
original 0 modq and the original modulo3q with ternary phase2 and
Q phase1. Select phases0 and1 at each prime cofactor and no others.
The actual PA source is the product law conditioned at each prime
on roots2,...,q-1, with Haar higher digits. Its raw mass is S=3/7;
all later rows are normalized below their existing caps.

Let M=product Q=1616615. Enumerate increasingly the45 residues t_j
modulo81 avoiding 1 mod3 and 3 mod9, j=1,...,45. Add the original
at numerical modulus81 M 5^(j-1) with ternary phase t_j and Q phase2.
CRT fixes its single residue. These are59 distinct odd nonunit
original numerical labels with the required shallow selection.

For E_j=[2]_(M 5^(j-1)) and N=sum_(j=1)^45 1_(E_j),

    nu(E_j)=1/(378675*5^(j-1)),
    W=(2/3)N,
    tau=E(W-16/3)_+=(1-5^(-37))/(6*378675*5^7)>0.

The ternary cylinders are disjoint. The last nested event has
positive mass and removes all45, so genuine zero-reserve fibres
occur. The clipped construction remains defined there.

For EVERY nonunit Q-smooth query d, phase3 mod d is maximizing
under nu. It avoids the whole damage cylinder E1: choose any prime
q dividing d, and its root3 differs from root2 there. Thus beta=1
on this maximizing cylinder and

    q_d(beta nu)=q_d(nu),
    R_Q(beta nu)=R_Q(nu)=214267985/147806208.             (PI12)

The unit query would lose mass and is correctly excluded from R_Q.
All query heights are covered by this argument, not by a finite
inventory test. The selected current-root unions are disjoint, so
their selected-overlap credit is also zero.

Nevertheless, for this fixed phase3 layout, before row19

    1+n19=K=product_(p in{5,7,11,13,17})(1+v_p(x_p-3)),
    Pr(K=1)=1792/4455,
    Pr(K=2)=6443456/18050175.

Since ell19=0 and C19-kappa19=58/85, PI3 gives

    D19(L1)=D19(L_beta)
       =16245701864/1661608859625
       =0.00977709150375282...>0.                        (PI13)

The old constant cap debit remains separately positive:

    (C19-kappa19)eta19(0)=29/276165.

It is NOT set to zero in this control. On the same source, choosing
phase0 at every query gives n19=0 and D19=0, while leaving the old
scalar cap and J data unchanged. Thus the new statistic retains
query-prefix incidence that those old scalar data do not express.
PI12's zero raw debit was already allowed by Report571; the
new role of this control is the simultaneous positive PI13.

This source has R_Q about1.44965, far below the remaining high-query
region. It is not a high-query obstruction, a new bare noncoverage
claim, or a uniform estimate for arbitrary original families.

## 7. Verification and the remaining joint problem

The [exact producer](../../frontier/cover-geometry/prefix_incidence_actual.py)
and [data](../../frontier/cover-geometry/prefix_incidence_actual.json)
retain the coefficient formulas, rational thresholds and actual
59-original control. The source coefficient data are pinned to
Report559's existing exact producer output. Finite checks test the
displayed coefficients and arithmetic control; Sections2--3 carry
the general comparison and complete-height passage.

All33 named checks pass, including216 coefficient controls with exact
geometric tails, all59 CRT originals, all46 actual nested incidence
atoms,243 low-count prefix categories and728 query-avoidance controls.
The complete-query avoidance proof in Section6 applies at every
height. These finite counts are not a replacement for that proof.

Run using Python3 standard library only:

    python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/prefix_incidence_actual.py

The remaining task is to force a sufficient joint debit, or another
compatible improvement, when actual query norm and ternary damage
are both adverse. PI6 constrains critical rows on fixed maximizing
prefix events. It does not exclude simultaneous near-criticality
for maximizing and original-damage layouts, remove the shallow
phase restriction, or extend the stated nine-prime support to
arbitrary primes.
