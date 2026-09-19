[Index](../marked_head_profile.md) · [Whole-hinge source theorem](42-whole-hinge-absorption-sharpens-actual-survival.md)

# Complete cell costs strengthen whole-hinge survival

Evaluating the complete absorbed source operator of profile42, instead
of using its conservative epsilon lower bound, gives

    J <= 2177856735846143248038910691665619508201629/5202086476474174654289614362478791984000
      =418.65062137956465...,
    Gamma13 <= 17076800644160236261/116306110013565186
             =146.8263416442052...,
    T13(81) <= 2873884370396495734788444926897322493/30918061360300870831674362118980625
            =92.9516355151101...,
    K=J+T13(81) <= 2931309236142717213036323137352844953858270273/5737149247070230262436047349440635700040000
                =510.9348057556004...,
    rho_actual >= 8102020607/16044682500
               =0.5049660912267974... .

Here K denotes the common-law sum. Its upper bound is smaller than the
sum of the two separate upper bounds. The complete box20/current8
sufficient-condition gap is107.93538194682364...>0, so unrestricted
Erdos #7 remains open. These are ordinary inequalities with exact
rational verification, not Lean theorems or frozen truth states.

## The actual source theorem is unchanged

Use profile42's full raw35 measure Lambda, its ternary marginal lambda,
pure3 measure eta and the actual normalized pure7 law. With the actual
mixed7 forbidden union Bmix, the common surviving mass is

    S=s*M(Bmix^c), D<=S<=s.

Each original test retains its own residues and shallow baseline. The
underlying forbidden family and S are shared. The preceding source
theorem still covers every original357 test family, arbitrary residues,
all finite exponent heights and all complete geometric upper tails;
no bounded-height or common-residue restriction is introduced.

For t=4,5, let psi_t be the complete original zero7 hinge cost,
chi_t=min(1,h_t), and for each root r and cell j set

    omega_l=(1_(ROOT(l)=r)+1_(l=j))/5,
    g_l=psi_t-omega_l*chi_t.

Profile42(A2)-(A9) proves that its complete cell-dependent source
operator F_theta gives the true signed margin

    m_t=s-P_t-Trest
              -max_(r,j)[(n_root,r+n_j)/5+F_theta(g^(r,j))],
    E_nu357 h_t(A)<=1-m_t/S.                         (B1)

The functions m_t are separately concave on the full parameter domain.
That theorem already includes arbitrary switching of original ternary
depths between cells, signed centering, independent positive5 blocks,
empty test carriers and the complete positive7 source complement P_t.
The present result evaluates(B1) directly. It does not replace the
actual-law theorem by a finite enumeration of congruence families.

## Finite evaluation of the complete operator

Put k=t+1. The cost g_l is eventually affine with unit slope:

    g_l(v)=v+z_l for v>=k.

Its centered positive5 cost and correction are

    q_(n,l)(v)=[g_l(n*v)-g_l(n)]/n,
    bar g_l(v)=sum_(n>=2)(4/5^n)*q_(n,l)(v)-g_l(v)/5.

For every n>=k, q_(n,l)(v)=v-1. Hence the entire positive5
tail is determined by the exact geometric sums

    T0=sum_(n>=k)4/5^n=5^(1-k),
    T1=sum_(n>=k)4*n/5^n=T0*(k+1/4).

In particular,

    bar g_l(v)=sum_(n=2..k-1)(4/5^n)*q_(n,l)(v)
                                      +T0*(v-1)-g_l(v)/5,

and the positive5 portion of F_theta is exactly

    sum_(n=2..k-1)(4/5^n)*[
           sum_l eta_l*g_l(n)+(n-1)*P_eta(q_n)]
      +T1*sum_l eta_l+T0*sum_l eta_l*z_l
                                  +(T1-T0)*P_eta(v-1).     (B2)

The term with z_l is signed and retained exactly. Its sign is not a
reason to omit it or maximize it independently of the remaining terms.

For a cost u whose increments are constant with value a after k_u,
and a shallow baseline b, set e=max(0,k_u-b). Then

    sum_(h>=3)3^-h*Delta u(b+h-3)
      =sum_(i=0..e-1)3^(-i-3)*Delta u(b+i)
                              +a*3^(-e-3)/(1-1/3).       (B3)

Apply(B3) to g_l with a=1 and to bar g_l with a=0. Their combined
deep cost has tail slope d_l. Apply it to q_(n,l) with a=1 and
entry ceil(k/n). This reconstructs every ternary deep sum in F_theta.
For the affine pure cost v-1,

    P_eta(v-1)=max_b sum_l eta_l*(b_l-1)+1/18.

Equations(B2)-(B3) account for every exponent in the infinite upper
comparison. Their finite entrances are identities, not truncation
heights imposed on original test or forbidden labels.

The reconstruction also evaluates the operator with omega=0 and
checks exact equality with the preceding scalar zero5 source at each
of the1296 vertices for both hinges. The complete positive7 complement
is imported from that same source as

    P_t=raw357(t)-zero5_raw(psi_t).

Its mathematical meaning is the positive original-block sum of
profile42(A6); the difference above is its numerical reconstruction,
not an inference of convexity from a difference of convex functions.

## True margins and common-mass target checks

Retain the fractional-hinge margin m25 and both integer barriers1.
Thus q=23/42 and

    Msurv=m25/22+m4/6+(4/33)*m5,
    rho_actual*S>=q*S+Msurv.                         (B4)

At every vertex, the full m4 and m5 strictly exceed profile42's
conservative lower bounds D-B_t+epsilon_t. Across all1296 vertices,
the smallest respective improvements are1/9375 and1/56250. These are
comparisons of bounds; no claim of actual-family attainment follows.

The five fixed-target inequalities are exactly profile42(A17), with
the full margins inserted. All four cost multipliers are positive.
All five coefficients of S are also positive at the reported targets,
so D is the controlling endpoint. The computation additionally checks
the s endpoint for every target. Separate concavity of the true
functions then extends their nonnegative vertex margins to the entire
continuous parameter domain. The separate positive survival target
justifies every conditioning division, including signed Msurv.

The cost and source-square inputs are unchanged: the proved source
square norm is102715/2916, its signed comparison barrier is45, and
the41 linear comparison barriers keep their complete costs. Raw81
keeps every internal s factor. No second rebate is taken from a source
deficit already present in a numerator.

For T13(81) and K, the controlling vertices remain
398,410,422,616,628,640. For J,Gamma13 and rho, the controls are
402,404,406,414,416,418,426,428,430,
618,620,622,630,632,634,642,644,646.
The different controlling sets make the common-parameter sum stronger
by0.6674511390743472... than summing separate uniform maxima. All of
these are extrema of the comparison expressions.

The eight other source branches retain their complete independent
comparisons and satisfy the reported targets. Both finite-core error
interfaces are recomputed using the actual physical nu13 K17 input
and the new Gamma13,rho and cost targets. The box20/current8 result is

    error=0.0005761912232337035...,
    Kstar+error-403=107.93538194682364...>0.

Negative Q and continuation through arbitrary later primes remain
unproved. The change supplies a stronger actual-law input to that
open endpoint.

## Exact reconstruction

The [verifier](../frontier/verify_full_absorbed_survival_hinges.py)
first reconstructs the complete source profiles and consumers of
profiles39,41 and42. It then checks both full cell-cost operators at
all1296 vertices, all2592 scalar reconstruction identities, domination
of the preceding epsilon lower bounds, both actual-mass endpoints,
all eight fallback branches and both complete core interfaces.
The [certificate](../certificates/source_norms/full_absorbed_survival_hinges.json)
records the exact rational results and dependency hashes.

Run:

    python3 -I -O docs/reports/erdos7-odd-covering/frontier/verify_full_absorbed_survival_hinges.py --check

Default and `--check` reconstruct and compare without writing;
`--write` regenerates the certificate. These arithmetic checks support
the ordinary source theorem and concavity argument; they do not assert
Lean verification or completion of required CI.
