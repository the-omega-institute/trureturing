[Index](../marked_head_profile.md) · [Common actual mass](39-source-deficits-through-one-actual-survivor-mass.md) · [Fractional survival hinge](41-a-source-hinge-deficit-improves-actual-ap45-survival.md)

# Whole-hinge absorption sharpens actual survival

On the complete actual AP11/T4,AP13/T5 law, absorbing the two shallow
mixed7 deletion terms into each original zero7 source cost gives

    J <= 257936427602342694912520914686140996612914319/603345023275531565453506866246392702291520
      =427.5106575040895...,
    Gamma13 <= 33484394308169583482819/227116437036386885559
             =147.43272105314406...,
    T13(81) <= 2873884370396495734788444926897322493/30192366753735365545124129154058275
            =95.18579294685277...,
    J+T13(81) <= 2928401376302642555839895965273453977288131513/5602489501844221679211135186573646521278400
              =522.6964504509423...,
    rho_actual >= 1171940629483/2362133812500
               =0.4961364268532522... .

The complete box20/current8 error is0.000586452245679290..., so the
remaining sufficient-criterion gap is119.69703690318796.... This does
not prove negative Q or unrestricted Erdős #7. The result consists of
ordinary mathematics and exact rational arithmetic, not a Lean theorem.
All original finite exponent heights and independent residues are
included; the exponent tails below are complete.

## Actual measures, quantifiers and retained deletion carriers

Fix any finite original forbidden family in the effective9 branch, with
distinct odd moduli, and any of its complete original357 test families.
Each test may choose its own original residues and ternary layouts.
Use the actual pure3 measure eta, the actual raw35 survivor measure
Lambda, and its3-coordinate marginal lambda from profile31. The five surviving
mod9 cells have roots ROOT=(0,0,1,1,1). Write

    eta_l=eta(cell l), n_l=Lambda(cell l)=lambda(cell l), s=sum_l n_l,
    0<=d lambda/d eta<=d_l on cell l, d_l>=1/4,
    R(v)=max(v_0+v_1,v_2+v_3+v_4), n_*=max_l n_l.

The density inequality is pointwise. It follows from the original
mixed35 forbidden unions as in profile31(ZC2); a marginal mass bound
alone would not imply it. The continuous parameter domain is

    eta_l=(1-deficit_l)/9,
    d_l=z-alpha_(ROOT(l))-beta_l,
    n_l=eta_l*d_l-late_l,

where the nonnegative deficit,alpha,beta,late vectors have total caps
1/2,1/4,1/4,1/72 respectively, and3/4<=z<=1. These are five separate
convex parameter blocks, with1296 product vertices. The formula below
is defined throughout this domain, including parameters not realized
by an actual forbidden family.

Let M be the product of the normalized actual35 survivor law Lambda/s and the
normalized actual pure7 survivor law. Let Bmix be its actual mixed7
forbidden union, V=Bmix^c, and

    S=s*M(V)>=D>0, nu357=M(.|V).

This is one actual source mass shared by all tests. Put w_l=9*eta_l and

    Trest=(max(d)/18+(sum(w)+R(w)+max(w))/36+1/72)/5.

The complete mixed7 cap identity is

    s-D=(R(n)+n_*)/5+Trest.                         (A1)

Only the cofactors3 and9 are separated from Trest. Every deeper pure3
and positive5 cofactor remains in its complete unweighted cap.

## A cell-dependent source operator with complete depth control

Fix costs f_l on v>=1 which are nonnegative, increasing and convex,
with f_l(1)=0. Assume the displayed complete series are finite. The
costs used below are eventually affine, so this condition holds.
For n>=2 define

    p5_n=4/5^n,
    q_(n,l)(v)=[f_l(nv)-f_l(n)]/n,
    bar f_l(v)=sum_(n>=2)p5_n*q_(n,l)(v)-f_l(v)/5.

The allowed shallow baselines are the ten vectors

    B={b: b_l=1+1_(ROOT(l)=r0)+1_(l=j0), r0=0,1; j0=0,...,4}.

For a vector u of increasing convex costs, put

    P_eta(u)=max_(b in B)[sum_l eta_l*u_l(b_l)
                 +max_l sum_(a>=3)3^-a*Delta u_l(b_l+a-3)].

Define the complete raw35 source operator

    F_theta(f)=max_(b in B)[
        sum_l(n_l*f_l(b_l)+eta_l*bar f_l(b_l))
        +max_l sum_(a>=3)3^-a*Delta(d_l*f_l+bar f_l)(b_l+a-3)]
      +sum_(n>=2)p5_n*[sum_l eta_l*f_l(n)
                                     +(n-1)*P_eta(q_n)].       (A2)

For every complete original35 test Z this bounds
integral_Lambda f_l(Z). Write its original pure3 blocks as A0,A1,...;
these blocks depend only on the3-coordinate and can be integrated
against lambda or eta. The cost's cell label is the old3 mod9 cell;
it does not depend on the5-coordinate or on the positive5 block.
The same f_l is therefore fixed throughout the pointwise positive5
comparison at that old3 point.

For completeness, the centered pointwise Jensen inequality is

    f_l(A0+...+A_(n-1))-f_l(A0)
      <=q_(n,l)(A0)-f_l(A0)+f_l(n)
                                      +sum_(e=1)^(n-1)q_(n,l)(A_e).

Applying the original positive5 comparison of profile31 before summing
the entire p5 mixture gives

    integral_lambda f_l(A0)+integral_eta bar f_l(A0)
      +sum_(n>=2)p5_n*[sum_l eta_l*f_l(n)
                       +sum_(e=1)^(n-1)integral_eta q_(n,l)(A_e)].

The expression retains one original A0 in both actual measures. Each
positive block A_e is then bounded by P_eta(q_n), uniformly in its own
independent residues. The centered costs q_(n,l) are nonnegative,
increasing and convex. No common residue or actual overlap between
different original blocks is assumed.

Here is the precise justification for the deep maximum in(A2). Let
r_l(k)>=0 be nondecreasing in k and let0<q<1. If

    W_l(k)=sum_(j>=0)q^j*r_l(k+j)<infinity,
    W(k-vector)=max_l W_l(k_l),

then for any choice of cell l, advancing only its own counter gives

    r_l(k_l)+q*W(k-vector+e_l)<=W(k-vector).          (A3)

Indeed W_l(k)=r_l(k)+q*W_l(k+1), and monotonicity implies
r_l(k)<=(1-q)*W_l(k). If the chosen cell maximizes the next potential,
the left side of(A3) is W_l(k_l). If an unchosen cell maximizes it,
its unchanged value equals the old maximum, and the preceding bound
on r_l gives(A3). Iterating and discarding the nonnegative final
potential proves

    sum_(a=3..H)3^-a*r_(l_a)(k_(l_a)(a))
      <=max_l sum_(a>=3)3^-a*r_l(a-3).               (A4)

This is profile30(DP2), applied with q=1/3. It bounds every switching
schedule; it does not exchange a sum and a maximum.

At original depth a, the actual ternary cylinder lies in one surviving
cell l or is empty. Its eta mass is at most3^-a. At each point of this
cylinder, the preceding active deep count is at most the number k_l
of preceding depth labels assigned to that cell, even if those actual
prefixes are disjoint or nonnested. Convexity therefore bounds the
pure-cost increment by3^-a*Delta u_l(b_l+k_l). Applying(A4) proves
P_eta. Missing or empty depth labels can be assigned arbitrary cells
in the upper comparison because all rewards are nonnegative.

For the common zero5 block, use the pointwise density bound and the
nonnegative increment of f_l. Its joint lambda and eta increment is
at most the eta integral of the increment of

    u_l=d_l*f_l+bar f_l
       =(d_l-1/5)*f_l
           +sum_(n>=2)[4/(n*5^n)]*[f_l(n v)-f_l(n)].          (A5)

The coefficients are nonnegative because d_l>=1/4. Hence u_l is
increasing and convex. Apply the same counter bound and(A4) to u_l,
which proves the first line of(A2). Thus its maximum of a complete
depth sum is valid for arbitrary original prefixes. It does not assert
that a constant cell schedule is an attainable congruence family.

For fixed costs, F_theta is separately convex on the five parameter
blocks. Initial terms are separately affine. Each deep sum is affine
in d_l before its maximum, and each pure term is a maximum of affine
functions of eta. Positive complete sums preserve convexity. This
also follows from finite partial sums and their finite limits.

## The whole clipped hinge can be absorbed without losing convexity

For t=4 or5 let h_t(v)=(v-t)_+ and chi_t(v)=min(1,h_t(v)). For a
complete original357 test A, denote its original zero7 block by Z0.
This is a complete35 load depending on both the3- and5-coordinates,
and is integrated against Lambda. Define

    p7_1=29/35, p7_n=36/(5*7^n) for n>=2,
    psi_t(v)=sum_(n>=1)(p7_n/n)*[h_t(nv)-h_t(n)].

The original all-block7 comparison gives

    s*E_M h_t(A)<=integral_Lambda psi_t(Z0)+P_t(theta),
    B_t=F_theta(psi_t)+P_t(theta).                         (A6)

Here P_t is the positive original7 complement: the exact affine
constant term plus the positive sum of source envelopes for all
original blocks e>=1, including its complete tail. Its separate
convexity follows from that positive representation. It is not
inferred by subtracting two arbitrary convex functions.

For a root r and cell j define fixed weights and costs

    omega_l=(1_(ROOT(l)=r)+1_(l=j))/5,
    g_l(v)=psi_t(v)-omega_l*chi_t(v), 0<=omega_l<=2/5.

Since chi_t=h_t-h_(t+1), the exact identity

    g_l=(29/35-omega_l)*h_t+omega_l*h_(t+1)
                  +sum_(n>=2)(p7_n/n)*[h_t(n v)-h_t(n)]       (A7)

has nonnegative coefficients. Consequently g_l is nonnegative,
increasing and convex, and g_l(1)=0. Thus(A2) applies. The coefficient
29/35 is from the auxiliary upper comparison; it is not substituted
for an actual pure7 probability.

Because A>=Z0 and h_t is increasing, the signed actual deletion
identity gives

    s*E_M[(h_t(A)-1)*1_V]
      <=P_t+integral_Lambda psi_t(Z0)-s
                      +s*E_M[(1-h_t(Z0))_+*1_Bmix].          (A8)

Use a union bound only on the nonnegative last integrand. For each
positive original7 depth, the forbidden cofactor3 has its own root
and the forbidden cofactor9 its own cell. Their complete pure7 cap
coefficients sum to1/5 for each cofactor. Independence of the product
law between35 and7, followed by summing these caps, therefore bounds
their joint contribution by

    max_(r,j) integral_Lambda omega_l*(1-h_t(Z0))_+.

The choices may change at every original7 depth: the inequality sums
their separate bounds and only then uses the maximum over root/cell
pairs. Missing or empty carriers cause no problem because the
integrand is nonnegative. All other cofactors contribute at most Trest.

For every v>=1,

    psi_t(v)+omega_l*(1-h_t(v))_+=omega_l+g_l(v).

Combining this identity with(A8), before the source operator is
applied, proves

    m_t^abs(theta)=s-P_t-Trest
          -max_(r,j)[(n_r+n_j)/5+F_theta(g^(r,j))],
    n_r=sum_(ROOT(l)=r)n_l,
    E_nu357 h_t(A)<=1-m_t^abs(theta)/S.                     (A9)

This holds for every independent original test. Margins may be
negative. The source and deletion use each retained contribution
once; no correction is also subtracted from the numerator deficits.

Each m_t^abs is separately concave: s is separately affine, P_t and
Trest are separately convex, and for every fixed(r,j) the summand
(n_r+n_j)/5+F_theta(g^(r,j)) is separately convex. Its finite maximum
preserves convexity. The weights and barriers are fixed independently
of theta, which is necessary for this argument.

## A finite lower bound on the true margin

Define, for b=1,2,3,

    kappa_t(b)=sum_(n>=2)[4/(n*5^n)]*[chi_t(n b)-chi_t(n)].

The summands vanish for n>=t+1. Exact evaluation gives

    (kappa_4(1),kappa_4(2),kappa_4(3))=(0,23/1875,173/1875),
    (kappa_5(1),kappa_5(2),kappa_5(3))=(0,587/46875,4337/46875).

For each fixed(r,j) the cell-dependent source comparison obeys

    F_theta(g^(r,j))<=F_theta(psi_t)
                -min_(b in B)sum_l eta_l*omega_l*kappa_t(b_l). (A10)

To prove(A10), compare the two explicit operators in(A2). At a
shallow baseline b_l<=3, chi_t(b_l)=0. Thus the old initial term
minus the new initial term is exactly eta_l*omega_l*kappa_t(b_l).
The old combined deep cost minus the new one is

    omega_l*[(d_l-1/5)*chi_t(v)
       +sum_(n>=2)[4/(n*5^n)]*[chi_t(n v)-chi_t(n)]].          (A11)

Every summand is increasing and nonnegative for v>=1. Consequently
every old deep increment is at least the corresponding new deep
increment. The difference itself need not be convex: its monotonicity
is sufficient here, while convexity of each separate source cost
was already established by(A5) and(A7).

For each positive5 strip the centered old-minus-new cost is

    [omega_l/n]*[chi_t(n v)-chi_t(n)].                        (A12)

It is nonnegative and increasing. Both its initial pure term and
every deep increment are nonnegative, so P_eta(q_n) decreases.
The strip constants decrease by sum_l eta_l*omega_l*chi_t(n)>=0
as well. Thus no positive5 term or complete tail can cancel the
initial saving. Taking the baseline maximum proves(A10).

Put

    epsilon_t(theta)=min_(r,j,b in B)[
       (R(n)+n_*-n_r-n_j)/5
                       +sum_l eta_l*omega_l*kappa_t(b_l)].  (A13)

Each term is nonnegative. Substituting(A10) in(A9), then using(A1)
and(A6), gives the global pointwise lower bound

    m_t^abs(theta)>=D-B_t+epsilon_t(theta), epsilon_t>=0.    (A14)

At each controlling vertex398,410,422,616,628,640,

    epsilon_4=23/84375,
    epsilon_5=587/2109375,
    epsilon_4/6+(4/33)*epsilon_5=11021/139218750.             (A15)

For example, vertex398 has

    eta=(1/18,1/9,1/9,1/9,1/9),
    d=(3/4,3/4,1/4,1/2,1/2),
    n=(1/36,1/12,1/36,1/18,1/18), s=1/4, D=53/360.

The maximum-mass root is the three-cell root, and the maximum-mass
cell is cell1 in the other root. That unique maximizing deletion
pair has omega=(0,1/5,1/5,1/5,1/5). Every baseline meets this support;
b=(3,2,1,1,1) attains the minimum kappa_t(2)/45. Any other deletion
pair incurs mass penalty at least1/180, greater than this minimum.
The other controls are within-root permutations.

No separate-concavity claim is made for epsilon_t, for D-B_t+epsilon_t,
or for their tabulated values. Those are lower bounds at vertices for
the globally defined, separately concave m_t^abs in(A9). Only that
true function is used in the interpolation argument.

## Exact tails and the full continuous survival comparison

Set K=t+1. For every integer v>=K, each g_l(v) is affine with slope1,
say g_l(v)=v+z_l. In particular q_(n,l)(v)=v-1 for n>=K. Exact
finite-plus-tail formulas are

    psi_t(v)=sum_(n=1..t)(p7_n/n)*[h_t(n v)-h_t(n)]
                                      +(6/5)*7^-t*(v-1),
    bar f_l(v)=sum_(n=2..K-1)p5_n*q_(n,l)(v)
                                      +5^(1-K)*(v-1)-f_l(v)/5,
    T0=sum_(n>=K)p5_n=5^(1-K),
    T1=sum_(n>=K)n*p5_n=T0*(K+1/4).

The positive5 tail of(A2) is exactly

    T1*sum_l eta_l+T0*sum_l eta_l*z_l
                                  +(T1-T0)*P_eta(v-1).

For a baseline b_l the combined deep increment is constant once
b_l+a-3>=K, so its remaining sum is that constant times
3^-a/(1-1/3). The pure tails are handled by the same identity. The
positive original7 complement in(A6) retains its existing complete
affine tail. No original exponent is dropped.

Retain profile41's m25 and barrier C25=7/2. Its signed inequality is
E_nu357 h_(5/2)<=7/2-m25/S. With barriers C4=C5=1 from(A9), define

    Msurv=m25/22+m_4^abs/6+(4/33)*m_5^abs,
    q=919/924-(7/2)/22-1/6-4/33
      =193/231-19/66=23/42=253/462.

The original AP bad-mass union inequality yields

    rho_actual*S>=q*S+Msurv.                              (A16)

Every margin here uses the same S; the three original tests keep
independent residue choices. Msurv is separately concave. Its values
need not be positive, and no monotonicity of a signed quotient in S
is assumed.

Retain the profile39 numerator constants and margins

    H=AC*H16+H41, M=AC*Mq+Ml,
    N_J=H*S-M,
    N_Gamma=H16*S-Mq,
    N_T=A81*S+Raw81-cG*mg,
    N_K=(H+A81)*S+Raw81-M-cG*mg.

Here mg uses square barrier45 and all41 globally fixed linear
barriers retain their complete costs. Raw81 retains its internal s
terms. The actual19 input remains the physical nu13 K17 law.

For proposed targets Jstar,GammaStar,Tstar,Kstar and r>0, put
j=Jstar-C0, g=GammaStar-16 and k=Kstar-C0. All four must be
nonnegative. The five sufficient fixed-target inequalities are

    (q-r)*D+Msurv>=0,
    (q*j-H)*D+j*Msurv+M>=0,
    (q*g-H16)*D+g*Msurv+Mq>=0,
    (q*Tstar-A81)*D+Tstar*Msurv-Raw81+cG*mg>=0,
    (q*k-H-A81)*D+k*Msurv-Raw81+M+cG*mg>=0.               (A17)

Their D coefficients are all positive at the reported targets.
Among the four cost coefficients, the smallest is the Gamma
coefficient4.69796845...; the survival coefficient is

    q-r=121608839267/2362133812500>0.

Each left side is separately concave: D,Mq,Ml,mg and Msurv are
separately concave, Raw81 is separately convex, and every displayed
coefficient has the required sign. Evaluate(A17) at the1296 product
vertices, using(A14) as lower bounds for the two true absorbed
margins. Nonnegative vertex values imply nonnegative true margins
throughout the continuous domain. Finally replacing D by the actual
S>=D only increases each left side. The first inequality proves
q*S+Msurv>=r*S>0, justifying every subsequent conditioning division.
This proves(A16) and all four cost bounds on the actual law.

All five controlling sets are the same six vertices in(A15), at the
D endpoint. The reported Kstar equals Jstar+Tstar exactly. This is
attainment by the comparison expressions, not a claim that an actual
congruence family attains them.

## Exact reconstruction and the remaining boundary

The [verifier](../frontier/verify_absorbed_survival_hinges.py) and
[certificate](../certificates/source_norms/absorbed_survival_hinges.json)
reconstruct the profile41 input and both finite kappa tables. They
check259200 epsilon layouts,6480 fixed-target vertex conditions, both
actual-mass endpoints, all eight other source branches, and both
complete finite-core interfaces. The vertex data certify(A17) using
the proved lower bounds; they do not replace the preceding universal
source/deletion proof or assert concavity of a table.

For box20/current8 the complete criterion remains

    Kstar+error<403,
    error=0.000586452245679290...,
    Kstar+error-403=119.69703690318796...>0.

For the unequal/current6 core the complete error is0.224925464765098...
and the gap is119.92137591570739.... Negative Q, continuation through
arbitrary later primes, and unrestricted Erdős #7 remain unproved.
The gain in(A15) is a source/deletion compatibility fact. It does not
assume positive actual intersection of the11- and13-bad events or
of independent mod5 test residues.
