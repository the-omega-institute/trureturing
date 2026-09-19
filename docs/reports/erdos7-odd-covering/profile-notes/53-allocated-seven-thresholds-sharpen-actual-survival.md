[Index](../marked_head_profile.md) · [Common survival carrier](46-one-forbidden-carrier-mixture-strengthens-survival.md) · [Full numerator carriers](49-full-linear-and-quadratic-carriers-refine-the-frontier.md)

# Allocated seven thresholds sharpen actual survival

Allocating the hinge threshold among the original seven blocks gives
stronger actual-law survival bounds. The allocation is fixed for each
full forbidden carrier throughout the continuous source domain. The
same carrier mixture, independent original test residues and complete
exponent tails give

| Quantity | Exact comparison target | Decimal |
| --- | --- | ---: |
| J upper | 32595101390312727014851562038240600447127/78184115000808437672366395852140969600 | 416.9018398427313 |
| Gamma13 upper | 85403176591026772601/582728885706925386 | 146.5573076704816 |
| T13(81) upper | 2873884370396495734788444926897322493/30990676126636038601041738670560375 | 92.73383899896375 |
| K=J+T13(81) common-law upper | 108508024932331114670819517565119344585698949/212986060315016386011231666281461556328000 | 509.4606885156834 |
| rho_actual lower | 40593580507/80223412500 | 0.5060066536935212 |

The J and K targets improve profile49 by0.7988175587932498... and
0.36602446838624997..., respectively. The complete box20/current8 core
gap is106.46126351600151...>0. The strict negative-Q endpoint and
unrestricted Erdos #7 remain open. These are ordinary inequalities
with exact rational verification; no Lean verification or actual
attainment of the final comparison is asserted.

## 1. Actual source, independent tests and fixed allocations

Use the effective9 source of profiles42 and46: eta is the raw pure3
survivor measure, Lambda the raw35 survivor measure, lambda its ternary
marginal, and

    eta_l=eta(cell l), n_l=lambda(cell l), s=sum_l n_l,
    0<=d lambda/d eta<=d_l, d_l>=1/4,
    ROOT=(0,0,1,1,1).

The original complete357 test has independent original35 blocks
A_0,A_1,..., each including its unit term. The complete auxiliary
seven count probabilities are

    p1=29/35, pn=36/(5*7^n) for n>=2.

They are the existing upper comparison probabilities, not the actual
pure7 law. The actual pre-deletion product measure is Lambda tensor
the normalized actual pure7 survivor law. Let V be the complement of
the actual mixed7 forbidden union, S its raw mass, and nu357 the
normalized actual survivor law. All original exponent heights and
residues remain arbitrary.

For t in{4,5} and each2<=n<t choose a rational tau_n with

    1<=tau_n<=t-n+1,
    a_(n,0)=tau_n,
    a_(n,e)=(t-tau_n)/(n-1) for1<=e<n.

Every a_(n,e)>=1 and sum_(e<n)a_(n,e)=t. The final allocations depend
only on the root entry of a full forbidden carrier:

| Hinge t | Forbidden root | (tau2,tau3,...) |
| --- | --- | --- |
| 4 | 0 or1 | (2,1) |
| 5 | 0 | (2,1,1) |
| 5 | 1 | (5/2,1,1) |

This table is fixed independently of theta and of every original test
layout. The positive blocks retain their separate original residues;
sharing a threshold is not an equality of their loads or layouts.

## 2. An allocated source inequality before any layout maximum

Write h_t(v)=(v-t)_+. For v_e>=1 and n<t,

    h_t(sum_(e<n)v_e)<=sum_(e<n)h_(a_(n,e))(v_e).       (A1)

The right side is nonnegative and is at least
sum_(e<n)(v_e-a_(n,e))=sum_(e<n)v_e-t. This proves(A1).
For n>=t the complete affine identity is

    h_t(sum_(e<n)v_e)=(n-t)+sum_(e<n)(v_e-1).          (A2)

For a fixed allocation tau define every original-block cost by

    psi_e^tau(v)=1_(e=0)*p1*h_t(v)
       +sum_(max(2,e+1)<=n<t)pn*h_(a_(n,e))(v)
       +Pr(N>=max(t,e+1))*(v-1).                     (A3)

All coefficients are nonnegative. These costs are nonnegative,
increasing and convex for v>=1, and vanish at one. Their affine
slopes are the original slopes:1 for e=0 and6/(5*7^e) for e>=1.
Only finite hinge positions and affine intercepts change. In
particular the native h_t coefficient of psi_0^tau is still29/35.

Apply the original7 comonotone comparison to h_t, then apply(A1)
separately to each outcome n<t and(A2) to every outcome n>=t.
Collecting the contributions of the same original block gives

    U_t(A):=integral_(Lambda tensor actual-pure7)h_t(A)
       <=s*E h_t(N)+sum_(e>=0)integral_Lambda psi_e^tau(A_e). (A4)

Every original block is kept through all outcomes in which it occurs.
The constant E h_t(N) is unchanged. Infinite completion of a finite
original family is justified by nonnegative summation and the finite
complete first moment. No auxiliary law is substituted for the actual
law without this original-label comparison.

Let F_theta denote the complete raw35 cell-cost source operator of
profile42(A2). Its independent layout maxima apply separately to each
cost in(A4). For e>=t-1 the cost is a nonnegative multiple of v-1,
so the complete positive-block complement is

    P_t^tau=s*E h_t(N)+sum_(e=1..t-2)F_theta(psi_e^tau)
                    +(7^(2-t)/5)*F_theta(v-1),             (A5)
    E h_t(N)=1/(5*7^(t-1)).

Indeed Pr(N>e)=6/(5*7^e) for e>=1 and
sum_(e>=t-1)Pr(N>e)=7^(2-t)/5. Thus(A5) retains every positive
original7 block and its complete tail.

## 3. Complete five and ternary tails

For any allocated cost f_l, including the absorbed costs below,
take K=t+1. Its tail is f_l(v)=sigma*v+kappa_l for v>=K, where
sigma is its original-block slope and is common to the five cells.
The complete positive5 centered cost is

    q_(n,l)(v)=[f_l(n*v)-f_l(n)]/n.

For n>=K this is exactly sigma*(v-1). With

    T0=sum_(n>=K)4/5^n=5^(1-K),
    T1=sum_(n>=K)4*n/5^n=T0*(K+1/4),

the entire positive5 tail in F_theta is

    sigma*T1*sum_l eta_l+T0*sum_l eta_l*kappa_l
                     +(T1-T0)*P_eta(sigma*(v-1)).          (A6)

The signed affine intercepts are retained. The zero5 correction
bar f_l=sum_(n>=2)(4/5^n)*q_(n,l)-f_l/5 has constant tail.
The combined deep cost d_l*f_l+bar f_l has affine slope d_l*sigma.

Every remaining ternary sum has an exact finite entrance and a
geometric tail. If the increments of u have constant value a from
argument K_u onward, and k=max(0,K_u-b), then

    sum_(j>=0)3^(-j-3)*[u(b+j+1)-u(b+j)]
      =sum_(j<k)3^(-j-3)*[u(b+j+1)-u(b+j)]
                                      +a/(2*3^(k+2)).      (A7)

These are identities for the complete source operator. The finite
entrances impose no bound on any original exponent height. Its
admissibility and arbitrary cell-switching control remain those of
the existing raw35 source theorem.

## 4. The same actual deletion and a source bound for each carrier

The18 shallow carriers are

    c in{-1,0,1} x{-1,0,1,2,3,4},

with-1 denoting an empty entry. The10 full carriers f=(r,j) have
r in{0,1} and j in{0,...,4}. Set

    omega_f,l=(1_(ROOT(l)=r)+1_(l=j))/5,
    h_f=integral_lambda omega_f=(n_root,r+n_j)/5,
    chi_t=min(1,h_t).

Use the unchanged complete remainder

    Trest=(max(d)/18+(sum(w)+R(w)+max(w))/36+1/72)/5,
    w_l=9*eta_l, R(w)=max(w0+w1,w2+w3+w4).

For each full carrier use its fixed allocation tau(f), and define

    g_(t,f)=psi_0^tau(f)-omega_f*chi_t.

Since chi_t=h_t-h_(t+1), its native h_t coefficient is
29/35-omega_f>=3/7 and the h_(t+1) coefficient is omega_f>=0.
Every other coefficient in(A3) remains nonnegative. Thus g_(t,f)
is an admissible cell cost and vanishes at one.

Let

    d_t=S*(1-E_nu357 h_t(A)),
    R_c(A0)=integral_Lambda omega_c*(1-h_t(A0))_+.

The actual signed deletion identity, A>=A0, and a union bound only
on the nonnegative deleted integrand give

    d_t>=s-U_t(A)-Trest-sum_c pi_c*R_c(A0).             (A8)

Here pi is the same actual forbidden-carrier mixture of profile46,
including its partial and empty carriers, and sum pi_c=1.
For a full carrier f, combining(A4) with its deleted integrand gives

    U_t(A)+R_f(A0)
       <=P_t^tau(f)+h_f+F_theta(g_(t,f))
       =:H_t(theta;f).                                (A9)

Although the chosen upper bound varies with f, U_t(A) is the same
actual source integral in every inequality. Consequently
sum pi_c*U_t(A)=U_t(A). This permits the carrier-dependent source
bound; it does not condition Lambda on the forbidden carrier or
identify the maximizing original tests of different envelopes.

## 5. Partial completion includes the positive complement

Let Comp(c) be the nonempty set of full carriers agreeing with every
nonempty entry of c. For each f in Comp(c), omega_c<=omega_f, hence
R_c<=R_f. The existing conservative completion convention therefore
gives

    H_t^+(theta;c)=max_(f in Comp(c))[
                         P_t^tau(f)+h_f+F_theta(g_(t,f))],
    m_t(theta;c)=s-Trest-H_t^+(theta;c).               (A10)

The complete positive7 complement must remain inside this maximum:
tau(f) can change when the root of a completion changes. Equivalently,
m_t(theta;c) is the minimum of the compatible full margins.
Equations(A8)-(A10) prove

    d_t>=sum_c pi_c*m_t(theta;c).                     (A11)

The actual partial-carrier mass lower bound D_c is unchanged. It
is not replaced by D_f for a full completion or by a minimum of such
completed masses. A direct source operator at a partial weight is a
different comparison and is not an additive correction to(A10).

## 6. The conditional27/81 credit remains exact

Fix a full completion f and refine its ternary cells to mod81. Put

    epsilon=(1_C27+1_C81)/5,
    Fcost=psi_0^tau(f)-omega_f*chi_t,
    Gcost=Fcost-epsilon*chi_t.

The refined total weight obeys omega_f+epsilon<=4/5. The native
h_t coefficient of Gcost is consequently at least
29/35-4/5=1/35>0. Both costs remain admissible, and Fcost is constant
on each mod9 parent.

The perturbation in profile45(DC5) is precisely epsilon*chi_t. Its
signed initial, deep and positive5 differences depend only on this
perturbation, not on the other hinges of Fcost. They are unchanged.
In particular

    a_t=sum_(n>=2)(4/5^n)*chi_t(n)=5^-t.

The baseline slack is still

    (1-chi_t(v))*(d_child*eta_child-n_child)
       +chi_t(v)*(d_child-1/5)*eta_child
       +eta_child*kappa_t(v)>=0,
    kappa_t(v)=sum_(n>=2)(4/(n*5^n))*[chi_t(n*v)-chi_t(n)].

Thus it also covers refined baselines above t. Combining that
perturbation inequality with the parent-constant refinement bound
of profile45(DC8) gives

    F4(Gcost)+integral_lambda epsilon
       <=F2(Fcost)+(d_*-5^-t)*(1/27+1/81)/5,
    d_*=max_l d_l.                                    (A12)

Removing those same two full cap terms from Trest cancels the
d_* part. Every fixed full completion therefore retains

    delta_t=4/(405*5^t),
    m_t^+(theta;c)=m_t(theta;c)+delta_t,
    d_t>=sum_c pi_c*m_t^+(theta;c).                   (A13)

The same delta_t applies before the completion maximum, so it
commutes with the minimum of full margins. The actual quadruple
carrier mixture has the original shallow marginal pi. Empty deeper
labels leave extra cap slack, as in profile46; no positive actual
occupation of their cylinders is assumed. The mass bounds D_c keep
their original27/81 cap accounting.

Hence the combined raw survival credit is unchanged:

    delta4/6+4*delta5/33=14/4640625.

## 7. One global comparison and the unchanged numerator inputs

For a fixed full f, its allocation and cell cost are fixed throughout
theta. Each P_t^tau(f) is a positive sum of separately convex source
operators plus the separately affine raw constant. The cell-cost
operator is separately convex as well. Thus H_t(theta;f), and its
finite completion maximum, are separately convex. Every true
m_t^+(theta;c) is separately concave.

Keep profile46's h25 margin and define

    M_c=m25(theta;c)/22+m4^+(theta;c)/6
                                      +4*m5^+(theta;c)/33,
    q=23/42.

The same actual-law survival argument gives

    rho_actual*S>=q*S+sum_c pi_c*M_c.                (A14)

All independent numerator-test margins of profile49 use this same
pi. Retain their globally defined true functions and their certified
vertex lower bounds: all41 linear and five quadratic conditional
costs at its24 refined vertices, and its established lower bounds
elsewhere. The independent source-square margin, its barrier45,
the41 linear barriers, the five quadratic barriers, H16,H41,A81,cG,
and the complete raw81 source input are unchanged.

For each cost target T with offset b and numerator slope L, write
its inherited numerator correction as C_c. The sufficient target
margin is

    [q*(T-b)-L]*S+sum_c pi_c*[(T-b)*M_c+C_c].       (A15)

The J, Gamma13, T13(81) and K offsets, slopes and corrections are
exactly those of profile49. For a=q*(T-b)-L>=0, insert
S>=sum pi_c*D_c before minimizing over c. For a<0, use S<=s.
The rho target has the analogous expression(q-rho)*S+sum pi_c*M_c.
All five coefficients are positive at the reported targets; both
mass endpoints are checked by exact arithmetic.

The resulting fixed-target expressions are separately concave in
the five source parameter groups. Their nonnegative values at all
1296 product vertices therefore cover the complete continuous
domain. This argument concerns the true allocated functions and
valid lower bounds for unchanged numerator functions; it does not
infer concavity from a numerical table. The allocated source bounds
are not required to dominate the old ones at every vertex.

## 8. Exact evaluation, remaining controls and scope

The [source helper](../frontier/allocated_seven_thresholds.py),
[verifier](../frontier/verify_allocated_seven_thresholds.py) and
[certificate](../certificates/source_norms/allocated_seven_thresholds.json)
evaluate the fixed allocation table and the complete tails above.
The reconstruction retains the existing source39 inputs and the
unchanged certified numerator data of profile49. It reconstructs
all46656 old h4/h5 full and partial carrier margins before replacing
them, including the complete positive7 complement inside each new
completion maximum.

The fixed-target evaluation covers1296 source vertices,18 carriers,
two actual-mass endpoints and five targets:233280 nonnegative exact
target margins. Positive survival denominators are checked before
conditioning. The eight other source branches retain their complete
independent comparisons, and both existing complete core interfaces
use the new actual rho, Gamma13, J and T13(81) inputs.

As local checks of the allocated source sums, theta404 with carrier
A=(0,1) gains2/8575 for h4 and1131/1200500 for h5. At theta398 with
carrier B=(1,1), the gains are1/5145 and23/240100. These are exact
comparisons of source bounds, not claims of actual attainment.

The final J, Gamma13 and rho controls are

    402,404,406,414,416,418,426,428,430 at(0,1),
    618,620,622,630,632,634,642,644,646 at(0,0).

The final T13(81) and K controls are

    398,410,422 at(1,1),
    616,628,640 at(1,0).

Every listed control uses the actual-mass lower endpoint D_c.
The two complete core errors and remaining K gaps are

| Core | Complete error | K+error-403 |
| --- | ---: | ---: |
| box20/current8 | 0.0005750003181418988 | 106.46126351600151 |
| box(17,10,8,7,6,6,6)/current6 | 0.22052040821266802 | 106.68120892389604 |

Both gaps are positive. No source-family exclusion, finite-height
restriction, actual-source extremal identification or continuation
through arbitrary later primes is used to obtain the stated bounds.

Reproduce the exact certificate with the read-only command:

```sh
python3 -I -O docs/reports/erdos7-odd-covering/frontier/verify_allocated_seven_thresholds.py --check
```

The checker reconstructs the source39 data and old46 margins; the
unchanged47/49 numerator entries are consumed from pinned certificates.
The previous numerator computations are not rerun by this command.
